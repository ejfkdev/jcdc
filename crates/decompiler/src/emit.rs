//! Java source emission from the statement/expression tree.

use jcdc_jvm::{ClassPool, JavaType, PoolClass};

use crate::expr::{BinOp, ConcatPart, ConstVal, Expr, LambdaKind, TypeRef, UnOp};
use crate::method::MethodBody;
use crate::stmt::{CaseGroup, Catch, Stmt};
use crate::varalloc::VarTable;

pub struct Printer<'a> {
    pub pc: &'a PoolClass,
    pub pool: &'a ClassPool,
    pub vt: &'a VarTable,
    out: String,
    indent: usize,
    /// Depth guard for recursive lambda printing.
    lambda_depth: usize,
    /// Names visible in enclosing lambda/method scopes BEYOND self.vt,
    /// accumulated down the lambda print chain: a nested lambda's locals
    /// must not redeclare ANY of them (jdk26 PackageSnippets
    /// .fooToBarUnrolled: the depth-2 codeBuilder lambda's foreach `i$`
    /// collided with the METHOD-level `i$` — the depth-1 rename only
    /// consulted depth-1's vt, 已在方法中定义了变量 i$).
    outer_names: Vec<String>,
    /// True when the enclosing method returns boolean.
    pub ret_bool: bool,
    /// True while rendering the ROOT of an expression statement: a
    /// signature-polymorphic call there must stay bare (`NEXT.compareAndSet
    /// (b, n, p);`) — `(boolean) call();` is not a legal statement.
    suppress_poly_cast: bool,
    /// True while rendering the direct child of a cast expression: a cast
    /// gives the diamond NO target type, so ` (T) new X<>(args)` infers
    /// Object bounds and then fails the cast — while the bare/raw form
    /// `(T) new X(args)` compiles (unchecked).
    suppress_diamond: bool,
    /// True while rendering a conditional expression's branches. Pre-Java-8
    /// (major < 52) conditionals are NOT poly expressions: a diamond branch
    /// (`c ? new HashMap<>(..) : new LinkedHashMap<>(..)`) infers each side
    /// standalone to <Object,Object> and fails the assignment target (jdk7
    /// HashSet.readObject 不兼容的类型 — the golden source carried explicit
    /// <E,Object> args). Diamond branches print RAW there instead:
    /// unchecked but always compilable.
    in_cond: bool,
    /// Instantiated SAM return type while rendering the Lambda directly
    /// inside a cast to a generic functional interface: the lambda body's
    /// returns may need `(R) value` witnesses (jdk17 Collectors
    /// `(Function<I,R>) i -> i`).
    lambda_sam_ret: Option<TypeRef>,
    /// The method's generic signature return (functional-interface or
    /// array form): a lambda in RETURN position has no cast node to hang
    /// the SAM witness on, so the Return arm derives it from this.
    ret_sam: Option<TypeRef>,
    /// True when the enclosing method returns char: int constants in the
    /// returned expression render as char literals (bytecode chars are
    /// ints; `return cond ? 63 : 105;` in a char method is a lossy
    /// conversion — source was `? '?' : 'i'`, jdk XML Parser x23).
    pub ret_char: bool,
    /// Narrowing-return markers: int-valued expressions in the return
    /// need `(byte)`/`(short)` casts (jdk11 MemberName:
    /// `byte normalVirtual = cond ? 5 : 9;`).
    pub ret_byte: bool,
    pub ret_short: bool,
}

impl<'a> Printer<'a> {
    pub fn new(pc: &'a PoolClass, pool: &'a ClassPool, vt: &'a VarTable) -> Self {
        Printer { pc, pool, vt, out: String::new(), indent: 0, lambda_depth: 0, outer_names: Vec::new(), ret_bool: false, suppress_poly_cast: false, suppress_diamond: false, in_cond: false, lambda_sam_ret: None, ret_sam: None, ret_char: false, ret_byte: false, ret_short: false }
    }

    pub fn with_ret_bool(mut self, b: bool) -> Self {
        self.ret_bool = b;
        self
    }

    pub fn with_ret_sam(mut self, t: Option<TypeRef>) -> Self {
        self.ret_sam = t;
        self
    }
    pub fn with_ret_char(mut self, b: bool) -> Self {
        self.ret_char = b;
        self
    }

    pub fn with_ret_narrow(mut self, byte: bool, short: bool) -> Self {
        self.ret_byte = byte;
        self.ret_short = short;
        self
    }

    /// Printer starting at a fixed indentation level (method bodies at 1).
    pub fn with_indent(mut self, indent: usize) -> Self {
        self.indent = indent;
        self
    }

    pub fn into_string(mut self, body: &Stmt) -> String {
        let body = truncate_dead_ends(body);
        self.stmt(&body);
        self.out
    }

    /// Print an expression that appears in a boolean context; int 0/1
    /// constants become true/false.
    fn bool_ish_expr(x: &Expr) -> bool {
        match x {
            Expr::Const(ConstVal::Int(n)) => *n == 0 || *n == 1,
            Expr::Cond { t, f, .. } => {
                matches!(&**t, Expr::Const(ConstVal::Int(0 | 1)))
                    && matches!(&**f, Expr::Const(ConstVal::Int(0 | 1)))
            }
            Expr::Un { op: crate::expr::UnOp::Not, .. } | Expr::InstanceOf { .. } => true,
            Expr::Bin { op, .. } => matches!(
                op,
                crate::expr::BinOp::Eq
                    | crate::expr::BinOp::Ne
                    | crate::expr::BinOp::Lt
                    | crate::expr::BinOp::Ge
                    | crate::expr::BinOp::Gt
                    | crate::expr::BinOp::Le
                    | crate::expr::BinOp::RefEq
                    | crate::expr::BinOp::RefNe
                    | crate::expr::BinOp::LogAnd
                    | crate::expr::BinOp::LogOr
            ),
            other => other.type_ref().erased() == jcdc_jvm::JavaType::Boolean,
        }
    }

    /// bool_ish_expr with VarTable resolution: booleanize retypes the vt
    /// while embedded Local tys stay frozen, and a bitwise bin over
    /// bool-ish sides is itself boolean (jdk26 LinkedTransferQueue
    /// `(spin & !upc) == 0`).
    fn bool_ish_vt(&self, x: &Expr) -> bool {
        match x {
            Expr::Local { var, .. } => {
                matches!(self.vt.var(*var).ty.erased(), jcdc_jvm::JavaType::Boolean)
            }
            Expr::Bin { op, l, r, .. }
                if matches!(
                    op,
                    crate::expr::BinOp::And | crate::expr::BinOp::Or | crate::expr::BinOp::Xor
                ) =>
            {
                self.bool_ish_vt(l) && self.bool_ish_vt(r)
            }
            _ => Self::bool_ish_expr(x),
        }
    }

    pub fn expr_bool(&mut self, e: &Expr, out: &mut String) {
        match e {
            Expr::Const(ConstVal::Int(n)) => {
                out.push_str(if *n != 0 { "true" } else { "false" });
            }
            // Bitwise ops over boolean-ish operands print as their
            // logical form: javac computes `a != b` over booleans as
            // IXOR of 0/1 ints (jdk17 DecimalFormat isNegative:
            // `(c1 ? 1 : 0) ^ (c2 ? 1 : 0)` against a boolean local —
            // "int无法转换为boolean").
            Expr::Bin { op: bop, l, r, .. }
                if matches!(
                    bop,
                    crate::expr::BinOp::Xor | crate::expr::BinOp::And | crate::expr::BinOp::Or
                ) && self.bool_ish_vt(l)
                    && self.bool_ish_vt(r) =>
            {
                let sym = match bop {
                    crate::expr::BinOp::Xor => "^",
                    crate::expr::BinOp::And => "&",
                    _ => "|",
                };
                // Parenthesize composite sides: expr_bool renders `||`/
                // `&&` conditions bare and ^ binds LOOSER than && but
                // TIGHTER than || (a || b && c ^ d would regroup).
                for (i, side) in [l.as_ref(), r.as_ref()].iter().enumerate() {
                    if i > 0 {
                        out.push(' ');
                        out.push_str(sym);
                        out.push(' ');
                    }
                    let needs = matches!(
                        side,
                        Expr::Bin { .. } | Expr::Cond { .. } | Expr::Assign { .. }
                    );
                    if needs {
                        out.push('(');
                    }
                    self.expr_bool(side, out);
                    if needs {
                        out.push(')');
                    }
                }
                return;
            }
            Expr::Cond { c, t, f } => {
                // `x ? true : false` → x ; `x ? false : true` → !x
                let tb = const_bool(t);
                let fb = const_bool(f);
                match (tb, fb) {
                    (Some(true), Some(false)) => self.expr_bool(c, out),
                    (Some(false), Some(true)) => {
                        // !(!x) collapses to x
                        if let Expr::Un { op: crate::expr::UnOp::Not, e: inner } = &**c {
                            self.expr_bool(inner, out);
                        } else {
                            out.push('!');
                            // expr_bool renders composite conditions bare:
                            // `!` + `ssign != 45` would regroup as
                            // `(!ssign) != 45` (jdk26 FloatingDecimal
                            // "一元运算符 '!' 的操作数类型int错误").
                            let needs = matches!(
                                &**c,
                                Expr::Bin { .. } | Expr::Cond { .. } | Expr::Assign { .. }
                            );
                            if needs {
                                out.push('(');
                            }
                            self.expr_bool(c, out);
                            if needs {
                                out.push(')');
                            }
                        }
                    }
                    _ => {
                        self.expr(c, 3, out);
                        out.push_str(" ? ");
                        self.expr_bool(t, out);
                        out.push_str(" : ");
                        self.expr_bool(f, out);
                    }
                }
            }
            _ => self.expr(e, 1, out),
        }
    }

    // ---------------- statements ----------------

    fn line(&mut self, s: &str) {
        for _ in 0..self.indent {
            self.out.push_str("    ");
        }
        self.out.push_str(s);
        self.out.push('\n');
    }

    /// Render an int-typed expression in a byte/short target: constants
    /// and ternary branches get the narrowing cast (javac's conditional
    /// expression only narrows when the target type is known — a return
    /// or local-decl of byte/short with int constants needs explicit
    /// casts: `byte normalVirtual = !if() ? (byte) 5 : (byte) 9;`).
    pub fn expr_narrow(&mut self, e: &Expr, ty: &jcdc_jvm::JavaType, out: &mut String) {
        self.expr_narrow_f(e, ty, false, out)
    }

    /// `force_consts`: the enclosing conditional's condition is not a
    /// compile-time constant, so the whole expression is not a constant
    /// expression and javac's assignment-context narrowing does NOT apply
    /// to in-range int constants either (byte getDirectionality: `return
    /// (ch & 0xFFFE) == 0xFFFE ? -1 : 0` — 从int转换到byte可能会有损失;
    /// the source branches are byte static finals the bytecode inlined).
    fn expr_narrow_f(
        &mut self,
        e: &Expr,
        ty: &jcdc_jvm::JavaType,
        force_consts: bool,
        out: &mut String,
    ) {
        match e {
            Expr::Const(ConstVal::Int(n)) => {
                let (lo, hi) = match ty {
                    jcdc_jvm::JavaType::Byte => (-128i64, 127i64),
                    jcdc_jvm::JavaType::Short => (-32768i64, 32767i64),
                    _ => (i32::MIN as i64, i32::MAX as i64),
                };
                if force_consts || (*n as i64) < lo || (*n as i64) > hi {
                    out.push('(');
                    out.push_str(&self.type_name(&TypeRef::J(ty.clone())));
                    out.push_str(") ");
                }
                out.push_str(&n.to_string());
            }
            Expr::Cond { c, t, f } => {
                let force = force_consts || !matches!(&**c, Expr::Const(_));
                self.expr(c, 3, out);
                out.push_str(" ? ");
                let prev = std::mem::replace(&mut self.in_cond, true);
                self.expr_narrow_f(t, ty, force, out);
                out.push_str(" : ");
                self.expr_narrow_f(f, ty, force, out);
                self.in_cond = prev;
            }
            // An int-typed local (typically a branch-merge stack temp)
            // under a byte/short target needs the explicit narrowing cast
            // (jdk17 InvokerBytecodeGenerator `return stack61;` —
            // 从int转换到byte可能会有损失; the merged branches carried
            // byte values the evidence widened to int).
            Expr::Local { var, .. } => {
                if matches!(
                    (self.vt.var(*var).ty.erased(), ty),
                    (jcdc_jvm::JavaType::Int, jcdc_jvm::JavaType::Byte)
                        | (jcdc_jvm::JavaType::Int, jcdc_jvm::JavaType::Short)
                ) {
                    out.push('(');
                    out.push_str(&self.type_name(&TypeRef::J(ty.clone())));
                    out.push_str(") ");
                }
                self.expr(e, 1, out);
            }
            _ => self.expr(e, 1, out),
        }
    }

    /// Call-argument variant of expr_narrow: invocation conversion never
    /// narrows, so in-range int constants keep the explicit cast too, and
    /// int conditionals get it per branch.
    fn expr_narrow_arg(&mut self, e: &Expr, ty: &jcdc_jvm::JavaType, out: &mut String) {
        match e {
            Expr::Const(ConstVal::Int(n)) => {
                out.push('(');
                out.push_str(&self.type_name(&TypeRef::J(ty.clone())));
                out.push_str(") ");
                out.push_str(&n.to_string());
            }
            Expr::Cond { c, t, f } => {
                self.expr(c, 3, out);
                out.push_str(" ? ");
                let prev = std::mem::replace(&mut self.in_cond, true);
                self.expr_narrow_arg(t, ty, out);
                out.push_str(" : ");
                self.expr_narrow_arg(f, ty, out);
                self.in_cond = prev;
            }
            _ => self.expr(e, 1, out),
        }
    }

    /// Render an expression in a char-typed target: int constants become
    /// char literals, ternary branches recurse (the lossy-conversion fix
    /// for `char name2type(..) { return c ? 63 : 105; }`).
    pub fn expr_char(&mut self, e: &Expr, out: &mut String) {
        match e {
            Expr::Const(ConstVal::Int(n)) => push_char_lit(out, *n),
            Expr::Cond { c, t, f } => {
                self.expr(c, 3, out);
                out.push_str(" ? ");
                let prev = std::mem::replace(&mut self.in_cond, true);
                self.expr_char(t, out);
                out.push_str(" : ");
                self.expr_char(f, out);
                self.in_cond = prev;
            }
            _ => self.expr(e, 1, out),
        }
    }

    fn stmt(&mut self, s: &Stmt) {
        match s {
            Stmt::Block(v) => {
                for x in v {
                    self.stmt(x);
                }
            }
            Stmt::ExprStmt(e) => {
                let mut line = String::new();
                if matches!(e, Expr::Method { .. }) {
                    self.suppress_poly_cast = true;
                }
                self.expr(e, 0, &mut line);
                self.suppress_poly_cast = false;
                line.push(';');
                self.line(&line);
            }
            Stmt::LocalDef { var, init, is_final, force_type } => {
                let _ = force_type;
                let info = self.vt.var(*var);
                let mut line = String::new();
                if *is_final {
                    line.push_str("final ");
                }
                line.push_str(&self.type_name(&info.ty));
                line.push(' ');
                line.push_str(&info.name);
                if let Some(e) = init {
                    line.push_str(" = ");
                    // A lambda initializing a generically-typed SAM local:
                    // the declared type is the only record of the
                    // instantiated SAM return (the indy's
                    // instantiatedMethodType is erased — IntFunction<T[]>
                    // records (I)[Object), so prime the lambda-body cast
                    // from it (jdk11 ForEachOps: `IntFunction<T[]>
                    // generator = size -> (T[]) new Object[size]` —
                    // without the cast "lambda 表达式中的返回类型错误").
                    if let (TypeRef::G(g @ jcdc_jvm::GenericType::Class(_)), Expr::Lambda(l)) =
                        (&info.ty, e)
                    {
                        if self.lambda_sam_ret.is_none() {
                            self.lambda_sam_ret = self.sam_ret_cast(g, &l.sam_name);
                        }
                    }
                    // Assigning a concrete type to a type-variable local
                    // needs the (erased-away) cast back in source form.
                    let need_cast = matches!(
                        &info.ty,
                        TypeRef::G(jcdc_jvm::GenericType::TypeVar(_))
                    ) && e.type_ref() != info.ty;
                    if need_cast {
                        line.push('(');
                        line.push_str(&self.type_name(&info.ty));
                        line.push_str(") ");
                        self.expr(e, 14, &mut line);
                    } else if info.ty.erased() == jcdc_jvm::JavaType::Boolean {
                        self.expr_bool(e, &mut line);
                    } else if info.ty.erased() == jcdc_jvm::JavaType::Char {
                        self.expr_char(e, &mut line);
                    } else if info.ty.erased() == jcdc_jvm::JavaType::Byte
                        || info.ty.erased() == jcdc_jvm::JavaType::Short
                    {
                        let t = info.ty.erased();
                        self.expr_narrow(e, &t, &mut line);
                    } else {
                        self.expr(e, 1, &mut line);
                    }
                }
                line.push(';');
                self.line(&line);
            }
            Stmt::Return(Some(e)) => {
                let mut line = String::from("return ");
                if self.ret_bool {
                    self.expr_bool(e, &mut line);
                } else if self.ret_char {
                    self.expr_char(e, &mut line);
                } else if self.ret_byte {
                    self.expr_narrow(e, &jcdc_jvm::JavaType::Byte, &mut line);
                } else if self.ret_short {
                    self.expr_narrow(e, &jcdc_jvm::JavaType::Short, &mut line);
                } else {
                    // Lambda in return position of a generic method: the
                    // SAM return witnesses the erased body value
                    // (castingIdentity `return i -> (R) i`, toArray
                    // `() -> (T[]) new Object[]{..}` — jdk17 Collectors).
                    if let (Some(TypeRef::G(g)), Expr::Lambda(l)) = (&self.ret_sam, e) {
                        self.lambda_sam_ret = match g {
                            jcdc_jvm::GenericType::Class(_) => self.sam_ret_cast(g, &l.sam_name),
                            jcdc_jvm::GenericType::Array(_) => Some(TypeRef::G(g.clone())),
                            _ => None,
                        };
                    }
                    self.expr(e, 1, &mut line);
                    self.lambda_sam_ret = None;
                }
                line.push(';');
                self.line(&line);
            }
            Stmt::Return(None) => self.line("return;"),
            Stmt::Throw(e) => {
                let mut line = String::from("throw ");
                self.expr(e, 1, &mut line);
                line.push(';');
                self.line(&line);
            }
            Stmt::If { cond, then_stmt, else_stmt } => {
                self.print_if(cond, then_stmt, else_stmt.as_deref(), "");
            }
            Stmt::While { cond, body } => {
                let mut head = String::from("while (");
                if matches!(cond, Expr::Const(ConstVal::Int(1))) {
                    head.push_str("true");
                } else {
                    self.expr_bool(cond, &mut head);
                }
                head.push(')');
                self.block_stmt(&head, body);
            }
            Stmt::DoWhile { body, cond } => {
                self.line("do {");
                self.indent += 1;
                self.stmt(body);
                self.indent -= 1;
                let mut tail = String::from("} while (");
                self.expr_bool(cond, &mut tail);
                tail.push_str(");");
                self.line(&tail);
            }
            Stmt::For { init, cond, update, body } => {
                let mut head = String::from("for (");
                for (i, s) in init.iter().enumerate() {
                    if i > 0 {
                        head.push_str(", ");
                    }
                    self.stmt_inline(s, &mut head);
                }
                head.push_str("; ");
                if let Some(c) = cond {
                    self.expr_bool(c, &mut head);
                }
                head.push_str("; ");
                for (i, u) in update.iter().enumerate() {
                    if i > 0 {
                        head.push_str(", ");
                    }
                    self.expr(u, 1, &mut head);
                }
                head.push(')');
                self.block_stmt(&head, body);
            }
            Stmt::ForEach { var, iterable, is_array, body } => {
                let _ = is_array;
                let info = self.vt.var(*var);
                let mut head = String::from("for (");
                head.push_str(&self.type_name(&info.ty));
                head.push(' ');
                head.push_str(&info.name);
                head.push_str(" : ");
                self.expr(iterable, 1, &mut head);
                head.push(')');
                self.block_stmt(&head, body);
            }
            Stmt::Switch { selector, cases, default, on_string } => {
                let _ = on_string;
                let mut head = String::from("switch (");
                self.expr(selector, 1, &mut head);
                head.push(')');
                self.line(&format!("{} {{", head));
                self.indent += 1;
                for c in cases {
                    // MULTIPLE pattern labels in one arm cannot share a
                    // colon body: neither stacked (`case P1 x:` `case P2
                    // y:` — 贯穿到模式非法) nor comma-joined (`case P1 x,
                    // P2 y:` — javac still demands a break between pattern
                    // labels) compile. Duplicate the body per label — the
                    // source's arrow-form multi-pattern arm
                    // (`case A _, B _ -> r;`, jdk26 ParserVerifier
                    // valueSize) in colon form.
                    if c.raw_labels.len() > 1
                        && c.labels.is_empty()
                        && c.string_labels.is_empty()
                        && c.enum_labels.is_empty()
                    {
                        for l in &c.raw_labels {
                            match &c.guard {
                                Some(g) => {
                                    let mut gtxt = String::new();
                                    self.expr(g, 1, &mut gtxt);
                                    self.line(&format!("case {} when {}:", l, gtxt));
                                }
                                None => self.line(&format!("case {}:", l)),
                            }
                            self.line("{");
                            self.indent += 1;
                            for st in &c.body {
                                self.stmt(st);
                            }
                            self.indent -= 1;
                            self.line("}");
                        }
                        continue;
                    }
                    for l in &c.enum_labels {
                        self.line(&format!("case {}:", l));
                    }
                    if let Some(g) = &c.guard {
                        // Folded pattern guard: the desugared restart shape
                        // (`if (guard) body else { state=N; continue; }`)
                        // restored to `case T v when guard:` (jdk26
                        // DecimalFormat — duplicate type-pattern labels are
                        // "此 case 标签由前一个 case 标签支配" without it).
                        let mut gtxt = String::new();
                        self.expr(g, 1, &mut gtxt);
                        let joined = c
                            .raw_labels
                            .iter()
                            .map(|l| format!("{} when {}", l, gtxt))
                            .collect::<Vec<_>>()
                            .join(", ");
                        self.line(&format!("case {}:", joined));
                    } else if !c.raw_labels.is_empty() {
                        // Pattern labels of one arm MUST be comma-joined:
                        // stacked `case P1 x:` / `case P2 y:` lines are a
                        // fall-through between patterns ("从模式贯穿非法",
                        // jdk26 ParserVerifier `case OfConstant _,
                        // OfClass _ -> 2`).
                        self.line(&format!("case {}:", c.raw_labels.join(", ")));
                    }
                    for l in &c.labels {
                        self.line(&format!("case {}:", l));
                    }
                    for l in &c.string_labels {
                        self.line(&format!("case \"{}\":", escape_string(l)));
                    }
                    // Braces give each case its own scope: pattern-switch
                    // restorations reuse binding names across cases.
                    self.line("{");
                    self.indent += 1;
                    for st in &c.body {
                        self.stmt(st);
                    }
                    self.indent -= 1;
                    self.line("}");
                }
                if let Some(d) = default {
                    self.line("default:");
                    self.indent += 1;
                    self.stmt(d);
                    self.indent -= 1;
                }
                self.indent -= 1;
                self.line("}");
            }
            Stmt::Try { body, catches, finally } => {
                self.line("try {");
                self.indent += 1;
                self.stmt(body);
                self.indent -= 1;
                for c in catches {
                    let exc_name = if c.exc.is_empty() {
                        "Throwable".to_string()
                    } else {
                        c.exc.iter().map(|e| self.shorten(e)).collect::<Vec<_>>().join(" | ")
                    };
                    let var_name = if c.var == u32::MAX {
                        "ignored".to_string()
                    } else {
                        c.var_name.clone().unwrap_or_else(|| self.vt.var(c.var).name.clone())
                    };
                    self.line(&format!("}} catch ({} {}) {{", exc_name, var_name));
                    self.indent += 1;
                    self.stmt(&c.body);
                    self.indent -= 1;
                }
                if let Some(f) = finally {
                    self.line("} finally {");
                    self.indent += 1;
                    self.stmt(f);
                    self.indent -= 1;
                }
                self.line("}");
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                let mut res: Vec<String> = Vec::new();
                for r in resources {
                    if let Stmt::LocalDef { var, init, .. } = r {
                        let info = self.vt.var(*var);
                        let mut t = String::new();
                        t.push_str(&self.type_name(&info.ty));
                        t.push(' ');
                        t.push_str(&info.name);
                        if let Some(e) = init {
                            t.push_str(" = ");
                            self.expr(e, 1, &mut t);
                        }
                        res.push(t);
                    }
                }
                self.line(&format!("try ({}) {{", res.join("; ")));
                self.indent += 1;
                self.stmt(body);
                self.indent -= 1;
                for c in catches {
                    let exc_name = if c.exc.is_empty() {
                        "Throwable".to_string()
                    } else {
                        c.exc.iter().map(|e| self.shorten(e)).collect::<Vec<_>>().join(" | ")
                    };
                    let var_name = if c.var == u32::MAX {
                        "ignored".to_string()
                    } else {
                        c.var_name.clone().unwrap_or_else(|| self.vt.var(c.var).name.clone())
                    };
                    self.line(&format!("}} catch ({} {}) {{", exc_name, var_name));
                    self.indent += 1;
                    self.stmt(&c.body);
                    self.indent -= 1;
                }
                if let Some(f) = finally {
                    self.line("} finally {");
                    self.indent += 1;
                    self.stmt(f);
                    self.indent -= 1;
                }
                self.line("}");
            }
            Stmt::Assert { cond, msg } => {
                let mut line = String::from("assert ");
                // The assert-condition is boolean-typed: the synthesized
                // `assert false` carries Const Int(0) — plain expr would
                // print `assert 0` (int无法转换为boolean, jdk17 URI).
                self.expr_bool(cond, &mut line);
                if let Some(m) = msg {
                    line.push_str(" : ");
                    self.expr(m, 1, &mut line);
                }
                line.push(';');
                self.line(&line);
            }
            Stmt::Synchronized { lock, body } => {
                let mut head = String::from("synchronized (");
                self.expr(lock, 1, &mut head);
                head.push(')');
                self.block_stmt(&head, body);
            }
            Stmt::TernaryValue { e } => {
                let mut line = String::from("/* ternary */ ");
                self.expr(e, 1, &mut line);
                line.push(';');
                self.line(&line);
            }
            Stmt::MonitorEnter(e) => {
                let mut line = String::from("/* monitorenter */ ");
                self.expr(e, 1, &mut line);
                line.push(';');
                self.line(&line);
            }
            Stmt::MonitorExit(e) => {
                let mut line = String::from("/* monitorexit */ ");
                self.expr(e, 1, &mut line);
                line.push(';');
                self.line(&line);
            }
            Stmt::ClassDecl { header, body, .. } => {
                let kw = if header.starts_with("record ")
                    || header.starts_with("interface ")
                    || header.starts_with("enum ")
                {
                    String::new()
                } else {
                    "class ".to_string()
                };
                self.line(&format!("{}{} {{", kw, header));
                for line in body.lines() {
                    if line.trim().is_empty() {
                        self.out.push('\n');
                    } else {
                        for _ in 0..self.indent + 1 {
                            self.out.push_str("    ");
                        }
                        self.out.push_str(line.trim_start());
                        self.out.push('\n');
                    }
                }
                self.line("}");
            }
            Stmt::Labeled { label, body } => {
                // label prefix on the following statement's line
                let save = self.out.len();
                self.stmt(body);
                // prepend "label: " before the first line just emitted
                let indent_str = "    ".repeat(self.indent);
                let emitted = self.out[save..].to_string();
                self.out.truncate(save);
                if let Some(rest) = emitted.strip_prefix(&indent_str) {
                    self.out.push_str(&indent_str);
                    self.out.push_str(label);
                    self.out.push_str(": ");
                    self.out.push_str(rest);
                } else {
                    self.out.push_str(&emitted);
                }
            }
            Stmt::Break(lbl) => match lbl {
                Some(l) => self.line(&format!("break {};", l)),
                None => self.line("break;"),
            },
            Stmt::Continue(lbl) => match lbl {
                Some(l) => self.line(&format!("continue {};", l)),
                None => self.line("continue;"),
            },
            Stmt::Label(id) => {
                // Emitted by breaking the following statement; standalone
                // labels are invalid before non-statements, so use a marker.
                self.line(&format!("L{}: ;", id));
            }
            Stmt::Goto(id) => self.line(&format!("break L{};", id)),
            Stmt::Comment(c) => self.line(&format!("// {}", c)),
        }
    }

    /// `head {` + body + `}`.
    fn block_stmt(&mut self, head: &str, body: &Stmt) {
        self.line(&format!("{} {{", head));
        self.indent += 1;
        self.stmt(body);
        self.indent -= 1;
        self.line("}");
    }

    /// Print an if statement; `opener` is "" for the first if and
    /// "} else " when continuing an else-if chain on the closing line.
    fn print_if(&mut self, cond: &Expr, then_stmt: &Stmt, else_stmt: Option<&Stmt>, opener: &str) {
        let mut head = String::from(opener);
        head.push_str("if (");
        self.expr_bool(cond, &mut head);
        head.push_str(") {");
        self.line(&head);
        self.indent += 1;
        self.stmt(then_stmt);
        self.indent -= 1;
        match else_stmt {
            Some(Stmt::If { cond: c2, then_stmt: t2, else_stmt: e2 }) => {
                self.print_if(c2, t2, e2.as_deref(), "} else ");
            }
            Some(other) => {
                self.line("} else {");
                self.indent += 1;
                self.stmt(other);
                self.indent -= 1;
                self.line("}");
            }
            None => self.line("}"),
        }
    }

    fn stmt_inline(&self, s: &Stmt, out: &mut String) {
        match s {
            Stmt::ExprStmt(e) => {
                let mut p = self.sub();
                if matches!(e, Expr::Method { .. }) {
                    p.suppress_poly_cast = true;
                }
                p.expr(e, 1, out);
            }
            Stmt::LocalDef { var, init, .. } => {
                let info = self.vt.var(*var);
                out.push_str(&self.type_name(&info.ty));
                out.push(' ');
                out.push_str(&info.name);
                if let Some(e) = init {
                    out.push_str(" = ");
                    let mut p = self.sub();
                    p.expr(e, 1, out);
                }
            }
            other => {
                let mut p = self.sub();
                p.stmt(other);
                out.push_str(p.out.trim_end());
            }
        }
    }

    fn sub(&self) -> Printer<'a> {
        Printer {
            pc: self.pc,
            pool: self.pool,
            vt: self.vt,
            out: String::new(),
            indent: 0,
            lambda_depth: self.lambda_depth,
            outer_names: self.outer_names.clone(),
            ret_bool: self.ret_bool,
            ret_char: self.ret_char,
            ret_byte: self.ret_byte,
            ret_short: self.ret_short,
            suppress_poly_cast: self.suppress_poly_cast,
            suppress_diamond: self.suppress_diamond,
            in_cond: self.in_cond,
            lambda_sam_ret: self.lambda_sam_ret.clone(),
            ret_sam: self.ret_sam.clone(),
        }
    }

    // ---------------- expressions ----------------

    pub fn expr(&mut self, e: &Expr, outer_prec: u8, out: &mut String) {
        let parens = e.needs_parens(outer_prec, false);
        if parens {
            out.push('(');
        }
        match e {
            Expr::Const(c) => self.const_val(c, out),
            Expr::Raw(t) if t == "\u{3}" => out.push_str("this"),
            Expr::Raw(t) => out.push_str(t),
            Expr::RawT(t, _) => out.push_str(t),
            Expr::Local { var, .. } => {
                let info = self.vt.var(*var);
                out.push_str(&info.name);
            }
            Expr::This => out.push_str("this"),
            Expr::New { cls, args, ty, .. } => {
                let no_diamond = self.suppress_diamond;
                self.suppress_diamond = false;
                // Explicit type arguments pinned by the AST passes
                // (diamond_explicit_args_from_call_args): print them
                // instead of the diamond.
                let explicit = match ty {
                    TypeRef::G(jcdc_jvm::GenericType::Class(cs))
                        if cs
                            .parts
                            .last()
                            .map(|p| !p.args.is_empty())
                            .unwrap_or(false)
                            && crate::method::classsig_internal(cs) == *cls =>
                    {
                        let rendered: Vec<String> = cs
                            .parts
                            .last()
                            .unwrap()
                            .args
                            .iter()
                            .map(|a| self.generic_name(a))
                            .collect();
                        Some(format!("<{}>", rendered.join(", ")))
                    }
                    _ => None,
                };
                // A wildcard-typed ctor argument dooms diamond inference
                // (the inference variable gets an equality constraint from
                // the capture and a different bound from the context —
                // "cannot infer type arguments for Entry<>", jdk11
                // Hashtable `tab[i] = new Entry<>(hash, key, value, e)`
                // with e: Entry<?,?>; the source declared e as Entry<K,V>
                // via an unchecked cast that leaves no bytecode trace).
                // The raw form is always applicable (unchecked).
                let args_wildcard = args.iter().any(|a| {
                    matches!(a.type_ref(), TypeRef::G(ref g)
                        if crate::classdec::g_has_wildcard(g))
                });
                let diamond: std::borrow::Cow<str> = match &explicit {
                    Some(x) => x.as_str().into(),
                    // Pre-Java-8 conditional branches are not poly
                    // expressions: the diamond cannot see the assignment
                    // target through the `?:` and infers <Object,Object>
                    // (jdk7 HashSet.readObject map-ternary 不兼容的类型).
                    // Raw is unchecked but always compilable.
                    None if no_diamond || args_wildcard
                        || (self.in_cond && self.pc.cf.major_version < 52) =>
                    {
                        "".into()
                    }
                    None => self.diamond_for(cls).into(),
                };
                let diamond = diamond.as_ref();
                if let Some(local) = cls.strip_prefix('\u{2}') {
                    out.push_str("new ");
                    out.push_str(local);
                    out.push_str(diamond);
                    out.push('(');
                    // Local records/classes keep bytecode-arity ctors:
                    // typed rendering turns an int constant into the
                    // char/boolean literal the ctor expects (jdk17
                    // MessageFormat `new Qchar(39, quoted)`).
                    // Nested local-class method printing runs under a
                    // TAKEN LOCAL_CLASS_INTERNALS registry — resolve a
                    // self-construction (`new BitSetSpliterator(..)` inside
                    // BitSetSpliterator.trySplit) through the printer's
                    // own class when the registry misses. Local-class
                    // ctors capture the enclosing instance as a leading
                    // param that the printed new-site omits; the this$0
                    // fallback in ctor_param_types lines the formals up
                    // (jdk11 BitSet$1BitSetSpliterator(BitSet,int,int,int,
                    // boolean) — the boolean formal rendered its arg `0`).
                    let internal = crate::classdec::local_class_internal(local).or_else(|| {
                        let tail =
                            self.pc.internal_name.rsplit('$').next().unwrap_or("");
                        let simple =
                            tail.trim_start_matches(|c: char| c.is_ascii_digit());
                        if !simple.is_empty() && simple == local {
                            return Some(self.pc.internal_name.clone());
                        }
                        // Probe the nested-name space of the printing
                        // context (javac numbers method-local classes
                        // `$1Name`): the new-site needs the real class to
                        // resolve its ctor formals.
                        let base = format!("{}${}", self.pc.internal_name, local);
                        if self.pool.get(&base).is_some() {
                            return Some(base);
                        }
                        for d in 0..10 {
                            let cand = format!("{}${}{}", self.pc.internal_name, d, local);
                            if self.pool.get(&cand).is_some() {
                                return Some(cand);
                            }
                        }
                        None
                    });
                    match internal
                        .as_deref()
                        .and_then(|i| self.ctor_param_types(i, 0, args.len(), args))
                    {
                        Some(pt) => self.args_typed(args, &pt, out),
                        None => self.args(args, out),
                    }
                    out.push(')');
                } else if self.is_member_inner(cls)
                    && !args.is_empty()
                    && !matches!(args[0], Expr::This)
                {
                    // `outerExpr.new Inner(rest...)` — the first ctor arg
                    // is the synthetic outer instance when the class has a
                    // this$0 field, or when the ctor forwards it straight
                    // to super (no field of its own; is_member_inner
                    // detected it). Either way the qualified-new form
                    // supplies the outer implicitly, so skip args[0].
                    self.expr(&args[0], 15, out);
                    out.push_str(".new ");
                    out.push_str(&inner_simple(cls));
                    out.push_str(diamond);
                    out.push('(');
                    match self.ctor_param_types(cls, 1, args.len() - 1, &args[1..]) {
                        Some(pt) => self.args_typed(&args[1..], &pt, out),
                        None => self.args(&args[1..], out),
                    }
                    out.push(')');
                } else {
                    out.push_str("new ");
                    let member_this = self.is_member_inner(cls)
                        && !args.is_empty()
                        && matches!(args[0], Expr::This);
                    let shown = if member_this {
                        // `new Inner()` from inside the outer class
                        inner_simple(cls)
                    } else {
                        self.shorten(cls)
                    };
                    out.push_str(&shown);
                    out.push_str(diamond);
                    out.push('(');
                    if member_this {
                        match self.ctor_param_types(cls, 1, args.len() - 1, &args[1..]) {
                            Some(pt) => self.args_typed(&args[1..], &pt, out),
                            None => self.args(&args[1..], out),
                        }
                    } else {
                        // Pinned generic instantiation: prime lambda args
                        // from the ctor's instantiated Signature formals.
                        let sam_rets: Vec<Option<TypeRef>> = match ty {
                            TypeRef::G(jcdc_jvm::GenericType::Class(cs))
                                if explicit.is_some()
                                    && crate::method::classsig_internal(cs) == *cls =>
                            {
                                let pinned = cs.parts.last().map(|p| p.args.clone());
                                let formals = crate::classdec::ctor_formals_by_arity(
                                    cls,
                                    args.len(),
                                    self.pool,
                                );
                                // The raw ctor formals carry the class's
                                // own typevars — substitute the pinned
                                // instantiation before reading the SAM
                                // return (an unsubstituted R printed `(R)`
                                // — 找不到符号).
                                let class_params = self
                                    .pool
                                    .get(cls)
                                    .and_then(|cpc| {
                                        cpc.class_attr("Signature").and_then(|b| {
                                            if b.len() >= 2 {
                                                cpc.utf8(u16::from_be_bytes([b[0], b[1]]))
                                                    .and_then(|x| jcdc_jvm::parse_class_signature(x))
                                            } else {
                                                None
                                            }
                                        })
                                    })
                                    .map(|sig| sig.params)
                                    .unwrap_or_default();
                                args.iter()
                                    .enumerate()
                                    .map(|(i, a)| {
                                        if !matches!(a, Expr::Lambda(_)) {
                                            return None;
                                        }
                                        let f = formals.as_ref()?.get(i)?;
                                        let pinned = pinned.as_ref()?;
                                        if pinned.len() != class_params.len() {
                                            return None;
                                        }
                                        let inst = crate::method::subst_typevars(
                                            f,
                                            &class_params,
                                            pinned,
                                        );
                                        let Expr::Lambda(l) = a else { return None };
                                        self.sam_ret_cast(&inst, &l.sam_name)
                                    })
                                    .collect()
                            }
                            _ => Vec::new(),
                        };
                        match self.ctor_param_types(cls, 0, args.len(), args) {
                            Some(pt) => self.args_typed_sam(args, &pt, &sam_rets, out),
                            None => self.args(args, out),
                        }
                    }
                    out.push(')');
                }
            }
            Expr::NewArray { elem, dims, trailing_dims, init } => {
                out.push_str("new ");
                out.push_str(&self.type_name(elem));
                match init {
                    Some(vals) => {
                        for _ in 0..=*trailing_dims {
                            out.push_str("[]");
                        }
                        out.push_str(" {");
                        // boolean[]/char[] initializers hold int constants
                        // in bytecode (iconst + bastore/castore): render
                        // them as true/false and char literals (jdk11
                        // PKCS9Attribute `new boolean[] {0, 0, 1, ..}` x18).
                        let elem_bool = elem.erased() == jcdc_jvm::JavaType::Boolean;
                        let elem_char = elem.erased() == jcdc_jvm::JavaType::Char;
                        for (i, v) in vals.iter().enumerate() {
                            if i > 0 {
                                out.push_str(", ");
                            }
                            if elem_bool {
                                self.expr_bool(v, out);
                            } else if elem_char {
                                self.expr_char(v, out);
                            } else {
                                self.expr(v, 1, out);
                            }
                        }
                        out.push('}');
                    }
                    None => {
                        for d in dims {
                            out.push('[');
                            self.expr(d, 1, out);
                            out.push(']');
                        }
                        for _ in 0..*trailing_dims {
                            out.push_str("[]");
                        }
                    }
                }
            }
            Expr::NewMultiArray { ty, dims } => {
                // Strip the dims.len() leading array levels from the type.
                let mut base = ty.erased();
                for _ in 0..dims.len() {
                    match base {
                        jcdc_jvm::JavaType::Array(inner) => base = *inner,
                        _ => break,
                    }
                }
                out.push_str("new ");
                out.push_str(&self.type_name(&TypeRef::J(base)));
                for d in dims {
                    out.push('[');
                    self.expr(d, 1, out);
                    out.push(']');
                }
            }
            Expr::Field { owner, cls, name, is_static, .. } => {
                // javac reserves `$assertionsDisabled`; the declaration and
                // all references are emitted under a private alias.
                let name: &str = if name == "$assertionsDisabled" {
                    crate::classdec::ASSERT_FIELD
                } else {
                    name
                };
                if name == crate::classdec::ASSERT_FIELD {
                    // Assert guards print bare: the field is declared on
                    // the enclosing emitted class or inlined body; the
                    // bytecode owner is often a synthetic holder class
                    // (`ConstantGroup$1`) whose shorten() fallback is
                    // `Object` — a qualified read can never resolve.
                    out.push_str(name);
                } else if name == "length" && cls.is_empty() {
                    if let Some(o) = owner {
                        self.expr(o, 15, out);
                    }
                    out.push_str(".length");
                } else if let Some(o) = owner {
                    if matches!(o.as_ref(), Expr::Raw(t) if t == "\u{3}") {
                        // Outer anonymous class member: unqualified lexical
                        // resolution (an anon outer has no nameable this).
                        out.push_str(name);
                    } else if self.private_super_field(cls, name, o.as_ref()) {
                        // A private field of a SUPERCLASS is not inherited
                        // into the subclass's member scope: `this.algorithm`
                        // inside Delegate (extends MessageDigest, algorithm
                        // private) is "private access" even though the
                        // source comment says it all — jdk11
                        // MessageDigest.Delegate.clone casts
                        // `((MessageDigest)this).algorithm`.
                        out.push_str("((");
                        out.push_str(&self.shorten(cls));
                        out.push_str(") ");
                        if matches!(o.as_ref(), Expr::This) {
                            out.push_str("this");
                        } else {
                            self.expr(o, 14, out);
                        }
                        out.push_str(").");
                        out.push_str(name);
                    } else {
                        self.expr(o, 15, out);
                        out.push('.');
                        out.push_str(name);
                    }
                } else if *is_static {
                    // A same-class static read prints bare — unless a local
                    // of this method shadows the field name: javac resolves
                    // the bare name as the LOCAL (jdk17 Socket.setImpl's
                    // `SocketImplFactory factory = factory;` self-reference
                    // — 可能尚未初始化变量factory x2 sites). Qualify with the
                    // class name to reach the field.
                    let shadowed_by_local = cls == &self.pc.internal_name
                        && self.vt.vars.iter().any(|v| v.name == name);
                    // ENCLOSING-class static fields read from a nested
                    // class print bare too (lexical scope) — and MUST when
                    // the class name itself is shadowed by a member of the
                    // same name: jdk26 HPKE$Impl reads the outer
                    // `byte[] HPKE`/PSK_ID_HASH/SECRET/EXP/KEY constants;
                    // `HPKE.PSK_ID_HASH` resolves the qualifier as the
                    // byte[] FIELD (variables obscure type names in
                    // expression names) — 找不到符号 变量 PSK_ID_HASH x6.
                    let enclosing_static = cls != &self.pc.internal_name
                        && self
                            .pc
                            .internal_name
                            .starts_with(&format!("{}$", cls))
                        && !self.vt.vars.iter().any(|v| v.name == name)
                        && {
                            let mut cur = self.pc.internal_name.clone();
                            let mut shadow = false;
                            while cur != *cls {
                                // Inherited fields shadow too (superclass
                                // chain — see the method-side twin).
                                let mut sup = Some(cur.clone());
                                while let Some(c) = sup.take() {
                                    if let Some(cpc) = self.pool.get(&c) {
                                        if cpc.cf.fields.iter().any(|f| {
                                            cpc.utf8(f.name_index) == Some(name)
                                        }) {
                                            shadow = true;
                                            break;
                                        }
                                        sup = cpc.super_name().map(|s| s.to_string());
                                    }
                                }
                                if shadow {
                                    break;
                                }
                                match cur.rfind('$') {
                                    Some(i) => cur.truncate(i),
                                    None => break,
                                }
                            }
                            !shadow
                        };
                    if !enclosing_static
                        && (cls != &self.pc.internal_name || shadowed_by_local)
                    {
                        out.push_str(&self.shorten(cls));
                        out.push('.');
                    }
                    out.push_str(name);
                } else if self.private_super_field(
                    cls,
                    name,
                    &Expr::This,
                ) {
                    out.push_str("((");
                    out.push_str(&self.shorten(cls));
                    out.push_str(") this).");
                    out.push_str(name);
                } else {
                    out.push_str("this.");
                    out.push_str(name);
                }
            }
            Expr::Method { owner, cls, name, desc, args, is_static, is_special, is_super, type_args, .. } => {
                // Signature-polymorphic calls need the descriptor return cast
                // in source form (see classdec::polymorphic_ret_cast) — except
                // at the root of an expression statement, where the bare call
                // is the only legal form. Consume the flag so a poly call
                // NESTED in the args still gets its cast.
                let bare_stmt_root = self.suppress_poly_cast;
                self.suppress_poly_cast = false;
                if !bare_stmt_root {
                    if let Some(t) = crate::classdec::polymorphic_ret_cast(cls, name, desc) {
                        out.push('(');
                        out.push_str(&self.type_name(&crate::expr::TypeRef::J(t)));
                        out.push_str(") ");
                    }
                }
                if name == "<init>" && *is_special {
                    // super(...) / this(...)
                    let is_super_form = *is_super || cls != &self.pc.internal_name;
                    // Qualified super for a STATIC class extending an
                    // INNER superclass: javac synthesizes the enclosing
                    // instance as the ctor's first param, and the source
                    // form is `outer.super(rest)` (jdk11/17/26
                    // BoundMethodHandle.SpeciesData extends
                    // ClassSpecializer<..>.SpeciesData — plain
                    // super(outer, key) is "需要包含..的封闭实例" x3 trees).
                    let qualified_outer = if is_super_form
                        && !args.is_empty()
                        && cls.contains('$')
                        && !crate::classdec::class_has_this0(self.pc)
                    {
                        let enclosing = cls.rsplit_once('$').map(|(o, _)| o.to_string());
                        match (enclosing, self.pool.get(cls)) {
                            (Some(enc), Some(spc))
                                if crate::classdec::class_has_this0(&spc)
                                    && crate::classdec::is_subtype_of(
                                        self.pool,
                                        &args[0].type_ref().erased(),
                                        &enc,
                                    ) =>
                            {
                                Some(enc)
                            }
                            _ => None,
                        }
                    } else {
                        None
                    };
                    if qualified_outer.is_some() {
                        self.expr(&args[0], 15, out);
                        out.push_str(".super(");
                    } else if is_super_form {
                        out.push_str("super(");
                    } else {
                        out.push_str("this(");
                    }
                    // Typed rendering: boolean/char params must not receive
                    // raw 0/1 int constants (`this(refKind, false)`). The
                    // methodref's descriptor `desc.args` is the EXACT invoked
                    // ctor signature, so prefer it over `ctor_param_types`
                    // (which matches by arg count and picks the wrong
                    // overload when a class has several ctors of equal arity,
                    // e.g. jdk26 Thread(ThreadGroup,Runnable,String,long,
                    // boolean) vs (...,long,Thread[])).
                    let _ = is_super_form;
                    // Upcast restoration only for SELF delegation: this(..)
                    // overload resolution binds the arg's static type (a
                    // JarEntry arg would recurse into JarEntry(JarEntry)
                    // instead of the descriptor's JarEntry(ZipEntry)).
                    // super(..) resolution is unambiguous through the
                    // generic formals — casting there broke FindOps
                    // `super(parent, spliterator)` (K := FindTask<..>
                    // accepts the arg fine; the raw erasure cast does not).
                    if qualified_outer.is_some() {
                        if desc.args.len() == args.len() && desc.args.len() >= 1 {
                            self.args_typed(&args[1..], &desc.args[1..], out);
                        } else {
                            self.args(&args[1..], out);
                        }
                    } else if desc.args.len() == args.len() {
                        if is_super_form {
                            self.args_typed(args, &desc.args, out);
                        } else {
                            self.args_delegation(args, &desc.args, out);
                        }
                    } else if !is_super_form {
                        // desc is the EXACT invoked ctor signature and the
                        // args are outer-stripped: args_delegation aligns
                        // by tail (jdk11 ZipFileInflaterInputStream —
                        // ctor_param_types' arity match would pick the
                        // wrong same-arity overload and cast against
                        // shifted formals, (ZipFile) zfin x3).
                        self.args_delegation(args, &desc.args, out);
                    } else {
                        match self.ctor_param_types(cls, 0, args.len(), args) {
                            Some(pt) if pt.len() == args.len() => {
                                self.args_typed(args, &pt, out)
                            }
                            _ => self.args(args, out),
                        }
                    }
                    out.push(')');
                } else {
                    if *is_super {
                        // invokespecial on `this` targeting another class:
                        // a superclass method call. Interface targets are
                        // qualified `Iface.super.m()` (JDK8 default-method
                        // invocations from implementors).
                        let itf = self
                            .pool
                            .get(cls)
                            .map(|cpc| {
                                cpc.cf.access_flags.contains(
                                    jcdc_classfile::ClassAccessFlags::INTERFACE,
                                )
                            })
                            .unwrap_or(false);
                        if itf {
                            out.push_str(&self.shorten(cls));
                            out.push('.');
                        }
                        out.push_str("super.");
                    } else if let Some(o) = owner {
                        if let Expr::Lambda(l) = o.as_ref() {
                            // A lambda RECEIVER needs the source's SAM cast
                            // (`((BooleanSupplier) () -> ..).getAsBoolean()`
                            // — a bare lambda cannot own a call: 此处不应为
                            // lambda 表达式, jdk26 Proxy assert).
                            if !l.sam_cls.is_empty() {
                                out.push_str("((");
                                out.push_str(&self.shorten(&l.sam_cls));
                                out.push_str(") ");
                                self.expr(o, 14, out);
                                out.push_str(").");
                            } else {
                                self.expr(o, 15, out);
                                out.push('.');
                            }
                        } else if matches!(o.as_ref(), Expr::Raw(t) if t == "\u{3}") {
                            // Outer anonymous member call: unqualified
                            // lexical resolution.
                        } else if self.needs_owner_cast(cls, name, desc, o) {
                            // Private / cross-package members are NOT
                            // inherited by the receiver's static type:
                            // the source cast to the declaring class
                            // (`((ZipFile) jar).getManifestNum()`) leaves
                            // no bytecode trace when the receiver is
                            // already a subtype.
                            out.push_str("((");
                            out.push_str(&self.shorten(cls));
                            out.push_str(") ");
                            self.expr(o, 14, out);
                            out.push_str(").");
                        } else {
                            self.expr(o, 15, out);
                            out.push('.');
                        }
                    } else if *is_static && (cls != &self.pc.internal_name || !type_args.is_empty())
                    {
                        // A static member of an ENCLOSING class resolves
                        // through lexical scope unqualified — and the
                        // qualified form is a TRAP when a field/local is
                        // named after the class: expression-name
                        // resolution prefers variables, so jdk26
                        // HPKE$Impl's `private static final byte[] HPKE`
                        // hijacked `HPKE.usePSK(psk)` into a member
                        // lookup on the array (找不到符号 方法
                        // usePSK(SecretKey) 位置: 类型为byte[]的变量
                        // HPKE). Keep the qualifier when an own or
                        // intermediate class declares a same-named
                        // method (real member shadowing) or when type
                        // witnesses need an explicit receiver.
                        let enclosing_static = type_args.is_empty()
                            && self.pc.internal_name.starts_with(&format!("{}$", cls))
                            && {
                                let mut cur = self.pc.internal_name.clone();
                                let mut shadow = false;
                                while cur != *cls {
                                    // Inherited members shadow too: the
                                    // lexical member scope of a class
                                    // includes its whole superclass chain
                                    // (jdk26 GaloisCounterMode$GCMDecrypt
                                    // extends GCMEngine, whose own
                                    // implGCMCrypt(ByteBuffer,..) hijacks
                                    // the bare 9-arg call to the OUTER
                                    // static — 无法将方法应用到给定类型).
                                    let mut sup = Some(cur.clone());
                                    while let Some(c) = sup.take() {
                                        if let Some(cpc) = self.pool.get(&c) {
                                            if (0..cpc.cf.methods.len()).any(|mi| {
                                                cpc.method_name(mi) == Some(name.as_str())
                                            }) {
                                                shadow = true;
                                                break;
                                            }
                                            sup = cpc.super_name().map(|s| s.to_string());
                                        }
                                    }
                                    if shadow {
                                        break;
                                    }
                                    match cur.rfind('$') {
                                        Some(i) => cur.truncate(i),
                                        None => break,
                                    }
                                }
                                !shadow
                            };
                        if !enclosing_static {
                            out.push_str(&self.shorten(cls));
                            out.push('.');
                        }
                    } else if !type_args.is_empty() {
                        // Type witnesses require an explicit receiver.
                        out.push_str("this.");
                    }
                    if !type_args.is_empty() {
                        out.push('<');
                        out.push_str(&type_args.join(", "));
                        out.push('>');
                    }
                    out.push_str(name);
                    out.push('(');
                    // Lambda args of a GENERIC call: prime each one's
                    // body-return cast from the instantiated formal's SAM
                    // return (jdk17 AbstractPipeline.opEvaluateParallelLazy:
                    // `i -> (E_OUT[]) new Object[i]` — the erasure-equal
                    // cast leaves no bytecode trace and without it the
                    // IntFunction<E_OUT[]> formal starves: Object[]无法
                    // 转换为E_OUT[]).
                    let sam_rets: Vec<Option<TypeRef>> = {
                        let mut v: Vec<Option<TypeRef>> =
                            std::iter::repeat_with(|| None).take(args.len()).collect();
                        if crate::classdec::is_generic_call(e, self.pool) {
                            if let Some((formals, mtvars)) =
                                crate::classdec::generic_call_formals(e, self.pool, self.pc)
                            {
                                if formals.len() == args.len() {
                                    for (i, (a, f)) in
                                        args.iter().zip(formals.iter()).enumerate()
                                    {
                                        // A raw-SAM-cast wrapper still
                                        // exposes the lambda (the overload
                                        // disambiguation cast; the primed
                                        // body return types the lambda
                                        // precisely).
                                        let a_inner = match a {
                                            Expr::Cast { e: ce, .. } => ce.as_ref(),
                                            other => other,
                                        };
                                        if let Expr::Lambda(l) = a_inner {
                                            // A formal still carrying the
                                            // callee's own method typevars
                                            // is not denotable at this
                                            // call site.
                                            if crate::classdec::g_mentions_any(f, &mtvars) {
                                                continue;
                                            }
                                            v[i] = self.sam_ret_cast(f, &l.sam_name);
                                        }
                                    }
                                }
                            }
                        }
                        v
                    };
                    if sam_rets.iter().any(|x| x.is_some()) {
                        self.args_typed_sam(args, &desc.args, &sam_rets, out);
                    } else {
                        self.args_typed(args, &desc.args, out);
                    }
                    out.push(')');
                }
            }
            Expr::ArrayIndex { array, index } => {
                self.expr(array, 15, out);
                out.push('[');
                // Array indexes are int by definition: a long-typed index
                // local (slot-sharing/merge typed the foreach lowering's
                // counter long — jdk26 Files.copy `options[i]`,
                // 从long转换到int可能会有损失) needs the narrowing cast.
                let idx_ty = match &**index {
                    Expr::Local { var, .. } => self.vt.var(*var).ty.erased(),
                    other => other.type_ref().erased(),
                };
                if matches!(idx_ty, jcdc_jvm::JavaType::Long) {
                    out.push_str("(int) ");
                }
                self.expr(index, 1, out);
                out.push(']');
            }
            Expr::Cast { ty, e } => {
                // `(T) (Serializable) lambda` is invalid Java: the source
                // form of a serializable-lambda cast is the intersection
                // `(T & Serializable) lambda`.
                if let Expr::Cast { ty: inner_ty, e: inner_e } = &**e {
                    let is_serializable = |t: &crate::expr::TypeRef| {
                        t.erased() == jcdc_jvm::JavaType::Object("java/io/Serializable".into())
                    };
                    if matches!(&**inner_e, Expr::Lambda(_)) && is_serializable(inner_ty) {
                        out.push('(');
                        out.push_str(&self.type_name(ty));
                        out.push_str(" & ");
                        out.push_str(&self.type_name(inner_ty));
                        out.push_str(") ");
                        self.expr(inner_e, 14, out);
                        return;
                    }
                }
                // CLASS-argument generic casts only: a TYPEVAR cast is
                // load-bearing (`(T) new SimpleEntry<>(..)` — jdk11
                // IdentityHashMap.toArray: the diamond infers from the
                // ctor args and the unchecked (T) makes the T[] store
                // legal; dropping it left the diamond to infer from the
                // array target T — 无法推断SimpleEntry<>的类型参数).
                if let (TypeRef::G(jcdc_jvm::GenericType::Class(_)), Expr::New { cls, .. }) =
                    (ty, &**e)
                {
                    if !self.diamond_for(cls).is_empty() {
                        // Synthetic generics-only cast around a diamond new:
                        // DROP the cast and keep the diamond. A generic-typed
                        // cast is always jcdc's own witness (a real checkcast
                        // carries only erasure), and every cast form loses
                        // here: with the diamond the cast starves inference
                        // (`(PendingFuture<Void,A>) new PendingFuture<>(..)`
                        // infers Object bounds and fails the cast), and the
                        // bare/raw form makes the whole creation raw so
                        // method-ref/lambda arguments stop type-checking
                        // (jdk17 Collectors `(Collector<T,?,C>) new
                        // CollectorImpl(.., Collection::add, ..)`). Cast-free
                        // `return new CollectorImpl<>(..)` / `x = new
                        // PendingFuture<>(..)` target-types the diamond —
                        // the source shape.
                        self.expr(e, outer_prec, out);
                        return;
                    }
                }
                out.push('(');
                out.push_str(&self.type_name(ty));
                out.push_str(") ");
                // Inconvertible direct casts from mis-joined stack-merge
                // vars (jdk26 AnnotationReader: `(SupertypeTarget)
                // var3_341` with var3 typed Iterator — sealed targets
                // reject the cross-cast): relay through Object, which is
                // always legal and semantically identical (the runtime
                // value IS the target type).
                if self.needs_object_relay(ty, e) {
                    out.push_str("(Object) ");
                }
                if matches!(&**e, Expr::New { .. }) {
                    self.suppress_diamond = true;
                }
                if let (TypeRef::G(g), Expr::Lambda(l)) = (ty, &**e) {
                    self.lambda_sam_ret = self.sam_ret_cast(g, &l.sam_name);
                }
                self.expr(e, 14, out);
                self.suppress_diamond = false;
                self.lambda_sam_ret = None;
            }
            Expr::InstanceOf { e, ty } => {
                self.expr(e, 10, out);
                out.push_str(" instanceof ");
                out.push_str(&self.type_name(ty));
            }
            Expr::Un { op, e } => {
                out.push_str(match op {
                    UnOp::Neg => "-",
                    UnOp::Not => "!",
                    UnOp::BitNot => "~",
                });
                self.expr(e, 14, out);
            }
            Expr::Bin { op, l, r, .. } => {
                // Boolean context special cases: `b == 0` → `!b`. A
                // Local's embedded type can be stale (booleanize retypes
                // the VarTable), and a boolified bitwise bin over
                // bool-ish operands is boolean too (jdk26
                // LinkedTransferQueue `(spin & !upc) == 0` — the frozen-Int
                // And with an int-form ternary side printed
                // `spin & (!upc ? 1 : 0)`: boolean & int).
                let lt = match &**l {
                    Expr::Local { var, .. } => self.vt.var(*var).ty.erased(),
                    other => other.type_ref().erased(),
                };
                let l_bool = lt == JavaType::Boolean;
                let l_boolish = l_bool || self.bool_ish_vt(l);
                if matches!(op, BinOp::Eq | BinOp::Ne | BinOp::RefEq | BinOp::RefNe)
                    && l_boolish
                {
                    if let Expr::Const(ConstVal::Int(n)) = &**r {
                        let polarity = matches!(op, BinOp::Eq | BinOp::RefEq);
                        let want_true = (*n != 0) == polarity;
                        if !want_true {
                            out.push('!');
                        }
                        if l_bool {
                            self.expr(l, 14, out);
                        } else {
                            // Composite boolean (a bitwise bin): parenthesize
                            // so a leading `!` binds the whole value.
                            out.push('(');
                            self.expr_bool(l, out);
                            out.push(')');
                        }
                        if parens {
                            out.push(')');
                        }
                        return;
                    }
                }
                // Mixed boolean/int equality on non-constants (stack-merge
                // vars of an assert desugaring: jdk26 VirtualThread
                // `stack38 == stack39` with stack38 boolean, stack39 int
                // 0/1 — "boolean和int不可比较"): normalize the int side
                // through `!= 0`.
                {
                    let rt = r.type_ref().erased();
                    if matches!(op, BinOp::Eq | BinOp::Ne)
                        && ((lt == jcdc_jvm::JavaType::Boolean
                            && rt == jcdc_jvm::JavaType::Int)
                            || (lt == jcdc_jvm::JavaType::Int
                                && rt == jcdc_jvm::JavaType::Boolean))
                    {
                        for (i, side) in [l, r].iter().enumerate() {
                            if i > 0 {
                                out.push(' ');
                                out.push_str(op.symbol());
                                out.push(' ');
                            }
                            if side.type_ref().erased() == jcdc_jvm::JavaType::Boolean {
                                self.expr_bool(side, out);
                            } else {
                                out.push('(');
                                self.expr(side, 1, out);
                                out.push_str(" != 0)");
                            }
                        }
                        if parens {
                            out.push(')');
                        }
                        return;
                    }
                }
                let p = op.precedence();
                self.expr(l, p, out);
                out.push(' ');
                out.push_str(op.symbol());
                out.push(' ');
                self.expr(r, p + 1, out);
            }
            Expr::Cond { c, t, f } => {
                self.expr(c, 3, out);
                out.push_str(" ? ");
                let prev = std::mem::replace(&mut self.in_cond, true);
                self.expr(t, 2, out);
                out.push_str(" : ");
                self.expr(f, 2, out);
                self.in_cond = prev;
            }
            Expr::Assign { target, op, value } => {
                // The local's VarTable type is authoritative: booleanize
                // flips vt types after the embedded Local tys were frozen
                // (Security `boolean var4_122 = 1` printed the int form —
                // "int无法转换为boolean").
                let tgt_er = match &**target {
                    Expr::Local { var, .. } => self.vt.var(*var).ty.erased(),
                    other => other.type_ref().erased(),
                };
                self.expr(target, 1, out);
                out.push(' ');
                out.push_str(op.symbol());
                out.push(' ');
                if matches!(op, crate::expr::AssignOp::Plain) {
                    // Narrow-target assignments render int constants in the
                    // target's form (jdk11/17/26 xml Parser: `mESt = ch !=
                    // 116 ? 512 : 60` against `private char mESt` —
                    // "从int转换到char可能会有损失").
                    match tgt_er {
                        jcdc_jvm::JavaType::Boolean => self.expr_bool(value, out),
                        jcdc_jvm::JavaType::Char => self.expr_char(value, out),
                        jcdc_jvm::JavaType::Byte => {
                            self.expr_narrow(value, &jcdc_jvm::JavaType::Byte, out)
                        }
                        jcdc_jvm::JavaType::Short => {
                            self.expr_narrow(value, &jcdc_jvm::JavaType::Short, out)
                        }
                        _ => self.expr(value, 1, out),
                    }
                } else {
                    self.expr(value, 1, out);
                }
            }
            Expr::PreIncDec { e, delta, .. } => {
                out.push_str(if *delta > 0 { "++" } else { "--" });
                self.expr(e, 14, out);
            }
            Expr::PostIncDec { e, delta, .. } => {
                self.expr(e, 14, out);
                out.push_str(if *delta > 0 { "++" } else { "--" });
            }
            Expr::Lambda(l) => self.lambda(l, out),
            Expr::AnonNew { base, args, body, .. } => {
                out.push_str("new ");
                let base_s = self.type_name(base);
                out.push_str(&base_s);
                out.push('(');
                // Render the ctor args through the base class's matching
                // <init> descriptor: an int 0/1 at a boolean parameter
                // must print as false/true (jdk11 Console's anonymous
                // PrintWriter subclass — `new PrintWriter(out, 1)` finds
                // no ctor). Pick the arity-matching ctor whose param
                // erasures best fit the actual arg types.
                let base_internal = match base {
                    TypeRef::J(jcdc_jvm::JavaType::Object(n)) => Some(n.clone()),
                    TypeRef::G(jcdc_jvm::GenericType::Class(cs)) => {
                        Some(crate::method::classsig_internal(cs))
                    }
                    _ => None,
                };
                let ctor_params = base_internal.and_then(|bi| {
                    let bpc = self.pool.get(&bi)?;
                    let mut best: Option<(usize, Vec<jcdc_jvm::JavaType>)> = None;
                    for mi in 0..bpc.cf.methods.len() {
                        if bpc.method_name(mi) != Some("<init>") {
                            continue;
                        }
                        let d = bpc.method_desc(mi)?;
                        let md = jcdc_jvm::parse_method_descriptor(d)?;
                        if md.args.len() != args.len() {
                            continue;
                        }
                        let score = md
                            .args
                            .iter()
                            .zip(args.iter())
                            .filter(|(pt, a)| {
                                matches!(a.type_ref().erased(), jcdc_jvm::JavaType::Object(an)
                                    if matches!(pt, jcdc_jvm::JavaType::Object(pn) if pn == &an))
                                    || (matches!(pt, jcdc_jvm::JavaType::Boolean)
                                        && matches!(a, Expr::Const(ConstVal::Int(0 | 1))))
                            })
                            .count();
                        if best.as_ref().map(|(s, _)| score > *s).unwrap_or(true) {
                            best = Some((score, md.args));
                        }
                    }
                    best.map(|(_, a)| a)
                });
                match ctor_params {
                    Some(pt) => self.args_typed(args, &pt, out),
                    None => self.args(args, out),
                }
                out.push_str(") {\n");
                for line in body.lines() {
                    for _ in 0..self.indent + 1 {
                        out.push_str("    ");
                    }
                    out.push_str(line.trim_start_matches(' '));
                    out.push('\n');
                }
                for _ in 0..self.indent {
                    out.push_str("    ");
                }
                out.push('}');
            }
            Expr::StringConcat(parts) => {
                let mut first = true;
                // Java semantics: the concatenation must start with a String.
                let needs_prefix = !matches!(parts.first(), Some(ConcatPart::Const(_)));
                if needs_prefix {
                    out.push_str("\"\"");
                    first = false;
                }
                for p in parts {
                    // Right-hand operands of `+` need parens at equal
                    // precedence to keep arithmetic grouping (`"t" + (x+1)`).
                    let is_first = first;
                    if !first {
                        out.push_str(" + ");
                    }
                    first = false;
                    match p {
                        ConcatPart::Const(s) => {
                            out.push('"');
                            out.push_str(&escape_string(s));
                            out.push('"');
                        }
                        ConcatPart::Str(e) => self.expr(e, if is_first { 12 } else { 13 }, out),
                    }
                }
                if parts.is_empty() {
                    out.push_str("\"\"");
                }
            }
            Expr::Invokedynamic { name, args, bsm_text, .. } => {
                if name.starts_with('\u{0}') {
                    out.push_str("/*bad-cmp*/0");
                } else {
                    out.push_str("/* invokedynamic ");
                    out.push_str(name);
                    out.push(' ');
                    out.push_str(bsm_text);
                    out.push_str(" */ (");
                    self.args(args, out);
                    out.push(')');
                }
            }
        }
        if parens {
            out.push(')');
        }
    }

    fn args(&mut self, args: &[Expr], out: &mut String) {
        for (i, a) in args.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            self.expr(a, 1, out);
        }
    }

    /// Print call args applying boolean-parameter constant adjustment.
    /// Delegation (this(..)/super(..)) args: typed rendering PLUS the
    /// elided-upcast restoration when the arg's static type differs from
    /// the descriptor formal — overload resolution binds the arg's type,
    /// not the descriptor (jdk17 JarEntry copy ctor: `this(je)` resolves
    /// recursively to JarEntry(JarEntry); the source `this((ZipEntry) je)`
    /// upcast is elided from bytecode because je <: ZipEntry is provable).
    fn args_delegation(
        &mut self,
        args: &[Expr],
        param_types: &[jcdc_jvm::JavaType],
        out: &mut String,
    ) {
        // Inner-class ctor descriptors carry the synthetic outer param
        // while the expression args are outer-stripped: align the formals
        // with the TRAIL of the args, like apply_ctor_param_casts (jdk11
        // ZipFileInflaterInputStream this(zfin, res, res.getInflater(),
        // size) was cast against the shifted descriptor formals —
        // (ZipFile) zfin, (ZipFileInputStream) res... x3 inconvertible).
        let off = param_types.len().saturating_sub(args.len());
        for (i, a) in args.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            match param_types.get(off + i) {
                Some(pt @ jcdc_jvm::JavaType::Object(_)) => {
                    let have = a.type_ref().erased();
                    // Generically-typed args (typevars/parameterized) are
                    // already source-typed: casting them to the descriptor
                    // erasure breaks convertibility to typevar formals
                    // (jdk17 StreamSpliterators SliceSpliterator.OfPrimitive
                    // this((Spliterator.OfPrimitive) s, ..) against a
                    // T_SPLITR formal — OfPrimitive无法转换为T_SPLITR).
                    if &have != pt
                        && !matches!(a.type_ref(), TypeRef::G(_))
                        && !matches!(
                            a,
                            Expr::Cast { .. }
                                | Expr::Const(_)
                                | Expr::Lambda(_)
                                | Expr::New { .. }
                                | Expr::AnonNew { .. }
                        )
                    {
                        out.push('(');
                        out.push_str(&self.type_name(&TypeRef::J(pt.clone())));
                        out.push_str(") ");
                        self.expr(a, 14, out);
                        continue;
                    }
                    self.expr(a, 1, out);
                }
                Some(jcdc_jvm::JavaType::Boolean) => self.expr_bool(a, out),
                Some(jcdc_jvm::JavaType::Char) => self.expr_char(a, out),
                Some(pt @ (jcdc_jvm::JavaType::Byte | jcdc_jvm::JavaType::Short)) => {
                    self.expr_narrow_arg(a, pt, out)
                }
                _ => self.expr(a, 1, out),
            }
        }
    }

    fn args_typed(&mut self, args: &[Expr], param_types: &[jcdc_jvm::JavaType], out: &mut String) {
        self.args_typed_sam(args, param_types, &[], out)
    }

    /// args_typed with per-argument SAM-return priming: a lambda actual at
    /// a parameterized-SAM formal of a pinned generic ctor gets its body
    /// return cast from the formal's instantiated SAM return (jdk11/17/26
    /// Collectors.toUnmodifiable*'s finisher `list -> (List<T>)
    /// List.of(list.toArray())` — the erased instantiatedMethodType says
    /// only List, so the generic cast is recoverable solely from the
    /// diamond's resolved formal).
    fn args_typed_sam(
        &mut self,
        args: &[Expr],
        param_types: &[jcdc_jvm::JavaType],
        sam_rets: &[Option<TypeRef>],
        out: &mut String,
    ) {
        for (i, a) in args.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            match param_types.get(i) {
                Some(jcdc_jvm::JavaType::Boolean) => self.expr_bool(a, out),
                // Char/narrow params: expr_char/expr_narrow render both
                // constants AND conditional branches in the target form
                // (jdk17 BasicAuthentication `super(!isProxy ? 115 : 112,
                // ..)` — the char param needs `!isProxy ? 's' : 'p'`;
                // a plain int ternary is "条件表达式中的类型错误").
                Some(jcdc_jvm::JavaType::Char) => self.expr_char(a, out),
                // Byte/short parameters: an int literal argument needs an
                // explicit cast (invocation conversion never narrows, even
                // for in-range constants) — and so do the branches of an
                // int conditional (jdk CompressedResourceHeader
                // `buffer.put(isTerminal ? (byte) 1 : (byte) 0)` — the
                // byte casts fold away in bytecode; a bare int ternary is
                // "对于put(int), 找不到合适的方法" x3 trees).
                Some(jcdc_jvm::JavaType::Byte) | Some(jcdc_jvm::JavaType::Short) => {
                    self.expr_narrow_arg(a, &param_types[i].clone(), out);
                }
                _ => {
                    let lam_under_cast = matches!(a, Expr::Lambda(_))
                        || matches!(a, Expr::Cast { e: ce, .. } if matches!(&**ce, Expr::Lambda(_)));
                    match sam_rets.get(i).and_then(|x| x.as_ref()) {
                        Some(t) if lam_under_cast => {
                            let prev = self.lambda_sam_ret.replace(t.clone());
                            self.expr(a, 1, out);
                            self.lambda_sam_ret = prev;
                        }
                        _ => self.expr(a, 1, out),
                    }
                }
            }
        }
    }

    fn const_val(&self, c: &ConstVal, out: &mut String) {
        match c {
            ConstVal::Int(i) => out.push_str(&i.to_string()),
            ConstVal::Long(l) => {
                if *l == i64::MIN {
                    out.push_str("-9223372036854775808L");
                } else {
                    out.push_str(&format!("{}L", l));
                }
            }
            ConstVal::Float(f) => out.push_str(&format_float(*f as f64, true)),
            ConstVal::Double(d) => out.push_str(&format_float(*d, false)),
            ConstVal::Str(s) => {
                out.push('"');
                out.push_str(&escape_string(s));
                out.push('"');
            }
            ConstVal::Null => out.push_str("null"),
            ConstVal::ClassLit(t) => {
                out.push_str(&self.type_name(t));
                out.push_str(".class");
            }
        }
    }

    fn lambda(&mut self, l: &crate::expr::LambdaExpr, out: &mut String) {
        // A `lambda$...` implementation method in the current class is a
        // compiler-generated lambda body, never a real method reference —
        // emit the body inline even when classified as a reference (the
        // method itself is hidden from the output).
        let synthetic_self_lambda =
            l.impl_name.starts_with("lambda$") && l.impl_owner == self.pc.internal_name;
        match l.kind {
            LambdaKind::MethodRef if !synthetic_self_lambda => {
                // Determine receiver form.
                if l.impl_name == "<init>" {
                    out.push_str(&self.shorten(&l.impl_owner));
                    out.push_str("::new");
                    return;
                }
                if let Some(recv) = &l.ref_receiver {
                    out.push_str(&self.shorten(recv));
                    out.push_str("::");
                    out.push_str(&l.impl_name);
                } else if !l.captures.is_empty() {
                    // bound receiver: first capture is the instance
                    self.expr(&l.captures[0], 15, out);
                    out.push_str("::");
                    out.push_str(&l.impl_name);
                } else {
                    out.push_str(&self.shorten(&l.impl_owner));
                    out.push_str("::");
                    out.push_str(&l.impl_name);
                }
            }
            _ => {
                if self.lambda_depth >= 8 {
                    out.push_str("/*nested-lambda*/null");
                    return;
                }
                // body: decompile the impl method if it lives in this class.
                let body_stmts = self
                    .pc
                    .find_own_method(&l.impl_name, &l.impl_desc.to_string())
                    .and_then(|mi| crate::method::decompile_method(self.pc, self.pool, mi).ok())
                    .flatten();
                // params: prefer the impl method's own LVT names so the
                // printed parameter list matches the body's references
                // (instance lambda impls carry only the SAM params).
                let mut pnames = l.param_names.clone();
                if let Some(MethodBody { vt, .. }) = &body_stmts {
                    let mut vt_params: Vec<String> = vt
                        .vars
                        .iter()
                        .filter(|v| v.is_param && v.name != "this")
                        .map(|v| v.name.clone())
                        .collect();
                    if vt_params.len() == pnames.len() {
                        pnames = vt_params;
                    } else if vt_params.len() > pnames.len() {
                        // The impl method's signature is (captures..., SAM
                        // params...): take the TRAILING SAM slice so the
                        // printed parameter list matches the body's variable
                        // references (ConcurrentMap.replaceAll printed
                        // `(x0, x1) -> { .. replace(k, v, ..) }` — undefined
                        // symbols; the captured `function` occupied the first
                        // impl slot, breaking the exact-length alignment).
                        let n = pnames.len();
                        pnames = vt_params.split_off(vt_params.len() - n);
                    }
                }
                let single = pnames.len() == 1;
                if !single {
                    out.push('(');
                }
                for (i, n) in pnames.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(n);
                }
                if !single {
                    out.push(')');
                }
                out.push_str(" -> ");
                let sam_wrap = self.lambda_sam_ret.take();
                match body_stmts {
                    Some(MethodBody { mut body, mut vt, .. }) => {
                        // A captured outer local may have been RENAMED by
                        // the outer method's lambda-scope disambiguation
                        // (hoisted decl vs a lambda-body local collision);
                        // the impl method's own LVT still carries the
                        // ORIGINAL name, and the printed body resolves
                        // lexically in the outer scope — sync the impl
                        // param names to the outer vt's current names
                        // (jdk26 UpcallLinker `doBindings` vs the renamed
                        // `doBindings$1` decls: 找不到符号 x2).
                        {
                            // Non-this impl params are [captures..., SAM
                            // params...]: the capture slice length is
                            // params - param_names (param_names is the
                            // indy's SAM arity; `this` is excluded from
                            // both sides). Walking captures against ALL
                            // params misaligns when the receiver rides in
                            // l.captures (default-method lambdas: the SAM
                            // param then takes a capture's name — jdk26
                            // Predicate.and printed `t -> test(other)`).
                            let nsam = l.param_names.len();
                            let pvars: Vec<u32> = vt
                                .vars
                                .iter()
                                .filter(|v| v.is_param && v.name != "this")
                                .map(|v| v.id)
                                .collect();
                            let ncaps = pvars.len().saturating_sub(nsam);
                            // An INSTANCE impl's captured receiver rides at
                            // captures[0] but `this` is excluded from
                            // pvars — offset the capture index (jdk26
                            // CompletionStage exceptionallyAsync: without
                            // it the executor param took fn's name).
                            let cap_off = if l.impl_is_static
                                || ncaps == l.captures.len()
                            {
                                0
                            } else {
                                l.captures.len().saturating_sub(ncaps)
                            };
                            for pi in 0..ncaps {
                                if let Some(crate::expr::Expr::Local { var, .. }) =
                                    l.captures.get(pi + cap_off)
                                {
                                    if let Some(outer) =
                                        self.vt.vars.iter().find(|ov| ov.id == *var)
                                    {
                                        if let Some(v) =
                                            vt.vars.iter_mut().find(|v| v.id == pvars[pi])
                                        {
                                            if outer.name != v.name {
                                                v.name = outer.name.clone();
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        // Apply capture-snapshot renames: captured outer
                        // locals that are not effectively final were
                        // snapshotted into `final` copies before this
                        // statement (classdec::fix_lambda_captures); the
                        // impl body must reference the copies.
                        if !l.capture_snaps.is_empty() {
                            let mut snap_vt = vt.clone();
                            for &(_, pid, ref snap) in &l.capture_snaps {
                                for v in snap_vt.vars.iter_mut() {
                                    if v.id == pid {
                                        v.name = snap.clone();
                                    }
                                }
                            }
                            vt = snap_vt;
                        }
                        // Pushdown-recipe repair (classdec::
                        // push_witness_into_branches): the impl body is
                        // decompiled fresh here, so registered branch
                        // repairs (drop erasure-raw casts, attach the
                        // enclosing return's witness) apply at this point.
                        if let Some((want, params)) =
                            crate::classdec::branch_witness_pushed(&l.impl_owner, &l.impl_name)
                        {
                            crate::classdec::repair_pushed_branches(
                                &mut body,
                                &want,
                                &params,
                                self.pool,
                            );
                        }
                        // Lambda impl params carry erased types (no LVTT
                        // on synthetic methods): lift generic types from
                        // the indy-site capture expressions, then restore
                        // comparison witnesses the erased types would
                        // starve (jdk26 Gatherers: `leftFinisher ==
                        // Gatherer.defaultFinisher()` inside the finisher
                        // lambdas — 不可比较的类型).
                        {
                            let mut pi = 0usize;
                            let mut lifted = 0usize;
                            for v in vt.vars.iter_mut() {
                                if v.is_param && v.name != "this" {
                                    if let Some(cap) = l.captures.get(pi) {
                                        let ct = cap.type_ref();
                                        if matches!(ct, TypeRef::G(_))
                                            && !matches!(v.ty, TypeRef::G(_))
                                        {
                                            v.ty = ct;
                                            lifted += 1;
                                        }
                                    }
                                    pi += 1;
                                }
                            }
                            if lifted > 0 {
                                let types: Vec<TypeRef> =
                                    vt.vars.iter().map(|vi| vi.ty.clone()).collect();
                                crate::method::rewrite_local_types(&mut body, &types);
                            }
                        }
                        crate::classdec::witness_comparison_operands(&mut body, None, self.pool);
                        crate::classdec::upgrade_typevar_array_casts(&mut body, self.pool, self.pc);
                        {
                            let fam = crate::classdec::Family::collect(self.pc, self.pool);
                            let _depth = crate::classdec::lambda_body_depth_enter();
                            crate::classdec::inline_anonymous(
                                &mut body,
                                self.pc,
                                self.pool,
                                &fam,
                                &vt,
                            );
                            // Lambda impl bodies decompiled HERE bypass
                            // emit_method_with, so the capture-snapshot
                            // pass never ran on them: an inner lambda
                            // capturing a multi-assigned local of THIS
                            // body rendered the raw name (jdk26
                            // MethodHandleProxies.createTemplate's
                            // withMethodBody/trying/catching lambdas
                            // capture the loop-reassigned `mi` —
                            // 从lambda表达式引用的本地变量必须是最终变量
                            // ×6). fix_lambda_captures inserts the
                            // `final T mi$capN = mi;` snapshots and
                            // registers the renames on the inner
                            // LambdaExprs before their own print-time
                            // decompile picks them up.
                            crate::classdec::fix_lambda_captures(
                                &mut body,
                                &mut vt,
                                self.pc,
                                self.pool,
                                &fam,
                            );
                        }
                        // Inner-class lambda impls read the synthetic
                        // outer field directly (`this.this$0.cp`): the
                        // body bypasses emit_method_with's outer-this
                        // substitution, so apply it here (jdk26
                        // ProxyGenerator ProxyMethod.generateMethod's
                        // withCode lambda — 13 "找不到符号 变量 this$0").
                        {
                            let outer_this = crate::classdec::outer_this_map(self.pc);
                            if !outer_this.is_empty() {
                                crate::classdec::substitute_captures(
                                    &mut body,
                                    &outer_this,
                                    self.pool,
                                );
                            }
                        }
                        crate::classdec::restore_enum_switches(&mut body, self.pc, self.pool);
                        crate::classdec::fold_restart_guards(&mut body);
                        // Nested calls inside lambda bodies need the same
                        // overload-disambiguation/instantiation witnesses
                        // as top-level method bodies (BootstrapLogger
                        // doPrivileged(() -> .., acc) stays ambiguous
                        // without the raw SAM cast).
                        crate::classdec::cast_wildcard_call_args(
                            &mut body,
                            self.pool,
                            self.pc,
                            &vt,
                            &[],
                        );
                        crate::method::prune_post_loop_label_breaks(&mut body);
                        crate::method::demote_undefined_label_jumps(&mut body);
                        crate::classdec::split_return_assigns(&mut body);
                        // Single-return body → expression lambda.
                        let mut single_expr = match &body {
                            Stmt::Return(Some(e)) => Some(e.clone()),
                            Stmt::Block(v) if v.len() == 1 => match &v[0] {
                                Stmt::Return(Some(e)) => Some(e.clone()),
                                _ => None,
                            },
                            _ => None,
                        };
                        // Witness the instantiated SAM return on the body's
                        // returns: the impl method is erased, so `i -> i`
                        // under `(Function<I,R>)` fails inference without
                        // `(R) i`.
                        fn sam_ok(t: &TypeRef, e: &Expr) -> bool {
                            !matches!(e, Expr::Cast { .. } | Expr::Const(_))
                                && e.type_ref() != *t
                        }
                        fn wrap_returns(s: &mut Stmt, t: &TypeRef) {
                            match s {
                                Stmt::Return(Some(e)) => {
                                    if sam_ok(t, e) {
                                        let v = std::mem::replace(e, Expr::This);
                                        *e = Expr::Cast { ty: t.clone(), e: Box::new(v) };
                                    }
                                }
                                Stmt::Block(v) => v.iter_mut().for_each(|x| wrap_returns(x, t)),
                                Stmt::If { then_stmt, else_stmt, .. } => {
                                    wrap_returns(then_stmt, t);
                                    if let Some(x) = else_stmt {
                                        wrap_returns(x, t);
                                    }
                                }
                                Stmt::While { body, .. }
                                | Stmt::DoWhile { body, .. }
                                | Stmt::ForEach { body, .. }
                                | Stmt::Labeled { body, .. }
                                | Stmt::Synchronized { body, .. } => wrap_returns(body, t),
                                Stmt::For { init, body, .. } => {
                                    init.iter_mut().for_each(|i| wrap_returns(i, t));
                                    wrap_returns(body, t);
                                }
                                Stmt::Switch { cases, default, .. } => {
                                    for c in cases.iter_mut() {
                                        for st in c.body.iter_mut() {
                                            wrap_returns(st, t);
                                        }
                                    }
                                    if let Some(d) = default {
                                        wrap_returns(d, t);
                                    }
                                }
                                Stmt::Try { body, catches, finally } => {
                                    wrap_returns(body, t);
                                    for c in catches.iter_mut() {
                                        wrap_returns(&mut c.body, t);
                                    }
                                    if let Some(f) = finally {
                                        wrap_returns(f, t);
                                    }
                                }
                                _ => {}
                            }
                        }
                        if let Some(t) = &sam_wrap {
                            if let Some(e) = &mut single_expr {
                                if sam_ok(t, e) {
                                    let v = std::mem::replace(e, Expr::This);
                                    *e = Expr::Cast { ty: t.clone(), e: Box::new(v) };
                                } else if let TypeRef::G(_) = t {
                                    // The body already carries the erasure
                                    // checkcast: retype it to the generic
                                    // SAM return (jdk26
                                    // CopyOnWriteArrayList.toArray `i ->
                                    // (T[]) new Object[i]` printed
                                    // `(Object[])` — Object[]无法转换为T[]
                                    // against IntFunction<T[]>).
                                    if let Expr::Cast { ty: ct, e: ce } = e {
                                        if ct.erased() == t.erased()
                                            && !matches!(&**ce, Expr::Cast { .. })
                                        {
                                            *ct = t.clone();
                                        }
                                    }
                                }
                            } else {
                                wrap_returns(&mut body, t);
                            }
                        } else if let Some(inst) = &l.inst_sam_desc {
                            if crate::dbg_flag!("JCDC_DBG_LAMRET") {
                                eprintln!(
                                    "LAMRET impl={}.{} inst_ret={:?} single={}",
                                    l.impl_owner,
                                    l.impl_name,
                                    inst.ret,
                                    single_expr.is_some()
                                );
                            }
                            // The invokedynamic's instantiatedMethodType
                            // records the lambda's inferred return at the
                            // call site; a source upcast can be elided from
                            // the bytecode when provable (jdk17
                            // JrtFileSystem.iteratorOf: `(Path)` around
                            // path.resolve(..) inside map(child -> ...) —
                            // JrtPath <: Path needs no checkcast, but
                            // without the cast map infers Stream<JrtPath>
                            // and .iterator() fails the Iterator<Path>
                            // return). Restore it when the expression body
                            // is typed a strict subtype of the recorded
                            // return.
                            fn upcast_ok(
                                e: &Expr,
                                target: &jcdc_jvm::JavaType,
                                pool: &ClassPool,
                            ) -> bool {
                                let jcdc_jvm::JavaType::Object(t) = target else {
                                    return false;
                                };
                                // A parameterized (generic) value whose
                                // erasure IS the target reaches it unchecked
                                // (jdk17 CompletionStage exceptionallyCompose:
                                // the cond branch fn.apply(ex) types as the
                                // capture ? extends CompletionStage<T>; the
                                // erased impl return CompletionStage needs no
                                // cast, and printing one breaks the outer
                                // chain's inference).
                                if let TypeRef::G(g0) = e.type_ref() {
                                    if let jcdc_jvm::GenericType::Class(cs) = &g0 {
                                        if crate::method::classsig_internal(cs) == *t {
                                            return true;
                                        }
                                    }
                                }
                                let jcdc_jvm::JavaType::Object(e0) = e.type_ref().erased() else {
                                    return false;
                                };
                                if &e0 == t {
                                    return false;
                                }
                                let mut queue = vec![e0];
                                let mut seen = std::collections::HashSet::new();
                                while let Some(cur) = queue.pop() {
                                    if !seen.insert(cur.clone()) {
                                        continue;
                                    }
                                    let Some(p) = pool.get(&cur) else { continue };
                                    for (sup, _) in crate::classdec::class_supers_args(&p, &[]) {
                                        if &sup == t {
                                            return true;
                                        }
                                        queue.push(sup);
                                    }
                                }
                                false
                            }
                            let want = TypeRef::J(inst.ret.clone());
                            // The sam_wrap prime (declared local / pinned
                            // ctor formal / generic-call formal) carries the
                            // GENERIC SAM return the erased
                            // instantiatedMethodType lost: upgrade an
                            // existing erasure-equal cast on the body (jdk26
                            // CopyOnWriteArrayList.toArray's `i -> (T[]) new
                            // Object[i]` printed `(Object[])` — the real
                            // checkcast erases T[] and Object[] alike;
                            // Object[]无法转换为T[] against
                            // IntFunction<T[]>).
                            let g_want: Option<TypeRef> = sam_wrap.as_ref().and_then(|t| {
                                if let TypeRef::G(g) = t {
                                    if TypeRef::G(g.clone()).erased() == inst.ret {
                                        return Some(t.clone());
                                    }
                                }
                                None
                            });
                            if let Some(e) = &mut single_expr {
                                if crate::dbg_flag!("JCDC_DBG_LAMRET") {
                                    eprintln!(
                                        "LAMRET2 inst_ret={:?} expr_ty={:?} sam_ok={} upcast_ok={} g_want={:?}",
                                        inst.ret,
                                        e.type_ref(),
                                        sam_ok(&want, e),
                                        upcast_ok(e, &inst.ret, self.pool),
                                        g_want
                                    );
                                }
                                let mut upgraded = false;
                                if let Some(gw) = &g_want {
                                    if let Expr::Cast { ty, e: ce } = e {
                                        if ty.erased() == inst.ret
                                            && !matches!(&**ce, Expr::Cast { .. })
                                        {
                                            *ty = gw.clone();
                                            upgraded = true;
                                        }
                                    }
                                }
                                if !upgraded && sam_ok(&want, e) && upcast_ok(e, &inst.ret, self.pool) {
                                    let v = std::mem::replace(e, Expr::This);
                                    *e = Expr::Cast { ty: want, e: Box::new(v) };
                                }
                            }
                        }
                        // A nested lambda body shares the ENCLOSING
                        // lambda's scope rules: its own locals must not
                        // redeclare names visible there (jdk26
                        // MethodHandleProxies.createTemplate — the clb
                        // lambda's foreach-desugared `i$`/`mi` collided
                        // with the nested cob lambda's own `i$`/`mi`,
                        // 已在方法中定义了变量 x2). Rename the inner
                        // impl's non-param locals on collision; the
                        // method-level twin is handled by
                        // disambiguate_lambda_locals.
                        {
                            let mut outer_names: std::collections::HashSet<&str> = self
                                .vt
                                .vars
                                .iter()
                                .map(|v| v.name.as_str())
                                .collect();
                            outer_names
                                .extend(self.outer_names.iter().map(|n| n.as_str()));
                            let mut used: std::collections::HashSet<String> =
                                vt.vars.iter().map(|v| v.name.clone()).collect();
                            for v in vt.vars.iter_mut() {
                                if v.is_param || !outer_names.contains(v.name.as_str()) {
                                    continue;
                                }
                                let base = v.name.clone();
                                let mut k = 1;
                                loop {
                                    let cand = format!("{}${}", base, k);
                                    if !used.contains(&cand)
                                        && !outer_names.contains(cand.as_str())
                                    {
                                        used.insert(cand.clone());
                                        v.name = cand;
                                        break;
                                    }
                                    k += 1;
                                }
                            }
                        }
                        let mut sub = Printer {
                            pc: self.pc,
                            pool: self.pool,
                            vt: &vt,
                            out: String::new(),
                            indent: self.indent,
                            lambda_depth: self.lambda_depth + 1,
                            outer_names: {
                                let mut n = self.outer_names.clone();
                                n.extend(self.vt.vars.iter().map(|v| v.name.clone()));
                                n
                            },
                            // The SAM's return type governs the impl
                            // body's renders: boolean SAMs must print
                            // `return true;` not the JVM-int `return 1;`
                            // (jdk26 Gatherers.fold's ofGreedy lambda).
                            ret_bool: l.sam_desc.ret == jcdc_jvm::JavaType::Boolean,
                            ret_char: l.sam_desc.ret == jcdc_jvm::JavaType::Char,
                            ret_byte: l.sam_desc.ret == jcdc_jvm::JavaType::Byte,
                            ret_short: l.sam_desc.ret == jcdc_jvm::JavaType::Short,
                            suppress_poly_cast: false,
                            suppress_diamond: false,
                            // A lambda body is a fresh expression context:
                            // the enclosing conditional's pre-8 non-poly
                            // rule does not propagate into it (the lambda
                            // is a standalone method body).
                            in_cond: false,
                            lambda_sam_ret: None,
                            ret_sam: None,
                        };
                        if let Some(e) = single_expr {
                            if l.sam_desc.ret == jcdc_jvm::JavaType::Boolean {
                                sub.expr_bool(&e, out);
                            } else {
                                sub.expr(&e, 1, out);
                            }
                        } else {
                            out.push_str("{\n");
                            sub.indent += 1;
                            sub.stmt(&body);
                            let text = sub.out;
                            out.push_str(&text);
                            for _ in 0..self.indent {
                                out.push_str("    ");
                            }
                            out.push('}');
                        }
                    }
                    None => {
                        out.push_str("/* lambda body in ");
                        out.push_str(&l.impl_owner);
                        out.push('.');
                        out.push_str(&l.impl_name);
                        out.push_str(" */ {}");
                    }
                }
            }
        }
    }

    // ---------------- names & types ----------------

    /// True if `cls` is a member inner class (declares this$0) per the pool.
    /// Parameter types of the `<init>` matching `skip + n` descriptor args,
    /// returning the tail after `skip` leading synthetic params. Used to
    /// print `new` arguments with boolean/char constant adjustment.
    fn ctor_param_types(
        &self,
        cls: &str,
        skip: usize,
        n: usize,
        args: &[Expr],
    ) -> Option<Vec<jcdc_jvm::JavaType>> {
        let pcx = self.pool.get(cls)?;
        // Enum ctors carry the implicit (String name, int ordinal) prefix.
        let extra: usize = if pcx.is_enum() { 2 } else { 0 };
        // Inner/local classes capture the enclosing instance as a leading
        // ctor param (this$0 field proves it) that the printed new-site
        // omits: fall back to skipping it so the formals line up (jdk11
        // BitSet$1BitSetSpliterator(BitSet,int,int,int,boolean) — the
        // boolean formal rendered its arg as `0`).
        let has_this0 = pcx.cf.fields.iter().any(|f| {
            pcx.utf8(f.name_index)
                .map(|nm| nm.starts_with("this$"))
                .unwrap_or(false)
        });
        let mut cands: Vec<Vec<jcdc_jvm::JavaType>> = Vec::new();
        for mi in 0..pcx.cf.methods.len() {
            if pcx.method_name(mi) != Some("<init>") {
                continue;
            }
            let d = pcx.method_desc(mi)?;
            if let Some(md) = jcdc_jvm::parse_method_descriptor(d) {
                if md.args.len() == skip + extra + n {
                    cands.push(md.args[skip + extra..].to_vec());
                }
            }
        }
        // jdk21+ javac forwards the enclosing instance straight to super
        // WITHOUT an own this$0 field (jdk26 CallArranger
        // BoxBindingCalculator: super(this$0param, forArguments, false)
        // with the outer arg later stripped — the untyped fallback
        // printed the boolean formal's `0`). Treat a leading
        // enclosing-class formal as the synthetic outer param too.
        let enclosing = cls.rsplit_once('$').map(|(o, _)| o.to_string());
        if cands.is_empty() && skip == 0 {
            for mi in 0..pcx.cf.methods.len() {
                if pcx.method_name(mi) != Some("<init>") {
                    continue;
                }
                let d = pcx.method_desc(mi)?;
                if let Some(md) = jcdc_jvm::parse_method_descriptor(d) {
                    if md.args.len() == extra + n + 1 {
                        let outer_first = match (&enclosing, md.args.first()) {
                            (Some(enc), Some(jcdc_jvm::JavaType::Object(nm))) => nm == enc,
                            _ => false,
                        };
                        if has_this0 || outer_first {
                            cands.push(md.args[extra + 1..].to_vec());
                        }
                    }
                }
            }
        }
        match cands.len() {
            0 => None,
            1 => Some(cands.pop().unwrap()),
            _ => {
                // Same-arity overloads (jdk11 System: PrintStream(OS,Z) vs
                // PrintStream(OS,String) — picking the first rendered the
                // boolean `true` as `1`: "no suitable constructor
                // PrintStream(BufferedOutputStream,int)"). Score by
                // argument compatibility; fall back to the first.
                fn arg_fits(a: &Expr, p: &jcdc_jvm::JavaType) -> bool {
                    use jcdc_jvm::JavaType as J;
                    match (a, p) {
                        (Expr::Const(ConstVal::Int(_)), J::Boolean | J::Byte | J::Short | J::Char | J::Int | J::Long | J::Float | J::Double) => true,
                        (Expr::Const(ConstVal::Long(_)), J::Long | J::Float | J::Double) => true,
                        (Expr::Const(ConstVal::Float(_)), J::Float | J::Double) => true,
                        (Expr::Const(ConstVal::Double(_)), J::Double) => true,
                        (Expr::Const(ConstVal::Str(_)), J::Object(nm)) => nm == "java/lang/String",
                        (Expr::Const(ConstVal::Null), J::Object(_) | J::Array(_)) => true,
                        (Expr::Const(_), _) => false,
                        (other, p) => {
                            let have = other.type_ref().erased();
                            match (&have, p) {
                                (J::Object(x), J::Object(y)) => x == y,
                                (J::Array(_), J::Array(_)) => true,
                                (J::Boolean, J::Boolean) | (J::Int, J::Int) | (J::Long, J::Long)
                                | (J::Float, J::Float) | (J::Double, J::Double)
                                | (J::Char, J::Char) | (J::Byte, J::Byte) | (J::Short, J::Short) => true,
                                (J::Int, J::Long | J::Float | J::Double) => true,
                                (J::Long, J::Float | J::Double) => true,
                                (J::Float, J::Double) => true,
                                (J::Byte | J::Short | J::Char, J::Int | J::Long | J::Float | J::Double) => true,
                                (J::Boolean, J::Int) | (J::Int, J::Boolean) => true,
                                _ => false,
                            }
                        }
                    }
                }
                let mut best: Option<(usize, Vec<jcdc_jvm::JavaType>)> = None;
                for c in cands {
                    let bad = c
                        .iter()
                        .zip(args.iter())
                        .filter(|(p, a)| !arg_fits(a, p))
                        .count();
                    if best.as_ref().map(|(b, _)| bad < *b).unwrap_or(true) {
                        best = Some((bad, c));
                    }
                }
                best.map(|(_, c)| c)
            }
        }
    }

    fn is_member_inner(&self, cls: &str) -> bool {
        let Some(pc) = self.pool.get(cls) else { return false };
        if pc.cf.fields.iter().any(|f| {
            pc.utf8(f.name_index)
                .map(|n| n.starts_with("this$"))
                .unwrap_or(false)
        }) {
            return true;
        }
        // jdk21+ javac drops the this$0 field when the inner class never
        // dereferences the outer instance itself: the ctor just forwards
        // it to the superclass (jdk26 WeakHashMap$EntryIterator ->
        // HashIterator). The ctor still takes the enclosing instance as
        // its first parameter, so call sites need the qualified-new form.
        if pc.is_enum() || !cls.contains('$') || crate::classdec::nested_is_static(&pc) {
            return false;
        }
        (0..pc.cf.methods.len()).any(|mi| {
            pc.method_name(mi) == Some("<init>")
                && pc
                    .method_desc(mi)
                    .map(|d| crate::classdec::outer_param_via_super(&pc, d))
                    .unwrap_or(false)
        })
    }

    /// Instantiated SAM return for a cast to a generic functional
    /// interface (`(Function<I,R>) lambda`): resolves the interface's SAM
    /// method Signature return against the cast's type arguments. Only
    /// meaningful when the result still contains a type variable — the
    /// erased impl body then needs `(R) value` witnesses on its returns
    /// (javac: "return type I cannot be converted to R" for `i -> i`).
    fn sam_ret_cast(&self, g: &jcdc_jvm::GenericType, sam_name: &str) -> Option<TypeRef> {
        let jcdc_jvm::GenericType::Class(cs) = g else { return None };
        let part = cs.parts.last()?;
        if part.args.is_empty() {
            return None;
        }
        let internal = if cs.package.is_empty() {
            cs.parts.iter().map(|p| p.name.as_str()).collect::<Vec<_>>().join("$")
        } else {
            format!("{}/{}", cs.package, cs.parts.iter().map(|p| p.name.as_str()).collect::<Vec<_>>().join("$"))
        };
        let pc = self.pool.get(&internal)?;
        let cls_params = pc
            .class_attr("Signature")
            .and_then(|b| {
                if b.len() >= 2 {
                    pc.utf8(u16::from_be_bytes([b[0], b[1]]))
                        .and_then(|s| jcdc_jvm::parse_class_signature(s))
                } else {
                    None
                }
            })?
            .params;
        for mi in 0..pc.cf.methods.len() {
            if pc.method_name(mi) != Some(sam_name) {
                continue;
            }
            let sig_bytes = pc.cf.methods[mi].attributes.iter().find_map(|at| {
                if pc.utf8(at.attribute_name_index) == Some("Signature") {
                    Some(at.info.as_slice())
                } else {
                    None
                }
            })?;
            if sig_bytes.len() < 2 {
                return None;
            }
            let msig = pc
                .utf8(u16::from_be_bytes([sig_bytes[0], sig_bytes[1]]))
                .and_then(|s| jcdc_jvm::parse_method_signature(s))?;
            let inst = crate::method::subst_typevars(&msig.ret, &cls_params, &part.args);
            // A wildcard anywhere in the instantiated return cannot be a
            // cast type (`(? extends V) x` is invalid syntax — jdk11
            // Collections.typeCheck's BiFunction<? super K, ? super V,
            // ? extends V> SAM); the erased body value already satisfies
            // the wildcard bound or the position needs no witness.
            if crate::classdec::g_has_typevar(&inst) && !crate::classdec::g_has_wildcard(&inst) {
                return Some(TypeRef::G(inst));
            }
            return None;
        }
        None
    }

    /// `<>` when `new cls(...)` should carry a diamond: the class is
    /// generic (class-level Signature with type params) and THIS file is
    /// Java 7+. A bare generic new compiles under old-style inference
    /// (standalone, not target-typed), which collapses to Object when
    /// implicitly-typed lambda args are involved — jdk11 Collectors.
    /// summingInt's `new CollectorImpl<>(() -> new int[1], (a, t) -> ...)`
    /// fails as bare `new CollectorImpl(...)` ("array required, but found
    /// Object", 72 errors in the concurrent-family closure). Bytecode
    /// cannot distinguish diamond from bare, so always prefer the diamond
    /// for generic classes.
    fn diamond_for(&self, cls: &str) -> &'static str {
        if self.pc.cf.major_version < 51 {
            return "";
        }
        let Some(pc) = self.pool.get(cls) else { return ""; };
        let generic = pc
            .class_attr("Signature")
            .map(|b| {
                b.len() >= 2
                    && pc.utf8(u16::from_be_bytes([b[0], b[1]]))
                        .and_then(|s| jcdc_jvm::parse_class_signature(s))
                        .map(|sig| !sig.params.is_empty())
                        .unwrap_or(false)
            })
            .unwrap_or(false);
        if generic { "<>" } else { "" }
    }

    /// Shorten an internal class name for emission: java.lang.* and same
    /// package use simple names; others fully qualified dotted.
    /// True when `cls.name` is a PRIVATE instance field and the owner
    /// expression's compile-time type is a strict subclass of cls: the
    /// field is not in the subclass's member scope, so the source must
    /// cast the owner to the declaring class
    /// (`((MessageDigest)this).algorithm` — jdk11 Delegate.clone x3,
    /// Signature.clone).
    fn private_super_field(&self, cls: &str, name: &str, o: &Expr) -> bool {
        if matches!(o, Expr::Raw(_) | Expr::RawT(..)) {
            return false;
        }
        let owner_ct = if matches!(o, Expr::This) {
            self.pc.internal_name.clone()
        } else {
            match o.type_ref().erased() {
                jcdc_jvm::JavaType::Object(n) => n,
                _ => return false,
            }
        };
        if owner_ct == cls {
            return false;
        }
        let Some(cpc) = self.pool.get(cls) else { return false };
        let Some(f) = cpc.cf.fields.iter().find(|f| {
            !f.access_flags.contains(jcdc_classfile::FieldAccessFlags::STATIC)
                && cpc.utf8(f.name_index) == Some(name)
        }) else {
            return false;
        };
        if !f.access_flags.contains(jcdc_classfile::FieldAccessFlags::PRIVATE) {
            return false;
        }
        // cls must be a strict superclass of the owner's compile-time type.
        let mut cur = owner_ct;
        for _ in 0..64 {
            let Some(pc2) = self.pool.get(&cur) else { return false };
            let Some(sup) = pc2.super_name() else { return false };
            if sup == cls {
                return true;
            }
            cur = sup.to_string();
        }
        false
    }

    fn needs_owner_cast(
        &self,
        cls: &str,
        name: &str,
        desc: &jcdc_jvm::MethodDescriptor,
        o: &Expr,
    ) -> bool {
        // Raw-rendered owners (qualified `HashMap.this`, substituted
        // capture text) carry no trustworthy static type — and casting
        // them to a RAW class erases the whole generic member chain
        // (`((HashMap) HashMap.this).<T>keysToArray(..)` made the call
        // raw: "Object[]无法转换为T[]").
        if matches!(o, Expr::Raw(_) | Expr::RawT(..) | Expr::This) {
            return false;
        }
        let jcdc_jvm::JavaType::Object(on) = o.type_ref().erased() else {
            return false;
        };
        if on == cls {
            return false;
        }
        let Some(cpc) = self.pool.get(cls) else { return false };
        let want = format!(
            "({}){}",
            desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
            desc.ret.to_descriptor()
        );
        let Some(mi) = (0..cpc.cf.methods.len()).find(|&i| {
            cpc.method_name(i) == Some(name) && cpc.method_desc(i) == Some(want.as_str())
        }) else {
            return false;
        };
        let acc = cpc.cf.methods[mi].access_flags;
        use jcdc_classfile::MethodAccessFlags as M;
        if acc.contains(M::PRIVATE) {
            return true;
        }
        if !acc.contains(M::PUBLIC) && !acc.contains(M::PROTECTED) {
            fn pkg(n: &str) -> &str {
                n.rsplit_once('/').map(|(p, _)| p).unwrap_or("")
            }
            return pkg(&on) != pkg(cls);
        }
        false
    }

    fn needs_object_relay(&self, ty: &TypeRef, e: &Expr) -> bool {
        if matches!(e, Expr::Cast { .. } | Expr::Const(_)) {
            return false;
        }
        let (
            jcdc_jvm::JavaType::Object(from),
            jcdc_jvm::JavaType::Object(to),
        ) = (e.type_ref().erased(), ty.erased())
        else {
            return false;
        };
        if from == to || from == "java/lang/Object" || to == "java/lang/Object" {
            return false;
        }
        let (Some(fpc), Some(tpc)) = (self.pool.get(&from), self.pool.get(&to)) else {
            return false;
        };
        if crate::classdec::is_subtype_of(self.pool, &e.type_ref().erased(), &to)
            || crate::classdec::is_subtype_of(self.pool, &ty.erased(), &from)
        {
            return false;
        }
        let sealed = |pc: &PoolClass| pc.class_attr("PermittedSubclasses").is_some();
        let both_classes = !fpc.is_interface() && !tpc.is_interface();
        both_classes || sealed(&fpc) || sealed(&tpc)
    }

    pub fn shorten(&self, internal: &str) -> String {
        if internal.is_empty() {
            return String::new();
        }
        // Literal-$ top-level class (in pool, no InnerClasses nesting
        // evidence): the $ is part of the SOURCE name (jextract-generated
        // errno_h$shared) — never dot it into a nested qualifier.
        let keep_dollar = internal.contains('$')
            && self
                .pool
                .get(internal)
                .map(|pc| crate::classdec::find_outer(&pc, self.pool).is_none())
                .unwrap_or(false);
        // Anonymous class types (all-digit last segment) have no source
        // name: print the base interface/superclass instead.
        if let Some(last) = internal.rsplit('$').next() {
            if !last.is_empty() && last.chars().all(|c| c.is_ascii_digit()) {
                if let Some(apc) = self.pool.get(internal) {
                    if let Some(&ii) = apc.cf.interfaces.first() {
                        if let Some(n) = apc.class_name(ii) {
                            return self.shorten(n);
                        }
                    }
                    if let Some(sup) = apc.super_name() {
                        if sup != "java/lang/Object" {
                            return self.shorten(sup);
                        }
                    }
                    return "Object".to_string();
                }
            }
        }
        // Local classes are emitted with their simple source name.
        if let Some(last) = internal.rsplit('$').next() {
            if !keep_dollar
                && !last.is_empty()
                && !last.chars().all(|c| c.is_ascii_digit())
                && internal.contains('$')
            {
                // Nested-class names print as Outer.Inner, except local
                // classes whose outer chain includes digits (e.g. Foo$1Bar).
                let mut segs = internal.split('$');
                if let Some(first) = segs.next() {
                    let rest: Vec<&str> = segs.collect();
                    if rest.iter().any(|r| r.starts_with(|c: char| c.is_ascii_digit())) {
                        // Local/synthetic class (digit-led segment): javac
                        // encodes a method-local class as `Outer$1Name`; its
                        // source name is the digit prefix stripped, declared
                        // `class Name` at its use site and referenced only
                        // within that scope. Printing the binary name leaves
                        // an unresolvable symbol (ClassSpecializer$Factory$1Var).
                        if let Some(last) = internal.rsplit('$').next() {
                            let stripped = last.trim_start_matches(|c: char| c.is_ascii_digit());
                            if !stripped.is_empty()
                                && !stripped.chars().next().unwrap().is_ascii_digit()
                            {
                                return stripped.to_string();
                            }
                        }
                        return internal.replace('/', ".");
                    }
                    let _ = first;
                    let _ = last;
                }
            }
        }
        let dotted = internal.replace('/', ".");
        // A simple type name shadowed by an in-scope VARIABLE (a field of
        // this class or a method local) cannot qualify a static access:
        // javac resolves the leading name as the variable first
        // (无法取消引用int — jdk26 VerificationType declares
        // `private static final int Integer` and the source spells
        // java.lang.Integer.toHexString in full). Keep the fully-qualified
        // form whenever the leading segment collides.
        let shadowed = |first: &str| {
            self.pc
                .cf
                .fields
                .iter()
                .any(|f| self.pc.utf8(f.name_index) == Some(first))
                || self.vt.vars.iter().any(|v| v.name == first)
        };
        if internal.starts_with("java/lang/") && !internal[10..].contains('/') {
            let simple = if keep_dollar {
                internal[10..].to_string()
            } else {
                internal[10..].replace('$', ".")
            };
            let first = simple.split('.').next().unwrap_or(simple.as_str());
            if !shadowed(first) {
                return simple;
            }
            return dotted.replace('$', ".");
        }
        if pkg_of(internal) == pkg_of(&self.pc.internal_name) {
            let simple = if keep_dollar {
                internal.rsplit('/').next().unwrap_or(internal).to_string()
            } else {
                internal.rsplit('/').next().unwrap_or(internal).replace('$', ".")
            };
            let first = simple.split('.').next().unwrap_or(simple.as_str());
            if !shadowed(first) {
                return simple;
            }
        }
        if keep_dollar {
            dotted
        } else {
            dotted.replace('$', ".")
        }
    }

    pub fn type_name(&self, ty: &TypeRef) -> String {
        match ty {
            TypeRef::J(t) => self.java_type_name(t),
            TypeRef::G(g) => {
                // Render generic signature with shortened class names.
                self.generic_name(g)
            }
        }
    }

    fn java_type_name(&self, t: &JavaType) -> String {
        match t {
            JavaType::Object(n) => self.shorten(n),
            JavaType::Array(inner) => format!("{}[]", self.java_type_name(inner)),
            other => other.to_java(false),
        }
    }

    fn generic_name(&self, g: &jcdc_jvm::GenericType) -> String {
        use jcdc_jvm::{GenericType, WildcardBound};
        match g {
            GenericType::Primitive(c) => prim_name(*c).to_string(),
            GenericType::Class(cs) => {
                // The signature parser splits a literal-$ top-level name
                // (jextract-generated errno_h$shared) into nested-looking
                // parts [errno_h, shared]; rejoin and, when the pool
                // proves the class is NOT nested, render the binary name
                // through shorten (same-package simple form keeps the $).
                if cs.parts.len() > 1
                    && cs.parts.iter().skip(1).all(|p| p.args.is_empty())
                {
                    let joined = cs
                        .parts
                        .iter()
                        .map(|p| p.name.as_str())
                        .collect::<Vec<_>>()
                        .join("$");
                    let full = if cs.package.is_empty() {
                        joined
                    } else {
                        format!("{}/{}", cs.package, joined)
                    };
                    let literal = self
                        .pool
                        .get(&full)
                        .map(|pc| {
                            crate::classdec::find_outer(&pc, self.pool).is_none()
                        })
                        .unwrap_or(false);
                    if literal {
                        return self.shorten(&full);
                    }
                }
                let mut s = String::new();
                if !cs.package.is_empty() {
                    let full = format!("{}/{}", cs.package, cs.parts.first().map(|p| p.name.as_str()).unwrap_or(""));
                    s.push_str(&self.shorten(&full));
                } else {
                    s.push_str(&cs.parts.first().map(|p| p.name.clone()).unwrap_or_default());
                }
                if let Some(first) = cs.parts.first() {
                    if !first.args.is_empty() {
                        s.push('<');
                        for (i, a) in first.args.iter().enumerate() {
                            if i > 0 {
                                s.push_str(", ");
                            }
                            s.push_str(&self.generic_name(a));
                        }
                        s.push('>');
                    }
                }
                for p in cs.parts.iter().skip(1) {
                    s.push('.');
                    s.push_str(&p.name);
                    if !p.args.is_empty() {
                        s.push('<');
                        for (i, a) in p.args.iter().enumerate() {
                            if i > 0 {
                                s.push_str(", ");
                            }
                            s.push_str(&self.generic_name(a));
                        }
                        s.push('>');
                    }
                }
                s
            }
            GenericType::Array(inner) => format!("{}[]", self.generic_name(inner)),
            GenericType::TypeVar(n) => n.clone(),
            GenericType::Wildcard(w) => match w {
                WildcardBound::Any => "?".to_string(),
                WildcardBound::Extends(t) => format!("? extends {}", self.generic_name(t)),
                WildcardBound::Super(t) => format!("? super {}", self.generic_name(t)),
            },
        }
    }
}

fn inner_simple(cls: &str) -> String {
    let last = cls.rsplit('/').next().unwrap_or(cls);
    last.rsplit('$').next().unwrap_or(last).to_string()
}

fn push_char_lit(out: &mut String, n: i32) {
    let c = (n as u16) as u32;
    match char::from_u32(c) {
        Some('\'') => out.push_str("'\\''"),
        Some('\\') => out.push_str("'\\\\'"),
        Some('\n') => out.push_str("'\\n'"),
        Some('\r') => out.push_str("'\\r'"),
        Some('\t') => out.push_str("'\\t'"),
        Some(ch) if ch.is_control() => out.push_str(&format!("'\\u{:04x}'", c)),
        Some(ch) => {
            out.push('\'');
            out.push(ch);
            out.push('\'');
        }
        None => out.push_str(&format!("'\\u{:04x}'", c)),
    }
}

fn const_bool(e: &Expr) -> Option<bool> {
    match e {
        Expr::Const(ConstVal::Int(n)) => Some(*n != 0),
        _ => None,
    }
}

fn pkg_of(n: &str) -> &str {
    n.rfind('/').map(|i| &n[..i]).unwrap_or("")
}

fn prim_name(c: char) -> &'static str {
    match c {
        'V' => "void",
        'Z' => "boolean",
        'B' => "byte",
        'C' => "char",
        'S' => "short",
        'I' => "int",
        'F' => "float",
        'J' => "long",
        'D' => "double",
        _ => "?",
    }
}

pub fn escape_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{0}' => out.push_str("\\0"),
            '\u{8}' => out.push_str("\\b"),
            '\u{C}' => out.push_str("\\f"),
            c if (c as u32) < 0x20 || (c as u32) == 0x7F => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out
}

pub fn escape_char(c: char) -> String {
    match c {
        '\'' => "\\'".to_string(),
        '\\' => "\\\\".to_string(),
        '\n' => "\\n".to_string(),
        '\r' => "\\r".to_string(),
        '\t' => "\\t".to_string(),
        '\0' => "\\0".to_string(),
        c if (c as u32) < 0x20 || (c as u32) == 0x7F => format!("\\u{:04x}", c as u32),
        c => c.to_string(),
    }
}

pub fn format_float(v: f64, is_float: bool) -> String {
    let suffix = if is_float { "f" } else { "" };
    // Arithmetic literals, not `Double.NaN`/`POSITIVE_INFINITY` field refs:
    // inside java.lang.Double/Float themselves a field reference would be
    // a self-reference initializing the very field being printed.
    if v.is_nan() {
        return if is_float { "(0.0f / 0.0f)".into() } else { "(0.0 / 0.0)".into() };
    }
    if v.is_infinite() {
        let one = if is_float { "1.0f" } else { "1.0" };
        let zero = if is_float { "0.0f" } else { "0.0" };
        return if v < 0.0 {
            format!("(-{} / {})", one, zero)
        } else {
            format!("({} / {})", one, zero)
        };
    }
    let mut s = format!("{}", v);
    if !s.contains('.') && !s.contains('e') && !s.contains('E') {
        s.push_str(".0");
    }
    // Java doesn't accept exponent forms like "1e-7"? It does: 1e-7 is a valid
    // double literal. But "inf"/"nan" handled above.
    format!("{}{}", s, suffix)
}


// ---------------------------------------------------------------------------
// Unreachable-code truncation (final statement tree)
// ---------------------------------------------------------------------------

/// Drop statements that follow a `while (true)` which cannot complete
/// normally (no `break` in its body binds to it): javac rejects them as
/// 无法访问的语句, and the structurers only emitted them as shared-tail
/// copies whose real arrivals all render INSIDE the loop arms (jdk17/26
/// Pattern.clazz's for(;;){switch}: case-93's `return prev/negate` tail
/// landed after the never-completing loop). Runs on the FINAL tree (after
/// switch restoration and goto resolution) so the break inventory is
/// exactly what gets emitted; every unknown shape stays conservative
/// (assumes the loop can complete).
fn truncate_dead_ends(s: &Stmt) -> Stmt {
    match s {
        Stmt::Block(v) => {
            let mut out: Vec<Stmt> = Vec::with_capacity(v.len());
            for x in v {
                if !out.is_empty() && dead_end_infinite_while(out.last().unwrap()) {
                    if crate::dbg_flag!("JCDC_DBG_GOTO") {
                        eprintln!(
                            "DEADEND truncate {} unreachable stmt(s)",
                            v.len() - out.len()
                        );
                    }
                    break;
                }
                out.push(truncate_dead_ends(x));
            }
            Stmt::Block(out)
        }
        Stmt::If { cond, then_stmt, else_stmt } => Stmt::If {
            cond: cond.clone(),
            then_stmt: Box::new(truncate_dead_ends(then_stmt)),
            else_stmt: else_stmt.as_deref().map(truncate_dead_ends).map(Box::new),
        },
        Stmt::While { cond, body } => Stmt::While {
            cond: cond.clone(),
            body: Box::new(truncate_dead_ends(body)),
        },
        Stmt::DoWhile { body, cond } => Stmt::DoWhile {
            body: Box::new(truncate_dead_ends(body)),
            cond: cond.clone(),
        },
        Stmt::For { init, cond, update, body } => Stmt::For {
            init: init.iter().map(truncate_dead_ends).collect(),
            cond: cond.clone(),
            update: update.clone(),
            body: Box::new(truncate_dead_ends(body)),
        },
        Stmt::ForEach { var, iterable, is_array, body } => Stmt::ForEach {
            var: *var,
            iterable: iterable.clone(),
            is_array: *is_array,
            body: Box::new(truncate_dead_ends(body)),
        },
        Stmt::Switch { selector, cases, default, on_string } => Stmt::Switch {
            selector: selector.clone(),
            cases: cases
                .iter()
                .map(|c| CaseGroup {
                    labels: c.labels.clone(),
                    string_labels: c.string_labels.clone(),
                    enum_labels: c.enum_labels.clone(),
                    raw_labels: c.raw_labels.clone(),
                    guard: c.guard.clone(),
                    body: c.body.iter().map(truncate_dead_ends).collect(),
                })
                .collect(),
            default: default.as_deref().map(truncate_dead_ends).map(Box::new),
            on_string: *on_string,
        },
        Stmt::Try { body, catches, finally } => Stmt::Try {
            body: Box::new(truncate_dead_ends(body)),
            catches: catches
                .iter()
                .map(|c| Catch {
                    exc: c.exc.clone(),
                    var: c.var,
                    var_name: c.var_name.clone(),
                    body: Box::new(truncate_dead_ends(&c.body)),
                })
                .collect(),
            finally: finally.as_deref().map(truncate_dead_ends).map(Box::new),
        },
        Stmt::TryWithResources { resources, body, catches, finally } => {
            Stmt::TryWithResources {
                resources: resources.iter().map(truncate_dead_ends).collect(),
                body: Box::new(truncate_dead_ends(body)),
                catches: catches
                    .iter()
                    .map(|c| Catch {
                        exc: c.exc.clone(),
                        var: c.var,
                        var_name: c.var_name.clone(),
                        body: Box::new(truncate_dead_ends(&c.body)),
                    })
                    .collect(),
                finally: finally.as_deref().map(truncate_dead_ends).map(Box::new),
            }
        }
        Stmt::Synchronized { lock, body } => Stmt::Synchronized {
            lock: lock.clone(),
            body: Box::new(truncate_dead_ends(body)),
        },
        Stmt::Labeled { label, body } => Stmt::Labeled {
            label: label.clone(),
            body: Box::new(truncate_dead_ends(body)),
        },
        other => other.clone(),
    }
}

/// True when `s` is a `while (true)` (labeled or not) whose body holds
/// no `break` binding to it — it can never complete normally.
pub(crate) fn dead_end_infinite_while(s: &Stmt) -> bool {
    let (label, body, cond) = match s {
        Stmt::While { cond, body } => (None, body.as_ref(), cond),
        Stmt::Labeled { label, body } => match &**body {
            Stmt::While { cond, body } => (Some(label.as_str()), body.as_ref(), cond),
            _ => return false,
        },
        _ => return false,
    };
    if !matches!(cond, Expr::Const(ConstVal::Int(1))) {
        return false;
    }
    // JLS 14.14: `while (true)` completes normally iff its body holds a
    // reachable break that exits IT: an unlabeled break not captured by
    // an inner breakable construct, or `break L` where L is THIS loop's
    // own label. A labeled break to any OTHER label — inner (Pattern
    // .clazz's `break L4`) or OUTER (jdk11/26 ThreadPoolExecutor
    // .addWorker's `break retry` inside the inner for(;;)) — completes
    // the while ABRUPTLY: javac's flow model marks the statements after
    // such a loop unreachable (the w26 `continue;` after the inner
    // while(true) was a latent 无法访问的语句 masked by alphabetically
    // earlier census errors).
    !has_break_exiting(body, label, 0)
}

fn has_break_exiting(s: &Stmt, lbl: Option<&str>, depth: usize) -> bool {
    match s {
        Stmt::Break(None) => depth == 0,
        // Only this loop's OWN label completes it; any other labeled
        // break exits abruptly (JLS 14.14/14.17).
        Stmt::Break(Some(l)) => Some(l.as_str()) == lbl,
        Stmt::Continue(_) | Stmt::Return(_) | Stmt::Throw(_) => false,
        Stmt::Goto(_) => true,
        Stmt::Block(v) => v.iter().any(|x| has_break_exiting(x, lbl, depth)),
        Stmt::If { then_stmt, else_stmt, .. } => {
            has_break_exiting(then_stmt, lbl, depth)
                || else_stmt
                    .as_deref()
                    .map(|e| has_break_exiting(e, lbl, depth))
                    .unwrap_or(false)
        }
        Stmt::While { body, .. }
        | Stmt::DoWhile { body, .. }
        | Stmt::For { body, .. }
        | Stmt::ForEach { body, .. } => has_break_exiting(body, lbl, depth + 1),
        Stmt::Switch { cases, default, .. } => {
            cases
                .iter()
                .any(|c| c.body.iter().any(|x| has_break_exiting(x, lbl, depth + 1)))
                || default
                    .as_deref()
                    .map(|d| has_break_exiting(d, lbl, depth + 1))
                    .unwrap_or(false)
        }
        Stmt::Try { body, catches, finally }
        | Stmt::TryWithResources { body, catches, finally, .. } => {
            has_break_exiting(body, lbl, depth)
                || catches.iter().any(|c| has_break_exiting(&c.body, lbl, depth))
                || finally
                    .as_deref()
                    .map(|f| has_break_exiting(f, lbl, depth))
                    .unwrap_or(false)
        }
        Stmt::Synchronized { body, .. } => has_break_exiting(body, lbl, depth),
        Stmt::Labeled { body, .. } => has_break_exiting(body, lbl, depth),
        // Plain leaf statements never contain a break.
        Stmt::ExprStmt(_)
        | Stmt::LocalDef { .. }
        | Stmt::Assert { .. }
        | Stmt::TernaryValue { .. }
        | Stmt::MonitorEnter(_)
        | Stmt::MonitorExit(_)
        | Stmt::Comment(_) => false,
        // Opaque shapes (raw labels, inline class decls, anything new):
        // keep truncation off when an escape cannot be ruled out.
        _ => true,
    }
}

