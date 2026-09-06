//! Java source emission from the statement/expression tree.

use jcdc_jvm::{ClassPool, JavaType, PoolClass};

use crate::expr::{BinOp, ConcatPart, ConstVal, Expr, LambdaKind, TypeRef, UnOp};
use crate::method::MethodBody;
use crate::stmt::Stmt;
use crate::varalloc::VarTable;

pub struct Printer<'a> {
    pub pc: &'a PoolClass,
    pub pool: &'a ClassPool,
    pub vt: &'a VarTable,
    out: String,
    indent: usize,
    /// Depth guard for recursive lambda printing.
    lambda_depth: usize,
    /// True when the enclosing method returns boolean.
    pub ret_bool: bool,
}

impl<'a> Printer<'a> {
    pub fn new(pc: &'a PoolClass, pool: &'a ClassPool, vt: &'a VarTable) -> Self {
        Printer { pc, pool, vt, out: String::new(), indent: 0, lambda_depth: 0, ret_bool: false }
    }

    pub fn with_ret_bool(mut self, b: bool) -> Self {
        self.ret_bool = b;
        self
    }

    /// Printer starting at a fixed indentation level (method bodies at 1).
    pub fn with_indent(mut self, indent: usize) -> Self {
        self.indent = indent;
        self
    }

    pub fn into_string(mut self, body: &Stmt) -> String {
        self.stmt(body);
        self.out
    }

    /// Print an expression that appears in a boolean context; int 0/1
    /// constants become true/false.
    pub fn expr_bool(&mut self, e: &Expr, out: &mut String) {
        match e {
            Expr::Const(ConstVal::Int(n)) => {
                out.push_str(if *n != 0 { "true" } else { "false" });
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
                            self.expr_bool(c, out);
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

    fn stmt(&mut self, s: &Stmt) {
        match s {
            Stmt::Block(v) => {
                for x in v {
                    self.stmt(x);
                }
            }
            Stmt::ExprStmt(e) => {
                let mut line = String::new();
                self.expr(e, 0, &mut line);
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
                } else {
                    self.expr(e, 1, &mut line);
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
                    for l in &c.enum_labels {
                        self.line(&format!("case {}:", l));
                    }
                    for l in &c.raw_labels {
                        self.line(&format!("case {}:", l));
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
                self.expr(cond, 1, &mut line);
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
            ret_bool: self.ret_bool,
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
            Expr::Raw(t) => out.push_str(t),
            Expr::Local { var, .. } => {
                let info = self.vt.var(*var);
                out.push_str(&info.name);
            }
            Expr::This => out.push_str("this"),
            Expr::New { cls, args, .. } => {
                if let Some(local) = cls.strip_prefix('\u{2}') {
                    out.push_str("new ");
                    out.push_str(local);
                    out.push('(');
                    self.args(args, out);
                    out.push(')');
                } else if self.is_member_inner(cls)
                    && !args.is_empty()
                    && !matches!(args[0], Expr::This)
                {
                    // `outerExpr.new Inner(rest...)` — the first ctor arg
                    // is the synthetic outer instance when the class has a
                    // this$0 field.
                    let has_this0 = self.pool.get(cls).map(|pcx| {
                        pcx.cf.fields.iter().any(|f| {
                            pcx.utf8(f.name_index).map(|n| n.starts_with("this$")).unwrap_or(false)
                        })
                    }).unwrap_or(false);
                    self.expr(&args[0], 15, out);
                    out.push_str(".new ");
                    out.push_str(&inner_simple(cls));
                    out.push('(');
                    if has_this0 {
                        match self.ctor_param_types(cls, 1, args.len() - 1) {
                            Some(pt) => self.args_typed(&args[1..], &pt, out),
                            None => self.args(&args[1..], out),
                        }
                    } else {
                        match self.ctor_param_types(cls, 0, args.len()) {
                            Some(pt) => self.args_typed(args, &pt, out),
                            None => self.args(args, out),
                        }
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
                    out.push('(');
                    if member_this {
                        match self.ctor_param_types(cls, 1, args.len() - 1) {
                            Some(pt) => self.args_typed(&args[1..], &pt, out),
                            None => self.args(&args[1..], out),
                        }
                    } else {
                        match self.ctor_param_types(cls, 0, args.len()) {
                            Some(pt) => self.args_typed(args, &pt, out),
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
                        for (i, v) in vals.iter().enumerate() {
                            if i > 0 {
                                out.push_str(", ");
                            }
                            self.expr(v, 1, out);
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
                if name == "length" && cls.is_empty() {
                    if let Some(o) = owner {
                        self.expr(o, 15, out);
                    }
                    out.push_str(".length");
                } else if let Some(o) = owner {
                    self.expr(o, 15, out);
                    out.push('.');
                    out.push_str(name);
                } else if *is_static {
                    if cls != &self.pc.internal_name {
                        out.push_str(&self.shorten(cls));
                        out.push('.');
                    }
                    out.push_str(name);
                } else {
                    out.push_str("this.");
                    out.push_str(name);
                }
            }
            Expr::Method { owner, cls, name, desc, args, is_static, is_special, is_super, type_args, .. } => {
                if name == "<init>" && *is_special {
                    // super(...) / this(...)
                    let is_super_form = *is_super || cls != &self.pc.internal_name;
                    if is_super_form {
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
                    if desc.args.len() == args.len() {
                        self.args_typed(args, &desc.args, out);
                    } else {
                        match self.ctor_param_types(cls, 0, args.len()) {
                            Some(pt) => self.args_typed(args, &pt, out),
                            None => self.args(args, out),
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
                        self.expr(o, 15, out);
                        out.push('.');
                    } else if *is_static && (cls != &self.pc.internal_name || !type_args.is_empty())
                    {
                        out.push_str(&self.shorten(cls));
                        out.push('.');
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
                    self.args_typed(args, &desc.args, out);
                    out.push(')');
                }
            }
            Expr::ArrayIndex { array, index } => {
                self.expr(array, 15, out);
                out.push('[');
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
                out.push('(');
                out.push_str(&self.type_name(ty));
                out.push_str(") ");
                self.expr(e, 14, out);
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
                // Boolean context special cases: `b == 0` → `!b`.
                let lt = l.type_ref().erased();
                if matches!(op, BinOp::Eq | BinOp::Ne | BinOp::RefEq | BinOp::RefNe)
                    && lt == JavaType::Boolean
                {
                    if let Expr::Const(ConstVal::Int(n)) = &**r {
                        let polarity = matches!(op, BinOp::Eq | BinOp::RefEq);
                        let want_true = (*n != 0) == polarity;
                        if !want_true {
                            out.push('!');
                        }
                        self.expr(l, 14, out);
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
                self.expr(t, 2, out);
                out.push_str(" : ");
                self.expr(f, 2, out);
            }
            Expr::Assign { target, op, value } => {
                let tgt_bool = target.type_ref().erased() == jcdc_jvm::JavaType::Boolean;
                self.expr(target, 1, out);
                out.push(' ');
                out.push_str(op.symbol());
                out.push(' ');
                if tgt_bool && matches!(op, crate::expr::AssignOp::Plain) {
                    self.expr_bool(value, out);
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
                self.args(args, out);
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
    fn args_typed(&mut self, args: &[Expr], param_types: &[jcdc_jvm::JavaType], out: &mut String) {
        for (i, a) in args.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            match param_types.get(i) {
                Some(jcdc_jvm::JavaType::Boolean) => self.expr_bool(a, out),
                Some(jcdc_jvm::JavaType::Char) => {
                    if let Expr::Const(ConstVal::Int(n)) = a {
                        if (0..=0xFFFF).contains(n) {
                            let c = char::from_u32(*n as u32).unwrap_or('?');
                            out.push('\'');
                            out.push_str(&escape_char(c));
                            out.push('\'');
                            continue;
                        }
                    }
                    self.expr(a, 1, out);
                }
                // Byte/short parameters: an int literal argument needs an
                // explicit cast (invocation conversion never narrows).
                Some(jcdc_jvm::JavaType::Byte) => {
                    if let Expr::Const(ConstVal::Int(n)) = a {
                        out.push_str(&format!("(byte) {}", n));
                        continue;
                    }
                    self.expr(a, 1, out);
                }
                Some(jcdc_jvm::JavaType::Short) => {
                    if let Expr::Const(ConstVal::Int(n)) = a {
                        out.push_str(&format!("(short) {}", n));
                        continue;
                    }
                    self.expr(a, 1, out);
                }
                _ => self.expr(a, 1, out),
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
                match body_stmts {
                    Some(MethodBody { mut body, vt, .. }) => {
                        {
                            let fam = crate::classdec::Family::collect(self.pc, self.pool);
                            crate::classdec::inline_anonymous(
                                &mut body,
                                self.pc,
                                self.pool,
                                &fam,
                                &vt,
                            );
                        }
                        crate::classdec::restore_enum_switches(&mut body, self.pc, self.pool);
                        // Single-return body → expression lambda.
                        let single_expr = match &body {
                            Stmt::Return(Some(e)) => Some(e.clone()),
                            Stmt::Block(v) if v.len() == 1 => match &v[0] {
                                Stmt::Return(Some(e)) => Some(e.clone()),
                                _ => None,
                            },
                            _ => None,
                        };
                        let mut sub = Printer {
                            pc: self.pc,
                            pool: self.pool,
                            vt: &vt,
                            out: String::new(),
                            indent: self.indent,
                            lambda_depth: self.lambda_depth + 1,
                            ret_bool: false,
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
    fn ctor_param_types(&self, cls: &str, skip: usize, n: usize) -> Option<Vec<jcdc_jvm::JavaType>> {
        let pcx = self.pool.get(cls)?;
        // Enum ctors carry the implicit (String name, int ordinal) prefix.
        let extra: usize = if pcx.is_enum() { 2 } else { 0 };
        for mi in 0..pcx.cf.methods.len() {
            if pcx.method_name(mi) != Some("<init>") {
                continue;
            }
            let d = pcx.method_desc(mi)?;
            if let Some(md) = jcdc_jvm::parse_method_descriptor(d) {
                if md.args.len() == skip + extra + n {
                    return Some(md.args[skip + extra..].to_vec());
                }
            }
        }
        None
    }

    fn is_member_inner(&self, cls: &str) -> bool {
        self.pool
            .get(cls)
            .map(|pc| {
                pc.cf.fields.iter().any(|f| {
                    pc.utf8(f.name_index)
                        .map(|n| n.starts_with("this$"))
                        .unwrap_or(false)
                })
            })
            .unwrap_or(false)
    }

    /// Shorten an internal class name for emission: java.lang.* and same
    /// package use simple names; others fully qualified dotted.
    pub fn shorten(&self, internal: &str) -> String {
        if internal.is_empty() {
            return String::new();
        }
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
            if !last.is_empty()
                && !last.chars().all(|c| c.is_ascii_digit())
                && internal.contains('$')
            {
                // Nested-class names print as Outer.Inner, except local
                // classes whose outer chain includes digits (e.g. Foo$1Bar).
                let mut segs = internal.split('$');
                if let Some(first) = segs.next() {
                    let rest: Vec<&str> = segs.collect();
                    if rest.iter().any(|r| r.starts_with(|c: char| c.is_ascii_digit())) {
                        // Local/synthetic class (digit-led segment): the
                        // simple name is not a valid identifier, so print
                        // the qualified binary name (with `$`), which Java
                        // accepts as an identifier.
                        return internal.replace('/', ".");
                    }
                    let _ = first;
                    let _ = last;
                }
            }
        }
        let dotted = internal.replace('/', ".");
        if internal.starts_with("java/lang/") && !internal[10..].contains('/') {
            return internal[10..].replace('$', ".");
        }
        if pkg_of(internal) == pkg_of(&self.pc.internal_name) {
            return internal.rsplit('/').next().unwrap_or(internal).replace('$', ".");
        }
        dotted.replace('$', ".")
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
