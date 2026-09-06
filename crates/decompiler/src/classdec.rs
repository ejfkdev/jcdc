//! Class-level decompilation: header, fields, methods, static initializer,
//! nested/anonymous class families.

use std::collections::{HashMap, HashSet};
use std::sync::OnceLock;

use jcdc_classfile::{
    parse_specialized_attribute, ClassAccessFlags, FieldAccessFlags, MethodAccessFlags,
    ParsedAttribute,
};
use jcdc_jvm::{
    parse_class_signature, parse_field_descriptor, parse_field_signature, parse_method_descriptor,
    parse_method_signature, ClassPool, JavaType, PoolClass,
};

use crate::emit::Printer;
use crate::expr::{Expr, TypeRef};
use crate::method::decompile_method;
use crate::stmt::Stmt;
use crate::varalloc::VarTable;

fn empty_pool() -> &'static ClassPool {
    static P: OnceLock<ClassPool> = OnceLock::new();
    P.get_or_init(ClassPool::new)
}

fn empty_vt() -> &'static VarTable {
    static V: OnceLock<VarTable> = OnceLock::new();
    V.get_or_init(VarTable::default)
}

#[derive(Clone)]
pub struct ClassOptions {
    /// Include synthetic/bridge members.
    pub show_synthetic: bool,
    /// Include private members.
    pub show_private: bool,
}

impl Default for ClassOptions {
    fn default() -> Self {
        ClassOptions { show_synthetic: false, show_private: true }
    }
}

// ---------------------------------------------------------------------------
// Family analysis (nested / anonymous / lambda classes)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum NestedKind {
    Member,
    Anonymous,
    Local,
    Lambda,
}

pub struct NestedClass {
    pub name: String,
    pub simple: String,
    pub kind: NestedKind,
    pub access: ClassAccessFlags,
    /// Source header rendered from the class Signature (generic
    /// supertypes + type params) when available; the inline local-class
    /// walker falls back to its erased rendering.
    pub sig_header: Option<String>,
}

pub struct Family {
    pub root: String,
    /// All nested classes (any depth) keyed by internal name.
    pub nested: HashMap<String, NestedClass>,
    /// Anonymous classes inlined at `new` sites (not printed separately).
    pub anonymous: HashSet<String>,
    /// Local classes: declared at their use site inside methods.
    pub locals: HashSet<String>,
    /// Lambda impl classes (skipped entirely).
    pub lambdas: HashSet<String>,
}

impl Family {
    pub fn collect(root_pc: &PoolClass, pool: &ClassPool) -> Family {
        let root = root_pc.internal_name.clone();
        let mut fam = Family {
            root: root.clone(),
            nested: HashMap::new(),
            anonymous: HashSet::new(),
            locals: HashSet::new(),
            lambdas: HashSet::new(),
        };
        let prefix = format!("{}$", root);
        // Only primary (input) sources: classpath jars must not leak
        // foreign nested classes into the emitted family.
        for name in pool.primary_names() {
            if !name.starts_with(&prefix) {
                continue;
            }
            let rest = &name[prefix.len()..];
            let Some(pc) = pool.get(&name) else { continue };
            let (kind, simple, access) = classify_nested(&name, rest, &pc);
            match kind {
                NestedKind::Lambda => {
                    fam.lambdas.insert(name.clone());
                }
                NestedKind::Anonymous => {
                    fam.anonymous.insert(name.clone());
                    fam.nested.insert(
                        name.clone(),
                        NestedClass { name: name.clone(), simple, kind, access, sig_header: None },
                    );
                }
                NestedKind::Local => {
                    fam.locals.insert(name.clone());
                    let sig_header = sig_class_header(&pc, &simple, pool);
                    fam.nested.insert(
                        name.clone(),
                        NestedClass { name: name.clone(), simple, kind, access, sig_header },
                    );
                }
                NestedKind::Member => {
                    let sig_header = sig_class_header(&pc, &simple, pool);
                    fam.nested.insert(
                        name.clone(),
                        NestedClass { name: name.clone(), simple, kind, access, sig_header },
                    );
                }
            }
        }
        fam
    }

    /// Direct nested classes of `outer` that should be printed inside it
    /// (member/local kinds; anonymous are inlined, lambdas skipped).
    pub fn direct_children(&self, outer: &str) -> Vec<&NestedClass> {
        let prefix = format!("{}$", outer);
        let mut v: Vec<&NestedClass> = self
            .nested
            .iter()
            .filter(|(name, n)| {
                name.starts_with(&prefix)
                    && !name[prefix.len()..].contains('$')
                    && n.kind != NestedKind::Anonymous
                    && n.kind != NestedKind::Local
            })
            .map(|(_, n)| n)
            .collect();
        v.sort_by(|a, b| a.name.cmp(&b.name));
        v
    }

    /// Direct anonymous children of `outer` (for enum constant bodies etc.).
    pub fn direct_anonymous(&self, outer: &str) -> Vec<&NestedClass> {
        let prefix = format!("{}$", outer);
        let mut v: Vec<&NestedClass> = self
            .nested
            .iter()
            .filter(|(name, n)| {
                name.starts_with(&prefix)
                    && !name[prefix.len()..].contains('$')
                    && n.kind == NestedKind::Anonymous
            })
            .map(|(_, n)| n)
            .collect();
        v.sort_by(|a, b| a.name.cmp(&b.name));
        v
    }
}

/// Inline javac's synthetic `access$NNN` bridge methods (JDK <= 10 inner
/// class access). The bridges are hidden from the printed class, so call
/// sites must carry the underlying field/method expression instead.
fn inline_accessors(s: &mut Stmt, pc: &PoolClass, pool: &ClassPool) {
    fn walk_stmt(s: &mut Stmt, pc: &PoolClass, pool: &ClassPool, depth: u8) {
        match s {
            Stmt::Block(v) => v.iter_mut().for_each(|x| walk_stmt(x, pc, pool, depth)),
            Stmt::ExprStmt(e) => walk_expr(e, pc, pool, depth),
            Stmt::LocalDef { init: Some(e), .. } => walk_expr(e, pc, pool, depth),
            Stmt::Return(e) => {
                if let Some(x) = e {
                    walk_expr(x, pc, pool, depth);
                }
            }
            Stmt::Throw(e) => walk_expr(e, pc, pool, depth),
            Stmt::If { cond, then_stmt, else_stmt } => {
                walk_expr(cond, pc, pool, depth);
                walk_stmt(then_stmt, pc, pool, depth);
                if let Some(x) = else_stmt {
                    walk_stmt(x, pc, pool, depth);
                }
            }
            Stmt::While { cond, body } | Stmt::DoWhile { body, cond } => {
                walk_expr(cond, pc, pool, depth);
                walk_stmt(body, pc, pool, depth);
            }
            Stmt::For { init, cond, update, body } => {
                init.iter_mut().for_each(|i| walk_stmt(i, pc, pool, depth));
                if let Some(c) = cond {
                    walk_expr(c, pc, pool, depth);
                }
                update.iter_mut().for_each(|u| walk_expr(u, pc, pool, depth));
                walk_stmt(body, pc, pool, depth);
            }
            Stmt::ForEach { iterable, body, .. } => {
                walk_expr(iterable, pc, pool, depth);
                walk_stmt(body, pc, pool, depth);
            }
            Stmt::Switch { selector, cases, default, .. } => {
                walk_expr(selector, pc, pool, depth);
                for c in cases.iter_mut() {
                    c.body.iter_mut().for_each(|x| walk_stmt(x, pc, pool, depth));
                }
                if let Some(d) = default {
                    walk_stmt(d, pc, pool, depth);
                }
            }
            Stmt::Try { body, catches, finally } => {
                walk_stmt(body, pc, pool, depth);
                for c in catches.iter_mut() {
                    walk_stmt(&mut c.body, pc, pool, depth);
                }
                if let Some(f) = finally {
                    walk_stmt(f, pc, pool, depth);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                for res in resources.iter_mut() { walk_stmt(res, pc, pool, depth); }
                walk_stmt(body, pc, pool, depth);
                for c in catches.iter_mut() {
                    walk_stmt(&mut c.body, pc, pool, depth);
                }
                if let Some(f) = finally {
                    walk_stmt(f, pc, pool, depth);
                }
            }
            Stmt::Synchronized { lock, body } => {
                walk_expr(lock, pc, pool, depth);
                walk_stmt(body, pc, pool, depth);
            }
            Stmt::Labeled { body, .. } => walk_stmt(body, pc, pool, depth),
            _ => {}
        }
    }
    fn walk_expr(e: &mut Expr, pc: &PoolClass, pool: &ClassPool, depth: u8) {
        if let Some(rep) = accessor_replacement(e, pc, pool, depth) {
            *e = rep;
            return;
        }
        match e {
            Expr::Method { owner, args, .. } => {
                if let Some(o) = owner {
                    walk_expr(o, pc, pool, depth);
                }
                args.iter_mut().for_each(|a| walk_expr(a, pc, pool, depth));
            }
            Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
                args.iter_mut().for_each(|a| walk_expr(a, pc, pool, depth));
            }
            Expr::Field { owner: Some(o), .. } => walk_expr(o, pc, pool, depth),
            Expr::ArrayIndex { array, index } => {
                walk_expr(array, pc, pool, depth);
                walk_expr(index, pc, pool, depth);
            }
            Expr::Cast { e: i, .. } | Expr::InstanceOf { e: i, .. } | Expr::Un { e: i, .. }
            | Expr::PreIncDec { e: i, .. } | Expr::PostIncDec { e: i, .. } => {
                walk_expr(i, pc, pool, depth)
            }
            Expr::Bin { l, r, .. } => {
                walk_expr(l, pc, pool, depth);
                walk_expr(r, pc, pool, depth);
            }
            Expr::Cond { c, t, f } => {
                walk_expr(c, pc, pool, depth);
                walk_expr(t, pc, pool, depth);
                walk_expr(f, pc, pool, depth);
            }
            Expr::Assign { target, value, .. } => {
                walk_expr(target, pc, pool, depth);
                walk_expr(value, pc, pool, depth);
            }
            Expr::NewArray { dims, init, .. } => {
                dims.iter_mut().for_each(|d| walk_expr(d, pc, pool, depth));
                if let Some(vals) = init {
                    vals.iter_mut().for_each(|v| walk_expr(v, pc, pool, depth));
                }
            }
            Expr::StringConcat(parts) => parts.iter_mut().for_each(|p| {
                if let crate::expr::ConcatPart::Str(i) = p {
                    walk_expr(i, pc, pool, depth);
                }
            }),
            Expr::Lambda(l) => {
                l.captures.iter_mut().for_each(|c| walk_expr(c, pc, pool, depth));
            }
            Expr::Invokedynamic { args, .. } => {
                args.iter_mut().for_each(|a| walk_expr(a, pc, pool, depth))
            }
            _ => {}
        }
    }
    walk_stmt(s, pc, pool, 0);
}

/// When `e` is a call to a synthetic `access$NNN` bridge, return its body
/// expression with the parameters substituted by the call arguments.
fn accessor_replacement(e: &Expr, _pc: &PoolClass, pool: &ClassPool, depth: u8) -> Option<Expr> {
    if depth > 4 {
        return None;
    }
    let (cls, name, args) = match e {
        Expr::Method { cls, name, args, is_static: true, .. } if name.starts_with("access$") => {
            (cls.as_str(), name.as_str(), args)
        }
        _ => return None,
    };
    let apc = pool.get(cls)?;
    use jcdc_classfile::MethodAccessFlags;
    let mi = (0..apc.cf.methods.len()).find(|&i| {
        apc.method_name(i) == Some(name)
            && apc.cf.methods[i].access_flags.contains(MethodAccessFlags::SYNTHETIC)
    })?;
    let mb = decompile_method(&apc, pool, mi).ok()??;
    let params: Vec<u32> = mb
        .vt
        .vars
        .iter()
        .filter(|v| v.is_param)
        .map(|v| v.id)
        .collect();
    if params.len() != args.len() {
        return None;
    }
    // Bridge bodies: `return expr;`, `lhs = rhs; return;`, or a void
    // delegation `x.m(args); return;`.
    let stmts = stmt_vec(&mb.body);
    let delegating = |x: &Stmt| {
        matches!(x, Stmt::ExprStmt(Expr::Assign { .. }) | Stmt::ExprStmt(Expr::Method { .. }))
    };
    let mut body_expr = match stmts.as_slice() {
        [Stmt::Return(Some(x))] => x.clone(),
        [Stmt::ExprStmt(x @ Expr::Assign { .. })] => x.clone(),
        [Stmt::ExprStmt(x @ Expr::Assign { .. }), Stmt::Return(None)] => x.clone(),
        [x] if delegating(x) => match x {
            Stmt::ExprStmt(e) => e.clone(),
            _ => return None,
        },
        [x, Stmt::Return(None)] if delegating(x) => match x {
            Stmt::ExprStmt(e) => e.clone(),
            _ => return None,
        },
        _ => return None,
    };
    // full recursive substitution
    fn subst_all(e: &mut Expr, params: &[u32], call_args: &[Expr]) {
        if let Expr::Local { var, .. } = e {
            if let Some(i) = params.iter().position(|p| p == var) {
                *e = call_args[i].clone();
                return;
            }
        }
        match e {
            Expr::Method { owner, args, .. } => {
                if let Some(o) = owner {
                    subst_all(o, params, call_args);
                }
                args.iter_mut().for_each(|a| subst_all(a, params, call_args));
            }
            Expr::Field { owner: Some(o), .. } => subst_all(o, params, call_args),
            Expr::ArrayIndex { array, index } => {
                subst_all(array, params, call_args);
                subst_all(index, params, call_args);
            }
            Expr::Cast { e: i, .. } | Expr::InstanceOf { e: i, .. } | Expr::Un { e: i, .. }
            | Expr::PreIncDec { e: i, .. } | Expr::PostIncDec { e: i, .. } => {
                subst_all(i, params, call_args)
            }
            Expr::Bin { l, r, .. } => {
                subst_all(l, params, call_args);
                subst_all(r, params, call_args);
            }
            Expr::Cond { c, t, f } => {
                subst_all(c, params, call_args);
                subst_all(t, params, call_args);
                subst_all(f, params, call_args);
            }
            Expr::Assign { target, value, .. } => {
                subst_all(target, params, call_args);
                subst_all(value, params, call_args);
            }
            Expr::NewArray { dims, init, .. } => {
                dims.iter_mut().for_each(|d| subst_all(d, params, call_args));
                if let Some(vals) = init {
                    vals.iter_mut().for_each(|v| subst_all(v, params, call_args));
                }
            }
            _ => {}
        }
    }
    subst_all(&mut body_expr, &params, args);
    // The bridge body may itself reference other bridges.
    let mut wrapped = Stmt::Return(Some(body_expr));
    inline_accessors(&mut wrapped, _pc, pool);
    if let Stmt::Return(Some(x)) = wrapped {
        Some(x)
    } else {
        None
    }
}

/// (class internal name, method name) from the EnclosingMethod attribute.
fn enclosing_method_of(pc: &PoolClass) -> Option<(String, String)> {
    let b = pc.class_attr("EnclosingMethod")?;
    if b.len() < 4 {
        return None;
    }
    let ci = u16::from_be_bytes([b[0], b[1]]);
    let mi = u16::from_be_bytes([b[2], b[3]]);
    let cls = pc.class_name(ci)?.to_string();
    let (mname, _) = pc.name_and_type(mi)?;
    Some((cls, mname.to_string()))
}

/// Source header for a local/member class rendered from its class
/// Signature: `Name<Params> extends Super<S> implements A<X>, B`. The
/// walker's erased fallback drops the superclass whenever an interface
/// exists and renders raw interface names — jdk11 ReduceOps' local
/// `class ReducingSink extends Box<U> implements AccumulatingSink<T, U,
/// ReducingSink>` printed as `class ReducingSink implements
/// ReduceOps.AccumulatingSink`: raw interface => "not abstract and does
/// not override combine", lost Box<U> => every `state` reference died
/// (56 symbol errors + 13 override errors in ReduceOps alone).
fn sig_class_header(lpc: &PoolClass, simple: &str, pool: &ClassPool) -> Option<String> {
    use jcdc_jvm::GenericType as G;
    let sig_bytes = lpc.class_attr("Signature")?;
    if sig_bytes.len() < 2 {
        return None;
    }
    let sig = lpc
        .utf8(u16::from_be_bytes([sig_bytes[0], sig_bytes[1]]))
        .and_then(|x| parse_class_signature(x))?;
    let vt = empty_vt();
    let p = Printer::new(lpc, pool, &vt);
    let mut h = String::from(simple);
    let mut tp = String::new();
    jcdc_jvm::render_type_params(&sig.params, &mut tp);
    h.push_str(&tp);
    let sup_is_object = matches!(&sig.superclass, G::Class(cs)
        if cs.parts.first().map(|q| q.name == "Object").unwrap_or(false));
    if !sup_is_object && matches!(&sig.superclass, G::Class(_) | G::Array(_) | G::TypeVar(_)) {
        h.push_str(" extends ");
        h.push_str(&p.type_name(&TypeRef::G(sig.superclass.clone())));
    }
    if !sig.interfaces.is_empty() {
        h.push_str(" implements ");
        let names: Vec<String> = sig
            .interfaces
            .iter()
            .map(|i| p.type_name(&TypeRef::G(i.clone())))
            .collect();
        h.push_str(&names.join(", "));
    }
    Some(h)
}

fn classify_nested(name: &str, rest: &str, pc: &PoolClass) -> (NestedKind, String, ClassAccessFlags) {
    if rest.contains("lambda$") {
        return (NestedKind::Lambda, rest.to_string(), pc.access());
    }
    if let Some(bytes) = pc.class_attr("InnerClasses") {
        if let Some(attr) = parse_inner_classes(bytes) {
            for e in &attr.classes {
                let is_self = pc
                    .class_name(e.inner_class_info_index)
                    .map(|n| n == name)
                    .unwrap_or(false);
                if is_self {
                    let simple_raw = if e.inner_name_index == 0 {
                        rest.rsplit('$').next().unwrap_or(rest).to_string()
                    } else {
                        pc.utf8(e.inner_name_index).unwrap_or(rest).to_string()
                    };
                    // Digit-leading simple names are desugared (no source
                    // identifier can start with a digit): all digits =
                    // anonymous (inline at `new` sites); digits + identifier =
                    // javac's local-class encoding `Outer$1Var` (a NAMED
                    // local class — declared at its use site, stripped name).
                    if simple_raw.chars().next().map(|c| c.is_ascii_digit()).unwrap_or(false) {
                        let (kind, simple) = split_desugared_name(&simple_raw, true);
                        return (kind, simple, e.inner_class_access_flags);
                    }
                    let kind = if e.inner_name_index == 0 {
                        NestedKind::Anonymous
                    } else if e.outer_class_info_index == 0 {
                        NestedKind::Local
                    } else {
                        NestedKind::Member
                    };
                    return (kind, simple_raw, e.inner_class_access_flags);
                }
            }
        }
    }
    // Heuristic fallback (no self InnerClasses entry — javac omits it for
    // some local classes, e.g. ClassSpecializer$Factory$1Var): all-digit
    // simple name → anonymous; digits+identifier → local class with the
    // digit prefix stripped; else member.
    let simple_last = rest.rsplit('$').next().unwrap_or(rest);
    let (kind, simple) = split_desugared_name(simple_last, false);
    let kind = if matches!(kind, NestedKind::Anonymous) && !simple_last.chars().all(|c| c.is_ascii_digit()) {
        // digits+identifier with no attribute evidence: local class.
        kind
    } else if matches!(kind, NestedKind::Local) {
        kind
    } else if !simple_last.is_empty() && simple_last.chars().all(|c| c.is_ascii_digit()) {
        NestedKind::Anonymous
    } else if simple_last.chars().next().map(|c| c.is_ascii_digit()).unwrap_or(false) {
        NestedKind::Local
    } else {
        NestedKind::Member
    };
    (kind, simple, pc.access())
}

/// Classify a desugared nested simple name: all digits → Anonymous;
/// leading digits followed by a valid identifier → Local (name = digits
/// stripped, javac's `Outer$1Var` encoding of a method-local class);
/// otherwise `fallback_anon` decides (an absent inner_name means anonymous).
fn split_desugared_name(simple: &str, fallback_anon: bool) -> (NestedKind, String) {
    let dlen = simple.chars().take_while(|c| c.is_ascii_digit()).count();
    if dlen == 0 {
        return (
            if fallback_anon { NestedKind::Anonymous } else { NestedKind::Member },
            simple.to_string(),
        );
    }
    if dlen == simple.len() {
        return (NestedKind::Anonymous, simple.to_string());
    }
    let tail = &simple[dlen..];
    let valid_ident = tail.chars().next().map(|c| c.is_ascii_alphabetic() || c == '_' || c == '$').unwrap_or(false)
        && tail.chars().all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$');
    if valid_ident {
        (NestedKind::Local, tail.to_string())
    } else {
        (NestedKind::Member, simple.to_string())
    }
}

fn parse_inner_classes(info: &[u8]) -> Option<jcdc_classfile::InnerClassesAttribute> {
    fn u2(b: &[u8], i: &mut usize) -> Option<u16> {
        let v = u16::from_be_bytes([*b.get(*i)?, *b.get(*i + 1)?]);
        *i += 2;
        Some(v)
    }
    let mut i = 0;
    let n = u2(info, &mut i)? as usize;
    let mut classes = Vec::with_capacity(n);
    for _ in 0..n {
        let inner_class_info_index = u2(info, &mut i)?;
        let outer_class_info_index = u2(info, &mut i)?;
        let inner_name_index = u2(info, &mut i)?;
        let flags = u2(info, &mut i)?;
        classes.push(jcdc_classfile::InnerClass {
            inner_class_info_index,
            outer_class_info_index,
            inner_name_index,
            inner_class_access_flags: ClassAccessFlags::from_bits_truncate(flags),
        });
    }
    Some(jcdc_classfile::InnerClassesAttribute { classes })
}

// ---------------------------------------------------------------------------
// Entry points
// ---------------------------------------------------------------------------

/// Decompile one class as a standalone compilation unit, inlining its
/// nested/anonymous family.
pub fn decompile_class(pc: &PoolClass, pool: &ClassPool, opts: &ClassOptions) -> anyhow::Result<String> {
    if pc.is_module() {
        return decompile_module_info(pc);
    }
    // If this class is itself nested and its outer class is in the pool,
    // decompile from the outer root so the output is a valid compilation unit.
    if let Some(outer) = find_outer(pc, pool) {
        let opc = pool.get(&outer).unwrap();
        return decompile_class(&opc, pool, opts);
    }
    let fam = Family::collect(pc, pool);
    let mut out = String::new();
    let internal = pc.internal_name.clone();
    if let Some(slash) = internal.rfind('/') {
        out.push_str(&format!("package {};\n\n", internal[..slash].replace('/', ".")));
    }
    emit_class(pc, pool, opts, &fam, &mut out, 0, true)?;
    Ok(out)
}

/// Nearest existing outer class by `$` splitting (None for top-level).
pub fn find_outer(pc: &PoolClass, pool: &ClassPool) -> Option<String> {
    let name = &pc.internal_name;
    let mut cut = name.as_str();
    while let Some(d) = cut.rfind('$') {
        cut = &cut[..d];
        if pool.get(cut).is_some() {
            return Some(cut.to_string());
        }
    }
    None
}

/// True if this class will be emitted inside another compilation unit.
pub fn is_nested_in_family(pc: &PoolClass, pool: &ClassPool) -> bool {
    find_outer(pc, pool).is_some()
}

/// Name-based variant: True if a `$`-prefix of this internal name exists in
/// the pool (so the class is emitted inside that outer class).
pub fn is_nested_in_pool(internal_name: &str, pool: &ClassPool) -> bool {
    let mut cut = internal_name;
    while let Some(d) = cut.rfind('$') {
        cut = &cut[..d];
        if pool.get(cut).is_some() {
            return true;
        }
    }
    false
}

// ---------------------------------------------------------------------------
// Class emission
// ---------------------------------------------------------------------------

thread_local! {
    /// Classes currently being emitted on this thread; guards against
    /// cyclic nested/anonymous emission (class A inlines B which inlines A).
    static EMITTING: std::cell::RefCell<std::collections::HashSet<String>> =
        std::cell::RefCell::new(std::collections::HashSet::new());
}

thread_local! {
    static EMIT_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

thread_local! {
    /// During the fix_lambda_captures extraction walk: the simple names
    /// whose ClassDecls were spliced into the cloned lambda body (their
    /// captures may be lambda params — must NOT be hoisted out).
    static LOCAL_DECL_SITES: std::cell::RefCell<Option<Vec<String>>> =
        const { std::cell::RefCell::new(None) };
}

thread_local! {
    /// Local-class names already declared in the outer method scope by
    /// fix_lambda_captures (extracted from lambda impl bodies at pass
    /// time): walk_stmt_anon must NOT re-declare them inside the lambda
    /// body at print time (shadowing would split the class identity —
    /// `FixedWindow::new` inside vs `FixedWindow::finish` outside).
    static EXTERN_DECL: std::cell::RefCell<HashSet<String>> =
        std::cell::RefCell::new(HashSet::new());

    /// Local-class names whose decl was extracted at one statement and
    /// MENTIONED again at a later statement of the same method: the decl
    /// must move to a position dominating both sites.
    static EXTERN_REDECL: std::cell::RefCell<HashSet<String>> =
        std::cell::RefCell::new(HashSet::new());
}

thread_local! {
    /// Depth of emit_anon_body emission: while > 0, LOCAL_DECL_HOIST
    /// entries are NOT drained by inline_anonymous — a local class
    /// declared inside an inlined anonymous/local body must land in the
    /// REAL method (jdk26 Gatherers: FixedWindow declared inside the
    /// supplier lambda was invisible to the sibling `FixedWindow::finish`
    /// method refs — 80 symbol errors).
    static ANON_BODY_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

struct AnonBodyDepthGuard;
impl Drop for AnonBodyDepthGuard {
    fn drop(&mut self) {
        ANON_BODY_DEPTH.with(|d| d.set(d.get() - 1));
    }
}

thread_local! {
    /// LAMBDA-body emission depth (printer): local-class decls found here
    /// must bubble to the outer method (sibling method refs cannot see
    /// into the lambda scope). Anonymous-CLASS bodies (ANON_BODY_DEPTH
    /// only) keep the old inline behavior: their methods' decls resolve
    /// locally (jdk26 ReferencePipeline.flatMap's FlatMap is used only
    /// inside the anon's opWrapSink).
    static LAMBDA_BODY_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

/// Mark the scope of an inlined anonymous/local/lambda body so
/// inline_anonymous leaves bubbled local-class decls on the stack for the
/// REAL method's drain (lambda bodies are decompiled at PRINT time —
/// their decls must still land in the outer method scope).
pub(crate) fn lambda_body_depth_enter() -> LambdaBodyDepthGuardEntry {
    ANON_BODY_DEPTH.with(|d| d.set(d.get() + 1));
    LAMBDA_BODY_DEPTH.with(|d| d.set(d.get() + 1));
    LambdaBodyDepthGuardEntry
}

pub struct LambdaBodyDepthGuardEntry;
impl Drop for LambdaBodyDepthGuardEntry {
    fn drop(&mut self) {
        ANON_BODY_DEPTH.with(|d| d.set(d.get() - 1));
        LAMBDA_BODY_DEPTH.with(|d| d.set(d.get() - 1));
    }
}

thread_local! {
    /// Local-class declarations bubble up from nested blocks to the
    /// METHOD-top block: type mentions (hoisted `List<Var>` decls) can
    /// precede the instantiation's enclosing block, and a local class is
    /// only visible from its declaration point — the top block is the
    /// only position that can satisfy every reference (jdk11
    /// ClassSpecializer$Factory$1Var).
    static LOCAL_DECL_HOIST: std::cell::RefCell<Vec<(String, Stmt)>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

thread_local! {
    /// While an anonymous-class body is being emitted: local-class
    /// declarations that lexically belong to the OUTER method (their
    /// EnclosingMethod names the outer class, not the anon's) collect
    /// here so build_anon_new can hand them to the outer pending list —
    /// the declaration must sit before the anonymous `new`, in the
    /// enclosing method scope, or the anon's own type arguments cannot
    /// resolve it (jdk11 ReduceOps: `new ReduceOp<T, U, ReducingSink>()
    /// { ... }` with `class ReducingSink` declared inside the anon's
    /// makeSink — "cannot find symbol ReducingSink" x56).
    static ANON_HOIST: std::cell::RefCell<Vec<Stmt>> = const { std::cell::RefCell::new(Vec::new()) };
}

thread_local! {
    /// Set while an anonymous-class METHOD body is about to be walked:
    /// the FIRST Block arm consumes it and becomes the designated splice
    /// point for local-class declarations. Inner blocks leave pending
    /// decls alone so they bubble to the method-top block — the only
    /// position that precedes EVERY reference (jdk26 ClassSpecializer
    /// Factory$1$1Var: the loop-body splice put `class Var` after the
    /// method-top `Var NO_THIS = ...` uses — "找不到符号" / forward
    /// reference).
    static ANON_TOP_BLOCK: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

struct EmitGuard(String);
impl Drop for EmitGuard {
    fn drop(&mut self) {
        EMITTING.with(|e| {
            e.borrow_mut().remove(&self.0);
        });
    }
}

fn emit_class(
    pc: &PoolClass,
    pool: &ClassPool,
    opts: &ClassOptions,
    fam: &Family,
    out: &mut String,
    indent: usize,
    is_root: bool,
) -> anyhow::Result<()> {
    let pad = "    ".repeat(indent);
    let internal = pc.internal_name.clone();
    let cyclic = EMITTING.with(|e| !e.borrow_mut().insert(internal.clone()));
    if cyclic {
        out.push_str(&format!(
            "{}// $JCDC: skipped cyclic emission of {}\n",
            pad, internal
        ));
        return Ok(());
    }
    let _emit_guard = EmitGuard(internal.clone());
    let simple = fam
        .nested
        .get(&internal)
        .map(|n| n.simple.clone())
        .unwrap_or_else(|| simple_name(&internal));

    let class_sig = pc.class_attr("Signature").and_then(|b| {
        if b.len() >= 2 {
            let idx = u16::from_be_bytes([b[0], b[1]]);
            pc.utf8(idx).and_then(|s| parse_class_signature(s))
        } else {
            None
        }
    });

    let acc = if is_root {
        pc.access()
    } else {
        fam.nested.get(&internal).map(|n| n.access).unwrap_or_else(|| pc.access())
    };
    let major = pc.cf.major_version;
    let is_enum = acc.contains(ClassAccessFlags::ENUM) || pc.is_enum();
    let is_interface = acc.contains(ClassAccessFlags::INTERFACE);
    let is_annotation = acc.contains(ClassAccessFlags::ANNOTATION);
    let is_record = pc.is_record();

    let annots = class_annotations(pc);
    if !annots.is_empty() {
        for line in annots.lines() {
            out.push_str(&pad);
            out.push_str(line);
            out.push('\n');
        }
    }

    let mut mods: Vec<&str> = Vec::new();
    if acc.contains(ClassAccessFlags::PUBLIC) {
        mods.push("public");
    }
    if acc.contains(ClassAccessFlags::PROTECTED) {
        mods.push("protected");
    }
    if acc.contains(ClassAccessFlags::PRIVATE) {
        mods.push("private");
    }
    if acc.contains(ClassAccessFlags::ABSTRACT) && !is_annotation && !is_enum {
        mods.push("abstract");
    }
    // Nested member classes: trust the InnerClasses STATIC flag when the
    // class was classified via InnerClasses (its `access` comes from there);
    // only infer static for heuristic-classified classes without this$0.
    let nested_needs_static = !is_root && !is_interface && !is_enum
        && fam.nested.get(&internal).map(|n| n.kind == NestedKind::Member).unwrap_or(false)
        && !class_has_this0(pc)
        && pc.class_attr("InnerClasses").is_none();
    if (acc.contains(ClassAccessFlags::STATIC) || nested_needs_static) && !is_root {
        mods.push("static");
    }
    if acc.contains(ClassAccessFlags::FINAL) && !is_enum && !is_record {
        mods.push("final");
    }
    // javac emits PermittedSubclasses for enums with constant bodies and
    // for records' hierarchies; `sealed` is only source-visible on plain
    // classes/interfaces.
    let permitted: Vec<String> = if is_enum || is_record {
        Vec::new()
    } else {
        pc.class_attr("PermittedSubclasses")
            .map(|b| parse_permitted(b, pc))
            .unwrap_or_default()
    };
    let mut sealed_mod = "";
    if !permitted.is_empty() {
        sealed_mod = "sealed";
    } else if !is_enum && !is_record && major >= 60 && !acc.contains(ClassAccessFlags::FINAL) {
        // non-sealed when a supertype is sealed
        if supertype_is_sealed(pc, pool) {
            sealed_mod = "non-sealed";
        }
    }

    let mut header = pad.clone();
    for m in &mods {
        header.push_str(m);
        header.push(' ');
    }
    if !sealed_mod.is_empty() {
        header.push_str(sealed_mod);
        header.push(' ');
    }
    if is_annotation {
        header.push_str("@interface ");
    } else if is_enum {
        header.push_str("enum ");
    } else if is_record {
        header.push_str("record ");
    } else if is_interface {
        header.push_str("interface ");
    } else {
        header.push_str("class ");
    }
    header.push_str(&simple);

    if let Some(sig) = &class_sig {
        let mut tp = String::new();
        jcdc_jvm::render_type_params(&sig.params, &mut tp);
        header.push_str(&tp);
    }
    if is_record {
        header.push_str(&record_components(pc, pool));
    }

    let super_name = pc.super_name().unwrap_or("").to_string();
    let suppress_super = super_name.is_empty()
        || super_name == "java/lang/Object"
        || (is_enum && super_name == "java/lang/Enum")
        || (is_record && super_name == "java/lang/Record")
        || is_annotation
        || is_record;
    if !suppress_super {
        let rendered = match &class_sig {
            Some(sig) => Printer::new(pc, pool, empty_vt()).type_name(&TypeRef::G(sig.superclass.clone())),
            None => Printer::new(pc, pool, empty_vt()).shorten(&super_name),
        };
        header.push_str(" extends ");
        header.push_str(&rendered);
    }

    let interfaces: Vec<String> = {
        let p = Printer::new(pc, pool, empty_vt());
        if let Some(sig) = &class_sig {
            sig.interfaces.iter().map(|i| p.type_name(&TypeRef::G(i.clone()))).collect()
        } else {
            pc.cf
                .interfaces
                .iter()
                .filter_map(|&i| pc.class_name(i))
                .filter(|n| *n != "java/lang/constant/Constable")
                .map(|n| p.shorten(n))
                .collect()
        }
    };
    if !interfaces.is_empty() && !is_annotation {
        header.push_str(if is_interface { " extends " } else { " implements " });
        header.push_str(&interfaces.join(", "));
    }

    if !permitted.is_empty() {
        let p = Printer::new(pc, pool, empty_vt());
        let names: Vec<String> = permitted.iter().map(|n| p.shorten(n)).collect();
        header.push_str(" permits ");
        header.push_str(&names.join(", "));
    }

    header.push_str(" {");
    out.push_str(&header);
    out.push('\n');

    let inner_pad = "    ".repeat(indent + 1);

    if is_enum {
        emit_enum_constants(pc, pool, opts, fam, out, indent + 1)?;
    }

    // Fields. For member inner classes whose synthetic constructor is
    // hidden, recover instance-field initializers from that constructor.
    let inner_ctor_inits: HashMap<String, Expr> = if !is_root
        && class_has_this0(pc)
        && (0..pc.cf.methods.len()).any(|mi| {
            pc.method_name(mi) == Some("<init>") && is_trivial_inner_ctor(pc, pool, mi)
        })
    {
        // Member inner class: `this$N` references in recovered field
        // initializers must read `Outer.this` (the synthetic field itself
        // is hidden).
        let mut inits = anon_field_inits(pc, pool, &outer_this_map(pc));
        for v in inits.values_mut() {
            // Recovered initializers can still carry bare `this$N` reads
            // (jdk11 LinkedHashMap$LinkedHashIterator `next = this$0.head;`
            // — symbol not found): fold the outer-this chains again on the
            // recovered expressions.
            let mut wrap = Stmt::ExprStmt(std::mem::replace(v, Expr::This));
            let otm = outer_this_map(pc);
            substitute_captures(&mut wrap, &otm, pool);
            *v = match wrap {
                Stmt::ExprStmt(e) => e,
                _ => Expr::This,
            };
            let mut pending: Vec<Stmt> = Vec::new();
            walk_expr_anon(v, pc, pool, fam, &mut pending, &empty_vt());
        }
        inits
    } else {
        HashMap::new()
    };
    // <clinit> handling. When the initializer only assigns static fields of
    // this class, fold the assignments into the field declarations —
    // interfaces cannot express `static final X f;` plus a static-block
    // assignment, and constant holders read better this way.
    let mut static_inits: HashMap<String, Expr> = HashMap::new();
    let mut clinit_body: Option<(Stmt, VarTable)> = None;
    if !is_enum {
        if let Some(ci) = pc.find_own_method("<clinit>", "()V") {
            if let Ok(Some(mut mb)) = decompile_method(pc, pool, ci) {
                let mut body = strip_trailing_return(&mb.body);
                strip_static_init_returns(&mut body);
                inline_anonymous(&mut body, pc, pool, fam, &mb.vt);
                inline_accessors(&mut body, pc, pool);
                // Static initializers need the same call-arg witnesses as
                // method bodies (jdk11 ObjectInputFilter's clinit
                // `doPrivileged(() -> {...})` is ambiguous without the raw
                // PrivilegedAction cast — the vT jdk11 first blocker).
                cast_wildcard_call_args(&mut body, pool, pc, &mb.vt);
                fix_lambda_captures(&mut body, &mut mb.vt, pc, pool, fam);
                restore_enum_switches(&mut body, pc, pool);
                hoist_clinit_returns(&mut body);
                let stmts = stmt_vec(&body);
                let mut all_assigns = !stmts.is_empty();
                let mut folded: HashMap<String, Expr> = HashMap::new();
                // Field emission positions: a folded initializer may not
                // reference a same-class static field declared AT OR AFTER
                // it ("非法前向引用" — jdk17 IOVecWrapper LEN_OFFSET =
                // addressSize with addressSize declared later; the source
                // kept those assignments in the static block).
                let field_pos: HashMap<String, usize> = pc
                    .cf
                    .fields
                    .iter()
                    .enumerate()
                    .filter_map(|(i, f)| {
                        pc.utf8(f.name_index).map(|n| (n.to_string(), i))
                    })
                    .collect();
                fn refs_forward(
                    e: &Expr,
                    pc: &PoolClass,
                    field_pos: &HashMap<String, usize>,
                    my_pos: usize,
                ) -> bool {
                    match e {
                        Expr::Field { cls, name, is_static: true, owner: None, .. }
                            if cls == &pc.internal_name =>
                        {
                            field_pos.get(name).map(|p| *p >= my_pos).unwrap_or(false)
                        }
                        Expr::Field { owner: Some(o), .. } => refs_forward(o, pc, field_pos, my_pos),
                        Expr::Method { owner, args, .. } => {
                            owner.as_deref().map(|o| refs_forward(o, pc, field_pos, my_pos)).unwrap_or(false)
                                || args.iter().any(|a| refs_forward(a, pc, field_pos, my_pos))
                        }
                        Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
                            args.iter().any(|a| refs_forward(a, pc, field_pos, my_pos))
                        }
                        Expr::NewArray { dims, init, .. } => {
                            dims.iter().any(|d| refs_forward(d, pc, field_pos, my_pos))
                                || init.as_ref().map(|v| v.iter().any(|x| refs_forward(x, pc, field_pos, my_pos))).unwrap_or(false)
                        }
                        Expr::ArrayIndex { array, index } => {
                            refs_forward(array, pc, field_pos, my_pos)
                                || refs_forward(index, pc, field_pos, my_pos)
                        }
                        Expr::Bin { l, r, .. } | Expr::Assign { target: l, value: r, .. } => {
                            refs_forward(l, pc, field_pos, my_pos) || refs_forward(r, pc, field_pos, my_pos)
                        }
                        Expr::Cond { c, t, f } => {
                            refs_forward(c, pc, field_pos, my_pos)
                                || refs_forward(t, pc, field_pos, my_pos)
                                || refs_forward(f, pc, field_pos, my_pos)
                        }
                        Expr::Un { e: x, .. }
                        | Expr::Cast { e: x, .. }
                        | Expr::InstanceOf { e: x, .. }
                        | Expr::PreIncDec { e: x, .. }
                        | Expr::PostIncDec { e: x, .. } => refs_forward(x, pc, field_pos, my_pos),
                        Expr::StringConcat(parts) => parts.iter().any(|pp| match pp {
                            crate::expr::ConcatPart::Str(x) => refs_forward(x, pc, field_pos, my_pos),
                            _ => false,
                        }),
                        Expr::Lambda(l) => l.captures.iter().any(|a| refs_forward(a, pc, field_pos, my_pos)),
                        _ => false,
                    }
                }
                for st in &stmts {
                    match st {
                        Stmt::ExprStmt(Expr::Assign { target, value, .. }) => {
                            match &**target {
                                Expr::Field { name, is_static: true, cls, .. }
                                    if cls == &pc.internal_name =>
                                {
                                    let my_pos = field_pos.get(name).copied().unwrap_or(usize::MAX);
                                    if refs_forward(value, pc, &field_pos, my_pos) {
                                        all_assigns = false;
                                    } else {
                                        folded.insert(name.clone(), (**value).clone());
                                    }
                                }
                                _ => all_assigns = false,
                            }
                        }
                        Stmt::Comment(_) => {}
                        _ => all_assigns = false,
                    }
                }
                if all_assigns {
                    static_inits = folded;
                } else {
                    clinit_body = Some((body, mb.vt));
                }
            }
        }
    }

    let comp_names = record_component_names(pc);
    let mut has_assert_field = false;
    for (fi, f) in pc.cf.fields.iter().enumerate() {
        let fname0 = pc.utf8(f.name_index).unwrap_or("").to_string();
        // `$assertionsDisabled` is synthetic but referenced by decompiled
        // assert guards; it must be declared for the output to compile —
        // under a renamed identifier, because javac reserves the exact
        // name for its own compiler-synthesized field.
        let keep_synthetic = fname0 == "$assertionsDisabled";
        if keep_synthetic {
            has_assert_field = true;
        }
        let fname = if keep_synthetic {
            ASSERT_FIELD.to_string()
        } else {
            fname0.clone()
        };
        if !opts.show_synthetic
            && f.access_flags.contains(FieldAccessFlags::SYNTHETIC)
            && !keep_synthetic
        {
            continue;
        }
        if is_enum && (f.access_flags.contains(FieldAccessFlags::ENUM) || fname == "$VALUES") {
            continue;
        }
        if is_record && comp_names.contains(&fname) {
            continue;
        }
        let init = inner_ctor_inits
            .get(&fname0)
            .or_else(|| static_inits.get(&fname0));
        emit_field_init(pc, pool, fi, out, indent + 1, init)?;
    }

    // <clinit>
    if let Some(ci) = pc.find_own_method("<clinit>", "()V") {
        let hide = is_enum && clinit_only_enum_init(pc, pool, ci);
        if !hide {
            let prepared = if is_enum {
                decompile_method(pc, pool, ci)
                    .ok()
                    .flatten()
                    .map(|mb| {
                        let mut body = strip_trailing_return(&mb.body);
                        strip_static_init_returns(&mut body);
                        strip_enum_const_stores(&mut body, pc);
                        inline_anonymous(&mut body, pc, pool, fam, &mb.vt);
                        inline_accessors(&mut body, pc, pool);
                        restore_enum_switches(&mut body, pc, pool);
                        hoist_clinit_returns(&mut body);
                        (body, mb.vt)
                    })
            } else {
                clinit_body.take()
            };
            if let Some((body, vt)) = prepared {
                let text = Printer::new(pc, pool, &vt).with_indent(indent + 1).into_string(&body);
                if !text.trim().is_empty() {
                    out.push('\n');
                    out.push_str(&inner_pad);
                    out.push_str("static {\n");
                    out.push_str(&text);
                    out.push_str(&inner_pad);
                    out.push_str("}\n");
                }
            }
        }
    }

    // Assert-holder field living on a synthetic sibling class (interfaces
    // get `ConstantGroup$1.$assertionsDisabled`): the references print
    // bare, so declare the field here when the pool references one and
    // this class does not carry it.
    if !has_assert_field
        && (0..pc.cf.constant_pool.len()).any(|i| {
            matches!(jcdc_classfile::get_entry(&pc.cf.constant_pool, i as u16),
                Some(jcdc_classfile::ConstantPoolEntry::Fieldref(fr))
                    if pc.utf8(
                        jcdc_classfile::get_entry(&pc.cf.constant_pool, fr.name_and_type_index)
                            .and_then(|nt| match nt {
                                jcdc_classfile::ConstantPoolEntry::NameAndType(n) => Some(n.name_index),
                                _ => None,
                            })
                            .unwrap_or(0)
                    ) == Some("$assertionsDisabled"))
        })
    {
        let top = pc.internal_name.split('$').next().unwrap_or(&pc.internal_name);
        let top_simple = top.rsplit('/').next().unwrap_or(top);
        out.push_str(&inner_pad);
        out.push_str(&format!(
            "static final boolean {} = !{}.class.desiredAssertionStatus();\n",
            ASSERT_FIELD, top_simple
        ));
    }

    // Methods.
    let skip = methods_to_skip(pc, pool, is_enum, is_record, opts);
    for mi in 0..pc.cf.methods.len() {
        if skip.contains(&mi) {
            continue;
        }
        emit_method(pc, pool, fam, mi, out, indent + 1)?;
    }

    // Nested member/local classes.
    for child in fam.direct_children(&internal) {
        let Some(npc) = pool.get(&child.name) else { continue };
        out.push('\n');
        emit_class(&npc, pool, opts, fam, out, indent + 1, false)?;
    }

    out.push_str(&pad);
    out.push_str("}\n");
    Ok(())
}

fn methods_to_skip(
    pc: &PoolClass,
    pool: &ClassPool,
    is_enum: bool,
    is_record: bool,
    opts: &ClassOptions,
) -> HashSet<usize> {
    let mut skip = HashSet::new();
    let lambda_methods = collect_lambda_methods(pc);
    for mi in 0..pc.cf.methods.len() {
        let m = &pc.cf.methods[mi];
        let name = pc.utf8(m.name_index).unwrap_or("").to_string();
        if name == "<clinit>" || lambda_methods.contains(&mi) {
            skip.insert(mi);
            continue;
        }
        if !opts.show_synthetic
            && (m.access_flags.contains(MethodAccessFlags::SYNTHETIC)
                || m.access_flags.contains(MethodAccessFlags::BRIDGE))
        {
            skip.insert(mi);
            continue;
        }
        if !opts.show_private && m.access_flags.contains(MethodAccessFlags::PRIVATE) {
            skip.insert(mi);
            continue;
        }
        // javac-GENERATED enum accessors only: match by descriptor, not
        // bare name — jdk17 ConstantPool.Tag declares its own
        // `private static Tag valueOf(byte)` which must survive (dropping
        // it left getTagAt calling a nonexistent overload).
        if is_enum && m.access_flags.contains(MethodAccessFlags::STATIC) {
            let d = pc.method_desc(mi).unwrap_or("");
            let self_l = format!("L{};", pc.internal_name);
            let is_generated = ((name == "values" || name == "$values")
                && d == format!("()[{}", self_l))
                || (name == "valueOf" && d == format!("(Ljava/lang/String;){}", self_l));
            if is_generated {
                skip.insert(mi);
                continue;
            }
        }
        if is_record && is_synthetic_record_method(pc, pool, mi) {
            skip.insert(mi);
            continue;
        }
        // equals/hashCode/toString generated as a single ObjectMethods
        // invokedynamic (records and record-like classes): implicit in
        // source, hidden like the record case.
        if matches!(name.as_str(), "equals" | "hashCode" | "toString")
            && is_object_methods_indy(pc, mi)
        {
            skip.insert(mi);
            continue;
        }
        // Synthetic outer-instance constructor of a member inner class.
        if name == "<init>" && class_has_this0(pc) && is_trivial_inner_ctor(pc, pool, mi) {
            skip.insert(mi);
        }
    }
    skip
}

/// True if an inner class constructor is compiler-generated: it only stores
/// this$0 (optionally with requireNonNull), calls super(), and copies
/// field-initializer values into this class's own instance fields.
/// True when the constructor's last descriptor parameter is a synthetic
/// marker class (`Outer$N`, empty + ACC_SYNTHETIC) — javac ≤10 adds it to
/// bridge private inner constructors.
fn marker_ctor(pc: &PoolClass, mi: usize) -> bool {
    let Some(d) = pc.method_desc(mi) else { return false };
    let Some(md) = parse_method_descriptor(d) else { return false };
    let Some(JavaType::Object(last)) = md.args.last() else { return false };
    last != &pc.internal_name
        && last.rsplit('$').next().map(|t| !t.is_empty() && t.chars().all(|c| c.is_ascii_digit())).unwrap_or(false)
}

fn is_trivial_inner_ctor(pc: &PoolClass, pool: &ClassPool, mi: usize) -> bool {
    // Only a parameterless (besides the outer instance / marker) ctor can
    // be hidden and its field stores recovered as field initializers; a
    // ctor with real parameters must stay visible.
    if let Some(d) = pc.method_desc(mi) {
        if let Some(md) = parse_method_descriptor(d) {
            let has_this0 = class_has_this0(pc);
            let n = md.args.len();
            let skip = (if has_this0 { 1 } else { 0 })
                + usize::from(n >= 2 && marker_ctor(pc, mi));
            if n > skip {
                return false;
            }
        }
    }
    let Ok(Some(mb)) = decompile_method(pc, pool, mi) else { return false };
    let stmts = stmt_vec(&mb.body);
    if stmts.is_empty() {
        return false;
    }
    let field_names: HashSet<String> = pc
        .cf
        .fields
        .iter()
        .filter(|f| !f.access_flags.contains(FieldAccessFlags::STATIC))
        .filter_map(|f| pc.utf8(f.name_index).map(|s| s.to_string()))
        .collect();
    stmts.iter().all(|st| match st {
        Stmt::ExprStmt(Expr::Method { name: n, .. }) if n == "<init>" => true,
        Stmt::ExprStmt(Expr::Method { name: n, cls, .. })
            if n == "requireNonNull" && cls == "java/util/Objects" => true,
        Stmt::ExprStmt(Expr::Assign { target, .. }) => match &**target {
            Expr::Field { name: f, is_static: false, .. } => {
                f.starts_with("this$") || field_names.contains(f)
            }
            _ => false,
        },
        Stmt::LocalDef { .. } => true,
        Stmt::Return(None) => true,
        Stmt::Comment(_) => true,
        _ => false,
    })
}

/// True if a DIRECT supertype carries PermittedSubclasses (sealed
/// hierarchy). Only the immediate superclass/interfaces count: sealing
/// TERMINATES at a `non-sealed` (or final) intermediate, so walking the
/// ancestor chain wrongly marks grandchildren — jdk26
/// `WeakHashMap$Entry extends WeakReference` got `non-sealed` because
/// Reference (grandparent) is sealed, but WeakReference itself is
/// non-sealed, and javac rejects it ("class Entry has no sealed
/// supertype").
fn supertype_is_sealed(pc: &PoolClass, pool: &ClassPool) -> bool {
    if let Some(c) = pc.super_name() {
        if c != "java/lang/Object" {
            if let Some(sp) = pool.get(c) {
                if sp.class_attr("PermittedSubclasses").is_some() {
                    return true;
                }
            }
        }
    }
    for &i in &pc.cf.interfaces {
        if let Some(n) = pc.class_name(i) {
            if let Some(ip) = pool.get(n) {
                if ip.class_attr("PermittedSubclasses").is_some() {
                    return true;
                }
            }
        }
    }
    false
}

/// True if the class declares a synthetic `this$0` outer-instance field.
/// True when a nested class's constructor takes the enclosing instance as
/// its first parameter even though the class itself has no `this$0` field
/// (the field lives on an inner superclass, e.g. `ListItr extends Itr`).
/// javac passes the outer instance straight to `super(...)`.
/// True when the class's own InnerClasses entry marks it static. Class-file
/// level access flags cannot express this (0x0008 there is ACC_SUPER).
pub(crate) fn nested_is_static(pc: &PoolClass) -> bool {
    let Some(bytes) = pc.class_attr("InnerClasses") else { return false };
    let Some(attr) = parse_inner_classes(bytes) else { return false };
    attr.classes.iter().any(|e| {
        pc.class_name(e.inner_class_info_index)
            .map(|n| n == pc.internal_name)
            .unwrap_or(false)
            && e
                .inner_class_access_flags
                .contains(jcdc_classfile::ClassAccessFlags::STATIC)
    })
}

pub(crate) fn outer_param_via_super(pc: &PoolClass, desc: &str) -> bool {
    let Some(md) = parse_method_descriptor(desc) else { return false };
    let Some(JavaType::Object(first)) = md.args.first() else { return false };
    // The parameter type must be the class's own this$0 field type...
    for f in &pc.cf.fields {
        let is_this0 = pc.utf8(f.name_index).map(|n| n.starts_with("this$")).unwrap_or(false);
        if is_this0 {
            if let Some(d) = pc.utf8(f.descriptor_index) {
                if d == format!("L{};", first) {
                    return true;
                }
            }
        }
    }
    // ...or an enclosing class in the $-chain (the field lives on an
    // inner superclass and the instance is forwarded to super()).
    let name = &pc.internal_name;
    let mut prefix = name.as_str();
    while let Some(i) = prefix.rfind('$') {
        prefix = &prefix[..i];
        if prefix == first {
            return true;
        }
    }
    false
}

/// (param slot, this$N field name) for the synthetic outer-instance ctor
/// parameter, when the class stores it in a field.
fn outer_param_slot(pc: &PoolClass) -> Option<(u16, String)> {
    if !class_has_this0(pc) {
        return None;
    }
    let fname = pc
        .cf
        .fields
        .iter()
        .find_map(|f| {
            pc.utf8(f.name_index)
                .filter(|n| n.starts_with("this$"))
                .map(|n| n.to_string())
        })?;
    Some((1, fname))
}

fn class_has_this0(pc: &PoolClass) -> bool {
    pc.cf.fields.iter().any(|f| {
        pc.utf8(f.name_index)
            .map(|n| n.starts_with("this$"))
            .unwrap_or(false)
    })
}

fn parse_permitted(info: &[u8], pc: &PoolClass) -> Vec<String> {
    let mut out = Vec::new();
    if info.len() < 2 {
        return out;
    }
    let n = u16::from_be_bytes([info[0], info[1]]) as usize;
    for i in 0..n {
        let off = 2 + i * 2;
        if off + 2 > info.len() {
            break;
        }
        let idx = u16::from_be_bytes([info[off], info[off + 1]]);
        if let Some(name) = pc.class_name(idx) {
            out.push(name.to_string());
        }
    }
    out
}

fn collect_lambda_methods(pc: &PoolClass) -> HashSet<usize> {
    let mut set = HashSet::new();
    for mi in 0..pc.cf.methods.len() {
        let name = pc.method_name(mi).unwrap_or("");
        if name.starts_with("lambda$") {
            set.insert(mi);
        }
    }
    set
}

fn simple_name(internal: &str) -> String {
    let last = internal.rsplit('/').next().unwrap_or(internal);
    let simple = last.rsplit('$').next().unwrap_or(last);
    if simple.is_empty() {
        last.to_string()
    } else {
        simple.to_string()
    }
}

fn record_component_names(pc: &PoolClass) -> Vec<String> {
    let mut names = Vec::new();
    if let Some(bytes) = pc.class_attr("Record") {
        if let Ok(attr) = parse_record_attr(bytes) {
            for c in &attr.components {
                if let Some(n) = pc.utf8(c.name_index) {
                    names.push(n.to_string());
                }
            }
        }
    }
    names
}

fn record_components(pc: &PoolClass, pool: &ClassPool) -> String {
    let mut out = String::from("(");
    let names = record_component_names(pc);
    for (i, n) in names.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        let ty = pc
            .find_own_field(n, None)
            .and_then(|fi| {
                let d = pc.utf8(pc.cf.fields[fi].descriptor_index)?;
                Some(field_type_of(pc, fi, d))
            })
            .unwrap_or(TypeRef::J(JavaType::Object("java/lang/Object".into())));
        out.push_str(&Printer::new(pc, pool, empty_vt()).type_name(&ty));
        out.push(' ');
        out.push_str(n);
    }
    out.push(')');
    out
}

fn field_type_of(pc: &PoolClass, fi: usize, desc: &str) -> TypeRef {
    let base = parse_field_descriptor(desc).unwrap_or(JavaType::Int);
    if let Some(sig) = pc.field_attr(&pc.cf.fields[fi], "Signature") {
        if sig.len() >= 2 {
            let idx = u16::from_be_bytes([sig[0], sig[1]]);
            if let Some(s) = pc.utf8(idx) {
                if let Some(g) = parse_field_signature(s) {
                    return TypeRef::G(g);
                }
            }
        }
    }
    TypeRef::J(base)
}

fn parse_record_attr(info: &[u8]) -> Result<jcdc_classfile::RecordAttribute, ()> {
    fn u2(b: &[u8], i: &mut usize) -> Result<u16, ()> {
        let v = u16::from_be_bytes([*b.get(*i).ok_or(())?, *b.get(*i + 1).ok_or(())?]);
        *i += 2;
        Ok(v)
    }
    fn u4(b: &[u8], i: &mut usize) -> Result<u32, ()> {
        let v = u32::from_be_bytes([
            *b.get(*i).ok_or(())?,
            *b.get(*i + 1).ok_or(())?,
            *b.get(*i + 2).ok_or(())?,
            *b.get(*i + 3).ok_or(())?,
        ]);
        *i += 4;
        Ok(v)
    }
    let mut i = 0;
    let n = u2(info, &mut i)? as usize;
    let mut components = Vec::with_capacity(n);
    for _ in 0..n {
        let name_index = u2(info, &mut i)?;
        let descriptor_index = u2(info, &mut i)?;
        let na = u2(info, &mut i)? as usize;
        let mut attributes = Vec::with_capacity(na);
        for _ in 0..na {
            let name_index2 = u2(info, &mut i)?;
            let len = u4(info, &mut i)? as usize;
            let bytes = info.get(i..i + len).ok_or(())?.to_vec();
            i += len;
            attributes.push(jcdc_classfile::AttributeInfo { attribute_name_index: name_index2, info: bytes });
        }
        components.push(jcdc_classfile::RecordComponentInfo { name_index, descriptor_index, attributes });
    }
    Ok(jcdc_classfile::RecordAttribute { components })
}

fn is_synthetic_record_method(pc: &PoolClass, pool: &ClassPool, mi: usize) -> bool {
    let name = pc.method_name(mi).unwrap_or("");
    let desc = pc.method_desc(mi).unwrap_or("");
    let access = pc.cf.methods[mi].access_flags;
    if access.contains(MethodAccessFlags::SYNTHETIC) {
        return true;
    }
    // Implicit component accessor: body is exactly `return this.<name>;`.
    {
        let comps = record_component_names(pc);
        if comps.iter().any(|c| c == name) {
            if let Ok(Some(mb)) = decompile_method(pc, pool, mi) {
                let stmts = stmt_vec(&mb.body);
                let implicit = stmts.len() == 1
                    && matches!(&stmts[0], Stmt::Return(Some(Expr::Field { name: fname, is_static: false, .. })) if fname == name);
                if implicit {
                    return true;
                }
            }
        }
    }
    // Implicit toString/hashCode/equals: single ObjectMethods indy return.
    let implicit = matches!(
        (name, desc),
        ("toString", "()Ljava/lang/String;") | ("hashCode", "()I") | ("equals", "(Ljava/lang/Object;)Z")
    );
    if implicit {
        if let Ok(Some(mb)) = decompile_method(pc, pool, mi) {
            let stmts = stmt_vec(&mb.body);
            let only = stmts.len() == 1
                && matches!(&stmts[0], Stmt::Return(Some(Expr::Invokedynamic { bsm_text, .. }))
                    if bsm_text.contains("ObjectMethods"));
            if only {
                return true;
            }
        }
    }
    // Member inner class synthetic constructor: only stores this$0 (+
    // null check) and calls super — implicit in Java source.
    if name == "<init>" && class_has_this0(pc) {
        if let Ok(Some(mb)) = decompile_method(pc, pool, mi) {
            let stmts = stmt_vec(&mb.body);
            let trivial = !stmts.is_empty()
                && stmts.iter().all(|st| match st {
                    Stmt::ExprStmt(Expr::Method { name: n, cls, .. })
                        if n == "<init>" && cls != &pc.internal_name =>
                    {
                        true
                    }
                    Stmt::ExprStmt(Expr::Method { name: n, cls, .. })
                        if n == "requireNonNull" && cls == "java/util/Objects" => true,
                    Stmt::ExprStmt(Expr::Assign { target, .. }) => {
                        matches!(&**target, Expr::Field { name: f, .. } if f.starts_with("this$"))
                    }
                    Stmt::LocalDef { .. } => true,
                    Stmt::Return(None) => true,
                    Stmt::Comment(_) => true,
                    _ => false,
                });
            if trivial {
                return true;
            }
        }
    }
    // Canonical constructor: body is only super() + field copies. A
    // THIS-delegation (`VMStorage(byte,short,int) { this(.., null); }`,
    // jdk26 records) is a real source constructor — skipping it left
    // call sites constructing an arity that no longer exists.
    if name == "<init>" {
        if let Ok(Some(mb)) = decompile_method(pc, pool, mi) {
            let stmts = stmt_vec(&mb.body);
            let trivial = !stmts.is_empty()
                && stmts.iter().all(|st| match st {
                    Stmt::ExprStmt(Expr::Method { name: n, cls, .. })
                        if n == "<init>" && cls != &pc.internal_name =>
                    {
                        true
                    }
                    Stmt::ExprStmt(Expr::Assign { target, .. }) => matches!(&**target, Expr::Field { .. }),
                    Stmt::Return(None) => true,
                    Stmt::Comment(_) => true,
                    _ => false,
                });
            if trivial {
                return true;
            }
        }
    }
    false
}

fn stmt_vec(s: &Stmt) -> Vec<Stmt> {
    match s {
        Stmt::Block(v) => v.clone(),
        other => vec![other.clone()],
    }
}

// ---------------------------------------------------------------------------
// Annotations
// ---------------------------------------------------------------------------

fn class_annotations(pc: &PoolClass) -> String {
    let mut out = String::new();
    for attr in &pc.cf.attributes {
        // CLASS-retention annotations live in RuntimeInvisibleAnnotations and
        // are load-bearing for recompilation: @MethodHandle.PolymorphicSignature
        // (VarHandle/MethodHandle accessors) changes how javac types every
        // call site — without it `int s = STATUS.getAndBitwiseOr(this, m);`
        // resolves to the Object-returning varargs form (ForkJoinTask corpus
        // family).
        let anns = match parse_specialized_attribute(attr, &pc.cf.constant_pool) {
            ParsedAttribute::RuntimeVisibleAnnotations(a)
            | ParsedAttribute::RuntimeInvisibleAnnotations(a) => Some(a),
            _ => None,
        };
        if let Some(a) = anns {
            for an in &a.annotations {
                if let Some(s) = render_annotation(pc, an) {
                    out.push_str(&s);
                    out.push('\n');
                }
            }
        }
    }
    out
}

fn member_annotations(pc: &PoolClass, attrs: &[jcdc_classfile::AttributeInfo]) -> Vec<String> {
    let mut out = Vec::new();
    for attr in attrs {
        // See class_annotations: invisible (CLASS-retention) annotations must
        // survive too (@PolymorphicSignature et al).
        let anns = match parse_specialized_attribute(attr, &pc.cf.constant_pool) {
            ParsedAttribute::RuntimeVisibleAnnotations(a)
            | ParsedAttribute::RuntimeInvisibleAnnotations(a) => Some(a),
            _ => None,
        };
        if let Some(a) = anns {
            for an in &a.annotations {
                if let Some(s) = render_annotation(pc, an) {
                    out.push(s);
                }
            }
        }
    }
    out
}

fn render_annotation(pc: &PoolClass, an: &jcdc_classfile::Annotation) -> Option<String> {
    let type_desc = pc.utf8(an.type_index)?;
    let name = type_desc.trim_start_matches('L').trim_end_matches(';');
    let p = Printer::new(pc, empty_pool(), empty_vt());
    let short = p.shorten(name);
    if an.element_value_pairs.is_empty() {
        return Some(format!("@{}", short));
    }
    let mut s = format!("@{}(", short);
    let single = an.element_value_pairs.len() == 1
        && pc.utf8(an.element_value_pairs[0].0).map(|n| n == "value").unwrap_or(false);
    for (i, (name_idx, v)) in an.element_value_pairs.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        if !single {
            s.push_str(pc.utf8(*name_idx).unwrap_or("?"));
            s.push_str(" = ");
        }
        s.push_str(&render_element_value(pc, v));
    }
    s.push(')');
    Some(s)
}

fn render_element_value(pc: &PoolClass, v: &jcdc_classfile::ElementValue) -> String {
    use jcdc_classfile::ElementValue as EV;
    match v {
        EV::Byte { const_value_index: i }
        | EV::Short { const_value_index: i }
        | EV::Int { const_value_index: i } => const_render(pc, *i, 'I'),
        EV::Char { const_value_index: i } => const_render(pc, *i, 'C'),
        EV::Long { const_value_index: i } => const_render(pc, *i, 'J'),
        EV::Float { const_value_index: i } => const_render(pc, *i, 'F'),
        EV::Double { const_value_index: i } => const_render(pc, *i, 'D'),
        EV::Boolean { const_value_index: i } => const_render(pc, *i, 'Z'),
        EV::String { const_value_index: i } => pc
            // JVMS: an element_value of tag 's' indexes a CONSTANT_Utf8
            // entry directly (not CONSTANT_String).
            .utf8(*i)
            .or_else(|| pc.string_value(*i))
            .map(|s| format!("\"{}\"", crate::emit::escape_string(s)))
            .unwrap_or_else(|| "\"\"".into()),
        EV::Enum { type_name_index, const_name_index } => {
            let t = pc.utf8(*type_name_index).unwrap_or("?");
            let t = t.trim_start_matches('L').trim_end_matches(';');
            let c = pc.utf8(*const_name_index).unwrap_or("?");
            format!("{}.{}", Printer::new(pc, empty_pool(), empty_vt()).shorten(t), c)
        }
        EV::Class { class_info_index } => pc
            .class_name(*class_info_index)
            .map(|n| format!("{}.class", Printer::new(pc, empty_pool(), empty_vt()).shorten(n)))
            .unwrap_or_else(|| "void.class".into()),
        EV::AnnotationType { annotation } => render_annotation(pc, annotation).unwrap_or_else(|| "@?".into()),
        EV::Array { values } => {
            let inner: Vec<String> = values.iter().map(|v| render_element_value(pc, v)).collect();
            format!("{{ {} }}", inner.join(", "))
        }
    }
}

fn const_render(pc: &PoolClass, idx: u16, kind: char) -> String {
    use jcdc_classfile::ConstantPoolEntry as C;
    match jcdc_classfile::get_entry(&pc.cf.constant_pool, idx) {
        Some(C::Integer(i)) => match kind {
            'Z' => (i.value != 0).to_string(),
            'C' => format!(
                "'{}'",
                crate::emit::escape_char(char::from_u32(i.value as u32).unwrap_or('?'))
            ),
            _ => i.value.to_string(),
        },
        Some(C::Long(l)) => format!("{}L", l.value),
        Some(C::Float(f)) => crate::emit::format_float(f.value as f64, true),
        Some(C::Double(d)) => crate::emit::format_float(d.value, false),
        _ => "?".into(),
    }
}

// ---------------------------------------------------------------------------
// Fields & methods
// ---------------------------------------------------------------------------

/// Extract `this.f = expr` field initializers from an anonymous/local
/// class's generated constructor (with captures substituted).
fn anon_field_inits(
    apc: &PoolClass,
    pool: &ClassPool,
    captures: &HashMap<String, Expr>,
) -> HashMap<String, Expr> {
    let mut map = HashMap::new();
    let Some(mi) = (0..apc.cf.methods.len()).find(|&i| apc.method_name(i) == Some("<init>")) else {
        return map;
    };
    let Ok(Some(mb)) = decompile_method(apc, pool, mi) else { return map };
    let mut body = mb.body.clone();
    // The ctor reads the outer instance through its PARAMETER slot before
    // the putfield mirror (`aload_1; getfield head`): normalize those
    // Local reads to this.this$N field reads (and drop the synthetic
    // stores) BEFORE capture substitution, or the param name survives as
    // a Raw `this$0` (LinkedHashMap$LinkedHashIterator field inits).
    // Field inits can also read the capture PARAMS directly (before any
    // putfield mirror), and javac may leave synthetic params unnamed in
    // the LVT (`arg0`): map each capture param Local to its replacement
    // via the ctor's own putfield statements (this$N -> outer-this expr,
    // val$N -> the captured expression) BEFORE the strip/junk passes
    // remove those stores (jdk26 WeakHashMap$HashIterator
    // `index = !arg0.isEmpty() ? arg0.table.length : 0`).
    {
        let otm = outer_this_map(apc);
        let mut rep: HashMap<u32, Expr> = HashMap::new();
        for st in stmt_vec(&body) {
            if let Stmt::ExprStmt(Expr::Assign { target, value, .. }) = st {
                if let Expr::Field { name, is_static: false, .. } = target.as_ref() {
                    let r = if name.starts_with("this$") {
                        otm.get(name.as_str())
                    } else if name.starts_with("val$") {
                        captures.get(name.as_str())
                    } else {
                        None
                    };
                    if let (Some(e), Expr::Local { var, .. }) = (r, value.as_ref()) {
                        rep.insert(*var, e.clone());
                    }
                }
            }
        }
        if !rep.is_empty() {
            rewrite_param_locals(&mut body, &rep);
        }
    }
    strip_inner_ctor_artifacts(&mut body, &mb.vt, outer_param_slot(apc));
    substitute_captures(&mut body, captures, pool);
    let vt = &mb.vt;
    for st in stmt_vec(&body) {
        if let Stmt::ExprStmt(Expr::Assign { target, value, .. }) = st {
            if let Expr::Field { name, is_static: false, .. } = &*target {
                if !name.starts_with("this$") && !name.starts_with("val$") {
                    let mut v = *value.clone();
                    locals_to_raw(&mut v, vt);
                    let mut wrap = Stmt::Return(Some(v));
                    inline_accessors(&mut wrap, apc, pool);
                    let v = match wrap {
                        Stmt::Return(Some(x)) => x,
                        _ => Expr::This,
                    };
                    map.insert(name.clone(), v);
                }
            }
        }
    }
    map
}

/// Replace Local reads of the given var ids with the mapped expressions.
fn rewrite_param_locals(s: &mut Stmt, rep: &HashMap<u32, Expr>) {
    fn ew(e: &mut Expr, rep: &HashMap<u32, Expr>) {
        if let Expr::Local { var, .. } = e {
            if let Some(r) = rep.get(var) {
                *e = r.clone();
                return;
            }
        }
        match e {
            Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
                args.iter_mut().for_each(|a| ew(a, rep))
            }
            Expr::Method { owner, args, .. } => {
                if let Some(o) = owner {
                    ew(o, rep);
                }
                args.iter_mut().for_each(|a| ew(a, rep));
            }
            Expr::Field { owner: Some(o), .. } => ew(o, rep),
            Expr::ArrayIndex { array, index } => {
                ew(array, rep);
                ew(index, rep);
            }
            Expr::Cast { e: i, .. } | Expr::InstanceOf { e: i, .. } | Expr::Un { e: i, .. }
            | Expr::PreIncDec { e: i, .. } | Expr::PostIncDec { e: i, .. } => ew(i, rep),
            Expr::Bin { l, r, .. } => {
                ew(l, rep);
                ew(r, rep);
            }
            Expr::Cond { c, t, f } => {
                ew(c, rep);
                ew(t, rep);
                ew(f, rep);
            }
            Expr::Assign { target, value, .. } => {
                ew(target, rep);
                ew(value, rep);
            }
            Expr::NewArray { dims, init, .. } => {
                dims.iter_mut().for_each(|d| ew(d, rep));
                if let Some(vals) = init {
                    vals.iter_mut().for_each(|v| ew(v, rep));
                }
            }
            Expr::StringConcat(parts) => parts.iter_mut().for_each(|p| {
                if let crate::expr::ConcatPart::Str(i) = p {
                    ew(i, rep);
                }
            }),
            Expr::Lambda(l) => l.captures.iter_mut().for_each(|c| ew(c, rep)),
            Expr::Invokedynamic { args, .. } => args.iter_mut().for_each(|a| ew(a, rep)),
            _ => {}
        }
    }
    fn sw(s: &mut Stmt, rep: &HashMap<u32, Expr>) {
        match s {
            Stmt::Block(v) => v.iter_mut().for_each(|x| sw(x, rep)),
            Stmt::ExprStmt(e) => ew(e, rep),
            Stmt::LocalDef { init: Some(e), .. } => ew(e, rep),
            Stmt::Return(Some(e)) | Stmt::Throw(e) => ew(e, rep),
            Stmt::If { cond, then_stmt, else_stmt } => {
                ew(cond, rep);
                sw(then_stmt, rep);
                if let Some(x) = else_stmt {
                    sw(x, rep);
                }
            }
            Stmt::While { cond, body } => {
                ew(cond, rep);
                sw(body, rep);
            }
            Stmt::DoWhile { body, cond } => {
                sw(body, rep);
                ew(cond, rep);
            }
            Stmt::For { init, cond, update, body } => {
                init.iter_mut().for_each(|i| sw(i, rep));
                if let Some(c) = cond {
                    ew(c, rep);
                }
                update.iter_mut().for_each(|u| ew(u, rep));
                sw(body, rep);
            }
            Stmt::ForEach { iterable, body, .. } => {
                ew(iterable, rep);
                sw(body, rep);
            }
            Stmt::Switch { selector, cases, default, .. } => {
                ew(selector, rep);
                for c in cases.iter_mut() {
                    c.body.iter_mut().for_each(|st| sw(st, rep));
                }
                if let Some(d) = default {
                    sw(d, rep);
                }
            }
            Stmt::Try { body, catches, finally } => {
                sw(body, rep);
                for c in catches.iter_mut() {
                    sw(&mut c.body, rep);
                }
                if let Some(f) = finally {
                    sw(f, rep);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                for r in resources.iter_mut() {
                    sw(r, rep);
                }
                sw(body, rep);
                for c in catches.iter_mut() {
                    sw(&mut c.body, rep);
                }
                if let Some(f) = finally {
                    sw(f, rep);
                }
            }
            Stmt::Synchronized { lock, body } => {
                ew(lock, rep);
                sw(body, rep);
            }
            Stmt::Labeled { body, .. } => sw(body, rep),
            _ => {}
        }
    }
    sw(s, rep)
}

/// Replace leftover `Local` references (anonymous ctor parameters with no
/// capture mapping) with raw name text so class-body rendering with an
/// empty VarTable cannot panic.
fn locals_to_raw(e: &mut Expr, vt: &crate::varalloc::VarTable) {
    if let Expr::Local { var, .. } = e {
        let name = vt.var(*var).name.clone();
        *e = Expr::Raw(name);
        return;
    }
    match e {
        Expr::New { args, .. } => args.iter_mut().for_each(|a| locals_to_raw(a, vt)),
        Expr::Method { owner, args, .. } => {
            if let Some(o) = owner {
                locals_to_raw(o, vt);
            }
            args.iter_mut().for_each(|a| locals_to_raw(a, vt));
        }
        Expr::Field { owner: Some(o), .. } => locals_to_raw(o, vt),
        Expr::ArrayIndex { array, index } => {
            locals_to_raw(array, vt);
            locals_to_raw(index, vt);
        }
        Expr::Cast { e: x, .. }
        | Expr::InstanceOf { e: x, .. }
        | Expr::Un { e: x, .. }
        | Expr::PreIncDec { e: x, .. }
        | Expr::PostIncDec { e: x, .. } => locals_to_raw(x, vt),
        Expr::Bin { l, r, .. } | Expr::Assign { target: l, value: r, .. } => {
            locals_to_raw(l, vt);
            locals_to_raw(r, vt);
        }
        Expr::Cond { c, t, f } => {
            locals_to_raw(c, vt);
            locals_to_raw(t, vt);
            locals_to_raw(f, vt);
        }
        Expr::NewArray { dims, init, .. } => {
            dims.iter_mut().for_each(|d| locals_to_raw(d, vt));
            if let Some(vals) = init {
                vals.iter_mut().for_each(|v| locals_to_raw(v, vt));
            }
        }
        Expr::StringConcat(parts) => parts.iter_mut().for_each(|p| {
            if let crate::expr::ConcatPart::Str(x) = p {
                locals_to_raw(x, vt);
            }
        }),
        _ => {}
    }
}

fn emit_field_init(
    pc: &PoolClass,
    pool: &ClassPool,
    fi: usize,
    out: &mut String,
    indent: usize,
    init: Option<&Expr>,
) -> anyhow::Result<()> {
    emit_field_impl(pc, pool, fi, out, indent, init)
}

#[allow(dead_code)]
fn emit_field(pc: &PoolClass, pool: &ClassPool, fi: usize, out: &mut String, indent: usize) -> anyhow::Result<()> {
    emit_field_impl(pc, pool, fi, out, indent, None)
}

/// The field's generic Signature as a TypeRef, when present.
fn field_sig_typeref(pc: &PoolClass, f: &jcdc_classfile::FieldInfo) -> Option<TypeRef> {
    let bytes = f.attributes.iter().find_map(|a| {
        if pc.utf8(a.attribute_name_index) == Some("Signature") {
            Some(a.info.as_slice())
        } else {
            None
        }
    })?;
    if bytes.len() < 2 {
        return None;
    }
    let idx = u16::from_be_bytes([bytes[0], bytes[1]]);
    let s = pc.utf8(idx)?;
    jcdc_jvm::parse_field_signature(s).map(TypeRef::G)
}

fn emit_field_impl(pc: &PoolClass, pool: &ClassPool, fi: usize, out: &mut String, indent: usize, ctor_init: Option<&Expr>) -> anyhow::Result<()> {
    let f = &pc.cf.fields[fi];
    let raw_name = pc.utf8(f.name_index).unwrap_or("?");
    let name: &str = if raw_name == "$assertionsDisabled" {
        ASSERT_FIELD
    } else {
        raw_name
    };
    let desc = pc.utf8(f.descriptor_index).unwrap_or("I");
    let acc = f.access_flags;
    let pad = "    ".repeat(indent);

    for a in member_annotations(pc, &f.attributes) {
        out.push_str(&pad);
        out.push_str(&a);
        out.push('\n');
    }

    let mut line = pad;
    if acc.contains(FieldAccessFlags::PUBLIC) {
        line.push_str("public ");
    }
    if acc.contains(FieldAccessFlags::PROTECTED) {
        line.push_str("protected ");
    }
    if acc.contains(FieldAccessFlags::PRIVATE) {
        line.push_str("private ");
    }
    if acc.contains(FieldAccessFlags::STATIC) {
        // javac synthesizes `$assertionsDisabled` as static final even in
        // (non-static) INNER classes, but source-level static members are
        // illegal there before Java 16 ("static declaration in inner class").
        // Emit the renamed field as an instance final so the family
        // recompiles; boolean reads inside instance methods resolve the same.
        let inner_assert = raw_name == "$assertionsDisabled" && class_has_this0(pc);
        if !inner_assert {
            line.push_str("static ");
        }
    }
    if acc.contains(FieldAccessFlags::FINAL) {
        line.push_str("final ");
    }
    if acc.contains(FieldAccessFlags::VOLATILE) {
        line.push_str("volatile ");
    }
    if acc.contains(FieldAccessFlags::TRANSIENT) {
        line.push_str("transient ");
    }
    let ty = field_type_of(pc, fi, desc);
    line.push_str(&Printer::new(pc, pool, empty_vt()).type_name(&ty));
    line.push(' ');
    line.push_str(name);
    for attr in &f.attributes {
        if let ParsedAttribute::ConstantValue(cv) = parse_specialized_attribute(attr, &pc.cf.constant_pool) {
            let base = parse_field_descriptor(desc).unwrap_or(JavaType::Int);
            let kind = base.primitive_char().unwrap_or('s');
            let rendered = match jcdc_classfile::get_entry(&pc.cf.constant_pool, cv.constantvalue_index) {
                Some(jcdc_classfile::ConstantPoolEntry::String(_)) => pc
                    .string_value(cv.constantvalue_index)
                    .map(|s| format!("\"{}\"", crate::emit::escape_string(s)))
                    .unwrap_or_default(),
                _ => const_render(pc, cv.constantvalue_index, kind),
            };
            line.push_str(" = ");
            line.push_str(&rendered);
        }
    }
    if !line.contains(" = ") {
        if let Some(init_e) = ctor_init {
            // Generic field type vs erased initializer (`Class<Double> TYPE
            // = (Class<Double>) getPrimitiveClass(...)`): the source cast
            // leaves no bytecode trace; re-insert it.
            let owned: Option<Expr> = match field_sig_typeref(pc, f) {
                Some(TypeRef::G(gt))
                    if !matches!(init_e, Expr::Cast { .. } | Expr::Const(_))
                        && init_e.type_ref() != TypeRef::G(gt.clone())
                        && init_e.type_ref().erased() == TypeRef::G(gt.clone()).erased() =>
                {
                    // A generic-method initializer gets an explicit type
                    // witness instead of a cast: casting a poly expression
                    // can break nested inference (`Map.ofEntries(...)`).
                    let mut call = init_e.clone();
                    let witnessed = match &mut call {
                        Expr::Method { cls, name, desc, type_args, args, .. }
                            if type_args.is_empty() && !args_have_generic_new(args, pool) =>
                        {
                            compute_witness(cls, name, desc, None, &gt, pool, None)
                        }
                        _ => None,
                    };
                    if let Some((w, _)) = witnessed {
                        if let Expr::Method { type_args, .. } = &mut call {
                            *type_args = w;
                        }
                        Some(call)
                    } else if args_have_generic_new(std::slice::from_ref(init_e), pool)
                        || is_generic_call(init_e, pool)
                    {
                        // A generic-call initializer (or one carrying a
                        // diamond new) target-types itself at the field
                        // assignment: javac infers through the whole
                        // nested chain. A synthesized cast freezes the
                        // OUTER call only — the diamond inside still
                        // infers <Object,Object> and the cast becomes
                        // inconvertible ("Map<Object,Object>无法转换为
                        // Map<Key,PermissionCollection>", jdk11
                        // ProtectionDomain cache; jdk17 System.classes).
                        // Leave the bare source form.
                        None
                    } else {
                        Some(Expr::Cast {
                            ty: TypeRef::G(gt),
                            e: Box::new(init_e.clone()),
                        })
                    }
                }
                _ => None,
            };
            let e: &Expr = owned.as_ref().unwrap_or(init_e);
            // Need the declaring method's VarTable for local names; ctor
            // initializers of anonymous classes only reference constants,
            // captures (raw text) and fields, so the empty table suffices.
            let mut p = Printer::new(pc, pool, empty_vt());
            let mut t = String::new();
            let is_bool = parse_field_descriptor(desc) == Some(jcdc_jvm::JavaType::Boolean);
            if is_bool {
                p.expr_bool(e, &mut t);
            } else {
                p.expr(e, 1, &mut t);
            }
            line.push_str(" = ");
            line.push_str(&t);
        }
    }
    line.push(';');
    out.push_str(&line);
    out.push('\n');
    Ok(())
}

fn emit_method(
    pc: &PoolClass,
    pool: &ClassPool,
    fam: &Family,
    mi: usize,
    out: &mut String,
    indent: usize,
) -> anyhow::Result<()> {
    emit_method_with(pc, pool, fam, mi, out, indent, &HashMap::new())
}

fn emit_method_with(
    pc: &PoolClass,
    pool: &ClassPool,
    fam: &Family,
    mi: usize,
    out: &mut String,
    indent: usize,
    captures: &HashMap<String, Expr>,
) -> anyhow::Result<()> {
    let depth = EMIT_DEPTH.with(|d| {
        let v = d.get() + 1;
        d.set(v);
        v
    });
    struct DepthGuard;
    impl Drop for DepthGuard {
        fn drop(&mut self) {
            EMIT_DEPTH.with(|d| d.set(d.get() - 1));
        }
    }
    let _depth_guard = DepthGuard;
    if depth > 60 {
        anyhow::bail!(
            "emit recursion depth exceeded at {}.{}",
            pc.internal_name,
            pc.method_name(mi).unwrap_or("?")
        );
    }
    let m = &pc.cf.methods[mi];
    let name = pc.utf8(m.name_index).unwrap_or("?").to_string();
    let desc = pc.utf8(m.descriptor_index).unwrap_or("()V").to_string();
    let acc = m.access_flags;
    let is_ctor = name == "<init>";
    let pad = "    ".repeat(indent);

    // Constructors of anonymous/local classes: captured parameters
    // (this$*/val$*) are implicit and must not be printed.
    let mut skip_params: HashSet<usize> = HashSet::new();
    if is_ctor && pc.is_enum() {
        // javac prepends (String name, int ordinal) to every enum ctor.
        if let Some(md) = parse_method_descriptor(&desc) {
            if md.args.len() >= 2 {
                skip_params.insert(0);
                skip_params.insert(1);
            }
        }
    }
    if is_ctor && (!captures.is_empty() || class_has_this0(pc)) {
        if let Some(md) = parse_method_descriptor(&desc) {
            let mut slot = 1u16;
            for (i, a) in md.args.iter().enumerate() {
                let pname = ctor_param_name(pc, mi, i, slot);
                if pname.starts_with("this$") || pname.starts_with("val$") {
                    skip_params.insert(i);
                }
                slot += a.slot_size() as u16;
            }
        }
    }
    // Ctor params that javac synthesized to carry captures (stored
    // straight into this$*/val$* fields) are hidden from source for
    // anonymous AND local classes; they are also omitted from the ctor's
    // Signature attribute, which the arg alignment below relies on.
    let is_local_class = matches!(
        fam.nested.get(&pc.internal_name).map(|n| n.kind),
        Some(NestedKind::Local)
    );
    if is_ctor && is_local_class {
        for i in ctor_capture_params(pc, mi) {
            skip_params.insert(i);
        }
    }
    // Inner subclass forwarding the enclosing instance to super(): the
    // first ctor parameter is synthetic even without a local this$0 field.
    let mut outer_super_param = false;
    if is_ctor
        && !pc.is_enum()
        && !nested_is_static(pc)
        && pc.internal_name.contains('$')
        && outer_param_via_super(pc, &desc)
    {
        skip_params.insert(0);
        outer_super_param = true;
    }

    for a in member_annotations(pc, &m.attributes) {
        out.push_str(&pad);
        out.push_str(&a);
        out.push('\n');
    }

    let msig = m.attributes.iter().find_map(|a| {
        match parse_specialized_attribute(a, &pc.cf.constant_pool) {
            ParsedAttribute::Signature { signature_index } => {
                pc.utf8(signature_index).and_then(|s| parse_method_signature(s))
            }
            _ => None,
        }
    });
    let mdesc = parse_method_descriptor(&desc);

    // Java <= 7 requires captured locals/parameters to be declared final.
    let need_final_params = pc.cf.major_version < 52
        && !acc.contains(MethodAccessFlags::ABSTRACT)
        && !acc.contains(MethodAccessFlags::NATIVE)
        && method_builds_inner(pc, mi);

    let mut line = pad.clone();
    if acc.contains(MethodAccessFlags::PUBLIC) {
        line.push_str("public ");
    }
    if acc.contains(MethodAccessFlags::PROTECTED) {
        line.push_str("protected ");
    }
    if acc.contains(MethodAccessFlags::PRIVATE) {
        line.push_str("private ");
    }
    if acc.contains(MethodAccessFlags::STATIC) {
        line.push_str("static ");
    }
    if acc.contains(MethodAccessFlags::FINAL) {
        line.push_str("final ");
    }
    if acc.contains(MethodAccessFlags::SYNCHRONIZED) {
        line.push_str("synchronized ");
    }
    if acc.contains(MethodAccessFlags::NATIVE) {
        line.push_str("native ");
    }
    if acc.contains(MethodAccessFlags::ABSTRACT) {
        line.push_str("abstract ");
    }
    let is_default = pc.is_interface()
        && !acc.contains(MethodAccessFlags::ABSTRACT)
        && !acc.contains(MethodAccessFlags::STATIC)
        && !acc.contains(MethodAccessFlags::PRIVATE)
        && !is_ctor
        && m.attributes.iter().any(|a| pc.utf8(a.attribute_name_index) == Some("Code"));
    if is_default {
        line.push_str("default ");
    }

    let p0 = Printer::new(pc, pool, empty_vt());
    if let Some(sig) = &msig {
        let mut tp = String::new();
        jcdc_jvm::render_type_params(&sig.params, &mut tp);
        if !tp.is_empty() {
            line.push_str(&tp);
            line.push(' ');
        }
    }

    if !is_ctor {
        let ret = match &msig {
            Some(sig) => p0.type_name(&TypeRef::G(sig.ret.clone())),
            None => mdesc
                .as_ref()
                .map(|d| p0.type_name(&TypeRef::J(d.ret.clone())))
                .unwrap_or_else(|| "void".into()),
        };
        line.push_str(&ret);
        line.push(' ');
        line.push_str(&name);
    } else {
        // Anonymous class constructors take the base type's name; LOCAL
        // classes ($1Splitr) take their stripped source name.
        let self_simple = simple_name(&pc.internal_name);
        let local_simple = fam
            .nested
            .get(&pc.internal_name)
            .filter(|n| matches!(n.kind, NestedKind::Local))
            .map(|n| n.simple.clone());
        let ctor_name = if let Some(ls) = local_simple {
            ls
        } else if self_simple.chars().all(|c| c.is_ascii_digit()) {
            let base = pc
                .cf
                .interfaces
                .first()
                .and_then(|&i| pc.class_name(i))
                .map(|s| s.to_string())
                .or_else(|| pc.super_name().map(|s| s.to_string()));
            match base {
                Some(b) if b != "java/lang/Object" => simple_name(&b),
                _ => self_simple,
            }
        } else {
            self_simple
        };
        line.push_str(&ctor_name);
    }

    line.push('(');
    let param_names = method_param_names(pc, mi, &desc);
    let mut arg_types: Vec<TypeRef> = match &msig {
        Some(sig) => sig.args.iter().map(|g| TypeRef::G(g.clone())).collect(),
        None => mdesc
            .as_ref()
            .map(|d| d.args.iter().map(|t| TypeRef::J(t.clone())).collect())
            .unwrap_or_default(),
    };
    // Constructors: javac's Signature attribute omits ALL synthetic
    // parameters — LEADING (name, ordinal) for enums and the forwarded
    // enclosing instance (this$0), plus TRAILING val$ capture params
    // (jdk11 WhileOps$1Op: Signature 3 args, descriptor 4 — padding only
    // the front shifted every type one param left: `Op(AbstractPipeline,
    // AbstractPipeline<?,T,?> inputShape, StreamShape opFlags)`).
    // skip_params and param_names are descriptor-indexed: rebuild the
    // type list over the descriptor, feeding Signature types to the
    // non-skipped positions in order (the TreeMap KeyIterator/
    // SubMapIterator leading case falls out of the same rule).
    if is_ctor {
        if let Some(md) = &mdesc {
            if arg_types.len() != md.args.len() {
                let mut sig_types = std::mem::take(&mut arg_types).into_iter();
                arg_types = md
                    .args
                    .iter()
                    .enumerate()
                    .map(|(i, t)| {
                        if skip_params.contains(&i) {
                            TypeRef::J(t.clone())
                        } else {
                            sig_types.next().unwrap_or_else(|| TypeRef::J(t.clone()))
                        }
                    })
                    .collect();
            }
        }
    }
    let varargs = acc.contains(MethodAccessFlags::VARARGS);
    let mut printed = 0;
    for (i, t) in arg_types.iter().enumerate() {
        if skip_params.contains(&i) {
            continue;
        }
        if printed > 0 {
            line.push_str(", ");
        }
        printed += 1;
        let mut ts = p0.type_name(t);
        if varargs && i + 1 == arg_types.len() {
            if let Some(pos) = ts.rfind("[]") {
                ts.replace_range(pos.., "...");
            }
        }
        if need_final_params {
            line.push_str("final ");
        }
        line.push_str(&ts);
        line.push(' ');
        line.push_str(param_names.get(i).map(|s| s.as_str()).unwrap_or("arg"));
    }
    line.push(')');

    let mut throws: Vec<String> = Vec::new();
    if let Some(sig) = &msig {
        for t in &sig.throws {
            throws.push(p0.type_name(&TypeRef::G(t.clone())));
        }
    }
    // Merge the Exceptions attribute, skipping entries that are just the
    // erasure of a signature throws clause (`throws E` with E extends
    // Exception lists java/lang/Exception in Exceptions).
    let sig_erasures: Vec<String> = match &msig {
        Some(sig) => sig
            .throws
            .iter()
            .filter_map(|t| generic_erasure(t, &sig.params))
            .collect(),
        None => Vec::new(),
    };
    for attr in &m.attributes {
        if let ParsedAttribute::Exceptions(e) = parse_specialized_attribute(attr, &pc.cf.constant_pool) {
            for idx in &e.exception_index_table {
                if let Some(n) = pc.class_name(*idx) {
                    if sig_erasures.iter().any(|x| x == n) {
                        continue;
                    }
                    let s = p0.shorten(n);
                    if !throws.contains(&s) {
                        throws.push(s);
                    }
                }
            }
        }
    }
    if !throws.is_empty() {
        line.push_str(" throws ");
        line.push_str(&throws.join(", "));
    }

    if acc.contains(MethodAccessFlags::ABSTRACT) || acc.contains(MethodAccessFlags::NATIVE) {
        // Annotation type members carry their default in AnnotationDefault.
        if pc.access().contains(jcdc_classfile::ClassAccessFlags::ANNOTATION) {
            for attr in &m.attributes {
                if let ParsedAttribute::AnnotationDefault(a) =
                    parse_specialized_attribute(attr, &pc.cf.constant_pool)
                {
                    line.push_str(" default ");
                    line.push_str(&render_element_value(pc, &a.default_value));
                }
            }
        }
        line.push(';');
        out.push_str(&line);
        out.push('\n');
        return Ok(());
    }

    match decompile_method(pc, pool, mi) {
        Ok(Some(mut mb)) => {
            let mut body = strip_trailing_return(&mb.body);
            // Generic methods returning a type variable: javac elides the
            // `(E)` cast when the erasure already matches, but source needs
            // it back.
            if let Some(sig) = &msig {
                match &sig.ret {
                    jcdc_jvm::GenericType::TypeVar(tv) => {
                        cast_returns_to_typevar(&mut body, tv, &mb.vt);
                    }
                    // Generic array/object returns (`T[]`, `List<E>`): the
                    // bytecode works on erasures, so source form needs the
                    // cast back when the returned expression's type is the
                    // erasure rather than the generic form.
                    g @ (jcdc_jvm::GenericType::Array(_) | jcdc_jvm::GenericType::Class(_)) => {
                        let want = TypeRef::G(g.clone());
                        cast_generic_returns(&mut body, &want, pc);
                        // A cast cannot drive inference for a generic
                        // callee; prefer an explicit type witness.
                        add_return_witnesses(&mut body, Some(sig), pool);
                    }
                    _ => {}
                }
            }
            // Wildcard-parameterized call sites: arguments that carry only
            // their erasure need the source-level cast back (`accept((K) x)`).
            cast_wildcard_call_args(&mut body, pool, pc, &mb.vt);
            if pc.cf.major_version < 52 {
                finalize_captured_locals(&mut body, &pc.internal_name);
            }
            if is_ctor && pc.is_enum() {
                strip_enum_super(&mut body);
            } else if is_ctor {
                if outer_super_param {
                    strip_outer_super_arg(&mut body, &mb.vt);
                }
                // anonymous/local subclass: drop a no-arg super() call
                strip_trivial_super(&mut body, pc);
                // javac evaluates a delegated `this(expr)` argument before
                // the call, which decompiles into assignments + mid-body
                // this(...) calls (invalid Java). Collapse them back into a
                // single leading delegation when every path delegates.
                collapse_ctor_delegation(&mut body, pc);
                if is_local_class {
                    prune_local_ctor_delegation(&mut body, pc, mi);
                }
            }
            substitute_captures(&mut body, captures, pool);
            // Ctor artifact stripping runs BEFORE the outer-this
            // substitution: it normalizes param-slot reads of the outer
            // instance (Local this$N) into field reads (this.this$N),
            // which the substitution below then rewrites to Outer.this.
            // Local-class ctors always strip: a static-method local has no
            // this$0, but its capture stores (val$ puts / substituted Raw
            // assigns) are junk all the same.
            let outer_slot_param = outer_param_slot(pc).or_else(|| {
                // No own this$0 field but the ctor forwards the enclosing
                // instance to super() (jdk26 WeakHashMap$EntryIterator:
                // javac's implicit inner ctor is requireNonNull(param) +
                // super(param); with the param unnamed 'arg0' both lines
                // must be recognized as outer artifacts).
                if outer_super_param {
                    Some((1u16, "this$0".to_string()))
                } else {
                    None
                }
            });
            if is_ctor && (class_has_this0(pc) || outer_super_param || is_local_class) {
                if is_local_class && std::env::var("JCDC_DBG_CTOR").is_ok() {
                    eprintln!("CTORCAP pc={} captures={:?}", pc.internal_name, captures.keys().collect::<Vec<_>>());
                }
                if is_local_class {
                    // Direct reads of capture PARAMS (before the putfield
                    // mirror) would print as `arg0` when the LVT lacks the
                    // synthetic name (jdk26 Gatherers FixedWindow:
                    // `window = new Object[arg0]`): map them through the
                    // ctor's putfield statements to the pre-rendered
                    // capture expressions, like anon_field_inits does.
                    let mut rep: HashMap<u32, Expr> = HashMap::new();
                    for st in stmt_vec(&body) {
                        if let Stmt::ExprStmt(Expr::Assign { target, value, .. }) = st {
                            match target.as_ref() {
                                Expr::Field { name, is_static: false, .. }
                                    if name.starts_with("val$") || name.starts_with("this$") =>
                                {
                                    if let (Some(e), Expr::Local { var, .. }) =
                                        (captures.get(name.as_str()), value.as_ref())
                                    {
                                        rep.insert(*var, e.clone());
                                    }
                                }
                                // substitute_captures already ran: the
                                // store target is the pre-rendered capture
                                // expression (`windowSize = arg0`).
                                Expr::Raw(t) => {
                                    if let Expr::Local { var, .. } = value.as_ref() {
                                        rep.insert(*var, Expr::Raw(t.clone()));
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                    if is_local_class && std::env::var("JCDC_DBG_CTOR").is_ok() {
                        eprintln!("CTORCAP pc={} rep={:?}", pc.internal_name, rep.len());
                    }
                    if !rep.is_empty() {
                        rewrite_param_locals(&mut body, &rep);
                    }
                }
                strip_inner_ctor_artifacts(&mut body, &mb.vt, outer_slot_param.clone());
            }
            // Member inner classes: this$N field reads become Outer.this.
            let outer_this = outer_this_map(pc);
            if !outer_this.is_empty() {
                substitute_captures(&mut body, &outer_this, pool);
            }
            inline_anonymous(&mut body, pc, pool, fam, &mb.vt);
            inline_accessors(&mut body, pc, pool);
            // Accessor inlining can EXPOSE diamond `new`s (the synthetic
            // accessor hid the ctor call from the earlier pass): retry the
            // ctor-arg witnesses (jdk11 ClassValue.refreshVersion's
            // `new Entry<>(v2, (T) value)` arrives via an inlined
            // access$000 ctor accessor).
            fix_diamond_localdefs(&mut body, &mb.vt, pool);
            // Accessor inlining can expose the real generic callee only
            // now; retry the return witnesses (idempotent).
            add_return_witnesses(&mut body, msig.as_ref(), pool);
            restore_enum_switches(&mut body, pc, pool);
            add_throw_witnesses(&mut body, msig.as_ref(), pool);
            strip_erasure_casts_generic_ret(&mut body, msig.as_ref(), pool);
            witness_generic_returns(&mut body, msig.as_ref(), pool);
            // Scope the extern-decl registry to THIS method's emission:
            // names extracted here must suppress re-declaration inside
            // lambda bodies printed below, but must not leak into other
            // methods (common local-class names like State/Spliterator
            // would suppress their legitimate decls — ReferencePipeline
            // +32 errors). Nested emissions (anon bodies) snapshot/restore
            // around themselves, preserving this frame.
            let extern_save = EXTERN_DECL.with(|x| x.borrow().clone());
            fix_lambda_captures(&mut body, &mut mb.vt, pc, pool, fam);
            line.push_str(" {\n");
            out.push_str(&line);
            let ret_bool = mdesc.as_ref().map(|d| d.ret == jcdc_jvm::JavaType::Boolean).unwrap_or(false)
                || msig.as_ref().map(|g| matches!(&g.ret, jcdc_jvm::GenericType::Primitive('Z'))).unwrap_or(false);
            let ret_char = mdesc.as_ref().map(|d| d.ret == jcdc_jvm::JavaType::Char).unwrap_or(false)
                || msig.as_ref().map(|g| matches!(&g.ret, jcdc_jvm::GenericType::Primitive('C'))).unwrap_or(false);
            let ret_byte = mdesc.as_ref().map(|d| d.ret == jcdc_jvm::JavaType::Byte).unwrap_or(false);
            let ret_short = mdesc.as_ref().map(|d| d.ret == jcdc_jvm::JavaType::Short).unwrap_or(false);
            // Generic signature return in functional-interface or array
            // form: feeds the Return arm's lambda SAM witness.
            let ret_sam = msig.as_ref().and_then(|sig| match &sig.ret {
                g @ (jcdc_jvm::GenericType::Class(_) | jcdc_jvm::GenericType::Array(_)) => {
                    Some(TypeRef::G(g.clone()))
                }
                _ => None,
            });
            let text = Printer::new(pc, pool, &mb.vt)
                .with_indent(indent + 1)
                .with_ret_bool(ret_bool)
                .with_ret_char(ret_char)
                .with_ret_narrow(ret_byte, ret_short)
                .with_ret_sam(ret_sam)
                .into_string(&body);
            EXTERN_DECL.with(|x| *x.borrow_mut() = extern_save);
            out.push_str(&text);
            out.push_str(&pad);
            out.push_str("}\n");
        }
        Ok(None) => {
            line.push(';');
            out.push_str(&line);
            out.push('\n');
        }
        Err(e) => {
            line.push_str(" {\n");
            out.push_str(&line);
            out.push_str(&format!("{}    // $JCDC: decompilation failed: {}\n", pad, e));
            out.push_str(&pad);
            out.push_str("}\n");
        }
    }
    Ok(())
}

fn ctor_param_name(pc: &PoolClass, mi: usize, idx: usize, slot: u16) -> String {
    let names = method_param_names(pc, mi, pc.method_desc(mi).unwrap_or("()V"));
    if let Some(n) = names.get(idx) {
        return n.clone();
    }
    let _ = slot;
    format!("arg{}", idx)
}

/// Rewrite the leading `super(outer, rest...)` of an inner subclass ctor
/// to `super(rest...)`: the enclosing-instance argument is implicit in
/// Java source. When no arguments remain the call is left for
/// `strip_trivial_super` to drop.
fn strip_outer_super_arg(body: &mut Stmt, vt: &VarTable) {
    let stmts = match body {
        Stmt::Block(v) => v,
        _ => return,
    };
    // Skip leading synthetic `this.this$N = param` stores to reach the
    // delegation call.
    let is_this_store = |st: &Stmt| -> bool {
        match st {
            Stmt::ExprStmt(Expr::Assign { target, .. }) => match &**target {
                Expr::Field { name, .. } => name.starts_with("this$"),
                _ => false,
            },
            _ => false,
        }
    };
    // javac's implicit inner ctor: requireNonNull(outerParam) sits right
    // before super(outerParam) — skip it when locating the delegation
    // (jdk26 WeakHashMap$EntryIterator: the check blocked the scan and
    // super(arg0) survived).
    let is_pre_junk = |st: &Stmt| -> bool {
        is_this_store(st)
            || matches!(st, Stmt::ExprStmt(Expr::Method { name, args, .. })
                if (name == "requireNonNull" || name == "checkNotNull")
                    && args.len() == 1
                    && match &args[0] {
                        Expr::Local { var, .. } => vt.var(*var).is_param,
                        Expr::This => true,
                        Expr::Field { name: fn2, .. } => fn2.starts_with("this$"),
                        _ => false,
                    })
    };
    let Some(idx) = stmts.iter().position(|st| !is_pre_junk(st)) else { return };
    if let Some(Stmt::ExprStmt(Expr::Method { name, args, .. })) = stmts.get_mut(idx) {
        if name == "<init>" && !args.is_empty() {
            let is_outer_local = match &args[0] {
                Expr::Local { var, .. } => vt.var(*var).name.starts_with("this$")
                    || vt.var(*var).is_param,
                Expr::This => true,
                _ => false,
            };
            if is_outer_local {
                args.remove(0);
            }
        }
    }
}

/// `return;` is illegal inside a static initializer (it is not a method
/// body); javac still emits RETURN in <clinit> bytecode. Drop trailing
/// bare returns from every branch tail.
/// Restructure mid-block bare `return;` statements inside <clinit>: a
/// branch that "returns" from a static initializer really means "skip the
/// rest of the initializer", and a literal `return;` there is a compile
/// error ("return outside method"). Rewrite `if (c) { A; return; } REST`
/// into `if (c) { A; } else { REST; }` (definite-exit branches get REST
/// moved into them minus the return; fall-through branches get REST
/// appended; a bare `return;` statement becomes REST). Applied bottom-up
/// per block so nested rotated chains (the assert desugaring
/// `if (AD) return; else if (cond) return; else throw;` at the end of
/// IntegerCache's archived branch) collapse outward correctly.
/// Pre-pass for hoist_clinit_returns, on the PRISTINE tree (bare returns
/// still present): truncate each block right after its first definite-exit
/// statement. In <clinit> the rotated assert chain (`if (AD) return; else if
/// (c) return; else throw;`) exits the initializer on every path; the shared
/// tail following it is the structurizer's duplicated copy — dead code whose
/// presence double-assigns final fields (IntegerCache `cache`). Rewriting
/// returns-as-skip first would sanitize the chain and hide the deadness, so
/// this must run before any rewrite.
fn prune_post_exit_dead(s: &mut Stmt) {
    match s {
        Stmt::Block(v) => {
            for x in v.iter_mut() {
                prune_post_exit_dead(x);
            }
            fn definite_exit0(s: &Stmt) -> bool {
                match s {
                    Stmt::Return(_) | Stmt::Throw(_) => true,
                    Stmt::Block(v) => v.last().map(definite_exit0).unwrap_or(false),
                    Stmt::If { then_stmt, else_stmt: Some(e), .. } => {
                        definite_exit0(then_stmt) && definite_exit0(e)
                    }
                    _ => false,
                }
            }
            if let Some(pos) = v.iter().position(definite_exit0) {
                v.truncate(pos + 1);
            }
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            prune_post_exit_dead(then_stmt);
            if let Some(e) = else_stmt {
                prune_post_exit_dead(e);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => prune_post_exit_dead(body),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(prune_post_exit_dead);
            prune_post_exit_dead(body);
        }
        Stmt::ForEach { body, .. } => prune_post_exit_dead(body),
        Stmt::Switch { cases, default, .. } => {
            for c in cases.iter_mut() {
                for st in c.body.iter_mut() {
                    prune_post_exit_dead(st);
                }
            }
            if let Some(d) = default {
                prune_post_exit_dead(d);
            }
        }
        Stmt::Try { body, catches, finally } => {
            prune_post_exit_dead(body);
            for c in catches.iter_mut() {
                prune_post_exit_dead(&mut c.body);
            }
            if let Some(f) = finally {
                prune_post_exit_dead(f);
            }
        }
        Stmt::Labeled { body, .. } | Stmt::Synchronized { body, .. } => {
            prune_post_exit_dead(body)
        }
        _ => {}
    }
}

fn hoist_clinit_returns(s: &mut Stmt) {
    prune_post_exit_dead(s);
    fn block_vec(x: Stmt) -> Vec<Stmt> {
        match x {
            Stmt::Block(v) => v,
            other => vec![other],
        }
    }
    fn make_block(mut v: Vec<Stmt>) -> Stmt {
        if v.len() == 1 {
            v.pop().unwrap()
        } else {
            Stmt::Block(v)
        }
    }
    fn any_bare_return(s: &Stmt) -> bool {
        match s {
            Stmt::Return(None) => true,
            Stmt::Block(v) => v.iter().any(any_bare_return),
            Stmt::If { then_stmt, else_stmt, .. } => {
                any_bare_return(then_stmt)
                    || else_stmt.as_deref().map(any_bare_return).unwrap_or(false)
            }
            _ => false,
        }
    }
    /// Every path through `s` ends in a bare `return;` (definite exit).
    fn definite_exit(s: &Stmt) -> bool {
        match s {
            Stmt::Return(None) | Stmt::Return(_) | Stmt::Throw(_) => true,
            Stmt::Block(v) => v.last().map(definite_exit).unwrap_or(false),
            Stmt::If { then_stmt, else_stmt: Some(e), .. } => {
                definite_exit(then_stmt) && definite_exit(e)
            }
            _ => false,
        }
    }
    /// Rewrite `s` so that control leaving it (other than through its
    /// bare-return exit paths) continues into `rest`:
    /// - a bare `return;` (skip-the-rest exit) is DROPPED — rest must NOT
    ///   run on that path;
    /// - a definite-exit branch keeps its content minus the trailing return;
    /// - every fall-through position gets `rest` appended;
    /// - a missing else becomes `else { rest }`.
    fn push_rest(s: Stmt, rest: Vec<Stmt>) -> Stmt {
        match s {
            Stmt::Return(None) => Stmt::Block(vec![]),
            Stmt::Block(mut v) => {
                if let Some(last) = v.pop() {
                    if matches!(last, Stmt::Return(None)) {
                        // Exit path: the return is dropped; the statements
                        // before it stay, rest does NOT join this path.
                        Stmt::Block(v)
                    } else {
                        v.push(push_rest(last, rest));
                        Stmt::Block(v)
                    }
                } else {
                    v.extend(rest);
                    Stmt::Block(v)
                }
            }
            Stmt::If { cond, then_stmt, else_stmt } => {
                let t = if definite_exit(&then_stmt) {
                    Box::new(push_rest(*then_stmt, Vec::new()))
                } else {
                    let mut tv = block_vec(*then_stmt);
                    tv.extend(rest.clone());
                    Box::new(make_block(tv))
                };
                let e = match else_stmt {
                    Some(eb) => {
                        let e2 = if definite_exit(&eb) {
                            push_rest(*eb, Vec::new())
                        } else {
                            let mut ev = block_vec(*eb);
                            ev.extend(rest);
                            make_block(ev)
                        };
                        Some(Box::new(e2))
                    }
                    None => Some(Box::new(make_block(rest))),
                };
                Stmt::If { cond, then_stmt: t, else_stmt: e }
            }
            other => make_block({
                let mut v = vec![other];
                v.extend(rest);
                v
            }),
        }
    }
    match s {
        Stmt::Block(v) => {
            // Rewrite BEFORE recursing: the loop needs the pristine bare
            // returns to see which statements are exit-skipped; child
            // recursion sanitizes them (correctly per-child, but blind to
            // the sibling `rest` that must be rerouted around the exit).
            let mut i = 0;
            while i < v.len() {
                if any_bare_return(&v[i]) {
                    let rest: Vec<Stmt> = v.drain(i + 1..).collect();
                    let taken = std::mem::replace(&mut v[i], Stmt::Block(vec![]));
                    let before = format!("{:?}", taken);
                    let rebuilt = push_rest(taken, rest.clone());
                    if format!("{:?}", rebuilt) == before {
                        // No progress (a mid-block bare return this rewrite
                        // cannot move); RESTORE the statement (v[i] currently
                        // holds the placeholder) and move on.
                        v[i] = rebuilt;
                        if !rest.is_empty() {
                            v.insert(i + 1, Stmt::Block(rest));
                        }
                        i += 1;
                        continue;
                    }
                    v[i] = rebuilt;
                    // The rewrite may expose further bare returns in v[i];
                    // re-check the same index.
                    continue;
                }
                i += 1;
            }
            // Drop now-empty trailing statements left by the rewrite.
            v.retain(|x| !matches!(x, Stmt::Block(b) if b.is_empty()));
            for x in v.iter_mut() {
                hoist_clinit_returns(x);
            }
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            hoist_clinit_returns(then_stmt);
            if let Some(e) = else_stmt {
                hoist_clinit_returns(e);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => hoist_clinit_returns(body),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(hoist_clinit_returns);
            hoist_clinit_returns(body);
        }
        Stmt::ForEach { body, .. } => hoist_clinit_returns(body),
        Stmt::Switch { cases, default, .. } => {
            for c in cases.iter_mut() {
                for st in c.body.iter_mut() {
                    hoist_clinit_returns(st);
                }
            }
            if let Some(d) = default {
                hoist_clinit_returns(d);
            }
        }
        Stmt::Try { body, catches, .. } => {
            hoist_clinit_returns(body);
            for c in catches.iter_mut() {
                hoist_clinit_returns(&mut c.body);
            }
        }
        Stmt::Labeled { body, .. } | Stmt::Synchronized { body, .. } => {
            hoist_clinit_returns(body)
        }
        _ => {}
    }
}

fn strip_static_init_returns(s: &mut Stmt) {
    // Java forbids `return;` in a static initializer and the method's
    // final one is the natural end. TOP LEVEL ONLY: a mid-body bare
    // return is a SKIP marker that hoist_clinit_returns redistributes
    // the rest around — stripping those first made exit branches fall
    // through silently (Long$LongCache branch copy double-assigned the
    // final `cache`).
    if let Stmt::Block(v) = s {
        while matches!(v.last(), Some(Stmt::Return(None))) {
            v.pop();
        }
    }
}
fn strip_trivial_super(body: &mut Stmt, pc: &PoolClass) {
    let stmts = match body {
        Stmt::Block(v) => v,
        _ => return,
    };
    if let Some(first) = stmts.first_mut() {
        if let Stmt::ExprStmt(Expr::Method { name, cls, args, .. }) = first {
            if name == "<init>" && args.is_empty() && cls != &pc.internal_name {
                *first = Stmt::Block(vec![]);
            }
        }
    }
    stmts.retain(|s| !s.is_empty_block());
}

/// Enum constructors: drop the implicit `super(name, ordinal)` call, and
/// trim the implicit (name, ordinal) args from `this(...)` delegation.
fn strip_enum_super(body: &mut Stmt) {
    let stmts = match body {
        Stmt::Block(v) => v,
        _ => return,
    };
    if let Some(first) = stmts.first_mut() {
        if let Stmt::ExprStmt(Expr::Method { name, cls, args, .. }) = first {
            if name == "<init>" && cls == "java/lang/Enum" {
                *first = Stmt::Block(vec![]);
            } else if name == "<init>" && args.len() > 2 {
                // this(name, ordinal, real...) → this(real...)
                args.drain(0..2);
            }
        }
    }
    stmts.retain(|s| !s.is_empty_block());
}

/// Local-class ctor this(..) delegation: the target ctor's synthesized
/// capture params are stripped from its printed signature (they are
/// substituted capture expressions), so the delegating call must drop
/// the matching args or the source ctor takes more params than any
/// declared ctor accepts (jdk26 Gatherers Composite.impl State:
/// `this(c1, c2, true, true, arg0..arg11)` against a 4-param State —
/// "找不到合适的构造器"). Mirrors the skip sets emit_method_with
/// applies to the target: val$/this$-named params plus direct
/// capture-store params.
fn prune_local_ctor_delegation(body: &mut Stmt, pc: &PoolClass, mi_self: usize) {
    let stmts = match body {
        Stmt::Block(v) => v,
        _ => return,
    };
    let Some(first) = stmts.first_mut() else { return };
    let Stmt::ExprStmt(Expr::Method { name, cls, args, desc, .. }) = first else {
        return;
    };
    if name != "<init>" || cls != &pc.internal_name {
        return;
    }
    // Locate the target ctor by its descriptor.
    let target = (0..pc.cf.methods.len()).find(|&mi2| {
        mi2 != mi_self && pc.method_name(mi2) == Some("<init>")
            && pc.method_desc(mi2)
                .and_then(parse_method_descriptor)
                .map(|md| md.args.len() == desc.args.len() && md.ret == desc.ret)
                .unwrap_or(false)
            && pc.method_desc(mi2).is_some()
    });
    let Some(mi2) = target else { return };
    let Some(md2) = pc.method_desc(mi2).and_then(parse_method_descriptor) else {
        return;
    };
    if md2.args.len() != args.len() {
        return;
    }
    let mut skip: HashSet<usize> = ctor_capture_params(pc, mi2);
    let mut slot = 1u16;
    for (i, a) in md2.args.iter().enumerate() {
        let pname = ctor_param_name(pc, mi2, i, slot);
        if pname.starts_with("this$") || pname.starts_with("val$") {
            skip.insert(i);
        }
        slot += a.slot_size() as u16;
    }
    if skip.is_empty() || skip.len() >= args.len() {
        return;
    }
    let mut i = 0;
    args.retain(|_| {
        let keep = !skip.contains(&i);
        i += 1;
        keep
    });
    i = 0;
    desc.args.retain(|_| {
        let keep = !skip.contains(&i);
        i += 1;
        keep
    });
}

fn method_param_names(pc: &PoolClass, mi: usize, desc: &str) -> Vec<String> {
    let md = parse_method_descriptor(desc);
    let n = md.as_ref().map(|d| d.args.len()).unwrap_or(0);
    let is_static = pc.cf.methods[mi].access_flags.contains(MethodAccessFlags::STATIC);
    // LVT-derived names (per descriptor arg) as the base.
    let code_len = crate::varalloc::code_attribute(pc, mi).map(|c| c.code.len() as u16).unwrap_or(0);
    let max_locals = crate::varalloc::code_attribute(pc, mi).map(|c| c.max_locals).unwrap_or(0);
    let mut names: Vec<String> = if let Some(md) = &md {
        let vt = VarTable::build(pc, mi, md, is_static, max_locals, code_len);
        vt.vars
            .iter()
            .filter(|v| v.is_param && v.name != "this")
            .map(|v| v.name.clone())
            .collect()
    } else {
        Vec::new()
    };
    if names.len() != n {
        names = (0..n).map(|i| format!("arg{}", i)).collect();
    }
    // MethodParameters overrides where a real name is present.
    for attr in &pc.cf.methods[mi].attributes {
        if let ParsedAttribute::MethodParameters(mp) = parse_specialized_attribute(attr, &pc.cf.constant_pool) {
            if mp.parameters.len() == n {
                for (i, p) in mp.parameters.iter().enumerate() {
                    if p.name_index != 0 {
                        if let Some(nm) = pc.utf8(p.name_index) {
                            names[i] = nm.to_string();
                        }
                    }
                }
            }
        }
    }
    names
}

// ---------------------------------------------------------------------------
// Enums
// ---------------------------------------------------------------------------

fn emit_enum_constants(
    pc: &PoolClass,
    pool: &ClassPool,
    opts: &ClassOptions,
    fam: &Family,
    out: &mut String,
    indent: usize,
) -> anyhow::Result<()> {
    let pad = "    ".repeat(indent);
    let names: Vec<String> = pc
        .cf
        .fields
        .iter()
        .filter(|f| f.access_flags.contains(FieldAccessFlags::ENUM))
        .filter_map(|f| pc.utf8(f.name_index).map(|s| s.to_string()))
        .collect();
    let inits = enum_ctor_inits(pc, pool);
    for (i, n) in names.iter().enumerate() {
        out.push_str(&pad);
        out.push_str(n);
        if let Some(init) = inits.get(n) {
            if !init.args.is_empty() {
                out.push('(');
                out.push_str(&init.args);
                out.push(')');
            }
            if let Some(body_cls) = &init.body_class {
                if let Some(bpc) = pool.get(body_cls) {
                    let mut body = String::new();
                    emit_enum_constant_body(&bpc, pool, fam, &mut body, indent)?;
                    if !body.trim().is_empty() {
                        out.push_str(" {\n");
                        out.push_str(&body);
                        out.push_str(&pad);
                        out.push('}');
                    }
                }
            }
        }
        if i + 1 == names.len() {
            out.push_str(";\n\n");
        } else {
            out.push_str(",\n");
        }
    }
    if names.is_empty() {
        out.push_str(&pad);
        out.push_str(";\n");
    }
    let _ = opts;
    Ok(())
}

fn emit_enum_constant_body(
    pc: &PoolClass,
    pool: &ClassPool,
    fam: &Family,
    out: &mut String,
    indent: usize,
) -> anyhow::Result<()> {
    let skip = methods_to_skip(pc, pool, false, false, &ClassOptions::default());
    for mi in 0..pc.cf.methods.len() {
        let name = pc.method_name(mi).unwrap_or("");
        if name == "<init>" || name == "<clinit>" || skip.contains(&mi) {
            continue;
        }
        emit_method(pc, pool, fam, mi, out, indent + 1)?;
    }
    Ok(())
}

struct EnumInit {
    args: String,
    body_class: Option<String>,
}

fn enum_ctor_inits(pc: &PoolClass, pool: &ClassPool) -> HashMap<String, EnumInit> {
    let mut map = HashMap::new();
    let Some(ci) = pc.find_own_method("<clinit>", "()V") else { return map };
    let Ok(Some(mb)) = decompile_method(pc, pool, ci) else { return map };
    walk_enum_inits(&mb.body, &mut map, pc, pool, &mb.vt);
    map
}

fn walk_enum_inits(s: &Stmt, map: &mut HashMap<String, EnumInit>, pc: &PoolClass, pool: &ClassPool, vt: &VarTable) {
    match s {
        Stmt::Block(v) => {
            for x in v {
                walk_enum_inits(x, map, pc, pool, vt);
            }
        }
        Stmt::ExprStmt(Expr::Assign { target, value, .. }) => {
            if let Expr::Field { name, is_static: true, .. } = &**target {
                if let Expr::New { cls, args, .. } = &**value {
                    let body_cls = if cls != &pc.internal_name { Some(cls.clone()) } else { None };
                    // Resolve the enum ctor descriptor so boolean/char
                    // constant arguments render as `true`/`'x'`, not 1/120.
                    // Same-arity overloads ((String,String,String...) vs
                    // (String,String,boolean) — jdk26 KnownOIDs) are scored
                    // by constant/parameter compatibility, not first-wins.
                    let ctor_params: Option<Vec<jcdc_jvm::JavaType>> = (0..pc.cf.methods.len())
                        .filter_map(|mi| {
                            if pc.method_name(mi) != Some("<init>") {
                                return None;
                            }
                            let d = pc.method_desc(mi)?;
                            let md = parse_method_descriptor(d)?;
                            if md.args.len() == args.len() {
                                Some(md.args)
                            } else {
                                None
                            }
                        })
                        .max_by_key(|cand| {
                            use crate::expr::ConstVal as CV;
                            cand.iter()
                                .enumerate()
                                .map(|(i, pt)| match (&args[i], pt) {
                                    (Expr::Const(CV::Int(n)), jcdc_jvm::JavaType::Boolean)
                                        if *n == 0 || *n == 1 => 4,
                                    (Expr::Const(CV::Int(_)), jcdc_jvm::JavaType::Char) => 4,
                                    (Expr::Const(CV::Int(_)), jcdc_jvm::JavaType::Int) => 2,
                                    (Expr::Const(CV::Int(_)), jcdc_jvm::JavaType::Array(_)) => 0,
                                    (Expr::Const(CV::Str(_)), jcdc_jvm::JavaType::Object(n))
                                        if n == "java/lang/String" => 2,
                                    (Expr::NewArray { .. }, jcdc_jvm::JavaType::Array(_)) => 3,
                                    _ => 1,
                                })
                                .sum::<i32>()
                        });
                    let extra: Vec<String> = args
                        .iter()
                        .enumerate()
                        .skip(2)
                        .map(|(i, a)| {
                            if let Some(pt) = ctor_params.as_ref().and_then(|p| p.get(i)) {
                                if let jcdc_jvm::JavaType::Boolean = pt {
                                    if let Expr::Const(crate::expr::ConstVal::Int(n)) = a {
                                        return if *n == 0 { "false".to_string() } else { "true".to_string() };
                                    }
                                }
                                if let jcdc_jvm::JavaType::Char = pt {
                                    if let Expr::Const(crate::expr::ConstVal::Int(n)) = a {
                                        if let Some(c) = char::from_u32(*n as u32) {
                                            return format!("'{}'", crate::emit::escape_char(c));
                                        }
                                    }
                                }
                            }
                            let mut p = Printer::new(pc, pool, empty_vt());
                            let mut s = String::new();
                            p.expr(a, 1, &mut s);
                            s
                        })
                        .collect();
                    map.insert(name.clone(), EnumInit { args: extra.join(", "), body_class: body_cls });
                }
            }
        }
        _ => {}
    }
}

/// Remove the `CONST = new ThisEnum("CONST", ordinal, ...)` stores from an
/// enum's <clinit> body: the constants are already printed in the enum
/// constant list, and source may neither assign them nor instantiate the
/// enum class.
fn strip_enum_const_stores(s: &mut Stmt, pc: &PoolClass) {
    let names: HashSet<String> = pc
        .cf
        .fields
        .iter()
        .filter(|f| f.access_flags.contains(FieldAccessFlags::ENUM))
        .filter_map(|f| pc.utf8(f.name_index).map(|n| n.to_string()))
        .collect();
    if names.is_empty() {
        return;
    }
    fn rec(s: &mut Stmt, pc: &PoolClass, names: &HashSet<String>) {
        match s {
            Stmt::Block(v) => {
                v.retain(|st| {
                    !matches!(st, Stmt::ExprStmt(Expr::Assign { target, .. })
                        if matches!(&**target, Expr::Field { name, is_static: true, .. }
                            if name == "$VALUES"))
                        && !matches!(st, Stmt::ExprStmt(Expr::Assign { target, value, .. })
                        if matches!(&**target, Expr::Field { name, is_static: true, .. }
                            if names.contains(name))
                            && matches!(&**value, Expr::New { cls, .. } if cls == &pc.internal_name
                                || pc.cf.fields.iter().any(|f| {
                                    f.access_flags.contains(FieldAccessFlags::ENUM)
                                })))
                });
                v.iter_mut().for_each(|x| rec(x, pc, names));
            }
            Stmt::If { then_stmt, else_stmt, .. } => {
                rec(then_stmt, pc, names);
                if let Some(e) = else_stmt {
                    rec(e, pc, names);
                }
            }
            Stmt::Try { body, .. } => rec(body, pc, names),
            _ => {}
        }
    }
    rec(s, pc, &names);
}

fn clinit_only_enum_init(pc: &PoolClass, pool: &ClassPool, ci: usize) -> bool {
    let Ok(Some(mb)) = decompile_method(pc, pool, ci) else { return false };
    let stmts = stmt_vec(&mb.body);
    !stmts.is_empty()
        && stmts.iter().all(|s| match s {
            Stmt::ExprStmt(Expr::Assign { target, .. }) => matches!(&**target, Expr::Field { is_static: true, .. }),
            Stmt::Return(None) => true,
            Stmt::Comment(_) => true,
            _ => false,
        })
}

/// Renamed `$assertionsDisabled` field (javac reserves the original name).
pub const ASSERT_FIELD: &str = "$jcdcAssertionsDisabled";

// ---------------------------------------------------------------------------
// Anonymous class inlining
// ---------------------------------------------------------------------------

pub fn inline_anonymous(body: &mut Stmt, pc: &PoolClass, pool: &ClassPool, fam: &Family, vt: &VarTable) {
    if fam.anonymous.is_empty() && fam.locals.is_empty() {
        return;
    }
    let mut pending: Vec<Stmt> = Vec::new();
    let mut declared: HashSet<String> = HashSet::new();
    let hoist_mark = LOCAL_DECL_HOIST.with(|h| h.borrow().len());
    let set_top = ANON_BODY_DEPTH.with(|d| d.get()) > 0;
    if set_top {
        ANON_TOP_BLOCK.with(|t| t.set(true));
    }
    walk_stmt_anon(body, pc, pool, fam, &mut pending, vt, &mut declared);
    if set_top {
        ANON_TOP_BLOCK.with(|t| t.set(false));
    }
    // Inside an inlined anon/local body: leave bubbled decls on the stack
    // for the REAL method's drain (their references — method refs, hoisted
    // type decls — live out there).
    let in_anon_body = ANON_BODY_DEPTH.with(|d| d.get()) > 0;
    // Insert bubbled-up local-class declarations at the top-block
    // position that satisfies both constraints: AFTER every captured
    // outer local's definition (a local class only sees locals declared
    // before it) and BEFORE its first mention (type references in
    // hoisted `= null` decls included — those are themselves deferred
    // past the decl when they appear too early).
    {
        let drained: Vec<(String, Stmt)> = if in_anon_body {
            Vec::new()
        } else {
            LOCAL_DECL_HOIST.with(|h| {
                let mut h = h.borrow_mut();
                h.drain(hoist_mark..).collect()
            })
        };
        if !drained.is_empty() && matches!(body, Stmt::Block(_)) && !in_anon_body {
            let Stmt::Block(v) = body else { unreachable!() };
            for (name, decl) in drained {
                if v.iter().any(|x| matches!(x, Stmt::ClassDecl { name: n2, .. } if *n2 == name))
                {
                    continue;
                }
                let marker = format!("\u{2}{}", name);
                let caps = local_class_captures(&name, fam, pool);
                let capture_end = if caps.is_empty() {
                    0
                } else {
                    // The decl must sit AFTER the DEFINITION of every
                    // captured local (a local class only sees locals
                    // declared before it). Mentions after the definition
                    // are fine — counting them would push the decl past
                    // earlier type references (className is read all over
                    // the method body).
                    let defines = |st: &Stmt| -> bool {
                        match st {
                            Stmt::LocalDef { var, .. } => {
                                caps.iter().any(|n| vt.var(*var).name == *n)
                            }
                            Stmt::ExprStmt(Expr::Assign { target, .. }) => {
                                matches!(&**target, Expr::Local { var, .. }
                                    if caps.iter().any(|n| vt.var(*var).name == *n))
                            }
                            _ => false,
                        }
                    };
                    v.iter().rposition(defines).map(|p| p + 1).unwrap_or(0)
                };
                let mut first_use =
                    first_local_mention(v, &marker, &name, vt, fam).unwrap_or(v.len());
                if first_use < capture_end {
                    // The early mentions sit in hoisted `= null` decls:
                    // move them past the insertion point (their runtime
                    // uses all postdate the class decl), then insert the
                    // decl after the LAST capture definition — a local
                    // class only sees outer locals declared before it.
                    let mut moved = Vec::new();
                    let mut capture_end = capture_end;
                    loop {
                        let fu =
                            first_local_mention(v, &marker, &name, vt, fam).unwrap_or(v.len());
                        if fu >= capture_end || fu >= v.len() {
                            break;
                        }
                        let movable = matches!(&v[fu], Stmt::LocalDef { init: None, .. })
                            || matches!(&v[fu], Stmt::LocalDef { init: Some(e), .. }
                                if matches!(e, Expr::Const(crate::expr::ConstVal::Null)));
                        if !movable {
                            break;
                        }
                        moved.push(v.remove(fu));
                        capture_end -= 1;
                    }
                    let fu =
                        first_local_mention(v, &marker, &name, vt, fam).unwrap_or(v.len());
                    let pos = std::cmp::min(std::cmp::max(fu, capture_end), v.len());
                    v.insert(pos, decl);
                    let mut at = pos + 1;
                    for m in moved {
                        v.insert(at, m);
                        at += 1;
                    }
                } else {
                    let pos = std::cmp::max(first_use, capture_end);
                    v.insert(pos, decl);
                }
            }
        }
    }
    if !pending.is_empty() {
        let in_anon = LAMBDA_BODY_DEPTH.with(|d| d.get()) > 0;
        let mut v: Vec<Stmt> = Vec::new();
        for d in pending.drain(..) {
            let decl_name = match &d {
                Stmt::ClassDecl { name, .. } => Some(name.clone()),
                _ => None,
            };
            if let Some(name) = decl_name {
                let extern_done = EXTERN_DECL.with(|x| x.borrow().contains(&name));
                if extern_done {
                    continue;
                }
                if in_anon {
                    // Bubble to the outer method's pass-time extraction
                    // (fix_lambda_captures declares it out there).
                    LOCAL_DECL_HOIST.with(|h| h.borrow_mut().push((name, d)));
                    continue;
                }
            }
            v.push(d);
        }
        if v.is_empty() {
            return;
        }
        let old = std::mem::replace(body, Stmt::Block(vec![]));
        match old {
            Stmt::Block(mut inner) => {
                v.append(&mut inner);
                *body = Stmt::Block(v);
            }
            other => {
                v.push(other);
                *body = Stmt::Block(v);
            }
        }
    }
}

/// Names of the outer locals a local class captures (its val$* fields).
/// Same-simple-name siblings are UNIONed: the simple name alone cannot
/// identify which local class a decl belongs to (jdk26 Gatherers has
/// four `State` classes; picking the first gave the wrong capture set
/// and mispositioned the decl at the method head).
fn local_class_captures(name: &str, fam: &Family, pool: &ClassPool) -> Vec<String> {
    let mut caps: Vec<String> = Vec::new();
    for (internal, nc) in fam.nested.iter() {
        if nc.simple == name && matches!(nc.kind, NestedKind::Local) {
            if let Some(lpc) = pool.get(internal) {
                for f in &lpc.cf.fields {
                    if let Some(v) = lpc
                        .utf8(f.name_index)
                        .and_then(|n| n.strip_prefix("val$").map(|x| x.to_string()))
                    {
                        if !caps.contains(&v) {
                            caps.push(v);
                        }
                    }
                }
            }
        }
    }
    caps
}

/// True when the expression references a local variable by one of `names`.
fn expr_mentions_local_names(e: &Expr, names: &[String], vt: &VarTable) -> bool {
    let mut found = false;
    fn w(e: &Expr, names: &[String], vt: &VarTable, found: &mut bool) {
        if *found {
            return;
        }
        match e {
            Expr::Local { var, .. } => {
                if names.iter().any(|n| vt.var(*var).name == *n) {
                    *found = true;
                }
            }
            Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
                args.iter().for_each(|a| w(a, names, vt, found))
            }
            Expr::Method { owner, args, .. } => {
                if let Some(o) = owner {
                    w(o, names, vt, found);
                }
                args.iter().for_each(|a| w(a, names, vt, found));
            }
            Expr::Field { owner: Some(o), .. } => w(o, names, vt, found),
            Expr::ArrayIndex { array, index } => {
                w(array, names, vt, found);
                w(index, names, vt, found);
            }
            Expr::Cast { e: i, .. } | Expr::InstanceOf { e: i, .. } | Expr::Un { e: i, .. }
            | Expr::PreIncDec { e: i, .. } | Expr::PostIncDec { e: i, .. } => w(i, names, vt, found),
            Expr::Bin { l, r, .. } => {
                w(l, names, vt, found);
                w(r, names, vt, found);
            }
            Expr::Cond { c, t, f } => {
                w(c, names, vt, found);
                w(t, names, vt, found);
                w(f, names, vt, found);
            }
            Expr::Assign { target, value, .. } => {
                w(target, names, vt, found);
                w(value, names, vt, found);
            }
            Expr::NewArray { dims, init, .. } => {
                dims.iter().for_each(|d| w(d, names, vt, found));
                if let Some(vals) = init {
                    vals.iter().for_each(|x| w(x, names, vt, found));
                }
            }
            Expr::NewMultiArray { dims, .. } => dims.iter().for_each(|d| w(d, names, vt, found)),
            Expr::StringConcat(parts) => parts.iter().for_each(|p| {
                if let crate::expr::ConcatPart::Str(i) = p {
                    w(i, names, vt, found);
                }
            }),
            Expr::Lambda(l) => l.captures.iter().for_each(|c| w(c, names, vt, found)),
            Expr::Invokedynamic { args, .. } => args.iter().for_each(|a| w(a, names, vt, found)),
            _ => {}
        }
    }
    w(e, names, vt, &mut found);
    found
}

/// True when a rendered type mentions the local class simple name.
fn ty_mentions_local(t: &TypeRef, name: &str, fam: &Family) -> bool {
    fn j_mentions(n: &str, name: &str, fam: &Family) -> bool {
        let tail = n.rsplit('$').next().unwrap_or(n);
        let stripped = tail.trim_start_matches(|c: char| c.is_ascii_digit());
        fam.nested.get(n).map(|x| x.simple.as_str()) == Some(name)
            || (!stripped.is_empty() && stripped == name && stripped != tail)
    }
    match t {
        TypeRef::J(jcdc_jvm::JavaType::Array(i)) => {
            ty_mentions_local(&TypeRef::J((**i).clone()), name, fam)
        }
        TypeRef::J(jcdc_jvm::JavaType::Object(n)) => j_mentions(n, name, fam),
        TypeRef::J(_) => false,
        TypeRef::G(g) => g_mentions_local(g, name, fam),
    }
}

fn g_mentions_local(g: &jcdc_jvm::GenericType, name: &str, fam: &Family) -> bool {
    use jcdc_jvm::GenericType as G;
    match g {
        G::Class(cs) => cs.parts.iter().any(|p| {
            // ClassSig parts carry the FULL internal simple chain with a
            // separate package field (`java/lang/invoke` +
            // `ClassSpecializer$Factory$1Var`).
            let full = if cs.package.is_empty() {
                p.name.clone()
            } else {
                format!("{}/{}", cs.package, p.name)
            };
            let tail = p.name.rsplit('$').next().unwrap_or("");
            let tail_stripped = tail.trim_start_matches(|c: char| c.is_ascii_digit());
            fam.nested.get(&full).map(|n| n.simple.as_str()) == Some(name)
                || (!tail_stripped.is_empty() && tail_stripped == name && tail != tail_stripped)
                || p.args.iter().any(|a| g_mentions_local(a, name, fam))
        }),
        G::Array(i) => g_mentions_local(i, name, fam),
        G::Wildcard(jcdc_jvm::WildcardBound::Extends(i))
        | G::Wildcard(jcdc_jvm::WildcardBound::Super(i)) => g_mentions_local(i, name, fam),
        // A local class used as a TYPE ARGUMENT parses as a TypeVar
        // (`new ReduceOp<T, U, ReducingSink>(..)`).
        G::TypeVar(n) => n == name,
        _ => false,
    }
}

/// True when the statement (or any nested expression) instantiates the
/// local class (post-walk marker `\u{2}Name`) or mentions its simple
/// name in any rendered TYPE (hoisted LocalDef decls, casts, array
/// creates, instanceof, method type witnesses).
/// First index in `v` mentioning the local class `name`: either a real
/// statement mention (marker new / type reference) or ANOTHER ClassDecl
/// whose rendered text names it — a local class is in scope only from
/// its declaration onward, so a sibling decl that references it (jdk26
/// Gatherers: State's field type ArrayDeque<MapConcurrentTask>) forces
/// the referenced decl to be inserted at-or-before the sibling.
fn first_local_mention(
    v: &[Stmt],
    marker: &str,
    name: &str,
    vt: &VarTable,
    fam: &Family,
) -> Option<usize> {
    v.iter().position(|s| match s {
        Stmt::ClassDecl { name: n2, header, body } => {
            *n2 != name && (text_mentions_name(header, name) || text_mentions_name(body, name))
        }
        other => stmt_mentions_local(other, marker, name, vt, fam),
    })
}

/// True when `text` contains `name` as a whole identifier.
fn text_mentions_name(text: &str, name: &str) -> bool {
    let b = text.as_bytes();
    let n = name.as_bytes();
    if n.is_empty() || b.len() < n.len() {
        return false;
    }
    let id = |c: u8| c.is_ascii_alphanumeric() || c == b'_' || c == b'$';
    b.windows(n.len()).enumerate().any(|(i, w)| {
        w == n && (i == 0 || !id(b[i - 1])) && (i + n.len() == b.len() || !id(b[i + n.len()]))
    })
}

fn stmt_mentions_local(s: &Stmt, marker: &str, name: &str, vt: &VarTable, fam: &Family) -> bool {
    let mut found = false;
    fn ty_hit(t: &TypeRef, name: &str, fam: &Family, found: &mut bool) {
        if !*found && ty_mentions_local(t, name, fam) {
            *found = true;
        }
    }
    fn walk_e(e: &Expr, marker: &str, name: &str, fam: &Family, found: &mut bool) {
        if *found {
            return;
        }
        match e {
            Expr::New { cls, ty, args, .. } => {
                if cls == marker {
                    *found = true;
                    return;
                }
                ty_hit(ty, name, fam, found);
                args.iter().for_each(|a| walk_e(a, marker, name, fam, found));
            }
            Expr::AnonNew { cls, base, args, .. } => {
                if cls == marker {
                    *found = true;
                    return;
                }
                // The anonymous base carries the type arguments
                // (`new ReduceOp<T, U, ReducingSink>() {...}`).
                ty_hit(base, name, fam, found);
                args.iter().for_each(|a| walk_e(a, marker, name, fam, found));
            }
            Expr::Method { owner, args, type_args, .. } => {
                if let Some(o) = owner {
                    walk_e(o, marker, name, fam, found);
                }
                args.iter().for_each(|a| walk_e(a, marker, name, fam, found));
                if type_args.iter().any(|t| t.contains(name)) {
                    *found = true;
                }
            }
            Expr::Const(crate::expr::ConstVal::ClassLit(t)) => ty_hit(t, name, fam, found),
            Expr::Cast { ty, e: inner, .. } | Expr::InstanceOf { e: inner, ty } => {
                ty_hit(ty, name, fam, found);
                walk_e(inner, marker, name, fam, found);
            }
            Expr::NewArray { elem, dims, init, .. } => {
                ty_hit(elem, name, fam, found);
                dims.iter().for_each(|d| walk_e(d, marker, name, fam, found));
                if let Some(vals) = init {
                    vals.iter().for_each(|v| walk_e(v, marker, name, fam, found));
                }
            }
            Expr::NewMultiArray { ty, dims } => {
                ty_hit(ty, name, fam, found);
                dims.iter().for_each(|d| walk_e(d, marker, name, fam, found));
            }
            Expr::Field { owner: Some(o), .. } => walk_e(o, marker, name, fam, found),
            Expr::ArrayIndex { array, index } => {
                walk_e(array, marker, name, fam, found);
                walk_e(index, marker, name, fam, found);
            }
            Expr::Un { e: inner, .. } | Expr::PreIncDec { e: inner, .. } | Expr::PostIncDec { e: inner, .. } => {
                walk_e(inner, marker, name, fam, found)
            }
            Expr::Bin { l, r, .. } => {
                walk_e(l, marker, name, fam, found);
                walk_e(r, marker, name, fam, found);
            }
            Expr::Cond { c, t, f } => {
                walk_e(c, marker, name, fam, found);
                walk_e(t, marker, name, fam, found);
                walk_e(f, marker, name, fam, found);
            }
            Expr::Assign { target, value, .. } => {
                walk_e(target, marker, name, fam, found);
                walk_e(value, marker, name, fam, found);
            }
            Expr::StringConcat(parts) => parts.iter().for_each(|p| {
                if let crate::expr::ConcatPart::Str(inner) = p {
                    walk_e(inner, marker, name, fam, found);
                }
            }),
            Expr::Lambda(l) => {
                // Method refs print as `Name::m` from ref_receiver/
                // impl_owner — a mention of the local class.
                let mref = l
                    .ref_receiver
                    .as_deref()
                    .unwrap_or(l.impl_owner.as_str());
                let tail = mref.rsplit('$').next().unwrap_or(mref);
                let stripped = tail.trim_start_matches(|c: char| c.is_ascii_digit());
                let full_matches = fam
                    .nested
                    .get(mref)
                    .map(|n| n.simple.as_str())
                    == Some(name);
                if full_matches
                    || (!stripped.is_empty() && stripped == name && stripped != tail)
                    || mref == marker
                {
                    *found = true;
                }
                l.captures.iter().for_each(|c| walk_e(c, marker, name, fam, found))
            }
            Expr::Invokedynamic { args, .. } => {
                args.iter().for_each(|a| walk_e(a, marker, name, fam, found))
            }
            _ => {}
        }
    }
    fn walk_s(s: &Stmt, marker: &str, name: &str, vt: &VarTable, fam: &Family, found: &mut bool) {
        if *found {
            return;
        }
        match s {
            Stmt::Block(v) => v.iter().for_each(|x| walk_s(x, marker, name, vt, fam, found)),
            Stmt::ExprStmt(e) => walk_e(e, marker, name, fam, found),
            Stmt::LocalDef { var, init, .. } => {
                ty_hit(&vt.var(*var).ty, name, fam, found);
                if let Some(e) = init {
                    walk_e(e, marker, name, fam, found);
                }
            }
            Stmt::Return(e) => {
                if let Some(x) = e {
                    walk_e(x, marker, name, fam, found);
                }
            }
            Stmt::Throw(e) => walk_e(e, marker, name, fam, found),
            Stmt::If { cond, then_stmt, else_stmt } => {
                walk_e(cond, marker, name, fam, found);
                walk_s(then_stmt, marker, name, vt, fam, found);
                if let Some(x) = else_stmt {
                    walk_s(x, marker, name, vt, fam, found);
                }
            }
            Stmt::While { cond, body } => {
                walk_e(cond, marker, name, fam, found);
                walk_s(body, marker, name, vt, fam, found);
            }
            Stmt::DoWhile { body, cond } => {
                walk_s(body, marker, name, vt, fam, found);
                walk_e(cond, marker, name, fam, found);
            }
            Stmt::For { init, cond, update, body } => {
                init.iter().for_each(|i| walk_s(i, marker, name, vt, fam, found));
                if let Some(c) = cond {
                    walk_e(c, marker, name, fam, found);
                }
                update.iter().for_each(|u| walk_e(u, marker, name, fam, found));
                walk_s(body, marker, name, vt, fam, found);
            }
            Stmt::ForEach { iterable, body, .. } => {
                walk_e(iterable, marker, name, fam, found);
                walk_s(body, marker, name, vt, fam, found);
            }
            Stmt::Switch { selector, cases, default, .. } => {
                walk_e(selector, marker, name, fam, found);
                for c in cases {
                    c.body.iter().for_each(|st| walk_s(st, marker, name, vt, fam, found));
                }
                if let Some(d) = default {
                    walk_s(d, marker, name, vt, fam, found);
                }
            }
            Stmt::Try { body, catches, finally } => {
                walk_s(body, marker, name, vt, fam, found);
                for c in catches {
                    walk_s(&c.body, marker, name, vt, fam, found);
                }
                if let Some(f) = finally {
                    walk_s(f, marker, name, vt, fam, found);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                resources.iter().for_each(|r| walk_s(r, marker, name, vt, fam, found));
                walk_s(body, marker, name, vt, fam, found);
                for c in catches {
                    walk_s(&c.body, marker, name, vt, fam, found);
                }
                if let Some(f) = finally {
                    walk_s(f, marker, name, vt, fam, found);
                }
            }
            Stmt::Synchronized { lock, body } => {
                walk_e(lock, marker, name, fam, found);
                walk_s(body, marker, name, vt, fam, found);
            }
            Stmt::Labeled { body, .. } => walk_s(body, marker, name, vt, fam, found),
            _ => {}
        }
    }
    walk_s(s, marker, name, vt, fam, &mut found);
    found
}

fn walk_stmt_anon(
    s: &mut Stmt,
    pc: &PoolClass,
    pool: &ClassPool,
    fam: &Family,
    pending: &mut Vec<Stmt>,
    vt: &VarTable,
    declared: &mut HashSet<String>,
) {
    match s {
        Stmt::Block(v) => {
            // Insert local-class declarations right before the statement
            // that first NAMES them — a type mention (`List<Var> targs`
            // hoisted to the method head) can precede the instantiation
            // (`new Var(..)` deep below), and javac requires the decl
            // before every reference (jdk11 ClassSpecializer$Factory$1Var:
            // "cannot find symbol Var" x11). Captures stay lexically valid:
            // jcdc hoists ALL local declarations to the block head, so any
            // captured local is in scope from position 0.
            let claimed_top = ANON_TOP_BLOCK.with(|t| {
                if t.get() {
                    t.set(false);
                    true
                } else {
                    false
                }
            });
            let n_orig = v.len();
            for i in 0..n_orig {
                walk_stmt_anon(&mut v[i], pc, pool, fam, pending, vt, declared);
            }
            // Local-class declarations bubble to the method-top block
            // (LOCAL_DECL_HOIST) at top level and inside LAMBDA bodies;
            // inside anonymous-CLASS bodies they splice inline (their
            // methods' uses are local — ReferencePipeline.flatMap's
            // FlatMap lives and dies inside the anon's opWrapSink, and
            // the anon body is a print-time string the outer mention
            // scan cannot see).
            if !pending.is_empty() {
                let in_anon_only = ANON_BODY_DEPTH.with(|d| d.get()) > 0
                    && LAMBDA_BODY_DEPTH.with(|d| d.get()) == 0;
                if in_anon_only && !claimed_top {
                    // Not the method-top block: leave the decls pending so
                    // the top block splices them before EVERY reference.
                } else if in_anon_only {
                    let mut k = 0;
                    while k < pending.len() {
                        let decl_name = match &pending[k] {
                            Stmt::ClassDecl { name, .. } => Some(name.clone()),
                            _ => None,
                        };
                        if let Some(name) = decl_name {
                            if declared.contains(&name)
                                || EXTERN_DECL.with(|x| x.borrow().contains(&name))
                            {
                                pending.remove(k);
                                continue;
                            }
                            declared.insert(name.clone());
                        }
                        k += 1;
                    }
                    let n0 = v.len();
                    if std::env::var("JCDC_DBG_ANON").is_ok() {
                        eprintln!("ANONAPPEND n0={} pending={}", n0, pending.len());
                    }
                    v.append(pending);
                    // Relocate each decl before its first mention in this
                    // block (uses inside the anon method itself).
                    let mut j = n0;
                    while j < v.len() {
                        let name = match &v[j] {
                            Stmt::ClassDecl { name, .. } => name.clone(),
                            _ => {
                                j += 1;
                                continue;
                            }
                        };
                        let marker = format!("\u{2}{}", name);
                        let first_use =
                            first_local_mention(v, &marker, &name, vt, fam).unwrap_or(j);
                        if std::env::var("JCDC_DBG_ANON").is_ok() {
                            eprintln!("RELOC name={} j={} first_use={} vlen={} depth={}", name, j, first_use, v.len(), ANON_BODY_DEPTH.with(|d| d.get()));
                        }
                        if first_use != j {
                            let d = v[j].clone();
                            v.insert(first_use, d);
                            let removed = if first_use < j { j + 1 } else { j };
                            v.remove(removed);
                        }
                        j += 1;
                    }
                } else {
                    let mut k = 0;
                    while k < pending.len() {
                        let decl_name = match &pending[k] {
                            Stmt::ClassDecl { name, .. } => Some(name.clone()),
                            _ => None,
                        };
                        if let Some(name) = decl_name {
                            let extern_done =
                                EXTERN_DECL.with(|x| x.borrow().contains(&name));
                            if declared.contains(&name) || extern_done {
                                pending.remove(k);
                                continue;
                            }
                            declared.insert(name.clone());
                            let d = pending.remove(k);
                            LOCAL_DECL_SITES.with(|c| {
                                if let Some(v) = c.borrow_mut().as_mut() {
                                    v.push(name.clone());
                                }
                            });
                            LOCAL_DECL_HOIST.with(|h| h.borrow_mut().push((name, d)));
                            continue;
                        }
                        k += 1;
                    }
                    if !pending.is_empty() {
                        v.append(pending);
                    }
                }
            }
        }
        Stmt::ExprStmt(e) => walk_expr_anon(e, pc, pool, fam, pending, vt),
        Stmt::LocalDef { init: Some(e), .. } => walk_expr_anon(e, pc, pool, fam, pending, vt),
        Stmt::Return(Some(e)) | Stmt::Throw(e) => walk_expr_anon(e, pc, pool, fam, pending, vt),
        Stmt::If { cond, then_stmt, else_stmt } => {
            walk_expr_anon(cond, pc, pool, fam, pending, vt);
            walk_stmt_anon(then_stmt, pc, pool, fam, pending, vt, declared);
            if let Some(e) = else_stmt {
                walk_stmt_anon(e, pc, pool, fam, pending, vt, declared);
            }
        }
        Stmt::While { cond, body } => {
            walk_expr_anon(cond, pc, pool, fam, pending, vt);
            walk_stmt_anon(body, pc, pool, fam, pending, vt, declared);
        }
        Stmt::DoWhile { body, cond } => {
            walk_stmt_anon(body, pc, pool, fam, pending, vt, declared);
            walk_expr_anon(cond, pc, pool, fam, pending, vt);
        }
        Stmt::For { init, cond, update, body } => {
            init.iter_mut().for_each(|i| walk_stmt_anon(i, pc, pool, fam, pending, vt, declared));
            if let Some(c) = cond {
                walk_expr_anon(c, pc, pool, fam, pending, vt);
            }
            update.iter_mut().for_each(|u| walk_expr_anon(u, pc, pool, fam, pending, vt));
            walk_stmt_anon(body, pc, pool, fam, pending, vt, declared);
        }
        Stmt::ForEach { iterable, body, .. } => {
            walk_expr_anon(iterable, pc, pool, fam, pending, vt);
            walk_stmt_anon(body, pc, pool, fam, pending, vt, declared);
        }
        Stmt::Switch { selector, cases, default, .. } => {
            walk_expr_anon(selector, pc, pool, fam, pending, vt);
            for c in cases {
                c.body.iter_mut().for_each(|st| walk_stmt_anon(st, pc, pool, fam, pending, vt, declared));
            }
            if let Some(d) = default {
                walk_stmt_anon(d, pc, pool, fam, pending, vt, declared);
            }
        }
        Stmt::Try { body, catches, finally } => {
            walk_stmt_anon(body, pc, pool, fam, pending, vt, declared);
            for c in catches {
                walk_stmt_anon(&mut c.body, pc, pool, fam, pending, vt, declared);
            }
            if let Some(f) = finally {
                walk_stmt_anon(f, pc, pool, fam, pending, vt, declared);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { walk_stmt_anon(res, pc, pool, fam, pending, vt, declared); }
            walk_stmt_anon(body, pc, pool, fam, pending, vt, declared);
            for c in catches {
                walk_stmt_anon(&mut c.body, pc, pool, fam, pending, vt, declared);
            }
            if let Some(f) = finally {
                walk_stmt_anon(f, pc, pool, fam, pending, vt, declared);
            }
        }
        Stmt::Synchronized { lock, body } => {
            walk_expr_anon(lock, pc, pool, fam, pending, vt);
            walk_stmt_anon(body, pc, pool, fam, pending, vt, declared);
        }
        // Coverage gaps that silently skipped anonymous `new` sites:
        // a Labeled body (SESE/walk label emission wraps loops and blocks),
        // Assert / TernaryValue / Monitor expressions. Missing these left
        // `new Outer$1(args)` un-inlined -> printed as the invalid
        // `new Outer.1(args)` / `new 1(args)` (jdk URLClassPath, a corpus
        // batch blocker on BOTH structurizers).
        Stmt::Labeled { body, .. } => {
            walk_stmt_anon(body, pc, pool, fam, pending, vt, declared);
        }
        Stmt::Assert { cond, msg } => {
            walk_expr_anon(cond, pc, pool, fam, pending, vt);
            if let Some(m) = msg {
                walk_expr_anon(m, pc, pool, fam, pending, vt);
            }
        }
        Stmt::TernaryValue { e } => walk_expr_anon(e, pc, pool, fam, pending, vt),
        Stmt::MonitorEnter(e) | Stmt::MonitorExit(e) => {
            walk_expr_anon(e, pc, pool, fam, pending, vt);
        }
        _ => {}
    }
}

/// Emit the source declaration of a local class once (dedup by simple
/// name), hoisting it out when its EnclosingMethod belongs to another
/// class. Called from construction sites AND from type-position mentions
/// (class literals / casts): jdk17 Module.moduleInfoClass references
/// `DummyModuleInfo` only via `DummyModuleInfo.class` — without a decl
/// the use is "找不到符号".
fn emit_local_class_decl(
    cls: &str,
    lpc: &PoolClass,
    simple: &str,
    pc: &PoolClass,
    pool: &ClassPool,
    fam: &Family,
    captures: &HashMap<String, Expr>,
    pending: &mut Vec<Stmt>,
) {
    let simple = simple.to_string();
    // Already extracted to an EARLIER statement of this method
    // (EXTERN_DECL is method-scoped): record the second mention site so
    // fix_lambda_captures can relocate the decl to a position dominating
    // both (jdk26 Gatherers Composite.impl: State extracted inside the
    // if-branch, mentioned again by the tail return after the chain —
    // 6 "找不到符号 类 State" at the tail).
    if EXTERN_DECL.with(|x| x.borrow().contains(&simple)) {
        EXTERN_REDECL.with(|r| r.borrow_mut().insert(simple.clone()));
        return;
    }
    // A local class whose EnclosingMethod names a DIFFERENT class than
    // the one being walked is declared in an enclosing scope (the new
    // site sits inside an inlined anonymous body): hoist the declaration
    // out instead of splicing it into the anon method.
    let hoist_out = enclosing_method_of(lpc)
        .map(|(c, _)| c != pc.internal_name)
        .unwrap_or(false);
    let dedup: &mut Vec<Stmt> = pending;
    if dedup.iter().any(|d| matches!(d, Stmt::ClassDecl { name, .. } if *name == simple)) {
        return;
    }
    let mut header = fam
        .nested
        .get(cls)
        .and_then(|n| n.sig_header.clone())
        .unwrap_or_else(|| simple.clone());
    if fam.nested.get(cls).and_then(|n| n.sig_header.as_ref()).is_none() {
        let mut bases: Vec<String> = Vec::new();
        let p = Printer::new(lpc, pool, empty_vt());
        if lpc.class_attr("Record").is_some() {
            // Local record: `record Name(components)`; the implicit
            // java.lang.Record supertype is not printed, but declared
            // interfaces ARE (`record CleanupAction(..) implements
            // Runnable` — dropping it made the value unassignable to
            // the method's Runnable return, jdk26
            // AbstractMemorySegmentImpl.cleanupAction).
            header = format!("record {}{}", simple, record_components(lpc, pool));
            let mut rifaces: Vec<String> = Vec::new();
            for &ii in &lpc.cf.interfaces {
                if let Some(n) = lpc.class_name(ii) {
                    if n != "java/lang/Record" {
                        rifaces.push(p.shorten(n));
                    }
                }
            }
            if !rifaces.is_empty() {
                header.push_str(" implements ");
                header.push_str(&rifaces.join(", "));
            }
        } else {
            for &ii in &lpc.cf.interfaces {
                if let Some(n) = lpc.class_name(ii) {
                    bases.push(p.shorten(n));
                }
            }
            if bases.is_empty() {
                if let Some(sup) = lpc.super_name() {
                    if sup != "java/lang/Object" && sup != "java/lang/Record" {
                        header.push_str(" extends ");
                        header.push_str(&p.shorten(sup));
                    }
                }
            } else {
                if let Some(sup) = lpc.super_name() {
                    if sup != "java/lang/Object" && sup != "java/lang/Record" {
                        header.push_str(" extends ");
                        header.push_str(&p.shorten(sup));
                    }
                }
                header.push_str(" implements ");
                header.push_str(&bases.join(", "));
            }
        }
    }
    let mut buf = String::new();
    // Sibling local classes: this class's body may declare-use another
    // local class of the SAME outer method (jdk26 Gatherers.mapConcurrent:
    // State.integrate does `new MapConcurrentTask(..)`, and State's field
    // type is ArrayDeque<MapConcurrentTask>). The inner walk hoists that
    // decl onto ANON_HOIST (its EnclosingMethod names the outer class, not
    // this one) but no build_anon_new follows to drain it — the decl was
    // lost entirely (19 "找不到符号"). Drain same-enclosing decls here and
    // put them BEFORE this class's own decl: a local class is in scope
    // only from its declaration onward, and the source declares the
    // sibling first (MapConcurrentTask at line 358, State at 366).
    let own_enc = enclosing_method_of(lpc);
    let hoist_mark = ANON_HOIST.with(|h| h.borrow().len());
    let emitted = emit_anon_body(lpc, pool, fam, captures, &mut buf, 0, true);
    if emitted.is_err() {
        ANON_HOIST.with(|h| h.borrow_mut().truncate(hoist_mark));
        return;
    }
    let siblings: Vec<Stmt> = ANON_HOIST.with(|h| {
        let mut h = h.borrow_mut();
        if h.len() <= hoist_mark {
            return Vec::new();
        }
        let mut keep: Vec<Stmt> = Vec::new();
        let mut taken: Vec<Stmt> = Vec::new();
        for d in h.drain(hoist_mark..) {
            let is_sibling = match (&d, &own_enc) {
                (Stmt::ClassDecl { name, .. }, Some(enc)) => fam
                    .nested
                    .iter()
                    .filter(|(_, nc)| nc.simple == *name)
                    .filter_map(|(internal, _)| pool.get(internal))
                    .any(|cpc| enclosing_method_of(&cpc).as_ref() == Some(enc)),
                _ => false,
            };
            if is_sibling {
                taken.push(d);
            } else {
                keep.push(d);
            }
        }
        h.extend(keep);
        taken
    });
    for d in siblings.into_iter().rev() {
        let dup = match &d {
            Stmt::ClassDecl { name, .. } => dedup
                .iter()
                .any(|x| matches!(x, Stmt::ClassDecl { name: n2, .. } if n2 == name)),
            _ => false,
        };
        if !dup {
            dedup.insert(0, d);
        }
    }
    let decl = Stmt::ClassDecl { name: simple.clone(), header, body: buf };
    if hoist_out {
        ANON_HOIST.with(|h| {
            let mut h = h.borrow_mut();
            if !h.iter().any(|d| matches!(d, Stmt::ClassDecl { name, .. } if *name == simple)) {
                h.push(decl);
            }
        });
    } else {
        dedup.push(decl);
    }
}

fn walk_expr_anon(e: &mut Expr, pc: &PoolClass, pool: &ClassPool, fam: &Family, pending: &mut Vec<Stmt>, vt: &VarTable) {
    if std::env::var("JCDC_DBG_ANON").is_ok() {
        if let Expr::New { cls, raw, .. } = e {
            eprintln!("ANON see new {} raw={} in_fam={}", cls, raw, fam.anonymous.contains(cls.as_str()));
        }
    }
    match e {
        Expr::New { cls, args, raw: false, .. } if fam.anonymous.contains(cls.as_str()) => {
            match pool.get(cls) {
                Some(apc) => {
                    if let Some(anon) = build_anon_new(&apc, args.clone(), pc, pool, fam, vt, pending) {
                        *e = anon;
                    } else if std::env::var("JCDC_DBG_ANON").is_ok() {
                        eprintln!("ANON inline declined {}", cls);
                    }
                }
                None => {
                    if std::env::var("JCDC_DBG_ANON").is_ok() {
                        eprintln!("ANON not in pool {}", cls);
                    }
                }
            }
        }
        Expr::New { cls, args, raw: false, ty, .. } if fam.locals.contains(cls.as_str()) => {
            if std::env::var("JCDC_DBG_ANON").is_ok() {
                eprintln!("LOCALNEW {} pending={} depth={}", cls, pending.len(), ANON_BODY_DEPTH.with(|d| d.get()));
            }
            if let Some(lpc) = pool.get(cls) {
                let simple = fam
                    .nested
                    .get(cls)
                    .map(|n| n.simple.clone())
                    .unwrap_or_else(|| simple_name(cls));
                let (kept, captures) = analyze_anon_ctor(&lpc, args.clone());
                let captures = render_captures(captures, pc, pool, vt);
                emit_local_class_decl(cls, &lpc, &simple, pc, pool, fam, &captures, pending);
                *e = Expr::New {
                    cls: format!("\u{2}{}", simple),
                    ty: ty.clone(),
                    args: kept,
                    raw: false,
                };
            }
        }
        // A class literal is the ONLY mention of some local classes
        // (jdk17 Module.moduleInfoClass: `clazz = DummyModuleInfo.class;`
        // with no construction site): emit the declaration here or the
        // name is unbound ("找不到符号").
        Expr::Const(crate::expr::ConstVal::ClassLit(t)) => {
            let internal = match t {
                TypeRef::J(JavaType::Object(n)) => Some(n.clone()),
                TypeRef::G(jcdc_jvm::GenericType::Class(cs)) => {
                    Some(crate::method::classsig_internal(cs))
                }
                _ => None,
            };
            if let Some(internal) = internal {
                if fam.locals.contains(internal.as_str()) {
                    if let Some(lpc) = pool.get(&internal) {
                        let simple = fam
                            .nested
                            .get(&internal)
                            .map(|n| n.simple.clone())
                            .unwrap_or_else(|| simple_name(&internal));
                        emit_local_class_decl(
                            &internal,
                            &lpc,
                            &simple,
                            pc,
                            pool,
                            fam,
                            &HashMap::new(),
                            pending,
                        );
                    }
                }
            }
        }
        Expr::New { args, .. } => args.iter_mut().for_each(|a| walk_expr_anon(a, pc, pool, fam, pending, vt)),
        Expr::AnonNew { args, .. } => args.iter_mut().for_each(|a| walk_expr_anon(a, pc, pool, fam, pending, vt)),
        Expr::Method { owner, args, .. } => {
            if let Some(o) = owner {
                walk_expr_anon(o, pc, pool, fam, pending, vt);
            }
            args.iter_mut().for_each(|a| walk_expr_anon(a, pc, pool, fam, pending, vt));
        }
        Expr::Field { owner: Some(o), .. } => walk_expr_anon(o, pc, pool, fam, pending, vt),
        Expr::ArrayIndex { array, index } => {
            walk_expr_anon(array, pc, pool, fam, pending, vt);
            walk_expr_anon(index, pc, pool, fam, pending, vt);
        }
        Expr::Cast { e: inner, .. } | Expr::InstanceOf { e: inner, .. } | Expr::Un { e: inner, .. } => {
            walk_expr_anon(inner, pc, pool, fam, pending, vt)
        }
        Expr::Bin { l, r, .. } => {
            walk_expr_anon(l, pc, pool, fam, pending, vt);
            walk_expr_anon(r, pc, pool, fam, pending, vt);
        }
        Expr::Cond { c, t, f } => {
            walk_expr_anon(c, pc, pool, fam, pending, vt);
            walk_expr_anon(t, pc, pool, fam, pending, vt);
            walk_expr_anon(f, pc, pool, fam, pending, vt);
        }
        Expr::Assign { target, value, .. } => {
            walk_expr_anon(target, pc, pool, fam, pending, vt);
            walk_expr_anon(value, pc, pool, fam, pending, vt);
        }
        Expr::PreIncDec { e: inner, .. } | Expr::PostIncDec { e: inner, .. } => {
            walk_expr_anon(inner, pc, pool, fam, pending, vt)
        }
        Expr::NewArray { dims, init, .. } => {
            dims.iter_mut().for_each(|d| walk_expr_anon(d, pc, pool, fam, pending, vt));
            if let Some(vals) = init {
                vals.iter_mut().for_each(|v| walk_expr_anon(v, pc, pool, fam, pending, vt));
            }
        }
        Expr::StringConcat(parts) => parts.iter_mut().for_each(|p| {
            if let crate::expr::ConcatPart::Str(inner) = p {
                walk_expr_anon(inner, pc, pool, fam, pending, vt);
            }
        }),
        Expr::Lambda(l) => l.captures.iter_mut().for_each(|c| walk_expr_anon(c, pc, pool, fam, pending, vt)),
        Expr::Invokedynamic { args, .. } => args.iter_mut().for_each(|a| walk_expr_anon(a, pc, pool, fam, pending, vt)),
        _ => {}
    }
}

/// Pre-render captured expressions in the OUTER context so the inner class
/// body (printed with its own VarTable) can splice them as raw text.
/// Dotted name for a qualified this (`X.this`): the last two `$`-segments
/// of the binary name (outermost of the pair + the class itself), or the
/// simple name for a top-level outer. A BARE simple name can be shadowed
/// inside the inner class by an inherited member type of the same name —
/// jdk11 SpinedBuffer$OfPrimitive$BaseSpliterator implements
/// java.util.Spliterator.OfPrimitive, whose member type is inherited into
/// scope and WINS the simple-name resolution, so `OfPrimitive.this`
/// resolves to the interface and javac rejects it ("not an enclosing
/// class", 13 errors in SpinedBuffer). `SpinedBuffer.OfPrimitive.this`
/// cannot be shadowed by a member type of SpinedBuffer.
fn qualified_this_tail(internal: &str) -> String {
    let (_, nested) = internal.rsplit_once('/').unwrap_or(("", internal));
    let segs: Vec<&str> = nested.split('$').collect();
    if segs.len() >= 2 {
        segs[segs.len() - 2..].join(".")
    } else {
        nested.to_string()
    }
}

/// Collapse a `this$N` field chain whose owner is an anonymous class:
/// `anonInstance.this$0` (possibly chained) resolves to the first NAMED
/// enclosing class, rendered `Name.this`. Anonymous classes have no
/// source name, but the lexical scope of an inlined anonymous body still
/// sees the named enclosing class. Returns None when the chain does not
/// bottom out at a named class resolvable in the pool.
fn collapse_this_chain(e: &Expr, pool: &ClassPool) -> Option<String> {
    let (name, cls) = match e {
        Expr::Field { name, cls, is_static: false, .. } if name.starts_with("this$") => {
            (name.as_str(), cls.as_str())
        }
        _ => return None,
    };
    let owner_pc = pool.get(cls)?;
    // Find the this$N field descriptor on the owner class.
    let mut target: Option<String> = None;
    for f in &owner_pc.cf.fields {
        if owner_pc.utf8(f.name_index).map(|n| n == name).unwrap_or(false) {
            if let Some(d) = owner_pc.utf8(f.descriptor_index) {
                if let Some(inner) = d.strip_prefix('L').and_then(|d| d.strip_suffix(';')) {
                    target = Some(inner.to_string());
                }
            }
            break;
        }
    }
    let target = target?;
    let simple = simple_name(&target);
    let anon = simple
        .chars()
        .next()
        .map(|c| c.is_ascii_digit())
        .unwrap_or(false);
    if anon {
        None
    } else {
        Some(format!("{}.this", qualified_this_tail(&target)))
    }
}

/// True when the expression is a call to a GENERIC method: its static type
/// at any argument position comes from inference, so inserting our own cast
/// would freeze a capture identity javac would otherwise unify.
pub(crate) fn g_has_typevar(g: &jcdc_jvm::GenericType) -> bool {
    use jcdc_jvm::GenericType as G;
    match g {
        G::TypeVar(_) => true,
        G::Array(i) => g_has_typevar(i),
        G::Class(cs) => cs.parts.iter().any(|p| p.args.iter().any(g_has_typevar)),
        G::Wildcard(w) => match w {
            jcdc_jvm::WildcardBound::Extends(i) | jcdc_jvm::WildcardBound::Super(i) => {
                g_has_typevar(i)
            }
            _ => false,
        },
        _ => false,
    }
}

pub(crate) fn g_has_wildcard(g: &jcdc_jvm::GenericType) -> bool {
    use jcdc_jvm::GenericType as G;
    match g {
        G::Wildcard(_) => true,
        G::Array(i) => g_has_wildcard(i),
        G::Class(cs) => cs.parts.iter().any(|p| p.args.iter().any(g_has_wildcard)),
        _ => false,
    }
}

/// A return expression whose static type is a WILDCARD parameterization
/// (`Class<?>`) does not satisfy a type-variable return (`Class<E>`) — javac
/// rejects the poly conditional outright ("条件表达式中的类型错误",
/// Enum.getDeclaringClass). No checkcast exists in the bytecode (same
/// erasure), so the cast must be reconstructed from the Signature: wrap the
/// return expression in `(RetG) expr` (unchecked, compilable). Skips
/// expressions already carrying the type-variable form (a poly conditional
/// whose branches are G — those compile as-is).
/// Cast bare-call arguments that sit at TYPEVAR (or array-of-typevar)
/// parameter positions but carry only their erasure: `Set.of(elements)`
/// where the source local was `E[] elements = (E[]) toArray()` — inlined,
/// the raw Object[] arg gives the call's inference variable an Object
/// equality bound that conflicts with the return position ("推论变量 E#1
/// 具有不兼容的上限", jdk11 Set.copyOf). The cast uses the ENCLOSING
/// method's return typevar name (valid when the call's variable flows
/// from the generic return — exactly the case the bare call failed on).
fn cast_typevar_param_args(
    cls: &str,
    name: &str,
    desc: &jcdc_jvm::MethodDescriptor,
    args: &mut [Expr],
    sig: &jcdc_jvm::MethodSignature,
    pool: &ClassPool,
) {
    let jcdc_jvm::GenericType::Class(ret_cs) = &sig.ret else {
        return;
    };
    let Some(ret_tvs) = ret_cs.parts.last().map(|p| &p.args) else {
        return;
    };
    if ret_tvs.is_empty() {
        return;
    }
    let Some(dpc) = pool.get(cls) else { return };
    let want_desc = {
        let mut a = String::new();
        for t in &desc.args {
            a.push_str(&t.to_descriptor());
        }
        format!("({}){}", a, desc.ret.to_descriptor())
    };
    let Some(mi) = (0..dpc.cf.methods.len()).find(|&i| {
        dpc.method_name(i) == Some(name) && dpc.method_desc(i) == Some(want_desc.as_str())
    }) else {
        return;
    };
    let Some(sig_bytes) = dpc.cf.methods[mi].attributes.iter().find_map(|a| {
        if dpc.utf8(a.attribute_name_index) == Some("Signature") {
            Some(a.info.as_slice())
        } else {
            None
        }
    }) else {
        return;
    };
    if sig_bytes.len() < 2 {
        return;
    }
    let idx = u16::from_be_bytes([sig_bytes[0], sig_bytes[1]]);
    let Some(msig) = dpc
        .utf8(idx)
        .and_then(|x| jcdc_jvm::parse_method_signature(x))
    else {
        return;
    };
    // Map the callee's return-parameter typevars positionally to the
    // enclosing return's.
    let mut map: Vec<(String, String)> = Vec::new();
    if let jcdc_jvm::GenericType::Class(cs) = &msig.ret {
        if let Some(last) = cs.parts.last() {
            for (a, b) in last.args.iter().zip(ret_tvs.iter()) {
                if let (jcdc_jvm::GenericType::TypeVar(x), jcdc_jvm::GenericType::TypeVar(y)) =
                    (a, b)
                {
                    map.push((x.clone(), y.clone()));
                }
            }
        }
    }
    if map.is_empty() {
        return;
    }
    fn subst(g: &jcdc_jvm::GenericType, map: &[(String, String)]) -> jcdc_jvm::GenericType {
        match g {
            jcdc_jvm::GenericType::TypeVar(x) => {
                let y = map
                    .iter()
                    .find(|(a, _)| a == x)
                    .map(|(_, b)| b.clone())
                    .unwrap_or_else(|| x.clone());
                jcdc_jvm::GenericType::TypeVar(y)
            }
            jcdc_jvm::GenericType::Array(i) => {
                jcdc_jvm::GenericType::Array(Box::new(subst(i, map)))
            }
            other => other.clone(),
        }
    }
    for (a, pt) in args.iter_mut().zip(msig.args.iter()) {
        let inst = subst(pt, &map);
        let is_tv = matches!(&inst, jcdc_jvm::GenericType::TypeVar(_))
            || matches!(&inst, jcdc_jvm::GenericType::Array(i)
                if matches!(&**i, jcdc_jvm::GenericType::TypeVar(_)));
        if !is_tv {
            continue;
        }
        if matches!(a, Expr::Cast { .. } | Expr::Const(_)) {
            continue;
        }
        let want = TypeRef::G(inst.clone());
        if a.type_ref() == want || a.type_ref().erased() != want.erased() {
            continue;
        }
        let inner = std::mem::replace(a, Expr::This);
        *a = Expr::Cast { ty: want, e: Box::new(inner) };
    }
}

fn witness_generic_returns(s: &mut Stmt, msig: Option<&jcdc_jvm::MethodSignature>, pool: &ClassPool) {
    use crate::expr::Expr;
    let Some(sig) = msig else { return };
    // Parameterized return, typevar or not: wildcard/capture values need
    // the source's unchecked cast (jdk17 Method.getTypeParameters returns
    // GenericDeclRepository.EMPTY_TYPE_VARS — TypeVariable<?>[] — as
    // TypeVariable<Method>[]; the cast leaves no checkcast trace).
    if !generic_ret_ish(&sig.ret) {
        return;
    }
    let ret_g = TypeRef::G(sig.ret.clone());
    let ret_er = ret_g.erased();
    // A returned value needs the erased-cast witness when its static type
    // is not convertible to the generic return: any reference type when
    // the return is a bare type variable (`(V) e.value` — Hashtable.get;
    // javac: "CAP#1 cannot be converted to V"), or a generic type carrying
    // type vars/wildcards with matching erasure. Type vars count too: a
    // field's own V (Entry<?,?>.value) is NOT the method's V — casts to a
    // type var are unchecked no-ops at runtime, so re-witnessing an
    // already-matching local is harmless.
    fn needs_witness(e: &Expr, ret_g: &TypeRef, ret_er: &jcdc_jvm::JavaType, pool: &ClassPool) -> bool {
        if matches!(e, Expr::Const(_) | Expr::Cast { .. }) {
            return false;
        }
        // A call already carrying explicit type witnesses types itself
        // (`Collections.<T>unmodifiableList(...)` IS List<T>); wrapping it
        // in a cast re-freezes inference and kills diamond args inside
        // ("无法推断ArrayList<>的类型参数", jdk17 Stream.toList).
        if matches!(e, Expr::Method { type_args, .. } if !type_args.is_empty()) {
            return false;
        }
        // Lambda/method-ref arms are poly expressions: they take their
        // target type from the return position itself. Wrapping the
        // conditional in a witness cast turns it into a standalone
        // expression and javac rejects the poly arms ("此处不应为 lambda
        // 表达式", jdk11 Predicate.isEqual `(Predicate<T>) (c ? l : m)`).
        if matches!(e, Expr::Lambda(_)) {
            return false;
        }
        // Ternaries: javac glues the branches; if ANY branch needs the
        // witness, wrap the whole cond (`(T) (c ? a : b)` — Hashtable
        // Enumerator.next).
        if let Expr::Cond { t, f, .. } = e {
            return needs_witness(t, ret_g, ret_er, pool) || needs_witness(f, ret_g, ret_er, pool);
        }
        let ret_is_typevar = matches!(ret_g, TypeRef::G(g) if g_has_typevar(g));
        match e.type_ref() {
            TypeRef::J(j) => {
                if ret_is_typevar {
                    matches!(j, jcdc_jvm::JavaType::Object(_) | jcdc_jvm::JavaType::Array(_))
                } else {
                    &j == ret_er
                }
            }
            TypeRef::G(g) => {
                // Identical parameterization: assignable as-is.
                if &TypeRef::G(g.clone()) == ret_g {
                    return false;
                }
                // A raw value converts unchecked-but-legal to any
                // parameterization of its erasure.
                if let jcdc_jvm::GenericType::Class(cs) = &g {
                    if cs.parts.iter().all(|p| p.args.is_empty()) {
                        return false;
                    }
                }
                let ev = TypeRef::G(g.clone()).erased();
                if &ev == ret_er {
                    // Same erasure, different parameterization: type
                    // vars/wildcards (CAP#1, a field's own V —
                    // Hashtable.get) AND concrete-but-different args
                    // (Spliterator<Object> -> Spliterator<T>, jdk11
                    // Spliterators.emptySpliterator — the source's
                    // unchecked cast leaves no checkcast) all need the
                    // erased witness; casts to generic types are unchecked
                    // no-ops at runtime, so re-witnessing an
                    // already-matching local is harmless.
                    return true;
                }
                // Subclass erasure with incompatible parameterization
                // (ListN<?> -> List<E>, jdk17 List.of(): "ListN<CAP#1>
                // 无法转换为List<E>") — only an unchecked cast bridges.
                match (&ev, ret_er) {
                    (jcdc_jvm::JavaType::Object(_), jcdc_jvm::JavaType::Object(n)) => {
                        is_subtype_of(pool, &ev, n)
                    }
                    _ => false,
                }
            }
        }
    }
    fn fix(
        e: &mut Expr,
        ret_g: &TypeRef,
        ret_er: &jcdc_jvm::JavaType,
        pool: &ClassPool,
        sig: &jcdc_jvm::MethodSignature,
    ) {
        // A conditional with a poly (lambda/method-ref) arm must NOT be
        // wrapped as a whole: the cast makes the conditional standalone
        // and javac rejects the poly arm ("此处不应为 lambda 表达式").
        // Witness the non-poly arms individually instead — in the return
        // position the conditional stays a poly expression and the lambda
        // arm takes the method's return type directly.
        if let Expr::Cond { t, f, .. } = e {
            if matches!(**t, Expr::Lambda(_)) || matches!(**f, Expr::Lambda(_)) {
                fix(t, ret_g, ret_er, pool, sig);
                fix(f, ret_g, ret_er, pool, sig);
                return;
            }
        }
        if !needs_witness(e, ret_g, ret_er, pool) {
            return;
        }
        // A GENERIC CALL must never take the cast: the cast context
        // starves its inference (it resolves to the bounds —
        // BiConsumer<Object,..> — and the cast to the parameterized
        // return is then REJECTED: "BiConsumer<Object,Downstream<? super
        // Object>>无法转换为BiConsumer<A,Downstream<? super R>>", jdk26
        // Gatherer.finisher). Prefer the explicit type witness; failing
        // that, leave the call bare — the return position infers it
        // (verified: both forms compile where the cast does not).
        let generic_bare = matches!(e, Expr::Method { type_args, .. } if type_args.is_empty())
            && is_generic_call(e, pool);
        if generic_bare {
            if let Expr::Method { cls, name, desc, type_args, owner, args, .. } = e {
                if let TypeRef::G(want) = ret_g {
                    // Diamond-bearing args must stay bare: an explicit
                    // outer witness pins the formal and gives the inner
                    // diamond contradictory bounds (jdk17 Stream.toList).
                    if !args_have_generic_new(args, pool) {
                        let w = compute_witness(
                            cls.as_str(),
                            name.as_str(),
                            desc,
                            owner.as_deref(),
                            want,
                            pool,
                            Some(&sig.params),
                        );
                        if let Some((wit, mapping)) = w {
                            *type_args = wit;
                            retype_witness_arg_casts(cls, name, desc, args, &mapping, pool);
                            return;
                        }
                    }
                    // Bare shape: typevar-parameter args that lost their
                    // source local's cast need it back at the arg.
                    cast_typevar_param_args(cls, name, desc, args, sig, pool);
                    // Witness failed. A cast to a typevar (or array of
                    // one) is always-legal unchecked and often REQUIRED
                    // (jdk17 ArrayList.toArray `(T[]) Arrays.copyOf(..)`
                    // — bare inference cannot recover T). A cast to a
                    // parameterized class would freeze inference and can
                    // be rejected outright (Gatherer.finisher) — there
                    // the bare call infers from the return position
                    // (the source shape).
                    let tv_target = matches!(want, jcdc_jvm::GenericType::TypeVar(_))
                        || matches!(want, jcdc_jvm::GenericType::Array(i)
                            if matches!(&**i, jcdc_jvm::GenericType::TypeVar(_)));
                    if tv_target {
                        let v = std::mem::replace(e, Expr::This);
                        *e = Expr::Cast { ty: ret_g.clone(), e: Box::new(v) };
                    }
                    return;
                }
            }
            return;
        }
        let v = std::mem::replace(e, Expr::This);
        *e = Expr::Cast { ty: ret_g.clone(), e: Box::new(v) };
    }
    fn rec(s: &mut Stmt, ret_g: &TypeRef, ret_er: &jcdc_jvm::JavaType, pool: &ClassPool, sig: &jcdc_jvm::MethodSignature) {
        match s {
            Stmt::Block(v) => v.iter_mut().for_each(|x| rec(x, ret_g, ret_er, pool, sig)),
            Stmt::Return(Some(e)) => fix(e, ret_g, ret_er, pool, sig),
            Stmt::If { then_stmt, else_stmt, .. } => {
                rec(then_stmt, ret_g, ret_er, pool, sig);
                if let Some(x) = else_stmt {
                    rec(x, ret_g, ret_er, pool, sig);
                }
            }
            Stmt::While { body, .. }
            | Stmt::DoWhile { body, .. }
            | Stmt::ForEach { body, .. }
            | Stmt::Labeled { body, .. }
            | Stmt::Synchronized { body, .. } => rec(body, ret_g, ret_er, pool, sig),
            Stmt::For { init, body, .. } => {
                init.iter_mut().for_each(|i| rec(i, ret_g, ret_er, pool, sig));
                rec(body, ret_g, ret_er, pool, sig);
            }
            Stmt::Switch { cases, default, .. } => {
                for c in cases.iter_mut() {
                    for st in c.body.iter_mut() {
                        rec(st, ret_g, ret_er, pool, sig);
                    }
                }
                if let Some(d) = default {
                    rec(d, ret_g, ret_er, pool, sig);
                }
            }
            Stmt::Try { body, catches, finally } => {
                rec(body, ret_g, ret_er, pool, sig);
                for c in catches.iter_mut() {
                    rec(&mut c.body, ret_g, ret_er, pool, sig);
                }
                if let Some(f) = finally {
                    rec(f, ret_g, ret_er, pool, sig);
                }
            }
            _ => {}
        }
    }
    rec(s, &ret_g, &ret_er, pool, sig);
}

/// True when `(cls, name)` is one of the signature-polymorphic methods
/// closed-set defined by JVMS 2.9 (only java.lang.invoke.MethodHandle and
/// java.lang.invoke.VarHandle carry @PolymorphicSignature). The pool is NOT
/// consulted: corpus runs carry a jdk8 rt.jar classpath where VarHandle
/// (JDK9+) is absent, so attribute lookup would miss exactly the classes
/// that need it.
pub(crate) fn is_spec_polymorphic(cls: &str, name: &str) -> bool {
    match cls {
        "java/lang/invoke/MethodHandle" => matches!(
            name,
            "invoke" | "invokeExact" | "invokeBasic" | "linkToVirtual"
                | "linkToStatic" | "linkToSpecial" | "linkToInterface" | "linkToNative"
        ),
        "java/lang/invoke/VarHandle" => matches!(
            name,
            "get" | "set" | "getVolatile" | "setVolatile" | "getOpaque" | "setOpaque"
                | "getAcquire" | "setRelease" | "compareAndSet" | "compareAndExchange"
                | "compareAndExchangeAcquire" | "compareAndExchangeRelease"
                | "weakCompareAndSet" | "weakCompareAndSetPlain" | "weakCompareAndSetAcquire"
                | "weakCompareAndSetRelease" | "getAndSet" | "getAndSetAcquire"
                | "getAndSetRelease" | "getAndAdd" | "getAndAddAcquire" | "getAndAddRelease"
                | "getAndBitwiseOr" | "getAndBitwiseOrAcquire" | "getAndBitwiseOrRelease"
                | "getAndBitwiseAnd" | "getAndBitwiseAndAcquire" | "getAndBitwiseAndRelease"
                | "getAndBitwiseXor" | "getAndBitwiseXorAcquire" | "getAndBitwiseXorRelease"
        ),
        _ => false,
    }
}

/// For a signature-polymorphic call (see `is_spec_polymorphic`), return the
/// call-site descriptor's return type. The SOURCE form must carry an
/// explicit cast: javac only gives such a call its descriptor return type
/// when a cast is present — bare `((s = STATUS.getAndBitwiseOr(this, DONE))
/// & SIGNAL)` types as Object and fails to compile (jdk ForkJoinTask
/// family). The original source always casts AT the call site (even in
/// plain assignments), so the printer emits it unconditionally. None for
/// non-polymorphic calls or Object/void descriptors (no cast needed).
pub(crate) fn polymorphic_ret_cast(
    cls: &str,
    name: &str,
    desc: &jcdc_jvm::MethodDescriptor,
) -> Option<jcdc_jvm::JavaType> {
    match &desc.ret {
        // Only a call-site descriptor returning plain Object needs no cast;
        // ANY other reference return (e.g. invokeBasic's `(BoundMethodHandle)
        // factory().invokeBasic(..)` — the source cast fixes the descriptor)
        // must be witnessed, or the bare call types as Object.
        jcdc_jvm::JavaType::Object(n) if n == "java/lang/Object" => None,
        jcdc_jvm::JavaType::Void => None,
        _ if is_spec_polymorphic(cls, name) => Some(desc.ret.clone()),
        _ => None,
    }
}

/// True when a generic return type actually differs from its erasure
/// (type variable, generic array, or parameterized class).
fn generic_ret_ish(g: &jcdc_jvm::GenericType) -> bool {
    use jcdc_jvm::GenericType as G;
    match g {
        G::TypeVar(_) => true,
        G::Array(i) => generic_ret_ish(i),
        G::Class(cs) => cs.parts.iter().any(|p| !p.args.is_empty()),
        _ => false,
    }
}

/// In a method whose SIGNATURE return is generic (`T[]`, `List<E>`, ...), a
/// javac-emitted checkcast to the ERASURE at a return position is invalid
/// source: the erasure is not convertible to the generic return type
/// ("Object[] cannot be converted to T[]", Class.getEnumConstants — a corpus
/// family blocker). When the cast's inner expression already carries the
/// generic source type (a generic-typed local/field/call, or `clone()` on a
/// generic array receiver — a poly expression typed by the return target),
/// drop the erasure cast: the bare expression compiles exactly like the
/// original source did.
fn strip_erasure_casts_generic_ret(s: &mut Stmt, msig: Option<&jcdc_jvm::MethodSignature>, pool: &ClassPool) {
    let Some(sig) = msig else { return };
    if !generic_ret_ish(&sig.ret) {
        return;
    }
    let ret_er = TypeRef::G(sig.ret.clone()).erased();
    fn fix(e: &mut Expr, ret_er: &jcdc_jvm::JavaType, pool: &ClassPool) {
        match e {
            Expr::Cond { t, f, .. } => {
                fix(t, ret_er, pool);
                fix(f, ret_er, pool);
            }
            Expr::Cast { ty, e: inner } => {
                if &ty.erased() == ret_er {
                    // Only GENERICS-ONLY casts (inner erasure == cast
                    // erasure — javac emits no checkcast for those, so
                    // they are our own synthesis) may be dropped. A cast
                    // whose erasure DIFFERS from the value's type is a
                    // real bytecode downcast that the source needs:
                    // jdk11 Set.copyOf's `return (Set<E>) coll;` (coll:
                    // Collection<CAP#1>) was stripped to `return coll;`
                    // — "Collection<CAP#1> cannot be converted to Set<E>"
                    // (the vP jdk11 first blocker, both paths).
                    let erasure_only = inner.type_ref().erased() == ty.erased();
                    let droppable = (matches!(inner.type_ref(), TypeRef::G(_)) && erasure_only)
                        || (is_generic_call(inner, pool) && erasure_only)
                        || matches!(&**inner, Expr::Method { name, owner: Some(o), .. }
                            if name == "clone" && matches!(o.type_ref(), TypeRef::G(_)));
                    if droppable {
                        let v = std::mem::replace(&mut **inner, Expr::This);
                        *e = v;
                        return;
                    }
                }
                fix(inner, ret_er, pool);
            }
            _ => {}
        }
    }
    fn rec(s: &mut Stmt, ret_er: &jcdc_jvm::JavaType, pool: &ClassPool) {
        match s {
            Stmt::Block(v) => v.iter_mut().for_each(|x| rec(x, ret_er, pool)),
            Stmt::Return(Some(e)) => fix(e, ret_er, pool),
            Stmt::If { then_stmt, else_stmt, .. } => {
                rec(then_stmt, ret_er, pool);
                if let Some(x) = else_stmt {
                    rec(x, ret_er, pool);
                }
            }
            Stmt::While { body, .. }
            | Stmt::DoWhile { body, .. }
            | Stmt::ForEach { body, .. }
            | Stmt::Labeled { body, .. }
            | Stmt::Synchronized { body, .. } => rec(body, ret_er, pool),
            Stmt::For { init, body, .. } => {
                init.iter_mut().for_each(|i| rec(i, ret_er, pool));
                rec(body, ret_er, pool);
            }
            Stmt::Switch { cases, default, .. } => {
                for c in cases.iter_mut() {
                    for st in c.body.iter_mut() {
                        rec(st, ret_er, pool);
                    }
                }
                if let Some(d) = default {
                    rec(d, ret_er, pool);
                }
            }
            Stmt::Try { body, catches, finally } => {
                rec(body, ret_er, pool);
                for c in catches.iter_mut() {
                    rec(&mut c.body, ret_er, pool);
                }
                if let Some(f) = finally {
                    rec(f, ret_er, pool);
                }
            }
            _ => {}
        }
    }
    rec(s, &ret_er, pool);
}

pub(crate) fn is_generic_call(a: &Expr, pool: &ClassPool) -> bool {
    let (cls, name, desc) = match a {
        Expr::Method { cls, name, desc, .. } => (cls.as_str(), name.as_str(), desc),
        _ => return false,
    };
    let want_desc = {
        let mut s = String::new();
        for t in &desc.args {
            s.push_str(&t.to_descriptor());
        }
        format!("({}){}", s, desc.ret.to_descriptor())
    };
    let Some(dpc) = pool.get(cls) else { return false };
    let Some(mi) = (0..dpc.cf.methods.len()).find(|&i| {
        dpc.method_name(i) == Some(name) && dpc.method_desc(i) == Some(want_desc.as_str())
    }) else { return false };
    let Some(sig_bytes) = dpc.cf.methods[mi].attributes.iter().find_map(|at| {
        if dpc.utf8(at.attribute_name_index) == Some("Signature") {
            Some(at.info.as_slice())
        } else {
            None
        }
    }) else { return false };
    if sig_bytes.len() < 2 {
        return false;
    }
    let idx = u16::from_be_bytes([sig_bytes[0], sig_bytes[1]]);
    dpc.utf8(idx)
        .and_then(|s2| jcdc_jvm::parse_method_signature(s2))
        .map(|msig| !msig.params.is_empty())
        .unwrap_or(false)
}

fn render_captures(
    captures: HashMap<String, Expr>,
    outer_pc: &PoolClass,
    pool: &ClassPool,
    outer_vt: &VarTable,
) -> HashMap<String, Expr> {
    let outer_simple = simple_name(&outer_pc.internal_name);
    let outer_qthis = qualified_this_tail(&outer_pc.internal_name);
    captures
        .into_iter()
        .map(|(k, v)| {
            if k.starts_with("this$") {
                // Anonymous outer classes have no source name; their body is
                // inlined, so plain `this` denotes the same instance.
                let starts_digit = outer_simple
                    .chars()
                    .next()
                    .map(|c| c.is_ascii_digit())
                    .unwrap_or(false);
                return if starts_digit {
                    (k, Expr::Raw("this".to_string()))
                } else {
                    (k, Expr::Raw(format!("{}.this", outer_qthis)))
                };
            }
            let mut p = Printer::new(outer_pc, pool, outer_vt);
            let mut text = String::new();
            let atomic = matches!(v, Expr::Local { .. } | Expr::This | Expr::Const(_));
            if !atomic {
                text.push('(');
            }
            p.expr(&v, 1, &mut text);
            if !atomic {
                text.push(')');
            }
            (k, Expr::Raw(text))
        })
        .collect()
}

fn build_anon_new(
    apc: &PoolClass,
    args: Vec<Expr>,
    outer_pc: &PoolClass,
    pool: &ClassPool,
    fam: &Family,
    outer_vt: &VarTable,
    outer_pending: &mut Vec<Stmt>,
) -> Option<Expr> {
    // Prefer the generic ClassSignature: anonymous classes record their
    // instantiated interface/superclass there, and the emitted body only
    // overrides the generic methods (bridges are hidden).
    let sig_base: Option<TypeRef> = apc.class_attr("Signature").and_then(|b| {
        if b.len() < 2 {
            return None;
        }
        let idx = u16::from_be_bytes([b[0], b[1]]);
        let sig = apc.utf8(idx).and_then(|s| parse_class_signature(s))?;
        if let Some(i) = sig.interfaces.first() {
            return Some(TypeRef::G(i.clone()));
        }
        match &sig.superclass {
            jcdc_jvm::GenericType::Class(cs)
                if cs.parts.first().map(|p| p.name == "Object").unwrap_or(false) =>
            {
                None
            }
            other => Some(TypeRef::G(other.clone())),
        }
    });
    let base = if let Some(&i) = apc.cf.interfaces.first() {
        let n = apc.class_name(i)?;
        sig_base.unwrap_or(TypeRef::J(JavaType::Object(n.to_string())))
    } else {
        let sup = apc.super_name()?.to_string();
        if sup == "java/lang/Object" {
            return None;
        }
        sig_base.unwrap_or(TypeRef::J(JavaType::Object(sup)))
    };

    let (kept_args, captures) = analyze_anon_ctor(apc, args);
    let captures = render_captures(captures, outer_pc, pool, outer_vt);

    let mut body = String::new();
    let hoist_mark = ANON_HOIST.with(|h| h.borrow().len());
    if let Err(e) = emit_anon_body(apc, pool, fam, &captures, &mut body, 0, false) {
        if std::env::var("JCDC_DBG_ANON").is_ok() {
            eprintln!("ANON build fail {}: {}", apc.internal_name, e);
        }
        ANON_HOIST.with(|h| h.borrow_mut().truncate(hoist_mark));
        return None;
    }
    // Local-class declarations belonging to the OUTER method surfaced
    // during the body walk: splice them into the outer pending list so
    // they land before the statement containing this anonymous new.
    ANON_HOIST.with(|h| {
        let mut h = h.borrow_mut();
        if h.len() > hoist_mark {
            outer_pending.extend(h.drain(hoist_mark..));
        }
    });
    let _ = outer_pc;

    Some(Expr::AnonNew { cls: apc.internal_name.clone(), base, args: kept_args, body })
}

/// Determine which ctor params are captures (stored into this$*/val$*
/// fields). Returns (kept args, field name -> captured expr).
fn analyze_anon_ctor(apc: &PoolClass, args: Vec<Expr>) -> (Vec<Expr>, HashMap<String, Expr>) {
    let mut captures: HashMap<String, Expr> = HashMap::new();
    let mut captured_idx: HashSet<usize> = HashSet::new();
    // The ctor matching the CALL SITE's arity: a local class with several
    // ctors applied the FIRST ctor's capture positions to every new site
    // (jdk11 Var: `new Var(vn, vt, className)` — prev dropped, className
    // kept — "String无法转换为Var").
    //
    // Same-arity ties: prefer the ctor that directly STORES the captures.
    // A delegating ctor hands them through this(..) — picking it left the
    // captures map empty and every val$ ref leaked unsubstituted (jdk26
    // Gatherers Composite.impl State: two 16-param ctors, the first
    // delegates; 24 "找不到符号 变量 val$leftStateless").
    fn capture_store_count(apc: &PoolClass, mi: usize) -> usize {
        decompile_method(apc, empty_pool(), mi)
            .ok()
            .flatten()
            .map(|mb| {
                stmt_vec(&mb.body)
                    .iter()
                    .filter(|st| {
                        matches!(st, Stmt::ExprStmt(Expr::Assign { target, .. })
                            if matches!(&**target, Expr::Field { name, is_static: false, .. }
                                if name.starts_with("this$") || name.starts_with("val$")))
                    })
                    .count()
            })
            .unwrap_or(0)
    }
    let arity_matches: Vec<usize> = (0..apc.cf.methods.len())
        .filter(|&mi| {
            apc.method_name(mi) == Some("<init>")
                && apc
                    .method_desc(mi)
                    .and_then(parse_method_descriptor)
                    .map(|md| md.args.len() == args.len())
                    .unwrap_or(false)
        })
        .collect();
    let ctor = match arity_matches.len() {
        0 => (0..apc.cf.methods.len()).find(|&mi| apc.method_name(mi) == Some("<init>")),
        1 => Some(arity_matches[0]),
        _ => Some(
            *arity_matches
                .iter()
                .max_by_key(|&&mi| capture_store_count(apc, mi))
                .unwrap(),
        ),
    };
    if let Some(mi) = ctor {
        if let Ok(Some(mb)) = decompile_method(apc, empty_pool(), mi) {
            // param var name -> index
            let mut param_names: Vec<(String, usize)> = Vec::new();
            let mut idx = 0usize;
            for v in &mb.vt.vars {
                if v.is_param && v.name != "this" {
                    param_names.push((v.name.clone(), idx));
                    idx += 1;
                }
            }
            for st in stmt_vec(&mb.body) {
                if let Stmt::ExprStmt(Expr::Assign { target, value, .. }) = st {
                    if let Expr::Field { name: fname, is_static: false, .. } = &*target {
                        if fname.starts_with("this$") || fname.starts_with("val$") {
                            if let Expr::Local { var, .. } = &*value {
                                let vname = mb.vt.var(*var).name.clone();
                                if let Some((_, pi)) = param_names.iter().find(|(n, _)| *n == vname) {
                                    if let Some(e) = args.get(*pi) {
                                        captures.insert(fname.clone(), e.clone());
                                        captured_idx.insert(*pi);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            // Delegating ctor: the capture stores live in the this(..)
            // target. Map the delegation's plain-local args back through
            // THIS ctor's params to the call-site args and harvest there
            // (jdk26 State joinLeft `new State(4 args)` matches no
            // bytecode arity and fell back to the 16-param delegator:
            // kept args must stay the 4 declared ones, captures come from
            // the delegatee's stores).
            if captures.is_empty() {
                let deleg = stmt_vec(&mb.body).iter().find_map(|st| match st {
                    Stmt::ExprStmt(Expr::Method { name, cls, desc, args: dargs, is_special: true, .. })
                        if name == "<init>" && cls == &apc.internal_name =>
                    {
                        Some((desc.args.len(), dargs.clone()))
                    }
                    _ => None,
                });
                if let Some((dargc, dargs)) = deleg {
                    // Pure-forward params: used ONLY as plain delegation
                    // args. Declared params participate in computed
                    // delegation args (jdk26 State: leftStateless feeds
                    // `!leftStateless ? leftInitializer.get() : null` AND
                    // doubles as the val$leftStateless capture source —
                    // marking it captured emptied the kept args:
                    // `() -> new State()` against a 12-param ctor).
                    let mut used_elsewhere: HashSet<u32> = HashSet::new();
                    fn collect_locals(e: &Expr, out: &mut HashSet<u32>) {
                        match e {
                            Expr::Local { var, .. } => {
                                out.insert(*var);
                            }
                            Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
                                args.iter().for_each(|a| collect_locals(a, out));
                            }
                            Expr::Method { owner, args, .. } => {
                                if let Some(o) = owner {
                                    collect_locals(o, out);
                                }
                                args.iter().for_each(|a| collect_locals(a, out));
                            }
                            Expr::Field { owner: Some(o), .. } => collect_locals(o, out),
                            Expr::ArrayIndex { array, index } => {
                                collect_locals(array, out);
                                collect_locals(index, out);
                            }
                            Expr::Cast { e: i, .. }
                            | Expr::InstanceOf { e: i, .. }
                            | Expr::Un { e: i, .. }
                            | Expr::PreIncDec { e: i, .. }
                            | Expr::PostIncDec { e: i, .. } => collect_locals(i, out),
                            Expr::Bin { l, r, .. } => {
                                collect_locals(l, out);
                                collect_locals(r, out);
                            }
                            Expr::Cond { c, t, f } => {
                                collect_locals(c, out);
                                collect_locals(t, out);
                                collect_locals(f, out);
                            }
                            Expr::Assign { target, value, .. } => {
                                collect_locals(target, out);
                                collect_locals(value, out);
                            }
                            Expr::NewArray { dims, init, .. } => {
                                dims.iter().for_each(|d| collect_locals(d, out));
                                if let Some(vals) = init {
                                    vals.iter().for_each(|x| collect_locals(x, out));
                                }
                            }
                            Expr::NewMultiArray { dims, .. } => {
                                dims.iter().for_each(|d| collect_locals(d, out));
                            }
                            Expr::StringConcat(parts) => parts.iter().for_each(|pp| {
                                if let crate::expr::ConcatPart::Str(i) = pp {
                                    collect_locals(i, out);
                                }
                            }),
                            Expr::Lambda(l) => {
                                l.captures.iter().for_each(|c| collect_locals(c, out));
                            }
                            Expr::Invokedynamic { args, .. } => {
                                args.iter().for_each(|a| collect_locals(a, out));
                            }
                            _ => {}
                        }
                    }
                    fn collect_stmt_locals(st: &Stmt, selfcls: &str, out: &mut HashSet<u32>) {
                        match st {
                            Stmt::ExprStmt(Expr::Method { name, cls, is_special: true, args, .. })
                                if name == "<init>" && cls == selfcls =>
                            {
                                for a in args {
                                    match a {
                                        Expr::Local { .. } => {}
                                        other => collect_locals(other, out),
                                    }
                                }
                            }
                            Stmt::ExprStmt(e) => collect_locals(e, out),
                            Stmt::LocalDef { init: Some(e), .. } => collect_locals(e, out),
                            Stmt::Return(Some(e)) => collect_locals(e, out),
                            Stmt::Throw(e) => collect_locals(e, out),
                            Stmt::Block(v) => {
                                v.iter().for_each(|x| collect_stmt_locals(x, selfcls, out));
                            }
                            _ => {}
                        }
                    }
                    for st in stmt_vec(&mb.body) {
                        collect_stmt_locals(&st, &apc.internal_name, &mut used_elsewhere);
                    }
                    let target_mi = (0..apc.cf.methods.len())
                        .filter(|&mi2| {
                            mi2 != mi
                                && apc.method_name(mi2) == Some("<init>")
                                && apc
                                    .method_desc(mi2)
                                    .and_then(parse_method_descriptor)
                                    .map(|md| md.args.len() == dargc)
                                    .unwrap_or(false)
                        })
                        .find(|&mi2| capture_store_count(apc, mi2) > 0);
                    if let Some(mi2) = target_mi {
                        if let Ok(Some(mb2)) = decompile_method(apc, empty_pool(), mi2) {
                            let mut p2: Vec<String> = Vec::new();
                            for v in &mb2.vt.vars {
                                if v.is_param && v.name != "this" {
                                    p2.push(v.name.clone());
                                }
                            }
                            for st in stmt_vec(&mb2.body) {
                                if let Stmt::ExprStmt(Expr::Assign { target, value, .. }) = st {
                                    if let Expr::Field { name: fname, is_static: false, .. } = &*target {
                                        if !(fname.starts_with("this$") || fname.starts_with("val$")) {
                                            continue;
                                        }
                                        if let Expr::Local { var, .. } = &*value {
                                            let vname = mb2.vt.var(*var).name.clone();
                                            let Some(k) = p2.iter().position(|n| *n == vname) else {
                                                continue;
                                            };
                                            // delegation arg k must be a plain
                                            // param local of THIS ctor
                                            let Some(Expr::Local { var: dv, .. }) = dargs.get(k) else {
                                                continue;
                                            };
                                            let dname = mb.vt.var(*dv).name.clone();
                                            let Some((_, pi)) =
                                                param_names.iter().find(|(n, _)| *n == dname)
                                            else {
                                                continue;
                                            };
                                            if let Some(e) = args.get(*pi) {
                                                captures.insert(fname.clone(), e.clone());
                                                // A declared param that DOUBLES
                                                // as a capture source stays in
                                                // the kept args: only pure
                                                // forwards are stripped.
                                                if !used_elsewhere.contains(dv) {
                                                    captured_idx.insert(*pi);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    // jdk21+ javac drops the this$0 FIELD when the anon body never
    // dereferences the outer instance: the ctor still RECEIVES it (param
    // 0, type = an enclosing $-prefix class) but only requireNonNull's
    // and pops it. The store-scan above misses it and the outer `this`
    // leaks into the new-site args ("匿名类实现接口; 不能有参数", jdk26
    // ClassFileImpl.transformClass). At an anon new site the enclosing
    // instance is always implicit, so drop a leading param of enclosing
    // type. (A static-context anon passing a real outer-typed value to
    // its super ctor would defeat this, but then javac would have kept a
    // use for it beyond requireNonNull — accepted edge.)
    if let Some(mi) = ctor {
        if !captured_idx.contains(&0) {
            if let Some(d) = apc.method_desc(mi) {
                if let Some(md) = parse_method_descriptor(d) {
                    if let Some(JavaType::Object(first)) = md.args.first() {
                        let name = &apc.internal_name;
                        let mut prefix = name.as_str();
                        let mut encloses = false;
                        while let Some(i) = prefix.rfind('$') {
                            prefix = &prefix[..i];
                            if prefix == first {
                                encloses = true;
                                break;
                            }
                        }
                        if encloses {
                            captured_idx.insert(0);
                        }
                    }
                }
            }
        }
    }
    if std::env::var("JCDC_DBG_ANON").is_ok() {
        eprintln!(
            "ANALYZE cls={} ctor={:?} arity={} captures={} captured_idx={:?}",
            apc.internal_name,
            ctor,
            args.len(),
            captures.len(),
            {
                let mut v: Vec<usize> = captured_idx.iter().copied().collect();
                v.sort();
                v
            }
        );
    }
    let kept: Vec<Expr> = args
        .into_iter()
        .enumerate()
        .filter(|(i, _)| !captured_idx.contains(i))
        .map(|(_, a)| a)
        .collect();
    (kept, captures)
}

fn self_simple_all_digits(pc: &PoolClass) -> bool {
    simple_name(&pc.internal_name)
        .chars()
        .all(|c| c.is_ascii_digit())
}

/// Descriptor-param indices of ctor parameters that javac synthesized to
/// carry captures (stored straight into this$*/val$* fields). Their LVT
/// names are often absent (`arg1`), so the name-based skip in
/// emit_method_with misses them — but a LOCAL class's emitted ctor must
/// not declare them (source locals capture lexically).
fn collect_expr_locals(e: &Expr, out: &mut HashSet<u32>) {
    match e {
        Expr::Local { var, .. } => {
            out.insert(*var);
        }
        Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
            args.iter().for_each(|a| collect_expr_locals(a, out));
        }
        Expr::Method { owner, args, .. } => {
            if let Some(o) = owner {
                collect_expr_locals(o, out);
            }
            args.iter().for_each(|a| collect_expr_locals(a, out));
        }
        Expr::Field { owner: Some(o), .. } => collect_expr_locals(o, out),
        Expr::ArrayIndex { array, index } => {
            collect_expr_locals(array, out);
            collect_expr_locals(index, out);
        }
        Expr::Cast { e: i, .. }
        | Expr::InstanceOf { e: i, .. }
        | Expr::Un { e: i, .. }
        | Expr::PreIncDec { e: i, .. }
        | Expr::PostIncDec { e: i, .. } => collect_expr_locals(i, out),
        Expr::Bin { l, r, .. } => {
            collect_expr_locals(l, out);
            collect_expr_locals(r, out);
        }
        Expr::Cond { c, t, f } => {
            collect_expr_locals(c, out);
            collect_expr_locals(t, out);
            collect_expr_locals(f, out);
        }
        Expr::Assign { target, value, .. } => {
            collect_expr_locals(target, out);
            collect_expr_locals(value, out);
        }
        Expr::NewArray { dims, init, .. } => {
            dims.iter().for_each(|d| collect_expr_locals(d, out));
            if let Some(vals) = init {
                vals.iter().for_each(|x| collect_expr_locals(x, out));
            }
        }
        Expr::NewMultiArray { dims, .. } => dims.iter().for_each(|d| collect_expr_locals(d, out)),
        Expr::StringConcat(parts) => parts.iter().for_each(|pp| {
            if let crate::expr::ConcatPart::Str(i) = pp {
                collect_expr_locals(i, out);
            }
        }),
        Expr::Lambda(l) => l.captures.iter().for_each(|c| collect_expr_locals(c, out)),
        Expr::Invokedynamic { args, .. } => args.iter().for_each(|a| collect_expr_locals(a, out)),
        _ => {}
    }
}

fn collect_stmt_locals(st: &Stmt, selfcls: &str, out: &mut HashSet<u32>) {
    match st {
        Stmt::ExprStmt(Expr::Method { name, cls, is_special: true, args, .. })
            if name == "<init>" && cls == selfcls =>
        {
            for a in args {
                match a {
                    Expr::Local { .. } => {}
                    other => collect_expr_locals(other, out),
                }
            }
        }
        Stmt::ExprStmt(e) => collect_expr_locals(e, out),
        Stmt::LocalDef { init: Some(e), .. } => collect_expr_locals(e, out),
        Stmt::Return(Some(e)) => collect_expr_locals(e, out),
        Stmt::Throw(e) => collect_expr_locals(e, out),
        Stmt::Block(v) => v.iter().for_each(|x| collect_stmt_locals(x, selfcls, out)),
        _ => {}
    }
}

/// Indices of ctor params that ONLY ride a this(..) delegation as plain
/// locals: synthesized capture forwards of a delegating local-class ctor
/// (the delegatee stores them into val$ fields). Stripped from the
/// printed signature exactly like direct-store capture params.
fn delegation_forward_params(apc: &PoolClass, mb: &crate::method::MethodBody) -> HashSet<usize> {
    let mut fwd: HashSet<usize> = HashSet::new();
    let deleg = stmt_vec(&mb.body).iter().find_map(|st| match st {
        Stmt::ExprStmt(Expr::Method { name, cls, is_special: true, args, .. })
            if name == "<init>" && cls == &apc.internal_name =>
        {
            Some(args.clone())
        }
        _ => None,
    });
    let Some(dargs) = deleg else { return fwd };
    let mut used_elsewhere: HashSet<u32> = HashSet::new();
    for st in stmt_vec(&mb.body) {
        collect_stmt_locals(&st, &apc.internal_name, &mut used_elsewhere);
    }
    let param_vars: Vec<u32> = mb
        .vt
        .vars
        .iter()
        .filter(|v| v.is_param && v.name != "this")
        .map(|v| v.id)
        .collect();
    for a in &dargs {
        if let Expr::Local { var, .. } = a {
            if used_elsewhere.contains(var) {
                continue;
            }
            if let Some(i) = param_vars.iter().position(|p| p == var) {
                fwd.insert(i);
            }
        }
    }
    fwd
}

fn ctor_capture_params(apc: &PoolClass, mi: usize) -> HashSet<usize> {
    let mut captured: HashSet<usize> = HashSet::new();
    // The CALLER's ctor index: scanning the class's FIRST <init> applied
    // one ctor's capture positions to every sibling (jdk11
    // ClassSpecializer$Factory$1Var: the (int,int) ctor's captures {0,3}
    // skipped `prev` in the (String,Class,Var) ctor, emitting it as
    // `Var arg4` while the body referenced prev — 找不到符号).
    if apc.method_name(mi) != Some("<init>") {
        return captured;
    }
    let Ok(Some(mb)) = decompile_method(apc, empty_pool(), mi) else {
        return captured;
    };
    let mut param_names: Vec<(String, usize)> = Vec::new();
    let mut idx = 0usize;
    for v in &mb.vt.vars {
        if v.is_param && v.name != "this" {
            param_names.push((v.name.clone(), idx));
            idx += 1;
        }
    }
    for st in stmt_vec(&mb.body) {
        if let Stmt::ExprStmt(Expr::Assign { target, value, .. }) = st {
            if let Expr::Field { name: fname, is_static: false, .. } = &*target {
                if fname.starts_with("this$") || fname.starts_with("val$") {
                    if let Expr::Local { var, .. } = &*value {
                        let vname = mb.vt.var(*var).name.clone();
                        if let Some((_, pi)) = param_names.iter().find(|(n, _)| *n == vname) {
                            captured.insert(*pi);
                        }
                    }
                }
            }
        }
    }
    if captured.is_empty() {
        captured.extend(delegation_forward_params(apc, &mb));
    }
    captured
}

fn emit_anon_body(
    apc: &PoolClass,
    pool: &ClassPool,
    fam: &Family,
    captures: &HashMap<String, Expr>,
    out: &mut String,
    indent: usize,
    is_local: bool,
) -> anyhow::Result<()> {
    // Self/mutual instantiation cycles: a local or anonymous class whose
    // methods instantiate it (or a sibling that instantiates it back) must
    // not be inlined recursively. The in-progress emission registers the
    // class name; a re-entry bails and the call site keeps a plain `new`.
    let cyc = EMITTING.with(|e| !e.borrow_mut().insert(apc.internal_name.clone()));
    if cyc {
        anyhow::bail!("cyclic anonymous instantiation of {}", apc.internal_name);
    }
    let _anon_guard = EmitGuard(apc.internal_name.clone());
    ANON_BODY_DEPTH.with(|d| d.set(d.get() + 1));
    let _anon_depth_guard = AnonBodyDepthGuard;
    // Anonymous/local classes have no source constructor: recover field
    // initializers from the generated <init>.
    let is_rec = apc.class_attr("Record").is_some();
    let rec_comps = if is_rec { record_component_names(apc) } else { Vec::new() };
    // LOCAL classes keep their real constructor (emitted below): their
    // field "initializers" are ctor parameter assignments, and folding
    // them onto the fields produces self-references and unresolved
    // parameter names (jdk11 SpinedBuffer$1Splitr: `final int
    // lastSpineIndex = lastSpineIndex;` + `= firstSpineIndex;` with no
    // ctor — 8 "cannot apply ctor" + 2 self-reference errors).
    let mut ctor_inits = if is_local {
        HashMap::new()
    } else {
        anon_field_inits(apc, pool, captures)
    };
    // Field initializers can instantiate anonymous classes (`new X() {...}`
    // shows up as a digit-leading class ref); inline them like method bodies.
    for v in ctor_inits.values_mut() {
        let mut pending: Vec<Stmt> = Vec::new();
        walk_expr_anon(v, apc, pool, fam, &mut pending, &empty_vt());
    }
    // Fields (skip capture/synthetic fields; record components are implicit).
    for (fi, f) in apc.cf.fields.iter().enumerate() {
        let fname = apc.utf8(f.name_index).unwrap_or("").to_string();
        if fname == "$assertionsDisabled" {
            // The inlined body's assert guards print as a bare reference
            // and the enclosing class does not declare the field (jdk17
            // ThreadLocalCoders$1, SpinedBuffer$1Splitr): carry the field
            // into the body. Statics are illegal in inner classes before
            // 16 — instance final computed exactly like javac's clinit.
            let top = apc.internal_name.split('$').next().unwrap_or(&apc.internal_name);
            let top_simple = top.rsplit('/').next().unwrap_or(top);
            out.push_str(&"    ".repeat(indent + 1));
            out.push_str(&format!(
                "final boolean {} = !{}.class.desiredAssertionStatus();\n",
                ASSERT_FIELD, top_simple
            ));
            continue;
        }
        if fname.starts_with("this$")
            || fname.starts_with("val$")
            || f.access_flags.contains(FieldAccessFlags::SYNTHETIC)
            || rec_comps.contains(&fname)
        {
            continue;
        }
        emit_field_init(apc, pool, fi, out, indent + 1, ctor_inits.get(&fname))?;
    }
    // Methods with capture substitution.
    let skip = methods_to_skip(apc, pool, false, is_rec, &ClassOptions::default());
    // Anonymous classes never declare constructors in source; super args
    // ride on the `new Base(args) { ... }` expression itself.
    for mi in 0..apc.cf.methods.len() {
        let name = apc.method_name(mi).unwrap_or("").to_string();
        if name == "<clinit>" || skip.contains(&mi) {
            continue;
        }
        if name == "<init>" && !is_local {
            continue;
        }
        emit_method_with(apc, pool, fam, mi, out, indent + 1, captures)?;
    }
    // Nested classes of the anonymous class.
    for child in fam.direct_children(&apc.internal_name) {
        let Some(npc) = pool.get(&child.name) else { continue };
        emit_class(&npc, pool, &ClassOptions::default(), fam, out, indent + 1, false)?;
    }
    Ok(())
}

/// Snapshot lambda captures of outer locals that are NOT effectively
/// final: the decompiler's hoisted shape (`T x = null;` + reassigns —
/// source assigned `x` once per mutually-exclusive branch, which javac
/// accepts as effectively final) can never be effectively final, so a
/// lambda capturing it fails ("local variables referenced from a lambda
/// must be final or effectively final" — jdk26 ObjectInputFilter.Config
/// createFilter's `patternFilter`, a vP jdk26 blocker). Before the
/// statement containing the lambda, declare `final T x$capN = x;` and
/// record the rename on LambdaExpr::capture_snaps so the printer points
/// the impl body's capture param at the snapshot.
pub(crate) fn fix_lambda_captures(
    s: &mut Stmt,
    vt: &mut crate::varalloc::VarTable,
    pc: &PoolClass,
    pool: &ClassPool,
    fam: &Family,
) {
    let mut assigns: HashMap<u32, usize> = HashMap::new();
    fn count_e(e: &Expr, assigns: &mut HashMap<u32, usize>) {
        match e {
            Expr::Assign { target, value, .. } => {
                if let Expr::Local { var, .. } = &**target {
                    *assigns.entry(*var).or_insert(0) += 1;
                }
                count_e(value, assigns);
            }
            Expr::PreIncDec { e: i, .. } | Expr::PostIncDec { e: i, .. } => {
                if let Expr::Local { var, .. } = &**i {
                    *assigns.entry(*var).or_insert(0) += 1;
                }
                count_e(i, assigns);
            }
            Expr::Method { owner, args, .. } => {
                if let Some(o) = owner {
                    count_e(o, assigns);
                }
                args.iter().for_each(|a| count_e(a, assigns));
            }
            Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
                args.iter().for_each(|a| count_e(a, assigns))
            }
            Expr::Field { owner: Some(o), .. } => count_e(o, assigns),
            Expr::ArrayIndex { array, index } => {
                count_e(array, assigns);
                count_e(index, assigns);
            }
            Expr::Cast { e: i, .. } | Expr::InstanceOf { e: i, .. } | Expr::Un { e: i, .. } => count_e(i, assigns),
            Expr::Bin { l, r, .. } => {
                count_e(l, assigns);
                count_e(r, assigns);
            }
            Expr::Cond { c, t, f } => {
                count_e(c, assigns);
                count_e(t, assigns);
                count_e(f, assigns);
            }
            Expr::NewArray { dims, init, .. } => {
                dims.iter().for_each(|d| count_e(d, assigns));
                if let Some(vals) = init {
                    vals.iter().for_each(|v| count_e(v, assigns));
                }
            }
            Expr::StringConcat(parts) => parts.iter().for_each(|p| {
                if let crate::expr::ConcatPart::Str(i) = p {
                    count_e(i, assigns);
                }
            }),
            Expr::Lambda(l) => l.captures.iter().for_each(|c| count_e(c, assigns)),
            Expr::Invokedynamic { args, .. } => args.iter().for_each(|a| count_e(a, assigns)),
            _ => {}
        }
    }
    fn count_s(st: &Stmt, assigns: &mut HashMap<u32, usize>) {
        match st {
            Stmt::Block(v) => v.iter().for_each(|x| count_s(x, assigns)),
            Stmt::ExprStmt(e) => count_e(e, assigns),
            Stmt::LocalDef { var, init, .. } => {
                if init.is_some() {
                    *assigns.entry(*var).or_insert(0) += 1;
                }
                if let Some(e) = init {
                    count_e(e, assigns);
                }
            }
            Stmt::Return(e) => {
                if let Some(x) = e {
                    count_e(x, assigns);
                }
            }
            Stmt::Throw(e) => count_e(e, assigns),
            Stmt::If { cond, then_stmt, else_stmt } => {
                count_e(cond, assigns);
                count_s(then_stmt, assigns);
                if let Some(x) = else_stmt {
                    count_s(x, assigns);
                }
            }
            Stmt::While { cond, body } => {
                count_e(cond, assigns);
                count_s(body, assigns);
            }
            Stmt::DoWhile { body, cond } => {
                count_s(body, assigns);
                count_e(cond, assigns);
            }
            Stmt::For { init, cond, update, body } => {
                init.iter().for_each(|i| count_s(i, assigns));
                if let Some(c) = cond {
                    count_e(c, assigns);
                }
                update.iter().for_each(|u| count_e(u, assigns));
                count_s(body, assigns);
            }
            Stmt::ForEach { iterable, body, .. } => {
                count_e(iterable, assigns);
                count_s(body, assigns);
            }
            Stmt::Switch { selector, cases, default, .. } => {
                count_e(selector, assigns);
                for c in cases {
                    c.body.iter().for_each(|st| count_s(st, assigns));
                }
                if let Some(d) = default {
                    count_s(d, assigns);
                }
            }
            Stmt::Try { body, catches, finally } => {
                count_s(body, assigns);
                for c in catches {
                    count_s(&c.body, assigns);
                }
                if let Some(f) = finally {
                    count_s(f, assigns);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                resources.iter().for_each(|r| count_s(r, assigns));
                count_s(body, assigns);
                for c in catches {
                    count_s(&c.body, assigns);
                }
                if let Some(f) = finally {
                    count_s(f, assigns);
                }
            }
            Stmt::Synchronized { lock, body } => {
                count_e(lock, assigns);
                count_s(body, assigns);
            }
            Stmt::Labeled { body, .. } => count_s(body, assigns),
            _ => {}
        }
    }
    count_s(s, &mut assigns);
    let multi: HashSet<u32> = assigns
        .iter()
        .filter(|(_, &n)| n >= 2)
        .map(|(&v, _)| v)
        .collect();
    if multi.is_empty() && fam.locals.is_empty() {
        return;
    }
    let mut counter = 0usize;
    fn lambda_snaps(
        e: &mut Expr,
        vt: &mut crate::varalloc::VarTable,
        pc: &PoolClass,
        pool: &ClassPool,
        fam: &Family,
        multi: &HashSet<u32>,
        counter: &mut usize,
        defs: &mut Vec<Stmt>,
    ) {
        if let Expr::Lambda(l) = e {
            if let Some(mi) = pc.find_own_method(&l.impl_name, &l.impl_desc.to_string()) {
                if let Ok(Some(mb)) = decompile_method(pc, pool, mi) {
                    // Local classes instantiated INSIDE the lambda body
                    // must be declared in the OUTER method (sibling
                    // method refs like `FixedWindow::finish` cannot see
                    // into the lambda scope; jdk26 Gatherers). Extract
                    // their decls from a throwaway walk of the impl body
                    // and register the names so the print-time walk
                    // inside the lambda body skips re-declaring.
                    if !fam.locals.is_empty() && ANON_BODY_DEPTH.with(|d| d.get()) == 0 {
                        let mut retained: HashSet<String> = HashSet::new();
                        let mark = LOCAL_DECL_HOIST.with(|h| h.borrow().len());
                        let mut cb = mb.body.clone();
                        let mut p2: Vec<Stmt> = Vec::new();
                        let mut d2: HashSet<String> = HashSet::new();
                        {
                            ANON_BODY_DEPTH.with(|d| d.set(d.get() + 1));
                            let _depth = AnonBodyDepthGuard;
                            let _capture = LOCAL_DECL_SITES.with(|c| c.borrow_mut().take());
                            LOCAL_DECL_SITES.with(|c| *c.borrow_mut() = Some(Vec::new()));
                            walk_stmt_anon(&mut cb, pc, pool, fam, &mut p2, &mb.vt, &mut d2);
                            // Capture local names whose decls live inside
                            // the lambda body and whose captures are lambda
                            // params (jdk26 Gatherers.map's `class Box`
                            // captures the lambda param b — hoisting it to
                            // the method top puts it out of scope).
                            let sites: Vec<String> = LOCAL_DECL_SITES
                                .with(|c| c.borrow_mut().take().unwrap_or_default());
                            let captured_params: HashSet<String> = mb
                                .vt
                                .vars
                                .iter()
                                .filter(|v| v.is_param && v.name != "this")
                                .map(|v| v.name.clone())
                                .collect();
                            for name in sites {
                                if let Some((_, nc)) = fam
                                    .nested
                                    .iter()
                                    .find(|(_, nc)| nc.simple == name)
                                {
                                    if let Some(lpc) = pool.get(&nc.name) {
                                        if lpc
                                            .cf
                                            .fields
                                            .iter()
                                            .filter_map(|f| {
                                                lpc.utf8(f.name_index)
                                                    .and_then(|n| n.strip_prefix("val$"))
                                                    .map(|x| x.to_string())
                                            })
                                            .any(|cn| captured_params.contains(&cn))
                                        {
                                            // Keep the decl INSIDE the lambda
                                            // body (print-time walk redeclares
                                            // it); do NOT register in
                                            // EXTERN_DECL and drop it from the
                                            // extraction below.
                                            retained.insert(name);
                                        }
                                    }
                                }
                            }
                            LOCAL_DECL_SITES.with(|c| *c.borrow_mut() = None);
                        }
                        let mut extracted: Vec<(String, Stmt)> = Vec::new();
                        fn pull(v: &mut Vec<Stmt>, out: &mut Vec<(String, Stmt)>) {
                            let mut i = 0;
                            while i < v.len() {
                                if let Stmt::ClassDecl { name, .. } = &v[i] {
                                    out.push((name.clone(), v.remove(i)));
                                    continue;
                                }
                                if let Stmt::Block(inner) = &mut v[i] {
                                    pull(inner, out);
                                }
                                i += 1;
                            }
                        }
                        pull(&mut p2, &mut extracted);
                        if let Stmt::Block(bv) = &mut cb {
                            pull(bv, &mut extracted);
                        }
                        let stacked: Vec<(String, Stmt)> = LOCAL_DECL_HOIST.with(|h| {
                            let mut h = h.borrow_mut();
                            if h.len() > mark {
                                h.drain(mark..).collect()
                            } else {
                                Vec::new()
                            }
                        });
                        extracted.extend(stacked);
                        if !extracted.is_empty() {
                            let already: HashSet<String> = EXTERN_DECL.with(|x| x.borrow().clone());
                            let fresh: Vec<(String, Stmt)> = extracted
                                .into_iter()
                                .filter(|(n, _)| !already.contains(n) && !retained.contains(n))
                                .collect();
                            if !fresh.is_empty() {
                                EXTERN_DECL.with(|x| {
                                    let mut x = x.borrow_mut();
                                    for (n, _) in &fresh {
                                        x.insert(n.clone());
                                    }
                                });
                                defs.extend(fresh.into_iter().map(|(_, d)| d));
                            }
                        }
                    }
                    let sam_n = l.param_names.len();
                    let impl_params: Vec<(u32, String)> = mb
                        .vt
                        .vars
                        .iter()
                        .filter(|v| v.is_param && v.name != "this")
                        .map(|v| (v.id, v.name.clone()))
                        .collect();
                    let n_cap = impl_params.len().saturating_sub(sam_n);
                    // Match captures positionally (impl-arg order); the
                    // impl LVT often lacks names for synthetic lambda
                    // params, so name matching against the outer var is
                    // unreliable.
                    let mut snaps: Vec<(u32, u32)> = Vec::new();
                    for (k, cap) in l.captures.iter().enumerate().take(n_cap) {
                        if let Expr::Local { var: ovid, .. } = cap {
                            if multi.contains(ovid) {
                                if let Some((pid, _)) = impl_params.get(k) {
                                    snaps.push((*ovid, *pid));
                                }
                            }
                        }
                    }
                    for (ovid, pid) in snaps {
                        let pname = vt.var(ovid).name.clone();
                        let snap = format!("{}$cap{}", pname, counter);
                        *counter += 1;
                        let ty = vt.var(ovid).ty.clone();
                        let newid = vt.vars.len() as u32;
                        vt.vars.push(crate::varalloc::VarInfo {
                            id: newid,
                            slot: u16::MAX,
                            name: snap.clone(),
                            ty,
                            is_param: false,
                            range_start: 0,
                            range_end: u16::MAX,
                            synthetic_name: true,
                        });
                        l.capture_snaps.push((ovid, pid, snap.clone()));
                        defs.push(Stmt::LocalDef {
                            var: newid,
                            init: Some(Expr::Local { var: ovid, ty: vt.var(ovid).ty.clone() }),
                            is_final: true,
                            force_type: false,
                        });
                    }
                }
            }
        }
        // recurse (captures of nested lambdas too)
        match e {
            Expr::Lambda(l) => l.captures.iter_mut().for_each(|c| {
                lambda_snaps(c, vt, pc, pool, fam, multi, counter, defs)
            }),
            Expr::Method { owner, args, .. } => {
                if let Some(o) = owner {
                    lambda_snaps(o, vt, pc, pool, fam, multi, counter, defs);
                }
                args.iter_mut().for_each(|a| lambda_snaps(a, vt, pc, pool, fam, multi, counter, defs));
            }
            Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
                args.iter_mut().for_each(|a| lambda_snaps(a, vt, pc, pool, fam, multi, counter, defs));
            }
            Expr::Field { owner: Some(o), .. } => lambda_snaps(o, vt, pc, pool, fam, multi, counter, defs),
            Expr::ArrayIndex { array, index } => {
                lambda_snaps(array, vt, pc, pool, fam, multi, counter, defs);
                lambda_snaps(index, vt, pc, pool, fam, multi, counter, defs);
            }
            Expr::Cast { e: i, .. } | Expr::InstanceOf { e: i, .. } | Expr::Un { e: i, .. }
            | Expr::PreIncDec { e: i, .. } | Expr::PostIncDec { e: i, .. } => {
                lambda_snaps(i, vt, pc, pool, fam, multi, counter, defs)
            }
            Expr::Bin { l: bl, r, .. } => {
                lambda_snaps(bl, vt, pc, pool, fam, multi, counter, defs);
                lambda_snaps(r, vt, pc, pool, fam, multi, counter, defs);
            }
            Expr::Cond { c, t, f } => {
                lambda_snaps(c, vt, pc, pool, fam, multi, counter, defs);
                lambda_snaps(t, vt, pc, pool, fam, multi, counter, defs);
                lambda_snaps(f, vt, pc, pool, fam, multi, counter, defs);
            }
            Expr::Assign { target, value, .. } => {
                lambda_snaps(target, vt, pc, pool, fam, multi, counter, defs);
                lambda_snaps(value, vt, pc, pool, fam, multi, counter, defs);
            }
            Expr::NewArray { dims, init, .. } => {
                dims.iter_mut().for_each(|d| lambda_snaps(d, vt, pc, pool, fam, multi, counter, defs));
                if let Some(vals) = init {
                    vals.iter_mut().for_each(|v| lambda_snaps(v, vt, pc, pool, fam, multi, counter, defs));
                }
            }
            Expr::StringConcat(parts) => parts.iter_mut().for_each(|p| {
                if let crate::expr::ConcatPart::Str(i) = p {
                    lambda_snaps(i, vt, pc, pool, fam, multi, counter, defs);
                }
            }),
            Expr::Invokedynamic { args, .. } => {
                args.iter_mut().for_each(|a| lambda_snaps(a, vt, pc, pool, fam, multi, counter, defs));
            }
            _ => {}
        }
    }
    fn fix_stmt(
        s: &mut Stmt,
        vt: &mut crate::varalloc::VarTable,
        pc: &PoolClass,
        pool: &ClassPool,
        fam: &Family,
        multi: &HashSet<u32>,
        counter: &mut usize,
    ) {
        // Leaf statements: process their expressions; when snapshots are
        // needed, wrap self in a Block with the decls preceding.
        macro_rules! leaf {
            ($e:expr) => {{
                let mut defs: Vec<Stmt> = Vec::new();
                lambda_snaps($e, vt, pc, pool, fam, multi, counter, &mut defs);
                if !defs.is_empty() {
                    let old = std::mem::replace(s, Stmt::Block(vec![]));
                    defs.push(old);
                    *s = Stmt::Block(defs);
                }
                return;
            }};
        }
        match s {
            Stmt::ExprStmt(e) => leaf!(e),
            Stmt::LocalDef { init: Some(e), .. } => leaf!(e),
            Stmt::Return(Some(e)) => leaf!(e),
            Stmt::Throw(e) => leaf!(e),
            Stmt::If { cond, then_stmt, else_stmt } => {
                let mut defs: Vec<Stmt> = Vec::new();
                lambda_snaps(cond, vt, pc, pool, fam, multi, counter, &mut defs);
                fix_stmt(then_stmt, vt, pc, pool, fam, multi, counter);
                if let Some(x) = else_stmt {
                    fix_stmt(x, vt, pc, pool, fam, multi, counter);
                }
                if !defs.is_empty() {
                    let old = std::mem::replace(s, Stmt::Block(vec![]));
                    defs.push(old);
                    *s = Stmt::Block(defs);
                }
            }
            Stmt::While { cond, body } => {
                let mut defs: Vec<Stmt> = Vec::new();
                lambda_snaps(cond, vt, pc, pool, fam, multi, counter, &mut defs);
                fix_stmt(body, vt, pc, pool, fam, multi, counter);
                if !defs.is_empty() {
                    let old = std::mem::replace(s, Stmt::Block(vec![]));
                    defs.push(old);
                    *s = Stmt::Block(defs);
                }
            }
            Stmt::DoWhile { body, cond } => {
                fix_stmt(body, vt, pc, pool, fam, multi, counter);
                let mut defs: Vec<Stmt> = Vec::new();
                lambda_snaps(cond, vt, pc, pool, fam, multi, counter, &mut defs);
                if !defs.is_empty() {
                    let old = std::mem::replace(s, Stmt::Block(vec![]));
                    defs.push(old);
                    *s = Stmt::Block(defs);
                }
            }
            Stmt::For { init, cond, update, body } => {
                for i in init.iter_mut() {
                    fix_stmt(i, vt, pc, pool, fam, multi, counter);
                }
                let mut defs: Vec<Stmt> = Vec::new();
                if let Some(c) = cond {
                    lambda_snaps(c, vt, pc, pool, fam, multi, counter, &mut defs);
                }
                for u in update.iter_mut() {
                    lambda_snaps(u, vt, pc, pool, fam, multi, counter, &mut defs);
                }
                fix_stmt(body, vt, pc, pool, fam, multi, counter);
                if !defs.is_empty() {
                    let old = std::mem::replace(s, Stmt::Block(vec![]));
                    defs.push(old);
                    *s = Stmt::Block(defs);
                }
            }
            Stmt::ForEach { iterable, body, .. } => {
                let mut defs: Vec<Stmt> = Vec::new();
                lambda_snaps(iterable, vt, pc, pool, fam, multi, counter, &mut defs);
                fix_stmt(body, vt, pc, pool, fam, multi, counter);
                if !defs.is_empty() {
                    let old = std::mem::replace(s, Stmt::Block(vec![]));
                    defs.push(old);
                    *s = Stmt::Block(defs);
                }
            }
            Stmt::Switch { selector, cases, default, .. } => {
                let mut defs: Vec<Stmt> = Vec::new();
                lambda_snaps(selector, vt, pc, pool, fam, multi, counter, &mut defs);
                for c in cases.iter_mut() {
                    for st in c.body.iter_mut() {
                        fix_stmt(st, vt, pc, pool, fam, multi, counter);
                    }
                }
                if let Some(d) = default {
                    fix_stmt(d, vt, pc, pool, fam, multi, counter);
                }
                if !defs.is_empty() {
                    let old = std::mem::replace(s, Stmt::Block(vec![]));
                    defs.push(old);
                    *s = Stmt::Block(defs);
                }
            }
            Stmt::Try { body, catches, finally } => {
                fix_stmt(body, vt, pc, pool, fam, multi, counter);
                for c in catches.iter_mut() {
                    fix_stmt(&mut c.body, vt, pc, pool, fam, multi, counter);
                }
                if let Some(f) = finally {
                    fix_stmt(f, vt, pc, pool, fam, multi, counter);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                for r in resources.iter_mut() {
                    fix_stmt(r, vt, pc, pool, fam, multi, counter);
                }
                fix_stmt(body, vt, pc, pool, fam, multi, counter);
                for c in catches.iter_mut() {
                    fix_stmt(&mut c.body, vt, pc, pool, fam, multi, counter);
                }
                if let Some(f) = finally {
                    fix_stmt(f, vt, pc, pool, fam, multi, counter);
                }
            }
            Stmt::Synchronized { lock, body } => {
                let mut defs: Vec<Stmt> = Vec::new();
                lambda_snaps(lock, vt, pc, pool, fam, multi, counter, &mut defs);
                fix_stmt(body, vt, pc, pool, fam, multi, counter);
                if !defs.is_empty() {
                    let old = std::mem::replace(s, Stmt::Block(vec![]));
                    defs.push(old);
                    *s = Stmt::Block(defs);
                }
            }
            Stmt::Labeled { body, .. } => fix_stmt(body, vt, pc, pool, fam, multi, counter),
            Stmt::Block(v) => {
                for x in v.iter_mut() {
                    fix_stmt(x, vt, pc, pool, fam, multi, counter);
                }
            }
            _ => {}
        }
    }
    let redecl_save = EXTERN_REDECL.with(|r| std::mem::take(&mut *r.borrow_mut()));
    fix_stmt(s, vt, pc, pool, fam, &multi, &mut counter);
    let collected = EXTERN_REDECL.with(|r| std::mem::take(&mut *r.borrow_mut()));
    EXTERN_REDECL.with(|r| *r.borrow_mut() = redecl_save);
    if !collected.is_empty() {
        relocate_multi_site_decls(s, &collected, fam, pool, vt);
    }
}

/// Move local-class decls mentioned at several statements of one method
/// to the method-top block, after the leading hoisted local definitions
/// (their substituted capture expressions reference those locals; jcdc
/// hoists every local decl to the block head, so top placement keeps
/// captures in scope) and before every statement — dominating all
/// mention sites wherever they sit.
fn relocate_multi_site_decls(
    s: &mut Stmt,
    names: &HashSet<String>,
    fam: &Family,
    pool: &ClassPool,
    vt: &VarTable,
) {
    fn pull(v: &mut Vec<Stmt>, names: &HashSet<String>, out: &mut Vec<Stmt>) {
        let mut i = 0;
        while i < v.len() {
            if let Stmt::ClassDecl { name, .. } = &v[i] {
                if names.contains(name) {
                    out.push(v.remove(i));
                    continue;
                }
            }
            pull_one(&mut v[i], names, out);
            i += 1;
        }
    }
    fn pull_one(s: &mut Stmt, names: &HashSet<String>, out: &mut Vec<Stmt>) {
        match s {
            Stmt::Block(v) => pull(v, names, out),
            Stmt::If { then_stmt, else_stmt, .. } => {
                pull_one(then_stmt, names, out);
                if let Some(e) = else_stmt {
                    pull_one(e, names, out);
                }
            }
            Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => pull_one(body, names, out),
            Stmt::For { init, body, .. } => {
                init.iter_mut().for_each(|x| pull_one(x, names, out));
                pull_one(body, names, out);
            }
            Stmt::ForEach { body, .. } => pull_one(body, names, out),
            Stmt::Labeled { body, .. } => pull_one(body, names, out),
            Stmt::Synchronized { body, .. } => pull_one(body, names, out),
            Stmt::Switch { cases, default, .. } => {
                for c in cases.iter_mut() {
                    c.body.iter_mut().for_each(|x| pull_one(x, names, out));
                }
                if let Some(d) = default {
                    pull_one(d, names, out);
                }
            }
            Stmt::Try { body, catches, finally } => {
                pull_one(body, names, out);
                for c in catches.iter_mut() {
                    pull_one(&mut c.body, names, out);
                }
                if let Some(f) = finally {
                    pull_one(f, names, out);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                for r in resources.iter_mut() {
                    pull_one(r, names, out);
                }
                pull_one(body, names, out);
                for c in catches.iter_mut() {
                    pull_one(&mut c.body, names, out);
                }
                if let Some(f) = finally {
                    pull_one(f, names, out);
                }
            }
            _ => {}
        }
    }
    let Stmt::Block(v) = s else { return };
    let mut moved = Vec::new();
    pull(v, names, &mut moved);
    if moved.is_empty() {
        return;
    }
    // A local class only sees outer locals DEFINED before it: land the
    // moved decl after the last definition of any captured local (jdk17
    // Collectors.teeing0: PairBox captures c1Supplier..merger defined
    // mid-method — a leading-slot insert put the decl before them,
    // "找不到符号 变量 c1Supplier 位置: 类 PairBox"). Null-initialized
    // hoisted decls are placeholders, not definitions.
    let mut pos = 0;
    while pos < v.len() && matches!(&v[pos], Stmt::ClassDecl { .. }) {
        pos += 1;
    }
    for name in names {
        let caps = local_class_captures(name, fam, pool);
        if caps.is_empty() {
            continue;
        }
        let defines = |st: &Stmt| -> bool {
            match st {
                Stmt::LocalDef { var, init, .. } => {
                    init.as_ref()
                        .map(|e| !matches!(e, Expr::Const(crate::expr::ConstVal::Null)))
                        .unwrap_or(true)
                        && caps.iter().any(|n| vt.var(*var).name == *n)
                }
                Stmt::ExprStmt(Expr::Assign { target, .. }) => {
                    matches!(&**target, Expr::Local { var, .. }
                        if caps.iter().any(|n| vt.var(*var).name == *n))
                }
                _ => false,
            }
        };
        if let Some(p) = v.iter().rposition(defines) {
            pos = std::cmp::max(pos, p + 1);
        }
    }
    for (k, d) in moved.into_iter().enumerate() {
        v.insert(pos + k, d);
    }
}

/// Map this$N fields of a member inner class to `Outer.this` raw exprs.
fn outer_this_map(pc: &PoolClass) -> HashMap<String, Expr> {
    let mut m = HashMap::new();
    for f in &pc.cf.fields {
        if let Some(name) = pc.utf8(f.name_index) {
            if name.starts_with("this$") {
                if let Some(desc) = pc.utf8(f.descriptor_index) {
                    if let Some(inner) = desc.strip_prefix('L').and_then(|d| d.strip_suffix(';')) {
                        let sn = simple_name(inner);
                        // An anonymous outer class has no source name; the
                        // emitted body is inlined, so plain `this` (or the
                        // enclosing scope) denotes the same instance.
                        let starts_digit = sn
                            .chars()
                            .next()
                            .map(|c| c.is_ascii_digit())
                            .unwrap_or(false);
                        let rep = if starts_digit {
                            Expr::This
                        } else {
                            Expr::Raw(format!("{}.this", qualified_this_tail(inner)))
                        };
                        m.insert(name.to_string(), rep);
                    }
                }
            }
        }
    }
    m
}

/// Replace reads of captured synthetic fields with the captured expressions.
/// True when the method's bytecode instantiates or constructs one of the
/// owner's inner classes (`Owner$...`) — such classes capture enclosing
/// locals, which Java <= 7 requires to be declared `final`.
fn method_builds_inner(pc: &PoolClass, mi: usize) -> bool {
    use jcdc_classfile::instruction::{decode_all, Opcode};
    let Some(code) = crate::varalloc::code_attribute(pc, mi) else {
        return false;
    };
    let prefix = format!("{}$", pc.internal_name);
    for ins in decode_all(&code.code) {
        match ins.op {
            Opcode::New => {
                if let Some(c) = pc.class_name(ins.a as u16) {
                    if c.starts_with(&prefix) {
                        return true;
                    }
                }
            }
            Opcode::Invokespecial => {
                if let Some((c, n, _)) = pc.member_ref(ins.a as u16) {
                    if n == "<init>" && c.starts_with(&prefix) {
                        return true;
                    }
                }
            }
            _ => {}
        }
    }
    false
}

/// Mark locals captured by inner/anonymous class constructors as `final`
/// (Java <= 7 compilation requirement).
fn finalize_captured_locals(s: &mut Stmt, owner_internal: &str) {
    let mut vars: HashSet<u32> = HashSet::new();
    let prefix = format!("{}$", owner_internal);
    collect_captured_stmt(s, &prefix, &mut vars);
    if vars.is_empty() {
        return;
    }
    mark_final_stmt(s, &vars);
}

fn collect_captured_expr(e: &Expr, prefix: &str, vars: &mut HashSet<u32>) {
    let grab_locals = |args: &[Expr], vars: &mut HashSet<u32>| {
        for a in args {
            collect_locals_in(a, vars);
        }
    };
    match e {
        Expr::Method { cls, name, args, .. } if name == "<init>" && cls.starts_with(prefix) => {
            grab_locals(args, vars);
        }
        Expr::AnonNew { args, .. } => grab_locals(args, vars),
        Expr::New { args, .. } => args.iter().for_each(|a| collect_captured_expr(a, prefix, vars)),
        Expr::Method { owner, args, .. } => {
            if let Some(o) = owner {
                collect_captured_expr(o, prefix, vars);
            }
            args.iter().for_each(|a| collect_captured_expr(a, prefix, vars));
        }
        Expr::Bin { l, r, .. } | Expr::Assign { target: l, value: r, .. } => {
            collect_captured_expr(l, prefix, vars);
            collect_captured_expr(r, prefix, vars);
        }
        Expr::Cond { c, t, f } => {
            collect_captured_expr(c, prefix, vars);
            collect_captured_expr(t, prefix, vars);
            collect_captured_expr(f, prefix, vars);
        }
        Expr::Un { e: x, .. }
        | Expr::Cast { e: x, .. }
        | Expr::InstanceOf { e: x, .. }
        | Expr::PreIncDec { e: x, .. }
        | Expr::PostIncDec { e: x, .. } => collect_captured_expr(x, prefix, vars),
        Expr::ArrayIndex { array, index } => {
            collect_captured_expr(array, prefix, vars);
            collect_captured_expr(index, prefix, vars);
        }
        Expr::Field { owner: Some(o), .. } => collect_captured_expr(o, prefix, vars),
        Expr::NewArray { dims, init, .. } => {
            dims.iter().for_each(|d| collect_captured_expr(d, prefix, vars));
            if let Some(vals) = init {
                vals.iter().for_each(|v| collect_captured_expr(v, prefix, vars));
            }
        }
        Expr::StringConcat(parts) => parts.iter().for_each(|p| {
            if let crate::expr::ConcatPart::Str(x) = p {
                collect_captured_expr(x, prefix, vars);
            }
        }),
        _ => {}
    }
}

fn collect_locals_in(e: &Expr, vars: &mut HashSet<u32>) {
    match e {
        Expr::Local { var, .. } => {
            vars.insert(*var);
        }
        Expr::Cast { e: x, .. } | Expr::Un { e: x, .. } => collect_locals_in(x, vars),
        _ => {}
    }
}

fn collect_captured_stmt(s: &Stmt, prefix: &str, vars: &mut HashSet<u32>) {
    match s {
        Stmt::Block(v) => v.iter().for_each(|x| collect_captured_stmt(x, prefix, vars)),
        Stmt::ExprStmt(e) => collect_captured_expr(e, prefix, vars),
        Stmt::LocalDef { init: Some(e), .. } => collect_captured_expr(e, prefix, vars),
        Stmt::Return(Some(e)) | Stmt::Throw(e) => collect_captured_expr(e, prefix, vars),
        Stmt::If { cond, then_stmt, else_stmt } => {
            collect_captured_expr(cond, prefix, vars);
            collect_captured_stmt(then_stmt, prefix, vars);
            if let Some(e) = else_stmt {
                collect_captured_stmt(e, prefix, vars);
            }
        }
        Stmt::While { cond, body } | Stmt::DoWhile { cond, body } => {
            collect_captured_expr(cond, prefix, vars);
            collect_captured_stmt(body, prefix, vars);
        }
        Stmt::For { init, cond, update, body } => {
            init.iter().for_each(|i| collect_captured_stmt(i, prefix, vars));
            if let Some(c) = cond {
                collect_captured_expr(c, prefix, vars);
            }
            update.iter().for_each(|u| collect_captured_expr(u, prefix, vars));
            collect_captured_stmt(body, prefix, vars);
        }
        Stmt::Switch { selector, cases, default, .. } => {
            collect_captured_expr(selector, prefix, vars);
            for c in cases {
                c.body.iter().for_each(|st| collect_captured_stmt(st, prefix, vars));
            }
            if let Some(d) = default {
                collect_captured_stmt(d, prefix, vars);
            }
        }
        Stmt::Try { body, catches, finally } => {
            collect_captured_stmt(body, prefix, vars);
            for c in catches {
                collect_captured_stmt(&c.body, prefix, vars);
            }
            if let Some(f) = finally {
                collect_captured_stmt(f, prefix, vars);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter() { collect_captured_stmt(res, prefix, vars); }
            collect_captured_stmt(body, prefix, vars);
            for c in catches {
                collect_captured_stmt(&c.body, prefix, vars);
            }
            if let Some(f) = finally {
                collect_captured_stmt(f, prefix, vars);
            }
        }
        Stmt::Synchronized { lock, body } => {
            collect_captured_expr(lock, prefix, vars);
            collect_captured_stmt(body, prefix, vars);
        }
        _ => {}
    }
}

fn mark_final_stmt(s: &mut Stmt, vars: &HashSet<u32>) {
    match s {
        Stmt::Block(v) => v.iter_mut().for_each(|x| mark_final_stmt(x, vars)),
        Stmt::LocalDef { var, is_final, .. } if vars.contains(var) => *is_final = true,
        Stmt::If { then_stmt, else_stmt, .. } => {
            mark_final_stmt(then_stmt, vars);
            if let Some(e) = else_stmt {
                mark_final_stmt(e, vars);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => mark_final_stmt(body, vars),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(|i| mark_final_stmt(i, vars));
            mark_final_stmt(body, vars);
        }
        Stmt::Try { body, catches, finally } => {
            mark_final_stmt(body, vars);
            for c in catches {
                mark_final_stmt(&mut c.body, vars);
            }
            if let Some(f) = finally {
                mark_final_stmt(f, vars);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { mark_final_stmt(res, vars); }
            mark_final_stmt(body, vars);
            for c in catches {
                mark_final_stmt(&mut c.body, vars);
            }
            if let Some(f) = finally {
                mark_final_stmt(f, vars);
            }
        }
        _ => {}
    }
}

fn substitute_captures(s: &mut Stmt, captures: &HashMap<String, Expr>, pool: &ClassPool) {
    if captures.is_empty() {
        return;
    }
    walk_stmt_subst(s, captures, pool);
}

fn walk_stmt_subst(s: &mut Stmt, caps: &HashMap<String, Expr>, pool: &ClassPool) {
    match s {
        Stmt::Block(v) => v.iter_mut().for_each(|x| walk_stmt_subst(x, caps, pool)),
        Stmt::ExprStmt(e) => walk_expr_subst(e, caps, pool),
        Stmt::LocalDef { init: Some(e), .. } => walk_expr_subst(e, caps, pool),
        Stmt::Return(Some(e)) | Stmt::Throw(e) => walk_expr_subst(e, caps, pool),
        Stmt::If { cond, then_stmt, else_stmt } => {
            walk_expr_subst(cond, caps, pool);
            walk_stmt_subst(then_stmt, caps, pool);
            if let Some(e) = else_stmt {
                walk_stmt_subst(e, caps, pool);
            }
        }
        Stmt::While { cond, body } => {
            walk_expr_subst(cond, caps, pool);
            walk_stmt_subst(body, caps, pool);
        }
        Stmt::DoWhile { body, cond } => {
            walk_stmt_subst(body, caps, pool);
            walk_expr_subst(cond, caps, pool);
        }
        Stmt::For { init, cond, update, body } => {
            init.iter_mut().for_each(|i| walk_stmt_subst(i, caps, pool));
            if let Some(c) = cond {
                walk_expr_subst(c, caps, pool);
            }
            update.iter_mut().for_each(|u| walk_expr_subst(u, caps, pool));
            walk_stmt_subst(body, caps, pool);
        }
        Stmt::ForEach { iterable, body, .. } => {
            walk_expr_subst(iterable, caps, pool);
            walk_stmt_subst(body, caps, pool);
        }
        Stmt::Switch { selector, cases, default, .. } => {
            walk_expr_subst(selector, caps, pool);
            for c in cases {
                c.body.iter_mut().for_each(|st| walk_stmt_subst(st, caps, pool));
            }
            if let Some(d) = default {
                walk_stmt_subst(d, caps, pool);
            }
        }
        Stmt::Try { body, catches, finally } => {
            walk_stmt_subst(body, caps, pool);
            for c in catches {
                walk_stmt_subst(&mut c.body, caps, pool);
            }
            if let Some(f) = finally {
                walk_stmt_subst(f, caps, pool);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { walk_stmt_subst(res, caps, pool); }
            walk_stmt_subst(body, caps, pool);
            for c in catches {
                walk_stmt_subst(&mut c.body, caps, pool);
            }
            if let Some(f) = finally {
                walk_stmt_subst(f, caps, pool);
            }
        }
        Stmt::Synchronized { lock, body } => {
            walk_expr_subst(lock, caps, pool);
            walk_stmt_subst(body, caps, pool);
        }
        // Coverage gaps: a Labeled body (SESE/walk label emission wraps
        // loops — sun KQueuePort$EventHandlerTask.poll's `L1: do {..}`
        // kept raw `this.this$0.kqfd` reads, symbol not found) and the
        // value/monitor forms.
        Stmt::Labeled { body, .. } => walk_stmt_subst(body, caps, pool),
        Stmt::Assert { cond, msg } => {
            walk_expr_subst(cond, caps, pool);
            if let Some(m) = msg {
                walk_expr_subst(m, caps, pool);
            }
        }
        Stmt::TernaryValue { e } => walk_expr_subst(e, caps, pool),
        Stmt::MonitorEnter(e) | Stmt::MonitorExit(e) => walk_expr_subst(e, caps, pool),
        _ => {}
    }
}

fn walk_expr_subst(e: &mut Expr, caps: &HashMap<String, Expr>, pool: &ClassPool) {
    // `anonOuter.this$N` chains: resolve against the owner class before
    // the generic recursion rewrites the owner to `this`.
    if let Expr::Field { name, is_static: false, .. } = &*e {
        if name.starts_with("this$") {
            if let Some(r) = collapse_this_chain(e, pool) {
                *e = Expr::Raw(r);
                return;
            }
        }
    }
    if let Expr::Field { name, is_static: false, owner, .. } = e {
        let owner_is_this = match owner {
            None => true,
            Some(o) => matches!(&**o, Expr::This),
        };
        if owner_is_this {
            if let Some(rep) = caps.get(name.as_str()) {
                *e = rep.clone();
                return;
            }
            if name.starts_with("this$") {
                *e = Expr::This;
                return;
            }
        }
    }
    match e {
        Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
            args.iter_mut().for_each(|a| walk_expr_subst(a, caps, pool))
        }
        Expr::Method { owner, args, .. } => {
            if let Some(o) = owner {
                walk_expr_subst(o, caps, pool);
            }
            args.iter_mut().for_each(|a| walk_expr_subst(a, caps, pool));
        }
        Expr::Field { owner: Some(o), .. } => walk_expr_subst(o, caps, pool),
        Expr::ArrayIndex { array, index } => {
            walk_expr_subst(array, caps, pool);
            walk_expr_subst(index, caps, pool);
        }
        Expr::Cast { e: inner, .. } | Expr::InstanceOf { e: inner, .. } | Expr::Un { e: inner, .. } => {
            walk_expr_subst(inner, caps, pool)
        }
        Expr::Bin { l, r, .. } => {
            walk_expr_subst(l, caps, pool);
            walk_expr_subst(r, caps, pool);
        }
        Expr::Cond { c, t, f } => {
            walk_expr_subst(c, caps, pool);
            walk_expr_subst(t, caps, pool);
            walk_expr_subst(f, caps, pool);
        }
        Expr::Assign { target, value, .. } => {
            walk_expr_subst(target, caps, pool);
            walk_expr_subst(value, caps, pool);
        }
        Expr::PreIncDec { e: inner, .. } | Expr::PostIncDec { e: inner, .. } => {
            walk_expr_subst(inner, caps, pool)
        }
        Expr::NewArray { dims, init, .. } => {
            dims.iter_mut().for_each(|d| walk_expr_subst(d, caps, pool));
            if let Some(vals) = init {
                vals.iter_mut().for_each(|v| walk_expr_subst(v, caps, pool));
            }
        }
        Expr::StringConcat(parts) => parts.iter_mut().for_each(|p| {
            if let crate::expr::ConcatPart::Str(inner) = p {
                walk_expr_subst(inner, caps, pool);
            }
        }),
        Expr::Lambda(l) => l.captures.iter_mut().for_each(|c| walk_expr_subst(c, caps, pool)),
        Expr::Invokedynamic { args, .. } => args.iter_mut().for_each(|a| walk_expr_subst(a, caps, pool)),
        _ => {}
    }
}

fn strip_trailing_return(s: &Stmt) -> Stmt {
    match s {
        Stmt::Block(v) => {
            let mut v = v.clone();
            if let Some(Stmt::Return(None)) = v.last() {
                v.pop();
            }
            Stmt::Block(v)
        }
        Stmt::Return(None) => Stmt::Block(vec![]),
        other => other.clone(),
    }
}

// ---------------------------------------------------------------------------
// module-info
// ---------------------------------------------------------------------------

fn decompile_module_info(pc: &PoolClass) -> anyhow::Result<String> {
    let Some(bytes) = pc.class_attr("Module") else {
        anyhow::bail!("module-info without Module attribute");
    };
    let attr = parse_module_attr(bytes)?;
    let mut out = String::new();
    let name = pc.class_name(attr.module_name_index).unwrap_or("module");
    out.push_str(&format!("module {} {{\n", name));
    for r in &attr.requires {
        let rn = pc.class_name(r.requires_index).unwrap_or("?");
        let mut mods = Vec::new();
        if r.requires_flags & 0x0020 != 0 {
            mods.push("transitive");
        }
        if r.requires_flags & 0x0040 != 0 {
            mods.push("static");
        }
        let mstr = if mods.is_empty() { String::new() } else { format!("{} ", mods.join(" ")) };
        out.push_str(&format!("    requires {}{};\n", mstr, rn));
    }
    for e in &attr.exports {
        let pn = pc.class_name(e.exports_index).unwrap_or("?").replace('/', ".");
        if e.exports_to_index.is_empty() {
            out.push_str(&format!("    exports {};\n", pn));
        } else {
            let tos: Vec<String> =
                e.exports_to_index.iter().filter_map(|&i| pc.class_name(i)).map(|s| s.to_string()).collect();
            out.push_str(&format!("    exports {} to {};\n", pn, tos.join(", ")));
        }
    }
    for o in &attr.opens {
        let pn = pc.class_name(o.opens_index).unwrap_or("?").replace('/', ".");
        if o.opens_to_index.is_empty() {
            out.push_str(&format!("    opens {};\n", pn));
        } else {
            let tos: Vec<String> =
                o.opens_to_index.iter().filter_map(|&i| pc.class_name(i)).map(|s| s.to_string()).collect();
            out.push_str(&format!("    opens {} to {};\n", pn, tos.join(", ")));
        }
    }
    for u in &attr.uses_index {
        if let Some(un) = pc.class_name(*u) {
            out.push_str(&format!("    uses {};\n", un.replace('/', ".")));
        }
    }
    for p in &attr.provides {
        let sn = pc.class_name(p.provides_index).unwrap_or("?").replace('/', ".");
        let ws: Vec<String> =
            p.provides_with_index.iter().filter_map(|&i| pc.class_name(i)).map(|s| s.replace('/', ".")).collect();
        out.push_str(&format!("    provides {} with {};\n", sn, ws.join(", ")));
    }
    out.push_str("}\n");
    Ok(out)
}

fn parse_module_attr(info: &[u8]) -> anyhow::Result<jcdc_classfile::ModuleAttribute> {
    fn u2(b: &[u8], i: &mut usize) -> anyhow::Result<u16> {
        anyhow::ensure!(*i + 2 <= b.len(), "truncated module attr");
        let v = u16::from_be_bytes([b[*i], b[*i + 1]]);
        *i += 2;
        Ok(v)
    }
    let mut i = 0;
    let module_name_index = u2(info, &mut i)?;
    let module_flags = u2(info, &mut i)?;
    let module_version_index = u2(info, &mut i)?;
    let nr = u2(info, &mut i)? as usize;
    let mut requires = Vec::with_capacity(nr);
    for _ in 0..nr {
        requires.push(jcdc_classfile::ModuleRequires {
            requires_index: u2(info, &mut i)?,
            requires_flags: u2(info, &mut i)?,
            requires_version_index: u2(info, &mut i)?,
        });
    }
    let ne = u2(info, &mut i)? as usize;
    let mut exports = Vec::with_capacity(ne);
    for _ in 0..ne {
        let ei = u2(info, &mut i)?;
        let ef = u2(info, &mut i)?;
        let nt = u2(info, &mut i)? as usize;
        let mut to = Vec::with_capacity(nt);
        for _ in 0..nt {
            to.push(u2(info, &mut i)?);
        }
        exports.push(jcdc_classfile::ModuleExports { exports_index: ei, exports_flags: ef, exports_to_index: to });
    }
    let no = u2(info, &mut i)? as usize;
    let mut opens = Vec::with_capacity(no);
    for _ in 0..no {
        let oi = u2(info, &mut i)?;
        let of = u2(info, &mut i)?;
        let nt = u2(info, &mut i)? as usize;
        let mut to = Vec::with_capacity(nt);
        for _ in 0..nt {
            to.push(u2(info, &mut i)?);
        }
        opens.push(jcdc_classfile::ModuleOpens { opens_index: oi, opens_flags: of, opens_to_index: to });
    }
    let nu = u2(info, &mut i)? as usize;
    let mut uses_index = Vec::with_capacity(nu);
    for _ in 0..nu {
        uses_index.push(u2(info, &mut i)?);
    }
    let np = u2(info, &mut i)? as usize;
    let mut provides = Vec::with_capacity(np);
    for _ in 0..np {
        let pi = u2(info, &mut i)?;
        let nw = u2(info, &mut i)? as usize;
        let mut with = Vec::with_capacity(nw);
        for _ in 0..nw {
            with.push(u2(info, &mut i)?);
        }
        provides.push(jcdc_classfile::ModuleProvides { provides_index: pi, provides_with_index: with });
    }
    Ok(jcdc_classfile::ModuleAttribute {
        module_name_index,
        module_flags,
        module_version_index,
        requires,
        exports,
        opens,
        uses_index,
        provides,
    })
}


// ---------------------------------------------------------------------------
// switch-on-enum restoration ($SwitchMap pattern)
// ---------------------------------------------------------------------------

/// javac compiles `switch (e)` on an enum into
/// `switch (Synth.$SwitchMap$pkg$Enum[e.ordinal()])` where the synthetic
/// holder's <clinit> maps `$SwitchMap[C.ordinal()] = k`. Restore: selector
/// becomes `e`, integer case labels become the enum constant names.
pub fn restore_enum_switches(s: &mut Stmt, pc: &PoolClass, pool: &ClassPool) {
    match s {
        Stmt::Switch { selector, cases, default, .. } => {
            restore_one_switch(selector, cases, default, pc, pool);
            for c in cases {
                c.body.iter_mut().for_each(|st| restore_enum_switches(st, pc, pool));
            }
            if let Some(d) = default {
                restore_enum_switches(d, pc, pool);
            }
        }
        Stmt::Block(v) => v.iter_mut().for_each(|x| restore_enum_switches(x, pc, pool)),
        Stmt::If { then_stmt, else_stmt, .. } => {
            restore_enum_switches(then_stmt, pc, pool);
            if let Some(e) = else_stmt {
                restore_enum_switches(e, pc, pool);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => restore_enum_switches(body, pc, pool),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(|i| restore_enum_switches(i, pc, pool));
            restore_enum_switches(body, pc, pool);
        }
        Stmt::ForEach { body, .. } => restore_enum_switches(body, pc, pool),
        Stmt::Try { body, catches, finally } => {
            restore_enum_switches(body, pc, pool);
            for c in catches {
                restore_enum_switches(&mut c.body, pc, pool);
            }
            if let Some(f) = finally {
                restore_enum_switches(f, pc, pool);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { restore_enum_switches(res, pc, pool); }
            restore_enum_switches(body, pc, pool);
            for c in catches {
                restore_enum_switches(&mut c.body, pc, pool);
            }
            if let Some(f) = finally {
                restore_enum_switches(f, pc, pool);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => {
            restore_enum_switches(body, pc, pool)
        }
        _ => {}
    }
}

fn restore_one_switch(
    selector: &mut Expr,
    cases: &mut Vec<crate::stmt::CaseGroup>,
    default: &mut Option<Box<Stmt>>,
    pc: &PoolClass,
    pool: &ClassPool,
) {
    // Java 21+ SwitchBootstraps.typeSwitch: `switch (recv)` with string
    // constants, `case null` (index -1) and type patterns.
    if let Expr::Invokedynamic { name, args, bsm_static_args, .. } = &*selector {
        if name == "typeSwitch" && !args.is_empty() {
            let recv = args[0].clone();
            let labels = bsm_static_args.clone();
            let _shorten = |c: &str| Printer::new(pc, pool, empty_vt()).shorten(c);
            let mut ok = true;
            let mut new_cases: Vec<(Vec<String>, Vec<String>)> = Vec::new(); // (raw, str)
            let mut pat_ctr = 0usize;
            for cgroup in cases.iter() {
                let mut raws = Vec::new();
                let mut strs = Vec::new();
                for k in &cgroup.labels {
                    if *k == -1 {
                        raws.push("null".to_string());
                    } else if *k >= 0 && (*k as usize) < labels.len() {
                        match &labels[*k as usize] {
                            crate::expr::BsmArg::Str(sv) => strs.push(sv.clone()),
                            crate::expr::BsmArg::Cls(cv) => {
                                // Render the pattern type through the
                                // printer so array types (`[B` → `byte[]`)
                                // and nested names come out as source.
                                let ty = if cv.starts_with('[') {
                                    match jcdc_jvm::parse_field_descriptor(cv) {
                                        Some(t) => TypeRef::J(t),
                                        None => TypeRef::J(jcdc_jvm::JavaType::Object(cv.clone())),
                                    }
                                } else {
                                    TypeRef::J(jcdc_jvm::JavaType::Object(cv.clone()))
                                };
                                let tn = Printer::new(pc, pool, empty_vt()).type_name(&ty);
                                raws.push(format!("{} ignored{}", tn, pat_ctr));
                                pat_ctr += 1;
                            }
                            crate::expr::BsmArg::Other => {
                                ok = false;
                            }
                        }
                    } else {
                        ok = false;
                    }
                }
                new_cases.push((raws, strs));
            }
            if ok {
                for (cgroup, (raws, strs)) in cases.iter_mut().zip(new_cases) {
                    cgroup.raw_labels = raws;
                    cgroup.string_labels = strs;
                    cgroup.labels.clear();
                }
                // A typeSwitch is a PATTERN switch in source: fall-through
                // is illegal ("贯穿到模式非法", jdk26 ParserVerifier x34).
                // Every labelled case (and the default) must end in a
                // jump; when structuring lost the break, re-append it.
                fn case_terminates(st: &Stmt) -> bool {
                    match st {
                        Stmt::Return(_) | Stmt::Throw(_) | Stmt::Break(_) | Stmt::Continue(_) => true,
                        Stmt::Block(v) => v.last().map(case_terminates).unwrap_or(false),
                        Stmt::If { then_stmt, else_stmt: Some(e), .. } => {
                            case_terminates(then_stmt) && case_terminates(e)
                        }
                        Stmt::Labeled { body, .. } | Stmt::Synchronized { body, .. } => {
                            case_terminates(body)
                        }
                        Stmt::Try { body, finally, .. }
                        | Stmt::TryWithResources { body, finally, .. } => match finally {
                            Some(f) => case_terminates(f),
                            None => case_terminates(body),
                        },
                        _ => false,
                    }
                }
                for cgroup in cases.iter_mut() {
                    if cgroup.raw_labels.is_empty() && cgroup.string_labels.is_empty() {
                        continue; // fall-through continuation group
                    }
                    if !cgroup.body.last().map(case_terminates).unwrap_or(false) {
                        cgroup.body.push(Stmt::Break(None));
                    }
                }
                if let Some(d) = default {
                    if !case_terminates(d) {
                        let inner = std::mem::replace(d, Box::new(Stmt::Block(vec![])));
                        *d = Box::new(Stmt::Block(vec![*inner, Stmt::Break(None)]));
                    }
                }
                *selector = recv;
                return;
            }
        }
    }
    let (synth, field, recv) = match &*selector {
        Expr::ArrayIndex { array, index } => {
            let (synth, field) = match &**array {
                Expr::Field { cls, name, is_static: true, .. } if name.starts_with("$SwitchMap$") => {
                    (cls.clone(), name.clone())
                }
                _ => return,
            };
            let recv = match &**index {
                Expr::Method { name, owner: Some(o), args, .. } if name == "ordinal" && args.is_empty() => {
                    (**o).clone()
                }
                _ => return,
            };
            (synth, field, recv)
        }
        _ => return,
    };
    let Some(map) = switch_map(pool, &synth, &field) else { return };
    if map.is_empty() {
        return;
    }
    let mut all_mapped = true;
    for c in cases.iter_mut() {
        let mut names = Vec::new();
        for k in &c.labels {
            match map.get(k) {
                Some(n) => names.push(n.clone()),
                None => {
                    all_mapped = false;
                    break;
                }
            }
        }
        if !all_mapped {
            break;
        }
        c.enum_labels = names;
    }
    if !all_mapped {
        for c in cases.iter_mut() {
            c.enum_labels.clear();
        }
        return;
    }
    for c in cases.iter_mut() {
        c.labels.clear();
    }
    *selector = recv;
}

/// Parse the synthetic holder's <clinit> for `$SwitchMap[C.ordinal()] = k`
/// sequences and return k -> constant name.
fn switch_map(pool: &ClassPool, synth: &str, field: &str) -> Option<std::collections::HashMap<i64, String>> {
    use jcdc_classfile::instruction::{decode_all, Opcode};
    let spc = pool.get(synth)?;
    let ci = spc.find_own_method("<clinit>", "()V")?;
    let code = crate::varalloc::code_attribute(&spc, ci)?;
    let ins = decode_all(&code.code);
    let const_int = |i: &jcdc_classfile::instruction::Instruction| -> Option<i32> {
        match i.op {
            Opcode::IconstM1 => Some(-1),
            Opcode::Iconst0 => Some(0),
            Opcode::Iconst1 => Some(1),
            Opcode::Iconst2 => Some(2),
            Opcode::Iconst3 => Some(3),
            Opcode::Iconst4 => Some(4),
            Opcode::Iconst5 => Some(5),
            Opcode::Bipush | Opcode::Sipush => Some(i.a),
            Opcode::Ldc | Opcode::LdcW => {
                match jcdc_classfile::get_entry(&spc.cf.constant_pool, i.a as u16) {
                    Some(jcdc_classfile::ConstantPoolEntry::Integer(n)) => Some(n.value),
                    _ => None,
                }
            }
            _ => None,
        }
    };
    let mut map = std::collections::HashMap::new();
    let mut i = 0;
    while i + 4 < ins.len() {
        let (i0, i1, i2, i3, i4) = (&ins[i], &ins[i + 1], &ins[i + 2], &ins[i + 3], &ins[i + 4]);
        if i0.op == Opcode::Getstatic
            && i1.op == Opcode::Getstatic
            && i2.op == Opcode::Invokevirtual
            && i4.op == Opcode::Iastore
        {
            let f0 = spc.member_ref(i0.a as u16);
            let f1 = spc.member_ref(i1.a as u16);
            let ord = spc.member_ref(i2.a as u16);
            if let (Some((c0, n0, _)), Some((_, cname, _)), Some((_, "ordinal", _))) = (f0, f1, ord) {
                if c0 == synth && n0 == field {
                    if let Some(k) = const_int(i3) {
                        map.insert(k as i64, cname.to_string());
                    }
                }
            }
        }
        i += 1;
    }
    Some(map)
}


/// Remove synthetic inner-class constructor artifacts: `Outer.this = this$0`
/// assignments and `Objects.requireNonNull(this$0)` guards on the hidden
/// enclosing-instance parameters (the parameters themselves are skipped in
/// the printed signature).
fn strip_inner_ctor_artifacts(s: &mut Stmt, vt: &VarTable, outer_param: Option<(u16, String)>) {
    fn is_this_param(e: &Expr, vt: &VarTable, outer_param: Option<&(u16, String)>) -> bool {
        match e {
            Expr::Local { var, .. } => {
                let info = vt.var(*var);
                info.name.starts_with("this$")
                    || match outer_param {
                        Some((slot, _)) => info.is_param && info.slot == *slot,
                        None => false,
                    }
            }
            Expr::Raw(t) => t.starts_with("this$") || t.ends_with(".this$0"),
            Expr::Field { name, .. } => name.starts_with("this$"),
            _ => false,
        }
    }
    fn junk(st: &Stmt, vt: &VarTable, outer_param: Option<&(u16, String)>) -> bool {
        match st {
            Stmt::ExprStmt(Expr::Assign { target, .. }) => match &**target {
                Expr::Field { name, .. } => {
                    name.starts_with("this$") || name.starts_with("val$")
                }
                // Capture substitution turns `this.val$x = param` into an
                // assign to a Raw outer-local name; an inner/local ctor can
                // never legally assign an outer local, so any Raw target
                // here is a capture store.
                Expr::Raw(_) => true,
                _ => false,
            },
            Stmt::ExprStmt(Expr::Method { name, args, .. }) => {
                (name == "requireNonNull" || name == "checkNotNull")
                    && args.len() == 1
                    && is_this_param(&args[0], vt, outer_param)
            }
            // LocalDef mirroring the outer instance into a synthetic
            // (`Local x = this$0; requireNonNull(x)`) — x dies with the
            // ctor prologue.
            Stmt::LocalDef { init: Some(e), .. } => is_this_param(e, vt, outer_param),
            _ => false,
        }
    }
    // Reads of the outer-instance PARAMETER slot (before/without the
    // putfield mirror) print as bare `this$0.field` (symbol not found).
    // Normalize them to field reads on `this`; the outer-this
    // substitution (which now runs after this pass) rewrites those to
    // `Outer.this.field`.
    fn fix_expr(e: &mut Expr, vt: &VarTable, outer_param: Option<&(u16, String)>) {
        if let Expr::Local { var, .. } = e {
            let info = vt.var(*var);
            // The forwarded outer-instance param is often UNNAMED in the
            // LVT (`arg0` — jdk11 ArrayDeque$DescendingIterator ctor:
            // `dec(arg0.tail, arg0.elements.length)`): identify it by
            // param slot when the class has a this$N field.
            let by_slot = match outer_param {
                Some((slot, _)) => {
                    info.is_param && info.slot == *slot && !info.name.starts_with("this$")
                }
                None => false,
            };
            if info.name.starts_with("this$") || by_slot {
                let name = if info.name.starts_with("this$") {
                    info.name.clone()
                } else {
                    outer_param.unwrap().1.clone()
                };
                let ty = info.ty.clone();
                *e = Expr::Field {
                    owner: Some(Box::new(Expr::This)),
                    cls: String::new(),
                    name,
                    ty,
                    is_static: false,
                };
                return;
            }
        }
        match e {
            Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
                args.iter_mut().for_each(|a| fix_expr(a, vt, outer_param))
            }
            Expr::Method { owner, args, .. } => {
                if let Some(o) = owner {
                    fix_expr(o, vt, outer_param);
                }
                args.iter_mut().for_each(|a| fix_expr(a, vt, outer_param));
            }
            Expr::Field { owner: Some(o), .. } => fix_expr(o, vt, outer_param),
            Expr::ArrayIndex { array, index } => {
                fix_expr(array, vt, outer_param);
                fix_expr(index, vt, outer_param);
            }
            Expr::Cast { e: inner, .. } | Expr::InstanceOf { e: inner, .. } | Expr::Un { e: inner, .. } => {
                fix_expr(inner, vt, outer_param)
            }
            Expr::Bin { l, r, .. } => {
                fix_expr(l, vt, outer_param);
                fix_expr(r, vt, outer_param);
            }
            Expr::Cond { c, t, f } => {
                fix_expr(c, vt, outer_param);
                fix_expr(t, vt, outer_param);
                fix_expr(f, vt, outer_param);
            }
            Expr::Assign { target, value, .. } => {
                fix_expr(target, vt, outer_param);
                fix_expr(value, vt, outer_param);
            }
            Expr::PreIncDec { e: inner, .. } | Expr::PostIncDec { e: inner, .. } => {
                fix_expr(inner, vt, outer_param)
            }
            Expr::NewArray { dims, init, .. } => {
                dims.iter_mut().for_each(|d| fix_expr(d, vt, outer_param));
                if let Some(vals) = init {
                    vals.iter_mut().for_each(|v| fix_expr(v, vt, outer_param));
                }
            }
            Expr::StringConcat(parts) => parts.iter_mut().for_each(|p| {
                if let crate::expr::ConcatPart::Str(inner) = p {
                    fix_expr(inner, vt, outer_param);
                }
            }),
            Expr::Lambda(l) => l.captures.iter_mut().for_each(|c| fix_expr(c, vt, outer_param)),
            Expr::Invokedynamic { args, .. } => args.iter_mut().for_each(|a| fix_expr(a, vt, outer_param)),
            _ => {}
        }
    }
    fn rec(s: &mut Stmt, vt: &VarTable, outer_param: Option<&(u16, String)>) {
        match s {
            Stmt::Block(v) => {
                v.retain(|st| !junk(st, vt, outer_param));
                v.iter_mut().for_each(|x| rec(x, vt, outer_param));
            }
            Stmt::ExprStmt(e) => fix_expr(e, vt, outer_param),
            Stmt::LocalDef { init: Some(e), .. } => fix_expr(e, vt, outer_param),
            Stmt::Return(Some(e)) | Stmt::Throw(e) => fix_expr(e, vt, outer_param),
            Stmt::If { cond, then_stmt, else_stmt } => {
                fix_expr(cond, vt, outer_param);
                rec(then_stmt, vt, outer_param);
                if let Some(x) = else_stmt {
                    rec(x, vt, outer_param);
                }
            }
            Stmt::While { cond, body } => {
                fix_expr(cond, vt, outer_param);
                rec(body, vt, outer_param);
            }
            Stmt::DoWhile { body, cond } => {
                rec(body, vt, outer_param);
                fix_expr(cond, vt, outer_param);
            }
            Stmt::For { init, cond, update, body } => {
                init.iter_mut().for_each(|i| rec(i, vt, outer_param));
                if let Some(c) = cond {
                    fix_expr(c, vt, outer_param);
                }
                update.iter_mut().for_each(|u| fix_expr(u, vt, outer_param));
                rec(body, vt, outer_param);
            }
            Stmt::ForEach { iterable, body, .. } => {
                fix_expr(iterable, vt, outer_param);
                rec(body, vt, outer_param);
            }
            Stmt::Switch { selector, cases, default, .. } => {
                fix_expr(selector, vt, outer_param);
                for c in cases.iter_mut() {
                    c.body.iter_mut().for_each(|st| rec(st, vt, outer_param));
                }
                if let Some(d) = default {
                    rec(d, vt, outer_param);
                }
            }
            Stmt::Try { body, catches, finally } => {
                rec(body, vt, outer_param);
                for c in catches.iter_mut() {
                    rec(&mut c.body, vt, outer_param);
                }
                if let Some(f) = finally {
                    rec(f, vt, outer_param);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                for r in resources.iter_mut() {
                    rec(r, vt, outer_param);
                }
                rec(body, vt, outer_param);
                for c in catches.iter_mut() {
                    rec(&mut c.body, vt, outer_param);
                }
                if let Some(f) = finally {
                    rec(f, vt, outer_param);
                }
            }
            Stmt::Synchronized { lock, body } => {
                fix_expr(lock, vt, outer_param);
                rec(body, vt, outer_param);
            }
            Stmt::Labeled { body, .. } => rec(body, vt, outer_param),
            _ => {}
        }
    }
    rec(s, vt, outer_param.as_ref());
}


/// True when the method body is built around an `ObjectMethods.bootstrap`
/// invokedynamic (compiler-generated equals/hashCode/toString).
fn is_object_methods_indy(pc: &PoolClass, mi: usize) -> bool {
    use jcdc_classfile::instruction::{decode_all, Opcode};
    let Some(code) = crate::varalloc::code_attribute(pc, mi) else {
        return false;
    };
    let Some(bsm_bytes) = pc.class_attr("BootstrapMethods") else {
        return false;
    };
    for ins in decode_all(&code.code) {
        if ins.op != Opcode::Invokedynamic {
            continue;
        }
        let bm_idx = match jcdc_classfile::get_entry(&pc.cf.constant_pool, ins.a as u16) {
            Some(jcdc_classfile::ConstantPoolEntry::InvokeDynamic(d)) => {
                d.bootstrap_method_attr_index
            }
            _ => continue,
        };
        let mut i = 0usize;
        let mut found = None;
        'scan: {
            let rd = |i: &mut usize| -> Option<u16> {
                let hi = *bsm_bytes.get(*i)?;
                let lo = *bsm_bytes.get(*i + 1)?;
                *i += 2;
                Some(u16::from_be_bytes([hi, lo]))
            };
            let Some(n) = rd(&mut i) else { break 'scan };
            for k in 0..n {
                let Some(href) = rd(&mut i) else { break 'scan };
                let Some(na) = rd(&mut i) else { break 'scan };
                if k == bm_idx {
                    found = Some(href);
                    break;
                }
                for _ in 0..na {
                    if rd(&mut i).is_none() {
                        break 'scan;
                    }
                }
            }
        }
        if let Some(href) = found {
            // href is a CONSTANT_MethodHandle; dereference to the method.
            let mref = match jcdc_classfile::get_entry(&pc.cf.constant_pool, href) {
                Some(jcdc_classfile::ConstantPoolEntry::MethodHandle(h)) => h.reference_index,
                _ => href,
            };
            if let Some((cls, _, _)) = pc.member_ref(mref) {
                return cls == "java/lang/runtime/ObjectMethods";
            }
        }
    }
    false
}


/// Re-insert `(T)` casts that javac elided for type-variable returns and
/// assignments (the bytecode needs no checkcast when the erasure matches).
fn cast_returns_to_typevar(s: &mut Stmt, tv: &str, vt: &VarTable) {
    let target = TypeRef::G(jcdc_jvm::GenericType::TypeVar(tv.to_string()));
    // A field read through a wildcard-parameterized receiver (`e.value`
    // where e: Entry<?,?>) has a CAPTURE type, not the method's own type
    // variable — even when the names collide. It always needs the cast.
    fn capture_field(e: &Expr) -> bool {
        if let Expr::Field { owner: Some(o), .. } = e {
            if let TypeRef::G(jcdc_jvm::GenericType::Class(cs)) = o.type_ref() {
                return cs.parts.iter().any(|p| {
                    p.args
                        .iter()
                        .any(|a| matches!(a, jcdc_jvm::GenericType::Wildcard(_)))
                });
            }
        }
        false
    }
    fn fix(e: &mut Expr, target: &TypeRef, tv: &str) {
        if matches!(e, Expr::Const(crate::expr::ConstVal::Null)) {
            return;
        }
        let already = match e.type_ref() {
            TypeRef::G(jcdc_jvm::GenericType::TypeVar(n)) => n == tv && !capture_field(e),
            _ => false,
        };
        if !already {
            let inner = std::mem::replace(e, Expr::This);
            *e = Expr::Cast { ty: target.clone(), e: Box::new(inner) };
        }
    }
    match s {
        Stmt::Block(v) => v.iter_mut().for_each(|x| cast_returns_to_typevar(x, tv, vt)),
        Stmt::Return(Some(e)) => fix(e, &target, tv),
        Stmt::LocalDef { var, init: Some(e), .. } => {
            let is_tv = match &vt.var(*var).ty {
                TypeRef::G(jcdc_jvm::GenericType::TypeVar(n)) => n == tv,
                _ => false,
            };
            if is_tv {
                fix(e, &target, tv);
            }
        }
        Stmt::ExprStmt(Expr::Assign { target: t, value, .. }) => {
            let is_tv = match t.type_ref() {
                TypeRef::G(jcdc_jvm::GenericType::TypeVar(n)) => n == tv,
                _ => false,
            };
            if is_tv {
                fix(value, &target, tv);
            }
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            cast_returns_to_typevar(then_stmt, tv, vt);
            if let Some(e) = else_stmt {
                cast_returns_to_typevar(e, tv, vt);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => {
            cast_returns_to_typevar(body, tv, vt)
        }
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(|i| cast_returns_to_typevar(i, tv, vt));
            cast_returns_to_typevar(body, tv, vt);
        }
        Stmt::ForEach { body, .. } => cast_returns_to_typevar(body, tv, vt),
        Stmt::Try { body, catches, finally } => {
            cast_returns_to_typevar(body, tv, vt);
            for c in catches {
                cast_returns_to_typevar(&mut c.body, tv, vt);
            }
            if let Some(f) = finally {
                cast_returns_to_typevar(f, tv, vt);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { cast_returns_to_typevar(res, tv, vt); }
            cast_returns_to_typevar(body, tv, vt);
            for c in catches {
                cast_returns_to_typevar(&mut c.body, tv, vt);
            }
            if let Some(f) = finally {
                cast_returns_to_typevar(f, tv, vt);
            }
        }
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(|st| cast_returns_to_typevar(st, tv, vt));
            }
            if let Some(d) = default {
                cast_returns_to_typevar(d, tv, vt);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => {
            cast_returns_to_typevar(body, tv, vt)
        }
        _ => {}
    }
}


/// Collapse `v = <branches>; this(v); return;` constructor bodies into a
/// single leading `this(<ternary chain>)` delegation.
fn collapse_ctor_delegation(body: &mut Stmt, pc: &PoolClass) {
    let items = match body {
        Stmt::Block(v) => v,
        _ => return,
    };
    if items.is_empty() {
        return;
    }
    // javac compiles a leading `this(<big conditional>)` into per-branch
    // delegations through a shared local: `[str = null;] if-tree with
    // leaves `str = X; this(str); return;` (branches may also FALL
    // THROUGH to a trailing `this(str);`)`. Fold the whole tail sequence
    // back into one leading delegation — mid-body `this(...)` is illegal
    // source (jdk26 String(Charset,byte[],int,int): "explicit constructor
    // call not allowed here", blocked every jdk26 corpus family).
    let (tail, fallback) = match items.last() {
        Some(Stmt::ExprStmt(e @ Expr::Method { name, cls, args, .. }))
            if name == "<init>" && cls == &pc.internal_name && args.len() == 1 =>
        {
            (&items[..items.len() - 1], Some(e.clone()))
        }
        _ => (items.as_slice(), None),
    };
    if tail.is_empty() {
        return;
    }
    let mut tmpl: Option<Expr> = None;
    let Some(val) = delegation_value_seq(tail, &mut tmpl, &pc.internal_name, fallback.as_ref())
    else {
        return;
    };
    let Some(mut call) = tmpl.or(fallback) else { return };
    // Only a delegation to THIS class (not super) may appear mid-body.
    match &mut call {
        Expr::Method { cls, args, .. } if args.len() == 1 => {
            if cls != &pc.internal_name {
                return;
            }
            args[0] = val;
        }
        _ => return,
    }
    *body = Stmt::Block(vec![Stmt::ExprStmt(call)]);
}

/// Fold a statement SEQUENCE (assignments + one if-tree + optional
/// trailing delegation) into the delegated value. Branches without their
/// own `this(...)` fall through to the trailing delegation, so their
/// folded value is their last assignment to the delegated local.
fn delegation_value_seq(
    stmts: &[Stmt],
    tmpl: &mut Option<Expr>,
    own: &str,
    fallback: Option<&Expr>,
) -> Option<Expr> {
    let mut val: Option<Expr> = None;
    for st in stmts {
        match st {
            Stmt::LocalDef { init: None, .. } => {}
            Stmt::LocalDef { init: Some(e), .. }
            | Stmt::ExprStmt(e @ Expr::Assign { .. }) => {
                let v = match e {
                    Expr::Assign { value, .. } => (**value).clone(),
                    other => other.clone(),
                };
                val = Some(v);
            }
            Stmt::Comment(_) => {}
            Stmt::If { .. } => {
                val = delegation_value(st, tmpl, own, fallback);
            }
            Stmt::ExprStmt(e @ Expr::Method { name, cls, .. })
                if name == "<init>" && cls == own =>
            {
                if tmpl.is_none() {
                    *tmpl = Some(e.clone());
                }
            }
            Stmt::Return(_) => {}
            _ => return None,
        }
    }
    val
}

/// Walk an if/else tree whose leaves are `v = e; this(v); return;` and
/// produce the folded value expression plus the delegation call template.
fn delegation_value(
    s: &Stmt,
    tmpl: &mut Option<Expr>,
    own: &str,
    fallback: Option<&Expr>,
) -> Option<Expr> {
    match s {
        Stmt::Block(v) => {
            let mut val: Option<Expr> = None;
            let mut call: Option<Expr> = None;
            for st in v {
                match st {
                    // Track the LAST assignment: a fall-through branch's
                    // delegated value is the local's final value on that
                    // path (branches that reassign before exiting).
                    Stmt::ExprStmt(Expr::Assign { value, .. }) => {
                        val = Some((**value).clone());
                    }
                    Stmt::LocalDef { init: Some(e), .. } => {
                        val = Some(e.clone());
                    }
                    Stmt::LocalDef { init: None, .. } => {}
                    Stmt::ExprStmt(e @ Expr::Method { name, cls, .. })
                        if name == "<init>" && cls == own && call.is_none() =>
                    {
                        call = Some(e.clone());
                    }
                    // Nested if-chains fold into a conditional value
                    // (javac wraps the dispatch chain in blocks).
                    Stmt::If { .. } => {
                        let iv = delegation_value(st, tmpl, own, fallback)?;
                        val = Some(iv);
                    }
                    Stmt::Return(_) | Stmt::Comment(_) => {}
                    _ => return None,
                }
            }
            match (val, call.or_else(|| fallback.cloned())) {
                (Some(v0), Some(c)) => {
                    if tmpl.is_none() {
                        *tmpl = Some(c);
                    }
                    Some(v0)
                }
                _ => None,
            }
        }
        Stmt::If { cond, then_stmt, else_stmt: Some(e), .. } => {
            let t = delegation_value(then_stmt, tmpl, own, fallback)?;
            let f = delegation_value(e, tmpl, own, fallback)?;
            Some(Expr::Cond {
                c: Box::new(cond.clone()),
                t: Box::new(t),
                f: Box::new(f),
            })
        }
        Stmt::ExprStmt(e @ Expr::Method { name, cls, args, .. })
            if name == "<init>" && cls == own && args.len() == 1 =>
        {
            if tmpl.is_none() {
                *tmpl = Some(e.clone());
            }
            Some(args[0].clone())
        }
        // A fall-through branch can be a BARE assignment (no block):
        // `str = decode(..)` flows to the trailing delegation.
        Stmt::ExprStmt(Expr::Assign { value, .. }) => Some((**value).clone()),
        Stmt::LocalDef { init: Some(e), .. } => Some(e.clone()),
        Stmt::Block(v) if v.len() == 1 => delegation_value(&v[0], tmpl, own, fallback),
        _ => None,
    }
}



/// Erasure (internal name) of a signature throws entry: type variables
/// erase to their class bound.
fn generic_erasure(t: &jcdc_jvm::GenericType, params: &[jcdc_jvm::TypeParam]) -> Option<String> {
    match t {
        jcdc_jvm::GenericType::Class(cs) => Some(cs.internal_name()),
        jcdc_jvm::GenericType::TypeVar(name) => {
            let p = params.iter().find(|p| &p.name == name)?;
            match &p.class_bound {
                Some(jcdc_jvm::GenericType::Class(cs)) => Some(cs.internal_name()),
                _ => Some("java/lang/Object".to_string()),
            }
        }
        _ => None,
    }
}


/// True when the erased type `ty` is `target` or a subtype of it (super
/// AND interface chains via the pool; unknown classes are not subtypes).
fn is_subtype_of(pool: &ClassPool, ty: &jcdc_jvm::JavaType, target: &str) -> bool {
    let jcdc_jvm::JavaType::Object(n0) = ty else { return false };
    let mut stack: Vec<String> = vec![n0.clone()];
    let mut seen: HashSet<String> = HashSet::new();
    while let Some(n) = stack.pop() {
        if n == target {
            return true;
        }
        if !seen.insert(n.clone()) {
            continue;
        }
        let Some(pc) = pool.get(&n) else { continue };
        if let Some(s) = pc.super_name() {
            if !s.is_empty() {
                stack.push(s.to_string());
            }
        }
        for &i in &pc.cf.interfaces {
            if let Some(iname) = pc.class_name(i) {
                stack.push(iname.to_string());
            }
        }
    }
    false
}

/// A generic method whose return type is its own type variable, called in
/// a `throw` statement, needs an explicit type witness (`String.<E>mk()`)
/// — inference in throw position falls back to the bound and would fail
/// the enclosing throws clause. Also retypes erasure casts on thrown
/// values to the declared throws type variable (`throw (X) e`).
fn add_throw_witnesses(s: &mut Stmt, msig: Option<&jcdc_jvm::MethodSignature>, pool: &ClassPool) {
    let Some(sig) = msig else { return };
    if sig.params.is_empty() {
        return;
    }
    match s {
        Stmt::Throw(e) => {
            // `throw (Throwable) supplier.get();` — javac checkcasts a
            // generically-thrown value to the ERASURE of the declared
            // throws type variable (`<X extends Throwable> ... throws X`).
            // Printing the erasure throws an exception the signature does
            // not declare ("未报告的异常错误Throwable", jdk17
            // Optional.orElseThrow). Retype the cast to the variable.
            // When javac omitted the vacuous checkcast entirely (the value
            // already has the bound's type — ForkJoinTask.uncheckedThrow
            // `throw (T) t`), synthesize the cast.
            let throws_typevar = sig.throws.iter().find_map(|t| {
                match t {
                    jcdc_jvm::GenericType::TypeVar(v) => {
                        let bounded = sig.params.iter().any(|p| {
                            p.name == *v
                                && p.class_bound.as_ref().map(|b| {
                                    TypeRef::G(b.clone()).erased()
                                        == jcdc_jvm::JavaType::Object("java/lang/Throwable".into())
                                }).unwrap_or(false)
                        });
                        if bounded { Some(v.clone()) } else { None }
                    }
                    _ => None,
                }
            });
            if let Expr::Cast { ty, e: _ } = e {
                if let TypeRef::J(jcdc_jvm::JavaType::Object(cn)) = ty {
                    if let Some(v) = sig.throws.iter().find_map(|t| {
                        match t {
                            jcdc_jvm::GenericType::TypeVar(v) => {
                                let bounded = sig.params.iter().any(|p| {
                                    p.name == *v
                                        && p.class_bound.as_ref().map(|b| {
                                            TypeRef::G(b.clone()).erased()
                                                == jcdc_jvm::JavaType::Object(cn.clone())
                                        }).unwrap_or(false)
                                });
                                if bounded { Some(v.clone()) } else { None }
                            }
                            _ => None,
                        }
                    }) {
                        *ty = TypeRef::G(jcdc_jvm::GenericType::TypeVar(v));
                        return;
                    }
                }
            } else if let Some(v) = &throws_typevar {
                // A bare throw of a Throwable-typed value under `throws T`:
                // legal source needs the vacuous `(T)` cast unless a
                // concrete throws entry already covers the type.
                let covered_by_concrete = sig.throws.iter().any(|t| {
                    match t {
                        jcdc_jvm::GenericType::Class(cs) => {
                            let n = crate::method::classsig_internal(cs);
                            is_subtype_of(pool, &e.type_ref().erased(), &n)
                        }
                        _ => false,
                    }
                });
                let already_var = matches!(e.type_ref(), TypeRef::G(jcdc_jvm::GenericType::TypeVar(_)));
                if !covered_by_concrete
                    && !already_var
                    && is_subtype_of(pool, &e.type_ref().erased(), "java/lang/Throwable")
                {
                    let inner = std::mem::replace(e, Expr::This);
                    *e = Expr::Cast {
                        ty: TypeRef::G(jcdc_jvm::GenericType::TypeVar(v.clone())),
                        e: Box::new(inner),
                    };
                    return;
                }
            }
            if let Expr::Method { cls, name, desc, type_args, .. } = e {
                if !type_args.is_empty() {
                    return;
                }
                let Some(cpc) = pool.get(cls) else { return };
                let mi = (0..cpc.cf.methods.len()).find(|&i| {
                    cpc.method_name(i) == Some(name.as_str())
                        && cpc
                            .method_desc(i)
                            .and_then(parse_method_descriptor)
                            .as_ref()
                            == Some(&*desc)
                });
                let Some(mi) = mi else { return };
                let m = &cpc.cf.methods[mi];
                let csig = m.attributes.iter().find_map(|a| {
                    if a.attribute_name_index != 0 {
                        if let Some(nm) = cpc.utf8(a.attribute_name_index) {
                            if nm == "Signature" && a.info.len() >= 2 {
                                let idx = u16::from_be_bytes([a.info[0], a.info[1]]);
                                return cpc
                                    .utf8(idx)
                                    .and_then(|s| parse_method_signature(s));
                            }
                        }
                    }
                    None
                });
                if let Some(cs) = csig {
                    if let jcdc_jvm::GenericType::TypeVar(v) = &cs.ret {
                        if sig.params.iter().any(|p| &p.name == v) {
                            *type_args = vec![v.clone()];
                        }
                    }
                }
            }
        }
        Stmt::Block(v) => {
            v.iter_mut().for_each(|x| add_throw_witnesses(x, msig, pool));
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            add_throw_witnesses(then_stmt, msig, pool);
            if let Some(e) = else_stmt {
                add_throw_witnesses(e, msig, pool);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => {
            add_throw_witnesses(body, msig, pool)
        }
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(|i| add_throw_witnesses(i, msig, pool));
            add_throw_witnesses(body, msig, pool);
        }
        Stmt::ForEach { body, .. } => add_throw_witnesses(body, msig, pool),
        Stmt::Try { body, catches, finally } => {
            add_throw_witnesses(body, msig, pool);
            for c in catches {
                add_throw_witnesses(&mut c.body, msig, pool);
            }
            if let Some(f) = finally {
                add_throw_witnesses(f, msig, pool);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { add_throw_witnesses(res, msig, pool); }
            add_throw_witnesses(body, msig, pool);
            for c in catches {
                add_throw_witnesses(&mut c.body, msig, pool);
            }
            if let Some(f) = finally {
                add_throw_witnesses(f, msig, pool);
            }
        }
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(|st| add_throw_witnesses(st, msig, pool));
            }
            if let Some(d) = default {
                add_throw_witnesses(d, msig, pool);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => {
            add_throw_witnesses(body, msig, pool)
        }
        _ => {}
    }
}


/// Wrap `return e;` in `(G) e` when the method's signature return type is
/// generic and `e` carries only the erased type.
/// Resolve the generic parameter types of a method call as instantiated by
/// the owner expression's parameterization. Returns None when unresolvable.
fn instantiated_method_params(
    m: &Expr,
    pool: &ClassPool,
    pc: &PoolClass,
) -> Option<Vec<jcdc_jvm::GenericType>> {
    let (cls, name, desc, owner, is_static) = match m {
        Expr::Method { cls, name, desc, owner, is_static, .. } => {
            (cls.as_str(), name.as_str(), desc, owner.as_deref(), *is_static)
        }
        _ => return None,
    };
    if name == "<init>" {
        return None;
    }
    // Owner parameterization: owner expr type, else `this`, else raw class.
    let (decl, args): (String, Vec<jcdc_jvm::GenericType>) = if is_static {
        (cls.to_string(), Vec::new())
    } else {
        match owner {
            Some(Expr::This) | None => {
                let own = owner.map(|o| o.type_ref());
                match own {
                    Some(TypeRef::G(jcdc_jvm::GenericType::Class(cs))) => {
                        (crate::method::classsig_internal(&cs), cs.parts.last()?.args.clone())
                    }
                    _ => {
                        // implicit `this` or erased owner: the enclosing class
                        let cs = pc.class_attr("Signature").and_then(|b| {
                            if b.len() < 2 {
                                return None;
                            }
                            let idx = u16::from_be_bytes([b[0], b[1]]);
                            pc.utf8(idx).and_then(|s| jcdc_jvm::parse_class_signature(s))
                        });
                        let args = cs
                            .as_ref()
                            .map(|c| {
                                c.params
                                    .iter()
                                    .map(|p| jcdc_jvm::GenericType::TypeVar(p.name.clone()))
                                    .collect()
                            })
                            .unwrap_or_default();
                        (pc.internal_name.clone(), args)
                    }
                }
            }
            Some(o) => match o.type_ref() {
                TypeRef::G(jcdc_jvm::GenericType::Class(cs)) => {
                    (crate::method::classsig_internal(&cs), cs.parts.last()?.args.clone())
                }
                t => match t.erased() {
                    jcdc_jvm::JavaType::Object(n) => (n, Vec::new()),
                    _ => return None,
                },
            },
        }
    };
    let dpc;
    let dref: &PoolClass = if decl == pc.internal_name {
        pc
    } else {
        dpc = pool.get(&decl)?;
        &dpc
    };
    let d_str = format!(
        "({}){}",
        desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
        desc.ret.to_descriptor()
    );
    let _ = &d_str;
    let mi = (0..dref.cf.methods.len()).find(|&i| {
        dref.method_name(i) == Some(name) && dref.method_desc(i) == Some(desc_raw(dref, i).as_str())
            && desc_raw(dref, i) == {
                let mut a = String::new();
                for t in &desc.args {
                    a.push_str(&t.to_descriptor());
                }
                format!("({}){}", a, desc.ret.to_descriptor())
            }
    })?;
    let sig_bytes = dref.cf.methods[mi].attributes.iter().find_map(|a| {
        if dref.utf8(a.attribute_name_index) == Some("Signature") {
            Some(a.info.as_slice())
        } else {
            None
        }
    })?;
    if sig_bytes.len() < 2 {
        return None;
    }
    let idx = u16::from_be_bytes([sig_bytes[0], sig_bytes[1]]);
    let msig = dref.utf8(idx).and_then(|s| jcdc_jvm::parse_method_signature(s))?;
    if !msig.params.is_empty() {
        // The method itself is generic; instantiation needs inference we
        // do not model here (handled by the return-witness pass instead).
        return None;
    }
    let class_params = dref.class_attr("Signature").and_then(|b| {
        if b.len() < 2 {
            return None;
        }
        let i2 = u16::from_be_bytes([b[0], b[1]]);
        dref.utf8(i2).and_then(|s| jcdc_jvm::parse_class_signature(s))
    })?;
    if class_params.params.len() != args.len() {
        return None;
    }
    let inst: Vec<jcdc_jvm::GenericType> = msig
        .args
        .iter()
        .map(|t| crate::method::subst_typevars(t, &class_params.params, &args))
        .collect();
    // Captured owner arguments can nest wildcards, which is not valid Java.
    if inst.iter().any(crate::method::has_nested_wildcard) {
        return None;
    }
    Some(inst)
}

fn desc_raw(pc: &PoolClass, mi: usize) -> String {
    pc.method_desc(mi).unwrap_or("").to_string()
}

/// SAM-interface cast for a lambda argument at an AMBIGUOUS overload
/// position: `AccessController.doPrivileged(() -> x)` matches both
/// doPrivileged(PrivilegedAction<T>) and doPrivileged(
/// PrivilegedExceptionAction<T>) — javac rejects the bare implicitly-
/// typed lambda ("reference to doPrivileged is ambiguous", 53 errors
/// across the jdk11 closure); the source always carries the cast
/// (`(PrivilegedAction<X>) () -> ...`). The call-site descriptor names
/// the chosen SAM interface; cast to its erasure (raw) — always
/// applicable and legal, merely unchecked. Fires only when the owner
/// class exposes same-name/same-arity overloads whose parameter at this
/// position ERASES differently (true ambiguity potential); unique
/// signatures keep the bare lambda and its target typing.
fn witness_ambiguous_lambda_args(e: &mut Expr, pool: &ClassPool, pc: &PoolClass) {
    let (cls, name, desc) = match &*e {
        Expr::Method { cls, name, desc, .. } => (cls.clone(), name.clone(), desc.clone()),
        _ => return,
    };
    if desc.args.is_empty() {
        return;
    }
    let dpc;
    let dref: &PoolClass = if cls == pc.internal_name {
        pc
    } else {
        dpc = match pool.get(&cls) {
            Some(p) => p,
            None => return,
        };
        &dpc
    };
    let mut ambiguous = vec![false; desc.args.len()];
    for mi in 0..dref.cf.methods.len() {
        if dref.method_name(mi) != Some(name.as_str()) {
            continue;
        }
        let Some(d_str) = dref.method_desc(mi) else { continue };
        if d_str == format!(
            "({}){}",
            desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
            desc.ret.to_descriptor()
        ) {
            continue; // the call itself
        }
        let Some(other) = parse_method_descriptor(d_str) else { continue };
        if other.args.len() != desc.args.len() {
            continue;
        }
        for (i, t) in other.args.iter().enumerate() {
            if t != &desc.args[i] {
                ambiguous[i] = true;
            }
        }
    }
    if !ambiguous.iter().any(|a| *a) {
        return;
    }
    let Expr::Method { args, .. } = e else { return };
    for (i, a) in args.iter_mut().enumerate() {
        if !ambiguous[i] || !matches!(a, Expr::Lambda(_)) {
            continue;
        }
        let sam = TypeRef::J(desc.args[i].clone());
        let inner = std::mem::replace(a, Expr::This);
        *a = Expr::Cast { ty: sam, e: Box::new(inner) };
    }
}

/// Raw-cast witness for a parameterized argument passed to a GENERIC
/// method's own typevar-parameterized formal: `Arrays.sort(a, c)` with
/// a: Object[] and c: Comparator<? super E> — javac pins T=Object from
/// the array, then rejects Comparator<? super E> for Comparator<? super
/// Object> ("no suitable method for sort(Object[], Comparator<CAP#1>)").
/// The source carried the RAW cast `(Comparator) c` (erased — no
/// bytecode trace). Fire only when formal and argument share the same
/// parameterized base class, the formal mentions a method type variable,
/// and the argument's parameters differ; every other shape stays with
/// inference. The raw cast makes the call unchecked but applicable —
/// the semantics are unchanged (erasure is identical).
fn raw_witness_generic_method_args(e: &mut Expr, pool: &ClassPool, pc: &PoolClass) {
    use jcdc_jvm::GenericType as G;
    fn has_tvar(g: &G, tvars: &[&str]) -> bool {
        match g {
            G::TypeVar(n) => tvars.contains(&n.as_str()),
            G::Array(i) => has_tvar(i, tvars),
            G::Class(cs) => cs.parts.iter().any(|p| p.args.iter().any(|a| has_tvar(a, tvars))),
            G::Wildcard(jcdc_jvm::WildcardBound::Extends(t))
            | G::Wildcard(jcdc_jvm::WildcardBound::Super(t)) => has_tvar(t, tvars),
            _ => false,
        }
    }
    let (cls, name, desc) = match &*e {
        Expr::Method { cls, name, desc, .. } => (cls.clone(), name.clone(), desc.clone()),
        _ => return,
    };
    let want_desc = format!(
        "({}){}",
        desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
        desc.ret.to_descriptor()
    );
    let dpc;
    let dref: &PoolClass = if cls == pc.internal_name {
        pc
    } else {
        dpc = match pool.get(&cls) {
            Some(p) => p,
            None => return,
        };
        &dpc
    };
    let Some(mi) = (0..dref.cf.methods.len())
        .find(|&i| dref.method_name(i) == Some(name.as_str()) && dref.method_desc(i) == Some(want_desc.as_str()))
    else {
        return;
    };
    let Some(sig_bytes) = dref.cf.methods[mi].attributes.iter().find_map(|a| {
        if dref.utf8(a.attribute_name_index) == Some("Signature") {
            Some(a.info.as_slice())
        } else {
            None
        }
    }) else {
        return;
    };
    if sig_bytes.len() < 2 {
        return;
    }
    let Some(msig) = dref
        .utf8(u16::from_be_bytes([sig_bytes[0], sig_bytes[1]]))
        .and_then(|x| parse_method_signature(x))
    else {
        return;
    };
    if msig.params.is_empty() {
        return;
    }
    let tvars: Vec<&str> = msig.params.iter().map(|p| p.name.as_str()).collect();
    let Expr::Method { args, .. } = e else { return };
    // Concrete-pinning scan: a param typevar that ANOTHER arg pins with a
    // concrete type (Arrays.sort(a, c): a:Object[] against param T[])
    // collides with a wildcard-parameterized arg and needs the raw cast;
    // when every co-mentioning arg carries outer typevars/wildcards the
    // inference chain unifies cleanly and the raw cast would SEVER it
    // (jdk17 Collectors.toUnmodifiableMap: toMap((Function) keyMapper,
    // (Function) valueMapper) collapsed the downstream R to Object —
    // "找不到符号 方法 entrySet() 类型为Object的变量 map").
    fn tvar_names(g: &G, out: &mut Vec<String>) {
        match g {
            G::TypeVar(n) => out.push(n.clone()),
            G::Array(i) => tvar_names(i, out),
            G::Class(cs) => cs
                .parts
                .iter()
                .for_each(|p| p.args.iter().for_each(|a| tvar_names(a, out))),
            G::Wildcard(jcdc_jvm::WildcardBound::Extends(t))
            | G::Wildcard(jcdc_jvm::WildcardBound::Super(t)) => tvar_names(t, out),
            _ => {}
        }
    }
    fn carries_tvar_or_wildcard(t: &TypeRef) -> bool {
        match t {
            TypeRef::G(g) => match g {
                G::TypeVar(_) | G::Wildcard(_) => true,
                G::Array(i) => carries_tvar_or_wildcard(&TypeRef::G(*i.clone())),
                G::Class(cs) => cs
                    .parts
                    .iter()
                    .any(|p| p.args.iter().any(|a| carries_tvar_or_wildcard(&TypeRef::G(a.clone())))),
                _ => false,
            },
            _ => false,
        }
    }
    let pinned: Vec<bool> = {
        let arg_types: Vec<TypeRef> = args.iter().map(|x| x.type_ref()).collect();
        msig.args
            .iter()
            .enumerate()
            .map(|(i, pt)| {
                let mut tvs_i: Vec<String> = Vec::new();
                tvar_names(pt, &mut tvs_i);
                if tvs_i.is_empty() {
                    return false;
                }
                (0..args.len()).any(|j| {
                    if j == i {
                        return false;
                    }
                    let mut tvs_j: Vec<String> = Vec::new();
                    tvar_names(&msig.args[j], &mut tvs_j);
                    let shares = tvs_j.iter().any(|n| tvs_i.contains(n));
                    shares && !carries_tvar_or_wildcard(&arg_types[j])
                })
            })
            .collect()
    };
    for (idx, (a, pt)) in args.iter_mut().zip(msig.args.iter()).enumerate() {
        let G::Class(cw) = pt else { continue };
        if cw.parts.iter().all(|p| p.args.is_empty()) || !has_tvar(pt, &tvars) {
            continue;
        }
        if matches!(a, Expr::Cast { .. } | Expr::Const(_)) {
            continue;
        }
        let ca = match a.type_ref() {
            TypeRef::G(G::Class(ca)) if !ca.parts.iter().all(|p| p.args.is_empty()) => ca,
            _ => continue,
        };
        // Only WILDCARD-parameterized arguments doom unification (a
        // capture cannot be named by an inference variable): a typevar-
        // parameterized arg (Class<T_outer> into Class<T_callee>) unifies
        // cleanly and the raw cast would force an unchecked call whose
        // erased return then fails its generic target (jdk26
        // AnnotatedElement: `(Class) annotationClass` made the callee
        // return Annotation[] against a T[] local).
        if !g_has_wildcard(&G::Class(ca.clone())) {
            continue;
        }
        if crate::method::classsig_internal(&ca) != crate::method::classsig_internal(cw) {
            continue;
        }
        if !pinned[idx] {
            continue;
        }
        let raw = TypeRef::J(jcdc_jvm::JavaType::Object(crate::method::classsig_internal(&ca)));
        let inner = std::mem::replace(a, Expr::This);
        *a = Expr::Cast { ty: raw, e: Box::new(inner) };
    }
}

/// Cast call arguments that land in wildcard/typevar parameter positions
/// but carry only their erasure (`action.accept((K) entry.key, ...)`).
/// Instantiated ctor parameter types for `new X<..>(args)` when the New
/// carries its instantiated generic type: the class Signature's params
/// substituted with the instantiation arguments (jdk11 ClassValue
/// refreshVersion: `new Entry<>(v2, (T) value)` — the erased `(T)` cast
/// leaves no bytecode trace, and without it the diamond gets Object
/// against T: "cannot infer type arguments for Entry<>").
fn instantiated_ctor_params(e: &Expr, pool: &ClassPool) -> Option<Vec<jcdc_jvm::GenericType>> {
    let Expr::New { cls, ty, args, .. } = e else { return None };
    let TypeRef::G(jcdc_jvm::GenericType::Class(cs)) = ty else { return None };
    let part = cs.parts.last()?;
    if part.args.is_empty() {
        return None;
    }
    instantiated_ctor_params_core(cls, &part.args, args.len(), pool)
}

fn instantiated_ctor_params_core(
    cls: &str,
    inst_args: &[jcdc_jvm::GenericType],
    nargs: usize,
    pool: &ClassPool,
) -> Option<Vec<jcdc_jvm::GenericType>> {
    let dpc = pool.get(cls)?;
    let class_sig = dpc.class_attr("Signature").and_then(|b| {
        if b.len() >= 2 {
            dpc.utf8(u16::from_be_bytes([b[0], b[1]])).and_then(|x| parse_class_signature(x))
        } else {
            None
        }
    })?;
    if class_sig.params.len() != inst_args.len() {
        return None;
    }
    let mi = (0..dpc.cf.methods.len()).find(|&i| {
        dpc.method_name(i) == Some("<init>")
            && dpc
                .method_desc(i)
                .and_then(|d| parse_method_descriptor(d))
                .map(|md| md.args.len() == nargs)
                .unwrap_or(false)
    })?;
    let sig_bytes = dpc.cf.methods[mi].attributes.iter().find_map(|a| {
        if dpc.utf8(a.attribute_name_index) == Some("Signature") {
            Some(a.info.as_slice())
        } else {
            None
        }
    })?;
    if sig_bytes.len() < 2 {
        return None;
    }
    let msig = dpc
        .utf8(u16::from_be_bytes([sig_bytes[0], sig_bytes[1]]))
        .and_then(|x| parse_method_signature(x))?;
    let inst: Vec<jcdc_jvm::GenericType> = msig
        .args
        .iter()
        .map(|t| crate::method::subst_typevars(t, &class_sig.params, inst_args))
        .collect();
    if inst.iter().any(crate::method::has_nested_wildcard) {
        return None;
    }
    Some(inst)
}

/// Apply per-argument source casts for a call/ctor whose instantiated
/// parameter types are known (see cast_wildcard_call_args).
fn apply_param_casts(args: &mut [Expr], params: &[jcdc_jvm::GenericType], pool: &ClassPool) {
    fn parameterized(t: &jcdc_jvm::GenericType) -> bool {
        match t {
            jcdc_jvm::GenericType::Class(cs) => cs.parts.iter().any(|p| !p.args.is_empty()),
            jcdc_jvm::GenericType::Array(i) => parameterized(i),
            _ => false,
        }
    }
    for (a, pt) in args.iter_mut().zip(params.iter()) {
                    fn parameterized(t: &jcdc_jvm::GenericType) -> bool {
                        match t {
                            jcdc_jvm::GenericType::Class(cs) => {
                                cs.parts.iter().any(|p| !p.args.is_empty())
                            }
                            jcdc_jvm::GenericType::Array(i) => parameterized(i),
                            _ => false,
                        }
                    }
                    let want = match pt {
                        jcdc_jvm::GenericType::TypeVar(_) => Some(pt.clone()),
                        jcdc_jvm::GenericType::Wildcard(jcdc_jvm::WildcardBound::Extends(t))
                        | jcdc_jvm::GenericType::Wildcard(jcdc_jvm::WildcardBound::Super(t)) => {
                            match t.as_ref() {
                                jcdc_jvm::GenericType::TypeVar(_)
                                | jcdc_jvm::GenericType::Class(_) => Some((**t).clone()),
                                _ => None,
                            }
                        }
                        // A parameterized parameter type (`BiFunction<? super
                        // String, ...>`): an argument whose erasure matches
                        // but whose parameters differ needs the source cast.
                        t @ (jcdc_jvm::GenericType::Class(_) | jcdc_jvm::GenericType::Array(_))
                            if parameterized(t) =>
                        {
                            Some(t.clone())
                        }
                        _ => None,
                    };
                    let Some(want) = want else { continue };
                    // Generic-method arguments infer their own type at the
                    // call site; a frozen cast would break unification.
                    if is_generic_call(a, pool) {
                        continue;
                    }
                    // Different parameterized classes (LinkedHashMap<..> →
                    // Map<..>): the original compiled without a cast via
                    // subtyping/inference; inserting one would fail on
                    // capture identities. A RE-parameterization of the same
                    // class (BiFunction<? super Object,..> → BiFunction<?
                    // super String,..>) still needs the source cast.
                    if let (TypeRef::G(jcdc_jvm::GenericType::Class(ca)),
                        jcdc_jvm::GenericType::Class(cw)) = (a.type_ref(), pt)
                    {
                        if crate::method::classsig_internal(&ca)
                            != crate::method::classsig_internal(cw)
                        {
                            continue;
                        }
                    }
                    // A field read through a wildcard-parameterized owner
                    // (`entry.key` where entry: Entry<?,?>) statically has
                    // a CAPTURE type in javac even though our expression
                    // records the declaring class's type variable; it still
                    // needs the cast.
                    let capture_read = matches!(a, Expr::Field { owner: Some(o), .. }
                        if matches!(o.type_ref(), TypeRef::G(jcdc_jvm::GenericType::Class(cs))
                            if cs.parts.iter().any(|p| p.args.iter().any(
                                |x| matches!(x, jcdc_jvm::GenericType::Wildcard(_))))));
                    if !capture_read && a.type_ref() == TypeRef::G(want.clone()) {
                        continue;
                    }
                    if matches!(a, Expr::Cast { .. } | Expr::Const(_)) {
                        continue;
                    }
                    // Erasures must line up.
                    let have = a.type_ref().erased();
                    let want_er = TypeRef::G(want.clone()).erased();
                    let ok = match (&have, &want_er) {
                        (jcdc_jvm::JavaType::Object(x), jcdc_jvm::JavaType::Object(y)) => x == y,
                        (jcdc_jvm::JavaType::Array(_), jcdc_jvm::JavaType::Array(_)) => true,
                        _ => false,
                    };
                    if !ok {
                        continue;
                    }
                    let inner = std::mem::replace(a, Expr::This);
                    *a = Expr::Cast { ty: TypeRef::G(want), e: Box::new(inner) };
    }
}

fn cast_wildcard_call_args(s: &mut Stmt, pool: &ClassPool, pc: &PoolClass, vt: &crate::varalloc::VarTable) {
    fn fix_expr(e: &mut Expr, pool: &ClassPool, pc: &PoolClass) {
        let params = instantiated_method_params(e, pool, pc);
        if params.is_none() && !matches!(e, Expr::New { .. }) {
            raw_witness_generic_method_args(e, pool, pc);
        }
        witness_ambiguous_lambda_args(e, pool, pc);
        let params = params.or_else(|| instantiated_ctor_params(e, pool));
        if let Some(params) = params {
            match e {
                Expr::Method { args, .. } => apply_param_casts(args, &params, pool),
                Expr::New { args, .. } => apply_param_casts(args, &params, pool),
                _ => {}
            }
        }
        walk_expr_children(e, pool, pc, fix_expr);
    }
    fix_diamond_localdefs(s, vt, pool);
    walk_stmt_exprs(s, pool, pc, fix_expr);
}

/// Diamond news assigned to a generically-declared local: the New's own
/// ty is erased, so take the instantiation from the local's declared
/// type and witness the ctor args from it (jdk11 ClassValue
/// refreshVersion: `Entry<T> e2 = new Entry<>(v2, (T) value)` — the
/// erased `(T)` cast has no bytecode trace; without it the diamond sees
/// Object against T and javac gives up: "cannot infer type arguments
/// for Entry<>").
fn fix_diamond_localdefs(s: &mut Stmt, vt: &crate::varalloc::VarTable, pool: &ClassPool) {
    fn inst_from(ty: &TypeRef, value: &Expr) -> Option<(String, Vec<jcdc_jvm::GenericType>, usize)> {
        let (cls, args) = match value {
            Expr::New { cls, args, .. } => (cls, args),
            Expr::Cast { e, .. } => match &**e {
                Expr::New { cls, args, .. } => (cls, args),
                _ => return None,
            },
            _ => return None,
        };
        // A generics-cast wrapper's own instantiation wins over the
        // declared/erased type.
        let inst_ty = match value {
            Expr::Cast { ty: t @ TypeRef::G(_), .. } => t.clone(),
            _ => ty.clone(),
        };
        match &inst_ty {
            TypeRef::G(jcdc_jvm::GenericType::Class(cs)) => cs
                .parts
                .last()
                .filter(|p| !p.args.is_empty())
                .map(|p| (cls.clone(), p.args.clone(), args.len())),
            _ => None,
        }
    }
    fn apply_to_value(value: &mut Expr, params: &[jcdc_jvm::GenericType], pool: &ClassPool) {
        match value {
            Expr::New { args, .. } => apply_param_casts(args, params, pool),
            Expr::Cast { e, .. } => {
                if let Expr::New { args, .. } = &mut **e {
                    apply_param_casts(args, params, pool);
                }
            }
            _ => {}
        }
    }
    match s {
        Stmt::LocalDef { var, init: Some(value), .. } => {
            if let Some((cls, iargs, n)) = inst_from(&vt.var(*var).ty, value) {
                if let Some(params) = instantiated_ctor_params_core(&cls, &iargs, n, pool) {
                    if let Stmt::LocalDef { init: Some(v), .. } = s {
                        apply_to_value(v, &params, pool);
                    }
                }
            }
        }
        // Ordinary locals are assignments in the AST (declarations are
        // synthesized from the VarTable at print time).
        Stmt::ExprStmt(inner) => {
            let target = match &*inner {
                Expr::Assign { target, value, .. } => match &**target {
                    Expr::Local { var, .. } => inst_from(&vt.var(*var).ty, value),
                    _ => None,
                },
                _ => None,
            };
            if let Some((cls, iargs, n)) = target {
                if let Some(params) = instantiated_ctor_params_core(&cls, &iargs, n, pool) {
                    if let Expr::Assign { value, .. } = &mut *inner {
                        apply_to_value(value, &params, pool);
                    }
                }
            }
        }
        Stmt::Block(v) => v.iter_mut().for_each(|x| fix_diamond_localdefs(x, vt, pool)),
        Stmt::If { then_stmt, else_stmt, .. } => {
            fix_diamond_localdefs(then_stmt, vt, pool);
            if let Some(x) = else_stmt {
                fix_diamond_localdefs(x, vt, pool);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } | Stmt::ForEach { body, .. }
        | Stmt::Labeled { body, .. } | Stmt::Synchronized { body, .. } => {
            fix_diamond_localdefs(body, vt, pool)
        }
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(|i| fix_diamond_localdefs(i, vt, pool));
            fix_diamond_localdefs(body, vt, pool);
        }
        Stmt::Switch { cases, default, .. } => {
            for c in cases.iter_mut() {
                c.body.iter_mut().for_each(|st| fix_diamond_localdefs(st, vt, pool));
            }
            if let Some(d) = default {
                fix_diamond_localdefs(d, vt, pool);
            }
        }
        Stmt::Try { body, catches, finally } => {
            fix_diamond_localdefs(body, vt, pool);
            for c in catches.iter_mut() {
                fix_diamond_localdefs(&mut c.body, vt, pool);
            }
            if let Some(f) = finally {
                fix_diamond_localdefs(f, vt, pool);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for r in resources.iter_mut() {
                fix_diamond_localdefs(r, vt, pool);
            }
            fix_diamond_localdefs(body, vt, pool);
            for c in catches.iter_mut() {
                fix_diamond_localdefs(&mut c.body, vt, pool);
            }
            if let Some(f) = finally {
                fix_diamond_localdefs(f, vt, pool);
            }
        }
        _ => {}
    }
}
fn walk_expr_children(
    e: &mut Expr,
    pool: &ClassPool,
    pc: &PoolClass,
    f: fn(&mut Expr, &ClassPool, &PoolClass),
) {
    match e {
        Expr::Method { owner, args, .. } => {
            if let Some(o) = owner {
                f(o, pool, pc);
            }
            args.iter_mut().for_each(|a| f(a, pool, pc));
        }
        Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
            args.iter_mut().for_each(|a| f(a, pool, pc))
        }
        Expr::Field { owner: Some(o), .. } => f(o, pool, pc),
        Expr::ArrayIndex { array, index } => {
            f(array, pool, pc);
            f(index, pool, pc);
        }
        Expr::Cast { e: i, .. } | Expr::InstanceOf { e: i, .. } | Expr::Un { e: i, .. }
        | Expr::PreIncDec { e: i, .. } | Expr::PostIncDec { e: i, .. } => f(i, pool, pc),
        Expr::Bin { l, r, .. } => {
            f(l, pool, pc);
            f(r, pool, pc);
        }
        Expr::Cond { c, t, f: ff } => {
            f(c, pool, pc);
            f(t, pool, pc);
            f(ff, pool, pc);
        }
        Expr::Assign { target, value, .. } => {
            f(target, pool, pc);
            f(value, pool, pc);
        }
        Expr::NewArray { dims, init, .. } => {
            dims.iter_mut().for_each(|d| f(d, pool, pc));
            if let Some(vals) = init {
                vals.iter_mut().for_each(|v| f(v, pool, pc));
            }
        }
        Expr::StringConcat(parts) => parts.iter_mut().for_each(|p| {
            if let crate::expr::ConcatPart::Str(i) = p {
                f(i, pool, pc);
            }
        }),
        Expr::Lambda(l) => l.captures.iter_mut().for_each(|c| f(c, pool, pc)),
        Expr::Invokedynamic { args, .. } => args.iter_mut().for_each(|a| f(a, pool, pc)),
        _ => {}
    }
}

fn walk_stmt_exprs(
    s: &mut Stmt,
    pool: &ClassPool,
    pc: &PoolClass,
    f: fn(&mut Expr, &ClassPool, &PoolClass),
) {
    match s {
        Stmt::Block(v) => v.iter_mut().for_each(|x| walk_stmt_exprs(x, pool, pc, f)),
        Stmt::ExprStmt(e) => f(e, pool, pc),
        Stmt::LocalDef { init: Some(e), .. } => f(e, pool, pc),
        Stmt::Return(e) => {
            if let Some(x) = e {
                f(x, pool, pc);
            }
        }
        Stmt::Throw(e) => f(e, pool, pc),
        Stmt::If { cond, then_stmt, else_stmt } => {
            f(cond, pool, pc);
            walk_stmt_exprs(then_stmt, pool, pc, f);
            if let Some(e) = else_stmt {
                walk_stmt_exprs(e, pool, pc, f);
            }
        }
        Stmt::While { cond, body } | Stmt::DoWhile { body, cond } => {
            f(cond, pool, pc);
            walk_stmt_exprs(body, pool, pc, f);
        }
        Stmt::For { init, cond, update, body } => {
            init.iter_mut().for_each(|i| walk_stmt_exprs(i, pool, pc, f));
            if let Some(c) = cond {
                f(c, pool, pc);
            }
            update.iter_mut().for_each(|u| f(u, pool, pc));
            walk_stmt_exprs(body, pool, pc, f);
        }
        Stmt::ForEach { iterable, body, .. } => {
            f(iterable, pool, pc);
            walk_stmt_exprs(body, pool, pc, f);
        }
        Stmt::Switch { selector, cases, default, .. } => {
            f(selector, pool, pc);
            for c in cases.iter_mut() {
                c.body.iter_mut().for_each(|x| walk_stmt_exprs(x, pool, pc, f));
            }
            if let Some(d) = default {
                walk_stmt_exprs(d, pool, pc, f);
            }
        }
        Stmt::Try { body, catches, finally } => {
            walk_stmt_exprs(body, pool, pc, f);
            for c in catches.iter_mut() {
                walk_stmt_exprs(&mut c.body, pool, pc, f);
            }
            if let Some(fl) = finally {
                walk_stmt_exprs(fl, pool, pc, f);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for r in resources.iter_mut() {
                walk_stmt_exprs(r, pool, pc, f);
            }
            walk_stmt_exprs(body, pool, pc, f);
            for c in catches.iter_mut() {
                walk_stmt_exprs(&mut c.body, pool, pc, f);
            }
            if let Some(fl) = finally {
                walk_stmt_exprs(fl, pool, pc, f);
            }
        }
        Stmt::Synchronized { lock, body } => {
            f(lock, pool, pc);
            walk_stmt_exprs(body, pool, pc, f);
        }
        Stmt::Labeled { body, .. } => walk_stmt_exprs(body, pool, pc, f),
        _ => {}
    }
}

/// `return (Iterator<Entry<K,V>>) getIterator(2);` — a cast cannot drive
/// type inference for a generic method; replace it with an explicit type
/// witness `getIterator::<...>` rendered as `.<T>name(...)`, and drop the
/// now-redundant cast.
/// True when any argument (recursively) is a `new` of a GENERIC class:
/// such a diamond is inference-sensitive, and an explicit type witness on
/// the enclosing call would give it contradictory bounds ("无法推断
/// ArrayList<>的类型参数", jdk17 Stream.toList `Collections.<T>
/// unmodifiableList(new ArrayList<>(Arrays.asList(toArray())))` — the
/// bare call plus the erasure cast is the compilable source form).
fn args_have_generic_new(args: &[Expr], pool: &ClassPool) -> bool {
    fn has(e: &Expr, pool: &ClassPool) -> bool {
        match e {
            Expr::New { cls, args, .. } => {
                if is_generic_class(cls, pool) {
                    return true;
                }
                args.iter().any(|a| has(a, pool))
            }
            Expr::AnonNew { args, .. } => args.iter().any(|a| has(a, pool)),
            Expr::Method { owner, args, .. } => {
                owner.as_deref().map(|o| has(o, pool)).unwrap_or(false)
                    || args.iter().any(|a| has(a, pool))
            }
            Expr::Cast { e: x, .. }
            | Expr::Un { e: x, .. }
            | Expr::InstanceOf { e: x, .. } => has(x, pool),
            Expr::Cond { c, t, f } => has(c, pool) || has(t, pool) || has(f, pool),
            Expr::Bin { l, r, .. } => has(l, pool) || has(r, pool),
            Expr::ArrayIndex { array, index } => has(array, pool) || has(index, pool),
            Expr::NewArray { dims, init, .. } => {
                dims.iter().any(|d| has(d, pool))
                    || init.as_ref().map(|v| v.iter().any(|x| has(x, pool))).unwrap_or(false)
            }
            _ => false,
        }
    }
    args.iter().any(|a| has(a, pool))
}

fn is_generic_class(cls: &str, pool: &ClassPool) -> bool {
    pool.get(cls)
        .map(|pcx| {
            pcx.class_attr("Signature")
                .map(|b| {
                    b.len() >= 2
                        && pcx
                            .utf8(u16::from_be_bytes([b[0], b[1]]))
                            .and_then(|s| parse_class_signature(s))
                            .map(|sig| !sig.params.is_empty())
                            .unwrap_or(false)
                })
                .unwrap_or(false)
        })
        .unwrap_or(false)
}

fn add_return_witnesses(s: &mut Stmt, msig: Option<&jcdc_jvm::MethodSignature>, pool: &ClassPool) {
    let Some(sig) = msig else { return };
    fn walk(s: &mut Stmt, sig: &jcdc_jvm::MethodSignature, pool: &ClassPool) {
        match s {
            Stmt::Block(v) => v.iter_mut().for_each(|x| walk(x, sig, pool)),
            Stmt::Return(Some(e)) => fix_ret(e, sig, pool),
            Stmt::If { then_stmt, else_stmt, .. } => {
                walk(then_stmt, sig, pool);
                if let Some(e) = else_stmt {
                    walk(e, sig, pool);
                }
            }
            Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => walk(body, sig, pool),
            Stmt::For { init, body, .. } => {
                init.iter_mut().for_each(|i| walk(i, sig, pool));
                walk(body, sig, pool);
            }
            Stmt::ForEach { body, .. } => walk(body, sig, pool),
            Stmt::Switch { cases, default, .. } => {
                for c in cases.iter_mut() {
                    c.body.iter_mut().for_each(|x| walk(x, sig, pool));
                }
                if let Some(d) = default {
                    walk(d, sig, pool);
                }
            }
            Stmt::Try { body, catches, finally } => {
                walk(body, sig, pool);
                for c in catches.iter_mut() {
                    walk(&mut c.body, sig, pool);
                }
                if let Some(f) = finally {
                    walk(f, sig, pool);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                for r in resources.iter_mut() {
                    walk(r, sig, pool);
                }
                walk(body, sig, pool);
                for c in catches.iter_mut() {
                    walk(&mut c.body, sig, pool);
                }
                if let Some(f) = finally {
                    walk(f, sig, pool);
                }
            }
            Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => walk(body, sig, pool),
            _ => {}
        }
    }
    fn fix_ret(e: &mut Expr, sig: &jcdc_jvm::MethodSignature, pool: &ClassPool) {
        // (Target) callExpr  →  callExpr with witnesses
        let mut had_cast = false;
        let witness = {
            let slot: &mut Expr = match e {
                Expr::Cast { e: inner, .. } if matches!(&**inner, Expr::Method { .. }) => {
                    had_cast = true;
                    inner.as_mut()
                }
                Expr::Method { .. } => e,
                _ => return,
            };
            let want = match &sig.ret {
                jcdc_jvm::GenericType::TypeVar(_) | jcdc_jvm::GenericType::Class(_)
                | jcdc_jvm::GenericType::Array(_) => &sig.ret,
                _ => return,
            };
            match &mut *slot {
                Expr::Method { cls, name, desc, type_args, owner, args, .. } if type_args.is_empty() => {
                    if args_have_generic_new(args, pool) {
                        None
                    } else {
                        compute_witness(cls.as_str(), name.as_str(), desc, owner.as_deref(), want, pool, Some(&sig.params))
                    }
                }
                _ => None,
            }
        };
        if let Some((w, mapping)) = witness {
            match e {
                Expr::Cast { e: inner, .. } => {
                    if let Expr::Method { type_args, cls, name, desc, args, .. } = &mut **inner {
                        *type_args = w;
                        retype_witness_arg_casts(cls, name, desc, args, &mapping, pool);
                    }
                }
                Expr::Method { type_args, cls, name, desc, args, .. } => {
                    *type_args = w;
                    retype_witness_arg_casts(cls, name, desc, args, &mapping, pool);
                }
                _ => {}
            }
            if had_cast {
                let inner = match std::mem::replace(e, Expr::This) {
                    Expr::Cast { e: inner, .. } => *inner,
                    other => other,
                };
                *e = inner;
            }
        }
    }
    walk(s, sig, pool);
}

fn compute_witness(
    cls: &str,
    name: &str,
    desc: &jcdc_jvm::MethodDescriptor,
    _owner: Option<&Expr>,
    want: &jcdc_jvm::GenericType,
    pool: &ClassPool,
    caller_params: Option<&[jcdc_jvm::TypeParam]>,
) -> Option<(Vec<String>, Vec<(String, jcdc_jvm::GenericType)>)> {
    let dpc = pool.get(cls)?;
    let want_desc = {
        // descriptor string of the call for matching
        let mut a = String::new();
        for t in &desc.args {
            a.push_str(&t.to_descriptor());
        }
        format!("({}){}", a, desc.ret.to_descriptor())
    };
    let mi = (0..dpc.cf.methods.len())
        .find(|&i| dpc.method_name(i) == Some(name) && dpc.method_desc(i) == Some(want_desc.as_str()))?;
    let sig_bytes = dpc.cf.methods[mi].attributes.iter().find_map(|a| {
        if dpc.utf8(a.attribute_name_index) == Some("Signature") {
            Some(a.info.as_slice())
        } else {
            None
        }
    })?;
    if sig_bytes.len() < 2 {
        return None;
    }
    let idx = u16::from_be_bytes([sig_bytes[0], sig_bytes[1]]);
    let msig = dpc.utf8(idx).and_then(|s| jcdc_jvm::parse_method_signature(s))?;
    if msig.params.is_empty() {
        return None; // not a generic method
    }
    // Match the callee's generic return against the wanted type.
    let mut mapping: Vec<(String, jcdc_jvm::GenericType)> = Vec::new();
    if !unify_types(&msig.ret, want, &mut mapping) {
        return None;
    }
    // Every method type parameter must be bound by the unification, and
    // only to a denotable type — a wildcard bound means inference should
    // come from the call arguments/target instead (keep the cast form).
    fn trivial_bound(p: &jcdc_jvm::TypeParam) -> bool {
        if !p.interface_bounds.is_empty() {
            return false;
        }
        match &p.class_bound {
            None => true,
            Some(jcdc_jvm::GenericType::Class(cs)) => {
                cs.parts.len() == 1 && cs.parts[0].name == "Object" && cs.parts[0].args.is_empty()
            }
            Some(jcdc_jvm::GenericType::TypeVar(_)) => false,
            _ => false,
        }
    }
    let mut out = Vec::with_capacity(msig.params.len());
    for p in &msig.params {
        match mapping.iter().find(|(n, _)| n == &p.name) {
            Some((_, jcdc_jvm::GenericType::Wildcard(_))) => return None,
            Some((_, t @ jcdc_jvm::GenericType::TypeVar(tn))) => {
                // An explicit type argument must SATISFY the callee's
                // declared bound: `Collections.<T>min(..)` where min
                // requires `T extends Comparable<? super T>` and the
                // caller's own T is unbound is rejected by javac
                // ("explicit type argument T does not conform"). Without
                // the witness, inference falls back to the raw-cast form
                // the source used (`(T) min((Collection) coll)`).
                if !trivial_bound(p) {
                    let caller_bounded = caller_params
                        .and_then(|cps| cps.iter().find(|cp| &cp.name == tn))
                        .map(|cp| !trivial_bound(cp))
                        .unwrap_or(true); // unknown caller: keep old behavior
                    if !caller_bounded {
                        return None;
                    }
                }
                out.push(t.to_java());
            }
            Some((_, t)) => out.push(t.to_java()),
            None => return None,
        }
    }
    Some((out, mapping))
}

/// With a call's type witnesses known, retype raw-erasure argument casts
/// (`(Class) x`) to the instantiated parameter type (`(Class<E>) x`).
fn retype_witness_arg_casts(
    cls: &str,
    name: &str,
    desc: &jcdc_jvm::MethodDescriptor,
    args: &mut [Expr],
    mapping: &[(String, jcdc_jvm::GenericType)],
    pool: &ClassPool,
) {
    let Some(dpc) = pool.get(cls) else { return };
    let want_desc = {
        let mut a = String::new();
        for t in &desc.args {
            a.push_str(&t.to_descriptor());
        }
        format!("({}){}", a, desc.ret.to_descriptor())
    };
    let Some(mi) = (0..dpc.cf.methods.len()).find(|&i| {
        dpc.method_name(i) == Some(name) && dpc.method_desc(i) == Some(want_desc.as_str())
    }) else { return };
    let Some(sig_bytes) = dpc.cf.methods[mi].attributes.iter().find_map(|a| {
        if dpc.utf8(a.attribute_name_index) == Some("Signature") {
            Some(a.info.as_slice())
        } else {
            None
        }
    }) else { return };
    if sig_bytes.len() < 2 {
        return;
    }
    let idx = u16::from_be_bytes([sig_bytes[0], sig_bytes[1]]);
    let Some(msig) = dpc.utf8(idx).and_then(|s| jcdc_jvm::parse_method_signature(s)) else { return };
    let params: Vec<jcdc_jvm::TypeParam> = mapping
        .iter()
        .map(|(n, t)| jcdc_jvm::TypeParam {
            name: n.clone(),
            class_bound: Some(t.clone()),
            interface_bounds: Vec::new(),
        })
        .collect();
    let arg_tys: Vec<jcdc_jvm::GenericType> = mapping
        .iter()
        .map(|(_, t)| t.clone())
        .collect();
    fn parameterized(t: &jcdc_jvm::GenericType) -> bool {
        match t {
            jcdc_jvm::GenericType::Class(cs) => cs.parts.iter().any(|p| !p.args.is_empty()),
            jcdc_jvm::GenericType::Array(i) => parameterized(i),
            // An array OF a type variable (`T[]`) is generic — skipping it
            // left the erasure checkcast around a generic-call argument
            // in place: jdk Collection.toArray(IntFunction) rendered
            // `this.<T>toArray((Object[]) generator.apply(0))` — with the
            // explicit witness pinning the formal to T[], the Object[]
            // cast made the call inapplicable ("no suitable method").
            jcdc_jvm::GenericType::TypeVar(_) => true,
            _ => false,
        }
    }
    for (a, pt) in args.iter_mut().zip(msig.args.iter()) {
        let inst = crate::method::subst_typevars(pt, &params, &arg_tys);
        if !parameterized(&inst) && !matches!(inst, jcdc_jvm::GenericType::TypeVar(_)) {
            continue;
        }
        let inst_ref = TypeRef::G(inst.clone());
        match a {
            Expr::Cast { ty, e: ce } => {
                if is_generic_call(ce, pool) {
                    // A raw checkcast around a generic call would make the
                    // whole outer call an unchecked erasure-invocation; the
                    // source relies on target-type inference instead — drop
                    // the cast and let inference run.
                    if ty.erased() == inst_ref.erased() {
                        let inner = std::mem::replace(a, Expr::This);
                        if let Expr::Cast { e: ce2, .. } = inner {
                            *a = *ce2;
                        }
                    }
                } else if inst_ref.erased() == ty.erased() && *ty != inst_ref {
                    *ty = inst_ref.clone();
                }
            }
            Expr::Const(_) => {}
            other => {
                // An argument whose static type is only the erasure (or a
                // capture) needs the source cast to the instantiated
                // parameter type — unless it is itself a generic call whose
                // type inference handles the position.
                if !is_generic_call(other, pool)
                    && other.type_ref() != inst_ref
                    && other.type_ref().erased() == inst_ref.erased()
                {
                    let inner = std::mem::replace(other, Expr::This);
                    *other = Expr::Cast { ty: inst_ref, e: Box::new(inner) };
                }
            }
        }
    }
}

fn unify_types(
    have: &jcdc_jvm::GenericType,
    want: &jcdc_jvm::GenericType,
    map: &mut Vec<(String, jcdc_jvm::GenericType)>,
) -> bool {
    use jcdc_jvm::GenericType as G;
    if let G::TypeVar(n) = have {
        if let Some((_, prev)) = map.iter().find(|(m, _)| m == n) {
            return prev == want;
        }
        map.push((n.clone(), want.clone()));
        return true;
    }
    match (have, want) {
        (G::Array(a), G::Array(b)) => unify_types(a, b, map),
        (G::Class(ca), G::Class(cb)) => {
            if ca.parts.len() != cb.parts.len() {
                return false;
            }
            for (pa, pb) in ca.parts.iter().zip(cb.parts.iter()) {
                if pa.name != pb.name || pa.args.len() != pb.args.len() {
                    return false;
                }
                for (x, y) in pa.args.iter().zip(pb.args.iter()) {
                    if !unify_types(x, y, map) {
                        return false;
                    }
                }
            }
            true
        }
        (a, b) => a == b,
    }
}

fn cast_generic_returns(s: &mut Stmt, want: &TypeRef, pc: &PoolClass) {
    fn fix(e: &mut Expr, want: &TypeRef, pc: &PoolClass) {
        if matches!(e, Expr::Const(_)) {
            return;
        }
        let compatible = |have_er: &jcdc_jvm::JavaType, want_er: &jcdc_jvm::JavaType| {
            match (have_er, want_er) {
                (jcdc_jvm::JavaType::Array(a), jcdc_jvm::JavaType::Array(b)) => {
                    matches!(&**a, jcdc_jvm::JavaType::Object(_))
                        || matches!(&**b, jcdc_jvm::JavaType::Object(_))
                        || a == b
                }
                (jcdc_jvm::JavaType::Object(x), jcdc_jvm::JavaType::Object(y)) => x == y,
                _ => false,
            }
        };
        // An existing checkcast carries the erasure (`(Object[])`); retype
        // it to the generic target (`(T[])`) when the erasures line up.
        if let Expr::Cast { ty, .. } = e {
            if matches!(want, TypeRef::G(_))
                && *ty != *want
                && compatible(&ty.erased(), &want.erased())
            {
                *ty = want.clone();
            }
            return;
        }
        if e.type_ref() == *want {
            return;
        }
        // Only cast when the erasures line up (avoid nonsense casts).
        // `this` erases to the enclosing class, not java/lang/Object.
        let have_er = if matches!(e, Expr::This) {
            jcdc_jvm::JavaType::Object(pc.internal_name.clone())
        } else {
            e.type_ref().erased()
        };
        let want_er = want.erased();
        if !compatible(&have_er, &want_er) {
            return;
        }
        let inner = std::mem::replace(e, Expr::This);
        *e = Expr::Cast { ty: want.clone(), e: Box::new(inner) };
    }
    match s {
        Stmt::Block(v) => v.iter_mut().for_each(|x| cast_generic_returns(x, want, pc)),
        Stmt::Return(Some(e)) => fix(e, want, pc),
        Stmt::If { then_stmt, else_stmt, .. } => {
            cast_generic_returns(then_stmt, want, pc);
            if let Some(x) = else_stmt {
                cast_generic_returns(x, want, pc);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => cast_generic_returns(body, want, pc),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(|i| cast_generic_returns(i, want, pc));
            cast_generic_returns(body, want, pc);
        }
        Stmt::ForEach { body, .. } => cast_generic_returns(body, want, pc),
        Stmt::Try { body, catches, finally } => {
            cast_generic_returns(body, want, pc);
            for c in catches {
                cast_generic_returns(&mut c.body, want, pc);
            }
            if let Some(f) = finally {
                cast_generic_returns(f, want, pc);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { cast_generic_returns(res, want, pc); }
            cast_generic_returns(body, want, pc);
            for c in catches {
                cast_generic_returns(&mut c.body, want, pc);
            }
            if let Some(f) = finally {
                cast_generic_returns(f, want, pc);
            }
        }
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(|st| cast_generic_returns(st, want, pc));
            }
            if let Some(d) = default {
                cast_generic_returns(d, want, pc);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => {
            cast_generic_returns(body, want, pc)
        }
        _ => {}
    }
}
