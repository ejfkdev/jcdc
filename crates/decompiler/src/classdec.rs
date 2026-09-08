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
        if cs.parts.first().map(|q| q.name == "Object" || q.name == "Record").unwrap_or(false));
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

    /// Simple name -> internal name of local classes declared in the
    /// method frame being emitted: the marker New (`\u{2}Name`) carries
    /// only the simple name, but typed ctor-arg rendering needs the
    /// class. Method-scoped (two same-simple local classes cannot
    /// coexist in one method; across methods the frame save/restore
    /// keeps the lookup exact).
    static LOCAL_CLASS_INTERNALS: std::cell::RefCell<HashMap<String, String>> =
        std::cell::RefCell::new(HashMap::new());

    /// Class-level typevar names that are OUT OF SCOPE at the emission
    /// site (static methods/clinit): unsubstituted field-signature types
    /// must not be cast to them ("无法从静态上下文中引用非静态 类型
    /// 变量 K", jdk26 ReferencedKeyMap.internKey putIfAbsent).
    static CAST_BANNED_TVARS: std::cell::RefCell<Vec<String>> =
        std::cell::RefCell::new(Vec::new());

    /// Capture TEXT -> first known GENERIC type: the winning local-class
    /// emission is often the fix_lambda_captures throwaway walk, whose vt
    /// carries erased lambda-param types; a later site (the outer method
    /// body) knows the declared generic type. The witness upgrade below
    /// runs per emission, so the recorded type upgrades every string
    /// rendered afterwards.
    static CAPTURE_GENERIC_TYPES: std::cell::RefCell<HashMap<String, TypeRef>> =
        std::cell::RefCell::new(HashMap::new());
}

fn g_mentions_tvar_named(g: &jcdc_jvm::GenericType, names: &[String]) -> bool {
    use jcdc_jvm::GenericType as G;
    match g {
        G::TypeVar(n) => names.iter().any(|b| b == n),
        G::Array(i) => g_mentions_tvar_named(i, names),
        G::Class(cs) => cs
            .parts
            .iter()
            .any(|p| p.args.iter().any(|a| g_mentions_tvar_named(a, names))),
        G::Wildcard(jcdc_jvm::WildcardBound::Extends(t))
        | G::Wildcard(jcdc_jvm::WildcardBound::Super(t)) => g_mentions_tvar_named(t, names),
        _ => false,
    }
}

fn class_typevar_names(pc: &PoolClass) -> Vec<String> {
    pc.class_attr("Signature")
        .and_then(|b| {
            if b.len() >= 2 {
                pc.utf8(u16::from_be_bytes([b[0], b[1]]))
                    .and_then(|x| parse_class_signature(x))
            } else {
                None
            }
        })
        .map(|sig| sig.params.iter().map(|p| p.name.clone()).collect())
        .unwrap_or_default()
}

pub(crate) fn local_class_internal(simple: &str) -> Option<String> {
    LOCAL_CLASS_INTERNALS.with(|m| m.borrow().get(simple).cloned())
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
                {
                    let banned = class_typevar_names(pc);
                    CAST_BANNED_TVARS.with(|b| *b.borrow_mut() = banned);
                    cast_wildcard_call_args(&mut body, pool, pc, &mb.vt, &[]);
                    CAST_BANNED_TVARS.with(|b| b.borrow_mut().clear());
                }
                fix_lambda_captures(&mut body, &mut mb.vt, pc, pool, fam);
                restore_enum_switches(&mut body, pc, pool);
                fold_restart_guards(&mut body);
                hoist_clinit_returns(&mut body);
                prune_tail_bare_returns(&mut body);
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
                        fold_restart_guards(&mut body);
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
        // Synthetic outer-instance constructor of a member inner class —
        // only when it is the class's SOLE ctor: javac mirrors every
        // source ctor with an outer-param variant and synthesizes a
        // default only when the source declares none. With siblings, the
        // trivial one IS the source no-arg ctor; skipping it left
        // `new Inet6AddressHolder()` against a 5-param-only class (jdk11
        // Inet6Address, 5 errors).
        if name == "<init>" && class_has_this0(pc) && is_trivial_inner_ctor(pc, pool, mi) {
            let nctors = (0..pc.cf.methods.len())
                .filter(|&m| pc.method_name(m) == Some("<init>"))
                .count();
            if nctors == 1 {
                skip.insert(mi);
            }
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
        Stmt::ExprStmt(Expr::Method { name: n, args, .. }) if n == "<init>" => {
                args.len() <= 2
                    && args.iter().all(|a| matches!(a, Expr::This | Expr::Local { .. }))
            }
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

pub(crate) fn class_has_this0(pc: &PoolClass) -> bool {
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
                    Stmt::ExprStmt(Expr::Method { name: n, cls, args, .. })
                        if n == "<init>" && cls != &pc.internal_name =>
                    {
                        // Only a synthetic delegation (outer-instance /
                        // marker passthrough) is trivial: super(outer,
                        // SRC_BIDI) carries a source-level super call
                        // (jdk11 UCharacterProperty BiDiIntProperty's ctor
                        // vanished, leaving the class without one).
                        args.len() <= 2
                            && args
                                .iter()
                                .all(|a| matches!(a, Expr::This | Expr::Local { .. }))
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
                    Stmt::ExprStmt(Expr::Method { name: n, cls, args, .. })
                        if n == "<init>" && cls != &pc.internal_name =>
                    {
                        // Only a synthetic delegation (outer-instance /
                        // marker passthrough) is trivial: super(outer,
                        // SRC_BIDI) carries a source-level super call
                        // (jdk11 UCharacterProperty BiDiIntProperty's ctor
                        // vanished, leaving the class without one).
                        args.len() <= 2
                            && args
                                .iter()
                                .all(|a| matches!(a, Expr::This | Expr::Local { .. }))
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

/// Instance-final fields whose declaration prints a ConstantValue
/// initializer: javac still emits the putfield into every ctor, which
/// the source form must not keep — the field is final and already
/// initialized ("无法为 final 变量 BITARRAYMASK 分配值" — jdk11
/// MergeCollation x3, ProcessHandleImpl x2, AccessorGenerator x2,
/// jdk17 MemoryCache QueueCacheEntry, jdk26 LinuxRISCV64CallArranger x2).
/// Drop `this.F = <const>;` for exactly those F in ctor bodies.
fn prune_const_final_ctor_assigns(s: &mut Stmt, pc: &PoolClass) {
    let names: HashSet<String> = pc
        .cf
        .fields
        .iter()
        .filter(|f| {
            !f.access_flags.contains(FieldAccessFlags::STATIC)
                && f.access_flags.contains(FieldAccessFlags::FINAL)
                && f.attributes
                    .iter()
                    .any(|a| pc.utf8(a.attribute_name_index) == Some("ConstantValue"))
        })
        .filter_map(|f| pc.utf8(f.name_index).map(|n| n.to_string()))
        .collect();
    if names.is_empty() {
        return;
    }
    fn is_target_assign(st: &Stmt, names: &HashSet<String>) -> bool {
        let Stmt::ExprStmt(Expr::Assign { target, op: crate::expr::AssignOp::Plain, value }) = st
        else {
            return false;
        };
        if !matches!(value.as_ref(), Expr::Const(_)) {
            return false;
        }
        match target.as_ref() {
            Expr::Field { owner, name, is_static: false, .. } => {
                (owner.is_none() || matches!(owner.as_deref(), Some(Expr::This)))
                    && names.contains(name)
            }
            _ => false,
        }
    }
    fn rec(s: &mut Stmt, names: &HashSet<String>) {
        match s {
            Stmt::Block(v) => {
                v.retain(|st| !is_target_assign(st, names));
                v.iter_mut().for_each(|x| rec(x, names));
            }
            Stmt::If { then_stmt, else_stmt, .. } => {
                rec(then_stmt, names);
                if let Some(e) = else_stmt {
                    rec(e, names);
                }
            }
            Stmt::Try { body, catches, finally } => {
                rec(body, names);
                for c in catches.iter_mut() {
                    rec(&mut c.body, names);
                }
                if let Some(f) = finally {
                    rec(f, names);
                }
            }
            Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => rec(body, names),
            _ => {}
        }
    }
    rec(s, &names);
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
            // Before any return-witness machinery: type field reads, drop
            // redundant raw self-casts and upgrade REAL checkcasts to the
            // instantiated returns (later raw-cast fallbacks must not be
            // rewritten — see upgrade_erased_call_casts).
            upgrade_erased_call_casts(&mut body, pool, pc);
            relay_inconvertible_local_casts(&mut body, &mb.vt, pool);
            upgrade_typevar_array_casts(&mut body, pool, pc);
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
                        cast_generic_returns(&mut body, &want, pc, pool);
                        // A cast cannot drive inference for a generic
                        // callee; prefer an explicit type witness.
                        add_return_witnesses(&mut body, Some(sig), pool, pc);
                    }
                    _ => {}
                }
            }
            // Wildcard-parameterized call sites: arguments that carry only
            // their erasure need the source-level cast back (`accept((K) x)`).
            let static_ban = acc.contains(MethodAccessFlags::STATIC);
            if static_ban {
                let banned = class_typevar_names(pc);
                CAST_BANNED_TVARS.with(|b| *b.borrow_mut() = banned);
            }
            let caller_params: Vec<jcdc_jvm::TypeParam> =
                msig.as_ref().map(|m| m.params.clone()).unwrap_or_default();
            cast_wildcard_call_args(&mut body, pool, pc, &mb.vt, &caller_params);
            witness_methodref_localdef_calls(&mut body, &mb.vt, pool, pc, &caller_params);
            pin_underdetermined_return_diamonds(&mut body, msig.as_ref(), pool);
            if static_ban {
                CAST_BANNED_TVARS.with(|b| b.borrow_mut().clear());
            }
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
                prune_const_final_ctor_assigns(&mut body, pc);
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
            // Capture substitution replaces val$/param reads with RawT
            // expressions carrying the OUTER scope's generic types — the
            // earlier generic passes saw only the erased capture shapes
            // (jdk26 LazyCollections LazyMapIterator's anon Consumer:
            // `action.accept(new LazyEntry(..))` with action raw-typed at
            // fix time, so the Consumer<? super Entry<K,V>> formal never
            // instantiated). Retry them on the substituted body (they are
            // idempotent: cast/witness/ty checks skip settled nodes).
            if !captures.is_empty() {
                if static_ban {
                    let banned = class_typevar_names(pc);
                    CAST_BANNED_TVARS.with(|b| *b.borrow_mut() = banned);
                }
                cast_wildcard_call_args(&mut body, pool, pc, &mb.vt, &caller_params);
                witness_methodref_localdef_calls(&mut body, &mb.vt, pool, pc, &caller_params);
                pin_underdetermined_return_diamonds(&mut body, msig.as_ref(), pool);
                if static_ban {
                    CAST_BANNED_TVARS.with(|b| b.borrow_mut().clear());
                }
            }
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
                                Expr::RawT(t, ty) => {
                                    if let Expr::Local { var, .. } = value.as_ref() {
                                        rep.insert(*var, Expr::RawT(t.clone(), ty.clone()));
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
                // The this$0 store kept the trivial super() from being the
                // FIRST statement when strip_trivial_super ran earlier; now
                // that the artifacts are gone, retry (jdk11/17
                // ConcurrentLinkedQueue.Itr: the printed `super();` after
                // the hoisted decls is a pre-22 "灵活构造器" error).
                if is_ctor {
                    strip_trivial_super(&mut body, pc);
                }
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
            fix_diamond_localdefs(&mut body, &mb.vt, pool, pc);
            // Accessor inlining can expose the real generic callee only
            // now; retry the return witnesses (idempotent).
            add_return_witnesses(&mut body, msig.as_ref(), pool, pc);
            restore_enum_switches(&mut body, pc, pool);
            fold_restart_guards(&mut body);
            // Switch restoration reassembles case blocks AFTER the method
            // pipeline: rerun the post-loop label-break prune there (jdk17
            // GregorianCalendar case 2 `L2: do..while; break L2;`) and the
            // undefined-label demotion (jdk11 Pattern slice case-0
            // fall-through compiled to `break L31`).
            crate::method::prune_post_loop_label_breaks(&mut body);
            crate::method::demote_undefined_label_jumps(&mut body);
            split_return_assigns(&mut body);
            disambiguate_catch_collisions(&mut body, &mb.vt);
            // Ctor delegations were still capture-arg-padded when
            // cast_wildcard_call_args ran, and prune_local_ctor_delegation
            // trims the ARGS without rewriting the node's descriptor (the
            // desc-based target lookup then misses). Cast the pruned
            // delegation's erased actuals against the target ctor's
            // typevar formals directly (jdk26 Gatherers Composite State's
            // `this(!arg0 ? arg1.get() : null, ..)` needs the source-elided
            // (A)/(AA) casts — the raw Supplier capture params type the
            // conditionals at Object: "Object无法转换为A").
            cast_pruned_delegation_typevar_args(&mut body, pc, mi);
            add_throw_witnesses(&mut body, msig.as_ref(), pool);
            strip_erasure_casts_generic_ret(&mut body, msig.as_ref(), pool);
            witness_generic_returns(&mut body, msig.as_ref(), pool, pc);
            push_witness_into_branches(&mut body, msig.as_ref(), pool, pc);
            witness_comparison_operands(&mut body, msig.as_ref(), pool);
            // Scope the extern-decl registry to THIS method's emission:
            // names extracted here must suppress re-declaration inside
            // lambda bodies printed below, but must not leak into other
            // methods (common local-class names like State/Spliterator
            // would suppress their legitimate decls — ReferencePipeline
            // +32 errors). Nested emissions (anon bodies) snapshot/restore
            // around themselves, preserving this frame.
            let extern_save = EXTERN_DECL.with(|x| x.borrow().clone());
            let internals_save =
                LOCAL_CLASS_INTERNALS.with(|m| std::mem::take(&mut *m.borrow_mut()));
            let captys_save =
                CAPTURE_GENERIC_TYPES.with(|m| std::mem::take(&mut *m.borrow_mut()));
            fix_lambda_captures(&mut body, &mut mb.vt, pc, pool, fam);
            // Snapshot names: the disambiguation renames OUTER locals whose
            // hoisted decls collide with lambda-scope names, but inlined
            // anon/local bodies capture the OLD names as RawT text (frozen
            // at render time) — stale references (jdk26 UpcallLinker
            // doBindings -> doBindings$1: 找不到符号 x2). Diff the VarTable
            // and rewrite exact-matching RawT texts.
            let names_before: HashMap<u32, String> =
                mb.vt.vars.iter().map(|v| (v.id, v.name.clone())).collect();
            disambiguate_lambda_locals(pc, pool, &mut mb.vt, &mut body);
            {
                let renames: HashMap<String, String> = mb
                    .vt
                    .vars
                    .iter()
                    .filter_map(|v| {
                        names_before
                            .get(&v.id)
                            .and_then(|old| {
                                if *old != v.name {
                                    Some((old.clone(), v.name.clone()))
                                } else {
                                    None
                                }
                            })
                    })
                    .collect();
                if !renames.is_empty() {
                    fn rewrite_rawt(
                        e: &mut Expr,
                        renames: &HashMap<String, String>,
                        pool: &ClassPool,
                        pc: &PoolClass,
                    ) {
                        if let Expr::RawT(text, _) = e {
                            if let Some(n) = renames.get(text.as_str()) {
                                *text = n.clone();
                            }
                        }
                        walk_expr_children(e, pool, pc, &mut |x, p2, c2| {
                            rewrite_rawt(x, renames, p2, c2)
                        });
                    }
                    walk_stmt_exprs(&mut body, pool, pc, &mut |e, p2, c2| {
                        rewrite_rawt(e, &renames, p2, c2)
                    });
                }
            }
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
            // Last moment before printing: labels can be dropped by any
            // earlier reshaping pass, leaving undefined-label breaks.
            crate::method::demote_undefined_label_jumps(&mut body);
            let text = Printer::new(pc, pool, &mb.vt)
                .with_indent(indent + 1)
                .with_ret_bool(ret_bool)
                .with_ret_char(ret_char)
                .with_ret_narrow(ret_byte, ret_short)
                .with_ret_sam(ret_sam)
                .into_string(&body);
            EXTERN_DECL.with(|x| *x.borrow_mut() = extern_save);
            LOCAL_CLASS_INTERNALS.with(|m| *m.borrow_mut() = internals_save);
            CAPTURE_GENERIC_TYPES.with(|m| *m.borrow_mut() = captys_save);
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
            // The outer instance is ALWAYS the first param (slot 1):
            // a bare is_param check ate a real super arg when the super
            // is static-nested and takes none (jdk17 ExplodedImage
            // PathNode(String name, ..) → `super(attrs)` lost name —
            // "需要: String,BasicFileAttributes 找到: BasicFileAttributes").
            let is_outer_local = match &args[0] {
                Expr::Local { var, .. } => {
                    vt.var(*var).name.starts_with("this$")
                        || (vt.var(*var).is_param && vt.var(*var).slot == 1)
                }
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

/// Safety net after hoist_clinit_returns: a bare `return;` left in TAIL
/// position (nothing follows in its block/branch — `if (c) { return; }
/// else { throw ..; }` as the whole clinit, jdk17 ClassLoaders
/// AppClassLoader) is illegal source ("返回外部方法") and dropping it is
/// exactly the fall-through semantics. Non-tail returns are hoist's job;
/// loop bodies never count as tail (dropping there would continue).
/// `return this.f = v;` (javac's dup+putfield+areturn for `this.f = v;
/// return v;`) types the return as the ASSIGNMENT's static type — the
/// field's — which fails a generic method return demanding a subtype
/// (jdk26 LinkedHashMap.sequencedKeySet `return this.keySet = sks;` —
/// Set<K>无法转换为SequencedSet<K>; the source stores then returns the
/// local). Split back into the two-statement form when the value is
/// side-effect-free; since the assign requires value <: field, the split
/// is compilable wherever the merged form was.
pub(crate) fn split_return_assigns(s: &mut Stmt) {
    match s {
        Stmt::Block(v) => {
            let mut i = 0;
            while i < v.len() {
                split_return_assigns(&mut v[i]);
                let mut replaced: Option<(Stmt, Stmt)> = None;
                if let Stmt::Return(Some(Expr::Assign { target, op, value })) = &v[i] {
                    if matches!(op, crate::expr::AssignOp::Plain)
                        && matches!(&**value, Expr::Local { .. } | Expr::Const(_) | Expr::This)
                    {
                        replaced = Some((
                            Stmt::ExprStmt(Expr::Assign {
                                target: target.clone(),
                                op: op.clone(),
                                value: value.clone(),
                            }),
                            Stmt::Return(Some((**value).clone())),
                        ));
                    }
                }
                if let Some((a, b)) = replaced {
                    v[i] = a;
                    v.insert(i + 1, b);
                    i += 1;
                }
                i += 1;
            }
        }
        Stmt::Return(Some(inner @ Expr::Assign { .. })) => {
            if let Expr::Assign { target, op, value } = &*inner {
                if matches!(op, crate::expr::AssignOp::Plain)
                    && matches!(&**value, Expr::Local { .. } | Expr::Const(_) | Expr::This)
                {
                    let a = Stmt::ExprStmt(Expr::Assign {
                        target: target.clone(),
                        op: op.clone(),
                        value: value.clone(),
                    });
                    let b = Stmt::Return(Some((**value).clone()));
                    *s = Stmt::Block(vec![a, b]);
                }
            }
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            split_return_assigns(then_stmt);
            if let Some(e) = else_stmt {
                split_return_assigns(e);
            }
        }
        Stmt::While { body, .. }
        | Stmt::DoWhile { body, .. }
        | Stmt::ForEach { body, .. }
        | Stmt::Labeled { body, .. }
        | Stmt::Synchronized { body, .. } => split_return_assigns(body),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(split_return_assigns);
            split_return_assigns(body);
        }
        Stmt::Switch { cases, default, .. } => {
            for c in cases.iter_mut() {
                for st in c.body.iter_mut() {
                    split_return_assigns(st);
                }
            }
            if let Some(d) = default {
                split_return_assigns(d);
            }
        }
        Stmt::Try { body, catches, finally } => {
            split_return_assigns(body);
            for c in catches.iter_mut() {
                split_return_assigns(&mut c.body);
            }
            if let Some(f) = finally {
                split_return_assigns(f);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            resources.iter_mut().for_each(split_return_assigns);
            split_return_assigns(body);
            for c in catches.iter_mut() {
                split_return_assigns(&mut c.body);
            }
            if let Some(f) = finally {
                split_return_assigns(f);
            }
        }
        _ => {}
    }
}

/// A catch parameter must not shadow a local declared in an ENCLOSING
/// block (javac: "已在方法 start 中定义了变量 e1" — jdk26 ProcessBuilder:
/// the hoisted method-top `Throwable e1 = null;` collides with the
/// catch's own LVT name). Rename the catch variable (narrower scope; its
/// references follow var_name) with the house `$N` suffix. Sibling
/// catches in DIFFERENT try statements may legally share a name, so only
/// decls/catches textually BEFORE this try (at any depth) plus the try's
/// own catch list count.
fn disambiguate_catch_collisions(s: &mut Stmt, vt: &crate::varalloc::VarTable) {
    fn eff_name(c: &crate::stmt::Catch, vt: &crate::varalloc::VarTable) -> String {
        c.var_name
            .clone()
            .unwrap_or_else(|| vt.var(c.var).name.clone())
    }
    fn used_before(stmts: &[Stmt], vt: &crate::varalloc::VarTable, used: &mut HashSet<String>) {
        for st in stmts {
            match st {
                Stmt::LocalDef { var, .. } => {
                    used.insert(vt.var(*var).name.clone());
                }
                Stmt::Block(v) => used_before(v, vt, used),
                Stmt::If { then_stmt, else_stmt, .. } => {
                    used_before(std::slice::from_ref(then_stmt.as_ref()), vt, used);
                    if let Some(e) = else_stmt {
                        used_before(std::slice::from_ref(e.as_ref()), vt, used);
                    }
                }
                Stmt::While { body, .. }
                | Stmt::DoWhile { body, .. }
                | Stmt::ForEach { body, .. }
                | Stmt::Labeled { body, .. }
                | Stmt::Synchronized { body, .. } => {
                    used_before(std::slice::from_ref(body.as_ref()), vt, used)
                }
                Stmt::For { init, body, .. } => {
                    used_before(init, vt, used);
                    used_before(std::slice::from_ref(body.as_ref()), vt, used);
                }
                Stmt::Switch { cases, default, .. } => {
                    for c in cases {
                        used_before(&c.body, vt, used);
                    }
                    if let Some(d) = default {
                        used_before(std::slice::from_ref(d.as_ref()), vt, used);
                    }
                }
                Stmt::Try { body, catches, finally } => {
                    used_before(std::slice::from_ref(body.as_ref()), vt, used);
                    for c in catches {
                        used.insert(eff_name(c, vt));
                        used_before(std::slice::from_ref(c.body.as_ref()), vt, used);
                    }
                    if let Some(f) = finally {
                        used_before(std::slice::from_ref(f.as_ref()), vt, used);
                    }
                }
                Stmt::TryWithResources { resources, body, catches, finally } => {
                    used_before(resources, vt, used);
                    used_before(std::slice::from_ref(body.as_ref()), vt, used);
                    for c in catches {
                        used.insert(eff_name(c, vt));
                        used_before(std::slice::from_ref(c.body.as_ref()), vt, used);
                    }
                    if let Some(f) = finally {
                        used_before(std::slice::from_ref(f.as_ref()), vt, used);
                    }
                }
                _ => {}
            }
        }
    }
    fn rec(s: &mut Stmt, vt: &crate::varalloc::VarTable, used: &mut HashSet<String>) {
        match s {
            Stmt::Block(v) => {
                for st in v.iter_mut() {
                    rec(st, vt, used);
                }
            }
            Stmt::LocalDef { var, .. } => {
                used.insert(vt.var(*var).name.clone());
            }
            Stmt::If { then_stmt, else_stmt, .. } => {
                rec(then_stmt, vt, used);
                if let Some(e) = else_stmt {
                    rec(e, vt, used);
                }
            }
            Stmt::While { body, .. }
            | Stmt::DoWhile { body, .. }
            | Stmt::ForEach { body, .. }
            | Stmt::Labeled { body, .. }
            | Stmt::Synchronized { body, .. } => rec(body, vt, used),
            Stmt::For { init, body, .. } => {
                for i in init.iter_mut() {
                    rec(i, vt, used);
                }
                rec(body, vt, used);
            }
            Stmt::Switch { cases, default, .. } => {
                for c in cases.iter_mut() {
                    for st in c.body.iter_mut() {
                        rec(st, vt, used);
                    }
                }
                if let Some(d) = default {
                    rec(d, vt, used);
                }
            }
            Stmt::Try { body, catches, finally }
            | Stmt::TryWithResources { body, catches, finally, .. } => {
                // Names in scope BEFORE this try.
                let mut before = used.clone();
                let _ = &mut before;
                {
                    // (used already carries the preceding decls; the catch
                    // list below adds this try's own names as it goes.)
                }
                rec(body, vt, used);
                let mut own: HashSet<String> = HashSet::new();
                for c in catches.iter_mut() {
                    let name = eff_name(c, vt);
                    if used.contains(&name) || own.contains(&name) {
                        let mut k = 1usize;
                        loop {
                            let cand = format!("{}${}", name, k);
                            if !used.contains(&cand) && !own.contains(&cand) {
                                c.var_name = Some(cand.clone());
                                own.insert(cand);
                                break;
                            }
                            k += 1;
                        }
                    } else {
                        own.insert(name.clone());
                    }
                    let cname = eff_name(c, vt);
                    let mut inner = used.clone();
                    inner.insert(cname);
                    rec(c.body.as_mut(), vt, &mut inner);
                }
                if let Some(f) = finally {
                    rec(f, vt, used);
                }
            }
            _ => {}
        }
    }
    // Seed with method-level decls that PRECEDE any try: a single forward
    // walk with a running `used` set handles ordering; hoisted method-top
    // decls are the first statements and land in `used` before the tries.
    let mut used: HashSet<String> = HashSet::new();
    let _ = used_before;
    rec(s, vt, &mut used);
}

fn prune_tail_bare_returns(s: &mut Stmt) {
    fn prune(s: &mut Stmt, tail: bool) {
        match s {
            Stmt::Return(None) => {
                if tail {
                    *s = Stmt::Block(vec![]);
                }
            }
            Stmt::Block(v) => {
                if tail {
                    while matches!(v.last(), Some(Stmt::Return(None))) {
                        v.pop();
                    }
                }
                let n = v.len();
                for (i, x) in v.iter_mut().enumerate() {
                    prune(x, tail && i + 1 == n);
                }
                v.retain(|x| !x.is_empty_block());
            }
            Stmt::If { then_stmt, else_stmt, .. } => {
                prune(then_stmt, tail);
                if let Some(e) = else_stmt {
                    prune(e, tail);
                }
            }
            Stmt::While { body, .. } | Stmt::DoWhile { body, .. } | Stmt::ForEach { body, .. } => {
                prune(body, false);
            }
            Stmt::For { init, body, .. } => {
                init.iter_mut().for_each(|x| prune(x, false));
                prune(body, false);
            }
            Stmt::Labeled { body, .. } | Stmt::Synchronized { body, .. } => prune(body, tail),
            Stmt::Switch { cases, default, .. } => {
                for c in cases.iter_mut() {
                    if tail {
                        while matches!(c.body.last(), Some(Stmt::Return(None))) {
                            c.body.pop();
                        }
                    }
                    let n = c.body.len();
                    for (i, x) in c.body.iter_mut().enumerate() {
                        prune(x, tail && i + 1 == n);
                    }
                }
                if let Some(d) = default {
                    prune(d, tail);
                }
            }
            Stmt::Try { body, catches, finally } => {
                prune(body, tail);
                for c in catches.iter_mut() {
                    prune(&mut c.body, tail);
                }
                if let Some(f) = finally {
                    prune(f, tail);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                resources.iter_mut().for_each(|x| prune(x, false));
                prune(body, tail);
                for c in catches.iter_mut() {
                    prune(&mut c.body, tail);
                }
                if let Some(f) = finally {
                    prune(f, tail);
                }
            }
            _ => {}
        }
    }
    prune(s, true);
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
    // Hoisted/trivial local declarations may precede the call (jdk11
    // ConcurrentLinkedQueue.Itr: `Node h = null; ... super();` — javac put
    // super() first in bytecode; the printed pre-super decls make it a
    // pre-22 "灵活构造器" error). Skip side-effect-free decls when
    // locating it.
    fn trivial_decl(s: &Stmt) -> bool {
        match s {
            Stmt::LocalDef { init: None, .. } => true,
            Stmt::LocalDef { init: Some(e), .. } => match e {
                Expr::Const(_) => true,
                Expr::Cast { e: i, .. } => matches!(&**i, Expr::Const(_)),
                _ => false,
            },
            _ => false,
        }
    }
    let idx = stmts.iter().position(|s| !trivial_decl(s));
    if let Some(i) = idx {
        if let Stmt::ExprStmt(Expr::Method { name, cls, args, .. }) = &stmts[i] {
            if name == "<init>" && args.is_empty() && cls != &pc.internal_name {
                stmts[i] = Stmt::Block(vec![]);
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
/// After prune_local_ctor_delegation: the leading `this(...)` delegation's
/// args were trimmed but its descriptor still records the synthetic
/// capture-ctor form, so the desc-keyed cast passes skipped it. Re-align
/// the pruned args against the same-arity Signature-bearing sibling ctor
/// and restore the unchecked casts to TYPEVAR formals whose actuals are
/// plain Object (erased raw-Supplier `get()` conditionals, null-merged
/// captures). Idempotent: already-cast or generically-typed actuals are
/// left alone.
fn cast_pruned_delegation_typevar_args(body: &mut Stmt, pc: &PoolClass, mi_self: usize) {
    let stmts = match body {
        Stmt::Block(v) => v,
        _ => return,
    };
    let Some(first) = stmts.first_mut() else { return };
    let Stmt::ExprStmt(Expr::Method { name, cls, args, .. }) = first else {
        return;
    };
    if name != "<init>" || cls != &pc.internal_name || args.is_empty() {
        return;
    }
    // The target ctor: same class, Signature-bearing, formals matching the
    // pruned arg count.
    let mut found: Option<(usize, jcdc_jvm::MethodSignature)> = None;
    for mi2 in 0..pc.cf.methods.len() {
        if mi2 == mi_self || pc.method_name(mi2) != Some("<init>") {
            continue;
        }
        let Some(msig) = method_signature_of(pc, mi2) else { continue };
        if msig.args.len() == args.len() {
            found = Some((mi2, msig));
            break;
        }
    }
    let Some((_mi2, msig)) = found else { return };
    for (a, formal) in args.iter_mut().zip(msig.args.iter()) {
        let jcdc_jvm::GenericType::TypeVar(tn) = formal else { continue };
        if matches!(a, Expr::Cast { .. } | Expr::Const(_) | Expr::Lambda(_)) {
            continue;
        }
        if !matches!(a.type_ref(), TypeRef::J(jcdc_jvm::JavaType::Object(n))
            if n == "java/lang/Object")
        {
            continue;
        }
        let inner = std::mem::replace(a, Expr::This);
        *a = Expr::Cast {
            ty: TypeRef::G(jcdc_jvm::GenericType::TypeVar(tn.clone())),
            e: Box::new(inner),
        };
    }
}

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
    // Only the enum-constant stores, `$VALUES`, and synthetic `$`-prefixed
    // bookkeeping (e.g. `$assertionsDisabled`) may be hidden — the constant
    // list already renders the first two and the assert field is re-derived.
    // Any OTHER static field assignment (jdk26 AccessFlag's `CLASS_FLAGS =
    // createDefinition(..)`, Location's `SET_* = ..`) has no other
    // initializer: hiding the clinit drops it and every read fails with
    // 可能尚未初始化变量 (30 errors across the AccessFlag tree).
    let const_names: HashSet<String> = pc
        .cf
        .fields
        .iter()
        .filter(|f| f.access_flags.contains(FieldAccessFlags::ENUM))
        .filter_map(|f| pc.utf8(f.name_index).map(|n| n.to_string()))
        .collect();
    !stmts.is_empty()
        && stmts.iter().all(|s| match s {
            Stmt::ExprStmt(Expr::Assign { target, .. }) => match &**target {
                Expr::Field { name, is_static: true, .. } => {
                    name == "$VALUES" || name.starts_with('$') || const_names.contains(name)
                }
                _ => false,
            },
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
        if std::env::var("JCDC_DBG_ANON").is_ok() && !drained.is_empty() {
            let names: Vec<&String> = drained.iter().map(|(n, _)| n).collect();
            eprintln!(
                "DRAIN {:?} is_block={} in_anon_body={}",
                names,
                matches!(body, Stmt::Block(_)),
                in_anon_body
            );
        }
        if !drained.is_empty() && !in_anon_body {
            // Single-statement bodies (bare `return ..;`) still need the
            // decl: wrap so the insertion has a block (jdk26 Utils
            // makeSegmentVarHandle — VarHandleCache decl drained but
            // dropped because the body was not a Block).
            if !matches!(body, Stmt::Block(_)) {
                let orig = std::mem::replace(body, Stmt::Block(vec![]));
                *body = Stmt::Block(vec![orig]);
            }
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
                    // the method body). Definitions inside branches count
                    // (SESE-copied tails): decl lands after the branch
                    // structure — before every mention anyway.
                    let pos = last_capture_def(v, &caps, 0, vt);
                    if pos < 0 {
                        0
                    } else if pos >> 32 == 0 {
                        (pos as usize) + 1
                    } else {
                        let (n, _anchor) =
                            hoist_branch_captures(v, &caps, vt, ((pos >> 32) as usize) + 1);
                        if n == 0 {
                            ((pos >> 32) as usize) + 1
                        } else {
                            // Blanks at the head; the decl only needs to
                            // precede its mentions (first_use below).
                            0
                        }
                    }
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
/// Captured locals whose definitions live only in NESTED scopes: the
/// class decl must sit at the block top (its sibling copy-tails mention
/// it from every branch), but a branch-scoped capture definition is out
/// of scope there — hoist a blank decl for it to the block top and
/// demote the nested LocalDefs to assignments (jdk26 DoublePipeline
/// flatMap: `fastPath` defined in each copied tail).
fn hoist_branch_captures(
    v: &mut Vec<Stmt>,
    caps: &[String],
    vt: &VarTable,
    pos: usize,
) -> (usize, usize) {
    use std::collections::HashSet;
    let mut seen: HashSet<u32> = HashSet::new();
    fn scan(v: &[Stmt], caps: &[String], vt: &VarTable, seen: &mut HashSet<u32>) {
        for st in v {
            match st {
                Stmt::LocalDef { var, init: Some(_), .. } => {
                    if caps.iter().any(|n| vt.var(*var).name == *n) {
                        seen.insert(*var);
                    }
                }
                Stmt::Block(x) => scan(x, caps, vt, seen),
                Stmt::If { then_stmt, else_stmt, .. } => {
                    scan(std::slice::from_ref(then_stmt.as_ref()), caps, vt, seen);
                    if let Some(e) = else_stmt {
                        scan(std::slice::from_ref(e.as_ref()), caps, vt, seen);
                    }
                }
                Stmt::While { body, .. }
                | Stmt::DoWhile { body, .. }
                | Stmt::ForEach { body, .. }
                | Stmt::Labeled { body, .. }
                | Stmt::Synchronized { body, .. } => {
                    scan(std::slice::from_ref(body.as_ref()), caps, vt, seen);
                }
                Stmt::For { init, body, .. } => {
                    scan(init, caps, vt, seen);
                    scan(std::slice::from_ref(body.as_ref()), caps, vt, seen);
                }
                Stmt::Switch { cases, default, .. } => {
                    for c in cases {
                        scan(&c.body, caps, vt, seen);
                    }
                    if let Some(d) = default {
                        scan(std::slice::from_ref(d.as_ref()), caps, vt, seen);
                    }
                }
                Stmt::Try { body, catches, finally } => {
                    scan(std::slice::from_ref(body.as_ref()), caps, vt, seen);
                    for c in catches {
                        scan(std::slice::from_ref(c.body.as_ref()), caps, vt, seen);
                    }
                    if let Some(f) = finally {
                        scan(std::slice::from_ref(f.as_ref()), caps, vt, seen);
                    }
                }
                Stmt::TryWithResources { resources, body, catches, finally } => {
                    scan(resources, caps, vt, seen);
                    scan(std::slice::from_ref(body.as_ref()), caps, vt, seen);
                    for c in catches {
                        scan(std::slice::from_ref(c.body.as_ref()), caps, vt, seen);
                    }
                    if let Some(f) = finally {
                        scan(std::slice::from_ref(f.as_ref()), caps, vt, seen);
                    }
                }
                _ => {}
            }
        }
    }
    scan(v, caps, vt, &mut seen);
    if seen.is_empty() {
        return (0, pos);
    }
    // A capture defined at the TOP level must keep the decl after it;
    // only nested (branch-copied) definitions are hoistable. Blank
    // (init-less) decls are placeholders, not definitions.
    let top_def = v.iter().rposition(|st| match st {
        Stmt::LocalDef { var, init: Some(_), .. } => seen.contains(var),
        Stmt::ExprStmt(Expr::Assign { target, .. }) => {
            matches!(&**target, Expr::Local { var, .. } if seen.contains(var))
        }
        _ => false,
    });
    let mut blanks: Vec<Stmt> = Vec::new();
    let mut blanks_seen: HashSet<u32> = HashSet::new();
    fn demote_stmt(
        s: &mut Stmt,
        seen: &HashSet<u32>,
        blanks: &mut Vec<Stmt>,
        blanks_seen: &mut HashSet<u32>,
        vt: &VarTable,
    ) {
        match s {
            Stmt::LocalDef { var, .. } if seen.contains(var) => {
                match std::mem::replace(s, Stmt::Block(vec![])) {
                    Stmt::LocalDef { var, init: Some(e), .. } => {
                        if blanks_seen.insert(var) {
                            blanks.push(Stmt::LocalDef {
                                var,
                                init: None,
                                is_final: false,
                                force_type: true,
                            });
                        }
                        *s = Stmt::ExprStmt(Expr::Assign {
                            target: Box::new(Expr::Local { var, ty: vt.var(var).ty.clone() }),
                            op: crate::expr::AssignOp::Plain,
                            value: Box::new(e),
                        });
                    }
                    other => {
                        // init-less blank: a hoisted placeholder from an
                        // earlier pass — leave it as the decl.
                        *s = other;
                    }
                }
            }
            Stmt::Block(v) => {
                for x in v.iter_mut() {
                    demote_stmt(x, seen, blanks, blanks_seen, vt);
                }
            }
            Stmt::If { then_stmt, else_stmt, .. } => {
                demote_stmt(then_stmt, seen, blanks, blanks_seen, vt);
                if let Some(e) = else_stmt {
                    demote_stmt(e, seen, blanks, blanks_seen, vt);
                }
            }
            Stmt::While { body, .. }
            | Stmt::DoWhile { body, .. }
            | Stmt::ForEach { body, .. }
            | Stmt::Labeled { body, .. }
            | Stmt::Synchronized { body, .. } => {
                demote_stmt(body, seen, blanks, blanks_seen, vt);
            }
            Stmt::For { init, body, .. } => {
                for x in init.iter_mut() {
                    demote_stmt(x, seen, blanks, blanks_seen, vt);
                }
                demote_stmt(body, seen, blanks, blanks_seen, vt);
            }
            Stmt::Switch { cases, default, .. } => {
                for c in cases.iter_mut() {
                    for x in c.body.iter_mut() {
                        demote_stmt(x, seen, blanks, blanks_seen, vt);
                    }
                }
                if let Some(d) = default {
                    demote_stmt(d, seen, blanks, blanks_seen, vt);
                }
            }
            Stmt::Try { body, catches, finally } => {
                demote_stmt(body, seen, blanks, blanks_seen, vt);
                for c in catches.iter_mut() {
                    demote_stmt(&mut c.body, seen, blanks, blanks_seen, vt);
                }
                if let Some(f) = finally {
                    demote_stmt(f, seen, blanks, blanks_seen, vt);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                for r in resources.iter_mut() {
                    demote_stmt(r, seen, blanks, blanks_seen, vt);
                }
                demote_stmt(body, seen, blanks, blanks_seen, vt);
                for c in catches.iter_mut() {
                    demote_stmt(&mut c.body, seen, blanks, blanks_seen, vt);
                }
                if let Some(f) = finally {
                    demote_stmt(f, seen, blanks, blanks_seen, vt);
                }
            }
            _ => {}
        }
    }
    for x in v.iter_mut() {
        demote_stmt(x, &seen, &mut blanks, &mut blanks_seen, vt);
    }
    let n = blanks.len();
    // Blanks land at the block head (after any leading plain decls):
    // the demoted assignments execute inside branches that precede the
    // class-decl anchor position.
    let mut blank_pos = 0;
    while blank_pos < v.len() && matches!(&v[blank_pos], Stmt::LocalDef { .. }) {
        blank_pos += 1;
    }
    let _ = pos;
    for (k, b) in blanks.into_iter().enumerate() {
        v.insert(blank_pos + k, b);
    }
    if n == 0 {
        return (0, pos);
    }
    (n, top_def.map(|p| p + 1 + n).unwrap_or(0))
}

/// Last position (in a possibly-nested block list) where a captured/// Last position (in a possibly-nested block list) where a captured
/// outer local is DEFINED: `-1` when no definition exists (param-only
/// captures), otherwise an opaque encoding `(path_index << 32) |
/// sibling_index` ordering paths first, then within-path positions —
/// branch-copied tails define the capture inside an if-branch (jdk26
/// DoublePipeline flatMap: `DoubleConsumer fastPath = stack0` lives in
/// each copied tail), invisible to a flat scan, which parked the decl
/// before every definition.
fn last_capture_def(v: &[Stmt], caps: &[String], path: usize, vt: &VarTable) -> i64 {
    let mut best: i64 = -1;
    for (i, st) in v.iter().enumerate() {
        let defines = match st {
            Stmt::LocalDef { var, .. } => caps.iter().any(|n| vt.var(*var).name == *n),
            Stmt::ExprStmt(Expr::Assign { target, .. }) => {
                matches!(&**target, Expr::Local { var, .. }
                    if caps.iter().any(|n| vt.var(*var).name == *n))
            }
            _ => false,
        };
        if defines {
            let cand = ((path as i64) << 32) | i as i64;
            if cand > best {
                best = cand;
            }
        }
        let sub: Vec<&Stmt> = match st {
            Stmt::Block(x) => x.iter().collect(),
            Stmt::If { then_stmt, else_stmt, .. } => {
                let mut s2 = vec![then_stmt.as_ref()];
                if let Some(e) = else_stmt {
                    s2.push(e.as_ref());
                }
                s2
            }
            Stmt::While { body, .. }
            | Stmt::DoWhile { body, .. }
            | Stmt::ForEach { body, .. }
            | Stmt::Labeled { body, .. }
            | Stmt::Synchronized { body, .. } => vec![body.as_ref()],
            Stmt::For { init, body, .. } => {
                let mut s2: Vec<&Stmt> = init.iter().collect();
                s2.push(body.as_ref());
                s2
            }
            Stmt::Switch { cases, default, .. } => {
                let mut s2: Vec<&Stmt> = Vec::new();
                for c in cases {
                    s2.extend(c.body.iter());
                }
                if let Some(d) = default {
                    s2.push(d.as_ref());
                }
                s2
            }
            Stmt::Try { body, catches, finally } => {
                let mut s2: Vec<&Stmt> = vec![body.as_ref()];
                s2.extend(catches.iter().map(|c| c.body.as_ref()));
                if let Some(f) = finally {
                    s2.push(f.as_ref());
                }
                s2
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                let mut s2: Vec<&Stmt> = resources.iter().collect();
                s2.push(body.as_ref());
                s2.extend(catches.iter().map(|c| c.body.as_ref()));
                if let Some(f) = finally {
                    s2.push(f.as_ref());
                }
                s2
            }
            _ => Vec::new(),
        };
        for x in sub {
            let cand = last_capture_def(std::slice::from_ref(x), caps, path + 1, vt);
            if cand > best {
                best = cand;
            }
        }
    }
    best
}

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
            Expr::Method { owner, cls, args, type_args, .. } => {
                if let Some(o) = owner {
                    walk_e(o, marker, name, fam, found);
                }
                args.iter().for_each(|a| walk_e(a, marker, name, fam, found));
                if type_args.iter().any(|t| t.contains(name)) {
                    *found = true;
                }
                if !*found
                    && fam.nested.get(cls.as_str()).map(|x| x.simple.as_str()) == Some(name)
                {
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
            Expr::Field { owner, cls, .. } => {
                if let Some(o) = owner {
                    walk_e(o, marker, name, fam, found);
                }
                if !*found
                    && fam.nested.get(cls.as_str()).map(|x| x.simple.as_str()) == Some(name)
                {
                    *found = true;
                }
            }
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
                                || v.iter().any(|x| {
                                    matches!(x, Stmt::ClassDecl { name: n2, .. } if *n2 == name)
                                })
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
                        // Take the decl OUT while computing its target: a
                        // backward move left it in the scan path and the
                        // loop reprocessed it (double hoists).
                        let d = v.remove(j);
                        // Capture definitions may live inside the branch
                        // structure that holds the mentions (copied tails):
                        // land the decl after that structure and hoist the
                        // branch-scoped capture decls to before it.
                        let caps = local_class_captures(&name, fam, pool);
                        let pdef = if caps.is_empty() {
                            -1
                        } else {
                            last_capture_def(v, &caps, 0, vt)
                        };
                        let cpos = if pdef < 0 {
                            0
                        } else {
                            ((pdef >> 32) as usize) + 1
                        };
                        let mut target =
                            first_local_mention(v, &marker, &name, vt, fam).unwrap_or(v.len());
                        if pdef >> 32 > 0 {
                            // Capture definitions nested inside the branch
                            // structure (copied tails): hoist them to blank
                            // decls at the block head; afterwards the decl
                            // only needs to precede its mentions (a
                            // surviving top-level assign can sit AFTER
                            // mentions — anchoring on it pushed the decl
                            // past the branch mentions again).
                            let (n, _anchor) = hoist_branch_captures(v, &caps, vt, cpos);
                            target = if n > 0 {
                                first_local_mention(v, &marker, &name, vt, fam)
                                    .unwrap_or(v.len())
                            } else {
                                std::cmp::max(target, cpos)
                            };
                        } else if cpos > 0 {
                            // Top-level definitions: the decl must sit
                            // after the last one (and before mentions).
                            target = std::cmp::max(target, cpos);
                        }
                        if target > v.len() {
                            target = v.len();
                        }
                        if std::env::var("JCDC_DBG_ANON").is_ok() {
                            let shapes: Vec<String> = v
                                .iter()
                                .map(|x| match x {
                                    Stmt::Block(_) => "blk",
                                    Stmt::LocalDef { init: Some(_), .. } => "def",
                                    Stmt::LocalDef { .. } => "blank",
                                    Stmt::ClassDecl { .. } => "cls",
                                    Stmt::If { .. } => "if",
                                    Stmt::Return(_) => "ret",
                                    Stmt::ExprStmt(_) => "expr",
                                    _ => "other",
                                })
                                .map(|x| x.to_string())
                                .collect();
                            eprintln!(
                                "RELOC2 name={} cpos={} first={:?} shapes={:?}",
                                name,
                                cpos,
                                first_local_mention(v, &marker, &name, vt, fam),
                                shapes
                            );
                            eprintln!("RELOC name={} j={} target={} vlen={} depth={}", name, j, target, v.len(), ANON_BODY_DEPTH.with(|d| d.get()));
                        }
                        v.insert(target, d);
                        j = target + 1;
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
    LOCAL_CLASS_INTERNALS.with(|m| {
        m.borrow_mut().insert(simple.clone(), cls.to_string());
    });
    // Already extracted to an EARLIER statement of this method
    // (EXTERN_DECL is method-scoped): record the second mention site so
    // fix_lambda_captures can relocate the decl to a position dominating
    // both (jdk26 Gatherers Composite.impl: State extracted inside the
    // if-branch, mentioned again by the tail return after the chain —
    // 6 "找不到符号 类 State" at the tail).
    if EXTERN_DECL.with(|x| x.borrow().contains(&simple)) {
        if std::env::var("JCDC_DBG_ANON").is_ok() {
            eprintln!("EXTERNHIT {}", simple);
        }
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
    let is_rec = lpc.class_attr("Record").is_some();
    let class_sig = lpc.class_attr("Signature").and_then(|b| {
        if b.len() >= 2 {
            lpc.utf8(u16::from_be_bytes([b[0], b[1]]))
                .and_then(|x| parse_class_signature(x))
        } else {
            None
        }
    });
    let mut header = if is_rec {
        // Local record: `record Name<TP>(components) implements ..`. The
        // sig_header path rendered `Name<T> extends Record implements ..`
        // for generic local records — "类无法直接扩展 Record", component
        // names unbound, and new-sites hit a 0-arg ctor (jdk26 classfile
        // Util ForEachConsumer/WithCodeMethodHandler/WithFlagFieldHandler).
        // The implicit java.lang.Record supertype is never printed, but
        // declared interfaces ARE (`record CleanupAction(..) implements
        // Runnable` — dropping it made the value unassignable to the
        // method's Runnable return, jdk26
        // AbstractMemorySegmentImpl.cleanupAction).
        let p = Printer::new(lpc, pool, empty_vt());
        let mut h = format!("record {}", simple);
        if let Some(sig) = &class_sig {
            let mut tp = String::new();
            jcdc_jvm::render_type_params(&sig.params, &mut tp);
            h.push_str(&tp);
        }
        h.push_str(&record_components(lpc, pool));
        let rifaces: Vec<String> = match &class_sig {
            Some(sig) if !sig.interfaces.is_empty() => sig
                .interfaces
                .iter()
                .map(|i| p.type_name(&TypeRef::G(i.clone())))
                .collect(),
            _ => {
                let mut v = Vec::new();
                for &ii in &lpc.cf.interfaces {
                    if let Some(n) = lpc.class_name(ii) {
                        if n != "java/lang/Record" {
                            v.push(p.shorten(n));
                        }
                    }
                }
                v
            }
        };
        if !rifaces.is_empty() {
            h.push_str(" implements ");
            h.push_str(&rifaces.join(", "));
        }
        h
    } else {
        fam.nested
            .get(cls)
            .and_then(|n| n.sig_header.clone())
            .unwrap_or_else(|| simple.clone())
    };
    if !is_rec && fam.nested.get(cls).and_then(|n| n.sig_header.as_ref()).is_none() {
        let mut bases: Vec<String> = Vec::new();
        let p = Printer::new(lpc, pool, empty_vt());
        {
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
        if std::env::var("JCDC_DBG_ANON").is_ok() {
            eprintln!(
                "LOCALDECL fail {} err={:?} emitting={:?} depth={}",
                cls,
                emitted.err(),
                EMITTING.with(|e| e.borrow().clone()),
                ANON_BODY_DEPTH.with(|d| d.get())
            );
        }
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
    // A local class mentioned only through a static member access
    // (`Holder.INSTANCE` — jdk26 LinuxAArch64Linker.getInstance) has no
    // `new` site and no class literal to trigger the decl: emit it here
    // or the name is unbound ("找不到符号 变量 Holder").
    if !fam.locals.is_empty() {
        let member_cls = match e {
            Expr::Field { cls, owner: None, .. } | Expr::Method { cls, owner: None, .. } => {
                Some(cls.as_str())
            }
            _ => None,
        };
        if std::env::var("JCDC_DBG_ANON").is_ok() {
            if let Some(c) = member_cls {
                eprintln!("MEMBERCLS {} in_locals={}", c, fam.locals.contains(c));
            }
        }
        if let Some(cls) = member_cls {
            if fam.locals.contains(cls) {
                if let Some(lpc) = pool.get(cls) {
                    let simple = fam
                        .nested
                        .get(cls)
                        .map(|n| n.simple.clone())
                        .unwrap_or_else(|| simple_name(cls));
                    emit_local_class_decl(cls, &lpc, &simple, pc, pool, fam, &HashMap::new(), pending);
                }
            }
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

thread_local! {
    /// Lambda impl methods whose cond branches must be repaired at PRINT
    /// time (push_witness_into_branches): key "owner|impl_name" -> the
    /// enclosing method's generic return (witness target) and its
    /// Signature params (caller_params for bound checks). The Printer
    /// re-decompiles lambda bodies from bytecode, so AST-level mutation
    /// cannot reach them; the decision is made on a fresh analysis
    /// decompile and the recipe applied when the body is printed.
    static BRANCH_WITNESS_PUSH: std::cell::RefCell<
        HashMap<String, (jcdc_jvm::GenericType, Vec<jcdc_jvm::TypeParam>)>,
    > = std::cell::RefCell::new(HashMap::new());
}

pub(crate) fn branch_witness_pushed(
    owner: &str,
    name: &str,
) -> Option<(jcdc_jvm::GenericType, Vec<jcdc_jvm::TypeParam>)> {
    BRANCH_WITNESS_PUSH.with(|m| m.borrow().get(&format!("{}|{}", owner, name)).cloned())
}

/// Repair one lambda impl body per a registered pushdown recipe: drop
/// erasure-raw casts over generic calls (`(CompletionStage) fn.apply(ex)` —
/// synthesized against the impl's erased capture parameter; unnecessary
/// once the printed body references the outer generically-typed local) and
/// attach the enclosing return's witness to bare generic call branches
/// (`this.<T>handleAsync(..)` — the source shape; without it the cond sits
/// at CompletionStage<CAP#1> and the outer chain's inference dies).
pub(crate) fn repair_pushed_branches(
    body: &mut Stmt,
    want: &jcdc_jvm::GenericType,
    params: &[jcdc_jvm::TypeParam],
    pool: &ClassPool,
) {
    fn fix_branch(
        e: &mut Expr,
        want: &jcdc_jvm::GenericType,
        params: &[jcdc_jvm::TypeParam],
        pool: &ClassPool,
    ) {
        // raw erasure cast over a call on a GENERIC DECLARING TYPE ->
        // unwrap. The cast bridges the impl method's ERASED signature
        // (fn.apply on a raw Function capture returns Object); printed in
        // the lambda's lexical position the receiver names the OUTER
        // generically-typed local, so the call types as the capture itself
        // and reaches the target unchecked.
        if let Expr::Cast { ty, e: inner } = e {
            let raw_erased = matches!(ty, TypeRef::J(jcdc_jvm::JavaType::Object(_)));
            if raw_erased && generic_decl_call(inner, pool) {
                let v = std::mem::replace(e, Expr::This);
                if let Expr::Cast { e: inner, .. } = v {
                    *e = *inner;
                }
            }
        }
        // bare generic call -> witness, but only a DIRECTLY this-rooted
        // one: witnessing a chained call pins its final typevar against an
        // unpinned receiver (handleAsync(..).<T>thenCompose(identity) —
        // identity can never satisfy it); the chained source shape stays
        // fully bare and infers from the cond/return position.
        let igc = is_generic_call(e, pool)
            && matches!(e, Expr::Method { owner, .. }
                if owner.is_none() || matches!(owner.as_deref(), Some(Expr::This)));
        if let Expr::Method { cls, name, desc, type_args, .. } = e {
            if type_args.is_empty() && igc {
                if let Some((w, _)) =
                    compute_witness(cls.as_str(), name.as_str(), desc, None, want, pool, Some(params))
                {
                    *type_args = w;
                }
            }
        }
    }
    let ret = match body {
        Stmt::Return(Some(e)) => Some(e),
        Stmt::Block(v) if v.len() == 1 => match &mut v[0] {
            Stmt::Return(Some(e)) => Some(e),
            _ => None,
        },
        _ => None,
    };
    let Some(e) = ret else { return };
    if let Expr::Cond { t, f, .. } = e {
        fix_branch(t, want, params, pool);
        fix_branch(f, want, params, pool);
    } else {
        fix_branch(e, want, params, pool);
    }
}

/// True when the call's DECLARING TYPE is generic and the declared method
/// carries a Signature: in the printed lambda body the receiver names the
/// outer generically-typed local, so the call's return types as the
/// substituted Signature return (a capture) rather than the erased
/// descriptor return the impl-method pipeline saw.
fn generic_decl_call(e: &Expr, pool: &ClassPool) -> bool {
    let Expr::Method { cls, name, desc, .. } = e else { return false };
    let Some(dpc) = pool.get(cls) else { return false };
    let cls_generic = dpc
        .class_attr("Signature")
        .map(|b| b.len() >= 2)
        .unwrap_or(false);
    if !cls_generic {
        return false;
    }
    let want_desc = {
        let mut a = String::new();
        for t in &desc.args {
            a.push_str(&t.to_descriptor());
        }
        format!("({}){}", a, desc.ret.to_descriptor())
    };
    let Some(mi) = (0..dpc.cf.methods.len())
        .find(|&i| dpc.method_name(i) == Some(name.as_str()) && dpc.method_desc(i) == Some(want_desc.as_str()))
    else {
        return false
    };
    dpc.cf.methods[mi]
        .attributes
        .iter()
        .any(|a| dpc.utf8(a.attribute_name_index) == Some("Signature"))
}

/// Source-shape witnesses for bare generic calls that sit as lambda-cond
/// branches inside a returned generic call chain (jdk17 CompletionStage
/// exceptionallyAsync/exceptionallyCompose family, 12 errors across trees).
///
/// The source pins the INNER branch:
/// `handle((r, ex) -> ex != null ? this.<T>handleAsync(..) : this)
///      .thenCompose(Function.identity())`
/// The return-position machinery instead witnesses the OUTERMOST call
/// (`.<T>thenCompose`), which is actively wrong here: pinning the final U
/// turns `Function.identity()` into
/// `Function<CompletionStage<CompletionStage<T>>, ..>`, not convertible to
/// `Function<? super .., ? extends CompletionStage<T>>`, and the
/// unwitnessed inner branch leaves the cond at CompletionStage<CAP#1>
/// ("推论变量 T#1 具有不兼容的上限").
///
/// Fires only when the outermost returned call carries a computed witness
/// binding a typevar of the ENCLOSING method's own return (the
/// pinned-final shape) AND a sibling lambda-cond branch can be repaired
/// (bare generic branch takes the witness, or a droppable erasure-raw cast
/// exists). The outer witness is dropped so the chain infers from the
/// return position, and the branch recipe is registered for print time.
/// All-or-nothing: on any failed classification the tree is untouched.
fn push_witness_into_branches(
    s: &mut Stmt,
    msig: Option<&jcdc_jvm::MethodSignature>,
    pool: &ClassPool,
    pc: &PoolClass,
) {
    use jcdc_jvm::GenericType as G;
    BRANCH_WITNESS_PUSH.with(|m| m.borrow_mut().clear());
    let Some(sig) = msig else { return };
    if !generic_ret_ish(&sig.ret) {
        return;
    }
    fn ret_tvars(g: &G, out: &mut Vec<String>) {
        match g {
            G::TypeVar(n) => {
                if !out.contains(n) {
                    out.push(n.clone());
                }
            }
            G::Array(i) => ret_tvars(i, out),
            G::Class(cs) => cs
                .parts
                .iter()
                .for_each(|p| p.args.iter().for_each(|a| ret_tvars(a, out))),
            G::Wildcard(jcdc_jvm::WildcardBound::Extends(t))
            | G::Wildcard(jcdc_jvm::WildcardBound::Super(t)) => ret_tvars(t, out),
            _ => {}
        }
    }
    let mut tvars: Vec<String> = Vec::new();
    ret_tvars(&sig.ret, &mut tvars);
    if tvars.is_empty() {
        return;
    }
    // Collect (lambda key, impl method index) candidates along a call's
    // owner chain: the pushdown walks the receiver calls' lambda args.
    fn impl_bodies(owner: &Expr, pc: &PoolClass, out: &mut Vec<(String, usize)>) {
        let Expr::Method { args, owner: oo, .. } = owner else { return };
        for a in args {
            if let Expr::Lambda(l) = a {
                if l.impl_owner == pc.internal_name {
                    if let Some(mi) = pc.find_own_method(&l.impl_name, &l.impl_desc.to_string()) {
                        out.push((format!("{}|{}", l.impl_owner, l.impl_name), mi));
                    }
                }
            }
        }
        if let Some(o) = oo {
            impl_bodies(o, pc, out);
        }
    }
    // Classify one candidate impl body: Return(Cond) whose branches are
    // all (a) This, (b) a DIRECTLY this-rooted bare generic call that
    // TAKES the witness, (c) a droppable erasure-raw cast over a call on a
    // generic declaring type, or (d) a fully-bare CHAIN whose nested
    // lambda impls are themselves droppable-cast/bare (jdk17
    // exceptionallyComposeAsync: `handleAsync((r1, ex1) -> fn.apply(ex1))
    // .thenCompose(identity())` — the source shape is bare end to end and
    // javac infers it from the return position; verified compilable, while
    // the raw-cast + outer-witness shape is not). Returns the nested lambda
    // impl keys to register alongside, or None when the candidate must keep
    // the status quo.
    fn classify(
        pc: &PoolClass,
        pool: &ClassPool,
        mi: usize,
        want: &G,
        sig: &jcdc_jvm::MethodSignature,
    ) -> Option<Vec<String>> {
        let Ok(Some(mb)) = decompile_method(pc, pool, mi) else { return None };
        let ret = match &mb.body {
            Stmt::Return(Some(e)) => Some(e),
            Stmt::Block(v) if v.len() == 1 => match &v[0] {
                Stmt::Return(Some(e)) => Some(e),
                _ => None,
            },
            _ => None,
        };
        let Some(ret) = ret else { return None };
        let branches: Vec<&Expr> = match ret {
            Expr::Cond { t, f, .. } => vec![t.as_ref(), f.as_ref()],
            other => vec![other],
        };
        fn collect_lambdas<'x>(e: &'x Expr, out: &mut Vec<&'x crate::expr::LambdaExpr>) {
            match e {
                Expr::Lambda(l) => out.push(l),
                Expr::Method { args, owner, .. } => {
                    args.iter().for_each(|a| collect_lambdas(a, out));
                    if let Some(o) = owner {
                        collect_lambdas(o, out);
                    }
                }
                Expr::Cast { e: i, .. } => collect_lambdas(i, out),
                Expr::Cond { c, t, f } => {
                    collect_lambdas(c, out);
                    collect_lambdas(t, out);
                    collect_lambdas(f, out);
                }
                _ => {}
            }
        }
        let mut repairable = false;
        let mut nested_keys: Vec<String> = Vec::new();
        for b in &branches {
            match b {
                Expr::This => {}
                Expr::Method { type_args, .. } if type_args.is_empty() => {
                    if !is_generic_call(b, pool) {
                        return None;
                    }
                    let this_rooted = matches!(b, Expr::Method { owner, .. }
                        if owner.is_none() || matches!(owner.as_deref(), Some(Expr::This)));
                    if !this_rooted {
                        // Chained branch: it stays bare, but every nested
                        // lambda impl must be bare or droppable-cast — the
                        // chain's inference only survives with bare
                        // generics end to end.
                        let mut lams: Vec<&crate::expr::LambdaExpr> = Vec::new();
                        collect_lambdas(b, &mut lams);
                        for l in lams {
                            if l.impl_owner != pc.internal_name {
                                return None;
                            }
                            let Some(nmi) =
                                pc.find_own_method(&l.impl_name, &l.impl_desc.to_string())
                            else {
                                return None;
                            };
                            let Ok(Some(nmb)) = decompile_method(pc, pool, nmi) else { return None };
                            let nret = match &nmb.body {
                                Stmt::Return(Some(e)) => Some(e),
                                Stmt::Block(v) if v.len() == 1 => match &v[0] {
                                    Stmt::Return(Some(e)) => Some(e),
                                    _ => None,
                                },
                                _ => None,
                            };
                            match nret {
                                Some(Expr::Cast { ty, e: inner }) => {
                                    let raw_erased =
                                        matches!(ty, TypeRef::J(jcdc_jvm::JavaType::Object(_)));
                                    if !raw_erased || !generic_decl_call(inner, pool) {
                                        return None;
                                    }
                                    nested_keys
                                        .push(format!("{}|{}", l.impl_owner, l.impl_name));
                                    repairable = true;
                                }
                                Some(Expr::Method { type_args: nta, .. }) if nta.is_empty() => {}
                                Some(Expr::This) | None => {}
                                _ => return None,
                            }
                        }
                        continue;
                    }
                    let Expr::Method { cls, name, desc, .. } = b else { unreachable!() };
                    if compute_witness(
                        cls.as_str(),
                        name.as_str(),
                        desc,
                        None,
                        want,
                        pool,
                        Some(&sig.params),
                    )
                    .is_some()
                    {
                        repairable = true;
                    }
                }
                Expr::Cast { ty, e: inner } => {
                    // Erasure-raw cast over a call on a GENERIC declaring
                    // type: synthesized against the impl's erased capture
                    // parameter (raw Function.apply returns Object);
                    // printed in the lambda's lexical position the receiver
                    // names the OUTER generically-typed local, so the call
                    // types as the capture itself and reaches the target
                    // unchecked.
                    let raw_erased = matches!(ty, TypeRef::J(jcdc_jvm::JavaType::Object(_)));
                    let gdc = generic_decl_call(inner, pool);
                    if raw_erased && gdc {
                        repairable = true;
                    } else {
                        return None;
                    }
                }
                _ => return None,
            }
        }
        // Repair-only: a fully-bare shape keeps the outer witness (it is
        // the return-position machinery's normal, usually-correct output).
        if repairable {
            Some(nested_keys)
        } else {
            None
        }
    }
    fn fix(
        e: &mut Expr,
        want: &G,
        sig: &jcdc_jvm::MethodSignature,
        tvars: &[String],
        pool: &ClassPool,
        pc: &PoolClass,
    ) {
        {
            let Expr::Method { type_args, owner: Some(_), .. } = e else { return };
            if type_args.is_empty()
                || !type_args.iter().any(|t| tvars.iter().any(|n| n == t))
            {
                return;
            }
        }
        let Expr::Method { owner: Some(owner), .. } = &*e else { return };
        let mut cand: Vec<(String, usize)> = Vec::new();
        impl_bodies(owner, pc, &mut cand);
        if cand.is_empty() {
            return;
        }
        let mut keys: Vec<String> = Vec::new();
        for (key, mi) in &cand {
            if let Some(mut nested) = classify(pc, pool, *mi, want, sig) {
                keys.push(key.clone());
                keys.append(&mut nested);
            }
        }
        if keys.is_empty() {
            return;
        }
        // Drop the outer witness and register the print-time recipes.
        if let Expr::Method { type_args, .. } = e {
            type_args.clear();
        }
        BRANCH_WITNESS_PUSH.with(|m| {
            let mut m = m.borrow_mut();
            for key in &keys {
                m.insert(key.clone(), (want.clone(), sig.params.clone()));
            }
        });
    }
    fn rec(s: &mut Stmt, want: &G, sig: &jcdc_jvm::MethodSignature, tvars: &[String], pool: &ClassPool, pc: &PoolClass) {
        match s {
            Stmt::Block(v) => v.iter_mut().for_each(|x| rec(x, want, sig, tvars, pool, pc)),
            Stmt::Return(Some(e)) => fix(e, want, sig, tvars, pool, pc),
            Stmt::If { then_stmt, else_stmt, .. } => {
                rec(then_stmt, want, sig, tvars, pool, pc);
                if let Some(x) = else_stmt {
                    rec(x, want, sig, tvars, pool, pc);
                }
            }
            Stmt::While { body, .. }
            | Stmt::DoWhile { body, .. }
            | Stmt::ForEach { body, .. }
            | Stmt::Labeled { body, .. }
            | Stmt::Synchronized { body, .. } => rec(body, want, sig, tvars, pool, pc),
            Stmt::For { init, body, .. } => {
                init.iter_mut().for_each(|i| rec(i, want, sig, tvars, pool, pc));
                rec(body, want, sig, tvars, pool, pc);
            }
            Stmt::Switch { cases, default, .. } => {
                for c in cases.iter_mut() {
                    for st in c.body.iter_mut() {
                        rec(st, want, sig, tvars, pool, pc);
                    }
                }
                if let Some(d) = default {
                    rec(d, want, sig, tvars, pool, pc);
                }
            }
            Stmt::Try { body, catches, finally } => {
                rec(body, want, sig, tvars, pool, pc);
                for c in catches.iter_mut() {
                    rec(&mut c.body, want, sig, tvars, pool, pc);
                }
                if let Some(f) = finally {
                    rec(f, want, sig, tvars, pool, pc);
                }
            }
            _ => {}
        }
    }
    rec(s, &sig.ret, sig, &tvars, pool, pc);
}

fn witness_generic_returns(s: &mut Stmt, msig: Option<&jcdc_jvm::MethodSignature>, pool: &ClassPool, pc: &PoolClass) {
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
        pc: &PoolClass,
    ) {
        // A conditional with a poly (lambda/method-ref) arm must NOT be
        // wrapped as a whole: the cast makes the conditional standalone
        // and javac rejects the poly arm ("此处不应为 lambda 表达式").
        // Witness the non-poly arms individually instead — in the return
        // position the conditional stays a poly expression and the lambda
        // arm takes the method's return type directly.
        if let Expr::Cond { t, f, .. } = e {
            if matches!(**t, Expr::Lambda(_)) || matches!(**f, Expr::Lambda(_)) {
                fix(t, ret_g, ret_er, pool, sig, pc);
                fix(f, ret_g, ret_er, pool, sig, pc);
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
                            retype_witness_arg_casts(cls, name, desc, args, &mapping, pool, pc, &sig.params);
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
    fn rec(s: &mut Stmt, ret_g: &TypeRef, ret_er: &jcdc_jvm::JavaType, pool: &ClassPool, sig: &jcdc_jvm::MethodSignature, pc: &PoolClass) {
        match s {
            Stmt::Block(v) => v.iter_mut().for_each(|x| rec(x, ret_g, ret_er, pool, sig, pc)),
            Stmt::Return(Some(e)) => fix(e, ret_g, ret_er, pool, sig, pc),
            Stmt::If { then_stmt, else_stmt, .. } => {
                rec(then_stmt, ret_g, ret_er, pool, sig, pc);
                if let Some(x) = else_stmt {
                    rec(x, ret_g, ret_er, pool, sig, pc);
                }
            }
            Stmt::While { body, .. }
            | Stmt::DoWhile { body, .. }
            | Stmt::ForEach { body, .. }
            | Stmt::Labeled { body, .. }
            | Stmt::Synchronized { body, .. } => rec(body, ret_g, ret_er, pool, sig, pc),
            Stmt::For { init, body, .. } => {
                init.iter_mut().for_each(|i| rec(i, ret_g, ret_er, pool, sig, pc));
                rec(body, ret_g, ret_er, pool, sig, pc);
            }
            Stmt::Switch { cases, default, .. } => {
                for c in cases.iter_mut() {
                    for st in c.body.iter_mut() {
                        rec(st, ret_g, ret_er, pool, sig, pc);
                    }
                }
                if let Some(d) = default {
                    rec(d, ret_g, ret_er, pool, sig, pc);
                }
            }
            Stmt::Try { body, catches, finally } => {
                rec(body, ret_g, ret_er, pool, sig, pc);
                for c in catches.iter_mut() {
                    rec(&mut c.body, ret_g, ret_er, pool, sig, pc);
                }
                if let Some(f) = finally {
                    rec(f, ret_g, ret_er, pool, sig, pc);
                }
            }
            _ => {}
        }
    }
    rec(s, &ret_g, &ret_er, pool, sig, pc);
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
                    // A generic call with diamond args must KEEP the cast:
                    // bare in the return position, the target pins the
                    // method's typevar (T := List<T>'s T) and the diamond
                    // can no longer infer the standalone type the source
                    // relied on (jdk17 Stream.toList — `new
                    // ArrayList<>(asList(toArray()))` is ArrayList<Object>
                    // under the cast, but List<Object> is not
                    // List<? extends T> bare). witness_generic_returns
                    // deliberately leaves diamond-bearing calls bare, so
                    // nothing downstream would restore this cast.
                    let diamond_arg_call = matches!(&**inner, Expr::Method { args, .. }
                        if args_have_generic_new(args, pool));
                    // A generic call whose Signature return is a bare
                    // METHOD typevar erases to Object, so javac emits a
                    // real checkcast to the target's erasure (Stream
                    // .collect: ()Object + checkcast Set). In the return
                    // position the source needs NO cast: the return type
                    // is the inference target and drives R (jdk26
                    // ReferencedKeyMap.entrySet — keeping the synthesized
                    // (Set<Entry<K,V>>) cast pins the chain at
                    // Set<SimpleEntry<K,V>>: invariant 无法转换; the real
                    // source is the bare chain).
                    let generic_ret_object = matches!(&**inner, Expr::Method { desc, .. }
                        if desc.ret == jcdc_jvm::JavaType::Object("java/lang/Object".to_string()))
                        && is_generic_call(inner, pool)
                        && matches!(inner.type_ref(), TypeRef::J(jcdc_jvm::JavaType::Object(n))
                            if n == "java/lang/Object")
                        && {
                            let want_cls = match ty {
                                TypeRef::G(jcdc_jvm::GenericType::Class(cs)) => {
                                    Some(crate::method::classsig_internal(cs))
                                }
                                TypeRef::J(jcdc_jvm::JavaType::Object(n)) => Some(n.clone()),
                                _ => None,
                            };
                            matches!(ret_er, jcdc_jvm::JavaType::Object(rn)
                                if want_cls.as_deref() == Some(rn.as_str()))
                        };
                    let droppable = !diamond_arg_call
                        && ((matches!(inner.type_ref(), TypeRef::G(_)) && erasure_only)
                            || (is_generic_call(inner, pool) && erasure_only)
                            || generic_ret_object
                            || matches!(&**inner, Expr::Method { name, owner: Some(o), .. }
                                if name == "clone" && matches!(o.type_ref(), TypeRef::G(_))));
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
                // Anonymous outer classes have no source name. The body
                // being emitted sits INSIDE the outer anon's inlined body,
                // so its members resolve LEXICALLY: substitute an unqualified
                // marker (the printer drops the owner entirely). A `this`
                // rendering would denote the NESTED class itself (jdk11/17
                // KeyStore Builder: nested anon reading getCalled/
                // oldException printed this.getCalled — 11 symbol errors);
                // an argument-position marker keeps the enclosing `this`.
                let starts_digit = outer_simple
                    .chars()
                    .next()
                    .map(|c| c.is_ascii_digit())
                    .unwrap_or(false);
                return if starts_digit {
                    (k, Expr::Raw("\u{3}".to_string()))
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
            // Keep the captured local's declared type on the Raw: the
            // substituted expression stands in comparisons inside the
            // class body (`leftFinisher == Gatherer.defaultFinisher()`),
            // and the comparison witness needs the generic operand type
            // to unify against (the erased val$ field type cannot drive
            // it).
            let mut ty = match &v {
                Expr::Local { var, .. } => outer_vt.var(*var).ty.clone(),
                _ => TypeRef::J(jcdc_jvm::JavaType::Object("java/lang/Object".into())),
            };
            CAPTURE_GENERIC_TYPES.with(|m| {
                let mut m = m.borrow_mut();
                match m.get(&text) {
                    Some(g) if matches!(g, TypeRef::G(_)) => ty = g.clone(),
                    _ => {
                        if matches!(ty, TypeRef::G(_)) {
                            m.insert(text.clone(), ty.clone());
                        }
                    }
                }
            });
            (k, Expr::RawT(text, ty))
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
    // Local classes of 16+ class files keep static state: the Holder
    // idiom (`class Holder { static final X INSTANCE = ..; }`, jdk26
    // LinuxAArch64Linker) carries its initializers in <clinit>; dropping
    // it left a blank `private static final` field. Emit the surviving
    // stores as a static block (the assertions store rides the instance
    // field emitted above). Pre-16 local classes cannot hold statics —
    // their <clinit> is only the assertions field.
    if apc.cf.major_version >= 60 {
        let clinit_mi = (0..apc.cf.methods.len()).find(|&mi| apc.method_name(mi) == Some("<clinit>"));
        if let Some(mi) = clinit_mi {
            if let Ok(Some(mb)) = decompile_method(apc, pool, mi) {
                let mut body = mb.body.clone();
                strip_static_init_returns(&mut body);
                let mut pending: Vec<Stmt> = Vec::new();
                let mut declared: HashSet<String> = HashSet::new();
                walk_stmt_anon(&mut body, apc, pool, fam, &mut pending, &mb.vt, &mut declared);
                fn drop_assert_stores(v: &mut Vec<Stmt>) {
                    v.retain(|st| {
                        !matches!(st, Stmt::ExprStmt(Expr::Assign { target, .. })
                            if matches!(&**target, Expr::Field { name, is_static: true, .. }
                                if name == "$assertionsDisabled" || name == ASSERT_FIELD))
                    });
                }
                match &mut body {
                    Stmt::Block(v) => drop_assert_stores(v),
                    Stmt::ExprStmt(Expr::Assign { target, .. })
                        if matches!(&**target, Expr::Field { name, is_static: true, .. }
                            if name == "$assertionsDisabled" || name == ASSERT_FIELD) =>
                    {
                        body = Stmt::Block(vec![]);
                    }
                    _ => {}
                }
                let text = Printer::new(apc, pool, &mb.vt)
                    .with_indent(indent + 2)
                    .into_string(&body);
                if !text.trim().is_empty() {
                    out.push_str(&"    ".repeat(indent + 1));
                    out.push_str("static {\n");
                    out.push_str(&text);
                    out.push_str(&"    ".repeat(indent + 1));
                    out.push_str("}\n");
                }
            }
        }
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
                            // Lambda impl methods carry erased param
                            // types (no LVTT on synthetic methods): lift
                            // the generic types from the LambdaExpr's
                            // capture expressions (outer locals at the
                            // indy site) so capture renderings — and the
                            // comparison witnesses they drive — see the
                            // declared parameterization.
                            let mut lvt = mb.vt.clone();
                            {
                                let mut pi = 0usize;
                                for v in lvt.vars.iter_mut() {
                                    if v.is_param && v.name != "this" {
                                        if let Some(cap) = l.captures.get(pi) {
                                            let ct = cap.type_ref();
                                            if matches!(ct, TypeRef::G(_))
                                                && !matches!(v.ty, TypeRef::G(_))
                                            {
                                                v.ty = ct;
                                            }
                                        }
                                        pi += 1;
                                    }
                                }
                            }
                            walk_stmt_anon(&mut cb, pc, pool, fam, &mut p2, &lvt, &mut d2);
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
                                if std::env::var("JCDC_DBG_ANON").is_ok() {
                                    let names: Vec<&String> =
                                        fresh.iter().map(|(n, _)| n).collect();
                                    eprintln!("EXTERNREG {:?}", names);
                                }
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
        let p = last_capture_def(v, &caps, 0, vt);
        if p < 0 {
            continue;
        }
        if p >> 32 == 0 {
            // Top-level definition: land right after the last one.
            pos = std::cmp::max(pos, (p as u32 as usize) + 1);
        } else {
            // Branch-copied definitions: hoist them to blank decls at the
            // head; the decl then only needs to precede its mentions.
            let cpos = ((p >> 32) as usize) + 1;
            let (n, _anchor) = hoist_branch_captures(v, &caps, vt, cpos);
            if n > 0 {
                let marker = format!("\u{2}{}", name);
                pos = std::cmp::max(
                    pos,
                    first_local_mention(v, &marker, name, vt, fam).unwrap_or(v.len()),
                );
            } else {
                pos = std::cmp::max(pos, cpos);
            }
        }
    }
    for (k, d) in moved.into_iter().enumerate() {
        v.insert(pos + k, d);
    }
}

/// Map this$N fields of a member inner class to `Outer.this` raw exprs.
pub(crate) fn outer_this_map(pc: &PoolClass) -> HashMap<String, Expr> {
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
    // jdk26 nest-based inner classes drop the this$0 FIELD: the ctor
    // param carries the enclosing instance and every read of it must
    // still render as the qualified outer this (CallArranger
    // BindingCalculator leaked `this.this$0.new StorageCalculator(..)`,
    // COWArrayList Reversed DescendingIterator leaked `this.this$0.lock`
    // — 找不到符号 变量 this$0).
    if m.is_empty() && !nested_is_static(pc) && pc.internal_name.contains('$') {
        if let Some((outer, _)) = pc.internal_name.rsplit_once('$') {
            if !outer.is_empty() {
                let sn = simple_name(outer);
                let starts_digit =
                    sn.chars().next().map(|c| c.is_ascii_digit()).unwrap_or(false);
                let rep = if starts_digit {
                    Expr::This
                } else {
                    Expr::Raw(format!("{}.this", qualified_this_tail(outer)))
                };
                m.insert("this$0".to_string(), rep);
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

pub(crate) fn substitute_captures(s: &mut Stmt, captures: &HashMap<String, Expr>, pool: &ClassPool) {
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
                Expr::Raw(_) | Expr::RawT(..) => true,
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
    // A ctor whose FIRST statement is already the delegation (this(..) or
    // super(..)) is in legal source form: the fold below targets only
    // javac's DEFERRED-delegation shape (assignments/if-tree with tail
    // `this(str)` leaves). Firing on the legal shape rewrote
    // `this(je); attr = je.attr; certs = ..; signers = je.signers;`
    // into `this(je.signers)` (jdk17 JarEntry copy ctor — the template
    // came from the leading call and the "value" from the last field
    // copy: 对于JarEntry(CodeSigner[]), 找不到合适的构造器). A ctor
    // never has a second delegation after the first, so this is safe.
    if let Some(Stmt::ExprStmt(Expr::Method { name, .. })) = items.first() {
        if name == "<init>" {
            return;
        }
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
pub(crate) fn is_subtype_of(pool: &ClassPool, ty: &jcdc_jvm::JavaType, target: &str) -> bool {
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
/// Direct supers of `pcls` as (internal name, type arguments), with the
/// class's own typevars substituted by `self_args`. Signature-driven when
/// present (parameterized supers); erased fallback otherwise.
pub(crate) fn class_supers_args(
    pcls: &PoolClass,
    self_args: &[jcdc_jvm::GenericType],
) -> Vec<(String, Vec<jcdc_jvm::GenericType>)> {
    let sig = pcls.class_attr("Signature").and_then(|b| {
        if b.len() >= 2 {
            pcls.utf8(u16::from_be_bytes([b[0], b[1]]))
                .and_then(|x| parse_class_signature(x))
        } else {
            None
        }
    });
    let mut out: Vec<(String, Vec<jcdc_jvm::GenericType>)> = Vec::new();
    if let Some(sig) = sig {
        let self_params = sig.params.clone();
        let mut candidates: Vec<jcdc_jvm::GenericType> = vec![sig.superclass.clone()];
        candidates.extend(sig.interfaces.iter().cloned());
        for cand in candidates {
            if let jcdc_jvm::GenericType::Class(cs) = &cand {
                let internal = crate::method::classsig_internal(cs);
                let args: Vec<jcdc_jvm::GenericType> = cs
                    .parts
                    .last()
                    .map(|p| {
                        p.args
                            .iter()
                            .map(|a| {
                                crate::method::subst_typevars(a, &self_params, self_args)
                            })
                            .collect()
                    })
                    .unwrap_or_default();
                out.push((internal, args));
            }
        }
    }
    if out.is_empty() {
        if let Some(sn) = pcls.super_name() {
            out.push((sn.to_string(), Vec::new()));
        }
        for i in pcls.interface_names() {
            out.push((i.to_string(), Vec::new()));
        }
    }
    out
}

/// The type arguments a superclass/superinterface `target` receives in
/// `pc`'s declaration (pc's own typevars passed through as TypeVars).
fn supertype_instantiation(
    pc: &PoolClass,
    target: &str,
    pool: &ClassPool,
) -> Option<Vec<jcdc_jvm::GenericType>> {
    let self_args: Vec<jcdc_jvm::GenericType> = pc
        .class_attr("Signature")
        .and_then(|b| {
            if b.len() >= 2 {
                pc.utf8(u16::from_be_bytes([b[0], b[1]]))
                    .and_then(|x| parse_class_signature(x))
            } else {
                None
            }
        })
        .map(|sig| {
            sig.params
                .iter()
                .map(|p| jcdc_jvm::GenericType::TypeVar(p.name.clone()))
                .collect()
        })
        .unwrap_or_default();
    let _ = pool;
    class_supers_args(pc, &self_args)
        .into_iter()
        .find(|(n, _)| n == target)
        .map(|(_, a)| a)
}

/// The instantiated return type of a call expression, resolved through
/// the owner's parameterization and the declaring super chain
/// (getLocalResult on a CollectorTask<P_IN,P_OUT,T_NODE,T_BUILDER>-typed
/// receiver declares R on AbstractTask<P_IN,P_OUT,R,K> → T_NODE). None
/// for statics, unresolvable owners, erased declarations, or returns
/// that mention no typevar after substitution.
pub(crate) fn instantiated_method_ret(
    m: &Expr,
    pool: &ClassPool,
    pc: &PoolClass,
) -> Option<jcdc_jvm::GenericType> {
    let (cls, name, desc, owner, is_static, args) = match m {
        Expr::Method { cls, name, desc, owner, is_static, args, .. } => (
            cls.as_str(),
            name.as_str(),
            desc,
            owner.as_deref(),
            *is_static,
            args.as_slice(),
        ),
        _ => return None,
    };
    if name == "<init>" {
        return None;
    }
    let d_str = format!(
        "({}){}",
        desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
        desc.ret.to_descriptor()
    );
    if is_static {
        // A static generic call whose return is the method's OWN typevar:
        // infer it from the single bare-typevar formal's actual (jdk
        // LoggerWrapper: `(System.Logger) Objects.requireNonNull(wrapped)`
        // upgrades to `(L)` — requireNonNull<T>(T) with wrapped: L;
        // Logger无法转换为L on the this(..) delegation formal).
        let dpc = pool.get(cls)?;
        let mi = (0..dpc.cf.methods.len())
            .find(|&i| dpc.method_name(i) == Some(name) && desc_raw(&dpc, i) == d_str)?;
        let msig = method_signature_of(&dpc, mi)?;
        let jcdc_jvm::GenericType::TypeVar(r) = &msig.ret else {
            return None;
        };
        let hits: Vec<usize> = msig
            .args
            .iter()
            .enumerate()
            .filter(|(_, f)| matches!(f, jcdc_jvm::GenericType::TypeVar(t) if t == r))
            .map(|(i, _)| i)
            .collect();
        if hits.len() != 1 {
            return None;
        }
        let arg = args.get(hits[0])?;
        if matches!(arg, Expr::Cast { .. } | Expr::Const(_) | Expr::Lambda(_)) {
            return None;
        }
        let tr = arg.type_ref();
        return match &tr {
            TypeRef::G(g @ jcdc_jvm::GenericType::TypeVar(_)) => Some(g.clone()),
            TypeRef::G(g @ jcdc_jvm::GenericType::Class(cs))
                if cs.parts.iter().any(|p| !p.args.is_empty()) =>
            {
                Some(g.clone())
            }
            _ => None,
        };
    }
    let (start, start_args): (String, Vec<jcdc_jvm::GenericType>) = match owner {
        Some(o) => {
            let raw_outer = match o {
                Expr::Raw(s) => s
                    .strip_suffix(".this")
                    .and_then(|simple| outer_this_instantiation(pc, simple, pool)),
                _ => None,
            };
            match raw_outer {
                Some(pair) => pair,
                None => match o.type_ref() {
                    TypeRef::G(jcdc_jvm::GenericType::Class(cs)) => {
                        (crate::method::classsig_internal(&cs), cs.parts.last()?.args.clone())
                    }
                    t => match t.erased() {
                        jcdc_jvm::JavaType::Object(n) => {
                            if pc.internal_name.starts_with(&n)
                                && pc.internal_name.as_bytes().get(n.len()) == Some(&b'$')
                            {
                                (n.clone(), own_typevars(&n, pool))
                            } else {
                                (n, Vec::new())
                            }
                        }
                        _ => return None,
                    },
                },
            }
        }
        None => {
            let args = pc
                .class_attr("Signature")
                .and_then(|b| {
                    if b.len() < 2 {
                        return None;
                    }
                    pc.utf8(u16::from_be_bytes([b[0], b[1]]))
                        .and_then(|s| parse_class_signature(s))
                })
                .map(|sig| {
                    sig.params
                        .iter()
                        .map(|p| jcdc_jvm::GenericType::TypeVar(p.name.clone()))
                        .collect()
                })
                .unwrap_or_default();
            (pc.internal_name.clone(), args)
        }
    };
    let mut queue: std::collections::VecDeque<(String, Vec<jcdc_jvm::GenericType>)> =
        std::collections::VecDeque::new();
    queue.push_back((start, start_args));
    let mut visited: std::collections::HashSet<String> = std::collections::HashSet::new();
    while let Some((cur, cur_args)) = queue.pop_front() {
        if !visited.insert(cur.clone()) {
            continue;
        }
        let dpc;
        let dref: &PoolClass = if cur == pc.internal_name {
            pc
        } else {
            match pool.get(&cur) {
                Some(p) => {
                    dpc = p;
                    &dpc
                }
                None => continue,
            }
        };
        let Some(mi) = (0..dref.cf.methods.len())
            .find(|&i| dref.method_name(i) == Some(name) && desc_raw(dref, i) == d_str)
        else {
            queue.extend(class_supers_args(dref, &cur_args));
            continue;
        };
        let msig = method_signature_of(dref, mi)?;
        let params = dref
            .class_attr("Signature")
            .and_then(|b| {
                if b.len() < 2 {
                    return None;
                }
                dref.utf8(u16::from_be_bytes([b[0], b[1]]))
                    .and_then(|s| parse_class_signature(s))
            })
            .map(|s| s.params)
            .unwrap_or_default();
        if params.len() != cur_args.len() {
            return None;
        }
        let inst = crate::method::subst_typevars(&msig.ret, &params, &cur_args);
        // Wildcard instantiations are RETURNED (callers decide): a cast
        // upgrade must stand down on them (previous() on a
        // ListIterator<? extends T> owner → `? extends T` is not a legal
        // cast target; spliterator() on a Collection<? extends E> field
        // would widen a precise `(Spliterator<E>)`), but cast_generic_
        // locals NEEDS the distinction: getKey() on a Map.Entry<?,?>
        // local instantiates to an unbounded wildcard ≠ the target K —
        // conflating it with "unresolvable" kept the name-based skip and
        // dropped the source's `(K)` cast (TreeMap.buildFromSorted
        // CAP#1无法转换为K/V x2 per tree).
        if crate::method::contains_typevar(&inst)
            || matches!(inst, jcdc_jvm::GenericType::Wildcard(_))
            || matches!(&inst, jcdc_jvm::GenericType::Class(cs)
                if cs.parts.iter().any(|p| !p.args.is_empty()))
        {
            return Some(inst);
        }
        return None;
    }
    None
}

/// The enclosing class of `pc` whose simple name matches `simple` (the
/// qualifier of a rendered `X.this` outer reference), paired with its own
/// typevars as arguments: they are in scope inside the inner class, so
/// `IdentityHashMap.this.put(traversalTable[i], v)` resolves its formals
/// to K/V (jdk11 IdentityHashMap.EntryIterator.Entry.setValue lost the
/// source's `(K)` cast — Object无法转换为K).
/// A class's own typevars as generic arguments (empty when non-generic).
fn own_typevars(cls: &str, pool: &ClassPool) -> Vec<jcdc_jvm::GenericType> {
    pool.get(cls)
        .and_then(|c| {
            c.class_attr("Signature").and_then(|b| {
                if b.len() < 2 {
                    return None;
                }
                let i2 = u16::from_be_bytes([b[0], b[1]]);
                c.utf8(i2).and_then(|s| parse_class_signature(s))
            })
        })
        .map(|sig| {
            sig.params
                .iter()
                .map(|p| jcdc_jvm::GenericType::TypeVar(p.name.clone()))
                .collect()
        })
        .unwrap_or_default()
}

fn outer_this_instantiation(
    pc: &PoolClass,
    simple: &str,
    pool: &ClassPool,
) -> Option<(String, Vec<jcdc_jvm::GenericType>)> {
    let name = pc.internal_name.as_str();
    let mut idx = name.rfind('$')?;
    loop {
        let cand = &name[..idx];
        if simple_name(cand) == simple {
            return Some((cand.to_string(), own_typevars(cand, pool)));
        }
        match cand.rfind('$') {
            Some(i) => idx = i,
            None => return None,
        }
    }
}

/// Instantiated Signature formals of a call for SAM-return priming:
/// unlike instantiated_method_params this does NOT bail on generic
/// methods — the caller gates each formal on mentioning no callee method
/// typevar (jdk17 AbstractPipeline.opEvaluateParallelLazy: the
/// IntFunction<E_OUT[]> formal is class-param-only while the sibling
/// formal carries the callee's P_IN). Direct declarations only (no super
/// walk); returns (formals, method-typevar names).
pub(crate) fn generic_call_formals(
    m: &Expr,
    pool: &ClassPool,
    pc: &PoolClass,
) -> Option<(Vec<jcdc_jvm::GenericType>, Vec<String>)> {
    use jcdc_jvm::GenericType as G;
    let (cls, name, desc, owner, is_static) = match m {
        Expr::Method { cls, name, desc, owner, is_static, .. } => {
            (cls.as_str(), name.as_str(), desc, owner.as_deref(), *is_static)
        }
        _ => return None,
    };
    if name == "<init>" {
        return None;
    }
    let (decl, decl_args): (String, Vec<G>) = if is_static {
        (cls.to_string(), Vec::new())
    } else {
        match owner {
            None | Some(Expr::This) => {
                let cs = pc.class_attr("Signature").and_then(|b| {
                    if b.len() >= 2 {
                        pc.utf8(u16::from_be_bytes([b[0], b[1]])).and_then(|x| parse_class_signature(x))
                    } else {
                        None
                    }
                });
                let args = cs
                    .as_ref()
                    .map(|c| c.params.iter().map(|p| G::TypeVar(p.name.clone())).collect())
                    .unwrap_or_default();
                (pc.internal_name.clone(), args)
            }
            Some(o) => match o.type_ref() {
                TypeRef::G(G::Class(cs)) => {
                    (crate::method::classsig_internal(&cs), cs.parts.last()?.args.clone())
                }
                _ => return None,
            },
        }
    };
    let d_str = format!(
        "({}){}",
        desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
        desc.ret.to_descriptor()
    );
    let owned;
    let dref: &PoolClass = if decl == pc.internal_name {
        pc
    } else {
        owned = pool.get(&decl)?;
        &owned
    };
    let mi = (0..dref.cf.methods.len())
        .find(|&i| dref.method_name(i) == Some(name) && desc_raw(dref, i) == d_str)?;
    let msig = method_signature_of(dref, mi)?;
    let class_params = dref
        .class_attr("Signature")
        .and_then(|b| {
            if b.len() >= 2 {
                dref.utf8(u16::from_be_bytes([b[0], b[1]])).and_then(|x| parse_class_signature(x))
            } else {
                None
            }
        })
        .map(|c| c.params)
        .unwrap_or_default();
    if class_params.len() != decl_args.len() {
        return None;
    }
    let mut formals: Vec<jcdc_jvm::GenericType> = msig
        .args
        .iter()
        .map(|a| crate::method::subst_typevars(a, &class_params, &decl_args))
        .collect();
    let mut mtvars: Vec<String> = msig.params.iter().map(|p| p.name.clone()).collect();
    // An explicitly witnessed call binds its own method typevars: swap
    // them for the witness types so formals like IntFunction<T[]> become
    // denotable at the call site (jdk26 CopyOnWriteArrayList.toArray
    // `this.<T>toArray(i -> (T[]) new Object[i])`). Simple witness
    // strings (bare identifiers) map to TypeVars — they render
    // identically to the caller's same-named typevar; complex ones fall
    // back to the method-ref mapping when an unbound ref arg produced
    // the witness.
    let Expr::Method { type_args, args, .. } = m else { unreachable!() };
    if !type_args.is_empty() && type_args.len() == msig.params.len() {
        let mut ref_map: Option<Vec<(String, jcdc_jvm::GenericType)>> = None;
        for (pi, p) in msig.params.iter().enumerate() {
            let mut g: Option<jcdc_jvm::GenericType> = None;
            let ta = &type_args[pi];
            if !ta.contains('<') && !ta.contains('.') && !ta.contains('[') {
                g = Some(jcdc_jvm::GenericType::TypeVar(ta.clone()));
            } else {
                if ref_map.is_none() {
                    ref_map = args.iter().find_map(|a| {
                        let lam = match a {
                            Expr::Lambda(l) => Some(l),
                            Expr::Cast { e: ce, .. } => match &**ce {
                                Expr::Lambda(l) => Some(l),
                                _ => None,
                            },
                            _ => None,
                        }?;
                        if lam.kind != crate::expr::LambdaKind::MethodRef
                            || lam.impl_is_static
                            || !lam.captures.is_empty()
                        {
                            return None;
                        }
                        method_ref_type_args(cls, name, desc, lam, pool).map(|(_, m)| m)
                    });
                }
                g = ref_map
                    .as_ref()
                    .and_then(|m| m.iter().find(|(n, _)| *n == p.name).map(|(_, v)| v.clone()));
            }
            if let Some(g) = g {
                if let Some(idx) = formals.iter().enumerate().map(|(k, _)| k).find(|_| true) {
                    let _ = idx;
                }
                for f in formals.iter_mut() {
                    *f = crate::method::subst_typevars(
                        f,
                        std::slice::from_ref(p),
                        std::slice::from_ref(&g),
                    );
                }
                mtvars.retain(|n| *n != p.name);
            }
        }
    }
    Some((formals, mtvars))
}

/// True when the type mentions any of the given typevar names.
pub(crate) fn g_mentions_any(g: &jcdc_jvm::GenericType, names: &[String]) -> bool {
    g_mentions_any_inner(g, names)
}
fn g_mentions_any_inner(g: &jcdc_jvm::GenericType, names: &[String]) -> bool {
    use jcdc_jvm::GenericType as G;
    match g {
        G::TypeVar(n) => names.iter().any(|x| x == n),
        G::Array(i) => g_mentions_any_inner(i, names),
        G::Class(cs) => cs
            .parts
            .iter()
            .any(|p| p.args.iter().any(|a| g_mentions_any_inner(a, names))),
        G::Wildcard(jcdc_jvm::WildcardBound::Extends(t))
        | G::Wildcard(jcdc_jvm::WildcardBound::Super(t)) => g_mentions_any_inner(t, names),
        _ => false,
    }
}

pub(crate) fn instantiated_method_params(
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
                        // implicit `this` or erased owner: the enclosing
                        // class. The super-chain BFS below walks pc's
                        // supers when pc does not declare name+desc (an
                        // inherited generic like FindSink.accept(T) whose
                        // methodref owner is the receiver class), carrying
                        // each hop's real instantiation — so decl starts
                        // at pc even when cls names a supertype (setting
                        // decl=cls with pc's own typevars instantiates
                        // foreign methods against the wrong parameters:
                        // `(T) u` regression in ReferencePipeline).
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
            Some(o) => {
                // A qualified outer this renders as Expr::Raw("X.this"):
                // resolve the enclosing class and its own typevars.
                let raw_outer = match o {
                    Expr::Raw(s) => s
                        .strip_suffix(".this")
                        .and_then(|simple| outer_this_instantiation(pc, simple, pool)),
                    _ => None,
                };
                match raw_outer {
                    Some(pair) => pair,
                    None => {
                        // A call-owned receiver whose descriptor return is
                        // ERASED: resolve the instantiated generic return
                        // from its Signature (jdk26 BoundAttribute.writeTo:
                        // attributeMapper() returns AttributeMapper<T>; the
                        // erased read loses T, the writeAttribute formal A
                        // cannot be substituted, and the source `(T) this`
                        // cast is dropped — BoundAttribute<T>无法转换为T).
                        let mut ot = o.type_ref();
                        if matches!(o, Expr::Method { .. }) && !matches!(ot, TypeRef::G(_)) {
                            if let Some(g @ jcdc_jvm::GenericType::Class(_)) =
                                instantiated_method_ret(o, pool, pc)
                            {
                                ot = TypeRef::G(g);
                            }
                        }
                        match ot {
                        TypeRef::G(jcdc_jvm::GenericType::Class(cs)) => {
                            (crate::method::classsig_internal(&cs), cs.parts.last()?.args.clone())
                        }
                        t => match t.erased() {
                            jcdc_jvm::JavaType::Object(n) => {
                                // An erased read of an ENCLOSING class
                                // instance (a this$0 field): the outer
                                // class's own typevars are in scope inside
                                // the inner one, so parameterize with them
                                // (IdentityHashMap.this.put needs K/V).
                                if pc.internal_name.starts_with(&n)
                                    && pc.internal_name.as_bytes().get(n.len()) == Some(&b'$')
                                {
                                    (n.clone(), own_typevars(&n, pool))
                                } else {
                                    (n, Vec::new())
                                }
                            }
                            _ => return None,
                        },
                        }
                    },
                }
            }
        }
    };
    let d_str = format!(
        "({}){}",
        desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
        desc.ret.to_descriptor()
    );
    // Resolve the declaring class. The methodref owner names the RECEIVER
    // class even for inherited methods (OfDouble.accept:(Object)V is
    // declared as Sink<T>.accept(T)) — BFS down the super chain, carrying
    // each hop's type arguments, until a class actually declares
    // name+d_str with a usable Signature.
    //
    // Gate: only walk when the START class cannot host the call at source
    // level itself — no own method with name+d_str at all (bridges count:
    // when the receiver's parameterized type exposes an applicable bridge,
    // the call was source-resolved THERE and walking would re-instantiate
    // against sloppily-typed owner generics: `(T) this.state` for
    // combiner.apply — ReduceOps/ReferencePipeline/Collections x25).
    let start_walk = {
        let owned0;
        let cref0: &PoolClass = if decl == pc.internal_name {
            pc
        } else {
            match pool.get(&decl) {
                Some(p) => {
                    owned0 = p;
                    &owned0
                }
                None => return None,
            }
        };
        !(0..cref0.cf.methods.len())
            .any(|i| cref0.method_name(i) == Some(name) && desc_raw(cref0, i) == d_str)
    };
    if !start_walk {
        // Old direct-resolution behavior: require the Signature-carrying
        // declaration right on the receiver class.
        let owned0;
        let cref0: &PoolClass = if decl == pc.internal_name {
            pc
        } else {
            match pool.get(&decl) {
                Some(p) => {
                    owned0 = p;
                    &owned0
                }
                None => { return None; }
            }
        };
        let mi0 = match (0..cref0.cf.methods.len()).find(|&i| {
            cref0.method_name(i) == Some(name) && desc_raw(cref0, i) == d_str
        }) {
            Some(m) => m,
            None => { return None; }
        };
        let sb0 = match cref0.cf.methods[mi0].attributes.iter().find_map(|a| {
            if cref0.utf8(a.attribute_name_index) == Some("Signature") {
                Some(a.info.as_slice())
            } else {
                None
            }
        }) {
            Some(b) => b,
            None => { return None; }
        };
        if sb0.len() < 2 {
            return None;
        }
        let msig0 = match cref0
            .utf8(u16::from_be_bytes([sb0[0], sb0[1]]))
            .and_then(|x| jcdc_jvm::parse_method_signature(x))
        {
            Some(m) => m,
            None => { return None; }
        };
        if !msig0.params.is_empty() {
            return None;
        }
        // No class Signature = non-generic declaring class: empty
        // substitution domain (parseEnumValue's parameterized formals
        // need no substitution at all).
        let cp0_params: Vec<jcdc_jvm::TypeParam> = cref0
            .class_attr("Signature")
            .and_then(|b| {
                if b.len() < 2 {
                    return None;
                }
                cref0
                    .utf8(u16::from_be_bytes([b[0], b[1]]))
                    .and_then(|x| parse_class_signature(x))
            })
            .map(|cs| cs.params)
            .unwrap_or_default();
        if cp0_params.len() != args.len() {
            return None;
        }
        let inst0: Vec<jcdc_jvm::GenericType> = msig0
            .args
            .iter()
            .map(|t| crate::method::subst_typevars(t, &cp0_params, &args))
            .collect();
        if inst0.iter().any(crate::method::has_nested_wildcard) {
            return None;
        }
        return Some(inst0);
    }
    let mut queue: std::collections::VecDeque<(String, Vec<jcdc_jvm::GenericType>)> =
        std::collections::VecDeque::new();
    queue.push_back((decl.clone(), args.clone()));
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    seen.insert(decl.clone());
    let mut resolved: Option<(String, Vec<jcdc_jvm::GenericType>)> = None;
    let mut hops = 0usize;
    while let Some((cur, cur_args)) = queue.pop_front() {
        hops += 1;
        if hops > 24 {
            break;
        }
        let owned;
        let cref: &PoolClass = if cur == pc.internal_name {
            pc
        } else {
            match pool.get(&cur) {
                Some(p) => {
                    owned = p;
                    &owned
                }
                None => continue,
            }
        };
        let declares = (0..cref.cf.methods.len()).any(|i| {
            cref.method_name(i) == Some(name) && desc_raw(cref, i) == d_str
                && cref.cf.methods[i].attributes.iter().any(|a| {
                    cref.utf8(a.attribute_name_index) == Some("Signature")
                })
        });
        if declares {
            resolved = Some((cur, cur_args));
            break;
        }
        // Expanding with fewer instantiation args than the class declares
        // typevars leaves FOREIGN typevars unsubstituted (raw-owner call
        // BinaryOperator.apply with args=[] would carry BinaryOperator's
        // own `(T)` into the param casts — ReduceOps `(T) this.state`).
        // Such a path carries no real instantiation; drop it.
        let own_params = cref
            .class_attr("Signature")
            .and_then(|b| {
                if b.len() >= 2 {
                    cref.utf8(u16::from_be_bytes([b[0], b[1]]))
                        .and_then(|x| parse_class_signature(x))
                } else {
                    None
                }
            })
            .map(|cs| cs.params.len())
            .unwrap_or(0);
        if own_params > cur_args.len() {
            continue;
        }
        for (sn, sargs) in class_supers_args(cref, &cur_args) {
            if seen.insert(sn.clone()) {
                queue.push_back((sn, sargs));
            }
        }
    }
    let (dclass, dargs) = resolved?;
    let dpc;
    let dref: &PoolClass = if dclass == pc.internal_name {
        pc
    } else {
        dpc = pool.get(&dclass)?;
        &dpc
    };
    let mi = (0..dref.cf.methods.len()).find(|&i| {
        dref.method_name(i) == Some(name) && desc_raw(dref, i) == d_str
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
    // A declaring class WITHOUT a class Signature is simply non-generic:
    // treat its (empty) parameter list as the substitution domain rather
    // than bailing — the method's own Signature still carries the
    // parameterized formals (AnnotationParser.parseEnumValue's
    // `(Class<? extends Enum>) memberType` source cast was lost because
    // the whole path returned None here).
    let class_params = dref
        .class_attr("Signature")
        .and_then(|b| {
            if b.len() < 2 {
                return None;
            }
            let i2 = u16::from_be_bytes([b[0], b[1]]);
            dref.utf8(i2).and_then(|s| jcdc_jvm::parse_class_signature(s))
        })
        .unwrap_or_else(|| jcdc_jvm::ClassSignature {
            params: Vec::new(),
            superclass: jcdc_jvm::GenericType::Class(jcdc_jvm::ClassSig {
                package: String::new(),
                parts: vec![jcdc_jvm::ClassSigPart { name: "Object".into(), args: Vec::new() }],
            }),
            interfaces: Vec::new(),
        });
    if class_params.params.len() != dargs.len() {
        return None;
    }
    let inst: Vec<jcdc_jvm::GenericType> = msig
        .args
        .iter()
        .map(|t| crate::method::subst_typevars(t, &class_params.params, &dargs))
        .collect();
    // Captured owner arguments can nest wildcards, which is not valid Java.
    if inst.iter().any(crate::method::has_nested_wildcard) {
        return None;
    }
    // The instantiated parameter types must be expressible at the call
    // site: a typevar only renders legally when the enclosing class
    // declares it (CAST_BANNED_TVARS covers static contexts downstream).
    fn mentions_tvar(g: &jcdc_jvm::GenericType) -> bool {
        use jcdc_jvm::GenericType as G;
        match g {
            G::TypeVar(_) => true,
            G::Array(i) => mentions_tvar(i),
            G::Class(cs) => cs.parts.iter().any(|p| p.args.iter().any(mentions_tvar)),
            G::Wildcard(jcdc_jvm::WildcardBound::Extends(t))
            | G::Wildcard(jcdc_jvm::WildcardBound::Super(t)) => mentions_tvar(t),
            _ => false,
        }
    }
    if inst.iter().any(mentions_tvar) {
        let in_scope: HashSet<String> = pc
            .class_attr("Signature")
            .and_then(|b| {
                if b.len() >= 2 {
                    pc.utf8(u16::from_be_bytes([b[0], b[1]]))
                        .and_then(|x| parse_class_signature(x))
                } else {
                    None
                }
            })
            .map(|cs| cs.params.iter().map(|p| p.name.clone()).collect())
            .unwrap_or_default();
        fn all_tvars_in(g: &jcdc_jvm::GenericType, scope: &HashSet<String>) -> bool {
            use jcdc_jvm::GenericType as G;
            match g {
                G::TypeVar(n) => scope.contains(n),
                G::Array(i) => all_tvars_in(i, scope),
                G::Class(cs) => cs.parts.iter().all(|p| p.args.iter().all(|a| all_tvars_in(a, scope))),
                G::Wildcard(jcdc_jvm::WildcardBound::Extends(t))
                | G::Wildcard(jcdc_jvm::WildcardBound::Super(t)) => all_tvars_in(t, scope),
                _ => true,
            }
        }
        if !inst.iter().all(|t| all_tvars_in(t, &in_scope)) {
            return None;
        }
    }
    Some(inst)
}

fn desc_raw(pc: &PoolClass, mi: usize) -> String {
    pc.method_desc(mi).unwrap_or("").to_string()
}

/// Drop the raw-SAM disambiguation casts once the call carries an
/// explicit type witness: the witness pins the overload, and the raw cast
/// would type the lambda against the erased SAM (jdk26
/// CopyOnWriteArrayList.toArray: `(IntFunction) i -> (T[]) ..` — raw, the
/// body faces Object[] instead of T[]: Object[]无法转换为T[]). Only the
/// RAW erasure form of a formal's own class is dropped; parameterized
/// overload-disambiguation casts (DoubleConsumer vs Consumer<Double>)
/// stay.
fn prune_witnessed_raw_sam_casts(e: &mut Expr, pool: &ClassPool) {
    let Expr::Method { cls, name, desc, type_args, args, .. } = e else { return };
    if type_args.is_empty() {
        return;
    }
    let Some(dpc) = pool.get(cls.as_str()) else { return };
    let want_desc = format!(
        "({}){}",
        desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
        desc.ret.to_descriptor()
    );
    let Some(mi) = (0..dpc.cf.methods.len())
        .find(|&i| dpc.method_name(i) == Some(name.as_str()) && dpc.method_desc(i) == Some(want_desc.as_str()))
    else {
        return;
    };
    let Some(msig) = method_signature_of(&dpc, mi) else { return };
    if msig.args.len() != args.len() {
        return;
    }
    for (pos, (a, formal)) in args.iter_mut().zip(msig.args.iter()).enumerate() {
        let Expr::Cast { ty, e: inner } = a else { continue };
        if !matches!(&**inner, Expr::Lambda(_)) {
            continue;
        }
        let TypeRef::J(jcdc_jvm::JavaType::Object(raw_n)) = ty else { continue };
        let formal_class = match formal {
            jcdc_jvm::GenericType::Class(cs) => crate::method::classsig_internal(cs),
            _ => continue,
        };
        if &formal_class != raw_n {
            continue;
        }
        // The witness pins the TYPE ARGUMENTS, not the overload: when a
        // sibling same-name overload also takes an interface (lambda-
        // targetable) formal at this position, the bare lambda stays
        // ambiguous and the raw cast is the disambiguator
        // (AccessController.doPrivileged: PrivilegedAction vs
        // PrivilegedExceptionAction — pruning it revived 17
        // 引用不明确 errors across p11/sj17). Prune only when no sibling
        // can take the lambda (COWAL Reversed.toArray: the sibling
        // formal is T[], an array — never lambda-compatible).
        let sibling_sam = (0..dpc.cf.methods.len()).any(|oi| {
            if oi == mi || dpc.method_name(oi) != Some(name.as_str()) {
                return false;
            }
            let Some(od) = dpc.method_desc(oi).and_then(parse_method_descriptor) else {
                return false;
            };
            if od.args.len() != desc.args.len() {
                return false;
            }
            match od.args.get(pos) {
                Some(jcdc_jvm::JavaType::Object(n)) if n != raw_n => pool
                    .get(n.as_str())
                    .map(|ipc| ipc.is_interface())
                    .unwrap_or(false),
                _ => false,
            }
        });
        if sibling_sam {
            continue;
        }
        let v = std::mem::replace(a, Expr::This);
        if let Expr::Cast { e: inner, .. } = v {
            *a = *inner;
        }
    }
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
/// Explicit `.<R>mapMulti` witness recovered from the lambda impl body.
/// javac erases R in the indy's instantiatedMethodType, but the bare call
/// infers R := Object and the chain terminal fails to convert (jdk26
/// AbstractUnboundModel `List<Object>无法转换为List<Attribute<?>>`,
/// BufferedCodeBuilder, BufferedMethodBuilder `Optional<Object>`). R is
/// the static type of the value the body feeds to `sink.accept(..)` —
/// exactly what the source witness names.
fn mapmulti_witness_from_body(
    cls: &str,
    name: &str,
    type_args: &[String],
    args: &[Expr],
    pool: &ClassPool,
    pc: &PoolClass,
) -> Option<Vec<String>> {
    if !type_args.is_empty() || name != "mapMulti" || cls != "java/util/stream/Stream" {
        return None;
    }
    let Expr::Lambda(l) = args.first()? else { return None };
    if l.kind == crate::expr::LambdaKind::MethodRef {
        return None;
    }
    let dpc_owned;
    let dpc: &PoolClass = if l.impl_owner == pc.internal_name {
        pc
    } else {
        dpc_owned = pool.get(l.impl_owner.as_str())?;
        &dpc_owned
    };
    let mi = dpc.find_own_method(&l.impl_name, &l.impl_desc.to_string())?;
    let mb = decompile_method(dpc, pool, mi).ok()??;
    // BiConsumer<T, Consumer<R>>: the sink is the LAST impl param
    // (params are [captures..., e, sink]).
    let sink = mb
        .vt
        .vars
        .iter()
        .rev()
        .find(|v| v.is_param && v.name != "this")?
        .id;
    fn scan_e(e: &Expr, sink: u32, out: &mut Option<TypeRef>) {
        if out.is_some() {
            return;
        }
        if let Expr::Method { name, owner, args, .. } = e {
            if name == "accept" && args.len() == 1 {
                if let Some(Expr::Local { var, .. }) = owner.as_deref() {
                    if *var == sink {
                        *out = Some(args[0].type_ref());
                        return;
                    }
                }
            }
        }
        match e {
            Expr::Method { owner, args, .. } => {
                if let Some(o) = owner {
                    scan_e(o, sink, out);
                }
                args.iter().for_each(|a| scan_e(a, sink, out));
            }
            Expr::Cast { e: i, .. } => scan_e(i, sink, out),
            Expr::Cond { c, t, f } => {
                scan_e(c, sink, out);
                scan_e(t, sink, out);
                scan_e(f, sink, out);
            }
            Expr::Bin { l, r, .. } => {
                scan_e(l, sink, out);
                scan_e(r, sink, out);
            }
            Expr::Lambda(l2) => l2.captures.iter().for_each(|c| scan_e(c, sink, out)),
            _ => {}
        }
    }
    fn scan_s(s: &Stmt, sink: u32, out: &mut Option<TypeRef>) {
        if out.is_some() {
            return;
        }
        match s {
            Stmt::Block(v) => v.iter().for_each(|x| scan_s(x, sink, out)),
            Stmt::ExprStmt(e) => scan_e(e, sink, out),
            Stmt::LocalDef { init: Some(e), .. } => scan_e(e, sink, out),
            Stmt::Return(Some(e)) | Stmt::Throw(e) => scan_e(e, sink, out),
            Stmt::If { cond, then_stmt, else_stmt, .. } => {
                scan_e(cond, sink, out);
                scan_s(then_stmt, sink, out);
                if let Some(x) = else_stmt {
                    scan_s(x, sink, out);
                }
            }
            Stmt::While { cond, body, .. } | Stmt::DoWhile { body, cond, .. } => {
                scan_e(cond, sink, out);
                scan_s(body, sink, out);
            }
            Stmt::For { init, cond, update, body, .. } => {
                init.iter().for_each(|i| scan_s(i, sink, out));
                if let Some(c) = cond {
                    scan_e(c, sink, out);
                }
                update.iter().for_each(|u| scan_e(u, sink, out));
                scan_s(body, sink, out);
            }
            Stmt::ForEach { .. } => {}
            Stmt::Try { body, catches, finally, .. } => {
                scan_s(body, sink, out);
                for c in catches {
                    scan_s(&c.body, sink, out);
                }
                if let Some(f) = finally {
                    scan_s(f, sink, out);
                }
            }
            Stmt::Switch { cases, default, .. } => {
                for c in cases {
                    c.body.iter().for_each(|x| scan_s(x, sink, out));
                }
                if let Some(d) = default {
                    scan_s(d, sink, out);
                }
            }
            Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => scan_s(body, sink, out),
            _ => {}
        }
    }
    let mut got: Option<TypeRef> = None;
    scan_s(&mb.body, sink, &mut got);
    let g = match got? {
        TypeRef::G(g) => g,
        TypeRef::J(jt) => {
            fn jt_to_g(jt: &jcdc_jvm::JavaType) -> jcdc_jvm::GenericType {
                match jt {
                    jcdc_jvm::JavaType::Object(n) => {
                        let (pkg, simple) = match n.rfind('/') {
                            Some(i) => (n[..i].to_string(), n[i + 1..].to_string()),
                            None => (String::new(), n.clone()),
                        };
                        jcdc_jvm::GenericType::Class(jcdc_jvm::ClassSig {
                            package: pkg,
                            parts: vec![jcdc_jvm::ClassSigPart { name: simple, args: Vec::new() }],
                        })
                    }
                    jcdc_jvm::JavaType::Array(i) => {
                        jcdc_jvm::GenericType::Array(Box::new(jt_to_g(i)))
                    }
                    _ => return jcdc_jvm::GenericType::TypeVar(String::new()),
                }
            }
            let g = jt_to_g(&jt);
            if matches!(g, jcdc_jvm::GenericType::TypeVar(_)) {
                return None;
            }
            g
        }
    };
    let s = g.to_java();
    // Captured wildcards are not denotable in a source witness.
    if s.is_empty() || s.contains("CAP#") || s.contains("capture") {
        return None;
    }
    Some(vec![s])
}

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
    // The chosen overload's generic Signature parameter (when concrete and
    // non-generic-method): a RAW SAM cast types the lambda params at the
    // erasure (DerInputStream `(Predicate) t -> t.byteValue()` — t:Object,
    // 找不到符号), while `(Predicate<Byte>)` keeps the body well-typed.
    let msig_args: Option<(bool, Vec<jcdc_jvm::GenericType>)> = (0..dref.cf.methods.len())
        .find(|&i| {
            dref.method_name(i) == Some(name.as_str())
                && dref.method_desc(i) == Some(format!(
                    "({}){}",
                    desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
                    desc.ret.to_descriptor()
                ).as_str())
        })
        .and_then(|mi| {
            dref.cf.methods[mi].attributes.iter().find_map(|a| {
                if dref.utf8(a.attribute_name_index) == Some("Signature") {
                    Some(a.info.as_slice())
                } else {
                    None
                }
            })
        })
        .and_then(|b| {
            if b.len() < 2 {
                return None;
            }
            dref.utf8(u16::from_be_bytes([b[0], b[1]]))
                .and_then(|x| jcdc_jvm::parse_method_signature(x))
        })
        .map(|ms| (ms.params.is_empty(), ms.args.clone()));
    fn mentions_tvar(g: &jcdc_jvm::GenericType) -> bool {
        use jcdc_jvm::GenericType as G;
        match g {
            G::TypeVar(_) => true,
            G::Array(i) => mentions_tvar(i),
            G::Class(cs) => cs.parts.iter().any(|p| p.args.iter().any(mentions_tvar)),
            G::Wildcard(jcdc_jvm::WildcardBound::Extends(t))
            | G::Wildcard(jcdc_jvm::WildcardBound::Super(t)) => mentions_tvar(t),
            _ => false,
        }
    }
    for (i, a) in args.iter_mut().enumerate() {
        // VARARGS calls carry more expanded args than the descriptor has
        // formals (ObjectInputStream's `readObject(String...)`-style sites):
        // the tail args map to the array formal — never SAM-ambiguous
        // positions, and indexing ambiguous/desc.args past the formal count
        // panicked (MethodHandles, ObjectInputStream, ModuleInfo...).
        if i >= ambiguous.len() || !ambiguous[i] || !matches!(a, Expr::Lambda(_)) {
            continue;
        }
        let mut sam = TypeRef::J(desc.args[i].clone());
        if let Some((true, sig_args)) = &msig_args {
            if let Some(g @ jcdc_jvm::GenericType::Class(cs)) = sig_args.get(i) {
                if cs.parts.iter().any(|p| !p.args.is_empty()) && !mentions_tvar(g) {
                    sam = TypeRef::G(g.clone());
                }
            }
        }
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
                    // VARARGS calls carry more expanded args than the
                    // Signature has formals (Arrays.asList("a","b") vs
                    // (T[])List<T>): the variadic tail's formal is always
                    // G::Array, which the cast loop below skips anyway,
                    // so tail args simply never pin.
                    if j == i || j >= msig.args.len() {
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
    if let TypeRef::G(jcdc_jvm::GenericType::Class(cs)) = ty {
        if let Some(part) = cs.parts.last() {
            if !part.args.is_empty() {
                let arg_tys: Vec<jcdc_jvm::JavaType> =
                    args.iter().map(|a| a.type_ref().erased()).collect();
                return instantiated_ctor_params_core(cls, &part.args, args.len(), pool, &arg_tys);
            }
        }
    }
    // Raw or non-generic new: the ctor's own Signature formals may still
    // be parameterized (jdk11 EnumConstantNotPresentExceptionProxy
    // `(Class<? extends Enum<?>>, String)` — the source cast on the arg
    // leaves only an erased checkcast in bytecode). Generic classes with
    // an empty domain safely bail on the arity check inside.
    let arg_tys: Vec<jcdc_jvm::JavaType> =
        args.iter().map(|a| a.type_ref().erased()).collect();
    instantiated_ctor_params_core(cls, &[], args.len(), pool, &arg_tys)
}

fn instantiated_ctor_params_core(
    cls: &str,
    inst_args: &[jcdc_jvm::GenericType],
    nargs: usize,
    pool: &ClassPool,
    arg_tys: &[jcdc_jvm::JavaType],
) -> Option<Vec<jcdc_jvm::GenericType>> {
    let dpc = { let x = pool.get(cls); if x.is_none() && std::env::var("JCDC_DBG_WIT").is_ok() { eprintln!("MRTA s1 dpc {}", cls); } x? };
    // A class WITHOUT a class Signature is non-generic: empty substitution
    // domain instead of a bail (EnumConstantNotPresentExceptionProxy's
    // `(Class<? extends Enum<?>>)` ctor formal needs the param casts).
    let class_params: Vec<jcdc_jvm::TypeParam> = dpc
        .class_attr("Signature")
        .and_then(|b| {
            if b.len() >= 2 {
                dpc.utf8(u16::from_be_bytes([b[0], b[1]])).and_then(|x| parse_class_signature(x))
            } else {
                None
            }
        })
        .map(|cs| cs.params)
        .unwrap_or_default();
    if class_params.len() != inst_args.len() {
        return None;
    }
    // Among same-arity ctors prefer one WITH a Signature attribute:
    // javac omits it when the generic form equals the descriptor, and a
    // primitive-form sibling (HashMap(int) vs HashMap(Map<? extends K,
    // ? extends V>)) would otherwise win the table-order scan and bail
    // the whole resolution (jdk17 PropertyResourceBundle lookup diamond).
    let has_sig = |i: usize| {
        dpc.cf.methods[i]
            .attributes
            .iter()
            .any(|a| dpc.utf8(a.attribute_name_index) == Some("Signature"))
    };
    let arity_ok = |i: usize| {
        dpc.method_desc(i)
            .and_then(|d| parse_method_descriptor(d))
            .map(|md| md.args.len() == nargs)
            .unwrap_or(false)
    };
    // Among same-arity ctors prefer Signature-bearing ones, scored by
    // erased-formal compatibility with the actual arg types: jdk17
    // Nodes$ToArrayTask$OfPrimitive has TWO 3-arg ctors —
    // (T_NODE, T_ARR, int) and (OfPrimitive<..>, T_NODE, int) — arity
    // order picked the first and the makeChild diamond args lost their
    // (T_NODE) casts (无法推断OfPrimitive<> x3 trees).
    let score = |i: usize| -> Option<i32> {
        if !has_sig(i) {
            return None;
        }
        let md = dpc.method_desc(i).and_then(|d| parse_method_descriptor(d))?;
        if arg_tys.is_empty() || md.args.len() != arg_tys.len() {
            return Some(0);
        }
        let mut sc = 0i32;
        for (f, a) in md.args.iter().zip(arg_tys.iter()) {
            sc += match (f, a) {
                (jcdc_jvm::JavaType::Object(x), jcdc_jvm::JavaType::Object(y)) if x == y => 2,
                (jcdc_jvm::JavaType::Array(_), jcdc_jvm::JavaType::Array(_)) => 2,
                (x, y) if x == y => 2,
                (_, jcdc_jvm::JavaType::Object(y)) if y == "java/lang/Object" => 1,
                (jcdc_jvm::JavaType::Object(x), jcdc_jvm::JavaType::Object(y))
                    if is_subtype_of(pool, &jcdc_jvm::JavaType::Object(y.clone()), x) =>
                {
                    1
                }
                _ => 0,
            };
        }
        Some(sc)
    };
    let mut best: Option<(usize, i32)> = None;
    for i in 0..dpc.cf.methods.len() {
        if dpc.method_name(i) != Some("<init>") || !arity_ok(i) {
            continue;
        }
        if let Some(sc) = score(i) {
            if best.map(|(_, b)| sc > b).unwrap_or(true) {
                best = Some((i, sc));
            }
        }
    }
    let mi = best
        .map(|(i, _)| i)
        .or_else(|| {
            (0..dpc.cf.methods.len())
                .find(|&i| dpc.method_name(i) == Some("<init>") && arity_ok(i))
        });
    let mi = mi?;
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
        .map(|t| crate::method::subst_typevars(t, &class_params, inst_args))
        .collect();
    if inst.iter().any(crate::method::has_nested_wildcard) {
        return None;
    }
    Some(inst)
}

/// Bound erasure lookup that also covers METHOD typevars (the caller's
/// `<V extends Number,A> read(...)` — V is not a class param).
pub(crate) fn typevar_bound_erasure_in(
    n: &str,
    caller_params: &[jcdc_jvm::TypeParam],
    pc: &PoolClass,
) -> Option<jcdc_jvm::JavaType> {
    if let Some(p) = caller_params.iter().find(|p| p.name == n) {
        let b = p
            .class_bound
            .clone()
            .or_else(|| p.interface_bounds.first().cloned())?;
        return Some(TypeRef::G(b).erased());
    }
    typevar_bound_erasure(n, pc)
}

/// The erasure of a class typevar's leftmost bound (T_NODE extends
/// Node<P_OUT> → Node): generic_to_erased flattens a bare TypeVar to
/// Object, losing the bound the checkcast/erasure-alignment checks need.
fn typevar_bound_erasure(n: &str, pc: &PoolClass) -> Option<jcdc_jvm::JavaType> {
    pc.class_attr("Signature")
        .and_then(|b| {
            if b.len() < 2 {
                return None;
            }
            pc.utf8(u16::from_be_bytes([b[0], b[1]]))
                .and_then(|s| parse_class_signature(s))
        })
        .and_then(|sig| {
            sig.params
                .iter()
                .find(|p| p.name == n)
                // `T_NODE::Ljava/util/stream/Node<TP_OUT;>;` — an EMPTY
                // class bound with the real bound first among interfaces.
                .and_then(|p| {
                    p.class_bound
                        .clone()
                        .or_else(|| p.interface_bounds.first().cloned())
                })
                .map(|cb| TypeRef::G(cb).erased())
        })
}

/// Ctor Signature formals EXCLUDE the synthetic outer-instance/marker
/// parameters that Expr::New's args may still carry (member-inner news
/// prepend the outer `this`): align the instantiated formals with the
/// TRAIL of the args, never the head (jdk26 ReverseOrderSortedMapView:
/// Submap's `(K head, K tail)` zipped against `(this, fromKey, toKey)`
/// cast the outer this to `(K)` — "找不到符号 类 Submap").
fn apply_ctor_param_casts(
    args: &mut [Expr],
    params: &[jcdc_jvm::GenericType],
    pool: &ClassPool,
    pc: Option<&PoolClass>,
    caller_params: &[jcdc_jvm::TypeParam],
) {
    let off = args.len().saturating_sub(params.len());
    apply_param_casts(&mut args[off..], params, pool, pc, caller_params);
}

/// Apply per-argument source casts for a call/ctor whose instantiated
/// parameter types are known (see cast_wildcard_call_args).
fn apply_param_casts(
    args: &mut [Expr],
    params: &[jcdc_jvm::GenericType],
    pool: &ClassPool,
    pc: Option<&PoolClass>,
    caller_params: &[jcdc_jvm::TypeParam],
) {
    let apc_dbg = std::env::var("JCDC_DBG_APC").is_ok();
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
                        // An ARRAY-of-typevar formal (`(E[]) input` — jdk17
                        // ImmutableCollections.listFromTrustedArrayNullsAllowed:
                        // the source cast erases away because E[] and Object[]
                        // coincide; without it the ListN<> diamond got E :=
                        // Object from the raw varargs actual against the
                        // target's E equality, 无法推断ListN<>).
                        t @ jcdc_jvm::GenericType::Array(_)
                            if crate::method::contains_typevar(t) =>
                        {
                            Some(t.clone())
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
                    if apc_dbg {
                        eprintln!("APC2 pos want={:?} actual={:?} banned={:?}", want,
                            std::mem::discriminant(a),
                            CAST_BANNED_TVARS.with(|b| b.borrow().clone()));
                    }
                    // Generic-method arguments infer their own type at the
                    // call site; a frozen cast would break unification.
                    if is_generic_call(a, pool) {
                        continue;
                    }
                    // A diamond new at a parameterized formal of the SAME
                    // class takes the formal's args: checked.add(new
                    // SimpleImmutableEntry<>(k, v)) against List<Entry<K,V>>
                    // .add(Entry<K,V>) — jdk11 CheckedMap.putAll: the
                    // source's (K)k/(V)v arg casts erase away (Object→
                    // Object) and the bare diamond over Object args fails
                    // inference (无法推断SimpleImmutableEntry<>的类型参数).
                    if let Expr::New { cls: acls, args: aargs, ty: aty, .. } = a {
                        if let jcdc_jvm::GenericType::Class(wcs) = &want {
                            // Same class: the formal's args are the diamond's
                            // own. Supertype formal (Entry<K,V> against a
                            // SimpleImmutableEntry diamond): resolve through
                            // the supertype unification.
                            let wargs = if crate::method::classsig_internal(wcs) == *acls {
                                wcs.parts.last().map(|p| p.args.clone()).unwrap_or_default()
                            } else {
                                diamond_args_from_target(acls, wcs, pool).unwrap_or_default()
                            };
                            {
                                if !wargs.is_empty() {
                                    // Pin the resolved instantiation on the
                                    // New itself: a wildcard-bearing ctor
                                    // arg strips the diamond at print time
                                    // (the raw new then fails the capture
                                    // formal — jdk26 LazyCollections
                                    // LazyEntry), while explicit args keep
                                    // the value convertible.
                                    {
                                        let already = matches!(aty, TypeRef::G(jcdc_jvm::GenericType::Class(cs2))
                                            if cs2.parts.last().map(|p| !p.args.is_empty()).unwrap_or(false));
                                        if !already {
                                            let ncs = jcdc_jvm::ClassSig {
                                                package: acls
                                                    .rfind('/')
                                                    .map(|i| acls[..i].to_string())
                                                    .unwrap_or_default(),
                                                parts: vec![jcdc_jvm::ClassSigPart {
                                                    name: acls
                                                        .rsplit('/')
                                                        .next()
                                                        .unwrap_or(acls)
                                                        .to_string(),
                                                    args: wargs.clone(),
                                                }],
                                            };
                                            *aty = TypeRef::G(jcdc_jvm::GenericType::Class(ncs));
                                        }
                                    }
                                    let arg_tys: Vec<jcdc_jvm::JavaType> = aargs
                                        .iter()
                                        .map(|x| x.type_ref().erased())
                                        .collect();
                                    if let Some(sub) = instantiated_ctor_params_core(
                                        acls,
                                        &wargs,
                                        aargs.len(),
                                        pool,
                                        &arg_tys,
                                    ) {
                                        let off = aargs.len().saturating_sub(sub.len());
                                        for (na, np) in
                                            aargs[off..].iter_mut().zip(sub.iter())
                                        {
                                            if !matches!(
                                                np,
                                                jcdc_jvm::GenericType::TypeVar(_)
                                            ) {
                                                continue;
                                            }
                                            if matches!(na, Expr::Cast { .. } | Expr::Const(_)) {
                                                continue;
                                            }
                                            if !matches!(
                                                na.type_ref(),
                                                TypeRef::J(jcdc_jvm::JavaType::Object(_))
                                            ) {
                                                continue;
                                            }
                                            if CAST_BANNED_TVARS.with(|b| {
                                                let b = b.borrow();
                                                !b.is_empty()
                                                    && g_mentions_tvar_named(np, &b)
                                            }) {
                                                continue;
                                            }
                                            let inner = std::mem::replace(na, Expr::This);
                                            *na = Expr::Cast {
                                                ty: TypeRef::G(np.clone()),
                                                e: Box::new(inner),
                                            };
                                        }
                                    }
                                }
                            }
                        }
                        continue;
                    }
                    // Class typevars are not in scope in static contexts
                    // (unsubstituted field-signature parameterization).
                    if CAST_BANNED_TVARS.with(|b| {
                        let b = b.borrow();
                        !b.is_empty() && g_mentions_tvar_named(&want, &b)
                    }) {
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
                    // A CONDITIONAL's type_ref reports the first branch's
                    // type, but javac glues divergent branches to their LUB
                    // (`!REVERSE ? e0 : e1` with e0:E, e1:Object types at
                    // Object — jdk26 ImmutableCollections Set12.forEach,
                    // "Object无法转换为CAP#1"): the equality shortcut only
                    // holds when BOTH branches already carry the want type.
                    let cond_mixed = matches!(a, Expr::Cond { t, f, .. }
                        if t.type_ref() != TypeRef::G(want.clone())
                            || f.type_ref() != TypeRef::G(want.clone()));
                    if !capture_read && !cond_mixed && a.type_ref() == TypeRef::G(want.clone()) {
                        continue;
                    }
                    if matches!(a, Expr::Cast { .. } | Expr::Const(_)) {
                        continue;
                    }
                    // An actual whose erasure is a SUBTYPE of a wildcard-
                    // parameterized formal's class needs the RAW source
                    // cast: the precise form is inconvertible and the bare
                    // actual poisons diamond/inference (jdk17
                    // PropertyResourceBundle this.lookup = new HashMap<>
                    // ((Map) properties) — with the bare Properties actual
                    // the diamond's K got an Object upper bound against
                    // the String equality constraint, 无法推断HashMap<>).
                    if let (
                        TypeRef::J(jcdc_jvm::JavaType::Object(an)),
                        jcdc_jvm::GenericType::Class(cw),
                    ) = (&a.type_ref(), &want)
                    {
                        let cw_internal = crate::method::classsig_internal(cw);
                        if cw.parts.iter().any(|p| {
                            p.args.iter().any(crate::classdec::g_has_wildcard)
                        }) && an != &cw_internal
                            && !matches!(a, Expr::Cast { .. } | Expr::Const(_) | Expr::Lambda(_))
                            && is_subtype_of(
                                pool,
                                &jcdc_jvm::JavaType::Object(an.clone()),
                                &cw_internal,
                            )
                        {
                            // Prefer the PRECISE cast when the actual's
                            // source-level type converts to the formal
                            // (jdk17 PKIX: new ArrayList<>((List<
                            // X509Certificate>) certPath.getCertificates())
                            // — the raw (Collection) form forced the
                            // diamond's E := Object against the target's
                            // X509Certificate equality, 无法推断ArrayList<>;
                            // Properties stays raw — its precise
                            // Map<Object,Object> is inconvertible to
                            // Map<? extends String,..>).
                            // Precise form: rebuild the actual's SOURCE
                            // class with the formal's wildcard-stripped
                            // args (jdk17 PKIX: getCertificates() sources
                            // as List<? extends Certificate>, the formal
                            // is Collection<? extends X509Certificate> —
                            // the source cast (List<X509Certificate>) is
                            // the unchecked downcast that feeds the
                            // diamond E := X509Certificate; the raw
                            // (Collection) form forced E := Object,
                            // 无法推断ArrayList<>).
                            let precise_ty: Option<TypeRef> = match pc {
                                Some(p) => instantiated_method_ret(a, pool, p).and_then(|src| {
                                    let cs_src = match &src {
                                        jcdc_jvm::GenericType::Class(c) => c,
                                        _ => return None,
                                    };
                                    let last_src = cs_src.parts.last()?;
                                    let last_w = cw.parts.last()?;
                                    if last_src.args.len() != last_w.args.len() {
                                        return None;
                                    }
                                    let stripped: Option<Vec<jcdc_jvm::GenericType>> = last_w
                                        .args
                                        .iter()
                                        .map(|w| match w {
                                            jcdc_jvm::GenericType::Wildcard(
                                                jcdc_jvm::WildcardBound::Extends(t),
                                            )
                                            | jcdc_jvm::GenericType::Wildcard(
                                                jcdc_jvm::WildcardBound::Super(t),
                                            ) if !g_has_wildcard(t) => Some((**t).clone()),
                                            jcdc_jvm::GenericType::Wildcard(_) => None,
                                            other => Some(other.clone()),
                                        })
                                        .collect();
                                    let stripped = stripped?;
                                    if stripped.iter().any(g_has_wildcard) {
                                        return None;
                                    }
                                    let mut fixed = cs_src.clone();
                                    if let Some(lp) = fixed.parts.last_mut() {
                                        lp.args = stripped;
                                    }
                                    Some(TypeRef::G(jcdc_jvm::GenericType::Class(fixed)))
                                }),
                                None => None,
                            };
                            let cast_ty = precise_ty.unwrap_or_else(|| {
                                TypeRef::J(jcdc_jvm::JavaType::Object(cw_internal.clone()))
                            });
                            let inner = std::mem::replace(a, Expr::This);
                            *a = Expr::Cast { ty: cast_ty, e: Box::new(inner) };
                            continue;
                        }
                    }
                    // A SUPER-wildcard formal's capture rejects raw and
                    // subtype values outright (no unchecked conversion to a
                    // capture variable): the precise cast to the stripped
                    // bound is the source shape (jdk26 LazyCollections
                    // LazyMapIterator.forEachRemaining — `action.accept(new
                    // LazyEntry<>(..))` printed raw by the diamond gate:
                    // "LazyEntry无法转换为CAP#1 from ? super Entry<K,V>").
                    if let jcdc_jvm::GenericType::Wildcard(jcdc_jvm::WildcardBound::Super(x)) = pt {
                        // A DIAMOND/raw New carries a G type with empty args
                        // in the AST but prints without parameterization —
                        // it needs the cast like any erased actual.
                        let diamond_new = {
                            let ar: &Expr = a;
                            match ar {
                                Expr::New { ty: TypeRef::G(jcdc_jvm::GenericType::Class(cs)), .. } => {
                                    cs.parts.last().map(|p| p.args.is_empty()).unwrap_or(true)
                                }
                                Expr::New { .. } => true,
                                _ => false,
                            }
                        };
                        if !matches!(a.type_ref(), TypeRef::G(_)) || diamond_new {
                            let have_er = a.type_ref().erased();
                            let x_er = TypeRef::G((**x).clone()).erased();
                            let aligned = match (&have_er, &x_er) {
                                (jcdc_jvm::JavaType::Object(hn), jcdc_jvm::JavaType::Object(xn)) => {
                                    hn == xn
                                        || is_subtype_of(
                                            pool,
                                            &jcdc_jvm::JavaType::Object(hn.clone()),
                                            xn,
                                        )
                                }
                                _ => false,
                            };
                            if aligned && !g_has_wildcard(x) {
                                let inner = std::mem::replace(a, Expr::This);
                                *a = Expr::Cast {
                                    ty: TypeRef::G((**x).clone()),
                                    e: Box::new(inner),
                                };
                                continue;
                            }
                        }
                    }
                    // Erasures must line up. A TypeVar formal erases to
                    // its leftmost BOUND, not Object (jdk11 Nodes.
                    // InternalNodeSpliterator.initStack: addFirst's
                    // formal N extends Node<T> against a getChild()
                    // actual erased to Node — javac elided the source
                    // `(N)` cast because the erasures coincide, and
                    // Deque<N>.addFirst(Node<T>) fails without it).
                    let have_ty = a.type_ref();
                    let mut have = have_ty.erased();
                    // `this` type_refs at java/lang/Object; the erasure
                    // gate needs the ENCLOSING class (the `(T) this`
                    // source cast against a self-bounded Attribute<T>).
                    if matches!(a, Expr::This) {
                        if let Some(p) = pc {
                            have = jcdc_jvm::JavaType::Object(p.internal_name.clone());
                        }
                    }
                    let want_er = match &want {
                        jcdc_jvm::GenericType::TypeVar(n) => caller_params
                            .iter()
                            .find(|p| &p.name == n)
                            .and_then(|p| {
                                p.class_bound
                                    .clone()
                                    .or_else(|| p.interface_bounds.first().cloned())
                            })
                            .map(|b| TypeRef::G(b).erased())
                            .or_else(|| pc.and_then(|p| typevar_bound_erasure(n, p)))
                            .unwrap_or_else(|| TypeRef::G(want.clone()).erased()),
                        _ => TypeRef::G(want.clone()).erased(),
                    };
                    let ok = match (&have, &want_er) {
                        (jcdc_jvm::JavaType::Object(x), jcdc_jvm::JavaType::Object(y)) if x == y => true,
                        // A TYPEVAR formal whose bound the actual's erasure
                        // SUBTYPES: javac elides the source `(T) x` cast
                        // whenever the erasure conversion is a no-op
                        // (jdk26 UnboundAttribute.writeTo: `(T) this`
                        // against A extends Attribute<A>, this:Unbound-
                        // Attribute implements Attribute — no checkcast in
                        // bytecode, and the bare actual fails to convert:
                        // UnboundAttribute<T>无法转换为T). Restrict to
                        // TypeVar wants: for Class wants a subtype actual
                        // is source-convertible without a cast.
                        (jcdc_jvm::JavaType::Object(x), jcdc_jvm::JavaType::Object(y))
                            if matches!(want, jcdc_jvm::GenericType::TypeVar(_)) =>
                        {
                            is_subtype_of(pool, &jcdc_jvm::JavaType::Object(x.clone()), y)
                        }
                        (jcdc_jvm::JavaType::Array(_), jcdc_jvm::JavaType::Array(_)) => true,
                        _ => false,
                    };
                    if apc_dbg {
                        eprintln!("APC3 have={:?} want_er={:?} ok={}", have, want_er, ok);
                    }
                    if !ok {
                        continue;
                    }
                    // An invariant-incompatible reparameterization of the
                    // same class (Collection<SocketPermission> against a
                    // Collection<Permission> formal — jdk11
                    // SocketPermissionCollection.elements) makes even the
                    // PRECISE cast inconvertible: javac rejects the cast
                    // itself. The source used the raw form. Wildcard
                    // positions keep the precise cast (a legal
                    // <? super Object> → <? super String> narrowing).
                    let raw_fallback = match (&have_ty, &want) {
                        (TypeRef::G(gx), jcdc_jvm::GenericType::Class(cw)) => {
                            concrete_g_mismatch(gx, &jcdc_jvm::GenericType::Class(cw.clone()))
                        }
                        _ => false,
                    };
                    let cast_ty = if raw_fallback {
                        TypeRef::J(TypeRef::G(want.clone()).erased())
                    } else {
                        TypeRef::G(want.clone())
                    };
                    if apc_dbg {
                        eprintln!("APC4 WRAPPED cast_ty={:?}", cast_ty);
                    }
                    let inner = std::mem::replace(a, Expr::This);
                    *a = Expr::Cast { ty: cast_ty, e: Box::new(inner) };
    }
}

/// Overload-disambiguation casts: the methodref descriptor records which
/// overload the source picked, but when the argument's static type fits
/// SEVERAL same-name same-arity overloads (Node.Builder.OfDouble is both
/// DoubleConsumer and Consumer<Double>), the untyped print is "对
/// tryAdvance的引用不明确". Cast the arg to the descriptor's param type —
/// exactly the source's `(DoubleConsumer) nodeBuilder` (an upcast with no
/// bytecode trace).
fn disambiguate_overload_args(e: &mut Expr, pool: &ClassPool) {
    let (cls, name, desc) = match &*e {
        Expr::Method { cls, name, desc, .. } => (cls.clone(), name.clone(), desc.clone()),
        _ => return,
    };
    if name == "<init>" {
        return;
    }
    let own_desc = format!(
        "({}){}",
        desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
        desc.ret.to_descriptor()
    );
    let Some(cpc) = pool.get(&cls) else { return };
    let mut variants: Vec<String> = Vec::new();
    for mi in 0..cpc.cf.methods.len() {
        if cpc.method_name(mi) != Some(name.as_str()) {
            continue;
        }
        if let Some(d) = cpc.method_desc(mi) {
            if d != own_desc {
                if let Some(md) = parse_method_descriptor(d) {
                    if md.args.len() == desc.args.len() {
                        variants.push(d.to_string());
                    }
                }
            }
        }
    }
    if variants.is_empty() {
        return;
    }
    let Expr::Method { args, .. } = e else { return };
    for (i, a) in args.iter_mut().enumerate() {
        if matches!(a, Expr::Cast { .. } | Expr::Const(_)) {
            continue;
        }
        let Some(jcdc_jvm::JavaType::Object(di)) = desc.args.get(i) else {
            continue;
        };
        let have = a.type_ref().erased();
        let jcdc_jvm::JavaType::Object(hn) = &have else {
            continue;
        };
        if hn == di || !is_subtype_of(pool, &have, di) {
            continue;
        }
        let ambiguous = variants.iter().any(|vd| {
            parse_method_descriptor(vd)
                .and_then(|md| md.args.get(i).cloned())
                .map(|t| {
                    matches!(&t, jcdc_jvm::JavaType::Object(on)
                        if on != di && is_subtype_of(pool, &have, on))
                })
                .unwrap_or(false)
        });
        if ambiguous {
            let inner = std::mem::replace(a, Expr::This);
            *a = Expr::Cast {
                ty: TypeRef::J(jcdc_jvm::JavaType::Object(di.clone())),
                e: Box::new(inner),
            };
        }
    }
}

/// Early pass (runs before the return-witness machinery): types field
/// reads, drops redundant raw self-casts, and upgrades RAW bytecode
/// checkcasts over generic calls to their instantiated returns. Running
/// before retype_witness_arg_casts matters: that pass deliberately
/// inserts raw casts for invariant-incompatible formals ((Collection)
/// perms.values()), and the upgrade must never rewrite them — it only
/// ever touches casts that exist at this point, i.e. real checkcasts
/// (jdk17 ModulePatcher: (List) e.getValue() upgrades to (List<String>)
/// feeding the stream/map chain — Object无法转换为String).
/// A raw-GENERIC-ELEMENT array cast over a generic call whose Signature
/// returns a typevar array erases to exactly this shape
/// (Arrays.copyOfRange(Class<?>[],..) -> (Class[]) — jdk26 MethodHandles
/// .longestParameterList: List.of over the raw Class[] types the chain at
/// List<Class>, inconvertible to the source's List<Class<?>>). Restore the
/// element form the call's actual array carries. Runs over the whole body
/// (the cast typically sits deep inside a lambda chain) and again in the
/// lambda-body print pipeline.
pub(crate) fn upgrade_typevar_array_casts(s: &mut Stmt, pool: &ClassPool, pc: &PoolClass) {
    fn fix(e: &mut Expr, pool: &ClassPool, pc: &PoolClass) {
        if let Expr::Cast { ty, e: ce } = e {
            if let TypeRef::J(jcdc_jvm::JavaType::Array(el)) = ty {
                if let jcdc_jvm::JavaType::Object(en) = el.as_ref() {
                    let generic = pool
                        .get(en.as_str())
                        .and_then(|epc| {
                            epc.class_attr("Signature").and_then(|b| {
                                if b.len() >= 2 {
                                    epc.utf8(u16::from_be_bytes([b[0], b[1]])).and_then(|x| parse_class_signature(x))
                                } else {
                                    None
                                }
                            })
                        })
                        .map(|cs| !cs.params.is_empty())
                        .unwrap_or(false);
                    if generic {
                        if let Some(el_g) = typevar_array_call_elem(ce, en, pool, pc) {
                            *ty = TypeRef::G(jcdc_jvm::GenericType::Array(Box::new(el_g)));
                        }
                    }
                }
            }
        }
        let f: fn(&mut Expr, &ClassPool, &PoolClass) = fix;
        walk_expr_children(e, pool, pc, &mut { f });
    }
    walk_stmt_exprs(s, pool, pc, &mut { fix });
}

pub(crate) fn upgrade_erased_call_casts(s: &mut Stmt, pool: &ClassPool, pc: &PoolClass) {
    fn fix(e: &mut Expr, pool: &ClassPool, pc: &PoolClass) {
        type_field_reads(e, pool, pc, true);
        let f: fn(&mut Expr, &ClassPool, &PoolClass) = fix;
        walk_expr_children(e, pool, pc, &mut { f });
    }
    walk_stmt_exprs(s, pool, pc, &mut { fix });
}

/// Type instance field reads with their instantiated Signature type
/// and drop raw self-casts over already-parameterized expressions:
/// javac emits a checkcast for erased inherited reads (jdk11
/// Nodes.CollectorTask.onCompletion: `(Nodes.CollectorTask)
/// this.leftChild` — leftChild is declared K on
/// AbstractTask<P_IN,P_OUT,R,K>, instantiated to
/// CollectorTask<P_IN,P_OUT,T_NODE,T_BUILDER>; the RAW cast erases
/// the receiver and getLocalResult() collapses to raw Node —
/// "Node无法转换为T_NODE" x2). With the read typed, the cast is
/// redundant and the call keeps its generic returns.
fn type_field_reads(e: &mut Expr, pool: &ClassPool, pc: &PoolClass, concrete_ok: bool) {
    fn type_one(e: &mut Expr, pool: &ClassPool, pc: &PoolClass) {
        if let Expr::Field { owner, cls, name, ty, is_static: false, .. } = e {
            if !matches!(ty, TypeRef::G(_)) {
                if let Some(g) =
                    crate::method::instantiated_field_type(owner.as_deref(), cls, name, pool, pc)
                {
                    *ty = g;
                }
            }
        }
    }
    // fix_expr is pre-order, but a cast upgrade needs its operand's
    // owner reads already typed (Cast{Node, Method{owner:
    // Cast{CollectorTask, Field leftChild}}} — the inner self-cast
    // must be dropped and the field typed before the outer (Node)
    // can resolve T_NODE). Recurse first; the walker's later revisit
    // is idempotent.
    match e {
        Expr::Cast { e: inner, .. } => type_field_reads(inner, pool, pc, concrete_ok),
        Expr::Method { owner, args, .. } => {
            if let Some(o) = owner {
                type_field_reads(o, pool, pc, concrete_ok);
            }
            args.iter_mut()
                .for_each(|a| type_field_reads(a, pool, pc, concrete_ok));
        }
        _ => {}
    }
    type_one(e, pool, pc);
    if let Expr::Cast { ty, e: inner } = e {
        // fix_expr is pre-order: type the cast's own operand before
        // deciding the cast is redundant.
        type_one(inner, pool, pc);
        let cast_internal = match ty {
            TypeRef::J(jcdc_jvm::JavaType::Object(n)) => Some(n.clone()),
            TypeRef::G(jcdc_jvm::GenericType::Class(cs))
                if cs.parts.iter().all(|p| p.args.is_empty()) =>
            {
                Some(crate::method::classsig_internal(cs))
            }
            _ => None,
        };
        let ty_erased = ty.erased();
        // Drop ONLY over a freshly typed FIELD read: a raw cast over a
        // wildcard-parameterized LOCAL (`(List) list` inserted by
        // raw_witness_capture_call_args to make an overloaded call
        // unchecked-applicable) is load-bearing — dropping it returned
        // 对于binarySearch(List<CAP#1>,T#1) 找不到合适的方法.
        let redundant_self_cast = match &cast_internal {
            Some(ci) => match (&**inner, inner.type_ref()) {
                (
                    Expr::Field { .. },
                    TypeRef::G(jcdc_jvm::GenericType::Class(ics)),
                ) => {
                    crate::method::classsig_internal(&ics) == *ci
                        // A WILDCARD-parameterized read keeps its raw
                        // cast: `(SetN) ImmutableCollections.EMPTY_SET`
                        // strips SetN<?>'s capture so the value assigns
                        // unchecked to Set<E> (jdk17 Set.of case 0 —
                        // SetN<CAP#1>无法转换为Set<E>; the source casts
                        // (Set<E>) which javac elides). Concrete/typevar
                        // args (leftChild) stay droppable.
                        && !ics.parts.iter().any(|p| {
                            p.args.iter().any(|a| {
                                matches!(a, jcdc_jvm::GenericType::Wildcard(_))
                                    || g_has_wildcard(a)
                            })
                        })
                }
                _ => false,
            },
            None => false,
        };
        if redundant_self_cast {
            let taken = std::mem::replace(&mut **inner, Expr::This);
            *e = taken;
        } else if cast_internal.is_some() && matches!(&**inner, Expr::Method { .. }) {
            // Only a RAW class cast (a real bytecode checkcast) may be
            // upgraded: a precise generic cast like `(T) it.next()`
            // (cast_generic_locals' synthesis for a T[] element store)
            // was being rewritten to the owner's typevar `(E)` —
            // ImmutableCollections SetN/SubList toArray "E无法转换为T"
            // x2 per tree.
            //
            // A raw erasure checkcast over a generic call is javac's
            // bridge from the erased return to the instantiated one
            // (Nodes.CollectorTask.onCompletion: getLocalResult()
            // :Object checkcast Node — the source expression is
            // already T_NODE via the typed receiver). Render the cast
            // at the instantiated return so the value keeps flowing
            // as T_NODE into apply(T_NODE,T_NODE)/setLocalResult
            // (T_NODE) — raw (Node) args are inconvertible
            // ("Node无法转换为T_NODE" x2).
            if std::env::var("JCDC_DBG_UPG").is_ok() {
                if let Expr::Method { name: mn, .. } = &**inner {
                    if mn == "getValue" {
                        eprintln!(
                            "UPG2 getValue cast_ty={:?} ret={:?}",
                            ty,
                            instantiated_method_ret(inner, pool, pc)
                        );
                    }
                }
            }
            if let Some(inst) = instantiated_method_ret(inner, pool, pc) {
                // A wildcard anywhere in the instantiated return is
                // not a legal cast target and would silently widen a
                // precise existing cast (`(Spliterator<E>)` →
                // `(Spliterator<? extends E>)` —
                // Spliterator<CAP#1>无法转换为Spliterator<E>).
                if g_has_wildcard(&inst) {
                    return;
                }
                // CONCRETE upgrades belong to the EARLY pass only (real
                // bytecode checkcasts): inside fix_expr they would rewrite
                // the deliberate raw casts that retype_witness_arg_casts /
                // apply_param_casts insert for inconvertible formals
                // ((Collection) perms.values() → Collection<SP> against a
                // Collection<Permission> formal — jdk11
                // SocketPermissionCollection.elements).
                if !concrete_ok && !crate::method::contains_typevar(&inst) {
                    return;
                }
                let matches_erasure = match &inst {
                    // The typevar's bound erases to the checkcast
                    // target (T_NODE extends Node<P_OUT> → Node).
                    jcdc_jvm::GenericType::TypeVar(n) => {
                        typevar_bound_erasure(n, pc)
                            .map(|b| b == ty_erased)
                            .unwrap_or(false)
                    }
                    _ => TypeRef::G(inst.clone()).erased() == ty_erased,
                };
                // Every typevar the upgraded form mentions must be
                // declared by the class being printed: FindOps
                // doLeaf's raw `(TerminalSink)` checkcast upgraded to
                // `(TerminalSink<T, O>)` where the enclosing scope
                // only declares O ("找不到符号 类 T").
                fn inst_tvars(g: &jcdc_jvm::GenericType, out: &mut Vec<String>) {
                    use jcdc_jvm::GenericType as GG;
                    match g {
                        GG::TypeVar(n) => {
                            if !out.contains(n) {
                                out.push(n.clone());
                            }
                        }
                        GG::Class(cs) => cs
                            .parts
                            .iter()
                            .for_each(|p| p.args.iter().for_each(|a| inst_tvars(a, out))),
                        GG::Array(i) => inst_tvars(i, out),
                        GG::Wildcard(jcdc_jvm::WildcardBound::Extends(t))
                        | GG::Wildcard(jcdc_jvm::WildcardBound::Super(t)) => {
                            inst_tvars(t, out)
                        }
                        _ => {}
                    }
                }
                let in_scope = {
                    let allowed = class_typevar_names(pc);
                    let mut mentioned: Vec<String> = Vec::new();
                    inst_tvars(&inst, &mut mentioned);
                    mentioned.iter().all(|n| allowed.contains(n))
                };
                if std::env::var("JCDC_DBG_UPG").is_ok() {
                    eprintln!("UPG3 me={} inscope={} inst={:?}", matches_erasure, in_scope, inst);
                }
                if matches_erasure && in_scope {
                    *ty = TypeRef::G(inst);
                }
            }
        }
    }
}

/// Generic call initializing a generically-declared local, with functional
/// (lambda/method-ref) arguments: the declared type is the inference target
/// the source used. `TerminalOp<T, LinkedHashSet<T>> reduceOp =
/// ReduceOps.<T, LinkedHashSet<T>>makeRef(LinkedHashSet::new, ...)` —
/// without the witness the raw-SAM-cast or bare forms die ("方法引用无效"
/// / 无法推断). When compute_witness recovers every callee typevar as a
/// denotable type, set the explicit type arguments and strip the raw
/// erasure casts wrapping the lambda args (the witness types the formals;
/// the raw casts would re-erase them and break method-ref arity).
fn witness_methodref_localdef_calls(
    s: &mut Stmt,
    vt: &crate::varalloc::VarTable,
    pool: &ClassPool,
    pc: &PoolClass,
    caller_params: &[jcdc_jvm::TypeParam],
) {
    fn fix(
        e: &mut Expr,
        want: &jcdc_jvm::GenericType,
        pool: &ClassPool,
        caller_params: &[jcdc_jvm::TypeParam],
    ) {
        let (cls, name, desc) = match &*e {
            Expr::Method { cls, name, desc, type_args, args, .. } if type_args.is_empty() => {
                // Every argument must be functional (possibly raw-cast):
                // a non-functional arg means the call is not the
                // lambda-overload shape the witness reconstructs.
                if !args.iter().all(|a| match a {
                    Expr::Lambda(_) => true,
                    Expr::Cast { e: i, .. } => matches!(&**i, Expr::Lambda(_)),
                    _ => false,
                }) {
                    return;
                }
                (cls.clone(), name.clone(), desc.clone())
            }
            _ => return,
        };
        let Some((w, _)) =
            compute_witness(cls.as_str(), name.as_str(), &desc, None, want, pool, Some(caller_params))
        else {
            return;
        };
        if let Expr::Method { type_args, args, .. } = e {
            *type_args = w;
            for a in args.iter_mut() {
                // Strip raw erasure casts wrapping the functional args:
                // with the call witnessed, the formals are concrete and
                // the raw cast would re-erase the SAM (breaking
                // method-ref arity).
                let raw_over_lambda = matches!(a, Expr::Cast { ty, e: i }
                    if matches!(ty, TypeRef::J(jcdc_jvm::JavaType::Object(_)))
                        && matches!(&**i, Expr::Lambda(_)));
                if raw_over_lambda {
                    let v = std::mem::replace(a, Expr::This);
                    if let Expr::Cast { e: i, .. } = v {
                        *a = *i;
                    }
                }
            }
        }
    }
    fn rec(
        s: &mut Stmt,
        vt: &crate::varalloc::VarTable,
        pool: &ClassPool,
        pc: &PoolClass,
        caller_params: &[jcdc_jvm::TypeParam],
    ) {
        let _ = pc;
        match s {
            Stmt::Block(v) => v
                .iter_mut()
                .for_each(|x| rec(x, vt, pool, pc, caller_params)),
            Stmt::LocalDef { var, init: Some(e), .. } => {
                if let TypeRef::G(want) = &vt.var(*var).ty {
                    fix(e, want, pool, caller_params);
                }
            }
            Stmt::If { then_stmt, else_stmt, .. } => {
                rec(then_stmt, vt, pool, pc, caller_params);
                if let Some(x) = else_stmt {
                    rec(x, vt, pool, pc, caller_params);
                }
            }
            Stmt::While { body, .. }
            | Stmt::DoWhile { body, .. }
            | Stmt::ForEach { body, .. }
            | Stmt::Labeled { body, .. }
            | Stmt::Synchronized { body, .. } => rec(body, vt, pool, pc, caller_params),
            Stmt::For { init, body, .. } => {
                init.iter_mut()
                    .for_each(|i| rec(i, vt, pool, pc, caller_params));
                rec(body, vt, pool, pc, caller_params);
            }
            Stmt::Switch { cases, default, .. } => {
                for c in cases.iter_mut() {
                    for st in c.body.iter_mut() {
                        rec(st, vt, pool, pc, caller_params);
                    }
                }
                if let Some(d) = default {
                    rec(d, vt, pool, pc, caller_params);
                }
            }
            Stmt::Try { body, catches, finally } => {
                rec(body, vt, pool, pc, caller_params);
                for c in catches.iter_mut() {
                    rec(&mut c.body, vt, pool, pc, caller_params);
                }
                if let Some(f) = finally {
                    rec(f, vt, pool, pc, caller_params);
                }
            }
            _ => {}
        }
    }
    rec(s, vt, pool, pc, caller_params);
}

/// Fold the desugared GUARDED-PATTERN restart shape back into a `when`
/// guard (jdk26 DecimalFormat/CompactNumberFormat 此 case 标签由前一个 case
/// 标签支配 x4). javac compiles `case BigInteger bi when bi.bitLength() < 64
/// -> body` into a restart-loop case that tests the guard and, on failure,
/// bumps the typeSwitch state and continues; the restored pattern switch
/// then carries the SAME type label twice (guarded + unguarded), which
/// javac rejects. Recognize the shape per case group:
/// `[T v = (T) sel;]? if (guard) { body } else { [state = N;] continue; }`
/// and rewrite to `case T v when <guard-with-v>: { body }` — the guard's
/// references to the binding local become casts of the selector (the
/// pattern variable is not in scope under its ignoredN label).
pub(crate) fn fold_restart_guards(s: &mut Stmt) {
    fn replace_local(e: &mut Expr, var: u32, with: &Expr) {
        match e {
            Expr::Local { var: v, .. } if *v == var => {
                *e = with.clone();
            }
            Expr::Cast { e: i, .. } => replace_local(i, var, with),
            Expr::Cond { c, t, f } => {
                replace_local(c, var, with);
                replace_local(t, var, with);
                replace_local(f, var, with);
            }
            Expr::Bin { l, r, .. } => {
                replace_local(l, var, with);
                replace_local(r, var, with);
            }
            Expr::Un { e: i, .. } => replace_local(i, var, with),
            Expr::Method { owner, args, .. } => {
                if let Some(o) = owner {
                    replace_local(o, var, with);
                }
                args.iter_mut().for_each(|a| replace_local(a, var, with));
            }
            Expr::Field { owner, .. } => {
                if let Some(o) = owner {
                    replace_local(o, var, with);
                }
            }
            Expr::ArrayIndex { array, index } => {
                replace_local(array, var, with);
                replace_local(index, var, with);
            }
            Expr::InstanceOf { e: i, .. } => replace_local(i, var, with),
            _ => {}
        }
    }
    // The else arm must be the restart: [int-state assigns...] continue;
    fn is_restart(st: &Stmt) -> bool {
        match st {
            Stmt::Continue(None) => true,
            Stmt::Block(v) => {
                !v.is_empty()
                    && matches!(v.last(), Some(Stmt::Continue(None)))
                    && v[..v.len() - 1].iter().all(|x| {
                        matches!(x, Stmt::ExprStmt(Expr::Assign { target, value, .. })
                            if matches!(&**target, Expr::Local { .. })
                                && matches!(&**value, Expr::Const(crate::expr::ConstVal::Int(_))))
                    })
            }
            _ => false,
        }
    }
    fn try_fold(c: &mut crate::stmt::CaseGroup) {
        if c.raw_labels.len() != 1 || c.guard.is_some() {
            return;
        }
        // Split: optional leading binding LocalDef, then the guard If as the
        // LAST statement of the group.
        let (bind_idx, if_idx) = match c.body.len() {
            n if n >= 1 && matches!(c.body[n - 1], Stmt::If { .. }) => {
                let b = if n >= 2 && matches!(c.body[n - 2], Stmt::LocalDef { .. }) {
                    Some(n - 2)
                } else {
                    None
                };
                (b, n - 1)
            }
            _ => return,
        };
        let (cond, then_box) = {
            let Stmt::If { cond, then_stmt, else_stmt: Some(els) } = &c.body[if_idx] else { return };
            if !is_restart(els) {
                return;
            }
            (cond.clone(), then_stmt.clone())
        };
        // The binding LocalDef (if any) must be immediately before the If
        // and initialize from a cast of the switch selector; its local is
        // what the guard references.
        let mut guard = cond;
        if let Some(bi) = bind_idx {
            if bi + 1 != if_idx {
                return;
            }
            let Stmt::LocalDef { var, init: Some(init), .. } = &c.body[bi] else { return };
            if !matches!(init, Expr::Cast { .. }) {
                return;
            }
            replace_local(&mut guard, *var, init);
        }
        c.guard = Some(guard);
        // Body becomes the guard-pass branch (minus the binding def and the
        // If wrapper).
        let then_stmts = match *then_box {
            Stmt::Block(v) => v,
            other => vec![other],
        };
        // Keep the binding LocalDef (the body references the local; the
        // when-guard uses the selector cast since the pattern variable is
        // bound under the label's ignoredN name).
        let mut nb: Vec<Stmt> = Vec::new();
        for (i, st) in c.body.iter().enumerate() {
            if i == if_idx {
                continue;
            }
            nb.push(st.clone());
        }
        nb.extend(then_stmts);
        c.body = nb;
    }
    match s {
        Stmt::Switch { cases, default, .. } => {
            for c in cases.iter_mut() {
                try_fold(c);
                for st in c.body.iter_mut() {
                    fold_restart_guards(st);
                }
            }
            if let Some(d) = default {
                fold_restart_guards(d);
            }
        }
        Stmt::Block(v) => v.iter_mut().for_each(fold_restart_guards),
        Stmt::If { then_stmt, else_stmt, .. } => {
            fold_restart_guards(then_stmt);
            if let Some(e) = else_stmt {
                fold_restart_guards(e);
            }
        }
        Stmt::While { body, .. }
        | Stmt::DoWhile { body, .. }
        | Stmt::ForEach { body, .. }
        | Stmt::Labeled { body, .. }
        | Stmt::Synchronized { body, .. } => fold_restart_guards(body),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(fold_restart_guards);
            fold_restart_guards(body);
        }
        Stmt::Try { body, catches, finally } => {
            fold_restart_guards(body);
            for c in catches.iter_mut() {
                fold_restart_guards(&mut c.body);
            }
            if let Some(f) = finally {
                fold_restart_guards(f);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            resources.iter_mut().for_each(fold_restart_guards);
            fold_restart_guards(body);
            for c in catches.iter_mut() {
                fold_restart_guards(&mut c.body);
            }
            if let Some(f) = finally {
                fold_restart_guards(f);
            }
        }
        _ => {}
    }
}

/// Witness a bare generic call from an ALREADY-WITNESSED sibling argument:
/// the sibling's method-ref unification bound the sibling callee's typevars;
/// substituting them into the sibling's generic return yields the arg's
/// instantiated type, which unifies against THIS callee's formal to bind the
/// leftover typevars the return target left open (jdk26 Gatherers
/// ofSequential: Integrator.<FixedWindow,TR,List<TR>>ofGreedy types the arg
/// Greedy<FixedWindow,TR,List<TR>>; the formal Integrator<A,T,R> then binds
/// A:=FixedWindow, T:=TR, R:=List<TR> — the source's
/// Gatherer.<TR,FixedWindow,List<TR>>ofSequential). Every callee typevar must
/// end up bound to a denotable non-wildcard type, and at least one binding
/// must come from the sibling (otherwise ordinary inference had the
/// information and pinning could only starve it).
fn arg_driven_call_witness(
    cls: &str,
    name: &str,
    desc: &jcdc_jvm::MethodDescriptor,
    args: &[Expr],
    sib_maps: &[(usize, Vec<(String, jcdc_jvm::GenericType)>)],
    pool: &ClassPool,
    caller_params: &[jcdc_jvm::TypeParam],
) -> Option<Vec<String>> {
    use jcdc_jvm::GenericType as G;
    if sib_maps.is_empty() {
        return None;
    }
    let dpc = pool.get(cls)?;
    let want_desc = format!(
        "({}){}",
        desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
        desc.ret.to_descriptor()
    );
    let mi = (0..dpc.cf.methods.len())
        .find(|&i| dpc.method_name(i) == Some(name) && dpc.method_desc(i) == Some(want_desc.as_str()))?;
    let msig = method_signature_of(&dpc, mi)?;
    if msig.params.is_empty() {
        return None;
    }
    let mut mapping: Vec<(String, G)> = Vec::new();
    let mut sibling_bound = false;
    for (ai, sib_map) in sib_maps {
        let Expr::Method { cls: scls, name: sname, desc: sdesc, type_args, .. } =
            args.get(*ai)?
        else {
            continue;
        };
        if type_args.is_empty() {
            continue;
        }
        // The sibling's generic return, instantiated with its witness.
        let sdpc = pool.get(scls.as_str())?;
        let swant = format!(
            "({}){}",
            sdesc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
            sdesc.ret.to_descriptor()
        );
        let smi = (0..sdpc.cf.methods.len()).find(|&i| {
            sdpc.method_name(i) == Some(sname.as_str())
                && sdpc.method_desc(i) == Some(swant.as_str())
        })?;
        let smsig = method_signature_of(&sdpc, smi)?;
        if smsig.params.len() != type_args.len() {
            continue;
        }
        // Bind the sibling callee's typevars from the witness mapping we
        // computed for it (names align by construction).
        let inst_ret = crate::method::subst_typevars(&smsig.ret, &smsig.params, &{
            let vals: Vec<G> = smsig
                .params
                .iter()
                .map(|p| {
                    sib_map
                        .iter()
                        .find(|(n, _)| *n == p.name)
                        .map(|(_, g)| g.clone())
                        .unwrap_or(G::TypeVar(p.name.clone()))
                })
                .collect();
            vals
        });
        let Some(formal) = msig.args.get(*ai) else { continue };
        // have = formal (callee-typevar side binds), want = the sibling's
        // instantiated type. The sibling's return may be a SUBTYPE of the
        // formal's class (Greedy<A,T,R> extends Integrator<A,T,R>): walk
        // its supertypes with the carried instantiation first.
        let mut bound = unify_types(formal, &inst_ret, &mut mapping);
        if !bound {
            if let (G::Class(have_cs), G::Class(want_cs)) = (&inst_ret, formal) {
                let have_internal = crate::method::classsig_internal(have_cs);
                let want_internal = crate::method::classsig_internal(want_cs);
                if have_internal != want_internal {
                    if let Some(hpc) = pool.get(&have_internal) {
                        let own = have_cs
                            .parts
                            .last()
                            .map(|p| p.args.clone())
                            .unwrap_or_default();
                        let mut queue = class_supers_args(&hpc, &own);
                        let mut seen: HashSet<String> = HashSet::new();
                        while let Some((sup, sup_args)) = queue.pop() {
                            if !seen.insert(sup.clone()) {
                                continue;
                            }
                            if sup == want_internal {
                                let mut sup_cs = want_cs.clone();
                                if let Some(last) = sup_cs.parts.last_mut() {
                                    last.args = sup_args;
                                }
                                mapping.clear();
                                bound = unify_types(
                                    formal,
                                    &G::Class(sup_cs),
                                    &mut mapping,
                                );
                                break;
                            }
                            if let Some(spc) = pool.get(&sup) {
                                queue.extend(class_supers_args(&spc, &sup_args));
                            }
                        }
                    }
                }
            }
        }
        if bound {
            sibling_bound = true;
        }
    }
    if !sibling_bound {
        return None;
    }
    fn trivial_bound(p: &jcdc_jvm::TypeParam) -> bool {
        if !p.interface_bounds.is_empty() {
            return false;
        }
        match &p.class_bound {
            None => true,
            Some(G::Class(cs)) => {
                cs.parts.len() == 1 && cs.parts[0].name == "Object" && cs.parts[0].args.is_empty()
            }
            Some(G::TypeVar(_)) => false,
            _ => false,
        }
    }
    let mut out = Vec::with_capacity(msig.params.len());
    for p in &msig.params {
        match mapping.iter().find(|(n, _)| n == &p.name) {
            Some((_, G::Wildcard(_))) => return None,
            Some((_, G::TypeVar(tn))) => {
                if !trivial_bound(p) {
                    let caller_bounded = caller_params
                        .iter()
                        .find(|cp| &cp.name == tn)
                        .map(|cp| !trivial_bound(cp))
                        .unwrap_or(true);
                    if !caller_bounded {
                        return None;
                    }
                }
                out.push(G::TypeVar(tn.clone()).to_java());
            }
            Some((_, t)) => {
                if !trivial_bound(p) {
                    // Class-typed explicit args must satisfy the declared
                    // bound; only check the cheap same-class case.
                    if let (G::Class(tc), Some(G::Class(bc))) = (t, p.class_bound.as_ref().or_else(|| p.interface_bounds.first())) {
                        let ti = crate::method::classsig_internal(tc);
                        let bi = crate::method::classsig_internal(bc);
                        if ti != bi
                            && !is_subtype_of(pool, &jcdc_jvm::JavaType::Object(ti), &bi)
                        {
                            return None;
                        }
                    }
                }
                out.push(t.to_java());
            }
            None => return None,
        }
    }
    if out.is_empty() {
        return None;
    }
    Some(out)
}

pub(crate) fn cast_wildcard_call_args(
    s: &mut Stmt,
    pool: &ClassPool,
    pc: &PoolClass,
    vt: &crate::varalloc::VarTable,
    caller_params: &[jcdc_jvm::TypeParam],
) {
    // Reference comparison between two different parameterizations of
    // the same generic class is "不可比较的类型" (jdk11 Arrays.copyOf:
    // Class<CAP#1 from ? extends T[]> against the class literal
    // Class<Object[]>) — the source carried `(Object)` erasure casts on
    // both operands, which leave no bytecode trace.
    fn incomparable_class_cmp(e: &mut Expr, pool: &ClassPool) {
        let (l, r) = match e {
            Expr::Bin { op, l, r, .. }
                if matches!(
                    op,
                    crate::expr::BinOp::Eq
                        | crate::expr::BinOp::Ne
                        | crate::expr::BinOp::RefEq
                        | crate::expr::BinOp::RefNe
                ) => (l, r),
            _ => return,
        };
        fn class_args(e: &Expr) -> Option<(String, Vec<jcdc_jvm::GenericType>)> {
            if let Expr::Const(crate::expr::ConstVal::ClassLit(t)) = e {
                fn jt_to_g(jt: &jcdc_jvm::JavaType) -> jcdc_jvm::GenericType {
                    match jt {
                        jcdc_jvm::JavaType::Object(n) => {
                            let (pkg, simple) = match n.rfind('/') {
                                Some(i) => (n[..i].to_string(), n[i + 1..].to_string()),
                                None => (String::new(), n.clone()),
                            };
                            jcdc_jvm::GenericType::Class(jcdc_jvm::ClassSig {
                                package: pkg,
                                parts: vec![jcdc_jvm::ClassSigPart { name: simple, args: Vec::new() }],
                            })
                        }
                        jcdc_jvm::JavaType::Array(i) => {
                            jcdc_jvm::GenericType::Array(Box::new(jt_to_g(i)))
                        }
                        jcdc_jvm::JavaType::Boolean => jcdc_jvm::GenericType::Primitive('Z'),
                        jcdc_jvm::JavaType::Byte => jcdc_jvm::GenericType::Primitive('B'),
                        jcdc_jvm::JavaType::Char => jcdc_jvm::GenericType::Primitive('C'),
                        jcdc_jvm::JavaType::Short => jcdc_jvm::GenericType::Primitive('S'),
                        jcdc_jvm::JavaType::Int => jcdc_jvm::GenericType::Primitive('I'),
                        jcdc_jvm::JavaType::Long => jcdc_jvm::GenericType::Primitive('J'),
                        jcdc_jvm::JavaType::Float => jcdc_jvm::GenericType::Primitive('F'),
                        jcdc_jvm::JavaType::Double => jcdc_jvm::GenericType::Primitive('D'),
                        jcdc_jvm::JavaType::Void => jcdc_jvm::GenericType::Primitive('V'),
                    }
                }
                // A PARAMETERIZED literal type (`Class<Object[]>`) must
                // keep its full G form: flattening G->J erased the
                // parameterization and Arrays.copyOf's comparison lost
                // its (Object) casts.
                if let TypeRef::G(g) = t {
                    return Some(("java/lang/Class".to_string(), vec![g.clone()]));
                }
                let g = match t {
                    TypeRef::J(jt) => jt_to_g(jt),
                    TypeRef::G(g) => g.clone(),
                };
                return Some(("java/lang/Class".to_string(), vec![g]));
            }
            match e.type_ref() {
                TypeRef::G(jcdc_jvm::GenericType::Class(cs))
                    if cs.parts.last().map(|p| !p.args.is_empty()).unwrap_or(false) =>
                {
                    Some((
                        crate::method::classsig_internal(&cs),
                        cs.parts.last()?.args.clone(),
                    ))
                }
                _ => None,
            }
        }
        fn internal_of(g: &jcdc_jvm::GenericType) -> Option<String> {
            match g {
                jcdc_jvm::GenericType::Class(cs) => Some(crate::method::classsig_internal(cs)),
                _ => None,
            }
        }
        // True when one instantiation is convertible to the other (then
        // javac accepts the comparison without casts).
        fn compat(a: &jcdc_jvm::GenericType, b: &jcdc_jvm::GenericType, pool: &ClassPool) -> bool {
            use jcdc_jvm::GenericType as G;
            if a == b {
                return true;
            }
            fn one(x: &G, y: &G, pool: &ClassPool) -> bool {
                use jcdc_jvm::GenericType as G;
                match y {
                    G::Wildcard(jcdc_jvm::WildcardBound::Any) => true,
                    G::Wildcard(jcdc_jvm::WildcardBound::Extends(t)) => match (x, &**t) {
                        (G::Class(cx), G::Class(ct)) => {
                            crate::classdec::is_subtype_of(
                                pool,
                                &jcdc_jvm::JavaType::Object(crate::method::classsig_internal(cx)),
                                &crate::method::classsig_internal(ct),
                            )
                        }
                        _ => x == &**t,
                    },
                    G::Wildcard(jcdc_jvm::WildcardBound::Super(t)) => match (x, &**t) {
                        (G::Class(cx), G::Class(ct)) => {
                            crate::classdec::is_subtype_of(
                                pool,
                                &jcdc_jvm::JavaType::Object(crate::method::classsig_internal(ct)),
                                &crate::method::classsig_internal(cx),
                            )
                        }
                        _ => x == &**t,
                    },
                    G::Class(cy) => match x {
                        G::Class(cx) => {
                            cx.parts.len() == cy.parts.len()
                                && crate::classdec::is_subtype_of(
                                    pool,
                                    &jcdc_jvm::JavaType::Object(crate::method::classsig_internal(cx)),
                                    &crate::method::classsig_internal(cy),
                                )
                        }
                        _ => false,
                    },
                    _ => false,
                }
            }
            one(a, b, pool) || one(b, a, pool)
        }
        let (Some((na, aa)), Some((nb, ab))) = (class_args(l), class_args(r)) else {
            return;
        };
        if na != nb || aa == ab || aa.len() != ab.len() {
            return;
        }
        if aa.iter().zip(ab.iter()).any(|(x, y)| !compat(x, y, pool)) {
            for side in [l, r] {
                let inner = std::mem::replace(&mut **side, Expr::This);
                **side = Expr::Cast {
                    ty: TypeRef::J(jcdc_jvm::JavaType::Object("java/lang/Object".into())),
                    e: Box::new(inner),
                };
            }
        }
    }
    /// super(...)/this(...) delegations whose actual is a same-class
    /// DIFFERENT parameterization than the target ctor formal: javac
    /// rejects even a precise cast between them, and the source used a
    /// RAW cast (jdk11 UnmodifiableEntrySet: `super((Set)s)` — "Need to
    /// cast to raw in order to work around a limitation in the type
    /// system"; Set<CAP#1>无法转换为Set<? extends Entry<K,V>>).
    fn cast_super_delegation_args(e: &mut Expr, pool: &ClassPool, pc: &PoolClass) {
        let (target_cls, desc_str) = match &*e {
            // Delegation form: builder marks super()/this() ctor calls
            // is_special and emits renders them as super(...)/this(...)
            // using `cls` (is_super or foreign cls → super form).
            Expr::Method { name, cls, desc, is_special, args, .. }
                if name == "<init>" && *is_special && !args.is_empty() =>
            {
                (
                    cls.clone(),
                    format!(
                        "({}){}",
                        desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
                        desc.ret.to_descriptor()
                    ),
                )
            }
            _ => return,
        };
        let inst_args: Vec<jcdc_jvm::GenericType> = if target_cls == pc.internal_name {
            pc.class_attr("Signature")
                .and_then(|b| {
                    if b.len() < 2 {
                        return None;
                    }
                    pc.utf8(u16::from_be_bytes([b[0], b[1]]))
                        .and_then(|x| parse_class_signature(x))
                })
                .map(|sig| {
                    sig.params
                        .iter()
                        .map(|p| jcdc_jvm::GenericType::TypeVar(p.name.clone()))
                        .collect()
                })
                .unwrap_or_default()
        } else {
            match supertype_instantiation(pc, &target_cls, pool) {
                Some(a) => a,
                None => Vec::new(),
            }
        };
        let dpc;
        let dref: &PoolClass = if target_cls == pc.internal_name {
            pc
        } else {
            match pool.get(&target_cls) {
                Some(p) => {
                    dpc = p;
                    &dpc
                }
                None => return,
            }
        };
        let class_params = dref
            .class_attr("Signature")
            .and_then(|b| {
                if b.len() < 2 {
                    return None;
                }
                dref.utf8(u16::from_be_bytes([b[0], b[1]]))
                    .and_then(|x| parse_class_signature(x))
            })
            .map(|x| x.params)
            .unwrap_or_default();
        if class_params.len() != inst_args.len() {
            return;
        }
        let Some(mi) = (0..dref.cf.methods.len())
            .find(|&i| dref.method_name(i) == Some("<init>") && desc_raw(dref, i) == desc_str)
        else {
            return;
        };
        let Some(msig) = method_signature_of(dref, mi) else {
            return;
        };
        let Expr::Method { args, .. } = e else { return };
        // Ctor Signature formals exclude synthetic outer/marker params.
        let off = args.len().saturating_sub(msig.args.len());
        for (a, pt) in args[off..].iter_mut().zip(msig.args.iter()) {
            if matches!(a, Expr::Cast { .. } | Expr::Const(_) | Expr::Lambda(_)) {
                continue;
            }
            let formal = crate::method::subst_typevars(pt, &class_params, &inst_args);
            // Typevar formal with an erased (plain-Object) actual: the
            // source carried the unchecked cast the bytecode elides
            // (jdk26 Gatherers impl() State's synthetic capture ctor
            // delegates `this(!arg0 ? arg1.get() : null, ..)` against the
            // private ctor's (A, AA, boolean, boolean) Signature — the raw
            // Supplier capture parameter types the conditional at Object:
            // "Object无法转换为A"). Cast to the typevar; skip values that
            // already carry a generic type.
            if let jcdc_jvm::GenericType::TypeVar(tn) = &formal {
                if matches!(a.type_ref(), TypeRef::J(jcdc_jvm::JavaType::Object(n))
                    if n == "java/lang/Object")
                {
                    let inner = std::mem::replace(a, Expr::This);
                    *a = Expr::Cast {
                        ty: TypeRef::G(jcdc_jvm::GenericType::TypeVar(tn.clone())),
                        e: Box::new(inner),
                    };
                }
                continue;
            }
            let jcdc_jvm::GenericType::Class(fc) = &formal else {
                continue;
            };
            let TypeRef::G(jcdc_jvm::GenericType::Class(ac)) = a.type_ref() else {
                continue;
            };
            if crate::method::classsig_internal(fc) != crate::method::classsig_internal(&ac)
                || fc == &ac
            {
                continue;
            }
            // Same class, different args is invariant-inconvertible for
            // javac even with wildcards on both sides (Set<? extends
            // Entry<? extends K,? extends V>> against Set<? extends
            // Entry<K,V>>: the capture's bound is not a subtype) — and
            // a precise cast between differing parameterizations is
            // rejected too, so RAW is the only source-legal form.
            let raw = TypeRef::J(TypeRef::G(formal.clone()).erased());
            let inner = std::mem::replace(a, Expr::This);
            *a = Expr::Cast { ty: raw, e: Box::new(inner) };
        }
    }
    /// An owner whose static type is wildcard-parameterized at a formal
    /// that lands in INPUT position: javac capture-converts the owner to
    /// a fresh CAP#1 and the source-typed actual becomes inconvertible
    /// (jdk11 UnmodifiableMap.getOrDefault: field m is
    /// Map<? extends K, ? extends V>, formal V substitutes to
    /// `? extends V`, actual defaultValue:V — "V无法转换为CAP#1"). The
    /// source carried a de-wildcarded owner cast that leaves NO bytecode
    /// trace when the erasures coincide (`((Map<K, V>)m)`). Restore it:
    /// ? extends X / ? super X strip to X. The cast is a legal same-
    /// erasure downcast; every formal that mentioned a stripped wildcard
    /// now accepts the source-typed actuals.
    fn owner_wildcard_cast(e: &mut Expr, pool: &ClassPool, pc: &PoolClass) {
        use jcdc_jvm::GenericType as G;
        fn subst_g(
            g: &G,
            names: &[jcdc_jvm::TypeParam],
            args: &[G],
        ) -> G {
            match g {
                G::TypeVar(n) => names
                    .iter()
                    .position(|p| &p.name == n)
                    .and_then(|i| args.get(i))
                    .cloned()
                    .unwrap_or_else(|| g.clone()),
                G::Class(cs) => G::Class(jcdc_jvm::ClassSig {
                    package: cs.package.clone(),
                    parts: cs
                        .parts
                        .iter()
                        .map(|p| jcdc_jvm::ClassSigPart {
                            name: p.name.clone(),
                            args: p.args.iter().map(|a| subst_g(a, names, args)).collect(),
                        })
                        .collect(),
                }),
                G::Array(i) => G::Array(Box::new(subst_g(i, names, args))),
                G::Wildcard(jcdc_jvm::WildcardBound::Extends(t)) => {
                    G::Wildcard(jcdc_jvm::WildcardBound::Extends(Box::new(subst_g(t, names, args))))
                }
                G::Wildcard(jcdc_jvm::WildcardBound::Super(t)) => {
                    G::Wildcard(jcdc_jvm::WildcardBound::Super(Box::new(subst_g(t, names, args))))
                }
                other => other.clone(),
            }
        }
        let (cls, name, desc_str) = match &*e {
            Expr::Method {
                cls,
                name,
                desc,
                owner: Some(_),
                is_static: false,
                is_super: false,
                type_args,
                ..
            } if type_args.is_empty() => (
                cls.clone(),
                name.clone(),
                format!(
                    "({}){}",
                    desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
                    desc.ret.to_descriptor()
                ),
            ),
            _ => return,
        };
        if name == "<init>" {
            return;
        }
        let Expr::Method { owner: Some(owner), args, .. } = e else {
            return;
        };
        if matches!(**owner, Expr::Cast { .. }) {
            return;
        }
        let TypeRef::G(G::Class(cs)) = owner.type_ref() else {
            return;
        };
        let Some(last) = cs.parts.last() else { return };
        // `? extends X` in input position breaks capture against an
        // exactly-X actual; an unbounded `?` breaks against a plain-Object
        // actual (LazyCollections FunctionHolder) and strips to Object —
        // the `broken` scan below decides which case actually applies.
        if !last.args.iter().any(|a| {
            matches!(
                a,
                G::Wildcard(jcdc_jvm::WildcardBound::Extends(_))
                    | G::Wildcard(jcdc_jvm::WildcardBound::Any)
            )
        }) {
            return;
        }
        let dpc;
        let dref: &PoolClass = if cls == pc.internal_name {
            pc
        } else {
            match pool.get(&cls) {
                Some(p) => {
                    dpc = p;
                    &dpc
                }
                None => return,
            }
        };
        let Some(mi) = (0..dref.cf.methods.len())
            .find(|&i| dref.method_name(i) == Some(name.as_str()) && desc_raw(dref, i) == desc_str)
        else {
            return;
        };
        let Some(msig) = method_signature_of(dref, mi) else {
            return;
        };
        if msig.args.len() != args.len() {
            return;
        }
        let class_params = dref
            .class_attr("Signature")
            .and_then(|b| {
                if b.len() < 2 {
                    return None;
                }
                let i2 = u16::from_be_bytes([b[0], b[1]]);
                dref.utf8(i2).and_then(|s| jcdc_jvm::parse_class_signature(s))
            })
            .map(|s| s.params)
            .unwrap_or_default();
        if class_params.len() != last.args.len() {
            return;
        }
        // Fire only on a concrete capture failure: a formal that substitutes
        // to exactly `? extends X` against an actual whose type is exactly
        // X. (`? super X` formals accept X fine — capture yields a supertype.)
        let broken = msig.args.iter().zip(args.iter()).any(|(formal, actual)| {
            // A `null` literal converts to EVERY reference type including
            // captures — it never breaks (jdk26 VectorSupport
            // libraryUnaryOp `defaultImpl.apply(v, null)` against
            // UnaryOperation<V,?> needed NO owner cast; treating null as
            // a plain-Object actual synthesized (UnaryOperation<V,Object>)
            // — 类型参数Object不在类型变量M的范围内 ×4).
            if matches!(actual, Expr::Const(crate::expr::ConstVal::Null)) {
                return false;
            }
            let subst = subst_g(formal, &class_params, &last.args);
            match (&subst, actual.type_ref()) {
                (
                    G::Wildcard(jcdc_jvm::WildcardBound::Extends(x)),
                    TypeRef::G(ag),
                ) => **x == ag,
                // An unbounded-wildcard formal against a plain-Object
                // actual: apply(CAP#1 from ?) cannot take Object (jdk26
                // LazyCollections FunctionHolder `fun.apply(input)` with
                // fun: Function<?,?> — "Object无法转换为CAP#1"; the source
                // de-wildcards the owner: ((Function<Object,T>) fun)).
                (
                    G::Wildcard(jcdc_jvm::WildcardBound::Any),
                    TypeRef::J(jcdc_jvm::JavaType::Object(n)),
                ) => n == "java/lang/Object",
                _ => false,
            }
        });
        if !broken {
            return;
        }
        let mut fixed = cs.clone();
        {
            let Some(lp) = fixed.parts.last_mut() else {
                return;
            };
            for (pi, a) in lp.args.iter_mut().enumerate() {
                match std::mem::replace(a, G::Primitive('V')) {
                    G::Wildcard(jcdc_jvm::WildcardBound::Extends(t))
                    | G::Wildcard(jcdc_jvm::WildcardBound::Super(t)) => *a = *t,
                    // Unbounded: Object is the only always-legal slot type
                    // (input position accepts any actual; the erased return
                    // flows through the source's own result cast) — unless
                    // the class parameter is BOUNDED (M extends
                    // VectorMask<?>): Object would violate the bound
                    // (类型参数Object不在类型变量M的范围内), so substitute
                    // the bound itself.
                    G::Wildcard(jcdc_jvm::WildcardBound::Any) => {
                        let bound = class_params
                            .get(pi)
                            .and_then(|p| p.class_bound.clone())
                            .filter(|b| !matches!(b, G::TypeVar(_)));
                        *a = bound.unwrap_or_else(|| {
                            G::Class(jcdc_jvm::ClassSig {
                                package: "java/lang".to_string(),
                                parts: vec![jcdc_jvm::ClassSigPart {
                                    name: "Object".to_string(),
                                    args: Vec::new(),
                                }],
                            })
                        })
                    }
                    other => *a = other,
                }
            }
        }
        let inner = std::mem::replace(&mut **owner, Expr::This);
        **owner = Expr::Cast {
            ty: TypeRef::G(G::Class(fixed)),
            e: Box::new(inner),
        };
    }
    /// A wildcard-parameterized argument at a GENERIC method's
    /// method-typevar-parameterized formal is a capture-conversion javac
    /// frequently fails (jdk11 Collections: `min(coll)` with
    /// coll:Collection<? extends T> unbounded — "推论变量 T#2 具有不兼容的
    /// 上限"; binarySearch's List<? extends T> against
    /// List<? extends Comparable<? super T#2>>). The source carried a RAW
    /// erasure cast (`(Collection) coll` / `(List<? extends Comparable
    /// <? super T>>) list`) that javac elides from the bytecode when the
    /// erasures coincide. Restore the raw form: the call becomes
    /// unchecked-applicable exactly like the source.
    fn raw_witness_capture_call_args(e: &mut Expr, pool: &ClassPool, pc: &PoolClass) {
        let (cls, name, desc) = match &*e {
            Expr::Method { cls, name, desc, type_args, .. } if type_args.is_empty() => {
                (cls.clone(), name.clone(), desc.clone())
            }
            _ => return,
        };
        if name == "<init>" {
            return;
        }
        let want_desc = format!(
            "({}){}",
            desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
            desc.ret.to_descriptor()
        );
        let dpc;
        let dref: &PoolClass = if cls == pc.internal_name {
            pc
        } else {
            match pool.get(&cls) {
                Some(p) => {
                    dpc = p;
                    &dpc
                }
                None => return,
            }
        };
        let Some(mi) = (0..dref.cf.methods.len())
            .find(|&i| dref.method_name(i) == Some(name.as_str()) && desc_raw(dref, i) == want_desc)
        else {
            return;
        };
        let Some(msig) = method_signature_of(dref, mi) else {
            return;
        };
        if msig.params.is_empty() {
            return;
        }
        let tvar_names: Vec<String> = msig.params.iter().map(|p| p.name.clone()).collect();
        let Expr::Method { args, .. } = e else { return };
        for (i, a) in args.iter_mut().enumerate() {
            if matches!(a, Expr::Cast { .. } | Expr::Const(_) | Expr::Lambda(_)) {
                continue;
            }
            if is_generic_call(a, pool) {
                continue;
            }
            let TypeRef::G(jcdc_jvm::GenericType::Class(ca)) = a.type_ref() else {
                continue;
            };
            if !ca.parts.iter().any(|p| p.args.iter().any(crate::classdec::g_has_wildcard)) {
                continue;
            }
            let Some(formal) = msig.args.get(i) else { continue };
            if !matches!(
                formal,
                jcdc_jvm::GenericType::Class(_) | jcdc_jvm::GenericType::Array(_)
            ) || !g_mentions_tvar_named(formal, &tvar_names)
            {
                continue;
            }
            // Fire only when capture conversion is plausibly doomed: a
            // mentioned callee typevar with a NON-TRIVIAL bound (min's
            // `T#2 extends Comparable<? super T#2>`) or nested inside a
            // parameterized class in the formal (binarySearch's
            // `List<? extends Comparable<? super T#2>>`). Unbounded
            // direct formals (`checkedEntry(Entry<? extends K,..>)`)
            // capture-instantiate fine — a raw cast there broke
            // CheckedEntrySet's accept chain instead.
            fn tvar_depth(g: &jcdc_jvm::GenericType, names: &[String], depth: usize) -> usize {
                use jcdc_jvm::GenericType as G;
                match g {
                    G::TypeVar(n) if names.iter().any(|t| t == n) => depth,
                    G::Array(i) => tvar_depth(i, names, depth),
                    G::Class(cs) => cs
                        .parts
                        .iter()
                        .flat_map(|p| p.args.iter())
                        .map(|a| tvar_depth(a, names, depth + 1))
                        .max()
                        .unwrap_or(0),
                    G::Wildcard(jcdc_jvm::WildcardBound::Extends(t))
                    | G::Wildcard(jcdc_jvm::WildcardBound::Super(t)) => {
                        tvar_depth(t, names, depth)
                    }
                    _ => 0,
                }
            }
            fn nontrivial_bound(p: &jcdc_jvm::TypeParam) -> bool {
                if !p.interface_bounds.is_empty() {
                    return true;
                }
                match &p.class_bound {
                    None => false,
                    Some(jcdc_jvm::GenericType::Class(cs)) => {
                        !(cs.parts.len() == 1
                            && cs.parts[0].name == "Object"
                            && cs.parts[0].args.is_empty())
                    }
                    Some(jcdc_jvm::GenericType::TypeVar(_)) => true,
                    _ => false,
                }
            }
            let mentioned: Vec<String> = tvar_names
                .iter()
                .filter(|n| {
                    g_mentions_tvar_named(formal, std::slice::from_ref(n))
                })
                .cloned()
                .collect();
            let nested = tvar_depth(formal, &tvar_names, 0) >= 2;
            let bounded = msig
                .params
                .iter()
                .any(|p| mentioned.iter().any(|m| m == &p.name) && nontrivial_bound(p));
            if !nested && !bounded {
                continue;
            }
            let raw = TypeRef::J(TypeRef::G(formal.clone()).erased());
            let inner = std::mem::replace(a, Expr::This);
            *a = Expr::Cast { ty: raw, e: Box::new(inner) };
        }
    }
    fn fix_expr(e: &mut Expr, pool: &ClassPool, pc: &PoolClass, caller_params: &[jcdc_jvm::TypeParam]) {
        incomparable_class_cmp(e, pool);
        // Before raw_witness_capture_call_args: type_field_reads drops
        // bytecode self-casts over freshly typed field reads, and a
        // later raw_witness `(Map) this.m` wrap over a field arg must
        // not be re-examined as a droppable self-cast.
        type_field_reads(e, pool, pc, false);
        raw_witness_capture_call_args(e, pool, pc);
        owner_wildcard_cast(e, pool, pc);
        cast_super_delegation_args(e, pool, pc);
        let params = instantiated_method_params(e, pool, pc);
        // An Object descriptor param that instantiates to something else is
        // the ERASURE of a generic parameter (accept(T) → (Object)V), not
        // a source-level overload — disambiguate_overload_args would cast
        // the arg to `(Object)`, a method that does not exist at source
        // level (FindOps.FindSink.OfDouble.accept).
        let erased_generic_param = match (&params, &*e) {
            (Some(ps), Expr::Method { desc, .. }) => {
                ps.iter().zip(desc.args.iter()).any(|(p, d)| {
                    matches!(d, jcdc_jvm::JavaType::Object(n) if n == "java/lang/Object")
                        && !matches!(p, jcdc_jvm::GenericType::Class(cs)
                            if crate::method::classsig_internal(cs) == "java/lang/Object")
                })
            }
            _ => false,
        };
        if !erased_generic_param {
            disambiguate_overload_args(e, pool);
        }
        // Explicit type arguments recorded in the invokedynamic's
        // instantiatedMethodType (Optional.<ConstantDesc>map(
        // Utf8Entry::stringValue) — the raw methodref leaves the chain
        // Optional<String> and the sibling orElse(BSM_NULL_CONSTANT)
        // fails to convert).
        let mut pending_ta: Option<Vec<String>> = None;
        if let Expr::Method { cls, name, desc, type_args, args, .. } = e {
            if type_args.is_empty() {
                if let Some(Expr::Lambda(lam)) = args.first() {
                    if lam.inst_sam_desc.is_some() {
                        if let Some(w) = method_ref_inst_type_args(cls, name, desc, lam, pool) {
                            if std::env::var("JCDC_DBG_WIT").is_ok() {
                                eprintln!("INSTTA {}.{} -> {:?}", cls, name, w);
                            }
                            pending_ta = Some(w);
                        }
                    }
                }
                // UNBOUND instance method ref in ANY argument position: the
                // SAM parameter shape unifies against the target method's
                // own Signature (Integrator.<FixedWindow,TR,List<TR>>
                // ofGreedy(FixedWindow::integrate) — jdk26 Gatherers; the
                // source witnesses leave no bytecode trace and javac's
                // untyped inference dies on the Downstream capture).
                // method_ref_type_args binds every callee typevar to a
                // denotable non-wildcard type or bails, so the witness is
                // exactly the one javac recorded. ref_receiver carries the
                // CLASS name for the unbound `X::y` form (the printer
                // renders it); the bound form carries captures[0] instead —
                // captures.is_empty() is the unbound check.
                if pending_ta.is_none() {
                    for a in args.iter() {
                        let Expr::Lambda(lam) = a else { continue };
                        if lam.kind != crate::expr::LambdaKind::MethodRef
                            || lam.impl_is_static
                            || !lam.captures.is_empty()
                        {
                            continue;
                        }
                        if let Some((w, _mapping)) =
                            method_ref_type_args(cls, name, desc, lam, pool)
                        {
                            if std::env::var("JCDC_DBG_WIT").is_ok() {
                                eprintln!("REFTA {}.{} -> {:?}", cls, name, w);
                            }
                            pending_ta = Some(w);
                            break;
                        }
                    }
                }
                if pending_ta.is_none() {
                    if let Some(w) = mapmulti_witness_from_body(cls, name, type_args, args, pool, pc) {
                        if std::env::var("JCDC_DBG_WIT").is_ok() {
                            eprintln!("MMWIT {}.{} -> {:?}", cls, name, w);
                        }
                        pending_ta = Some(w);
                    }
                }
            }
        }
        if let Some(w) = pending_ta {
            if let Expr::Method { type_args, .. } = e {
                *type_args = w;
            }
        }
        if params.is_none() && !matches!(e, Expr::New { .. }) {
            raw_witness_generic_method_args(e, pool, pc);
        }
        witness_ambiguous_lambda_args(e, pool, pc);
        prune_witnessed_raw_sam_casts(e, pool);
        let params = params.or_else(|| instantiated_ctor_params(e, pool));
        if std::env::var("JCDC_DBG_APC").is_ok() {
            if let Expr::Method { cls, name, .. } = &*e {
                eprintln!("APC {}.{} params={:?}", cls, name, params);
            }
        }
        if let Some(params) = params {
            match e {
                Expr::Method { args, .. } => apply_param_casts(args, &params, pool, Some(pc), caller_params),
                Expr::New { args, .. } => apply_ctor_param_casts(args, &params, pool, Some(pc), caller_params),
                _ => {}
            }
        }
        cast_object_locals_at_typed_formals(e);
        walk_expr_children(e, pool, pc, &mut |x, p2, c2| fix_expr(x, p2, c2, caller_params));
        // Arg-driven witness, POST-children: a bare generic call whose
        // sibling call args now carry method-ref witnesses gets its own
        // leftover typevars pinned from the sibling's instantiated return
        // (jdk26 Gatherers ofSequential — the source carries
        // Gatherer.<TR,FixedWindow,List<TR>>ofSequential around the
        // witnessed Integrator.<FixedWindow,TR,List<TR>>ofGreedy; without
        // it the finisher ref faces an unresolved inference variable:
        // "Downstream<CAP#1>无法转换为Downstream<? super List<TR>>").
        if let Expr::Method { cls, name, desc, type_args, args, .. } = &*e {
            if type_args.is_empty() {
                let mut sib_maps: Vec<(usize, Vec<(String, jcdc_jvm::GenericType)>)> =
                    Vec::new();
                for (ai, a) in args.iter().enumerate() {
                    let Expr::Method {
                        cls: scls,
                        name: sname,
                        desc: sdesc,
                        type_args: sta,
                        args: sargs,
                        ..
                    } = a
                    else {
                        continue;
                    };
                    if sta.is_empty() {
                        continue;
                    }
                    // Re-derive the sibling's witness mapping from its own
                    // unbound method-ref arg (deterministic; the sibling's
                    // type_args were set by the pass above).
                    for sa in sargs.iter() {
                        let Expr::Lambda(lam) = sa else { continue };
                        if lam.kind != crate::expr::LambdaKind::MethodRef
                            || lam.impl_is_static
                            || !lam.captures.is_empty()
                        {
                            continue;
                        }
                        if let Some((_, mapping)) =
                            method_ref_type_args(scls, sname, sdesc, lam, pool)
                        {
                            if !mapping.is_empty() {
                                sib_maps.push((ai, mapping));
                            }
                        }
                        break;
                    }
                }
                if !sib_maps.is_empty() {
                    if let Some(w) = arg_driven_call_witness(
                        cls, name, desc, args, &sib_maps, pool, caller_params,
                    ) {
                        if std::env::var("JCDC_DBG_WIT").is_ok() {
                            eprintln!("ARGWIT {}.{} -> {:?}", cls, name, w);
                        }
                        if let Expr::Method { type_args, .. } = e {
                            *type_args = w;
                        }
                    }
                }
            }
        }
    }
    fix_diamond_localdefs(s, vt, pool, pc);
    walk_stmt_exprs(s, pool, pc, &mut |x, p2, c2| fix_expr(x, p2, c2, caller_params));
}

/// Diamond news assigned to a generically-declared local: the New's own
/// ty is erased, so take the instantiation from the local's declared
/// type and witness the ctor args from it (jdk11 ClassValue
/// refreshVersion: `Entry<T> e2 = new Entry<>(v2, (T) value)` — the
/// erased `(T)` cast has no bytecode trace; without it the diamond sees
/// Object against T and javac gives up: "cannot infer type arguments
/// for Entry<>").
/// Structural unification of a supertype-arg PATTERN (over a class's own
/// typevars) against a CONCRETE type arg list.
fn unify_g_types(
    pattern: &jcdc_jvm::GenericType,
    concrete: &jcdc_jvm::GenericType,
    subst: &mut HashMap<String, jcdc_jvm::GenericType>,
) -> bool {
    use jcdc_jvm::GenericType as G;
    match (pattern, concrete) {
        // A wildcard TARGET position does not constrain the diamond's own
        // arg (Collector<T,?,C> against CollectorImpl<T,A,R>: binding
        // A := ? poisoned toCollection's ctor-arg casts into Supplier<?>
        // and made the whole new-expression raw — 方法引用无效 on
        // Collection::add). Leave the typevar unbound; the resolution
        // bails and the bare diamond infers A from the arguments, like
        // the source.
        (_, G::Wildcard(_)) => true,
        (G::TypeVar(n), _) => match subst.get(n) {
            Some(prev) => prev == concrete,
            None => {
                subst.insert(n.clone(), concrete.clone());
                true
            }
        },
        (G::Class(p), G::Class(c)) => {
            crate::method::classsig_internal(p) == crate::method::classsig_internal(c)
                && p.parts.len() == c.parts.len()
                && p.parts.iter().zip(c.parts.iter()).all(|(pp, cp)| {
                    pp.args.len() == cp.args.len()
                        && pp.args
                            .iter()
                            .zip(cp.args.iter())
                            .all(|(a, b)| unify_g_types(a, b, subst))
                })
        }
        (G::Array(pi), G::Array(ci)) => unify_g_types(pi, ci, subst),
        (
            G::Wildcard(jcdc_jvm::WildcardBound::Extends(pt)),
            G::Wildcard(jcdc_jvm::WildcardBound::Extends(ct)),
        )
        | (
            G::Wildcard(jcdc_jvm::WildcardBound::Super(pt)),
            G::Wildcard(jcdc_jvm::WildcardBound::Super(ct)),
        ) => unify_g_types(pt, ct, subst),
        (G::Primitive(a), G::Primitive(b)) => a == b,
        _ => false,
    }
}

/// Resolve a diamond-newed class's OWN type args from a target type that
/// is one of its supertypes (SimpleImmutableEntry<K2,V2> implements
/// Map.Entry<K2,V2> against a formal Map.Entry<K,V> → [K, V]).
fn diamond_args_from_target(
    new_cls: &str,
    target: &jcdc_jvm::ClassSig,
    pool: &ClassPool,
) -> Option<Vec<jcdc_jvm::GenericType>> {
    let target_internal = crate::method::classsig_internal(target);
    let target_args = target.parts.last()?.args.clone();
    if target_args.is_empty() {
        return None;
    }
    let cpc = pool.get(new_cls)?;
    let own_params: Vec<String> = cpc
        .class_attr("Signature")
        .and_then(|b| {
            if b.len() < 2 {
                return None;
            }
            cpc.utf8(u16::from_be_bytes([b[0], b[1]]))
                .and_then(|x| parse_class_signature(x))
        })
        .map(|sig| sig.params.iter().map(|p| p.name.clone()).collect())
        .unwrap_or_default();
    if own_params.is_empty() {
        return None;
    }
    let self_args: Vec<jcdc_jvm::GenericType> = own_params
        .iter()
        .map(|n| jcdc_jvm::GenericType::TypeVar(n.clone()))
        .collect();
    let mut queue = class_supers_args(&cpc, &self_args);
    let mut seen: HashSet<String> = HashSet::new();
    while let Some((sup, sup_args)) = queue.pop() {
        if !seen.insert(sup.clone()) {
            continue;
        }
        if sup == target_internal {
            if sup_args.len() != target_args.len() {
                return None;
            }
            let mut subst: HashMap<String, jcdc_jvm::GenericType> = HashMap::new();
            let ok = sup_args
                .iter()
                .zip(target_args.iter())
                .all(|(p, c)| unify_g_types(p, c, &mut subst));
            if !ok {
                return None;
            }
            return own_params.iter().map(|n| subst.get(n).cloned()).collect();
        }
        if let Some(spc) = pool.get(&sup) {
            queue.extend(class_supers_args(&spc, &sup_args));
        }
    }
    None
}

fn fix_diamond_localdefs(s: &mut Stmt, vt: &crate::varalloc::VarTable, pool: &ClassPool, pc: &PoolClass) {
    fn inst_from(
        ty: &TypeRef,
        value: &Expr,
        pool: &ClassPool,
    ) -> Option<(String, Vec<jcdc_jvm::GenericType>, usize, Vec<jcdc_jvm::JavaType>)> {
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
        let cs = match &inst_ty {
            TypeRef::G(jcdc_jvm::GenericType::Class(cs)) => cs,
            _ => return None,
        };
        let last = cs.parts.last().filter(|p| !p.args.is_empty())?;
        let arg_tys: Vec<jcdc_jvm::JavaType> =
            args.iter().map(|a| a.type_ref().erased()).collect();
        let ty_internal = crate::method::classsig_internal(cs);
        if ty_internal == *cls {
            return Some((cls.clone(), last.args.clone(), args.len(), arg_tys));
        }
        // Diamond against a SUPERTYPE-typed local (`Spliterator<Provider
        // <S>> s = new ProviderSpliterator<>(it)`): the local's args are
        // the INTERFACE's, not the newed class's own — feeding them
        // straight into ProviderSpliterator<T>'s ctor formals substituted
        // T := Provider<S> and cast the arg to Iterator<Provider<Provider
        // <S>>> (Iterator<Provider<S>>无法转换为..., jdk11 ServiceLoader
        // x2 per tree). Resolve the class's own args by unifying its
        // declared supertype instantiation (with own typevars symbolic)
        // against the local's concrete type.
        let resolved = diamond_args_from_target(cls, cs, pool)?;
        Some((cls.clone(), resolved, args.len(), arg_tys))
    }
    fn apply_to_value(
        value: &mut Expr,
        params: &[jcdc_jvm::GenericType],
        pool: &ClassPool,
        pc: &PoolClass,
    ) {
        match value {
            Expr::New { args, .. } => apply_ctor_param_casts(args, params, pool, Some(pc), &[]),
            Expr::Cast { e, .. } => {
                if let Expr::New { args, .. } = &mut **e {
                    apply_ctor_param_casts(args, params, pool, Some(pc), &[]);
                }
            }
            _ => {}
        }
    }
    match s {
        Stmt::LocalDef { var, init: Some(value), .. } => {
            if let Some((cls, iargs, n, atys)) = inst_from(&vt.var(*var).ty, value, pool) {
                if let Some(params) = instantiated_ctor_params_core(&cls, &iargs, n, pool, &atys) {
                    if let Stmt::LocalDef { init: Some(v), .. } = s {
                        apply_to_value(v, &params, pool, pc);
                    }
                }
            }
        }
        // Ordinary locals are assignments in the AST (declarations are
        // synthesized from the VarTable at print time).
        Stmt::ExprStmt(inner) => {
            let target = match &*inner {
                Expr::Assign { target, value, .. } => match &**target {
                    Expr::Local { var, .. } => inst_from(&vt.var(*var).ty, value, pool),
                    // Diamond new assigned to an INSTANCE field: the
                    // field's instantiated Signature type is the diamond's
                    // target (jdk17 PropertyResourceBundle: this.lookup =
                    // new HashMap<>(properties) against Map<String,Object>).
                    Expr::Field { owner, cls, name, is_static: false, .. } => {
                        crate::method::instantiated_field_type(
                            owner.as_deref(),
                            cls,
                            name,
                            pool,
                            pc,
                        )
                        .and_then(|ty| inst_from(&ty, value, pool))
                    }
                    _ => None,
                },
                _ => None,
            };
            if let Some((cls, iargs, n, atys)) = target {
                if let Some(params) = instantiated_ctor_params_core(&cls, &iargs, n, pool, &atys) {
                    if let Expr::Assign { value, .. } = &mut *inner {
                        apply_to_value(value, &params, pool, pc);
                    }
                }
            }
        }
        Stmt::Block(v) => v.iter_mut().for_each(|x| fix_diamond_localdefs(x, vt, pool, pc)),
        Stmt::If { then_stmt, else_stmt, .. } => {
            fix_diamond_localdefs(then_stmt, vt, pool, pc);
            if let Some(x) = else_stmt {
                fix_diamond_localdefs(x, vt, pool, pc);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } | Stmt::ForEach { body, .. }
        | Stmt::Labeled { body, .. } | Stmt::Synchronized { body, .. } => {
            fix_diamond_localdefs(body, vt, pool, pc)
        }
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(|i| fix_diamond_localdefs(i, vt, pool, pc));
            fix_diamond_localdefs(body, vt, pool, pc);
        }
        Stmt::Switch { cases, default, .. } => {
            for c in cases.iter_mut() {
                c.body.iter_mut().for_each(|st| fix_diamond_localdefs(st, vt, pool, pc));
            }
            if let Some(d) = default {
                fix_diamond_localdefs(d, vt, pool, pc);
            }
        }
        Stmt::Try { body, catches, finally } => {
            fix_diamond_localdefs(body, vt, pool, pc);
            for c in catches.iter_mut() {
                fix_diamond_localdefs(&mut c.body, vt, pool, pc);
            }
            if let Some(f) = finally {
                fix_diamond_localdefs(f, vt, pool, pc);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for r in resources.iter_mut() {
                fix_diamond_localdefs(r, vt, pool, pc);
            }
            fix_diamond_localdefs(body, vt, pool, pc);
            for c in catches.iter_mut() {
                fix_diamond_localdefs(&mut c.body, vt, pool, pc);
            }
            if let Some(f) = finally {
                fix_diamond_localdefs(f, vt, pool, pc);
            }
        }
        _ => {}
    }
}
fn walk_expr_children<F: FnMut(&mut Expr, &ClassPool, &PoolClass)>(
    e: &mut Expr,
    pool: &ClassPool,
    pc: &PoolClass,
    f: &mut F,
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

fn walk_stmt_exprs<F: FnMut(&mut Expr, &ClassPool, &PoolClass)>(
    s: &mut Stmt,
    pool: &ClassPool,
    pc: &PoolClass,
    f: &mut F,
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
                // An anonymous class new carries its parameterized
                // supertype in the class Signature (PollingWatchService$1
                // implements PrivilegedExceptionAction<PollingWatchKey>):
                // that pinning must block an outer return witness the
                // same way a diamond does.
                if let Some(npc) = pool.get(cls) {
                    if let Some(sig) = npc.class_attr("Signature").and_then(|b| {
                        if b.len() >= 2 {
                            npc.utf8(u16::from_be_bytes([b[0], b[1]]))
                                .and_then(|x| parse_class_signature(x))
                        } else {
                            None
                        }
                    }) {
                        let parameterized = |g: &jcdc_jvm::GenericType| {
                            matches!(g, jcdc_jvm::GenericType::Class(cs)
                                if cs.parts.iter().any(|p| !p.args.is_empty()))
                        };
                        if sig.params.is_empty()
                            && (parameterized(&sig.superclass)
                                || sig.interfaces.iter().any(parameterized))
                        {
                            return true;
                        }
                    }
                }
                args.iter().any(|a| has(a, pool))
            }
            Expr::AnonNew { base, args, .. } => {
                // The anon's own parameterized supertype pins the
                // enclosing call's typevars (doPrivileged(new
                // PrivilegedExceptionAction<PollingWatchKey>..) — an
                // explicit return witness <WatchKey> clashes with the
                // invariant formal).
                matches!(base, TypeRef::G(jcdc_jvm::GenericType::Class(cs))
                    if cs.parts.iter().any(|p| !p.args.is_empty()))
                    || args.iter().any(|a| has(a, pool))
            }
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

fn add_return_witnesses(s: &mut Stmt, msig: Option<&jcdc_jvm::MethodSignature>, pool: &ClassPool, pc: &PoolClass) {
    let Some(sig) = msig else { return };
    fn walk(s: &mut Stmt, sig: &jcdc_jvm::MethodSignature, pool: &ClassPool, pc: &PoolClass) {
        match s {
            Stmt::Block(v) => v.iter_mut().for_each(|x| walk(x, sig, pool, pc)),
            Stmt::Return(Some(e)) => fix_ret(e, sig, pool, pc),
            Stmt::If { then_stmt, else_stmt, .. } => {
                walk(then_stmt, sig, pool, pc);
                if let Some(e) = else_stmt {
                    walk(e, sig, pool, pc);
                }
            }
            Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => walk(body, sig, pool, pc),
            Stmt::For { init, body, .. } => {
                init.iter_mut().for_each(|i| walk(i, sig, pool, pc));
                walk(body, sig, pool, pc);
            }
            Stmt::ForEach { body, .. } => walk(body, sig, pool, pc),
            Stmt::Switch { cases, default, .. } => {
                for c in cases.iter_mut() {
                    c.body.iter_mut().for_each(|x| walk(x, sig, pool, pc));
                }
                if let Some(d) = default {
                    walk(d, sig, pool, pc);
                }
            }
            Stmt::Try { body, catches, finally } => {
                walk(body, sig, pool, pc);
                for c in catches.iter_mut() {
                    walk(&mut c.body, sig, pool, pc);
                }
                if let Some(f) = finally {
                    walk(f, sig, pool, pc);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                for r in resources.iter_mut() {
                    walk(r, sig, pool, pc);
                }
                walk(body, sig, pool, pc);
                for c in catches.iter_mut() {
                    walk(&mut c.body, sig, pool, pc);
                }
                if let Some(f) = finally {
                    walk(f, sig, pool, pc);
                }
            }
            Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => walk(body, sig, pool, pc),
            _ => {}
        }
    }
    fn fix_ret(e: &mut Expr, sig: &jcdc_jvm::MethodSignature, pool: &ClassPool, pc: &PoolClass) {
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
                        retype_witness_arg_casts(cls, name, desc, args, &mapping, pool, pc, &sig.params);
                    }
                }
                Expr::Method { type_args, cls, name, desc, args, .. } => {
                    *type_args = w;
                    retype_witness_arg_casts(cls, name, desc, args, &mapping, pool, pc, &sig.params);
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
    walk(s, sig, pool, pc);
}

/// Equality operands: a generic call compared against a parameterized
/// value needs its type arguments restored — `leftFinisher !=
/// Gatherer.defaultFinisher()` fails as "不可比较的类型" because the
/// bare call infers <Object,Object>. The comparison operand supplies
/// the wanted type; compute_witness unifies it with the callee's
/// generic return (jdk26 Gatherers 12-14 errors).
///
/// ALSO: Type arguments for a generic call whose functional argument is an
/// UNBOUND method reference: the SAM parameter shape unifies against the
/// target method's signature (`Integrator.<State,T,RR>of(State::integrate)`
/// — jdk26 Gatherers; the source witnesses leave no bytecode trace and
/// javac's untyped inference dies on the Downstream capture: "方法引用
/// 无效"). Conservative v1: the receiver fills the first SAM param when
/// it is a callee typevar; remaining SAM params unify against the target's
/// Signature; every callee typevar must end up bound and denotable.
/// Shared resolution prefix for method-ref witnesses: the caller method's
/// generic Signature, its typevar names, the SAM class signature in the
/// formal, and the SAM method's own signature + class params + the
/// formal's actual type arguments.
fn method_ref_common(
    cls: &str,
    name: &str,
    desc: &jcdc_jvm::MethodDescriptor,
    lam: &crate::expr::LambdaExpr,
    pool: &ClassPool,
) -> Option<(
    jcdc_jvm::MethodSignature,
    Vec<String>,
    jcdc_jvm::ClassSig,
    jcdc_jvm::MethodSignature,
    Vec<jcdc_jvm::TypeParam>,
    Vec<jcdc_jvm::GenericType>,
)> {
    use jcdc_jvm::GenericType as G;
    if lam.kind != crate::expr::LambdaKind::MethodRef || lam.impl_is_static {
        if std::env::var("JCDC_DBG_WIT").is_ok() {
            eprintln!(
                "MRTA bail1 {} {} kind={:?} static={} impl={}.{} ref_recv={:?}",
                cls, name, lam.kind, lam.impl_is_static, lam.impl_owner, lam.impl_name, lam.ref_receiver
            );
        }
        return None;
    }
    let dpc = pool.get(cls)?;
    let want_desc = format!(
        "({}){}",
        desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
        desc.ret.to_descriptor()
    );
    let mi = (0..dpc.cf.methods.len())
        .find(|&i| dpc.method_name(i) == Some(name) && dpc.method_desc(i) == Some(want_desc.as_str()))?;
    let msig = { let x = method_signature_of(&dpc, mi); if x.is_none() && std::env::var("JCDC_DBG_WIT").is_ok() { eprintln!("MRTA s2 msig {} {}", cls, name); } x? };
    if msig.params.is_empty() {
        { if std::env::var("JCDC_DBG_WIT").is_ok() { eprintln!("MRTA bail{} {} at {}", cls, name, 2); } return None; }
    }
    let tvar_names: Vec<String> = msig.params.iter().map(|p| p.name.clone()).collect();
    let mut sam_cs: Option<jcdc_jvm::ClassSig> = None;
    for pt in &msig.args {
        if let G::Class(cs) = pt {
            if g_mentions_tvar_named(pt, &tvar_names) {
                sam_cs = Some(cs.clone());
                break;
            }
        }
    }
    let sam_cs = { if sam_cs.is_none() && std::env::var("JCDC_DBG_WIT").is_ok() { eprintln!("MRTA s3 sam_cs {}", name); } sam_cs? };
    let sam_internal = crate::method::classsig_internal(&sam_cs);
    let sam_pc = { let x = pool.get(&sam_internal); if x.is_none() && std::env::var("JCDC_DBG_WIT").is_ok() { eprintln!("MRTA s4 sam_pc {}", sam_internal); } x? };
    // The SAM method may be inherited (ofGreedy's param is
    // Integrator$Greedy which does NOT redeclare integrate): walk the
    // interface's supers. Class params of the declaring type pair with
    // the instantiation args positionally (same-name passthrough is the
    // norm; anything else fails unification safely).
    fn find_sam(
        pcx: &PoolClass,
        sam_name: &str,
        pool: &ClassPool,
        depth: usize,
    ) -> Option<(jcdc_jvm::MethodSignature, Vec<jcdc_jvm::TypeParam>)> {
        let own = (0..pcx.cf.methods.len()).find(|&i| pcx.method_name(i) == Some(sam_name));
        if let Some(mi) = own {
            if let Some(msig) = method_signature_of(pcx, mi) {
                let params = pcx
                    .class_attr("Signature")
                    .and_then(|b| {
                        if b.len() >= 2 {
                            pcx.utf8(u16::from_be_bytes([b[0], b[1]]))
                                .and_then(|x| parse_class_signature(x))
                        } else {
                            None
                        }
                    })
                    .map(|cs| cs.params)
                    .unwrap_or_default();
                return Some((msig, params));
            }
        }
        if depth >= 4 {
            return None;
        }
        for &ii in &pcx.cf.interfaces {
            if let Some(iname) = pcx.class_name(ii) {
                if let Some(ipc) = pool.get(iname) {
                    if let Some(x) = find_sam(&ipc, sam_name, pool, depth + 1) {
                        return Some(x);
                    }
                }
            }
        }
        if let Some(sup) = pcx.super_name() {
            if !sup.is_empty() {
                if let Some(spc) = pool.get(sup) {
                    return find_sam(&spc, sam_name, pool, depth + 1);
                }
            }
        }
        None
    }
    let (sam_msig, sam_cls_params) = {
        let x = find_sam(&sam_pc, &lam.sam_name, pool, 0);
        if x.is_none() && std::env::var("JCDC_DBG_WIT").is_ok() {
            eprintln!("MRTA s5 sam_mi {}", lam.sam_name);
        }
        x?
    };
    let inst_args = {
        let pl = sam_cs.parts.last();
        if pl.is_none() && std::env::var("JCDC_DBG_WIT").is_ok() {
            eprintln!("MRTA s7 parts");
        }
        pl?.args.clone()
    };
    Some((msig, tvar_names, sam_cs, sam_msig, sam_cls_params, inst_args))
}

/// Witness from the invokedynamic's instantiatedMethodType — javac's own
/// record of the SAM instantiation at this site. Authoritative; unlike
/// the unification heuristic it never guesses.
fn method_ref_inst_type_args(
    cls: &str,
    name: &str,
    desc: &jcdc_jvm::MethodDescriptor,
    lam: &crate::expr::LambdaExpr,
    pool: &ClassPool,
) -> Option<Vec<String>> {
    use jcdc_jvm::GenericType as G;
    let inst = lam.inst_sam_desc.as_ref()?;
    let (msig, tvar_names, _sam_cs, sam_msig, sam_cls_params, inst_args) =
        method_ref_common(cls, name, desc, lam, pool)?;
    // The invokedynamic's instantiatedMethodType is javac's own record of
    // the SAM instantiation: `.<ConstantDesc>map(Utf8Entry::stringValue)`
    // compiles samMethodType `(LObject;)LObject;` with instantiated
    // `(LUtf8Entry;)LConstantDesc;` (jdk26 ClassPrinterImpl — without the
    // explicit witness the raw methodref types the lambda against the
    // erased Function and the orElse argument fails to convert). Pair it
    // positionally with the SAM method's generic signature to recover the
    // SAM class typevar values, then read the CALLER's typevars off the
    // formal's (wildcard-wrapped) type arguments.
    if let Some(inst) = &lam.inst_sam_desc {
        if inst.args.len() == sam_msig.args.len() && inst != &lam.sam_desc {
            fn jt_to_g(jt: &jcdc_jvm::JavaType) -> G {
                match jt {
                    jcdc_jvm::JavaType::Object(n) => {
                        let (pkg, simple) = match n.rfind('/') {
                            Some(i) => (n[..i].to_string(), n[i + 1..].to_string()),
                            None => (String::new(), n.clone()),
                        };
                        G::Class(jcdc_jvm::ClassSig {
                            package: pkg,
                            parts: vec![jcdc_jvm::ClassSigPart { name: simple, args: Vec::new() }],
                        })
                    }
                    jcdc_jvm::JavaType::Array(i) => G::Array(Box::new(jt_to_g(i))),
                    jcdc_jvm::JavaType::Boolean => G::Primitive('Z'),
                    jcdc_jvm::JavaType::Byte => G::Primitive('B'),
                    jcdc_jvm::JavaType::Char => G::Primitive('C'),
                    jcdc_jvm::JavaType::Short => G::Primitive('S'),
                    jcdc_jvm::JavaType::Int => G::Primitive('I'),
                    jcdc_jvm::JavaType::Long => G::Primitive('J'),
                    jcdc_jvm::JavaType::Float => G::Primitive('F'),
                    jcdc_jvm::JavaType::Double => G::Primitive('D'),
                    jcdc_jvm::JavaType::Void => G::Primitive('V'),
                }
            }
            // An instantiated type that is a RAW GENERIC class
            // (Stream.<Set>map from an erased instantiatedMethodType)
            // poisons the downstream chain with rawtype inference —
            // javac's real type argument was parameterized and is not
            // recoverable from the descriptor. Only allow raw forms of
            // NON-generic classes (ConstantDesc), primitives and arrays.
            let raw_generic = |jt: &jcdc_jvm::JavaType| -> bool {
                if let jcdc_jvm::JavaType::Object(n) = jt {
                    if let Some(cpc) = pool.get(n) {
                        return cpc
                            .class_attr("Signature")
                            .and_then(|b| {
                                if b.len() >= 2 {
                                    cpc.utf8(u16::from_be_bytes([b[0], b[1]]))
                                        .and_then(|x| parse_class_signature(x))
                                } else {
                                    None
                                }
                            })
                            .map(|cs| !cs.params.is_empty())
                            .unwrap_or(false);
                    }
                }
                false
            };
            if inst.args.iter().any(&raw_generic) || raw_generic(&inst.ret) {
                return None;
            }
            // SAM class typevar name -> instantiated concrete type.
            let mut sam_vals: Vec<(String, G)> = Vec::new();
            for (sa, ia) in sam_msig.args.iter().zip(inst.args.iter()) {
                if let G::TypeVar(n) = sa {
                    if !sam_vals.iter().any(|(m, _)| m == n) {
                        sam_vals.push((n.clone(), jt_to_g(ia)));
                    }
                }
            }
            if let G::TypeVar(n) = &sam_msig.ret {
                if !sam_vals.iter().any(|(m, _)| m == n) {
                    sam_vals.push((n.clone(), jt_to_g(&inst.ret)));
                }
            }
            if !sam_vals.is_empty() && sam_cls_params.len() == inst_args.len() {
                let mut mapping: Vec<(String, G)> = Vec::new();
                let mut ok = true;
                for (p, actual) in sam_cls_params.iter().zip(inst_args.iter()) {
                    let Some((_, concrete)) =
                        sam_vals.iter().find(|(n, _)| *n == p.name)
                    else {
                        ok = false;
                        break;
                    };
                    let inner = match actual {
                        G::Wildcard(jcdc_jvm::WildcardBound::Extends(t))
                        | G::Wildcard(jcdc_jvm::WildcardBound::Super(t)) => t.as_ref(),
                        other => other,
                    };
                    // Only slots mentioning a CALLER METHOD typevar bind
                    // it; receiver-side class typevars (`? super T` of
                    // Optional<T>) and concrete pins are the receiver's
                    // business — skip them (failing there blocked the
                    // Function<? super T, ? extends U> case entirely).
                    if let G::TypeVar(v) = inner {
                        if tvar_names.iter().any(|t| t == v) {
                            match mapping.iter().find(|(m, _)| m == v) {
                                Some((_, prev)) if prev != concrete => {
                                    ok = false;
                                    break;
                                }
                                Some(_) => {}
                                None => mapping.push((v.clone(), concrete.clone())),
                            }
                        }
                    }
                }
                if ok && !mapping.is_empty() {
                    let mut out = Vec::with_capacity(msig.params.len());
                    let mut done = true;
                    for p in &msig.params {
                        match mapping.iter().find(|(n, _)| n == &p.name) {
                            Some((_, t)) => out.push(t.to_java()),
                            None => {
                                done = false;
                                break;
                            }
                        }
                    }
                    if done && !out.is_empty() {
                        return Some(out);
                    }
                }
            }
        }
    }
    None
}

fn method_ref_type_args(
    cls: &str,
    name: &str,
    desc: &jcdc_jvm::MethodDescriptor,
    lam: &crate::expr::LambdaExpr,
    pool: &ClassPool,
) -> Option<(Vec<String>, Vec<(String, jcdc_jvm::GenericType)>)> {
    use jcdc_jvm::GenericType as G;
    if let Some(w) = method_ref_inst_type_args(cls, name, desc, lam, pool) {
        return Some((w, Vec::new()));
    }
    let (msig, tvar_names, sam_cs, sam_msig, sam_cls_params, inst_args) =
        method_ref_common(cls, name, desc, lam, pool)?;
    let _ = (&tvar_names, &sam_cs);
    let sam_params: Vec<G> = sam_msig
        .args
        .iter()
        .map(|a| crate::method::subst_typevars(a, &sam_cls_params, &inst_args))
        .collect();
    let rpc = { let x = pool.get(&lam.impl_owner); if x.is_none() && std::env::var("JCDC_DBG_WIT").is_ok() { eprintln!("MRTA s8 rpc {}", lam.impl_owner); } x? };
    let rmi = (0..rpc.cf.methods.len()).find(|&i| {
        rpc.method_name(i) == Some(lam.impl_name.as_str())
            && rpc
                .method_desc(i)
                .map(|d| {
                    d == format!(
                        "({}){}",
                        lam.impl_desc
                            .args
                            .iter()
                            .map(|t| t.to_descriptor())
                            .collect::<String>(),
                        lam.impl_desc.ret.to_descriptor()
                    )
                })
                .unwrap_or(false)
    })?;
    let ref_msig = { let x = method_signature_of(&rpc, rmi); if x.is_none() && std::env::var("JCDC_DBG_WIT").is_ok() { eprintln!("MRTA s10 ref_msig {}.{}", lam.impl_owner, lam.impl_name); } x? };
    if sam_params.len() != ref_msig.args.len() + 1 {
        { if std::env::var("JCDC_DBG_WIT").is_ok() { eprintln!("MRTA bail{} {} at {}", cls, name, 3); } return None; }
    }
    let mut mapping: Vec<(String, G)> = Vec::new();
    match &sam_params[0] {
        G::TypeVar(tn) => {
            let tail = lam.impl_owner.rsplit('$').next().unwrap_or(&lam.impl_owner);
            let simple = tail.trim_start_matches(|c: char| c.is_ascii_digit()).to_string();
            if simple.is_empty() {
                { if std::env::var("JCDC_DBG_WIT").is_ok() { eprintln!("MRTA bail{} {} at {}", cls, name, 4); } return None; }
            }
            mapping.push((
                tn.clone(),
                G::Class(jcdc_jvm::ClassSig {
                    package: String::new(),
                    parts: vec![jcdc_jvm::ClassSigPart { name: simple, args: Vec::new() }],
                }),
            ));
        }
        _ => { if std::env::var("JCDC_DBG_WIT").is_ok() { eprintln!("MRTA s12 recv {:?}", sam_params.first()); } return None; }
    }
    // Direction matters: `have` is the SAM (callee-typevar) side so the
    // mapping binds CALLEE typevars to the target method's types
    // (A:=State, T:=T, R:=RR), not the reverse.
    for (i, rp) in ref_msig.args.iter().enumerate() {
        if !unify_types(&sam_params[i + 1], rp, &mut mapping) {
            { if std::env::var("JCDC_DBG_WIT").is_ok() { eprintln!("MRTA bail{} {} at {}", cls, name, 5); } return None; }
        }
    }
    let mut out = Vec::with_capacity(msig.params.len());
    for p in &msig.params {
        match mapping.iter().find(|(n, _)| n == &p.name) {
            Some((_, G::Wildcard(_))) => return None,
            Some((_, t)) => out.push(t.to_java()),
            None => return None,
        }
    }
    Some((out, mapping))
}

fn method_signature_of(pc: &PoolClass, mi: usize) -> Option<jcdc_jvm::MethodSignature> {
    let sig_bytes = pc.cf.methods[mi].attributes.iter().find_map(|a| {
        if pc.utf8(a.attribute_name_index) == Some("Signature") {
            Some(a.info.as_slice())
        } else {
            None
        }
    })?;
    if sig_bytes.len() < 2 {
        return None;
    }
    pc.utf8(u16::from_be_bytes([sig_bytes[0], sig_bytes[1]]))
        .and_then(|x| parse_method_signature(x))
}

/// A hoisted method-top local can collide with lambda parameter and
/// lambda-body local names that the source declared BEFORE the local's
/// original (block-scoped) declaration — legal in source, but the hoist
/// moves the declaration above the lambdas and javac rejects the
/// shadowing ("已在方法 makeGraph 中定义了变量 m2", jdk11 module
/// Resolver). Rename the OUTER local (all references follow the
/// VarTable name) until no lambda-scope name collides.
fn disambiguate_lambda_locals(
    pc: &PoolClass,
    pool: &ClassPool,
    vt: &mut crate::varalloc::VarTable,
    body: &mut Stmt,
) {
    fn collect_lambda_names(
        e: &Expr,
        pc: &PoolClass,
        pool: &ClassPool,
        names: &mut HashSet<String>,
        seen: &mut HashSet<usize>,
    ) {
        if let Expr::Lambda(l) = e {
            for n in &l.param_names {
                names.insert(n.clone());
            }
            // The printer prefers the impl method's own LVT names for the
            // parameter list, and the impl body's locals share the lambda's
            // scope rules — collect both.
            if l.impl_owner == pc.internal_name {
                if let Some(mi) = pc.find_own_method(&l.impl_name, &l.impl_desc.to_string()) {
                    // A method ref to the ENCLOSING method itself
                    // (jdk26 FallbackLinker.assertNotEmpty:
                    // `forEach(FallbackLinker::assertNotEmpty)`) would
                    // re-decompile and re-collect forever — the impl's
                    // names are already accumulated (or in progress) on
                    // this stack, so a repeat visit adds nothing.
                    if !seen.insert(mi) {
                        return;
                    }
                    if let Ok(Some(mb)) = decompile_method(pc, pool, mi) {
                        // Params split into [captures..., SAM params...]:
                        // capture params are LEXICAL references to outer
                        // locals (renaming the outer var on their account
                        // breaks the very reference — System.LoggerFinder
                        // `rb` regression), only the trailing SAM slice
                        // introduces new lambda-scope names.
                        let pvars: Vec<&crate::varalloc::VarInfo> = mb
                            .vt
                            .vars
                            .iter()
                            .filter(|v| v.is_param && v.name != "this")
                            .collect();
                        let nsam = l.param_names.len();
                        let skip = pvars.len().saturating_sub(nsam);
                        for (i, v) in pvars.iter().enumerate() {
                            if i >= skip {
                                names.insert(v.name.clone());
                            }
                        }
                        for v in &mb.vt.vars {
                            if !v.is_param && v.name != "this" {
                                names.insert(v.name.clone());
                            }
                        }
                        // Nested lambdas inside this impl body share the
                        // same shadow rules (Resolver: the m2 lambda lives
                        // inside the flatMap lambda's body).
                        collect_stmt(&mb.body, pc, pool, names, seen);
                    }
                }
            }
        }
        match e {
            Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
                args.iter().for_each(|a| collect_lambda_names(a, pc, pool, names, seen));
            }
            Expr::Method { owner, args, .. } => {
                if let Some(o) = owner {
                    collect_lambda_names(o, pc, pool, names, seen);
                }
                args.iter().for_each(|a| collect_lambda_names(a, pc, pool, names, seen));
            }
            Expr::Field { owner: Some(o), .. } => collect_lambda_names(o, pc, pool, names, seen),
            Expr::ArrayIndex { array, index } => {
                collect_lambda_names(array, pc, pool, names, seen);
                collect_lambda_names(index, pc, pool, names, seen);
            }
            Expr::Cast { e: i, .. }
            | Expr::InstanceOf { e: i, .. }
            | Expr::Un { e: i, .. }
            | Expr::PreIncDec { e: i, .. }
            | Expr::PostIncDec { e: i, .. } => collect_lambda_names(i, pc, pool, names, seen),
            Expr::Bin { l, r, .. } => {
                collect_lambda_names(l, pc, pool, names, seen);
                collect_lambda_names(r, pc, pool, names, seen);
            }
            Expr::Cond { c, t, f } => {
                collect_lambda_names(c, pc, pool, names, seen);
                collect_lambda_names(t, pc, pool, names, seen);
                collect_lambda_names(f, pc, pool, names, seen);
            }
            Expr::Assign { target, value, .. } => {
                collect_lambda_names(target, pc, pool, names, seen);
                collect_lambda_names(value, pc, pool, names, seen);
            }
            Expr::NewArray { dims, init, .. } => {
                dims.iter().for_each(|d| collect_lambda_names(d, pc, pool, names, seen));
                if let Some(vals) = init {
                    vals.iter().for_each(|x| collect_lambda_names(x, pc, pool, names, seen));
                }
            }
            Expr::NewMultiArray { dims, .. } => {
                dims.iter().for_each(|d| collect_lambda_names(d, pc, pool, names, seen));
            }
            Expr::StringConcat(parts) => parts.iter().for_each(|pp| {
                if let crate::expr::ConcatPart::Str(i) = pp {
                    collect_lambda_names(i, pc, pool, names, seen);
                }
            }),
            Expr::Lambda(l) => l.captures.iter().for_each(|c| collect_lambda_names(c, pc, pool, names, seen)),
            Expr::Invokedynamic { args, .. } => {
                args.iter().for_each(|a| collect_lambda_names(a, pc, pool, names, seen));
            }
            _ => {}
        }
    }
    fn collect_stmt(s: &Stmt, pc: &PoolClass, pool: &ClassPool, names: &mut HashSet<String>, seen: &mut HashSet<usize>) {
        match s {
            Stmt::Block(v) => v.iter().for_each(|x| collect_stmt(x, pc, pool, names, seen)),
            Stmt::ExprStmt(e) => collect_lambda_names(e, pc, pool, names, seen),
            Stmt::LocalDef { init: Some(e), .. } => collect_lambda_names(e, pc, pool, names, seen),
            Stmt::Return(Some(e)) | Stmt::Throw(e) => collect_lambda_names(e, pc, pool, names, seen),
            Stmt::If { cond, then_stmt, else_stmt } => {
                collect_lambda_names(cond, pc, pool, names, seen);
                collect_stmt(then_stmt, pc, pool, names, seen);
                if let Some(e) = else_stmt {
                    collect_stmt(e, pc, pool, names, seen);
                }
            }
            Stmt::While { cond, body } => {
                collect_lambda_names(cond, pc, pool, names, seen);
                collect_stmt(body, pc, pool, names, seen);
            }
            Stmt::DoWhile { body, cond } => {
                collect_stmt(body, pc, pool, names, seen);
                collect_lambda_names(cond, pc, pool, names, seen);
            }
            Stmt::For { init, cond, update, body } => {
                init.iter().for_each(|i| collect_stmt(i, pc, pool, names, seen));
                if let Some(c) = cond {
                    collect_lambda_names(c, pc, pool, names, seen);
                }
                update.iter().for_each(|u| collect_lambda_names(u, pc, pool, names, seen));
                collect_stmt(body, pc, pool, names, seen);
            }
            Stmt::ForEach { iterable, body, .. } => {
                collect_lambda_names(iterable, pc, pool, names, seen);
                collect_stmt(body, pc, pool, names, seen);
            }
            Stmt::Switch { selector, cases, default, .. } => {
                collect_lambda_names(selector, pc, pool, names, seen);
                for c in cases {
                    c.body.iter().for_each(|st| collect_stmt(st, pc, pool, names, seen));
                }
                if let Some(d) = default {
                    collect_stmt(d, pc, pool, names, seen);
                }
            }
            Stmt::Try { body, catches, finally } => {
                collect_stmt(body, pc, pool, names, seen);
                for c in catches {
                    collect_stmt(&c.body, pc, pool, names, seen);
                }
                if let Some(f) = finally {
                    collect_stmt(f, pc, pool, names, seen);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                resources.iter().for_each(|r| collect_stmt(r, pc, pool, names, seen));
                collect_stmt(body, pc, pool, names, seen);
                for c in catches {
                    collect_stmt(&c.body, pc, pool, names, seen);
                }
                if let Some(f) = finally {
                    collect_stmt(f, pc, pool, names, seen);
                }
            }
            Stmt::Synchronized { lock, body } => {
                collect_lambda_names(lock, pc, pool, names, seen);
                collect_stmt(body, pc, pool, names, seen);
            }
            Stmt::Labeled { body, .. } => collect_stmt(body, pc, pool, names, seen),
            Stmt::Assert { cond, msg } => {
                collect_lambda_names(cond, pc, pool, names, seen);
                if let Some(m) = msg {
                    collect_lambda_names(m, pc, pool, names, seen);
                }
            }
            Stmt::TernaryValue { e } => collect_lambda_names(e, pc, pool, names, seen),
            Stmt::MonitorEnter(e) | Stmt::MonitorExit(e) => collect_lambda_names(e, pc, pool, names, seen),
            _ => {}
        }
    }
    let mut lambda_names: HashSet<String> = HashSet::new();
    let mut seen_impls: HashSet<usize> = HashSet::new();
    collect_stmt(body, pc, pool, &mut lambda_names, &mut seen_impls);
    if lambda_names.is_empty() {
        return;
    }
    let existing: HashSet<String> = vt.vars.iter().map(|v| v.name.clone()).collect();
    let mut renames: HashMap<u32, String> = HashMap::new();
    for v in vt.vars.iter_mut() {
        if v.is_param || !lambda_names.contains(&v.name) {
            continue;
        }
        let base = v.name.clone();
        let mut k = 1;
        loop {
            let cand = format!("{}${}", base, k);
            if !lambda_names.contains(&cand) && !existing.contains(&cand) {
                v.name = cand.clone();
                renames.insert(v.id, cand);
                break;
            }
            k += 1;
        }
    }
    // Catch declarations carry a frozen `var_name` override — without the
    // sync the decl prints the old name while references print the renamed
    // one (ModuleHashes `catch (NoSuchAlgorithmException e1) { throw new
    // IllegalArgumentException(e1$1); }` — 找不到符号 e1$1).
    if !renames.is_empty() {
        fn sync(s: &mut Stmt, renames: &HashMap<u32, String>) {
            match s {
                Stmt::Block(v) => v.iter_mut().for_each(|x| sync(x, renames)),
                Stmt::If { then_stmt, else_stmt, .. } => {
                    sync(then_stmt, renames);
                    if let Some(x) = else_stmt {
                        sync(x, renames);
                    }
                }
                Stmt::While { body, .. }
                | Stmt::DoWhile { body, .. }
                | Stmt::ForEach { body, .. }
                | Stmt::Labeled { body, .. }
                | Stmt::Synchronized { body, .. } => sync(body, renames),
                Stmt::For { init, body, .. } => {
                    init.iter_mut().for_each(|x| sync(x, renames));
                    sync(body, renames);
                }
                Stmt::Switch { cases, default, .. } => {
                    for c in cases {
                        c.body.iter_mut().for_each(|x| sync(x, renames));
                    }
                    if let Some(d) = default {
                        sync(d, renames);
                    }
                }
                Stmt::Try { body, catches, finally } => {
                    sync(body, renames);
                    for c in catches {
                        if let Some(n) = renames.get(&c.var) {
                            c.var_name = Some(n.clone());
                        }
                        sync(&mut c.body, renames);
                    }
                    if let Some(f) = finally {
                        sync(f, renames);
                    }
                }
                Stmt::TryWithResources { resources, body, catches, finally } => {
                    resources.iter_mut().for_each(|x| sync(x, renames));
                    sync(body, renames);
                    for c in catches {
                        if let Some(n) = renames.get(&c.var) {
                            c.var_name = Some(n.clone());
                        }
                        sync(&mut c.body, renames);
                    }
                    if let Some(f) = finally {
                        sync(f, renames);
                    }
                }
                _ => {}
            }
        }
        sync(body, &renames);
    }
}

/// True when a computed witness would break the call's own capture-typed
/// actuals: a bare-typevar formal whose witness binding is concrete cannot
/// accept a wildcard-parameterized actual (jdk26 MethodHandles.constant:
/// the comparison operand void.class witnesses requireNonNull to
/// <Class<Void>>, but the actual `type` is Class<CAP#1> — "Class<CAP#1>
/// 无法转换为Class<Void>"; the source keeps the call bare and javac's
/// reference-equality rules accept the capture comparison).
fn witness_breaks_capture_args(
    cls: &str,
    name: &str,
    desc: &jcdc_jvm::MethodDescriptor,
    args: &[Expr],
    mapping: &[(String, jcdc_jvm::GenericType)],
    pool: &ClassPool,
) -> bool {
    use jcdc_jvm::GenericType as G;
    let Some(dpc) = pool.get(cls) else { return false };
    let want_desc = format!(
        "({}){}",
        desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
        desc.ret.to_descriptor()
    );
    let Some(mi) = (0..dpc.cf.methods.len())
        .find(|&i| dpc.method_name(i) == Some(name) && dpc.method_desc(i) == Some(want_desc.as_str()))
    else {
        return false;
    };
    let Some(msig) = method_signature_of(&dpc, mi) else { return false };
    for (a, formal) in args.iter().zip(msig.args.iter()) {
        let G::TypeVar(tn) = formal else { continue };
        let Some((_, bound)) = mapping.iter().find(|(n, _)| n == tn) else { continue };
        if matches!(bound, G::TypeVar(_)) {
            continue;
        }
        if let TypeRef::G(G::Class(ca)) = a.type_ref() {
            if ca.parts.iter().any(|p| p.args.iter().any(g_has_wildcard)) {
                return true;
            }
        }
    }
    false
}

pub(crate) fn witness_comparison_operands(
    s: &mut Stmt,
    msig: Option<&jcdc_jvm::MethodSignature>,
    pool: &ClassPool,
) {
    use jcdc_jvm::GenericType as G;
    let caller_params: Option<&[jcdc_jvm::TypeParam]> = msig.map(|m| m.params.as_slice());
    let ret_want: Option<G> = msig.and_then(|m| match &m.ret {
        g @ (G::Class(_) | G::Array(_)) => Some(g.clone()),
        _ => None,
    });

    // Instantiate a callee's generic params for a call expression: the
    // receiver's parameterization (instance calls) or the declared owner
    // typevars mapped to the caller's SAME-NAMED typevars (static calls
    // inside a generic class — Gatherers.impl's `Integrator.of(..)` where
    // the SAM carries the caller's A/T/R).
    fn inst_params(
        cls: &str,
        mname: &str,
        mdesc: &jcdc_jvm::MethodDescriptor,
        owner: Option<&Expr>,
        pool: &ClassPool,
        caller_params: Option<&[jcdc_jvm::TypeParam]>,
    ) -> Option<Vec<G>> {
        let cpc = pool.get(cls)?;
        let want_desc = format!(
            "({}){}",
            mdesc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
            mdesc.ret.to_descriptor()
        );
        let mi = (0..cpc.cf.methods.len())
            .find(|&i| cpc.method_name(i) == Some(mname) && cpc.method_desc(i) == Some(want_desc.as_str()))?;
        let msig_c = method_signature_of(&cpc, mi)?;
        let cls_params = cpc
            .class_attr("Signature")
            .and_then(|b| {
                if b.len() >= 2 {
                    cpc.utf8(u16::from_be_bytes([b[0], b[1]]))
                        .and_then(|x| parse_class_signature(x))
                } else {
                    None
                }
            })
            .map(|cs| cs.params)
            .unwrap_or_default();
        if cls_params.is_empty() {
            return Some(msig_c.args.clone());
        }
        // Receiver actuals for instance calls.
        let recv_args: Option<Vec<G>> = match owner {
            Some(Expr::This) | None => None,
            Some(o) => match o.type_ref() {
                TypeRef::G(G::Class(cs)) => cs.parts.last().map(|p| p.args.clone()),
                _ => None,
            },
        };
        let inst: Vec<G> = match recv_args {
            Some(a) if a.len() == cls_params.len() => a,
            _ => {
                // Static call inside a generic owner: map the class typevars
                // to same-named caller typevars when they exist there.
                let cps = caller_params?;
                cls_params
                    .iter()
                    .map(|p| {
                        if cps.iter().any(|cp| cp.name == p.name) {
                            G::TypeVar(p.name.clone())
                        } else {
                            G::TypeVar(p.name.clone())
                        }
                    })
                    .collect()
            }
        };
        Some(
            msig_c
                .args
                .iter()
                .map(|a| crate::method::subst_typevars(a, &cls_params, &inst))
                .collect(),
        )
    }

    fn fix_e(
        e: &mut Expr,
        pool: &ClassPool,
        caller_params: Option<&[jcdc_jvm::TypeParam]>,
        want: Option<&G>,
    ) {
        // Comparisons: operand parameterization drives witnesses.
        if let Expr::Bin { op, l, r, .. } = e {
            use crate::expr::BinOp;
            if matches!(op, BinOp::Eq | BinOp::Ne | BinOp::RefEq | BinOp::RefNe) {
                let try_witness = |a: &mut Expr,
                                   b: &Expr,
                                   pool: &ClassPool,
                                   caller_params: Option<&[jcdc_jvm::TypeParam]>| {
                    let TypeRef::G(want) = b.type_ref() else { return };
                    let Expr::Method { cls, name, desc, type_args, args, .. } = &*a else {
                        return;
                    };
                    if !type_args.is_empty() {
                        return;
                    }
                    if let Some((w, mapping)) =
                        compute_witness(cls, name, desc, None, &want, pool, caller_params)
                    {
                        if witness_breaks_capture_args(cls, name, desc, args, &mapping, pool) {
                            return;
                        }
                        if let Expr::Method { type_args, .. } = a {
                            *type_args = w;
                        }
                    }
                };
                try_witness(l, r, pool, caller_params);
                try_witness(r, l, pool, caller_params);
                // Comparison side fed by an unbound method ref.
                let mut apply: Option<(bool, Vec<String>)> = None;
                for (idx, (a, b)) in
                    [(l.as_ref(), r.as_ref()), (r.as_ref(), l.as_ref())]
                        .into_iter()
                        .enumerate()
                {
                    if !matches!(b.type_ref(), TypeRef::G(_)) {
                        continue;
                    }
                    let Expr::Method { cls, name, desc, type_args, args, .. } = a else {
                        continue;
                    };
                    if !type_args.is_empty() {
                        continue;
                    }
                    let Some(Expr::Lambda(lam)) = args.first() else { continue };
                    if let Some((w, _)) = method_ref_type_args(cls, name, desc, lam, pool) {
                        apply = Some((idx == 0, w));
                        break;
                    }
                }
                if let Some((is_l, w)) = apply {
                    let target = if is_l { l } else { r };
                    if let Expr::Method { type_args, .. } = target.as_mut() {
                        *type_args = w;
                    }
                }
            }
        }
        // Method calls: witness from the contextual target when the call
        // carries an unbound method ref whose SAM contains wildcards (bare
        // inference dies on capture conversion: "方法引用无效
        // Downstream<CAP#1>无法转换为Downstream<? super RR>"). Only fire
        // when a target exists — pinned witnesses WITHOUT a driving target
        // starve outer inference (ofSequential finisher regression).
        if let Some(want_g) = want {
            if let Expr::Method { cls, name, desc, type_args, args, owner, .. } = &*e {
                if type_args.is_empty() {
                    if let Some(Expr::Lambda(lam)) = args.first() {
                        if lam.kind == crate::expr::LambdaKind::MethodRef {
                            if let Some(params) =
                                inst_params(cls, name, desc, owner.as_deref(), pool, caller_params)
                            {
                                if params.len() == args.len() {
                                    if let Some(p0) = params.first() {
                                        if g_has_wildcard(p0) {
                                            if let Some((w, _)) = compute_witness(
                                                cls,
                                                name,
                                                desc,
                                                None,
                                                want_g,
                                                pool,
                                                caller_params,
                                            ) {
                                                if let Expr::Method { type_args, .. } = e {
                                                    *type_args = w;
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
        fix_children_e(e, pool, caller_params, want);
    }
    fn fix_children_e(
        e: &mut Expr,
        pool: &ClassPool,
        caller_params: Option<&[jcdc_jvm::TypeParam]>,
        want: Option<&G>,
    ) {
        // Param wants for call/ctor args, computed before the mutable walk.
        let call_params: Option<Vec<G>> = match &*e {
            Expr::New { .. } => instantiated_ctor_params(e, pool),
            Expr::Method { cls, name, desc, owner, .. } => {
                inst_params(cls, name, desc, owner.as_deref(), pool, caller_params)
            }
            _ => None,
        };
        match e {
            Expr::New { args, .. } => {
                for (i, a) in args.iter_mut().enumerate() {
                    let pw = call_params.as_ref().and_then(|ps| ps.get(i).cloned());
                    fix_e(a, pool, caller_params, pw.as_ref());
                }
            }
            Expr::AnonNew { args, .. } => {
                args.iter_mut().for_each(|a| fix_e(a, pool, caller_params, want));
            }
            Expr::Method { owner, args, .. } => {
                if let Some(o) = owner {
                    fix_e(o, pool, caller_params, None);
                }
                for (i, a) in args.iter_mut().enumerate() {
                    let pw = call_params.as_ref().and_then(|ps| ps.get(i).cloned());
                    fix_e(a, pool, caller_params, pw.as_ref());
                }
            }
            Expr::Field { owner: Some(o), .. } => fix_e(o, pool, caller_params, None),
            Expr::ArrayIndex { array, index } => {
                fix_e(array, pool, caller_params, want);
                fix_e(index, pool, caller_params, None);
            }
            Expr::Cast { ty, e: i } => {
                let w = match ty {
                    TypeRef::G(g) => Some(g.clone()),
                    _ => None,
                };
                fix_e(i, pool, caller_params, w.as_ref().or(want));
            }
            Expr::InstanceOf { e: i, .. }
            | Expr::Un { e: i, .. }
            | Expr::PreIncDec { e: i, .. }
            | Expr::PostIncDec { e: i, .. } => fix_e(i, pool, caller_params, want),
            Expr::Bin { l, r, .. } => {
                fix_e(l, pool, caller_params, want);
                fix_e(r, pool, caller_params, want);
            }
            Expr::Cond { c, t, f } => {
                fix_e(c, pool, caller_params, None);
                fix_e(t, pool, caller_params, want);
                fix_e(f, pool, caller_params, want);
            }
            Expr::Assign { target, value, .. } => {
                let tw = match target.type_ref() {
                    TypeRef::G(g) => Some(g.clone()),
                    _ => None,
                };
                fix_e(target, pool, caller_params, None);
                fix_e(value, pool, caller_params, tw.as_ref().or(want));
            }
            Expr::NewArray { elem, dims, init, .. } => {
                dims.iter_mut().for_each(|d| fix_e(d, pool, caller_params, None));
                if let Some(vals) = init {
                    let _ = elem;
                    vals.iter_mut().for_each(|x| fix_e(x, pool, caller_params, want));
                }
            }
            Expr::NewMultiArray { dims, .. } => {
                dims.iter_mut().for_each(|d| fix_e(d, pool, caller_params, None));
            }
            Expr::StringConcat(parts) => parts.iter_mut().for_each(|pp| {
                if let crate::expr::ConcatPart::Str(i) = pp {
                    fix_e(i, pool, caller_params, want);
                }
            }),
            Expr::Lambda(l) => l
                .captures
                .iter_mut()
                .for_each(|c| fix_e(c, pool, caller_params, want)),
            Expr::Invokedynamic { args, .. } => {
                args.iter_mut().for_each(|a| fix_e(a, pool, caller_params, want));
            }
            _ => {}
        }
    }
    fn rec(
        s: &mut Stmt,
        pool: &ClassPool,
        caller_params: Option<&[jcdc_jvm::TypeParam]>,
        ret_want: Option<&G>,
    ) {
        match s {
            Stmt::Block(v) => v.iter_mut().for_each(|x| rec(x, pool, caller_params, ret_want)),
            Stmt::ExprStmt(e) => fix_e(e, pool, caller_params, None),
            Stmt::LocalDef { var: _, init: Some(e), .. } => {
                fix_e(e, pool, caller_params, None);
            }
            Stmt::Return(Some(e)) => {
                fix_e(e, pool, caller_params, ret_want);
            }
            Stmt::Throw(e) => fix_e(e, pool, caller_params, None),
            Stmt::If { cond, then_stmt, else_stmt } => {
                fix_e(cond, pool, caller_params, None);
                rec(then_stmt, pool, caller_params, ret_want);
                if let Some(e) = else_stmt {
                    rec(e, pool, caller_params, ret_want);
                }
            }
            Stmt::While { cond, body } => {
                fix_e(cond, pool, caller_params, None);
                rec(body, pool, caller_params, ret_want);
            }
            Stmt::DoWhile { body, cond } => {
                rec(body, pool, caller_params, ret_want);
                fix_e(cond, pool, caller_params, None);
            }
            Stmt::For { init, cond, update, body } => {
                init.iter_mut().for_each(|i| rec(i, pool, caller_params, ret_want));
                if let Some(c) = cond {
                    fix_e(c, pool, caller_params, None);
                }
                update.iter_mut().for_each(|u| fix_e(u, pool, caller_params, None));
                rec(body, pool, caller_params, ret_want);
            }
            Stmt::ForEach { iterable, body, .. } => {
                fix_e(iterable, pool, caller_params, None);
                rec(body, pool, caller_params, ret_want);
            }
            Stmt::Switch { selector, cases, default, .. } => {
                fix_e(selector, pool, caller_params, None);
                for c in cases.iter_mut() {
                    c.body.iter_mut().for_each(|st| rec(st, pool, caller_params, ret_want));
                }
                if let Some(d) = default {
                    rec(d, pool, caller_params, ret_want);
                }
            }
            Stmt::Try { body, catches, finally } => {
                rec(body, pool, caller_params, ret_want);
                for c in catches.iter_mut() {
                    rec(&mut c.body, pool, caller_params, ret_want);
                }
                if let Some(f) = finally {
                    rec(f, pool, caller_params, ret_want);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                resources.iter_mut().for_each(|r| rec(r, pool, caller_params, ret_want));
                rec(body, pool, caller_params, ret_want);
                for c in catches.iter_mut() {
                    rec(&mut c.body, pool, caller_params, ret_want);
                }
                if let Some(f) = finally {
                    rec(f, pool, caller_params, ret_want);
                }
            }
            Stmt::Synchronized { lock, body } => {
                fix_e(lock, pool, caller_params, None);
                rec(body, pool, caller_params, ret_want);
            }
            Stmt::Labeled { body, .. } => rec(body, pool, caller_params, ret_want),
            Stmt::Assert { cond, msg } => {
                fix_e(cond, pool, caller_params, None);
                if let Some(m) = msg {
                    fix_e(m, pool, caller_params, None);
                }
            }
            Stmt::TernaryValue { e } => fix_e(e, pool, caller_params, ret_want),
            Stmt::MonitorEnter(e) | Stmt::MonitorExit(e) => fix_e(e, pool, caller_params, None),
            _ => {}
        }
    }
    rec(s, pool, caller_params, ret_want.as_ref());
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
        // A covariant declared return that is a SUBTYPE of the wanted
        // class (CompletedFuture<V#1>.withResult returned where
        // CompletableFuture<V> is wanted — jdk11
        // AsynchronousSocketChannelImpl.read `return CompletedFuture
        // .withResult((V) result)`: "推论变量 V#1 具有不兼容的上限" x12
        // across trees): walk the declared return's supertype chain with
        // its own args as the carried instantiation and unify the
        // matching supertype against want.
        mapping.clear();
        let (have_cs, want_cs) = match (&msig.ret, want) {
            (jcdc_jvm::GenericType::Class(a), jcdc_jvm::GenericType::Class(b)) => (a, b),
            _ => return None,
        };
        let have_internal = crate::method::classsig_internal(have_cs);
        let want_internal = crate::method::classsig_internal(want_cs);
        if have_internal == want_internal {
            return None;
        }
        let hpc = pool.get(&have_internal)?;
        let own: Vec<jcdc_jvm::GenericType> = have_cs
            .parts
            .last()
            .map(|p| p.args.clone())
            .unwrap_or_default();
        let mut found: Option<Vec<jcdc_jvm::GenericType>> = None;
        let mut queue = class_supers_args(&hpc, &own);
        let mut seen: HashSet<String> = HashSet::new();
        while let Some((sup, sup_args)) = queue.pop() {
            if !seen.insert(sup.clone()) {
                continue;
            }
            if sup == want_internal {
                found = Some(sup_args);
                break;
            }
            if let Some(spc) = pool.get(&sup) {
                queue.extend(class_supers_args(&spc, &sup_args));
            }
        }
        let Some(sup_args) = found else { return None };
        let mut sup_cs = want_cs.clone();
        if let Some(last) = sup_cs.parts.last_mut() {
            last.args = sup_args;
        }
        if !unify_types(&jcdc_jvm::GenericType::Class(sup_cs), want, &mut mapping) {
            return None;
        }
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
            Some((_, t)) => {
                // An explicit CLASS type argument must satisfy the
                // callee's declared bound too: `Enum.<Object>valueOf(..)`
                // violates `T extends Enum<T>` (jdk11 AnnotationParser
                // parseEnumValue — the bare call infers the capture and
                // compiles unchecked).
                if !trivial_bound(p) {
                    let ok_bound = |b: &jcdc_jvm::GenericType| -> bool {
                        match b {
                            jcdc_jvm::GenericType::Class(bc) => {
                                let bi = crate::method::classsig_internal(bc);
                                match t {
                                    jcdc_jvm::GenericType::Class(tc) => {
                                        let ti = crate::method::classsig_internal(tc);
                                        ti == bi
                                            || is_subtype_of(
                                                pool,
                                                &jcdc_jvm::JavaType::Object(ti),
                                                &bi,
                                            )
                                    }
                                    jcdc_jvm::GenericType::Array(_) => bi == "java/lang/Object",
                                    _ => false,
                                }
                            }
                            // Typevar/wildcard bounds (incl. F-bounds on
                            // caller typevars) are not cheaply checkable.
                            _ => true,
                        }
                    };
                    if let Some(cb) = &p.class_bound {
                        if !ok_bound(cb) {
                            return None;
                        }
                    }
                    if p.interface_bounds.iter().any(|ib| !ok_bound(ib)) {
                        return None;
                    }
                }
                out.push(t.to_java());
            }
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
    pc: &PoolClass,
    caller_params: &[jcdc_jvm::TypeParam],
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
        // A TypeVar instantiation erases to its BOUND, not Object: the
        // source `(V) result` cast (result: Number, V extends Number) is
        // a provable no-op javac elides, and only the bound-aware
        // erasure match restores it (jdk11 AsynchronousSocketChannelImpl
        // read/write x4 per tree).
        let inst_er = match &inst {
            jcdc_jvm::GenericType::TypeVar(n) => {
                typevar_bound_erasure_in(n, caller_params, pc)
                    .unwrap_or_else(|| inst_ref.erased())
            }
            _ => inst_ref.erased(),
        };
        match a {
            Expr::Cast { ty, e: ce } => {
                if is_generic_call(ce, pool) {
                    // A raw checkcast around a generic call would make the
                    // whole outer call an unchecked erasure-invocation; the
                    // source relies on target-type inference instead — drop
                    // the cast and let inference run.
                    if ty.erased() == inst_er {
                        let inner = std::mem::replace(a, Expr::This);
                        if let Expr::Cast { e: ce2, .. } = inner {
                            *a = *ce2;
                        }
                    }
                } else if inst_er == ty.erased() && *ty != inst_ref {
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
                    && other.type_ref().erased() == inst_er
                {
                    // Invariant-incompatible reparameterization of the same
                    // class: the precise cast is inconvertible (javac
                    // rejects the cast itself), the source used the raw
                    // form — Collection<SocketPermission>.values() against
                    // a Collection<Permission> instantiation (jdk11
                    // SocketPermissionCollection.elements). The arg's
                    // SOURCE-level type comes from the owner-instantiated
                    // call return; the erased expr type cannot show the
                    // mismatch.
                    // The owner field may not be typed yet (this pass runs
                    // before cast_wildcard_call_args): type it so the
                    // source-level return resolves.
                    if let Expr::Method { owner: Some(ow), .. } = other {
                        if let Expr::Field {
                            owner: fo,
                            cls: fcls,
                            name: fname,
                            ty: fty,
                            is_static: false,
                            ..
                        } = ow.as_mut()
                        {
                            if !matches!(fty, TypeRef::G(_)) {
                                if let Some(g) = crate::method::instantiated_field_type(
                                    fo.as_deref(),
                                    fcls,
                                    fname,
                                    pool,
                                    pc,
                                ) {
                                    *fty = g;
                                }
                            }
                        }
                    }
                    let inconvertible =
                        instantiated_method_ret(other, pool, pc)
                            .map(|src| concrete_g_mismatch(&src, &inst))
                            .unwrap_or(false);
                    let cast_ty = if inconvertible {
                        TypeRef::J(inst_ref.erased())
                    } else {
                        inst_ref.clone()
                    };
                    let inner = std::mem::replace(other, Expr::This);
                    *other = Expr::Cast { ty: cast_ty, e: Box::new(inner) };
                }
            }
        }
    }
}

/// Same generic class with an invariant-incompatible argument position
/// (both sides concrete and different, no wildcard escape hatch): even a
/// precise cast between the two is a compile error, so call sites must
/// fall back to the raw form.
fn concrete_g_mismatch(
    x: &jcdc_jvm::GenericType,
    y: &jcdc_jvm::GenericType,
) -> bool {
    use jcdc_jvm::GenericType as GG;
    fn mismatch(x: &GG, y: &GG) -> bool {
        match (x, y) {
            (GG::Wildcard(_), _) | (_, GG::Wildcard(_)) => false,
            (GG::TypeVar(m), GG::TypeVar(n)) => m != n,
            (GG::TypeVar(_), _) | (_, GG::TypeVar(_)) => false,
            (GG::Class(cx), GG::Class(cy)) => {
                crate::method::classsig_internal(cx) != crate::method::classsig_internal(cy)
                    || cx.parts.len() != cy.parts.len()
                    || cx.parts.iter().zip(cy.parts.iter()).any(|(px, py)| {
                        px.args.len() != py.args.len()
                            || px
                                .args
                                .iter()
                                .zip(py.args.iter())
                                .any(|(u, v)| mismatch(u, v))
                    })
            }
            (GG::Array(ix), GG::Array(iy)) => mismatch(ix, iy),
            (GG::Primitive(px), GG::Primitive(py)) => px != py,
            _ => true,
        }
    }
    match (x, y) {
        (GG::Class(cx), GG::Class(cy))
            if crate::method::classsig_internal(cx) == crate::method::classsig_internal(cy) =>
        {
            mismatch(x, y)
        }
        _ => false,
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
        (G::Wildcard(ba), G::Wildcard(bb)) => {
            use jcdc_jvm::WildcardBound as W;
            match (ba, bb) {
                (W::Extends(x), W::Extends(y)) | (W::Super(x), W::Super(y)) => {
                    unify_types(x, y, map)
                }
                _ => false,
            }
        }
        (a, b) => a == b,
    }
}

/// Substitute typevar NAMES positionally (the SAM class's params are not
/// the newed class's TypeParam list, so subst_typevars' &TypeParam keying
/// does not fit).
fn subst_g_named(
    g: &jcdc_jvm::GenericType,
    names: &[String],
    args: &[jcdc_jvm::GenericType],
) -> jcdc_jvm::GenericType {
    use jcdc_jvm::GenericType as G;
    match g {
        G::TypeVar(n) => names
            .iter()
            .position(|p| p == n)
            .and_then(|i| args.get(i))
            .cloned()
            .unwrap_or_else(|| g.clone()),
        G::Class(cs) => G::Class(jcdc_jvm::ClassSig {
            package: cs.package.clone(),
            parts: cs
                .parts
                .iter()
                .map(|p| jcdc_jvm::ClassSigPart {
                    name: p.name.clone(),
                    args: p.args.iter().map(|a| subst_g_named(a, names, args)).collect(),
                })
                .collect(),
        }),
        G::Array(i) => G::Array(Box::new(subst_g_named(i, names, args))),
        G::Wildcard(jcdc_jvm::WildcardBound::Extends(t)) => {
            G::Wildcard(jcdc_jvm::WildcardBound::Extends(Box::new(subst_g_named(t, names, args))))
        }
        G::Wildcard(jcdc_jvm::WildcardBound::Super(t)) => {
            G::Wildcard(jcdc_jvm::WildcardBound::Super(Box::new(subst_g_named(t, names, args))))
        }
        other => other.clone(),
    }
}

/// A resolved type-argument value is DENOTABLE at the new site when every
/// typevar it mentions is in scope there: the caller's own method typevars
/// (collected from the return target), an own-param NAME COLLISION (the
/// caller's same-named typevar is what renders), and never an unbound
/// receiver-class typevar (List's E1) or a foreign name.
fn denotable_type_args(
    g: &jcdc_jvm::GenericType,
    own: &[jcdc_jvm::TypeParam],
    want_tvars: &HashSet<String>,
    recv_tvars: &HashSet<String>,
) -> bool {
    use jcdc_jvm::GenericType as G;
    fn tvs(g: &G, out: &mut Vec<String>) {
        match g {
            G::TypeVar(n) => out.push(n.clone()),
            G::Array(i) => tvs(i, out),
            G::Class(cs) => cs.parts.iter().for_each(|p| p.args.iter().for_each(|a| tvs(a, out))),
            G::Wildcard(jcdc_jvm::WildcardBound::Extends(t))
            | G::Wildcard(jcdc_jvm::WildcardBound::Super(t)) => tvs(t, out),
            _ => {}
        }
    }
    if matches!(g, G::Wildcard(_)) {
        return false;
    }
    let mut names: Vec<String> = Vec::new();
    tvs(g, &mut names);
    names.iter().all(|n| {
        !recv_tvars.contains(n)
            && (want_tvars.contains(n) || own.iter().any(|p| &p.name == n))
    })
}

fn want_typevars(g: &jcdc_jvm::GenericType) -> HashSet<String> {
    let mut out = Vec::new();
    fn tvs(g: &jcdc_jvm::GenericType, out: &mut Vec<String>) {
        use jcdc_jvm::GenericType as G;
        match g {
            G::TypeVar(n) => out.push(n.clone()),
            G::Array(i) => tvs(i, out),
            G::Class(cs) => cs.parts.iter().for_each(|p| p.args.iter().for_each(|a| tvs(a, out))),
            G::Wildcard(jcdc_jvm::WildcardBound::Extends(t))
            | G::Wildcard(jcdc_jvm::WildcardBound::Super(t)) => tvs(t, out),
            _ => {}
        }
    }
    tvs(g, &mut out);
    out.into_iter().collect()
}

/// Resolve a diamond's own type args with method-ref help: the target
/// resolves what it can (jdk11 Collectors.toUnmodifiableList's
/// Collector<T,?,List<T>> binds T2:=T, R:=List<T> but leaves A open —
/// wildcard slots never bind); each UNBOUND method-ref actual then fills
/// the gaps through its SAM formal (List::add at BiConsumer<A,T2>: the
/// receiver slot gives A := List<E1>, the ref method's param unifies
/// E1 with the already-bound T2 := T, so A := List<T> — the source's
/// (Supplier<List<T>>) pin). Every own param must end up bound to a
/// denotable non-wildcard type or the diamond stays bare.
fn diamond_args_from_refs(
    ncls: &str,
    args: &[Expr],
    wcs: &jcdc_jvm::ClassSig,
    pool: &ClassPool,
) -> Option<Vec<jcdc_jvm::GenericType>> {
    use jcdc_jvm::GenericType as G;
    let want_internal = crate::method::classsig_internal(wcs);
    let want_args = wcs.parts.last()?.args.clone();
    let npc = pool.get(ncls)?;
    let csig = npc.class_attr("Signature").and_then(|b| {
        if b.len() >= 2 {
            npc.utf8(u16::from_be_bytes([b[0], b[1]])).and_then(|x| parse_class_signature(x))
        } else {
            None
        }
    })?;
    if csig.params.is_empty() {
        return None;
    }
    let own_syms: Vec<G> = csig
        .params
        .iter()
        .map(|p| G::TypeVar(p.name.clone()))
        .collect();
    // Seed: bind own params from the target through the supertype chain.
    let mut subst: HashMap<String, G> = HashMap::new();
    if want_internal == *ncls {
        if want_args.len() != csig.params.len() {
            return None;
        }
        for (p, w) in csig.params.iter().zip(want_args.iter()) {
            let mut one: HashMap<String, G> = HashMap::new();
            if unify_g_types(&G::TypeVar(p.name.clone()), w, &mut one) {
                if let Some(g) = one.get(&p.name) {
                    if !matches!(g, G::Wildcard(_)) {
                        subst.insert(p.name.clone(), g.clone());
                    }
                }
            }
        }
    } else {
        let mut queue = class_supers_args(&npc, &own_syms);
        let mut seen: HashSet<String> = HashSet::new();
        while let Some((sup, sup_args)) = queue.pop() {
            if !seen.insert(sup.clone()) {
                continue;
            }
            if sup == want_internal {
                if sup_args.len() != want_args.len() {
                    return None;
                }
                for (sa, wa) in sup_args.iter().zip(want_args.iter()) {
                    unify_g_types(sa, wa, &mut subst);
                }
                subst.retain(|_, v| !matches!(v, G::Wildcard(_)));
                break;
            }
            if let Some(spc) = pool.get(&sup) {
                queue.extend(class_supers_args(&spc, &sup_args));
            }
        }
    }
    if csig.params.iter().all(|p| subst.contains_key(&p.name)) {
        return None; // fully target-resolved: the plain path handles it
    }
    // Method-ref actuals fill the gaps through the ctor formals.
    let mut recv_tvars: HashSet<String> = HashSet::new();
    let Some(cmi) = (0..npc.cf.methods.len()).find(|&i| {
        npc.method_name(i) == Some("<init>")
            && npc
                .method_desc(i)
                .and_then(parse_method_descriptor)
                .map(|md| md.args.len() == args.len())
                .unwrap_or(false)
            && method_signature_of(&npc, i).is_some()
    }) else {
        return None;
    };
    let Some(cmsig) = method_signature_of(&npc, cmi) else {
        return None;
    };
    for (a, formal) in args.iter().zip(cmsig.args.iter()) {
        let Expr::Lambda(lam) = a else { continue };
        if lam.kind != crate::expr::LambdaKind::MethodRef
            || lam.impl_is_static
            || !lam.captures.is_empty()
        {
            continue;
        }
        // The formal must be a parameterized SAM class.
        let inst_formal = {
            let vals: Vec<G> = csig
                .params
                .iter()
                .map(|p| {
                    subst
                        .get(&p.name)
                        .cloned()
                        .unwrap_or(G::TypeVar(p.name.clone()))
                })
                .collect();
            crate::method::subst_typevars(formal, &csig.params, &vals)
        };
        let G::Class(sam_cs) = &inst_formal else { continue };
        if sam_cs.parts.last().map(|p| p.args.is_empty()).unwrap_or(true) {
            continue;
        }
        let sam_internal = crate::method::classsig_internal(sam_cs);
        let Some(sam_pc) = pool.get(&sam_internal) else { continue };
        // The SAM method by name (walking supers like method_ref_common).
        fn find_sam_sig(
            pcx: &PoolClass,
            sam_name: &str,
            pool: &ClassPool,
            depth: usize,
        ) -> Option<jcdc_jvm::MethodSignature> {
            let own = (0..pcx.cf.methods.len()).find(|&i| pcx.method_name(i) == Some(sam_name));
            if let Some(mi) = own {
                if let Some(msig) = method_signature_of(pcx, mi) {
                    return Some(msig);
                }
            }
            if depth >= 4 {
                return None;
            }
            for &ii in &pcx.cf.interfaces {
                if let Some(iname) = pcx.class_name(ii) {
                    if let Some(ipc) = pool.get(iname) {
                        if let Some(x) = find_sam_sig(&ipc, sam_name, pool, depth + 1) {
                            return Some(x);
                        }
                    }
                }
            }
            None
        }
        let Some(sam_msig) = find_sam_sig(&sam_pc, &lam.sam_name, pool, 0) else { continue };
        // Unbound ref: the SAM's first formal param is the receiver slot;
        // the rest align with the target method's params.
        let rpc = {
            let x = pool.get(&lam.impl_owner);
            match x {
                Some(p) => p,
                None => continue,
            }
        };
        let rcsig = rpc.class_attr("Signature").and_then(|b| {
            if b.len() >= 2 {
                rpc.utf8(u16::from_be_bytes([b[0], b[1]])).and_then(|x| parse_class_signature(x))
            } else {
                None
            }
        });
        let own_ref: Vec<G> = rcsig
            .as_ref()
            .map(|cs| {
                cs.params
                    .iter()
                    .map(|p| G::TypeVar(p.name.clone()))
                    .collect()
            })
            .unwrap_or_default();
        if let Some(cs) = &rcsig {
            for p in &cs.params {
                recv_tvars.insert(p.name.clone());
            }
        }
        // Receiver class for the slot: the impl owner with its own params
        // symbolic (List<E1>).
        let recv = G::Class(jcdc_jvm::ClassSig {
            package: lam
                .impl_owner
                .rfind('/')
                .map(|i| lam.impl_owner[..i].to_string())
                .unwrap_or_default(),
            parts: vec![jcdc_jvm::ClassSigPart {
                name: lam.impl_owner.rsplit('/').next().unwrap_or(&lam.impl_owner).to_string(),
                args: own_ref.clone(),
            }],
        });
        // Map the SAM's class params positionally to the formal's actual
        // args, then bind the receiver slot.
        let sam_params_names: Vec<String> = sam_pc
            .class_attr("Signature")
            .and_then(|b| {
                if b.len() >= 2 {
                    sam_pc.utf8(u16::from_be_bytes([b[0], b[1]])).and_then(|x| parse_class_signature(x))
                } else {
                    None
                }
            })
            .map(|cs| cs.params.iter().map(|p| p.name.clone()).collect())
            .unwrap_or_default();
        let formal_args = &sam_cs.parts.last()?.args;
        if sam_params_names.len() != formal_args.len() {
            continue;
        }
        // Translate the sam method's formal params through the class
        // param -> actual mapping.
        let sam_formals: Vec<G> = sam_msig
            .args
            .iter()
            .map(|sa| subst_g_named(sa, &sam_params_names, formal_args))
            .collect();
        // Receiver slot: unify sam_formals[0] (an own-param-carrying
        // formal like A) against the receiver shape List<E1>.
        let mut mapping: Vec<(String, G)> = subst
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        if sam_formals.is_empty() {
            continue;
        }
        if !unify_types(&sam_formals[0], &recv, &mut mapping) {
            continue;
        }
        // Remaining SAM params against the ref method's Signature params.
        let rmi = (0..rpc.cf.methods.len()).find(|&i| {
            rpc.method_name(i) == Some(lam.impl_name.as_str())
                && rpc
                    .method_desc(i)
                    .map(|d| {
                        d == format!(
                            "({}){}",
                            lam.impl_desc
                                .args
                                .iter()
                                .map(|t| t.to_descriptor())
                                .collect::<String>(),
                            lam.impl_desc.ret.to_descriptor()
                        )
                    })
                    .unwrap_or(false)
        });
        let Some(rmi) = rmi else { continue };
        let Some(ref_msig) = method_signature_of(&rpc, rmi) else { continue };
        if ref_msig.args.len() + 1 != sam_formals.len() {
            continue;
        }
        let mut ok = true;
        for (i, rp) in ref_msig.args.iter().enumerate() {
            // The ref method's params carry the receiver class's own
            // typevars (List.add's E1). Direction matters: `rp` is the
            // pattern side so the RECEIVER's typevar binds (E1 := T from
            // the already-bound sam slot); the opposite order would bind
            // the caller's typevar (T := E1) and drop the resolution.
            let f_i = &sam_formals[i + 1];
            if let G::TypeVar(rn) = rp {
                match mapping.iter().find(|(n, _)| n == rn) {
                    Some((_, prev)) => {
                        if prev != f_i {
                            // Consistent only if the prior value unifies
                            // with this slot.
                            let mut probe = mapping.clone();
                            if !unify_types(prev, f_i, &mut probe) {
                                ok = false;
                                break;
                            }
                            mapping = probe;
                        }
                    }
                    None => {
                        mapping.push((rn.clone(), f_i.clone()));
                    }
                }
            } else if !unify_types(f_i, rp, &mut mapping) {
                ok = false;
                break;
            }
        }
        if !ok {
            continue;
        }
        // Fixpoint: receiver typevars bound later (E1 := T) must be
        // substituted through earlier values (A := List<E1> -> List<T>).
        for _ in 0..4 {
            let keys: Vec<String> = mapping.iter().map(|(k, _)| k.clone()).collect();
            let vals: Vec<G> = mapping.iter().map(|(_, v)| v.clone()).collect();
            let mut changed = false;
            for (_, v) in mapping.iter_mut() {
                let nv = subst_g_named(v, &keys, &vals);
                if &nv != v {
                    *v = nv;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        subst = mapping
            .into_iter()
            .filter(|(k, _)| csig.params.iter().any(|p| &p.name == k))
            .collect();
    }
    let want_tvs = want_typevars(&G::Class(wcs.clone()));
    let out: Option<Vec<G>> = csig
        .params
        .iter()
        .map(|p| {
            subst.get(&p.name).and_then(|g| {
                if denotable_type_args(g, &csig.params, &want_tvs, &recv_tvars) {
                    Some(g.clone())
                } else {
                    None
                }
            })
        })
        .collect();
    out
}

/// True when a bare generic call's diamond arguments stay consistent with
/// the TARGET-inferred instantiation of the call's own typevars: binding the
/// method typevars from `want` (the return), substituting into the formals,
/// and unifying each diamond's declared supertype instantiation against the
/// formal must bind every diamond class param — with no conflicting binding.
/// Then the bare return-position call infers from the target (the source
/// shape) and a synthesized precise cast would only freeze the arg-driven
/// inference into an invariance failure (jdk11/17/26 ImmutableCollections
/// Map1.entrySet: `(Set<Map.Entry<K,V>>) Set.of(new KeyValueHolder<>(k0,v0))`
/// — Set<KeyValueHolder<K,V>> is not Set<Entry<K,V>>; bare `Set.of(new
/// KeyValueHolder<>(k0, v0))` target-types E := Entry<K,V> and the diamond
/// follows). jdk17 Stream.toList fails this check (ArrayList<Object> is
/// never <: List<? extends T>) and keeps its required cast.
fn target_inferable_diamonds(
    cls: &str,
    name: &str,
    desc: &jcdc_jvm::MethodDescriptor,
    args: &[Expr],
    want: &TypeRef,
    pool: &ClassPool,
) -> bool {
    use jcdc_jvm::GenericType as G;
    let TypeRef::G(wg) = want else { return false };
    let Some(dpc) = pool.get(cls) else { return false };
    let want_desc = format!(
        "({}){}",
        desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
        desc.ret.to_descriptor()
    );
    let Some(mi) = (0..dpc.cf.methods.len())
        .find(|&i| dpc.method_name(i) == Some(name) && dpc.method_desc(i) == Some(want_desc.as_str()))
    else {
        return false;
    };
    let Some(msig) = method_signature_of(&dpc, mi) else { return false };
    if msig.params.is_empty() {
        return false;
    }
    let mut map: Vec<(String, G)> = Vec::new();
    if !unify_types(&msig.ret, wg, &mut map) {
        return false;
    }
    if msig
        .params
        .iter()
        .any(|p| !map.iter().any(|(n, _)| *n == p.name))
    {
        return false;
    }
    let vals: Vec<G> = msig
        .params
        .iter()
        .map(|p| {
            map.iter()
                .find(|(n, _)| *n == p.name)
                .map(|(_, g)| g.clone())
                .unwrap_or(G::TypeVar(p.name.clone()))
        })
        .collect();
    let mut saw_diamond = false;
    for (a, formal) in args.iter().zip(msig.args.iter()) {
        let Expr::New { cls: ncls, args: nargs, .. } = a else { continue };
        // Diamond new: the erased form prints `new X<>(..)`; require the
        // class to be generic (a diamond on a non-generic class is a plain
        // new and imposes nothing).
        if !is_generic_class(ncls, pool) {
            continue;
        }
        saw_diamond = true;
        let inst_formal = crate::method::subst_typevars(formal, &msig.params, &vals);
        let own = if let G::Class(fcs) = &inst_formal {
            if crate::method::classsig_internal(fcs) == *ncls {
                fcs.parts.last().map(|p| p.args.clone()).unwrap_or_default()
            } else {
                match diamond_args_from_target(ncls, fcs, pool) {
                    Some(o) => o,
                    None => return false,
                }
            }
        } else {
            return false;
        };
        if own.is_empty() {
            return false;
        }
        // The formal's target-side shape may still carry wildcards after
        // substitution (toList's List<? extends T>): the diamond resolves
        // its own params from the ctor args in that slot; only a fully
        // concrete target proves the consistency.
        if own.iter().any(crate::classdec::g_has_wildcard) {
            return false;
        }
        // Standalone (ctor-arg-driven) inference of the diamond's own params.
        let Some(npc) = pool.get(ncls) else { return false };
        let Some(csig) = npc.class_attr("Signature").and_then(|b| {
            if b.len() >= 2 {
                npc.utf8(u16::from_be_bytes([b[0], b[1]])).and_then(|x| parse_class_signature(x))
            } else {
                None
            }
        }) else {
            return false;
        };
        let Some(cmi) = (0..npc.cf.methods.len()).find(|&i| {
            npc.method_name(i) == Some("<init>")
                && npc
                    .method_desc(i)
                    .map(|d| {
                        d == format!(
                            "({})V",
                            nargs
                                .iter()
                                .map(|x| x.type_ref().erased().to_descriptor())
                                .collect::<String>()
                        )
                    })
                    .unwrap_or(false)
        }) else {
            return false;
        };
        let Some(cmsig) = method_signature_of(&npc, cmi) else { return false };
        fn tyref_to_g(t: &TypeRef) -> jcdc_jvm::GenericType {
            match t {
                TypeRef::G(g) => g.clone(),
                TypeRef::J(jt) => match jt {
                    jcdc_jvm::JavaType::Object(n) => {
                        let (pkg, simple) = match n.rfind('/') {
                            Some(i) => (n[..i].to_string(), n[i + 1..].to_string()),
                            None => (String::new(), n.clone()),
                        };
                        jcdc_jvm::GenericType::Class(jcdc_jvm::ClassSig {
                            package: pkg,
                            parts: vec![jcdc_jvm::ClassSigPart { name: simple, args: Vec::new() }],
                        })
                    }
                    jcdc_jvm::JavaType::Array(i) => {
                        jcdc_jvm::GenericType::Array(Box::new(tyref_to_g(&TypeRef::J((**i).clone()))))
                    }
                    jcdc_jvm::JavaType::Boolean => jcdc_jvm::GenericType::Primitive('Z'),
                    jcdc_jvm::JavaType::Byte => jcdc_jvm::GenericType::Primitive('B'),
                    jcdc_jvm::JavaType::Char => jcdc_jvm::GenericType::Primitive('C'),
                    jcdc_jvm::JavaType::Short => jcdc_jvm::GenericType::Primitive('S'),
                    jcdc_jvm::JavaType::Int => jcdc_jvm::GenericType::Primitive('I'),
                    jcdc_jvm::JavaType::Long => jcdc_jvm::GenericType::Primitive('J'),
                    jcdc_jvm::JavaType::Float => jcdc_jvm::GenericType::Primitive('F'),
                    jcdc_jvm::JavaType::Double => jcdc_jvm::GenericType::Primitive('D'),
                    jcdc_jvm::JavaType::Void => jcdc_jvm::GenericType::Primitive('V'),
                },
            }
        }
        let mut subst: HashMap<String, jcdc_jvm::GenericType> = HashMap::new();
        for (ca, cf) in nargs.iter().zip(cmsig.args.iter()) {
            if !unify_g_types(cf, &tyref_to_g(&ca.type_ref()), &mut subst) {
                return false;
            }
        }
        if csig
            .params
            .iter()
            .any(|p| !subst.contains_key(&p.name))
        {
            return false;
        }
        // The standalone instantiation must convert to the target
        // instantiation: walk the diamond class's supertypes to the formal's
        // class and compare args structurally.
        let standalone: Vec<G> = csig
            .params
            .iter()
            .map(|p| subst.get(&p.name).cloned().unwrap_or(G::TypeVar(p.name.clone())))
            .collect();
        let f_internal = if let G::Class(fcs) = &inst_formal {
            crate::method::classsig_internal(fcs)
        } else {
            return false;
        };
        if f_internal == *ncls {
            if standalone != own {
                return false;
            }
            continue;
        }
        let mut queue = class_supers_args(&npc, &standalone);
        let mut seen: HashSet<String> = HashSet::new();
        let mut found: Option<Vec<G>> = None;
        while let Some((sup, sup_args)) = queue.pop() {
            if !seen.insert(sup.clone()) {
                continue;
            }
            if sup == f_internal {
                found = Some(sup_args);
                break;
            }
            if let Some(spc) = pool.get(&sup) {
                queue.extend(class_supers_args(&spc, &sup_args));
            }
        }
        let Some(sup_args) = found else { return false };
        if sup_args != own {
            return false;
        }
    }
    saw_diamond
}

fn g_has_typevar_in(g: &jcdc_jvm::GenericType, params: &[jcdc_jvm::TypeParam]) -> bool {
    use jcdc_jvm::GenericType as G;
    match g {
        G::TypeVar(n) => params.iter().any(|p| &p.name == n),
        G::Array(i) => g_has_typevar_in(i, params),
        G::Class(cs) => cs
            .parts
            .iter()
            .any(|p| p.args.iter().any(|a| g_has_typevar_in(a, params))),
        G::Wildcard(jcdc_jvm::WildcardBound::Extends(t))
        | G::Wildcard(jcdc_jvm::WildcardBound::Super(t)) => g_has_typevar_in(t, params),
        _ => false,
    }
}

/// Explicit type arguments for a diamond `new` whose own args the return
/// target cannot fully resolve: the wildcard slot of the target
/// (Gatherer<T,?,RR>) leaves the middle parameter open, and javac's
/// diamond inference then drowns the constructor's functional arguments
/// in captures (jdk26 Gatherers Composite.impl: `new GathererImpl<>(..)`
/// — the finisher/combiner method refs face CAP#1 from `? super R#2`,
/// "方法引用无效"; the source pins `new GathererImpl<T, State, RR>(..)`).
/// Resolution: unify the newed class's declared supertype instantiation
/// (own params symbolic) against the target to bind what the target
/// gives, then bind the rest from the witnessed generic-call arguments
/// (a Cond counts when both branches agree). All params must end up
/// bound to denotable non-wildcard types or the diamond stays.
/// The Signature formals of the class's arity-matching constructor (the
/// printer's diamond gates need the formal shapes; synthetic capture
/// ctors carry no Signature and are skipped).
pub(crate) fn ctor_formals_by_arity(
    cls: &str,
    nargs: usize,
    pool: &ClassPool,
) -> Option<Vec<jcdc_jvm::GenericType>> {
    let cpc = pool.get(cls)?;
    let cmi = (0..cpc.cf.methods.len()).find(|&i| {
        cpc.method_name(i) == Some("<init>")
            && cpc
                .method_desc(i)
                .and_then(parse_method_descriptor)
                .map(|md| md.args.len() == nargs)
                .unwrap_or(false)
            && method_signature_of(&cpc, i).is_some()
    })?;
    let cmsig = method_signature_of(&cpc, cmi)?;
    if cmsig.args.len() != nargs {
        return None;
    }
    Some(cmsig.args)
}

fn diamond_explicit_args_from_call_args(
    e: &Expr,
    want: &jcdc_jvm::GenericType,
    pool: &ClassPool,
) -> Option<Vec<jcdc_jvm::GenericType>> {
    use jcdc_jvm::GenericType as G;
    let Expr::New { cls, args, .. } = e else { return None };
    let G::Class(wcs) = want else { return None };
    let npc = pool.get(cls)?;
    let Some(csig) = npc.class_attr("Signature").and_then(|b| {
        if b.len() >= 2 {
            npc.utf8(u16::from_be_bytes([b[0], b[1]])).and_then(|x| parse_class_signature(x))
        } else {
            None
        }
    }) else {
        return None;
    };
    if csig.params.is_empty() {
        return None;
    }
    let own_syms: Vec<G> = csig
        .params
        .iter()
        .map(|p| G::TypeVar(p.name.clone()))
        .collect();
    // Bind own params from the target through the supertype chain.
    let want_internal = crate::method::classsig_internal(wcs);
    let mut subst: HashMap<String, G> = HashMap::new();
    if want_internal == *cls {
        let want_args = &wcs.parts.last()?.args;
        if want_args.len() != csig.params.len() {
            return None;
        }
        for (p, w) in csig.params.iter().zip(want_args.iter()) {
            let mut one: HashMap<String, G> = HashMap::new();
            if unify_g_types(&G::TypeVar(p.name.clone()), w, &mut one) {
                if let Some(g) = one.get(&p.name) {
                    if !matches!(g, G::Wildcard(_)) {
                        subst.insert(p.name.clone(), g.clone());
                    }
                }
            }
        }
    } else {
        let mut queue = class_supers_args(&npc, &own_syms);
        let mut seen: HashSet<String> = HashSet::new();
        while let Some((sup, sup_args)) = queue.pop() {
            if !seen.insert(sup.clone()) {
                continue;
            }
            if sup == want_internal {
                let want_args = &wcs.parts.last()?.args;
                if sup_args.len() != want_args.len() {
                    return None;
                }
                for (sa, wa) in sup_args.iter().zip(want_args.iter()) {
                    unify_g_types(sa, wa, &mut subst);
                }
                subst.retain(|_, v| !matches!(v, G::Wildcard(_)));
                break;
            }
            if let Some(spc) = pool.get(&sup) {
                queue.extend(class_supers_args(&spc, &sup_args));
            }
        }
    }
    if csig.params.iter().all(|p| subst.contains_key(&p.name)) {
        // Fully target-resolved: keep the diamond (target typing works).
        return None;
    }
    // Bind the rest from the ctor's Signature formals against witnessed
    // generic-call actuals.
    fn witnessed_ret(a: &Expr, pool: &ClassPool) -> Option<G> {
        match a {
            Expr::Cond { t, f, .. } => {
                let x = witnessed_ret(t, pool)?;
                let y = witnessed_ret(f, pool)?;
                if x == y {
                    return Some(x);
                }
                // Branches may sit at different levels of the same hierarchy
                // (ofGreedy returns Greedy<State,..>, of returns
                // Integrator<State,..>): widen the subtype side through its
                // supertypes and retry equality.
                fn internal(g: &G) -> Option<String> {
                    match g {
                        G::Class(cs) => Some(crate::method::classsig_internal(cs)),
                        _ => None,
                    }
                }
                fn widen(x: &G, target_internal: &str, pool: &ClassPool) -> Option<G> {
                    let G::Class(cs) = x else { return None };
                    let xpc = pool.get(&crate::method::classsig_internal(cs))?;
                    let own = cs.parts.last()?.args.clone();
                    let mut queue = class_supers_args(&xpc, &own);
                    let mut seen: HashSet<String> = HashSet::new();
                    while let Some((sup, sup_args)) = queue.pop() {
                        if !seen.insert(sup.clone()) {
                            continue;
                        }
                        if sup == target_internal {
                            let mut out = cs.clone();
                            out.package = sup.rfind('/').map(|i| sup[..i].to_string()).unwrap_or_default();
                            out.parts = vec![jcdc_jvm::ClassSigPart {
                                name: sup.rsplit('/').next().unwrap_or(&sup).to_string(),
                                args: sup_args,
                            }];
                            return Some(G::Class(out));
                        }
                        if let Some(spc) = pool.get(&sup) {
                            queue.extend(class_supers_args(&spc, &sup_args));
                        }
                    }
                    None
                }
                let (yi, xi) = (internal(&y), internal(&x));
                if let (Some(yi), Some(xi)) = (yi, xi) {
                    if xi != yi {
                        if let Some(wx) = widen(&x, &yi, pool) {
                            if wx == y {
                                return Some(y);
                            }
                        }
                        if let Some(wy) = widen(&y, &xi, pool) {
                            if wy == x {
                                return Some(x);
                            }
                        }
                    }
                }
                None
            }
            Expr::Cast { e: i, .. } => witnessed_ret(i, pool),
            Expr::Method { cls, name, desc, type_args, args, .. } if !type_args.is_empty() => {
                let dpc = pool.get(cls.as_str())?;
                let want_desc = format!(
                    "({}){}",
                    desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
                    desc.ret.to_descriptor()
                );
                let mi = (0..dpc.cf.methods.len()).find(|&i| {
                    dpc.method_name(i) == Some(name.as_str())
                        && dpc.method_desc(i) == Some(want_desc.as_str())
                })?;
                let msig = method_signature_of(&dpc, mi)?;
                if msig.params.len() != type_args.len() {
                    return None;
                }
                // Re-derive the binding types from the arg's unbound
                // method ref (same machinery that produced the witness).
                for sa in args.iter() {
                    let Expr::Lambda(lam) = sa else { continue };
                    if lam.kind != crate::expr::LambdaKind::MethodRef
                        || lam.impl_is_static
                        || !lam.captures.is_empty()
                    {
                        continue;
                    }
                    if let Some((_, mapping)) =
                        method_ref_type_args(cls, name, desc, lam, pool)
                    {
                        let vals: Vec<G> = msig
                            .params
                            .iter()
                            .map(|p| {
                                mapping
                                    .iter()
                                    .find(|(n, _)| *n == p.name)
                                    .map(|(_, g)| g.clone())
                                    .unwrap_or(G::TypeVar(p.name.clone()))
                            })
                            .collect();
                        return Some(crate::method::subst_typevars(
                            &msig.ret,
                            &msig.params,
                            &vals,
                        ));
                    }
                }
                None
            }
            _ => None,
        }
    }
    // Pick the ctor by arity (the New node carries no descriptor; the
    // args' static erasures are lambda/Object noise). Prefer the
    // Signature-bearing one on arity ties.
    let Some(cmi) = (0..npc.cf.methods.len()).find(|&i| {
        npc.method_name(i) == Some("<init>")
            && npc
                .method_desc(i)
                .and_then(parse_method_descriptor)
                .map(|md| md.args.len() == args.len())
                .unwrap_or(false)
            && method_signature_of(&npc, i).is_some()
    }) else {
        return None;
    };
    let Some(cmsig) = method_signature_of(&npc, cmi) else {
        return None;
    };
    if cmsig.args.len() != args.len() {
        return None;
    }
    for (a, formal) in args.iter().zip(cmsig.args.iter()) {
        let Some(g) = witnessed_ret(a, pool) else { continue };
        // Unify the formal (own params symbolic, already-bound ones fixed)
        // against the actual's witnessed return.
        let bound_formal = crate::method::subst_typevars(
            formal,
            &csig.params,
            &csig
                .params
                .iter()
                .map(|p| subst.get(&p.name).cloned().unwrap_or(G::TypeVar(p.name.clone())))
                .collect::<Vec<_>>(),
        );
        unify_g_types(&bound_formal, &g, &mut subst);
    }
    // Denotability at the sibling-witnessed new site (see
    // denotable_type_args).
    let want_tvs = want_typevars(want);
    let no_recv: HashSet<String> = HashSet::new();
    let out: Option<Vec<G>> = csig
        .params
        .iter()
        .map(|p| {
            subst.get(&p.name).and_then(|g| {
                if denotable_type_args(g, &csig.params, &want_tvs, &no_recv) {
                    Some(g.clone())
                } else {
                    None
                }
            })
        })
        .collect();
    out
}

/// Pin explicit type arguments on a return-position diamond `new` whose
/// target instantiation is UNDER-DETERMINED (a wildcard slot the target
/// cannot resolve — jdk26 Gatherers Composite.impl returns
/// GathererImpl<T,?,RR>). Runs AFTER the method-ref witness passes so the
/// constructor's functional args already carry their instantiated types
/// for diamond_explicit_args_from_call_args to read.
fn pin_underdetermined_return_diamonds(
    s: &mut Stmt,
    msig: Option<&jcdc_jvm::MethodSignature>,
    pool: &ClassPool,
) {
    let Some(sig) = msig else { return };
    // The owner-diamond pin is target-less (the chained call's formals
    // drive it), so it runs for ANY generic return; the New pin needs a
    // Class return target and is skipped for typevar/wildcard returns.
    let want = match &sig.ret {
        jcdc_jvm::GenericType::Class(cs) => Some(jcdc_jvm::GenericType::Class(cs.clone())),
        _ => None,
    };
    // A diamond RECEIVER of a chained generic call infers Object bounds
    // (the owner position has no target typing): pin its own params from
    // the chained call's formals against the G-typed actuals (jdk26
    // ForkJoinPool.invokeAny `(T) new InvokeAnyRoot<>().invokeAny(tasks,
    // ..)` — tasks: Collection<? extends Callable<T>> binds the root's T;
    // the source writes new InvokeAnyRoot<T>()).
    fn pin_owner_diamond(e: &mut Expr, pool: &ClassPool) {
        let call = match &mut *e {
            Expr::Cast { e: i, .. } => i.as_mut(),
            other => other,
        };
        let Expr::Method { cls: mcls, name, desc, owner: Some(owner), args, .. } = call else { return };
        let Expr::New { cls: ncls, ty, args: nargs, .. } = owner.as_mut() else { return };
        if ncls != mcls && !mcls.starts_with(ncls.as_str()) {
            // the call may be inherited; allow only same-class chains here
        }
        let already = matches!(ty, TypeRef::G(jcdc_jvm::GenericType::Class(cs))
            if cs.parts.last().map(|p| !p.args.is_empty()).unwrap_or(false));
        if already {
            return;
        }
        let Some(npc) = pool.get(ncls.as_str()) else { return };
        let Some(csig) = npc.class_attr("Signature").and_then(|b| {
            if b.len() >= 2 {
                npc.utf8(u16::from_be_bytes([b[0], b[1]])).and_then(|x| parse_class_signature(x))
            } else {
                None
            }
        }) else {
            return;
        };
        if csig.params.is_empty() {
            return;
        }
        // The chained method's Signature on the newed class.
        let want_desc = format!(
            "({}){}",
            desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
            desc.ret.to_descriptor()
        );
        let Some(mi) = (0..npc.cf.methods.len()).find(|&i| {
            npc.method_name(i) == Some(name.as_str())
                && npc.method_desc(i) == Some(want_desc.as_str())
        }) else {
            return;
        };
        let Some(msig) = method_signature_of(&npc, mi) else {
            return;
        };
        if msig.args.len() != args.len() {
            return;
        }
        let own_syms: Vec<jcdc_jvm::GenericType> = csig
            .params
            .iter()
            .map(|p| jcdc_jvm::GenericType::TypeVar(p.name.clone()))
            .collect();
        let mut subst: Vec<(String, jcdc_jvm::GenericType)> = Vec::new();
        for (a, formal) in args.iter().zip(msig.args.iter()) {
            let TypeRef::G(ag) = a.type_ref() else {
                continue;
            };
            let inst_formal =
                crate::method::subst_typevars(formal, &csig.params, &own_syms);
            unify_types(&inst_formal, &ag, &mut subst);
        }
        let resolved: Option<Vec<jcdc_jvm::GenericType>> = csig
            .params
            .iter()
            .map(|p| {
                subst.iter().find(|(n, _)| *n == p.name).and_then(|(_, g)| {
                    // A bare TypeVar value naming the own param is the
                    // caller's same-named typevar (in scope at the new
                    // site, renders identically); deeper own-param mentions
                    // mean the slot stayed symbolic.
                    let ok = match g {
                        jcdc_jvm::GenericType::Wildcard(_) => false,
                        jcdc_jvm::GenericType::TypeVar(n) => {
                            n == &p.name || !g_has_typevar_in(g, &csig.params)
                        }
                        other => !g_has_typevar_in(other, &csig.params),
                    };
                    if ok {
                        Some(g.clone())
                    } else {
                        None
                    }
                })
            })
            .collect();
        let Some(resolved) = resolved else { return };
        let ncs = jcdc_jvm::ClassSig {
            package: ncls.rfind('/').map(|i| ncls[..i].to_string()).unwrap_or_default(),
            parts: vec![jcdc_jvm::ClassSigPart {
                name: ncls.rsplit('/').next().unwrap_or(ncls).to_string(),
                args: resolved,
            }],
        };
        *ty = TypeRef::G(jcdc_jvm::GenericType::Class(ncs));
        let _ = nargs;
    }
    // A diamond new at a return position whose own params are NOT all
    // bound by the direct target (the method returns a SUPERTYPE with
    // fewer params — jdk26 GathererOp.of returns Stream<R> while the
    // diamond is GathererOp<T,A,R>): resolve the gaps from the ctor
    // formals unified against the G-typed actuals (wildcard formal slots
    // impose nothing) and pin explicitly. When ONE actual conflicts, the
    // source re-parameterized it with an unchecked cast
    // ((ReferencePipeline<?,T>) upstream — bare, its P_OUT clashes with
    // the gatherer's T on the diamond's T2 and javac gives up: 无法推断
    // GathererOp<>): resolve without it, pin, then retype it to the
    // substituted formal.
    fn unify_formal_relaxed(
        formal: &jcdc_jvm::GenericType,
        actual: &jcdc_jvm::GenericType,
        subst: &mut Vec<(String, jcdc_jvm::GenericType)>,
    ) -> bool {
        use jcdc_jvm::GenericType as G;
        match formal {
            G::Wildcard(_) => true, // a wildcard formal slot imposes nothing
            G::TypeVar(n) => {
                if let Some((_, prev)) = subst.iter().find(|(m, _)| m == n) {
                    return prev == actual;
                }
                subst.push((n.clone(), actual.clone()));
                true
            }
            G::Array(fi) => match actual {
                G::Array(ai) => unify_formal_relaxed(fi, ai, subst),
                _ => false,
            },
            G::Class(fc) => {
                let G::Class(ac) = actual else { return false };
                if crate::method::classsig_internal(fc) != crate::method::classsig_internal(ac)
                    || fc.parts.len() != ac.parts.len()
                {
                    return false;
                }
                for (pf, pa) in fc.parts.iter().zip(ac.parts.iter()) {
                    if pf.name != pa.name || pf.args.len() != pa.args.len() {
                        return false;
                    }
                    for (x, y) in pf.args.iter().zip(pa.args.iter()) {
                        if !unify_formal_relaxed(x, y, subst) {
                            return false;
                        }
                    }
                }
                true
            }
            other => other == actual,
        }
    }
    fn pin_new_from_ctor_args(e: &mut Expr, pool: &ClassPool) {
        let dbgp = std::env::var("JCDC_DBG_PIN").is_ok();
        if dbgp {
            if let Expr::New { cls, .. } = &*e {
                if cls.contains("GathererOp") {
                    eprintln!("PINCAND {}", cls);
                }
            }
        }
        let (ncls, already, nargs) = match &*e {
            Expr::New { cls, ty, args, .. } => {
                let already = matches!(ty, TypeRef::G(jcdc_jvm::GenericType::Class(cs))
                    if cs.parts.last().map(|p| !p.args.is_empty()).unwrap_or(false));
                (cls.clone(), already, args.len())
            }
            _ => return,
        };
        if already {
            return;
        }
        let Some(npc) = pool.get(&ncls) else { return };
        let Some(csig) = npc.class_attr("Signature").and_then(|b| {
            if b.len() >= 2 {
                npc.utf8(u16::from_be_bytes([b[0], b[1]])).and_then(|x| parse_class_signature(x))
            } else {
                None
            }
        }) else {
            return;
        };
        if csig.params.is_empty() {
            return;
        }
        let Some(cmi) = (0..npc.cf.methods.len()).find(|&i| {
            npc.method_name(i) == Some("<init>")
                && npc
                    .method_desc(i)
                    .and_then(parse_method_descriptor)
                    .map(|md| md.args.len() == nargs)
                    .unwrap_or(false)
                && method_signature_of(&npc, i).is_some()
        }) else {
            return;
        };
        let Some(cmsig) = method_signature_of(&npc, cmi) else { return };
        if cmsig.args.len() != nargs {
            return;
        }
        // Resolve, allowing a single conflicting G actual to be excluded
        // (it becomes the cast).
        enum Resolve {
            Ok(Vec<(String, jcdc_jvm::GenericType)>),
            Conflict(usize),
            Fail,
        }
        fn try_resolve(
            e: &Expr,
            csig: &jcdc_jvm::ClassSignature,
            cmsig: &jcdc_jvm::MethodSignature,
            skip: Option<usize>,
        ) -> Resolve {
            let Expr::New { args, .. } = e else { return Resolve::Fail };
            let mut subst: Vec<(String, jcdc_jvm::GenericType)> = Vec::new();
            for (i, (a, formal)) in args.iter().zip(cmsig.args.iter()).enumerate() {
                if Some(i) == skip {
                    continue;
                }
                let TypeRef::G(ag) = a.type_ref() else { continue };
                if !unify_formal_relaxed(formal, &ag, &mut subst) {
                    return if skip.is_none() {
                        Resolve::Conflict(i)
                    } else {
                        Resolve::Fail
                    };
                }
            }
            // Every own param bound and denotable.
            let resolved: Option<Vec<jcdc_jvm::GenericType>> = csig
                .params
                .iter()
                .map(|p| {
                    subst.iter().find(|(n, _)| *n == p.name).and_then(|(_, g)| {
                        let ok = match g {
                            jcdc_jvm::GenericType::Wildcard(_) => false,
                            jcdc_jvm::GenericType::TypeVar(n) => {
                                n == &p.name || !g_has_typevar_in(g, &csig.params)
                            }
                            other => !g_has_typevar_in(other, &csig.params),
                        };
                        if ok {
                            Some(g.clone())
                        } else {
                            None
                        }
                    })
                })
                .collect();
            match resolved {
                Some(_) => Resolve::Ok(subst),
                None => Resolve::Fail,
            }
        }
        let (subst, skipped) = match try_resolve(e, &csig, &cmsig, None) {
            Resolve::Ok(su) => (su, None),
            _ => {
                // A conflicting/incomplete actual may be the one the source
                // re-parameterized with a cast: try excluding EACH actual
                // in turn and accept the resolution only when exactly one
                // exclusion completes (GathererOp: dropping upstream lets
                // the gatherer bind T,A,R; dropping the gatherer binds
                // nothing).
                let mut wins: Vec<(Vec<(String, jcdc_jvm::GenericType)>, usize)> = Vec::new();
                for j in 0..nargs {
                    if let Resolve::Ok(su) = try_resolve(e, &csig, &cmsig, Some(j)) {
                        wins.push((su, j));
                    }
                }
                if wins.len() != 1 {
                    if dbgp && ncls.contains("GathererOp") { eprintln!("PINRES skip-wins={}", wins.len()); }
                    return;
                }
                let (su, j) = wins.into_iter().next().unwrap();
                if dbgp && ncls.contains("GathererOp") { eprintln!("PINRES skip={}", j); }
                (su, Some(j))
            }
        };
        if dbgp && ncls.contains("GathererOp") { eprintln!("PINRES ok subst={:?}", subst.iter().map(|(k,v)| (k.clone(), format!("{:?}", v))).collect::<Vec<_>>()); }
        let resolved: Vec<jcdc_jvm::GenericType> = csig
            .params
            .iter()
            .map(|p| {
                subst
                    .iter()
                    .find(|(n, _)| *n == p.name)
                    .map(|(_, g)| g.clone())
                    .unwrap_or(jcdc_jvm::GenericType::TypeVar(p.name.clone()))
            })
            .collect();
        // Retype the conflicting actual to its substituted formal (the
        // source's unchecked re-parameterization cast).
        if let Some(si) = skipped {
            if let Expr::New { args, .. } = e {
                if let Some(a) = args.get_mut(si) {
                    let formal_inst =
                        crate::method::subst_typevars(&cmsig.args[si], &csig.params, &resolved);
                    if let TypeRef::G(_) = a.type_ref() {
                        let inner = std::mem::replace(a, Expr::This);
                        *a = Expr::Cast {
                            ty: TypeRef::G(formal_inst),
                            e: Box::new(inner),
                        };
                    }
                }
            }
        }
        let ncs = jcdc_jvm::ClassSig {
            package: ncls.rfind('/').map(|i| ncls[..i].to_string()).unwrap_or_default(),
            parts: vec![jcdc_jvm::ClassSigPart {
                name: ncls.rsplit('/').next().unwrap_or(&ncls).to_string(),
                args: resolved,
            }],
        };
        if let Expr::New { ty, .. } = e {
            *ty = TypeRef::G(jcdc_jvm::GenericType::Class(ncs));
        }
    }
    fn pin(e: &mut Expr, want: &jcdc_jvm::GenericType, pool: &ClassPool) {
        let (ncls, under) = match &*e {
            Expr::New { cls, ty, .. } => {
                // Only diamonds (erased/absent own args) are candidates.
                let already = matches!(ty, TypeRef::G(jcdc_jvm::GenericType::Class(cs))
                    if cs.parts.last().map(|p| !p.args.is_empty()).unwrap_or(false));
                (cls.clone(), !already)
            }
            _ => return,
        };
        if !under {
            return;
        }
        let Some(resolved) = diamond_explicit_args_from_call_args(e, want, pool) else { return };
        let ncs = jcdc_jvm::ClassSig {
            package: ncls.rfind('/').map(|i| ncls[..i].to_string()).unwrap_or_default(),
            parts: vec![jcdc_jvm::ClassSigPart {
                name: ncls.rsplit('/').next().unwrap_or(&ncls).to_string(),
                args: resolved,
            }],
        };
        if let Expr::New { ty, .. } = e {
            *ty = TypeRef::G(jcdc_jvm::GenericType::Class(ncs));
        }
    }
    fn rec(s: &mut Stmt, want: Option<&jcdc_jvm::GenericType>, pool: &ClassPool) {
        match s {
            Stmt::Block(v) => v.iter_mut().for_each(|x| rec(x, want, pool)),
            Stmt::Return(Some(e)) => {
                pin_owner_diamond(e, pool);
                if let Some(w) = want {
                    pin(e, w, pool);
                }
                pin_new_from_ctor_args(e, pool);
            }
            Stmt::If { then_stmt, else_stmt, .. } => {
                rec(then_stmt, want, pool);
                if let Some(x) = else_stmt {
                    rec(x, want, pool);
                }
            }
            Stmt::While { body, .. }
            | Stmt::DoWhile { body, .. }
            | Stmt::ForEach { body, .. }
            | Stmt::Labeled { body, .. }
            | Stmt::Synchronized { body, .. } => rec(body, want, pool),
            Stmt::For { init, body, .. } => {
                init.iter_mut().for_each(|i| rec(i, want, pool));
                rec(body, want, pool);
            }
            Stmt::Switch { cases, default, .. } => {
                for c in cases.iter_mut() {
                    for st in c.body.iter_mut() {
                        rec(st, want, pool);
                    }
                }
                if let Some(d) = default {
                    rec(d, want, pool);
                }
            }
            Stmt::Try { body, catches, finally } => {
                rec(body, want, pool);
                for c in catches.iter_mut() {
                    rec(&mut c.body, want, pool);
                }
                if let Some(f) = finally {
                    rec(f, want, pool);
                }
            }
            _ => {}
        }
    }
    rec(s, want.as_ref(), pool);
}

/// For a generic call whose Signature return is a TYPEVAR ARRAY (T[]),
/// resolve T's element instantiation from the first array formal's actual
/// (declared/instantiated return — Arrays.copyOfRange(ptypes(), ..) with
/// ptypes(): Class<?>[]). Returns the element type when it is a
/// parameterization of `en` (the raw cast's element class).
fn typevar_array_call_elem(
    e: &Expr,
    en: &str,
    pool: &ClassPool,
    pc: &PoolClass,
) -> Option<jcdc_jvm::GenericType> {
    use jcdc_jvm::GenericType as G;
    let Expr::Method { cls, name, desc, args, owner, .. } = e else { return None };
    let dpc = pool.get(cls.as_str())?;
    let want_desc = format!(
        "({}){}",
        desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
        desc.ret.to_descriptor()
    );
    let mi = (0..dpc.cf.methods.len())
        .find(|&i| dpc.method_name(i) == Some(name.as_str()) && dpc.method_desc(i) == Some(want_desc.as_str()))?;
    let msig = method_signature_of(&dpc, mi)?;
    let G::Array(inner) = &msig.ret else { return None };
    let G::TypeVar(tn) = inner.as_ref() else { return None };
    // The formal that is T[] (or mentions T) paired with an array actual.
    for (formal, actual) in msig.args.iter().zip(args.iter()) {
        let is_tv_array = matches!(formal, G::Array(fi) if matches!(fi.as_ref(), G::TypeVar(n) if n == tn));
        if !is_tv_array {
            continue;
        }
        // The actual's declared generic element type.
        let g = match actual {
            Expr::Method { .. } => {
                let mut r = instantiated_method_ret(actual, pool, pc);
                if r.is_none() {
                    // Fall back to the DECLARED Signature return: valid
                    // as-is when the declaring class is non-generic (a raw
                    // owner still calls the same declared method —
                    // MethodType.ptypes(): Class<?>[]; the lambda impl's
                    // erased param starves instantiated_method_ret).
                    if let Expr::Method { cls: acls, name: aname, desc: adesc, .. } = actual {
                        if let Some(adpc) = pool.get(acls.as_str()) {
                            let cls_generic = adpc
                                .class_attr("Signature")
                                .and_then(|b| {
                                    if b.len() >= 2 {
                                        adpc.utf8(u16::from_be_bytes([b[0], b[1]])).and_then(|x| parse_class_signature(x))
                                    } else {
                                        None
                                    }
                                })
                                .map(|cs| !cs.params.is_empty())
                                .unwrap_or(false);
                            if !cls_generic {
                                let awant = format!(
                                    "({}){}",
                                    adesc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
                                    adesc.ret.to_descriptor()
                                );
                                if let Some(ami) = (0..adpc.cf.methods.len()).find(|&i| {
                                    adpc.method_name(i) == Some(aname.as_str())
                                        && adpc.method_desc(i) == Some(awant.as_str())
                                }) {
                                    if let Some(amsig) = method_signature_of(&adpc, ami) {
                                        if matches!(amsig.ret, jcdc_jvm::GenericType::Array(_)) {
                                            r = Some(amsig.ret.clone());
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                if std::env::var("JCDC_DBG_TVA").is_ok() {
                    eprintln!("TVA call={} actual_ret={:?}", name, r);
                }
                r?
            }
            other => match other.type_ref() {
                TypeRef::G(g) => g,
                _ => return None,
            },
        };
        let G::Array(el_g) = &g else { return None };
        let G::Class(el_cs) = el_g.as_ref() else { return None };
        if crate::method::classsig_internal(el_cs) != en {
            return None;
        }
        if el_cs.parts.last().map(|p| p.args.is_empty()).unwrap_or(true) {
            return None; // still raw: nothing gained
        }
        let _ = owner;
        return Some((**el_g).clone());
    }
    None
}

/// Post-upgrade sibling of the cast_generic_locals relay: the raw
/// checkcast over a generic call is upgraded to the precise instantiated
/// return HERE (upgrade_erased_call_casts), after cast_generic_locals
/// ran — an upgraded cast that is invariant-inconvertible to the local's
/// declared type needs the source's RAW intermediate hop (jdk26
/// Properties.store0: `(Set<Map.Entry<String,String>>) (Set) entrySet()`
/// decompiled to the single precise (Set<Map.Entry<Object,Object>>) cast —
/// 无法转换). Demote the cast to its erasure and wrap with the target.
fn relay_inconvertible_local_casts(s: &mut Stmt, vt: &crate::varalloc::VarTable, pool: &ClassPool) {
    use jcdc_jvm::GenericType as G;
    fn relay(value: &mut Expr, want: &TypeRef, pool: &ClassPool) {
        let TypeRef::G(wg @ G::Class(wc)) = want else { return };
        let Expr::Cast { ty, .. } = &*value else { return };
        let TypeRef::G(G::Class(cc)) = ty else { return };
        let args_differ = match (cc.parts.last(), wc.parts.last()) {
            (Some(a), Some(b)) => a.args != b.args,
            _ => false,
        };
        if !args_differ {
            return;
        }
        let cc_internal = crate::method::classsig_internal(cc);
        let wc_internal = crate::method::classsig_internal(wc);
        let convertible_classes = cc_internal == wc_internal
            || is_subtype_of(pool, &jcdc_jvm::JavaType::Object(cc_internal.clone()), &wc_internal);
        if !convertible_classes || g_has_wildcard(&G::Class(cc.clone())) || g_has_wildcard(wg) {
            return;
        }
        let raw = ty.erased();
        if let Expr::Cast { ty: inner_ty, .. } = value {
            *inner_ty = TypeRef::J(raw);
        }
        let v = std::mem::replace(value, Expr::This);
        *value = Expr::Cast { ty: TypeRef::G(wg.clone()), e: Box::new(v) };
    }
    fn rec(s: &mut Stmt, vt: &crate::varalloc::VarTable, pool: &ClassPool) {
        match s {
            Stmt::Block(v) => v.iter_mut().for_each(|x| rec(x, vt, pool)),
            Stmt::LocalDef { var, init: Some(e), .. } => {
                let want = vt.var(*var).ty.clone();
                relay(e, &want, pool);
            }
            Stmt::ExprStmt(Expr::Assign { target, value, .. }) => {
                if let Expr::Local { var, .. } = &**target {
                    let want = vt.var(*var).ty.clone();
                    relay(value, &want, pool);
                }
            }
            Stmt::If { then_stmt, else_stmt, .. } => {
                rec(then_stmt, vt, pool);
                if let Some(e) = else_stmt {
                    rec(e, vt, pool);
                }
            }
            Stmt::While { body, .. }
            | Stmt::DoWhile { body, .. }
            | Stmt::ForEach { body, .. }
            | Stmt::Labeled { body, .. }
            | Stmt::Synchronized { body, .. } => rec(body, vt, pool),
            Stmt::For { init, body, .. } => {
                init.iter_mut().for_each(|i| rec(i, vt, pool));
                rec(body, vt, pool);
            }
            Stmt::Switch { cases, default, .. } => {
                for c in cases.iter_mut() {
                    for st in c.body.iter_mut() {
                        rec(st, vt, pool);
                    }
                }
                if let Some(d) = default {
                    rec(d, vt, pool);
                }
            }
            Stmt::Try { body, catches, finally } => {
                rec(body, vt, pool);
                for c in catches.iter_mut() {
                    rec(&mut c.body, vt, pool);
                }
                if let Some(f) = finally {
                    rec(f, vt, pool);
                }
            }
            _ => {}
        }
    }
    rec(s, vt, pool);
}

/// Cast plain-Object LOCAL actuals at typed reference formals using the
/// call's DESCRIPTOR (no Signature needed): a switch-expression merge var
/// whose per-arm stores LUB'ed to Object loses the source's static type
/// (jdk26 ConstantPoolBuilder.methodHandleEntry(stack77, stack78) —
/// stack78: Object against MemberRefEntry; ConstantValueAttribute
/// of(stack79) stays ambiguous between its two overloads without it).
/// The source compiled, so the runtime value satisfies the formal; the
/// explicit cast restores exactly that guarantee.
fn cast_object_locals_at_typed_formals(e: &mut Expr) {
    let Expr::Method { desc, args, name, .. } = e else { return };
    if name == "<init>" || desc.args.len() != args.len() {
        return;
    }
    for (a, ft) in args.iter_mut().zip(desc.args.iter()) {
        let jcdc_jvm::JavaType::Object(fn_name) = ft else { continue };
        if fn_name == "java/lang/Object" {
            continue;
        }
        if !matches!(a, Expr::Local { .. }) {
            continue;
        }
        if !matches!(a.type_ref(), TypeRef::J(jcdc_jvm::JavaType::Object(n))
            if n == "java/lang/Object")
        {
            continue;
        }
        let inner = std::mem::replace(a, Expr::This);
        *a = Expr::Cast { ty: TypeRef::J(ft.clone()), e: Box::new(inner) };
    }
}

/// True when a generic call's Class-literal actual pins a callee typevar
/// to a concrete class that CONFLICTS with the binding the assignment
/// target imposes on the same typevar (RandomGeneratorFactory.of:
/// factoryOf(String, Class<T#1>) returns RandomGeneratorFactory<T#1>; the
/// target RandomGeneratorFactory<T#2> binds T#1 := T#2 while
/// RandomGenerator.class at the Class<T#1> formal binds T#1 :=
/// RandomGenerator — bare inference: 推论变量T#1具有不兼容的等式约束条件).
pub(crate) fn classlit_want_conflict(value: &Expr, want: &TypeRef, pool: &ClassPool) -> bool {
    use jcdc_jvm::GenericType as G;
    let Expr::Method { cls, name, desc, args, type_args, .. } = value else { return false };
    if !type_args.is_empty() {
        return false;
    }
    let TypeRef::G(want_g) = want else { return false };
    let Some(dpc) = pool.get(cls.as_str()) else { return false };
    let want_desc = format!(
        "({}){}",
        desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
        desc.ret.to_descriptor()
    );
    let Some(mi) = (0..dpc.cf.methods.len())
        .find(|&i| dpc.method_name(i) == Some(name.as_str()) && dpc.method_desc(i) == Some(want_desc.as_str()))
    else {
        return false;
    };
    let Some(msig) = method_signature_of(&dpc, mi) else { return false };
    if msig.params.is_empty() {
        return false;
    }
    // Bindings the TARGET imposes via the generic return.
    let mut map: Vec<(String, G)> = Vec::new();
    if !unify_types(&msig.ret, want_g, &mut map) {
        return false;
    }
    // Class-literal actuals at Class<typevar> formals pin concretely.
    for (a, formal) in args.iter().zip(msig.args.iter()) {
        let Expr::Const(crate::expr::ConstVal::ClassLit(lit)) = a else { continue };
        let G::Class(fc) = formal else { continue };
        let lit_internal = match lit {
            TypeRef::J(jcdc_jvm::JavaType::Object(n)) => n.clone(),
            TypeRef::G(G::Class(cs)) => crate::method::classsig_internal(cs),
            _ => continue,
        };
        let Some(last) = fc.parts.last() else { continue };
        if crate::method::classsig_internal(fc) != "java/lang/Class" || last.args.len() != 1 {
            continue;
        }
        let G::TypeVar(tn) = &last.args[0] else { continue };
        if let Some((_, bound)) = map.iter().find(|(n, _)| n == tn) {
            // The target bound must be a DIFFERENT concrete type than the
            // literal (a typevar bound is the usual conflicting shape).
            let conflicts = match bound {
                G::TypeVar(_) => true,
                G::Class(bc) => crate::method::classsig_internal(bc) != lit_internal,
                _ => true,
            };
            if conflicts {
                return true;
            }
        }
    }
    false
}

/// True when binding a generic call's typevars from the assignment target
/// VIOLATES a declared bound: bare, javac resolves the callee typevar from
/// the target and then rejects the bound (jdk26
/// ReverseOrderSortedSetView.Subset: `c = Comparator.naturalOrder()` —
/// T := E from Comparator<E> against `T extends Comparable<? super T>`
/// with the class's E unbounded; the source casts
/// `(Comparator<E>) Comparator.naturalOrder()` — under the cast the call
/// infers standalone and the unchecked hop bridges).
pub(crate) fn target_binding_bound_conflict(
    value: &Expr,
    want: &TypeRef,
    pool: &ClassPool,
    pc: &PoolClass,
) -> bool {
    use jcdc_jvm::GenericType as G;
    let Expr::Method { cls, name, desc, type_args, .. } = value else { return false };
    if !type_args.is_empty() {
        return false;
    }
    let TypeRef::G(want_g) = want else { return false };
    let Some(dpc) = pool.get(cls.as_str()) else { return false };
    let want_desc = format!(
        "({}){}",
        desc.args.iter().map(|t| t.to_descriptor()).collect::<String>(),
        desc.ret.to_descriptor()
    );
    let Some(mi) = (0..dpc.cf.methods.len())
        .find(|&i| dpc.method_name(i) == Some(name.as_str()) && dpc.method_desc(i) == Some(want_desc.as_str()))
    else {
        return false;
    };
    let Some(msig) = method_signature_of(&dpc, mi) else { return false };
    if msig.params.is_empty() {
        return false;
    }
    let mut map: Vec<(String, G)> = Vec::new();
    if !unify_types(&msig.ret, want_g, &mut map) {
        return false;
    }
    fn trivial_bound(p: &jcdc_jvm::TypeParam) -> bool {
        if !p.interface_bounds.is_empty() {
            return false;
        }
        match &p.class_bound {
            None => true,
            Some(G::Class(cs)) => {
                cs.parts.len() == 1 && cs.parts[0].name == "Object" && cs.parts[0].args.is_empty()
            }
            Some(G::TypeVar(_)) => false,
            _ => false,
        }
    }
    // The enclosing class's own typevar bounds (E in the example).
    let class_params: Vec<jcdc_jvm::TypeParam> = pc
        .class_attr("Signature")
        .and_then(|b| {
            if b.len() >= 2 {
                pc.utf8(u16::from_be_bytes([b[0], b[1]])).and_then(|x| parse_class_signature(x))
            } else {
                None
            }
        })
        .map(|cs| cs.params)
        .unwrap_or_default();
    for p in &msig.params {
        if trivial_bound(p) {
            continue;
        }
        let Some((_, bound_to)) = map.iter().find(|(n, _)| n == &p.name) else { continue };
        // The declared bound's own class (Comparable<? super T> ->
        // java/lang/Comparable); the bound typevar T's identity does not
        // change the required supertype.
        let bound_class = match p.class_bound.as_ref().or_else(|| p.interface_bounds.first()) {
            Some(G::Class(cs)) => crate::method::classsig_internal(cs),
            Some(G::TypeVar(_)) | None => continue, // typevar bound: not cheaply checkable
            _ => continue,
        };
        let er = TypeRef::G(bound_to.clone()).erased();
        let violates = match &er {
            jcdc_jvm::JavaType::Object(n) => {
                if n == &bound_class {
                    false
                } else if let G::TypeVar(tn) = bound_to {
                    // A caller typevar: its own declared bound's erasure
                    // must reach the required supertype.
                    let own_bound = class_params
                        .iter()
                        .find(|cp| &cp.name == tn)
                        .and_then(|cp| {
                            cp.class_bound
                                .clone()
                                .or_else(|| cp.interface_bounds.first().cloned())
                        })
                        .map(|b| TypeRef::G(b).erased())
                        .unwrap_or(jcdc_jvm::JavaType::Object("java/lang/Object".into()));
                    match &own_bound {
                        jcdc_jvm::JavaType::Object(m) => {
                            !is_subtype_of(pool, &jcdc_jvm::JavaType::Object(m.clone()), &bound_class)
                        }
                        _ => true,
                    }
                } else {
                    !is_subtype_of(pool, &jcdc_jvm::JavaType::Object(n.clone()), &bound_class)
                }
            }
            _ => true,
        };
        if violates {
            return true;
        }
    }
    false
}

fn cast_generic_returns(s: &mut Stmt, want: &TypeRef, pc: &PoolClass, pool: &ClassPool) {
    fn fix(e: &mut Expr, want: &TypeRef, pc: &PoolClass, pool: &ClassPool) {
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
        if let Expr::Cast { ty, e: ce } = e {
            // A wildcard-bearing precise target over a GENERIC call poisons
            // its inference: (Map<String,Provider<? extends RG>>) around
            // collect(toMap(..)) flows the wildcard into toMap's U and
            // javac rejects the whole conversion (jdk17
            // RandomGeneratorFactory.createFactoryMap — ground truth: the
            // RAW (Map) form compiles via unchecked conversion). Keep raw.
            let wildcard_target = match want {
                TypeRef::G(g) => g_has_wildcard(g),
                _ => false,
            };
            if matches!(want, TypeRef::G(_))
                && *ty != *want
                && compatible(&ty.erased(), &want.erased())
                && !(wildcard_target && is_generic_call(ce, pool))
            {
                *ty = want.clone();
            }
            return;
        }
        // A return-position diamond new resolves its own type args from
        // the method's generic return through the supertype chain, and
        // its ctor args regain the source casts (jdk11
        // UnmodifiableEntrySet.spliterator: `new
        // UnmodifiableEntrySetSpliterator<>((Spliterator<Entry<K,V>>)
        // c.spliterator())` — the capture-typed bare arg starved the
        // diamond, 无法推断UnmodifiableEntrySetSpliterator<>).
        if let Expr::New { cls: ncls, args, ty: nty, .. } = e {
            if let TypeRef::G(jcdc_jvm::GenericType::Class(wcs)) = want {
                let same_cls = crate::method::classsig_internal(wcs) == *ncls;
                let own = if same_cls {
                    wcs.parts.last().map(|p| p.args.clone()).unwrap_or_default()
                } else {
                    diamond_args_from_target(ncls, wcs, pool).unwrap_or_default()
                };
                // Target left own args unresolved (wildcard slot): let the
                // method-ref actuals fill the gaps and pin the New's type
                // (jdk11/17/26 Collectors.toUnmodifiable* — A := List<T>
                // from List::add at BiConsumer<A,T>; the bare diamond
                // collapsed A to the raw-ref inference and javac gave up:
                // 无法推断CollectorImpl<>的类型参数).
                // Pin the New's type ONLY for the refs-resolved case (the
                // target-resolved path keeps the diamond; a same-class
                // wildcard target like ChronoZonedDateTimeImpl<?> would
                // otherwise print the illegal `new X<?>(..)`).
                let mut pinned: Option<Vec<jcdc_jvm::GenericType>> = None;
                let own = if own.is_empty()
                    && !same_cls
                    && args.iter().any(|a| {
                        matches!(a, Expr::Lambda(l)
                            if l.kind == crate::expr::LambdaKind::MethodRef
                                && !l.impl_is_static
                                && l.captures.is_empty())
                    })
                {
                    match diamond_args_from_refs(ncls, args, wcs, pool) {
                        Some(r) => {
                            pinned = Some(r.clone());
                            r
                        }
                        None => Vec::new(),
                    }
                } else {
                    own
                };
                if let Some(resolved) = &pinned {
                    let already = matches!(nty, TypeRef::G(jcdc_jvm::GenericType::Class(cs2))
                        if cs2.parts.last().map(|p| !p.args.is_empty()).unwrap_or(false));
                    if !already {
                        let ncs = jcdc_jvm::ClassSig {
                            package: ncls
                                .rfind('/')
                                .map(|i| ncls[..i].to_string())
                                .unwrap_or_default(),
                            parts: vec![jcdc_jvm::ClassSigPart {
                                name: ncls.rsplit('/').next().unwrap_or(ncls).to_string(),
                                args: resolved.clone(),
                            }],
                        };
                        *nty = TypeRef::G(jcdc_jvm::GenericType::Class(ncs));
                    }
                }
                if !own.is_empty() {
                    let arg_tys: Vec<jcdc_jvm::JavaType> =
                        args.iter().map(|x| x.type_ref().erased()).collect();
                    if let Some(sub) =
                        instantiated_ctor_params_core(ncls, &own, args.len(), pool, &arg_tys)
                    {
                        apply_ctor_param_casts(args, &sub, pool, Some(pc), &[]);
                    }
                }
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
        // Type an owner field read before asking for the call's source
        // return (this pass runs before cast_wildcard_call_args).
        if let Expr::Method { owner: Some(ow), .. } = e {
            if let Expr::Field {
                owner: fo,
                cls: fcls,
                name: fname,
                ty: fty,
                is_static: false,
                ..
            } = ow.as_mut()
            {
                if !matches!(fty, TypeRef::G(_)) {
                    if let Some(g) =
                        crate::method::instantiated_field_type(fo.as_deref(), fcls, fname, pool, pc)
                    {
                        *fty = g;
                    }
                }
            }
        }
        // Bare generic call with diamond args that stay consistent under
        // target inference: skip the cast entirely (the bare return
        // position is the source shape; a precise cast freezes the
        // arg-driven inference into an invariance failure — jdk11/17/26
        // ImmutableCollections Map1.entrySet).
        if let Expr::Method { cls: mcls, name: mname, desc: mdesc, type_args: mta, args: margs, .. } =
            &*e
        {
            if mta.is_empty()
                && matches!(want, TypeRef::G(_))
                && is_generic_call(e, pool)
                && target_inferable_diamonds(mcls, mname, mdesc, margs, want, pool)
            {
                return;
            }
        }
        // Invariant-incompatible reparameterization of the same class
        // (perms.elements(): Enumeration<PropertyPermission> against the
        // Enumeration<Permission> return): the precise cast is
        // inconvertible, the source used the raw form.
        let mut cast_ty = want.clone();
        if let (TypeRef::G(gw @ jcdc_jvm::GenericType::Class(_)), Expr::Method { .. }) =
            (want, &*e)
        {
            if let Some(src) = instantiated_method_ret(e, pool, pc) {
                if concrete_g_mismatch(&src, gw) {
                    cast_ty = TypeRef::J(want_er.clone());
                }
            }
        }
        let inner = std::mem::replace(e, Expr::This);
        *e = Expr::Cast { ty: cast_ty, e: Box::new(inner) };
    }
    match s {
        Stmt::Block(v) => v.iter_mut().for_each(|x| cast_generic_returns(x, want, pc, pool)),
        Stmt::Return(Some(e)) => fix(e, want, pc, pool),
        Stmt::If { then_stmt, else_stmt, .. } => {
            cast_generic_returns(then_stmt, want, pc, pool);
            if let Some(x) = else_stmt {
                cast_generic_returns(x, want, pc, pool);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => cast_generic_returns(body, want, pc, pool),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(|i| cast_generic_returns(i, want, pc, pool));
            cast_generic_returns(body, want, pc, pool);
        }
        Stmt::ForEach { body, .. } => cast_generic_returns(body, want, pc, pool),
        Stmt::Try { body, catches, finally } => {
            cast_generic_returns(body, want, pc, pool);
            for c in catches {
                cast_generic_returns(&mut c.body, want, pc, pool);
            }
            if let Some(f) = finally {
                cast_generic_returns(f, want, pc, pool);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { cast_generic_returns(res, want, pc, pool); }
            cast_generic_returns(body, want, pc, pool);
            for c in catches {
                cast_generic_returns(&mut c.body, want, pc, pool);
            }
            if let Some(f) = finally {
                cast_generic_returns(f, want, pc, pool);
            }
        }
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(|st| cast_generic_returns(st, want, pc, pool));
            }
            if let Some(d) = default {
                cast_generic_returns(d, want, pc, pool);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => {
            cast_generic_returns(body, want, pc, pool)
        }
        _ => {}
    }
}
