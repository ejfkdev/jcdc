//! Adapters between the JVM front-end and `jdc_core::Ctx`.
//!
//! The functions here are the JVM answers to the core's semantic questions;
//! most of them were Printer methods / classdec helpers before the split (the
//! printer and the pass suite now live in `jdc-core`).

use jcdc_jvm::{ClassPool, GenericType, JavaType, MethodDescriptor, PoolClass};

use crate::expr::{ConstVal, Expr, LambdaExpr, TypeRef};
use crate::varalloc::VarTable;
use crate::jvmctx::JvmCtx;

/// Type name for the current class context (inline printer use).
pub(crate) fn ctx_type_name(pc: &PoolClass, pool: &ClassPool, ty: &TypeRef) -> String {
    let ctx = JvmCtx::new(pc, pool);
    jdc_core::emit::Printer::new(&ctx, &VarTable::default()).type_name(ty)
}

/// Shortened class name for the current class context (inline printer use).
pub(crate) fn ctx_shorten(pc: &PoolClass, pool: &ClassPool, internal: &str) -> String {
    let ctx = JvmCtx::new(pc, pool);
    jdc_core::emit::Printer::new(&ctx, &VarTable::default()).shorten(internal)
}

pub(crate) fn find_outer_of(pc: &PoolClass, pool: &ClassPool) -> Option<String> {
    crate::classdec::find_outer(pc, pool)
}

/// jcdc's family analysis produces its own `Family`; the core has its own
/// (identical shape) — map across.
pub(crate) fn convert_family(pc: &PoolClass, pool: &ClassPool, root: &str) -> jdc_core::Family {
    let fam = crate::classdec::Family::collect(pc, pool);
    let mut out = jdc_core::Family { root: fam.root.clone(), ..Default::default() };
    for (name, nc) in &fam.nested {
        out.nested.insert(
            name.clone(),
            jdc_core::NestedClass {
                name: nc.name.clone(),
                simple: nc.simple.clone(),
                kind: match nc.kind {
                    crate::classdec::NestedKind::Member => jdc_core::NestedKind::Member,
                    crate::classdec::NestedKind::Anonymous => jdc_core::NestedKind::Anonymous,
                    crate::classdec::NestedKind::Local => jdc_core::NestedKind::Local,
                    crate::classdec::NestedKind::Lambda => jdc_core::NestedKind::Lambda,
                },
                access: nc.access,
                sig_header: nc.sig_header.clone(),
            },
        );
    }
    out.anonymous = fam.anonymous.iter().cloned().collect();
    out.locals = fam.locals.iter().cloned().collect();
    out.lambdas = fam.lambdas.iter().cloned().collect();
    let _ = root;
    out
}

pub(crate) fn nested_is_static_pc(pc: &PoolClass) -> bool {
    crate::classdec::nested_is_static(pc)
}

pub(crate) fn class_has_this0_pc(pc: &PoolClass) -> bool {
    crate::classdec::class_has_this0(pc)
}

pub(crate) fn outer_param_via_super_pc(pc: &PoolClass) -> bool {
    (0..pc.cf.methods.len()).any(|mi| {
        pc.method_name(mi) == Some("<init>")
            && pc
                .method_desc(mi)
                .map(|d| crate::classdec::outer_param_via_super(pc, d))
                .unwrap_or(false)
    })
}

pub(crate) fn is_subtype_of_pool(pool: &ClassPool, sub: &JavaType, sup: &str) -> bool {
    crate::classdec::is_subtype_of(pool, sub, sup)
}

/// Class-level type parameters, from the class Signature attribute.
pub(crate) fn class_type_params_of(pool: &ClassPool, internal: &str) -> Vec<jcdc_jvm::TypeParam> {
    let Some(pc) = pool.get(internal) else { return Vec::new() };
    pc.class_attr("Signature")
        .and_then(|b| {
            if b.len() >= 2 {
                pc.utf8(u16::from_be_bytes([b[0], b[1]]))
                    .and_then(jcdc_jvm::parse_class_signature)
            } else {
                None
            }
        })
        .map(|sig| sig.params)
        .unwrap_or_default()
}

pub(crate) fn is_generic_call_expr(e: &Expr, pool: &ClassPool) -> bool {
    crate::classdec::is_generic_call(e, pool)
}

pub(crate) fn generic_call_formals_expr(
    e: &Expr,
    pool: &ClassPool,
    pc: &PoolClass,
) -> Option<(Vec<GenericType>, Vec<String>)> {
    crate::classdec::generic_call_formals(e, pool, pc)
}

pub(crate) fn polymorphic_ret_cast_fn(
    cls: &str,
    name: &str,
    desc: &MethodDescriptor,
) -> Option<JavaType> {
    crate::classdec::polymorphic_ret_cast(cls, name, desc)
}

pub(crate) fn ctor_formals_by_arity_fn(
    cls: &str,
    nargs: usize,
    pool: &ClassPool,
) -> Option<Vec<GenericType>> {
    crate::classdec::ctor_formals_by_arity(cls, nargs, pool)
}

/// `Outer$1Local`-style marker → the local class's internal name, when the
/// current class records one (the printer's `$`-probe used to do this inline).
pub(crate) fn local_class_internal_fn(
    cls_name: &str,
    simple: &str,
    pool: &ClassPool,
) -> Option<String> {
    if let Some(internal) = crate::classdec::local_class_internal(simple) {
        return Some(internal);
    }
    for cand in [format!("{}${}", cls_name, simple)] {
        if pool.get(&cand).is_some() {
            return Some(cand);
        }
    }
    for d in 1..4 {
        let cand = format!("{}${}{}", cls_name, d, simple);
        if pool.get(&cand).is_some() {
            return Some(cand);
        }
    }
    None
}

pub(crate) fn ctor_param_types_fn(
    ctx: &JvmCtx<'_>,
    cls: &str,
    skip: usize,
    n: usize,
    args: &[Expr],
) -> Option<Vec<JavaType>> {
        let pcx = ctx.pool.get(cls)?;
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
        let mut cands: Vec<Vec<JavaType>> = Vec::new();
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
                            (Some(enc), Some(JavaType::Object(nm))) => nm == enc,
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
                fn arg_fits(a: &Expr, p: &JavaType) -> bool {
                    use JavaType as J;
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
                let mut best: Option<(usize, Vec<JavaType>)> = None;
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

pub(crate) fn sam_ret_cast_fn(
    ctx: &JvmCtx<'_>,
    g: &jcdc_jvm::GenericType,
    sam_name: &str,
) -> Option<TypeRef> {
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
        let pc = ctx.pool.get(&internal)?;
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

/// Decompile a nested method body (lambda impl / anonymous-class method /
/// local-class method) and run the JVM front-end's idiom recovery on it.
pub(crate) fn nested_method_fn(
    ctx: &JvmCtx<'_>,
    l: &LambdaExpr,
    outer_vt: &VarTable,
) -> Option<jdc_core::MethodBody> {
    let owner_pc = ctx.pool.get(l.impl_owner.as_str())?;
    let body_stmts = owner_pc
        .find_own_method(&l.impl_name, &l.impl_desc.to_string())
        .and_then(|mi| crate::method::decompile_method(&owner_pc, ctx.pool, mi).ok())
        .flatten();
let crate::method::MethodBody { mut body, mut vt, .. } = body_stmts?;
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
                    outer_vt.vars.iter().find(|ov| ov.id == *var)
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
            ctx.pool,
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
    crate::classdec::witness_comparison_operands(&mut body, None, ctx.pool);
    crate::classdec::upgrade_typevar_array_casts(&mut body, ctx.pool, ctx.pc);
    {
        let fam = crate::classdec::Family::collect(ctx.pc, ctx.pool);
        let _depth = crate::classdec::lambda_body_depth_enter();
        crate::classdec::inline_anonymous(
            &mut body,
            ctx.pc,
            ctx.pool,
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
            ctx.pc,
            ctx.pool,
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
        let outer_this = crate::classdec::outer_this_map(ctx.pc);
        if !outer_this.is_empty() {
            crate::classdec::substitute_captures(
                &mut body,
                &outer_this,
                ctx.pool,
            );
        }
    }
    crate::classdec::restore_enum_switches(&mut body, ctx.pc, ctx.pool);
    crate::classdec::fold_restart_guards(&mut body);
    // Nested calls inside lambda bodies need the same
    // overload-disambiguation/instantiation witnesses
    // as top-level method bodies (BootstrapLogger
    // doPrivileged(() -> .., acc) stays ambiguous
    // without the raw SAM cast).
    crate::classdec::cast_wildcard_call_args(
        &mut body,
        ctx.pool,
        ctx.pc,
        &vt,
        &[],
    );
    crate::method::prune_post_loop_label_breaks(&mut body);
    crate::method::demote_undefined_label_jumps(&mut body);
    crate::classdec::split_return_assigns(&mut body);
    Some(jdc_core::ctx_method_body(body, vt, l.impl_desc.clone()))
}
