//! Per-method decompilation pipeline:
//! code bytes → CFG → block expressions → region tree → statement tree →
//! post-passes (catch vars, synchronized, if/loop refinements).

use std::collections::{HashMap, HashSet};

use jcdc_classfile::MethodAccessFlags;
use jcdc_jvm::{parse_method_descriptor, ClassPool, JavaType, MethodDescriptor, PoolClass};

use crate::block::Cfg;
use crate::builder::{BlockResult, BuildError, Builder};
use crate::convert::Converter;
use crate::expr::{ConstVal, Expr, TypeRef};
use crate::stmt::Stmt;
use crate::structure::Structurer;
use crate::varalloc::VarTable;

pub struct MethodBody {
    /// Final statement tree.
    pub body: Stmt,
    pub vt: VarTable,
    pub desc: MethodDescriptor,
}

/// Decompile one method. Returns Err only for malformed input; unsupported
/// constructs degrade to comments inside the statement tree.
#[track_caller]
pub fn decompile_method(
    pc: &PoolClass,
    pool: &ClassPool,
    m_idx: usize,
) -> Result<Option<MethodBody>, String> {
    let m = &pc.cf.methods[m_idx];
    if std::env::var("JCDC_TRACE_METHOD").is_ok() {
        let loc = std::panic::Location::caller();
        eprintln!("mtrace {}.{}{} <- {}:{}", pc.internal_name,
            pc.method_name(m_idx).unwrap_or("?"),
            pc.method_desc(m_idx).unwrap_or("?"),
            loc.file(), loc.line());
    }
    thread_local! {
        static DECOMP_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    }
    let d = DECOMP_DEPTH.with(|c| { let v = c.get() + 1; c.set(v); v });
    struct DepthGuard;
    impl Drop for DepthGuard {
        fn drop(&mut self) {
            DECOMP_DEPTH.with(|c| c.set(c.get() - 1));
        }
    }
    let _dg = DepthGuard;
    if d == 1 {
        crate::sese::MATEXIT_FIRED.with(|f| f.set(false));
    }
    if d > 64 {
        // Safety net: a self-referential method-ref cycle (impl body
        // contains a lambda whose impl is the method being decompiled)
        // recurses decompile_method forever; the 512 MB worker stack
        // overflows and aborts the WHOLE process (uncatchable), silently
        // truncating tree runs (jdk26 FallbackLinker.assertNotEmpty ->
        // forEach(FallbackLinker::assertNotEmpty), 56k re-entries).
        // Bail gracefully instead — callers treat Err as "no body".
        return Err(format!(
            "decompile_method recursion depth {} at {}.{}",
            d, pc.internal_name,
            pc.method_name(m_idx).unwrap_or("?")
        ));
    }
    let access = m.access_flags;
    if access.contains(MethodAccessFlags::ABSTRACT) || access.contains(MethodAccessFlags::NATIVE) {
        return Ok(None);
    }
    let desc_str = pc.method_desc(m_idx).ok_or("missing descriptor")?;
    let desc = parse_method_descriptor(desc_str).ok_or_else(|| format!("bad descriptor {}", desc_str))?;
    let is_static = access.contains(MethodAccessFlags::STATIC);

    let code = crate::varalloc::code_attribute(pc, m_idx).ok_or("missing Code attribute")?;
    let code_len = code.code.len() as u16;
    let vt = VarTable::build(pc, m_idx, &desc, is_static, code.max_locals, code_len);

    let exc: Vec<(u16, u16, u16, u16)> = code
        .exception_table
        .iter()
        .map(|e| (e.start_pc, e.end_pc, e.handler_pc, e.catch_type))
        .collect();
    let cfg = Cfg::build(pc, &code.code, &exc);

    // Temp-local forwarding pairs: a slot stored EXACTLY once and loaded
    // EXACTLY once by the immediately-following instruction in the same
    // block (javac's pattern-match temps: `checkcast X; astore n;
    // aload n`). Forwarding removes the temp's LocalDef so value-diamond
    // arms stay pure and fold to ternaries (jdk26 PrintWriter ctor
    // delegation `this(out, autoFlush, out instanceof PrintStream ?
    // ((PrintStream) out).charset() : Charset.defaultCharset())`).
    let fwd = {
        use jcdc_classfile::Opcode as O;
        let mut stores_by_slot: HashMap<u16, Vec<(usize, usize)>> = HashMap::new();
        let mut loads_by_slot: HashMap<u16, Vec<(usize, usize)>> = HashMap::new();
        for b in &cfg.blocks {
            for (idx, ins) in b.ins.iter().enumerate() {
                let (slot, kind) = match ins.op {
                    O::Istore | O::Lstore | O::Fstore | O::Dstore | O::Astore => {
                        (ins.a as u16, 1u8)
                    }
                    O::Istore0 | O::Istore1 | O::Istore2 | O::Istore3 => {
                        ((ins.op as u8 - O::Istore0 as u8) as u16, 1)
                    }
                    O::Lstore0 | O::Lstore1 | O::Lstore2 | O::Lstore3 => {
                        ((ins.op as u8 - O::Lstore0 as u8) as u16, 1)
                    }
                    O::Fstore0 | O::Fstore1 | O::Fstore2 | O::Fstore3 => {
                        ((ins.op as u8 - O::Fstore0 as u8) as u16, 1)
                    }
                    O::Dstore0 | O::Dstore1 | O::Dstore2 | O::Dstore3 => {
                        ((ins.op as u8 - O::Dstore0 as u8) as u16, 1)
                    }
                    O::Astore0 | O::Astore1 | O::Astore2 | O::Astore3 => {
                        ((ins.op as u8 - O::Astore0 as u8) as u16, 1)
                    }
                    O::Iload | O::Lload | O::Fload | O::Dload | O::Aload => {
                        (ins.a as u16, 2u8)
                    }
                    O::Iload0 | O::Iload1 | O::Iload2 | O::Iload3 => {
                        ((ins.op as u8 - O::Iload0 as u8) as u16, 2)
                    }
                    O::Lload0 | O::Lload1 | O::Lload2 | O::Lload3 => {
                        ((ins.op as u8 - O::Lload0 as u8) as u16, 2)
                    }
                    O::Fload0 | O::Fload1 | O::Fload2 | O::Fload3 => {
                        ((ins.op as u8 - O::Fload0 as u8) as u16, 2)
                    }
                    O::Dload0 | O::Dload1 | O::Dload2 | O::Dload3 => {
                        ((ins.op as u8 - O::Dload0 as u8) as u16, 2)
                    }
                    O::Aload0 | O::Aload1 | O::Aload2 | O::Aload3 => {
                        ((ins.op as u8 - O::Aload0 as u8) as u16, 2)
                    }
                    // iinc reads AND writes: registering it on both sides
                    // disqualifies the slot from forwarding.
                    O::Iinc => (ins.a as u16, 3u8),
                    _ => continue,
                };
                match kind {
                    1 => stores_by_slot.entry(slot).or_default().push((b.id, idx)),
                    2 => loads_by_slot.entry(slot).or_default().push((b.id, idx)),
                    _ => {
                        stores_by_slot.entry(slot).or_default().push((b.id, idx));
                        loads_by_slot.entry(slot).or_default().push((b.id, idx));
                    }
                }
            }
        }
        let mut pend: u16 = if is_static { 0 } else { 1 };
        for a in &desc.args {
            pend += match a {
                jcdc_jvm::JavaType::Long | jcdc_jvm::JavaType::Double => 2,
                _ => 1,
            };
        }
        let mut fwd_stores: std::collections::HashSet<u16> = std::collections::HashSet::new();
        let mut fwd_loads: HashMap<u16, u16> = HashMap::new();
        for (slot, ss) in &stores_by_slot {
            if *slot < pend || *slot >= code.max_locals {
                continue;
            }
            if ss.len() != 1 {
                continue;
            }
            let Some(ls) = loads_by_slot.get(slot) else { continue };
            if ls.len() != 1 {
                continue;
            }
            let (sb, si) = ss[0];
            let (lb, li) = ls[0];
            if sb != lb || si + 1 != li {
                continue; // load must be the instruction right AFTER the store
            }
            let insb = &cfg.blocks[sb].ins;
            let (st, ld) = (&insb[si], &insb[li]);
            if st.pc + st.size != ld.pc {
                continue;
            }
            // The stored value must not be a plain load of the SAME slot.
            // (defensive; cannot happen with single store+load)
            fwd_stores.insert(st.pc);
            fwd_loads.insert(ld.pc, *slot);
        }
        (fwd_stores, fwd_loads)
    };

    // Build expressions per block in reverse postorder so that operand
    // stacks propagate across block boundaries. At merge points whose
    // predecessors bring different stacks, introduce synthetic "stack
    // variables": each predecessor assigns its outgoing value to the
    // variable; the merge block reads it (fixpoint iteration).
    let n = cfg.blocks.len();
    let universe: std::collections::HashSet<usize> = (0..n).collect();
    let mut order = crate::structure::reverse_postorder(&cfg, cfg.entry, &universe);
    {
        let mut seen: std::collections::HashSet<usize> = order.iter().copied().collect();
        for b in &cfg.blocks {
            if seen.insert(b.id) {
                order.push(b.id);
            }
        }
    }
    let mut handler_heads: std::collections::HashSet<usize> = std::collections::HashSet::new();
    for r in &cfg.exc_ranges {
        if let Some(hb) = cfg.block_at(r.handler) {
            handler_heads.insert(hb);
        }
    }

    let mut vt = vt;
    // A merge block's per-depth slot: a fresh stack var (divergent sides
    // copy into it) or the expression every side agreed on (passed
    // through verbatim — see the diverged-merge comment).
    #[derive(Clone)]
    enum MergeSlot {
        Var(u32),
        Pass(Expr),
    }
    let mut merge_vars: HashMap<usize, Vec<MergeSlot>> = HashMap::new();
    // Merge blocks whose input stack is a folded ternary expression.
    let mut merge_cond: HashMap<usize, Vec<Expr>> = HashMap::new();
    // Folded diamond regions: merge -> (root header, blocks absorbed).
    let mut fold_regions: HashMap<usize, (usize, std::collections::HashSet<usize>)> = HashMap::new();
    let mut results: Vec<BlockResult> = Vec::with_capacity(n);
    results.resize_with(n, || BlockResult {
        stmts: vec![],
        out_stack: vec![],
        term: crate::builder::Term::Return(None),
    });
    let mut errors: HashMap<usize, String> = HashMap::new();
    let mut var_counter = 0usize;
    let mut prev_out: Vec<Option<Vec<Expr>>> = vec![None; n];
    // Per-predecessor statements storing outgoing stack values into merge
    // variables; recomputed each round and re-appended after each rebuild.
    #[allow(unused_assignments)]
    let mut appends: HashMap<usize, Vec<Stmt>> = HashMap::new();

    loop {
        // Errors from intermediate rounds (before merges are folded) are
        // transient; only the final round counts.
        errors.clear();
        let mut out_stacks: Vec<Option<Vec<Expr>>> = vec![None; n];
        let mut in_stacks: Vec<Vec<Expr>> = vec![Vec::new(); n];
        let _builder = Builder::new(pc, pool, &vt, &desc, is_static);

        let entry_dom = crate::structure::compute_dominators(
            &cfg,
            &(0..n).collect::<std::collections::HashSet<usize>>(),
            cfg.entry,
        );
        // Phase 1: iterate in-stack propagation to a fixpoint WITHIN this
        // pass (blocks are (re)built whenever their input stack changes),
        // so diamond folds compose across chained merges immediately.
        let mut diverged = false;
        let mut new_merge_cond: HashMap<usize, Vec<Expr>> = HashMap::new();
        let mut new_fold_regions: HashMap<usize, (usize, HashSet<usize>)> = HashMap::new();
        let mut new_merge_vars: HashMap<usize, Vec<MergeSlot>> = HashMap::new();
        let mut new_appends: HashMap<usize, Vec<Stmt>> = HashMap::new();
        let mut built_once = vec![false; n];
        let mut iter = 0;
        loop {
            iter += 1;
            if iter > 32 {
                break;
            }
            let mut changed_this_iter = false;
            for &bid in &order {
                let b = &cfg.blocks[bid];
                let in_stack: Vec<Expr> = if bid == cfg.entry {
                    Vec::new()
                } else if handler_heads.contains(&bid) {
                    vec![Expr::Const(crate::expr::ConstVal::Null)]
                } else if let Some(c) = merge_cond.get(&bid) {
                    c.clone()
                } else if let Some(vars) = merge_vars.get(&bid) {
                    vars.iter()
                        .map(|slot| match slot {
                            MergeSlot::Var(v) => {
                                let info = vt.var(*v);
                                Expr::Local { var: *v, ty: info.ty.clone() }
                            }
                            MergeSlot::Pass(e) => e.clone(),
                        })
                        .collect()
                } else {
                    let preds: Vec<usize> = b.pred.clone();
                    let known: Vec<(usize, Vec<Expr>)> = preds
                        .iter()
                        .filter_map(|p| out_stacks[*p].clone().map(|o| (*p, o)))
                        .collect();
                    if known.len() >= 2 {
                        let first = known[0].1.clone();
                        if known.iter().all(|(_, o)| *o == first) {
                            first
                        } else {
                            // Try pure value-diamond folding first; only fall
                            // back to stack variables when folding fails.
                            let mut folded: Option<Vec<Expr>> = None;
                            {
                                let r = try_diamond_fold(
                                    bid, &known, &out_stacks, &results_terms_placeholder(&results), &cfg, &entry_dom,
                                );
                                if let Some((f, root, vis)) = r {
                                    new_fold_regions.insert(bid, (root, vis));
                                    folded = Some(f);
                                }
                            }
                            if let Some(f) = folded {
                                merge_cond.insert(bid, f.clone());
                                f
                            } else {
                                diverged = true;
                                // Stack variables. Per depth: None when
                                // EVERY pred contributes the identical
                                // expression — the merge passes it through
                                // instead of copying it into a fresh var.
                                // Two reasons: a FRESH expression (the
                                // `new C` twin riding a dup across the
                                // inner-ternary merge, jdk26 Gatherers
                                // mapConcurrent) must not be duplicated —
                                // each copy site would re-materialize
                                // `new C(..)` (double side effect) or,
                                // worse, the twin got a var the ctor never
                                // assigned (invokespecial on a VAR receiver
                                // emits a call stmt and pushes NOTHING
                                // back), leaving the downstream throw
                                // reading a never-assigned blank (可能尚未
                                // 初始化变量stack389); and a plain Local
                                // copy is pure noise. With pass-through the
                                // ctor sees the raw New twin again, folds
                                // it, and re-pushes the initialized object.
                                let vars: Vec<MergeSlot> = match merge_vars.get(&bid) {
                                    Some(v) => v.clone(),
                                    None => {
                                        let depth = known.iter().map(|(_, o)| o.len()).min().unwrap_or(0);
                                        let mut vs: Vec<MergeSlot> = Vec::with_capacity(depth);
                                        for d in 0..depth {
                                            let first_at_d = known[0].1.get(d);
                                            if let Some(e) = first_at_d {
                                                if known.iter().all(|(_, o)| o.get(d) == first_at_d) {
                                                    vs.push(MergeSlot::Pass(e.clone()));
                                                    continue;
                                                }
                                            }
                                            // Join the divergent branch types:
                                            // the merge variable must accept
                                            // every side (String vs E, ...).
                                            // Join the non-null branch types.
                                            // A generic side (type variable) or
                                            // a plain Object side cannot be
                                            // captured by a narrower declared
                                            // type, so fall back to Object
                                            // which accepts every side.
                                            let mut sides: Vec<JavaType> = Vec::new();
                                            let mut wide = false;
                                            for (_, o) in known.iter() {
                                                let Some(x) = o.get(d) else { continue };
                                                if matches!(x, Expr::Const(crate::expr::ConstVal::Null)) {
                                                    continue;
                                                }
                                                if matches!(x, Expr::This) {
                                                    sides.push(JavaType::Object(
                                                        pc.internal_name.clone(),
                                                    ));
                                                    continue;
                                                }
                                                if matches!(x.type_ref(), TypeRef::G(_)) {
                                                    wide = true;
                                                }
                                                let e = x.type_ref().erased();
                                                if matches!(&e, JavaType::Object(n) if n == "java/lang/Object") {
                                                    wide = true;
                                                }
                                                sides.push(e);
                                            }
                                            // Only merge when every non-null side
                                            // agrees; a genuine Object/generic side
                                            // keeps the merge variable at Object so
                                            // it accepts all branch values.
                                            // All-numeric sides merge by numeric
                                            // promotion (char/int ternaries).
                                            let uniform = sides.windows(2).all(|w| w[0] == w[1]);
                                            let numeric = |t: &JavaType| {
                                                matches!(
                                                    t,
                                                    JavaType::Boolean
                                                        | JavaType::Byte
                                                        | JavaType::Char
                                                        | JavaType::Short
                                                        | JavaType::Int
                                                        | JavaType::Long
                                                        | JavaType::Float
                                                        | JavaType::Double
                                                )
                                            };
                                            let all_numeric =
                                                !sides.is_empty() && sides.iter().all(numeric);
                                            let (tyj, is_wide) = if sides.is_empty() {
                                                (JavaType::Object("java/lang/Object".into()), false)
                                            } else if all_numeric {
                                                let mut t = sides[0].clone();
                                                for x in &sides[1..] {
                                                    t = join_types(&t, x);
                                                }
                                                (t, false)
                                            } else if uniform && !wide {
                                                (sides[0].clone(), false)
                                            } else if uniform {
                                                (sides[0].clone(), true)
                                            } else {
                                                (JavaType::Object("java/lang/Object".into()), true)
                                            };
                                            if std::env::var("JCDC_DBG_MERGE").is_ok() {
                                                eprintln!("MERGE bid={} d={} sides={:?} wide={} tyj={:?}", bid, d, sides, wide, &tyj);
                                            }
                                            let ty = TypeRef::J(tyj);
                                            let slot = (code.max_locals + 100 + var_counter as u16) as u16;
                                            var_counter += 1;
                                            // Globally unique names: lambda
                                            // and nested-class bodies are
                                            // inlined into enclosing
                                            // methods, where Java forbids
                                            // shadowing locals.
                                            static STACK_SEQ: std::sync::atomic::AtomicU64 =
                                                std::sync::atomic::AtomicU64::new(0);
                                            let seq = STACK_SEQ.fetch_add(
                                                1,
                                                std::sync::atomic::Ordering::Relaxed,
                                            );
                                            let v = vt.add_stack_var(slot, format!("stack{}", seq), ty);
                                            if is_wide {
                                                vt.wide_stack_vars.insert(v);
                                            }
                                            vs.push(MergeSlot::Var(v));
                                        }
                                        vs
                                    }
                                };
                                new_appends.remove(&bid);
                                for (p, o) in &known {
                                    let mut adds = Vec::new();
                                    for (d, slot) in vars.iter().enumerate() {
                                        let MergeSlot::Var(v) = slot else { continue };
                                        if d < o.len() {
                                            adds.push(Stmt::LocalDef {
                                                var: *v,
                                                init: Some(o[d].clone()),
                                                is_final: false,
                                                force_type: true,
                                            });
                                        }
                                    }
                                    new_appends.entry(*p).or_default().extend(adds);
                                }
                                merge_vars.insert(bid, vars.clone());
                                vars.iter()
                                    .map(|slot| match slot {
                                        MergeSlot::Var(v) => {
                                            let info = vt.var(*v);
                                            Expr::Local { var: *v, ty: info.ty.clone() }
                                        }
                                        // Identical on every pred: pass the
                                        // common expression through.
                                        MergeSlot::Pass(e) => e.clone(),
                                    })
                                    .collect()
                            }
                        }
                    } else {
                        known.first().map(|(_, o)| o.clone()).unwrap_or_default()
                    }
                };
                let need_build = !built_once[bid] || in_stacks[bid] != in_stack;
                in_stacks[bid] = in_stack.clone();
                if !need_build {
                    continue;
                }
                built_once[bid] = true;
                changed_this_iter = true;
                let builder = Builder::new(pc, pool, &vt, &desc, is_static)
                    .with_fwd(fwd.clone());
                match builder.build_block(&b.ins, in_stack) {
                    Ok(r) => {
                        if std::env::var("JCDC_DBG_BLOCKS").is_ok() {
                            eprintln!(
                                "build block {} [{}..{}) ins={} in_stack={} stmts={} out={} succ={:?} term={}",
                                bid, b.start, b.end, b.ins.len(), in_stacks[bid].len(),
                                r.stmts.len(), r.out_stack.len(), b.succ,
                                match &r.term {
                                    crate::builder::Term::Fallthrough => "Fall".to_string(),
                                    crate::builder::Term::Goto => format!("Goto->{}", b.succ.first().copied().unwrap_or(usize::MAX)),
                                    crate::builder::Term::Cond { .. } => format!("Cond(f={},t={})", b.succ.first().copied().unwrap_or(0), b.succ.get(1).copied().unwrap_or(0)),
                                    crate::builder::Term::Switch { .. } => format!("Switch{:?}", b.succ),
                                    crate::builder::Term::Return(_) => "Return".to_string(),
                                    crate::builder::Term::Throw(_) => "Throw".to_string(),
                                    crate::builder::Term::Jsr => "Jsr".to_string(),
                                    crate::builder::Term::Ret => "Ret".to_string(),
                                }
                            );
                        }
                        let keep_out = !matches!(
                            r.term,
                            crate::builder::Term::Return(_) | crate::builder::Term::Throw(_)
                        );
                        if keep_out {
                            out_stacks[bid] = Some(r.out_stack.clone());
                        } else {
                            out_stacks[bid] = None;
                        }
                        results[bid] = r;
                    }
                    Err(BuildError(msg)) => {
                        results[bid] = BlockResult {
                            stmts: vec![Stmt::Comment(format!("$JCDC-BLOCK-ERROR: {}", msg))],
                            out_stack: vec![],
                            term: crate::builder::Term::Return(None),
                        };
                        out_stacks[bid] = Some(vec![]);
                        errors.insert(bid, msg.clone());
                    }
                }
            }
            if !changed_this_iter {
                break;
            }
        }

        // Attach merge-variable stores to predecessor blocks. The inner
        // loop only exits once every block's input stack is unchanged, so
        // this state is final.
        appends = new_appends;
        for (p, adds) in appends.iter() {
            results[*p].stmts.extend(adds.iter().cloned());
        }
        fold_regions.extend(new_fold_regions);
        let _ = &mut new_merge_cond;
        let _ = &mut new_merge_vars;
        let _ = &mut diverged;
        let _ = &mut prev_out;
        break;
    }

    // Structure.
    let diamond_merges: std::collections::HashSet<usize> =
        merge_cond.keys().copied().collect();
    let mut structurer = Structurer::with_diamonds(&cfg, &results, diamond_merges, fold_regions);
    structurer.final_fields = pc
        .cf
        .fields
        .iter()
        .filter(|f| {
            f.access_flags
                .contains(jcdc_classfile::FieldAccessFlags::FINAL)
        })
        .filter_map(|f| pc.utf8(f.name_index).map(|n| n.to_string()))
        .collect();
    if std::env::var("JCDC_DBG_MNAME").is_ok() {
        eprintln!(
            "METHOD {} {}",
            pc.method_name(m_idx).unwrap_or("?"),
            desc_str
        );
    }
    let region = structurer.structure_method();

    // Convert to statements.
    let copied_tails = structurer.copied_tails.clone();
    // Final fields of this class: the converter must not duplicate a shared
    // terminator block that assigns one (a final field accepts exactly one
    // assignment; copies are a compile error, sun.security.util.Debug).
    let final_fields: std::collections::HashSet<String> = pc
        .cf
        .fields
        .iter()
        .filter(|f| {
            f.access_flags
                .contains(jcdc_classfile::FieldAccessFlags::FINAL)
        })
        .filter_map(|f| pc.utf8(f.name_index).map(|n| n.to_string()))
        .collect();
    let mut converter = Converter::new(&cfg, &results)
        .with_copied_tails(copied_tails)
        .with_final_fields(final_fields);
    let mut body = converter.convert(region);
    if let Ok(want) = std::env::var("JCDC_DBG_BODY") {
        if pc.method_name(m_idx) == Some(want.as_str())
            || (want == "<init>" && pc.method_name(m_idx) == Some("<init>")
                && desc_str.contains(&std::env::var("JCDC_DBG_BODY_DESC").unwrap_or_default()))
        {
            eprintln!("BODY-CONVERT: {:#?}", body);
        }
    }
    macro_rules! dbg_body {
        ($tag:expr) => {
            if let Ok(want) = std::env::var("JCDC_DBG_BODY") {
                if pc.method_name(m_idx) == Some(want.as_str()) {
                    eprintln!("BODY[{}]: {:#?}", $tag, body);
                }
            }
        };
    }

    // Post-passes.
    resolve_catch_vars(&mut vt, &mut body);
    assign_catch_names(&mut vt, &mut body);
    cleanup(&mut body);
    reconstruct_synchronized(&mut body);
    dbg_body!("post-cleanup1");
    strip_monitors_in_sync(&mut body);
    drop_monitor_stores(&mut body, &vt);
    strip_selftype_checkcasts(&mut body, pool);
    cleanup(&mut body);
    restore_asserts(&mut body);
    cleanup(&mut body);
    twr_j11(&mut body);
    cleanup(&mut body);
    twr_j7(&mut body);
    cleanup(&mut body);
    dedupe_finally(&mut body);
    cleanup(&mut body);
    dbg_body!("post-dedupe");
    prune_finally_rethrows(&mut body);
    cleanup(&mut body);
    dbg_body!("post-prune-rethrows");
    fix_empty_catchall(&mut body);
    cleanup(&mut body);
    let stack_vars = vt.stack_vars.clone();
    fold_this_stack_vars(&mut body, &vt, &stack_vars);
    hoist_stack_vars(&mut body, &stack_vars);
    cleanup(&mut body);
    dbg_body!("post-stackvars");
    let numeric_ret = matches!(
        desc.ret,
        jcdc_jvm::JavaType::Byte
            | jcdc_jvm::JavaType::Short
            | jcdc_jvm::JavaType::Int
            | jcdc_jvm::JavaType::Long
            | jcdc_jvm::JavaType::Char
            | jcdc_jvm::JavaType::Float
            | jcdc_jvm::JavaType::Double
    );
    booleanize_deep_stmt_r(&mut body, numeric_ret, &desc.ret);
    cleanup(&mut body);
    dbg_body!("post-booleanize");
    rotate_empty_then(&mut body);
    cleanup(&mut body);
    // Type inference for synthetic (no-LVT) variables, then fix the embedded
    // types in Local expressions.
    let ret_ty = desc.ret.clone();
    infer_var_types(&mut vt, &mut body, &ret_ty, pc);
    dbg_body!("post-infer");
    prune_dead_synth_stores(&mut body, &vt);
    dbg_body!("post-prune-dead");
    cast_generic_locals(&vt, pool, pc, &mut body);
    cast_object_returns(&mut body, &ret_ty);
    cast_narrowing_assigns(&vt, &mut body);
    if pc.method_name(m_idx) != Some("<init>") {
        fold_merged_new_inits(&mut body, pc);
        cleanup(&mut body);
    }
    if pc.method_name(m_idx) == Some("<init>") {
        hoist_ctor_call_guards(&mut body);
        cleanup(&mut body);
    }
    dedupe_declarations(&mut body);
    ensure_declared(&vt, &mut body);
    cleanup(&mut body);
    // Flattening can merge sibling scopes; dedupe once more to be safe.
    dedupe_declarations(&mut body);
    // Variables declared in a nested scope but used after it must be hoisted.
    hoist_escaped_vars(&mut body, &vt);
    cleanup(&mut body);
    prune_dead_breaks(&mut body);
    prune_post_loop_label_breaks(&mut body);
    demote_undefined_label_jumps(&mut body);
    cleanup(&mut body);
    disambiguate_nested_locals(&mut vt, &body);
    prune_unreachable(&mut body);
    cleanup(&mut body);
    dbg_body!("post-unreachable");

    if !errors.is_empty() {
        let n = errors.len();
        prepend_comment(&mut body, format!("$JCDC: {} block(s) failed to decompile", n));
    }
    // Post-pipeline safety net for the matexit splices: the conversion-
    // time trial cannot see pathologies CREATED BY THE POST-CONVERT
    // PASSES (classify_loop/rotate_empty_then rotations turning a spliced
    // arm all-abrupt and stranding the parent's next sibling — jdk
    // ConcurrentHashMap.getTable 无法访问的语句 x3 trees). When this method
    // spliced an exit cascade and the final tree strands statements after
    // a terminator, redo the method with matexit disabled (one retry; the
    // disabled flag makes it terminate).
    if crate::sese::MATEXIT_FIRED.with(|f| f.get())
        && crate::structure::Structurer::stmt_splice_pathology(&body)
    {
        crate::sese::MATEXIT_DISABLED.with(|d| d.set(true));
        // The retry must see FIRED=false: the flag is only reset at
        // depth 1, and with matexit DISABLED the inner pass cannot
        // re-set it — a stale TRUE plus a pathology the scanner also
        // flags in the DISABLED shape re-armed this branch at every
        // level (jdk26 ConcurrentLinkedQueue.poll recursed to the
        // depth-64 bail, the method emitted as a comment stub —
        // 缺少返回语句). One retry means one retry.
        let fired_saved = crate::sese::MATEXIT_FIRED.with(|f| f.replace(false));
        let retry = decompile_method(pc, pool, m_idx);
        crate::sese::MATEXIT_FIRED.with(|f| f.set(fired_saved));
        crate::sese::MATEXIT_DISABLED.with(|d| d.set(false));
        return retry;
    }
    Ok(Some(MethodBody { body, vt, desc }))
}

/// Safety net: any non-parameter local that is referenced but never declared
/// gets a bare declaration at the top of the method body.
fn ensure_declared(vt: &VarTable, body: &mut Stmt) {
    let mut declared: std::collections::HashSet<u32> = std::collections::HashSet::new();
    let mut used: std::collections::HashSet<u32> = std::collections::HashSet::new();
    collect_decl_use(body, &mut declared, &mut used);
    let mut missing: Vec<u32> = used.difference(&declared).copied().collect();
    missing.retain(|v| {
        let info = vt.var(*v);
        !info.is_param
    });
    let _ = &mut missing;
    if std::env::var("JCDC_DBG_HOIST").is_ok() {
        eprintln!("ENSURE missing={:?} declared={} used={}", missing, declared.len(), used.len());
    }
    if missing.is_empty() {
        return;
    }
    missing.sort_unstable();
    let decls: Vec<Stmt> = missing
        .into_iter()
        .map(|v| Stmt::LocalDef {
            var: v,
            init: if captured_by_anon(body, v) && !assigns_null_to(body, v) {
                None
            } else {
                default_init_for(vt, v)
            },
            is_final: false,
            force_type: true,
        })
        .collect();
    prepend_decls(body, decls);
}

fn collect_decl_use(s: &Stmt, declared: &mut std::collections::HashSet<u32>, used: &mut std::collections::HashSet<u32>) {
    match s {
        Stmt::Block(v) => v.iter().for_each(|x| collect_decl_use(x, declared, used)),
        Stmt::ExprStmt(e) => expr_uses(e, used),
        Stmt::LocalDef { var, init, .. } => {
            declared.insert(*var);
            used.insert(*var);
            if let Some(e) = init {
                expr_uses(e, used);
            }
        }
        Stmt::Return(e) => {
            if let Some(x) = e {
                expr_uses(x, used);
            }
        }
        Stmt::Throw(e) => expr_uses(e, used),
        Stmt::If { cond, then_stmt, else_stmt } => {
            expr_uses(cond, used);
            collect_decl_use(then_stmt, declared, used);
            if let Some(x) = else_stmt {
                collect_decl_use(x, declared, used);
            }
        }
        Stmt::While { cond, body } => {
            expr_uses(cond, used);
            collect_decl_use(body, declared, used);
        }
        Stmt::DoWhile { body, cond } => {
            collect_decl_use(body, declared, used);
            expr_uses(cond, used);
        }
        Stmt::For { init, cond, update, body } => {
            init.iter().for_each(|i| collect_decl_use(i, declared, used));
            if let Some(c) = cond {
                expr_uses(c, used);
            }
            update.iter().for_each(|u| expr_uses(u, used));
            collect_decl_use(body, declared, used);
        }
        Stmt::ForEach { var, iterable, body, .. } => {
            declared.insert(*var);
            used.insert(*var);
            expr_uses(iterable, used);
            collect_decl_use(body, declared, used);
        }
        Stmt::Switch { selector, cases, default, .. } => {
            expr_uses(selector, used);
            for c in cases {
                c.body.iter().for_each(|st| collect_decl_use(st, declared, used));
            }
            if let Some(d) = default {
                collect_decl_use(d, declared, used);
            }
        }
        Stmt::Try { body, catches, finally } => {
            collect_decl_use(body, declared, used);
            for c in catches {
                if c.var != u32::MAX {
                    declared.insert(c.var);
                }
                collect_decl_use(&c.body, declared, used);
            }
            if let Some(f) = finally {
                collect_decl_use(f, declared, used);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for r in resources {
                collect_decl_use(r, declared, used);
            }
            collect_decl_use(body, declared, used);
            for c in catches {
                if c.var != u32::MAX {
                    declared.insert(c.var);
                }
                collect_decl_use(&c.body, declared, used);
            }
            if let Some(f) = finally {
                collect_decl_use(f, declared, used);
            }
        }
        Stmt::Synchronized { lock, body } => {
            expr_uses(lock, used);
            collect_decl_use(body, declared, used);
        }
        // SESE wraps labelled loops in Labeled nodes: without this arm the
        // whole loop body is invisible to ensure_declared (jdk11
        // SynchronousQueue.TransferStack.transfer: m's 11 uses inside
        // `L1: while` went uncounted, its lost decl never re-added —
        // 找不到符号 变量 m x11).
        Stmt::Labeled { body, .. } => collect_decl_use(body, declared, used),
        Stmt::MonitorEnter(e) | Stmt::MonitorExit(e) => expr_uses(e, used),
        _ => {}
    }
}

fn expr_uses(e: &Expr, used: &mut std::collections::HashSet<u32>) {
    match e {
        Expr::Local { var, .. } => {
            used.insert(*var);
        }
        Expr::Const(_) | Expr::This | Expr::Raw(_) | Expr::RawT(..) => {}
        Expr::New { args, .. } | Expr::AnonNew { args, .. } => args.iter().for_each(|a| expr_uses(a, used)),
        Expr::NewArray { dims, init, .. } => {
            dims.iter().for_each(|d| expr_uses(d, used));
            if let Some(vals) = init {
                vals.iter().for_each(|v| expr_uses(v, used));
            }
        }
        Expr::NewMultiArray { dims, .. } => dims.iter().for_each(|d| expr_uses(d, used)),
        Expr::Field { owner: Some(o), .. } => expr_uses(o, used),
        Expr::Field { .. } => {}
        Expr::Method { owner, args, .. } => {
            if let Some(o) = owner {
                expr_uses(o, used);
            }
            args.iter().for_each(|a| expr_uses(a, used));
        }
        Expr::ArrayIndex { array, index } => {
            expr_uses(array, used);
            expr_uses(index, used);
        }
        Expr::Cast { e, .. } | Expr::InstanceOf { e, .. } | Expr::Un { e, .. } => expr_uses(e, used),
        Expr::Bin { l, r, .. } => {
            expr_uses(l, used);
            expr_uses(r, used);
        }
        Expr::Cond { c, t, f } => {
            expr_uses(c, used);
            expr_uses(t, used);
            expr_uses(f, used);
        }
        Expr::Assign { target, value, .. } => {
            expr_uses(target, used);
            expr_uses(value, used);
        }
        Expr::PreIncDec { e, .. } | Expr::PostIncDec { e, .. } => expr_uses(e, used),
        Expr::Lambda(l) => l.captures.iter().for_each(|c| expr_uses(c, used)),
        Expr::StringConcat(parts) => parts.iter().for_each(|p| {
            if let crate::expr::ConcatPart::Str(inner) = p {
                expr_uses(inner, used);
            }
        }),
        Expr::Invokedynamic { args, .. } => args.iter().for_each(|a| expr_uses(a, used)),
    }
}

/// Drop dead stores/declarations of SYNTHETIC gap temps: the
/// monitorenter store of `synchronized` lands in a slot the block body
/// reuses for a real local, and the gap temp inherits that local's type
/// (jdk11 SecurityManager.checkPackageDefinition `String[] var3_42 =
/// packageDefinitionLock;`, KeepAliveCache `Iterator var2_14 = this;`,
/// AbstractSelectableChannel `SelectionKey[] var2_11 = keyLock` —
/// X无法转换为Y x3). The monitor value is never loaded back, so the
/// store is dead; only prune when the temp has no reads anywhere.
fn prune_dead_synth_stores(s: &mut Stmt, vt: &VarTable) {
    use std::collections::HashSet;
    fn collect_expr_reads(e: &Expr, read: &mut HashSet<u32>) {
        match e {
            Expr::Local { var, .. } => {
                read.insert(*var);
            }
            Expr::Assign { target, value, op } => {
                match target.as_ref() {
                    // A plain local store does not read its target;
                    // compound ops and array/field stores read.
                    Expr::Local { .. } if *op == crate::expr::AssignOp::Plain => {}
                    other => collect_expr_reads(other, read),
                }
                collect_expr_reads(value, read);
            }
            other => expr_uses(other, read),
        }
    }
    fn collect_stmt_reads(s: &Stmt, read: &mut HashSet<u32>) {
        match s {
            Stmt::Block(v) => v.iter().for_each(|x| collect_stmt_reads(x, read)),
            Stmt::ExprStmt(e) => collect_expr_reads(e, read),
            Stmt::LocalDef { init, .. } => {
                if let Some(e) = init {
                    collect_expr_reads(e, read);
                }
            }
            Stmt::Return(e) => {
                if let Some(x) = e {
                    collect_expr_reads(x, read);
                }
            }
            Stmt::Throw(e) => collect_expr_reads(e, read),
            Stmt::If { cond, then_stmt, else_stmt } => {
                collect_expr_reads(cond, read);
                collect_stmt_reads(then_stmt, read);
                if let Some(x) = else_stmt {
                    collect_stmt_reads(x, read);
                }
            }
            Stmt::While { cond, body } => {
                collect_expr_reads(cond, read);
                collect_stmt_reads(body, read);
            }
            Stmt::DoWhile { body, cond } => {
                collect_stmt_reads(body, read);
                collect_expr_reads(cond, read);
            }
            Stmt::For { init, cond, update, body } => {
                init.iter().for_each(|x| collect_stmt_reads(x, read));
                if let Some(c) = cond {
                    collect_expr_reads(c, read);
                }
                update.iter().for_each(|u| collect_expr_reads(u, read));
                collect_stmt_reads(body, read);
            }
            Stmt::ForEach { var, iterable, body, .. } => {
                read.insert(*var);
                collect_expr_reads(iterable, read);
                collect_stmt_reads(body, read);
            }
            Stmt::Switch { selector, cases, default, .. } => {
                collect_expr_reads(selector, read);
                for c in cases {
                    c.body.iter().for_each(|st| collect_stmt_reads(st, read));
                }
                if let Some(d) = default {
                    collect_stmt_reads(d, read);
                }
            }
            Stmt::Try { body, catches, finally } => {
                collect_stmt_reads(body, read);
                for c in catches {
                    if c.var != u32::MAX {
                        read.insert(c.var);
                    }
                    collect_stmt_reads(&c.body, read);
                }
                if let Some(f) = finally {
                    collect_stmt_reads(f, read);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                resources.iter().for_each(|x| collect_stmt_reads(x, read));
                collect_stmt_reads(body, read);
                for c in catches {
                    if c.var != u32::MAX {
                        read.insert(c.var);
                    }
                    collect_stmt_reads(&c.body, read);
                }
                if let Some(f) = finally {
                    collect_stmt_reads(f, read);
                }
            }
            Stmt::Synchronized { lock, body } => {
                collect_expr_reads(lock, read);
                collect_stmt_reads(body, read);
            }
            Stmt::MonitorEnter(e) | Stmt::MonitorExit(e) => collect_expr_reads(e, read),
            Stmt::Labeled { body, .. } => collect_stmt_reads(body, read),
            _ => {}
        }
    }
    fn is_cand(s: &Stmt, vt: &VarTable) -> Option<u32> {
        let var = match s {
            Stmt::ExprStmt(Expr::Assign { target, op: crate::expr::AssignOp::Plain, .. }) => {
                match target.as_ref() {
                    Expr::Local { var, .. } => *var,
                    _ => return None,
                }
            }
            Stmt::LocalDef { var, .. } => *var,
            _ => return None,
        };
        let info = vt.var(var);
        if info.synthetic_name && !info.is_param {
            Some(var)
        } else {
            None
        }
    }
    let mut read: HashSet<u32> = HashSet::new();
    collect_stmt_reads(&*s, &mut read);
    // A dead store whose VALUE has real effects must not vanish with the
    // variable: `Class<?> c = Class.forName("jdk.net.ExtendedSocketOptions");`
    // in the jdk11 ExtendedSocketOptions clinit is never read, but dropping
    // the call skips the class-init trigger AND leaves the surrounding try
    // body empty -- javac then rejects the checked-exception catch (在相应的
    // try 语句主体中不能抛出异常错误ClassNotFoundException). Demote such
    // statements to bare expression statements. Only top-level Java
    // statement expressions qualify (call / new / assign / inc-dec); a dead
    // store of a plain field or local read (the monitor-store shapes this
    // pass exists for) stays fully dropped -- a bare field read is not a
    // valid statement expression.
    fn demote_value(e: &Expr) -> Option<Expr> {
        match e {
            Expr::Method { .. }
            | Expr::New { .. }
            | Expr::AnonNew { .. }
            | Expr::Assign { .. }
            | Expr::PreIncDec { .. }
            | Expr::PostIncDec { .. } => Some(e.clone()),
            _ => None,
        }
    }
    fn cand_demote(s: &Stmt) -> Option<Expr> {
        match s {
            Stmt::ExprStmt(Expr::Assign { value, op: crate::expr::AssignOp::Plain, .. }) => {
                demote_value(value)
            }
            Stmt::LocalDef { init: Some(e), .. } => demote_value(e),
            _ => None,
        }
    }
    fn prune(s: &mut Stmt, vt: &VarTable, read: &HashSet<u32>) {
        match s {
            Stmt::Block(v) => {
                let mut i = 0;
                while i < v.len() {
                    match is_cand(&v[i], vt) {
                        Some(var) if !read.contains(&var) => {
                            match cand_demote(&v[i]) {
                                Some(e) => {
                                    v[i] = Stmt::ExprStmt(e);
                                    i += 1;
                                }
                                None => {
                                    v.remove(i);
                                }
                            }
                        }
                        _ => i += 1,
                    }
                }
                v.iter_mut().for_each(|x| prune(x, vt, read));
            }
            Stmt::If { then_stmt, else_stmt, .. } => {
                prune(then_stmt, vt, read);
                if let Some(x) = else_stmt {
                    prune(x, vt, read);
                }
            }
            Stmt::While { body, .. }
            | Stmt::DoWhile { body, .. }
            | Stmt::ForEach { body, .. }
            | Stmt::Labeled { body, .. } => prune(body, vt, read),
            Stmt::For { init, body, .. } => {
                init.iter_mut().for_each(|x| prune(x, vt, read));
                prune(body, vt, read);
            }
            Stmt::Switch { cases, default, .. } => {
                for c in cases.iter_mut() {
                    let mut i = 0;
                    while i < c.body.len() {
                        let dead = match is_cand(&c.body[i], vt) {
                            Some(var) => !read.contains(&var),
                            None => false,
                        };
                        if dead {
                            match cand_demote(&c.body[i]) {
                                Some(e) => {
                                    c.body[i] = Stmt::ExprStmt(e);
                                    i += 1;
                                }
                                None => {
                                    c.body.remove(i);
                                }
                            }
                        } else {
                            prune(&mut c.body[i], vt, read);
                            i += 1;
                        }
                    }
                }
                if let Some(d) = default {
                    prune(d, vt, read);
                }
            }
            Stmt::Try { body, catches, finally } => {
                prune(body, vt, read);
                for c in catches.iter_mut() {
                    prune(&mut c.body, vt, read);
                }
                if let Some(f) = finally {
                    prune(f, vt, read);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                resources.iter_mut().for_each(|x| prune(x, vt, read));
                prune(body, vt, read);
                for c in catches.iter_mut() {
                    prune(&mut c.body, vt, read);
                }
                if let Some(f) = finally {
                    prune(f, vt, read);
                }
            }
            Stmt::Synchronized { body, .. } => prune(body, vt, read),
            _ => {}
        }
    }
    prune(s, vt, &read);
}

/// Scope-aware deduplication: a variable already declared in an enclosing
/// open scope gets plain assignments instead of re-declarations. Sibling
/// scopes may each declare (legal Java).
/// Erasure checkcasts that source generics make redundant: a call
/// whose methodref owner redeclares the method with a self-covariant
/// return (Stream overrides BaseStream.onClose to return Stream) is
/// followed by javac's `checkcast Owner` because the descriptor return
/// is the erased supertype. Printing that cast RAW poisons the whole
/// generic chain downstream (jdk17 Files.find: `((Stream) stream(..)
/// .onClose(..)).filter(entry -> entry.file())` — entry became Object).
/// Drop the cast when it targets exactly the methodref owner class.
fn strip_selftype_checkcasts(body: &mut Stmt, pool: &ClassPool) {
    fn self_covariant(cls: &str, name: &str, pool: &ClassPool) -> bool {
        // The source-level return of `recv.name(..)` is the receiver's own
        // type when the declaring method's generic return is a self-bounded
        // type variable (BaseStream<T, S extends BaseStream<T,S>>.onClose()
        // returns S := Stream<Path>) or the owner class redeclares it with
        // a self return. Walk supers AND interfaces to find the declaration.
        let want = format!("L{};", cls);
        let mut queue: Vec<String> = vec![cls.to_string()];
        let mut seen: HashSet<String> = HashSet::new();
        let mut depth = 0;
        while let Some(c) = queue.pop() {
            if depth > 64 || !seen.insert(c.clone()) {
                continue;
            }
            depth += 1;
            let Some(cpc) = pool.get(&c) else { continue };
            for mi in 0..cpc.cf.methods.len() {
                if cpc.method_name(mi) != Some(name) {
                    continue;
                }
                if cpc
                    .method_desc(mi)
                    .map(|d| d.ends_with(&format!("){}", want)))
                    .unwrap_or(false)
                {
                    return true;
                }
                let sig_ret_is_typevar = cpc.cf.methods[mi].attributes.iter().any(|a| {
                    cpc.utf8(a.attribute_name_index) == Some("Signature")
                        && a.info.len() >= 2
                        && cpc
                            .utf8(u16::from_be_bytes([a.info[0], a.info[1]]))
                            .and_then(|x| jcdc_jvm::parse_method_signature(x))
                            .map(|sig| matches!(sig.ret, jcdc_jvm::GenericType::TypeVar(_)))
                            .unwrap_or(false)
                });
                if sig_ret_is_typevar && c != cls {
                    // Declared on a supertype with a generic (self-bounded)
                    // return: the checkcast to the receiver class is the
                    // erasure artifact.
                    return true;
                }
            }
            if let Some(sup) = cpc.super_name() {
                queue.push(sup.to_string());
            }
            for &ii in &cpc.cf.interfaces {
                if let Some(n) = cpc.class_name(ii) {
                    queue.push(n.to_string());
                }
            }
        }
        false
    }
    fn fix_expr(e: &mut Expr, pool: &ClassPool) {
        if let Expr::Cast { ty, e: inner } = e {
            let dominated = match (&**inner, ty) {
                (Expr::Method { cls, name, desc, .. }, TypeRef::J(JavaType::Object(x))) => {
                    x == cls
                        && desc.ret != JavaType::Object(cls.clone())
                        && self_covariant(cls, name, pool)
                }
                _ => false,
            };
            if dominated {
                let inner = std::mem::replace(inner.as_mut(), Expr::This);
                *e = inner;
            }
        }
        fix_children(e, pool);
    }
    fn fix_children(e: &mut Expr, pool: &ClassPool) {
        match e {
            Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
                args.iter_mut().for_each(|a| fix_expr(a, pool));
            }
            Expr::Method { owner, args, .. } => {
                if let Some(o) = owner {
                    fix_expr(o, pool);
                }
                args.iter_mut().for_each(|a| fix_expr(a, pool));
            }
            Expr::Field { owner: Some(o), .. } => fix_expr(o, pool),
            Expr::ArrayIndex { array, index } => {
                fix_expr(array, pool);
                fix_expr(index, pool);
            }
            Expr::Cast { e: i, .. }
            | Expr::InstanceOf { e: i, .. }
            | Expr::Un { e: i, .. }
            | Expr::PreIncDec { e: i, .. }
            | Expr::PostIncDec { e: i, .. } => fix_expr(i, pool),
            Expr::Bin { l, r, .. } => {
                fix_expr(l, pool);
                fix_expr(r, pool);
            }
            Expr::Cond { c, t, f } => {
                fix_expr(c, pool);
                fix_expr(t, pool);
                fix_expr(f, pool);
            }
            Expr::Assign { target, value, .. } => {
                fix_expr(target, pool);
                fix_expr(value, pool);
            }
            Expr::NewArray { dims, init, .. } => {
                dims.iter_mut().for_each(|d| fix_expr(d, pool));
                if let Some(vals) = init {
                    vals.iter_mut().for_each(|x| fix_expr(x, pool));
                }
            }
            Expr::NewMultiArray { dims, .. } => dims.iter_mut().for_each(|d| fix_expr(d, pool)),
            Expr::StringConcat(parts) => parts.iter_mut().for_each(|pp| {
                if let crate::expr::ConcatPart::Str(i) = pp {
                    fix_expr(i, pool);
                }
            }),
            Expr::Lambda(l) => l.captures.iter_mut().for_each(|c| fix_expr(c, pool)),
            Expr::Invokedynamic { args, .. } => args.iter_mut().for_each(|a| fix_expr(a, pool)),
            _ => {}
        }
    }
    fn rec(s: &mut Stmt, pool: &ClassPool) {
        match s {
            Stmt::Block(v) => v.iter_mut().for_each(|x| rec(x, pool)),
            Stmt::ExprStmt(e) => fix_expr(e, pool),
            Stmt::LocalDef { init: Some(e), .. } => fix_expr(e, pool),
            Stmt::Return(Some(e)) | Stmt::Throw(e) => fix_expr(e, pool),
            Stmt::If { cond, then_stmt, else_stmt } => {
                fix_expr(cond, pool);
                rec(then_stmt, pool);
                if let Some(e) = else_stmt {
                    rec(e, pool);
                }
            }
            Stmt::While { cond, body } => {
                fix_expr(cond, pool);
                rec(body, pool);
            }
            Stmt::DoWhile { body, cond } => {
                rec(body, pool);
                fix_expr(cond, pool);
            }
            Stmt::For { init, cond, update, body } => {
                init.iter_mut().for_each(|i| rec(i, pool));
                if let Some(c) = cond {
                    fix_expr(c, pool);
                }
                update.iter_mut().for_each(|u| fix_expr(u, pool));
                rec(body, pool);
            }
            Stmt::ForEach { iterable, body, .. } => {
                fix_expr(iterable, pool);
                rec(body, pool);
            }
            Stmt::Switch { selector, cases, default, .. } => {
                fix_expr(selector, pool);
                for c in cases.iter_mut() {
                    c.body.iter_mut().for_each(|st| rec(st, pool));
                }
                if let Some(d) = default {
                    rec(d, pool);
                }
            }
            Stmt::Try { body, catches, finally } => {
                rec(body, pool);
                for c in catches.iter_mut() {
                    rec(&mut c.body, pool);
                }
                if let Some(f) = finally {
                    rec(f, pool);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                resources.iter_mut().for_each(|r| rec(r, pool));
                rec(body, pool);
                for c in catches.iter_mut() {
                    rec(&mut c.body, pool);
                }
                if let Some(f) = finally {
                    rec(f, pool);
                }
            }
            Stmt::Synchronized { lock, body } => {
                fix_expr(lock, pool);
                rec(body, pool);
            }
            Stmt::Labeled { body, .. } => rec(body, pool),
            Stmt::Assert { cond, msg } => {
                fix_expr(cond, pool);
                if let Some(m) = msg {
                    fix_expr(m, pool);
                }
            }
            Stmt::TernaryValue { e } => fix_expr(e, pool),
            Stmt::MonitorEnter(e) | Stmt::MonitorExit(e) => fix_expr(e, pool),
            _ => {}
        }
    }
    rec(body, pool);
}

/// `new C` values that reached an `invokespecial C.<init>` through
/// stack-merge variables (branch-duplicated news): fold the init args
/// back into the raw new assignments and drop the bare super(..)
/// statement. Outside a constructor a Method{<init>} on a non-this
/// owner can never be a real super call — it is always a merged new's
/// initializer (jdk17 InflaterInputStream read(): `stack231 = new
/// ZipException(); super(stack233); throw stack231;` — "显式构造器调用
/// 只能出现在构造器主体中" + the message never reached the exception).
fn fold_merged_new_inits(body: &mut Stmt, pc: &PoolClass) {
    let mut inits: Vec<(u32, String, Vec<Expr>)> = Vec::new();
    fn find_inits(s: &Stmt, pc: &PoolClass, out: &mut Vec<(u32, String, Vec<Expr>)>) {
        match s {
            Stmt::ExprStmt(Expr::Method { name, cls, owner, args, .. })
                if name == "<init>" && cls != &pc.internal_name =>
            {
                if let Some(o) = owner {
                    if let Expr::Local { var, .. } = &**o {
                        out.push((*var, cls.clone(), args.clone()));
                    }
                }
            }
            Stmt::Block(v) => v.iter().for_each(|x| find_inits(x, pc, out)),
            Stmt::If { then_stmt, else_stmt, .. } => {
                find_inits(then_stmt, pc, out);
                if let Some(e) = else_stmt {
                    find_inits(e, pc, out);
                }
            }
            Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => find_inits(body, pc, out),
            Stmt::For { init, body, .. } => {
                init.iter().for_each(|x| find_inits(x, pc, out));
                find_inits(body, pc, out);
            }
            Stmt::ForEach { body, .. } => find_inits(body, pc, out),
            Stmt::Labeled { body, .. } | Stmt::Synchronized { body, .. } => {
                find_inits(body, pc, out);
            }
            Stmt::Switch { cases, default, .. } => {
                for c in cases {
                    c.body.iter().for_each(|x| find_inits(x, pc, out));
                }
                if let Some(d) = default {
                    find_inits(d, pc, out);
                }
            }
            Stmt::Try { body, catches, finally } => {
                find_inits(body, pc, out);
                for c in catches {
                    find_inits(&c.body, pc, out);
                }
                if let Some(f) = finally {
                    find_inits(f, pc, out);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                resources.iter().for_each(|x| find_inits(x, pc, out));
                find_inits(body, pc, out);
                for c in catches {
                    find_inits(&c.body, pc, out);
                }
                if let Some(f) = finally {
                    find_inits(f, pc, out);
                }
            }
            _ => {}
        }
    }
    find_inits(body, pc, &mut inits);
    if inits.is_empty() {
        return;
    }
    fn rewrite(s: &mut Stmt, inits: &[(u32, String, Vec<Expr>)], pc: &PoolClass) {
        match s {
            Stmt::Block(v) => {
                // Raw `v = new C()` assignments in this block whose class
                // has a merged init later: the initialized value is
                // assigned at the INIT site instead; the raw twin store
                // is dead (its object is never observed).
                let dead: std::collections::HashSet<u32> = v
                    .iter()
                    .filter_map(|st| match st {
                        Stmt::ExprStmt(Expr::Assign { target, value, .. }) => {
                            match (&**target, &**value) {
                                (Expr::Local { var, .. }, Expr::New { cls, raw: true, .. })
                                    if inits.iter().any(|(_, c, _)| c == cls) =>
                                {
                                    Some(*var)
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    })
                    .collect();
                if !dead.is_empty() {
                    v.retain(|st| {
                        !matches!(st, Stmt::ExprStmt(Expr::Assign { target, .. })
                            if matches!(&**target, Expr::Local { var, .. } if dead.contains(var)))
                    });
                }
                let mut i = 0;
                while i < v.len() {
                    let folded = match &v[i] {
                        Stmt::ExprStmt(Expr::Method { name, cls, owner, args, .. })
                            if name == "<init>" && cls != &pc.internal_name =>
                        {
                            match owner.as_deref() {
                                Some(Expr::Local { var, ty }) => {
                                    let var = *var;
                                    let ty = ty.clone();
                                    inits.iter().find(|(v2, c2, _)| *v2 == var && c2 == cls).map(
                                        |(_, _, iargs)| {
                                            let mut stmts = vec![Stmt::ExprStmt(Expr::Assign {
                                                target: Box::new(Expr::Local { var, ty: ty.clone() }),
                                                op: crate::expr::AssignOp::Plain,
                                                value: Box::new(Expr::New {
                                                    cls: cls.clone(),
                                                    ty: crate::expr::TypeRef::J(
                                                        jcdc_jvm::JavaType::Object(cls.clone()),
                                                    ),
                                                    args: iargs.clone(),
                                                    raw: false,
                                                }),
                                            })];
                                            // DUP twins: point every other
                                            // raw-new var of the same class
                                            // (the dead raw assigns removed
                                            // above) at the initialized
                                            // object — the throw/return flow
                                            // reads a twin.
                                            for &tv in dead.iter() {
                                                if tv != var {
                                                    stmts.push(Stmt::ExprStmt(Expr::Assign {
                                                        target: Box::new(Expr::Local {
                                                            var: tv,
                                                            ty: ty.clone(),
                                                        }),
                                                        op: crate::expr::AssignOp::Plain,
                                                        value: Box::new(Expr::Local {
                                                            var,
                                                            ty: ty.clone(),
                                                        }),
                                                    }));
                                                }
                                            }
                                            Stmt::Block(stmts)
                                        },
                                    )
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    };
                    if let Some(f) = folded {
                        v[i] = f;
                    } else {
                        rewrite(&mut v[i], inits, pc);
                    }
                    i += 1;
                }
                v.retain(|x| !x.is_empty_block());
            }
            Stmt::If { then_stmt, else_stmt, .. } => {
                rewrite(then_stmt, inits, pc);
                if let Some(e) = else_stmt {
                    rewrite(e, inits, pc);
                }
            }
            Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => rewrite(body, inits, pc),
            Stmt::For { init, body, .. } => {
                init.iter_mut().for_each(|x| rewrite(x, inits, pc));
                rewrite(body, inits, pc);
            }
            Stmt::ForEach { body, .. } => rewrite(body, inits, pc),
            Stmt::Labeled { body, .. } | Stmt::Synchronized { body, .. } => {
                rewrite(body, inits, pc);
            }
            Stmt::Switch { cases, default, .. } => {
                for c in cases.iter_mut() {
                    for x in c.body.iter_mut() {
                        rewrite(x, inits, pc);
                    }
                }
                if let Some(d) = default {
                    rewrite(d, inits, pc);
                }
            }
            Stmt::Try { body, catches, finally } => {
                rewrite(body, inits, pc);
                for c in catches.iter_mut() {
                    rewrite(&mut c.body, inits, pc);
                }
                if let Some(f) = finally {
                    rewrite(f, inits, pc);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                for r in resources.iter_mut() {
                    rewrite(r, inits, pc);
                }
                rewrite(body, inits, pc);
                for c in catches.iter_mut() {
                    rewrite(&mut c.body, inits, pc);
                }
                if let Some(f) = finally {
                    rewrite(f, inits, pc);
                }
            }
            _ => {}
        }
    }
    rewrite(body, &inits, pc);
}
fn dedupe_declarations(body: &mut Stmt) {
    let mut scopes: Vec<std::collections::HashSet<u32>> = Vec::new();
    scopes.push(std::collections::HashSet::new());
    dedupe_walk(body, &mut scopes);
}

fn in_scope(scopes: &[std::collections::HashSet<u32>], v: u32) -> bool {
    scopes.iter().any(|s| s.contains(&v))
}

fn dedupe_walk(s: &mut Stmt, scopes: &mut Vec<std::collections::HashSet<u32>>) {
    match s {
        Stmt::LocalDef { var, init, .. } => {
            if in_scope(scopes, *var) {
                match init.take() {
                    Some(e) => {
                        *s = Stmt::ExprStmt(Expr::Assign {
                            target: Box::new(Expr::Local {
                                var: *var,
                                ty: crate::expr::TypeRef::J(jcdc_jvm::JavaType::Int),
                            }),
                            op: crate::expr::AssignOp::Plain,
                            value: Box::new(e),
                        });
                    }
                    None => *s = Stmt::Block(vec![]),
                }
            } else {
                scopes.last_mut().unwrap().insert(*var);
            }
        }
        Stmt::Block(v) => {
            scopes.push(std::collections::HashSet::new());
            for x in v.iter_mut() {
                dedupe_walk(x, scopes);
            }
            scopes.pop();
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            dedupe_walk(then_stmt, scopes);
            if let Some(e) = else_stmt {
                dedupe_walk(e, scopes);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => dedupe_walk(body, scopes),
        Stmt::For { init, body, .. } => {
            scopes.push(std::collections::HashSet::new());
            init.iter_mut().for_each(|i| dedupe_walk(i, scopes));
            dedupe_walk(body, scopes);
            scopes.pop();
        }
        Stmt::ForEach { var, body, .. } => {
            scopes.push(std::collections::HashSet::new());
            scopes.last_mut().unwrap().insert(*var);
            dedupe_walk(body, scopes);
            scopes.pop();
        }
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                scopes.push(std::collections::HashSet::new());
                c.body.iter_mut().for_each(|st| dedupe_walk(st, scopes));
                scopes.pop();
            }
            if let Some(d) = default {
                dedupe_walk(d, scopes);
            }
        }
        Stmt::Try { body, catches, finally } => {
            dedupe_walk(body, scopes);
            for c in catches {
                scopes.push(std::collections::HashSet::new());
                if c.var != u32::MAX {
                    scopes.last_mut().unwrap().insert(c.var);
                }
                dedupe_walk(&mut c.body, scopes);
                scopes.pop();
            }
            if let Some(f) = finally {
                dedupe_walk(f, scopes);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            scopes.push(std::collections::HashSet::new());
            for r in resources.iter_mut() {
                dedupe_walk(r, scopes);
            }
            dedupe_walk(body, scopes);
            for c in catches {
                scopes.push(std::collections::HashSet::new());
                if c.var != u32::MAX {
                    scopes.last_mut().unwrap().insert(c.var);
                }
                dedupe_walk(&mut c.body, scopes);
                scopes.pop();
            }
            if let Some(f) = finally {
                dedupe_walk(f, scopes);
            }
            scopes.pop();
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => dedupe_walk(body, scopes),
        _ => {}
    }
}

/// Decide pure value-diamond folding for a divergent 2-pred merge using the
/// previous round's block results (terms and purity are stable across rounds
/// for javac-style code).
fn try_diamond_fold(
    bid: usize,
    known: &[(usize, Vec<Expr>)],
    prev_out: &[Option<Vec<Expr>>],
    results: &[BlockResult],
    cfg: &Cfg,
    dom: &crate::structure::DomInfo,
) -> Option<(Vec<Expr>, usize, HashSet<usize>)> {
    let _ = prev_out;
    if known.len() < 2 {
        return None;
    }
    // Every direct predecessor must be a pure value block feeding the merge.
    for (p, _) in known {
        let pure = results[*p].stmts.is_empty()
            && !matches!(
                results[*p].term,
                crate::builder::Term::Return(_) | crate::builder::Term::Throw(_)
            )
            && cfg.blocks[*p].succ.first() == Some(&bid);
        if !pure {
            if std::env::var("JCDC_DBG_DIAMOND").is_ok() {
                eprintln!("fold REJECT merge {}: pred {} not pure", bid, p);
            }
            return None;
        }
    }
    // Common carried prefix; each pred contributes exactly one new value.
    let outs: Vec<&Vec<Expr>> = known.iter().map(|(_, o)| o).collect();
    let minlen = outs.iter().map(|o| o.len()).min()?;
    let mut k = 0;
    'prefix: while k < minlen {
        let e = &outs[0][k];
        for o in &outs[1..] {
            if o[k] != *e {
                break 'prefix;
            }
        }
        k += 1;
    }
    for o in &outs {
        if o.len() - k != 1 {
            if std::env::var("JCDC_DBG_DIAMOND").is_ok() {
                eprintln!("fold REJECT merge {}: suffix len {} after common {}", bid, o.len() - k, k);
            }
            return None;
        }
    }
    let prefix = outs[0][..k].to_vec();
    let leaf_val: HashMap<usize, Expr> = known
        .iter()
        .map(|(p, o)| (*p, o[k].clone()))
        .collect();

    // Find the cond header whose branches resolve (through pure chains and
    // nested cond headers) to exactly the leaf set. Chained diamonds like
    // `a && b` fold recursively into nested ternaries.
    fn resolve(
        x: usize,
        bid: usize,
        leaf_val: &HashMap<usize, Expr>,
        results: &[BlockResult],
        cfg: &Cfg,
        dom: &crate::structure::DomInfo,
        depth: usize,
        vis: &mut HashSet<usize>,
        memo: &mut HashMap<usize, Expr>,
    ) -> Option<Expr> {
        if let Some(v) = leaf_val.get(&x) {
            vis.insert(x);
            return Some(v.clone());
        }
        if let Some(v) = memo.get(&x) {
            vis.insert(x);
            return Some(v.clone());
        }
        if depth > 16 || !vis.insert(x) {
            return None;
        }
        match &results[x].term {
            crate::builder::Term::Cond { cond } if cfg.blocks[x].succ.len() == 2 => {
                let t = cfg.blocks[x].succ[1];
                let f = cfg.blocks[x].succ[0];
                let te = resolve(t, bid, leaf_val, results, cfg, dom, depth + 1, vis, memo)?;
                let fe = resolve(f, bid, leaf_val, results, cfg, dom, depth + 1, vis, memo)?;
                let e = Expr::Cond {
                    c: Box::new(cond.clone()),
                    t: Box::new(te),
                    f: Box::new(fe),
                };
                memo.insert(x, e.clone());
                Some(e)
            }
            crate::builder::Term::Fallthrough | crate::builder::Term::Goto
                if results[x].stmts.is_empty()
                    && results[x].out_stack.is_empty()
                    && cfg.blocks[x].succ.len() == 1 =>
            {
                // Transparent chain block (e.g. an empty goto trampoline).
                let n = cfg.blocks[x].succ[0];
                if n == bid {
                    return None;
                }
                resolve(n, bid, leaf_val, results, cfg, dom, depth + 1, vis, memo)
            }
            _ => {
                if std::env::var("JCDC_DBG_DIAMOND").is_ok() {
                    eprintln!("  resolve fail x={} term={:?} succ={:?}", x, std::mem::discriminant(&results[x].term), cfg.blocks[x].succ);
                }
                None
            }
        }
    }

    // Candidate roots in reverse-postorder; the merge's immediate postdom
    // relationship is irrelevant here — we need the header that routes ALL
    // leaves. Prefer the latest dominator of the leaves (smallest region).
    let n = cfg.blocks.len();
    let universe: HashSet<usize> = (0..n).collect();
    let rpo = crate::structure::reverse_postorder(cfg, cfg.entry, &universe);
    if std::env::var("JCDC_DBG_DIAMOND").is_ok() {
        eprintln!("fold merge {} rpo={:?}", bid, rpo);
    }
    let leaves: Vec<usize> = known.iter().map(|(p, _)| *p).collect();
    let dbg = std::env::var("JCDC_DBG_DIAMOND").is_ok();
    let mut best: Option<(usize, Expr, HashSet<usize>)> = None;
    for &h in rpo.iter().rev() {
        if !matches!(results[h].term, crate::builder::Term::Cond { .. }) {
            continue;
        }
        if !leaves.iter().all(|&l| dom.dominates(h, l)) {
            if dbg { eprintln!("  root {} skipped: doesn't dominate leaves {:?}", h, leaves); }
            continue;
        }
        let mut vis = HashSet::new();
        let mut memo = HashMap::new();
        if let Some(e) = resolve(h, bid, &leaf_val, results, cfg, dom, 0, &mut vis, &mut memo) {
            // All leaves must be covered by this root's resolution, and the
            // resolved region must be single-entry: every block inside is
            // entered only from inside (plus the root itself). Otherwise a
            // bypass path would take the folded ternary without evaluating
            // the conditions.
            let single_entry = cfg.blocks.iter().all(|b| {
                b.id == h
                    || b.id == bid
                    || !vis.contains(&b.id)
                    || b.pred.iter().all(|p| vis.contains(p) || *p == h)
            });
            if dbg { eprintln!("  root {} resolve ok vis={:?} single_entry={} leaves_cov={}", h, vis, single_entry, leaves.iter().all(|l| vis.contains(l))); }
            // Intermediate blocks with statements (e.g. `x = (T) y;` before
            // a comparison) can only be folded away when no variable they
            // assign is referenced by the folded expression — otherwise
            // the assignment would silently vanish. The ROOT is exempt:
            // fold-collapse emits the root's own statements in place
            // (Region::Basic{root}) before the merge in BOTH structurizers,
            // so a root like `props = ...; JAVA_VERSION = ...; if (prop ==
            // null)` folds safely even though the condition references
            // `props`. Requiring the root to be statement-free rejected
            // every clinit-style diamond whose header block also performs
            // the setup assignments (jdk URLClassPath DEBUG/DISABLE_JAR_CHECKING:
            // fallback stack-vars typed int but consumed as boolean fields ->
            // uncompilable, plus a mis-structured `||` chain that always
            // stored 1 — a shared walk+SESE corpus blocker family).
            let mut assigned: HashSet<u32> = HashSet::new();
            for &b in &vis {
                if b == h {
                    continue;
                }
                for st in &results[b].stmts {
                    collect_assigned_vars(st, &mut assigned);
                }
            }
            let mut referenced: HashSet<u32> = HashSet::new();
            collect_expr_locals(&e, &mut referenced);
            let clean = assigned.is_disjoint(&referenced);
            if single_entry && clean && leaves.iter().all(|l| vis.contains(l)) {
                best = Some((h, e, vis.clone()));
                break;
            }
        }
    }
    let Some((root, folded_val, vis)) = best else {
        if std::env::var("JCDC_DBG_DIAMOND").is_ok() {
            eprintln!("fold REJECT merge {}: no resolving root", bid);
        }
        return None;
    };
    let mut folded = prefix;
    folded.push(folded_val);
    if std::env::var("JCDC_DBG_DIAMOND").is_ok() {
        eprintln!("fold OK merge {} depth {} root={} vis={:?}", bid, folded.len(), root, vis);
    }
    Some((folded, root, vis))
}

fn results_terms_placeholder(r: &[BlockResult]) -> &[BlockResult] {
    r
}

#[allow(dead_code)]
fn depth_of(known: &[(usize, Vec<Expr>)]) -> usize {
    known.iter().map(|(_, o)| o.len()).min().unwrap_or(0)
}

/// Remove `break;` statements that are immediately followed by the end of
/// their loop body (dead code, rejected by javac).
fn prune_dead_breaks(s: &mut Stmt) {
    let strippable = tail_break_strippable(s);
    match s {
        Stmt::Block(v) => {
            for x in v.iter_mut() {
                prune_dead_breaks(x);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => {
            prune_dead_breaks(body);
            if strippable {
                strip_tail_break(body);
            }
        }
        Stmt::For { body, .. } | Stmt::ForEach { body, .. } => {
            prune_dead_breaks(body);
            if strippable {
                strip_tail_break(body);
            }
        }
        Stmt::Labeled { body, .. } | Stmt::Synchronized { body, .. } => prune_dead_breaks(body),
        Stmt::If { then_stmt, else_stmt, .. } => {
            prune_dead_breaks(then_stmt);
            if let Some(e) = else_stmt {
                prune_dead_breaks(e);
            }
        }
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(prune_dead_breaks);
            }
            if let Some(d) = default {
                prune_dead_breaks(d);
            }
        }
        Stmt::Try { body, catches, finally } => {
            prune_dead_breaks(body);
            for c in catches {
                prune_dead_breaks(&mut c.body);
            }
            if let Some(f) = finally {
                prune_dead_breaks(f);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { prune_dead_breaks(res); }
            prune_dead_breaks(body);
            for c in catches {
                prune_dead_breaks(&mut c.body);
            }
            if let Some(f) = finally {
                prune_dead_breaks(f);
            }
        }
        _ => {}
    }
}

/// Truncate statement sequences after an unconditional terminator
/// (return/throw/break/continue) — javac rejects such unreachable code.
/// True when control cannot fall out of the end of `s` (children are
/// already pruned when this is consulted).
/// Conservative: does `s` contain ANY `break` statement (at any nesting)?
/// True when `s` contains a `break` that could complete the ENCLOSING
/// loop normally. JLS 14.21: an unlabeled break binds the INNERMOST
/// enclosing loop/switch — plain breaks nested inside a While/DoWhile/
/// For/ForEach/Switch body never escape the outer loop and must not
/// count (jdk26 Bits.reserveMemory: the inlined phase-2 do-while's own
/// `break` made the phase-1 while(true) look escapable, prune kept the
/// post-loop duplicate tail and javac flagged it 无法访问的语句).
/// LABELED breaks stay conservatively counted — without the enclosing
/// loop's label in scope we cannot tell whether they target it.
/// Synchronized/Labeled/If/Block/Try wrappers are transparent.
fn contains_break_stmt(s: &Stmt) -> bool {
    match s {
        Stmt::Break(_) => true,
        Stmt::Block(v) => v.iter().any(contains_break_stmt),
        Stmt::If { then_stmt, else_stmt, .. } => {
            contains_break_stmt(then_stmt)
                || else_stmt.as_deref().map(contains_break_stmt).unwrap_or(false)
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => {
            contains_break_stmt(body)
        }
        // Nested loop/switch bodies capture plain breaks; only labeled
        // breaks inside them could reach the enclosing loop.
        Stmt::While { body, .. }
        | Stmt::DoWhile { body, .. }
        | Stmt::ForEach { body, .. }
        | Stmt::For { body, .. } => contains_labeled_break(body),
        Stmt::Switch { cases, default, .. } => {
            cases
                .iter()
                .flat_map(|c| c.body.iter())
                .any(contains_labeled_break)
                || default.as_deref().map(contains_labeled_break).unwrap_or(false)
        }
        Stmt::Try { body, catches, finally } => {
            contains_break_stmt(body)
                || catches.iter().any(|c| contains_break_stmt(&c.body))
                || finally.as_deref().map(contains_break_stmt).unwrap_or(false)
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            resources.iter().any(contains_break_stmt)
                || contains_break_stmt(body)
                || catches.iter().any(|c| contains_break_stmt(&c.body))
                || finally.as_deref().map(contains_break_stmt).unwrap_or(false)
        }
        _ => false,
    }
}

/// Only LABELED breaks (which may target an enclosing construct).
fn contains_labeled_break(s: &Stmt) -> bool {
    match s {
        Stmt::Break(Some(_)) => true,
        Stmt::Break(None) => false,
        Stmt::Block(v) => v.iter().any(contains_labeled_break),
        Stmt::If { then_stmt, else_stmt, .. } => {
            contains_labeled_break(then_stmt)
                || else_stmt.as_deref().map(contains_labeled_break).unwrap_or(false)
        }
        Stmt::While { body, .. }
        | Stmt::DoWhile { body, .. }
        | Stmt::ForEach { body, .. }
        | Stmt::Synchronized { body, .. }
        | Stmt::Labeled { body, .. } => contains_labeled_break(body),
        Stmt::For { init, body, .. } => {
            init.iter().any(contains_labeled_break) || contains_labeled_break(body)
        }
        Stmt::Switch { cases, default, .. } => {
            cases.iter().flat_map(|c| c.body.iter()).any(contains_labeled_break)
                || default.as_deref().map(contains_labeled_break).unwrap_or(false)
        }
        Stmt::Try { body, catches, finally } => {
            contains_labeled_break(body)
                || catches.iter().any(|c| contains_labeled_break(&c.body))
                || finally.as_deref().map(contains_labeled_break).unwrap_or(false)
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            resources.iter().any(contains_labeled_break)
                || contains_labeled_break(body)
                || catches.iter().any(|c| contains_labeled_break(&c.body))
                || finally.as_deref().map(contains_labeled_break).unwrap_or(false)
        }
        _ => false,
    }
}

pub(crate) fn stmt_terminates(s: &Stmt) -> bool {
    match s {
        Stmt::Return(_) | Stmt::Throw(_) | Stmt::Break(_) | Stmt::Continue(_) => true,
        Stmt::Block(v) => v.last().map(stmt_terminates).unwrap_or(false),
        Stmt::If { then_stmt, else_stmt: Some(e), .. } => {
            stmt_terminates(then_stmt) && stmt_terminates(e)
        }
        // NOTE: a Switch terminates only when it is exhaustive (has a
        // default) and every case either terminates on its own or falls
        // through to a successor that terminates. Computed in `switch_terminates`.
        Stmt::Switch { cases, default, .. } => switch_terminates(cases, default.as_deref()),
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => stmt_terminates(body),
        // An infinite loop that cannot complete normally (JLS 14.21):
        // `while (true)`, `do .. while (true)`, `for (;;)` with NO `break`
        // anywhere in the body (conservative: any break, labeled or not, and
        // even one belonging to a nested construct, makes us treat the loop
        // as escapable). Decompiled shared-return tails copied into every
        // branch can leave the original tail after such a loop — javac then
        // rejects it as an unreachable statement (jdk11/26 String.split).
        Stmt::While { cond, body } | Stmt::DoWhile { body, cond }
            if matches!(cond, Expr::Const(ConstVal::Int(1))) && !contains_break_stmt(body) =>
        {
            true
        }
        Stmt::For { cond, body, .. }
            if match cond {
                None => true,
                Some(c) => matches!(c, Expr::Const(ConstVal::Int(1))),
            } && !contains_break_stmt(body) =>
        {
            true
        }
        Stmt::Try { body, catches, .. } => {
            // A finally that cannot complete abruptly does not change
            // termination; if body and all catches terminate, so does the
            // try (javac agrees and flags following statements).
            stmt_terminates(body)
                && catches.iter().all(|c| stmt_terminates(&c.body))
        }
        // try-with-resources completes normally only when its body (and
        // every catch) does: the implicit resource close cannot restore
        // normal completion. Without this arm a fully-returning TWR let
        // prune_unreachable keep the duplicated shared tail return after
        // it (jdk17/26 JarFile.getBytes: 无法访问的语句 on the method-level
        // `return var8_122`).
        Stmt::TryWithResources { body, catches, .. } => {
            stmt_terminates(body)
                && catches.iter().all(|c| stmt_terminates(&c.body))
        }
        _ => false,
    }
}

/// A switch completes abruptly (control never falls out of its end) when it
/// has a default — so every selector value is handled — and each case body
/// either terminates (return/throw) or falls through to the next case (or,
/// for the last case, to the default) which terminates. A case ending in
/// `break` exits the switch normally, so the switch does NOT terminate.
/// Without this, a trailing `return`/`throw` after an all-returning switch is
/// kept and javac rejects it as unreachable.
/// `stmt_terminates` parameterized: with `no_break`, `break`/`continue`
/// count as NORMAL completion of the enclosing switch/loop rather than
/// abrupt termination. `switch_terminates_with` needs this: a case body
/// `if (c) { ..; break; } else { ..; break; }` exits the switch normally,
/// but plain `stmt_terminates` read the nested breaks as terminating, the
/// whole switch read as abrupt, and `prune_unreachable` truncated the
/// post-switch tail (MemberName.asNormalOriginal lost its merge-var
/// comparison, clone and both returns → "missing return statement").
fn stmt_terminates_with(s: &Stmt, no_break: bool) -> bool {
    match s {
        Stmt::Return(_) | Stmt::Throw(_) => true,
        Stmt::Break(_) | Stmt::Continue(_) => !no_break,
        Stmt::Block(v) => v.last().map(|x| stmt_terminates_with(x, no_break)).unwrap_or(false),
        Stmt::If { then_stmt, else_stmt: Some(e), .. } => {
            stmt_terminates_with(then_stmt, no_break) && stmt_terminates_with(e, no_break)
        }
        Stmt::Switch { cases, default, .. } => {
            switch_terminates_with(cases, default.as_deref(), no_break)
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => {
            stmt_terminates_with(body, no_break)
        }
        Stmt::While { cond, body } | Stmt::DoWhile { body, cond }
            if matches!(cond, Expr::Const(ConstVal::Int(1))) && !contains_break_stmt(body) =>
        {
            true
        }
        Stmt::For { cond, body, .. }
            if match cond {
                None => true,
                Some(c) => matches!(c, Expr::Const(ConstVal::Int(1))),
            } && !contains_break_stmt(body)
        => {
            true
        }
        Stmt::Try { body, catches, .. } => {
            stmt_terminates_with(body, no_break)
                && catches.iter().all(|c| stmt_terminates_with(&c.body, no_break))
        }
        _ => false,
    }
}

/// True when `s` holds a reachable PLAIN `break` in a position
/// transparent to the enclosing switch (not captured by a nested
/// loop/switch — breaks there bind to the inner construct; labeled
/// breaks reach their own target, not the switch end).
fn has_plain_break(s: &Stmt) -> bool {
    match s {
        Stmt::Break(None) => true,
        Stmt::Block(v) => v.iter().any(has_plain_break),
        Stmt::If { then_stmt, else_stmt, .. } => {
            has_plain_break(then_stmt)
                || else_stmt.as_deref().map(has_plain_break).unwrap_or(false)
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => {
            has_plain_break(body)
        }
        Stmt::Try { body, catches, .. } => {
            has_plain_break(body)
                || catches.iter().any(|c| has_plain_break(&c.body))
        }
        // Breaks inside loops or nested switches belong to those
        // constructs.
        _ => false,
    }
}

fn switch_terminates(cases: &[crate::stmt::CaseGroup], default: Option<&Stmt>) -> bool {
    switch_terminates_with(cases, default, false)
}

fn switch_terminates_with(
    cases: &[crate::stmt::CaseGroup],
    default: Option<&Stmt>,
    outer_no_break: bool,
) -> bool {
    // A `break` inside THIS switch's cases exits it normally, so case-level
    // analysis always treats break as non-terminating (no_break = true).
    let no_break = true;
    let _ = outer_no_break;
    let Some(def) = default else { return false };
    if !stmt_terminates_with(def, no_break) {
        return false;
    }
    if has_plain_break(def) {
        return false;
    }
    // t[i]: once control has entered case i (via its label OR fall-through
    // from case i-1), does it necessarily terminate? A case ending in `break`
    // exits the switch normally (false); one ending in return/throw terminates
    // (true); one that falls through inherits the next case's status.
    /// True when the statement can complete normally WITHOUT a break/
    /// return/throw/continue — i.e. control really falls through to the
    /// next case label. An if whose arms all break (`if (v != 0) break;
    /// else { v = 2; break; }`) does NOT fall through, but it does not
    /// terminate either — the old shape match treated it as fallthrough
    /// and inherited the terminating default, so the whole switch counted
    /// as abrupt and prune_unreachable deleted the post-switch
    /// `return value;` (jdk26 CalendarDataUtility
    /// CalendarWeekParameterGetter.getObject: 缺少返回语句).
    fn last_falls_through(s: &Stmt) -> bool {
        match s {
            Stmt::Break(_) | Stmt::Continue(_) | Stmt::Return(_) | Stmt::Throw(_) => false,
            Stmt::Block(v) => v.last().map(last_falls_through).unwrap_or(true),
            Stmt::If { then_stmt, else_stmt, .. } => match else_stmt {
                Some(e) => last_falls_through(then_stmt) || last_falls_through(e),
                None => true,
            },
            Stmt::While { cond, body } | Stmt::DoWhile { body, cond }
                if matches!(cond, Expr::Const(ConstVal::Int(1)))
                    && !contains_break_stmt(body) =>
            {
                false
            }
            Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => {
                last_falls_through(body)
            }
            // A nested switch falls through to the next outer case ONLY
            // when it can complete normally. Consulting it matters: a
            // group whose every case ends in `break OUTER_LABEL`/throw
            // never completes (jdk26 BytecodeHelpers.convertOpcode: the
            // from-switch cases each hold a to-switch whose cases are
            // `stack0 = Opcode.X; break L1;` + throwing default — the
            // blind `true` made every outer case inherit the terminating
            // default, the outer switch read as abrupt, and
            // prune_unreachable deleted the merge `return stack0;` —
            // 缺少返回语句).
            Stmt::Switch { cases, default, .. } => {
                // Does this nested switch complete normally? Group i does
                // when it holds a PLAIN `break` (exits the switch), or its
                // last statement is not abrupt (return/throw/break/
                // continue — a LABELED break exits an OUTER construct, not
                // this switch) and group i+1 completes normally.
                fn completes_normally(s: &Stmt) -> bool {
                    match s {
                        Stmt::Switch { cases, default, .. } => {
                            let n = cases.len();
                            let mut c = vec![false; n + 1];
                            c[n] = default
                                .as_deref()
                                .map(|d| {
                                    has_plain_break(d)
                                        || (!stmt_terminates_with(d, false) && true)
                                })
                                .unwrap_or(true);
                            for i in (0..n).rev() {
                                let body = &cases[i].body;
                                c[i] = match body.last() {
                                    None => c[i + 1],
                                    Some(l) => {
                                        has_plain_break(l)
                                            || (!stmt_terminates_with(l, false) && c[i + 1])
                                    }
                                };
                            }
                            c.iter().take(n + 1).any(|&x| x)
                        }
                        other => {
                            has_plain_break(other) || !stmt_terminates_with(other, false)
                        }
                    }
                }
                completes_normally(s)
            }
            Stmt::Try { body, catches, .. } => {
                last_falls_through(body)
                    || catches.iter().any(|c| last_falls_through(&c.body))
            }
            _ => true,
        }
    }
    let n = cases.len();
    let mut t = vec![false; n + 1];
    t[n] = true; // falling off the last case reaches the default, which terminates
    for i in (0..n).rev() {
        let body = &cases[i].body;
        t[i] = match body.last() {
            Some(last) if last_falls_through(last) => t[i + 1],
            Some(last) => stmt_terminates_with(last, no_break),
            None => t[i + 1],
        };
        // A plain `break` ANYWHERE in the body (not just its last
        // statement) exits the switch normally: the body may still end
        // in a terminating copy of the shared tail while a mid-arm
        // branch breaks out (jdk17 DirectMethodHandle
        // .shouldBeInitialized: every case targets the tail, the arm
        // inlined it ending in `return false`, and the isSamePackage
        // paths' interior `break`s were invisible to the last-stmt
        // scan — the switch read as abrupt, prune_unreachable deleted
        // the post-switch ensureClassInitialized tail, and both the
        // breaks and the fall-out landed at the method end —
        // 缺少返回语句 + lost ensure-init).
        if t[i] && body.iter().any(has_plain_break) {
            t[i] = false;
        }
    }
    // The switch completes abruptly only if EVERY case entry terminates. If any
    // case breaks (or falls through to one that breaks), control exits the
    // switch normally, so a following return is reachable and must be kept.
    // (Returning just t[0] over-pruned when case 0 falls through to a later
    // case that breaks — e.g. DirectMethodHandle.makeImpl lost its post-switch
    // return, causing "missing return statement".)
    t.iter().take(n).all(|&x| x)
}

/// jdk26 (JEP 513, flexible constructor bodies): statements may PRECEDE
/// super()/this(), but the delegation call itself must not sit inside a
/// control-flow statement. A pre-super guard throw structures as
/// `if (c) { super(..); ..; return; } else { throw ..; }` — semantically
/// right, but javac rejects the nested explicit ctor call (AbstractPoolEntry
/// Utf8EntryImpl). Rotate to the source shape:
/// `if (!c) { throw ..; } super(..); ..`.
fn hoist_ctor_call_guards(s: &mut Stmt) {
    fn is_ctor_call(x: &Stmt) -> bool {
        matches!(x, Stmt::ExprStmt(Expr::Method { name, .. }) if name == "<init>")
    }
    fn throw_terminated(x: &Stmt) -> bool {
        match x {
            Stmt::Throw(_) => true,
            Stmt::Block(v) => matches!(v.last(), Some(Stmt::Throw(_))),
            _ => false,
        }
    }
    fn contains_ctor_call(x: &Stmt) -> bool {
        match x {
            Stmt::Block(v) => v.iter().any(contains_ctor_call),
            other => is_ctor_call(other),
        }
    }
    fn into_vec(x: Stmt) -> Vec<Stmt> {
        match x {
            Stmt::Block(v) => v,
            other => vec![other],
        }
    }
    fn strip_tail_return(v: &mut Vec<Stmt>) {
        while matches!(v.last(), Some(Stmt::Return(None))) {
            v.pop();
        }
    }
    fn rotate_one(s: &mut Stmt) -> bool {
        let (cond, then_stmt, else_stmt) = match s {
            Stmt::If { cond, then_stmt, else_stmt: Some(e) } => (cond, then_stmt, e),
            _ => return false,
        };
        let mut then_vec = into_vec(*std::mem::replace(then_stmt, Box::new(Stmt::Block(vec![]))));
        let else_body = *std::mem::replace(else_stmt, Box::new(Stmt::Block(vec![])));
        let cond_val = std::mem::replace(cond, Expr::This);
        // then = ctor-call body, else = throw guard
        if is_ctor_call(then_vec.first().unwrap_or(&Stmt::Return(None)))
            && throw_terminated(&else_body)
            && !contains_ctor_call(&else_body)
        {
            strip_tail_return(&mut then_vec);
            let neg = match cond_val {
                Expr::Un { op: crate::expr::UnOp::Not, e } => *e,
                c => Expr::Un { op: crate::expr::UnOp::Not, e: Box::new(c) },
            };
            let mut out: Vec<Stmt> = Vec::with_capacity(1 + then_vec.len());
            out.push(Stmt::If { cond: neg, then_stmt: Box::new(else_body), else_stmt: None });
            out.extend(then_vec);
            *s = Stmt::Block(out);
            return true;
        }
        // else = ctor-call body, then = throw guard
        let mut else_vec = into_vec(else_body);
        if is_ctor_call(else_vec.first().unwrap_or(&Stmt::Return(None)))
            && throw_terminated(then_stmt)
            && !contains_ctor_call(then_stmt)
        {
            strip_tail_return(&mut else_vec);
            let guard_body = *std::mem::replace(then_stmt, Box::new(Stmt::Block(vec![])));
            let mut out: Vec<Stmt> = Vec::with_capacity(1 + else_vec.len());
            out.push(Stmt::If { cond: cond_val, then_stmt: Box::new(guard_body), else_stmt: None });
            out.extend(else_vec);
            *s = Stmt::Block(out);
            return true;
        }
        // Not rotatable: restore the original If.
        *s = Stmt::If {
            cond: cond_val,
            then_stmt: Box::new(Stmt::Block(then_vec)),
            else_stmt: Some(Box::new(Stmt::Block(else_vec))),
        };
        false
    }
    fn rec(s: &mut Stmt) {
        match s {
            Stmt::Block(v) => {
                let mut i = 0;
                while i < v.len() {
                    if rotate_one(&mut v[i]) {
                        i += 1;
                        continue;
                    }
                    rec(&mut v[i]);
                    i += 1;
                }
            }
            other => {
                rotate_one(other);
            }
        }
    }
    rec(s);
}

fn prune_unreachable(s: &mut Stmt) {
    match s {
        Stmt::Block(v) => {
            // Post-order: children are truncated first, so compound
            // terminators (if/else both returning, etc.) are visible.
            v.iter_mut().for_each(prune_unreachable);
            if let Some(pos) = v.iter().position(stmt_terminates) {
                v.truncate(pos + 1);
            }
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            prune_unreachable(then_stmt);
            if let Some(e) = else_stmt {
                prune_unreachable(e);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => prune_unreachable(body),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(prune_unreachable);
            prune_unreachable(body);
        }
        Stmt::ForEach { body, .. } => prune_unreachable(body),
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                // `stmt_terminates`, not just the flat Return/Throw/Break
                // check: a case body ending in `while (true) { .. return .. }`
                // (no break anywhere) cannot complete normally, and javac
                // rejects the shared-tail return copy after it as
                // 无法访问的语句 (jdk26 DateTimeTextProvider getIterator
                // cases 2/7).
                if let Some(pos) = c.body.iter().position(stmt_terminates) {
                    // `break` at case end is idiomatic; keep it, drop what follows
                    c.body.truncate(pos + 1);
                }
                c.body.iter_mut().for_each(prune_unreachable);
            }
            if let Some(d) = default {
                prune_unreachable(d);
            }
        }
        Stmt::Try { body, catches, finally } => {
            prune_unreachable(body);
            for c in catches {
                prune_unreachable(&mut c.body);
            }
            if let Some(f) = finally {
                prune_unreachable(f);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { prune_unreachable(res); }
            prune_unreachable(body);
            for c in catches {
                prune_unreachable(&mut c.body);
            }
            if let Some(f) = finally {
                prune_unreachable(f);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => prune_unreachable(body),
        _ => {}
    }
}

fn is_terminator_stmt(s: &Stmt) -> bool {
    matches!(s, Stmt::Return(_) | Stmt::Throw(_) | Stmt::Break(_) | Stmt::Continue(_))
}

fn strip_tail_break(body: &mut Stmt) {
    if let Stmt::Block(v) = body {
        while matches!(v.last(), Some(Stmt::Break(None))) {
            v.pop();
        }
    } else if matches!(body, Stmt::Break(None)) {
        *body = Stmt::Block(vec![]);
    }
}

/// True when stripping a tail `break;` from this loop body is safe: only
/// for do-whiles and infinite loops, where the body end already leaves /
/// re-iterates unconditionally. A tail break in a CONDITIONAL loop is the
/// loop's normal-completion exit (an enclosing-loop barrier materialized
/// by the structurer): popping it makes the conditional loop spin forever
/// (jdk11 FutureTask.removeWaiter: the inner `while (q != null)`
/// completion had to break the outer retry loop — stripped, the outer
/// while(true) never completed and the tail `return` went unreachable).
fn tail_break_strippable(s: &Stmt) -> bool {
    // ONLY do-while: there the tail break is the rotation residue the
    // strip was written for (the do-while condition already names the
    // exit). In every other loop the tail break is the body's normal
    // completion exit — e.g. an enclosing-loop barrier the structurer
    // materialized after an inner loop (jdk11 FutureTask.removeWaiter:
    // stripping it made the outer while(true) never complete and the
    // tail return unreachable).
    matches!(s, Stmt::DoWhile { .. })
}

/// Give catch variables their exception type when the LVT did not provide
/// one (catch-all handlers default to java/lang/Throwable).
/// Assign each catch occurrence a printed name that is unique among all
/// names visible at that point (locals + enclosing catches).
fn assign_catch_names(vt: &mut VarTable, s: &mut Stmt) {
    let mut used: std::collections::HashSet<String> =
        vt.vars.iter().map(|v| v.name.clone()).collect();
    // Names shared by several variables (slot reuse) always conflict.
    let mut counts: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
    for v in &vt.vars {
        *counts.entry(v.name.clone()).or_insert(0) += 1;
    }
    assign_catch_names_rec(vt, s, &mut Vec::new(), &mut used, &counts);
}

fn assign_catch_names_rec(
    vt: &mut VarTable,
    s: &mut Stmt,
    open: &mut Vec<String>,
    used: &mut std::collections::HashSet<String>,
    counts: &std::collections::HashMap<String, usize>,
) {
    match s {
        Stmt::Try { body, catches, finally } => {
            assign_catch_names_rec(vt, body, open, used, counts);
            for c in catches.iter_mut() {
                let base = if c.var != u32::MAX && (c.var as usize) < vt.vars.len() {
                    vt.vars[c.var as usize].name.clone()
                } else {
                    "ignored".to_string()
                };
                let shared = counts.get(&base).copied().unwrap_or(0) > 1;
                let name = if open.contains(&base) || base == "ignored" || shared {
                    let mut k = 1;
                    loop {
                        let cand = format!("e{}", k);
                        if !used.contains(&cand) && !open.contains(&cand) {
                            break cand;
                        }
                        k += 1;
                    }
                } else {
                    base.clone()
                };
                used.insert(name.clone());
                open.push(name.clone());
                // The catch variable is exclusively ours (freshly split in
                // resolve_catch_vars): rename it in the table so body
                // references print consistently.
                if c.var != u32::MAX && (c.var as usize) < vt.vars.len() {
                    vt.vars[c.var as usize].name = name.clone();
                }
                c.var_name = Some(name);
                assign_catch_names_rec(vt, &mut c.body, open, used, counts);
                open.pop();
            }
            if let Some(f) = finally {
                assign_catch_names_rec(vt, f, open, used, counts);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { assign_catch_names_rec(vt, res, open, used, counts); }
            assign_catch_names_rec(vt, body, open, used, counts);
            for c in catches.iter_mut() {
                let base = if c.var != u32::MAX && (c.var as usize) < vt.vars.len() {
                    vt.vars[c.var as usize].name.clone()
                } else {
                    "ignored".to_string()
                };
                let shared = counts.get(&base).copied().unwrap_or(0) > 1;
                let name = if open.contains(&base) || base == "ignored" || shared {
                    let mut k = 1;
                    loop {
                        let cand = format!("e{}", k);
                        if !used.contains(&cand) && !open.contains(&cand) {
                            break cand;
                        }
                        k += 1;
                    }
                } else {
                    base.clone()
                };
                used.insert(name.clone());
                open.push(name.clone());
                // The catch variable is exclusively ours (freshly split in
                // resolve_catch_vars): rename it in the table so body
                // references print consistently.
                if c.var != u32::MAX && (c.var as usize) < vt.vars.len() {
                    vt.vars[c.var as usize].name = name.clone();
                }
                c.var_name = Some(name);
                assign_catch_names_rec(vt, &mut c.body, open, used, counts);
                open.pop();
            }
            if let Some(f) = finally {
                assign_catch_names_rec(vt, f, open, used, counts);
            }
        }
        Stmt::Block(v) => v.iter_mut().for_each(|x| assign_catch_names_rec(vt, x, open, used, counts)),
        Stmt::If { then_stmt, else_stmt, .. } => {
            assign_catch_names_rec(vt, then_stmt, open, used, counts);
            if let Some(e) = else_stmt {
                assign_catch_names_rec(vt, e, open, used, counts);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => {
            assign_catch_names_rec(vt, body, open, used, counts)
        }
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(|i| assign_catch_names_rec(vt, i, open, used, counts));
            assign_catch_names_rec(vt, body, open, used, counts);
        }
        Stmt::ForEach { body, .. } => assign_catch_names_rec(vt, body, open, used, counts),
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(|st| assign_catch_names_rec(vt, st, open, used, counts));
            }
            if let Some(d) = default {
                assign_catch_names_rec(vt, d, open, used, counts);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => {
            assign_catch_names_rec(vt, body, open, used, counts)
        }
        _ => {}
    }
}

#[allow(dead_code)]
fn collect_catch_vars(s: &Stmt, out: &mut Vec<u32>) {
    match s {
        Stmt::Try { body, catches, finally } => {
            for c in catches {
                if c.var != u32::MAX {
                    out.push(c.var);
                }
                collect_catch_vars(&c.body, out);
            }
            collect_catch_vars(body, out);
            if let Some(f) = finally {
                collect_catch_vars(f, out);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter() { collect_catch_vars(res, out); }
            for c in catches {
                if c.var != u32::MAX {
                    out.push(c.var);
                }
                collect_catch_vars(&c.body, out);
            }
            collect_catch_vars(body, out);
            if let Some(f) = finally {
                collect_catch_vars(f, out);
            }
        }
        Stmt::Block(v) => v.iter().for_each(|x| collect_catch_vars(x, out)),
        Stmt::If { then_stmt, else_stmt, .. } => {
            collect_catch_vars(then_stmt, out);
            if let Some(e) = else_stmt {
                collect_catch_vars(e, out);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => collect_catch_vars(body, out),
        Stmt::For { init, body, .. } => {
            init.iter().for_each(|i| collect_catch_vars(i, out));
            collect_catch_vars(body, out);
        }
        Stmt::ForEach { body, .. } => collect_catch_vars(body, out),
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter().for_each(|st| collect_catch_vars(st, out));
            }
            if let Some(d) = default {
                collect_catch_vars(d, out);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => collect_catch_vars(body, out),
        _ => {}
    }
}

#[allow(dead_code)]
fn type_catch_vars(vt: &mut VarTable, s: &Stmt) {
    match s {
        Stmt::Try { body, catches, finally } => {
            for c in catches {
                if c.var != u32::MAX && (c.var as usize) < vt.vars.len() {
                    let want = if c.exc.is_empty() {
                        Some("java/lang/Throwable".to_string())
                    } else {
                        c.exc.first().cloned()
                    };
                    if let Some(w) = want {
                        let cur = vt.vars[c.var as usize].ty.erased();
                        let placeholder = matches!(&cur, JavaType::Object(n) if n == "java/lang/Object")
                            || cur == JavaType::Int;
                        if placeholder {
                            vt.vars[c.var as usize].ty = TypeRef::J(JavaType::Object(w));
                        }
                    }
                }
                type_catch_vars(vt, &c.body);
            }
            type_catch_vars(vt, body);
            if let Some(f) = finally {
                type_catch_vars(vt, f);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter() { type_catch_vars(vt, res); }
            for c in catches {
                if c.var != u32::MAX && (c.var as usize) < vt.vars.len() {
                    let want = if c.exc.is_empty() {
                        Some("java/lang/Throwable".to_string())
                    } else {
                        c.exc.first().cloned()
                    };
                    if let Some(w) = want {
                        let cur = vt.vars[c.var as usize].ty.erased();
                        let placeholder = matches!(&cur, JavaType::Object(n) if n == "java/lang/Object")
                            || cur == JavaType::Int;
                        if placeholder {
                            vt.vars[c.var as usize].ty = TypeRef::J(JavaType::Object(w));
                        }
                    }
                }
                type_catch_vars(vt, &c.body);
            }
            type_catch_vars(vt, body);
            if let Some(f) = finally {
                type_catch_vars(vt, f);
            }
        }
        Stmt::Block(v) => v.iter().for_each(|x| type_catch_vars(vt, x)),
        Stmt::If { then_stmt, else_stmt, .. } => {
            type_catch_vars(vt, then_stmt);
            if let Some(e) = else_stmt {
                type_catch_vars(vt, e);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => type_catch_vars(vt, body),
        Stmt::For { init, body, .. } => {
            init.iter().for_each(|i| type_catch_vars(vt, i));
            type_catch_vars(vt, body);
        }
        Stmt::ForEach { body, .. } => type_catch_vars(vt, body),
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter().for_each(|st| type_catch_vars(vt, st));
            }
            if let Some(d) = default {
                type_catch_vars(vt, d);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => type_catch_vars(vt, body),
        _ => {}
    }
}

/// An empty catch-all clause would silently swallow exceptions (and break
/// definite assignment). Restore `throw e;` so propagation is preserved.
fn fix_empty_catchall(s: &mut Stmt) {
    match s {
        Stmt::Try { body, catches, finally } => {
            fix_empty_catchall(body);
            for c in catches.iter_mut() {
                fix_empty_catchall(&mut c.body);
                if c.exc.is_empty() {
                    let empty = match &*c.body {
                        Stmt::Block(v) => v.is_empty(),
                        _ => false,
                    };
                    if empty && c.var != u32::MAX {
                        c.body = Box::new(Stmt::Throw(Expr::Local {
                            var: c.var,
                            ty: crate::expr::TypeRef::J(jcdc_jvm::JavaType::Object(
                                "java/lang/Throwable".into(),
                            )),
                        }));
                    }
                }
            }
            if let Some(f) = finally {
                fix_empty_catchall(f);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { fix_empty_catchall(res); }
            fix_empty_catchall(body);
            for c in catches.iter_mut() {
                fix_empty_catchall(&mut c.body);
                if c.exc.is_empty() {
                    let empty = match &*c.body {
                        Stmt::Block(v) => v.is_empty(),
                        _ => false,
                    };
                    if empty && c.var != u32::MAX {
                        c.body = Box::new(Stmt::Throw(Expr::Local {
                            var: c.var,
                            ty: crate::expr::TypeRef::J(jcdc_jvm::JavaType::Object(
                                "java/lang/Throwable".into(),
                            )),
                        }));
                    }
                }
            }
            if let Some(f) = finally {
                fix_empty_catchall(f);
            }
        }
        Stmt::Block(v) => v.iter_mut().for_each(fix_empty_catchall),
        Stmt::If { then_stmt, else_stmt, .. } => {
            fix_empty_catchall(then_stmt);
            if let Some(e) = else_stmt {
                fix_empty_catchall(e);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => fix_empty_catchall(body),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(fix_empty_catchall);
            fix_empty_catchall(body);
        }
        Stmt::ForEach { body, .. } => fix_empty_catchall(body),
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(fix_empty_catchall);
            }
            if let Some(d) = default {
                fix_empty_catchall(d);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => fix_empty_catchall(body),
        _ => {}
    }
}

fn prepend_comment(s: &mut Stmt, text: String) {
    let old = std::mem::replace(s, Stmt::Block(vec![]));
    let old_vec = match old {
        Stmt::Block(v) => v,
        other => vec![other],
    };
    let mut v = vec![Stmt::Comment(text)];
    v.extend(old_vec);
    *s = Stmt::Block(v);
}

/// Assign exception parameter variables: the handler's first statement is
/// normally `e = <stack>` (LocalDef or Assign to a local). Replace it with
/// the catch variable binding.
fn resolve_catch_vars(vt: &mut VarTable, s: &mut Stmt) {
    match s {
        Stmt::Try { body, catches, finally } => {
            resolve_catch_vars(vt, body);
            for c in catches.iter_mut() {
                if c.var == u32::MAX {
                    // Bind the exception parameter: the handler's first
                    // statement stores the (placeholder) exception object.
                    let first = first_stmt_mut(&mut c.body);
                    let extracted = match first {
                        Some(Stmt::LocalDef { var, .. }) => Some(*var),
                        Some(Stmt::ExprStmt(Expr::Assign { target, .. })) => match &**target {
                            Expr::Local { var, .. } => Some(*var),
                            _ => None,
                        },
                        _ => None,
                    };
                    if let Some(v) = extracted {
                        // The handler slot may be shared with a normal
                        // local (result temps!): give the exception its own
                        // variable identity and rewrite the handler body.
                        let exc_ty = c
                            .exc
                            .first()
                            .cloned()
                            .map(JavaType::Object)
                            .unwrap_or(JavaType::Object("java/lang/Throwable".into()));
                        let new_var = {
                            let slot = vt.vars[v as usize].slot;
                            // Prefer the LVT name of the handler's own
                            // variable (catch (Exception e0) — jdk17
                            // SocketExceptions.create: the synthesized "e"
                            // shadowed the anon body's substituted outer
                            // capture `return e`, binding it to the catch
                            // param instead — Exception无法转换为IOException).
                            let vi = &vt.vars[v as usize];
                            let nm = if vi.synthetic_name {
                                "e".to_string()
                            } else {
                                vi.name.clone()
                            };
                            vt.add_catch_var(slot, nm, TypeRef::J(exc_ty))
                        };
                        remove_first_stmt(&mut c.body);
                        rewrite_var_until_assign(&mut c.body, v, new_var);
                        c.var = new_var;
                    } else if std::env::var("JCDC_DBG_CATCH").is_ok() {
                        eprintln!("no store at handler head: {:?}", first_stmt_peek(&c.body));
                    }
                }
                resolve_catch_vars(vt, &mut c.body);
            }
            if let Some(f) = finally {
                resolve_catch_vars(vt, f);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { resolve_catch_vars(vt, res); }
            resolve_catch_vars(vt, body);
            for c in catches.iter_mut() {
                if c.var == u32::MAX {
                    // Bind the exception parameter: the handler's first
                    // statement stores the (placeholder) exception object.
                    let first = first_stmt_mut(&mut c.body);
                    let extracted = match first {
                        Some(Stmt::LocalDef { var, .. }) => Some(*var),
                        Some(Stmt::ExprStmt(Expr::Assign { target, .. })) => match &**target {
                            Expr::Local { var, .. } => Some(*var),
                            _ => None,
                        },
                        _ => None,
                    };
                    if let Some(v) = extracted {
                        // The handler slot may be shared with a normal
                        // local (result temps!): give the exception its own
                        // variable identity and rewrite the handler body.
                        let exc_ty = c
                            .exc
                            .first()
                            .cloned()
                            .map(JavaType::Object)
                            .unwrap_or(JavaType::Object("java/lang/Throwable".into()));
                        let new_var = {
                            let slot = vt.vars[v as usize].slot;
                            // Prefer the LVT name of the handler's own
                            // variable (catch (Exception e0) — jdk17
                            // SocketExceptions.create: the synthesized "e"
                            // shadowed the anon body's substituted outer
                            // capture `return e`, binding it to the catch
                            // param instead — Exception无法转换为IOException).
                            let vi = &vt.vars[v as usize];
                            let nm = if vi.synthetic_name {
                                "e".to_string()
                            } else {
                                vi.name.clone()
                            };
                            vt.add_catch_var(slot, nm, TypeRef::J(exc_ty))
                        };
                        remove_first_stmt(&mut c.body);
                        rewrite_var_until_assign(&mut c.body, v, new_var);
                        c.var = new_var;
                    } else if std::env::var("JCDC_DBG_CATCH").is_ok() {
                        eprintln!("no store at handler head: {:?}", first_stmt_peek(&c.body));
                    }
                }
                resolve_catch_vars(vt, &mut c.body);
            }
            if let Some(f) = finally {
                resolve_catch_vars(vt, f);
            }
        }
        Stmt::Block(v) => {
            for x in v {
                resolve_catch_vars(vt, x);
            }
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            resolve_catch_vars(vt, then_stmt);
            if let Some(e) = else_stmt {
                resolve_catch_vars(vt, e);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => resolve_catch_vars(vt, body),
        Stmt::For { body, init, .. } => {
            for i in init {
                resolve_catch_vars(vt, i);
            }
            resolve_catch_vars(vt, body);
        }
        Stmt::ForEach { body, .. } => resolve_catch_vars(vt, body),
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                for st in c.body.iter_mut() {
                    resolve_catch_vars(vt, st);
                }
            }
            if let Some(d) = default {
                resolve_catch_vars(vt, d);
            }
        }
        Stmt::Synchronized { body, .. } => resolve_catch_vars(vt, body),
        _ => {}
    }
}

/// Rename every reference of variable `from` to `to` inside `s`.
/// rewrite_var, bounded to the leading statements before the first
/// (re)assignment of `from`: a catch handler whose slot is shared with an
/// ordinary local carries the exception identity only until the normal
/// flow reassigns the slot (jdk11 Calendar.createCalendar: the handler
/// stores the exception into `cal`'s slot, immediately overwrites it with
/// `cal = null` and falls into the shared method tail — a full rewrite
/// painted the whole tail as the exception var: "BuddhistCalendar无法转换
/// 为IllegalArgumentException"). Compound statements containing any
/// assignment of `from` stop the rewrite conservatively.
fn rewrite_var_until_assign(s: &mut Stmt, from: u32, to: u32) -> bool {
    match s {
        Stmt::Block(v) => {
            for x in v.iter_mut() {
                if !rewrite_var_until_assign(x, from, to) {
                    return false;
                }
            }
            true
        }
        Stmt::ExprStmt(e) => {
            let assigns = matches!(e,
                Expr::Assign { target, .. }
                if matches!(&**target, Expr::Local { var, .. } if *var == from));
            if assigns {
                // RHS still reads the exception; the store rebinds the
                // slot to the normal local — rewrite the value, keep the
                // target, and stop.
                if let Expr::Assign { value, .. } = e {
                    let mut tmp = Stmt::ExprStmt((**value).clone());
                    rewrite_var(&mut tmp, from, to);
                    if let (Stmt::ExprStmt(rv), Expr::Assign { value, .. }) = (tmp, &mut *e) {
                        *value = Box::new(rv);
                    }
                }
                return false;
            }
            if stmt_assigns_var(s, from) {
                return false;
            }
            rewrite_var(s, from, to);
            true
        }
        Stmt::LocalDef { var, .. } if *var == from => false,
        other => {
            if stmt_assigns_var(other, from) {
                return false;
            }
            rewrite_var(other, from, to);
            true
        }
    }
}

fn rewrite_var(s: &mut Stmt, from: u32, to: u32) {
    fn rw_expr(e: &mut Expr, from: u32, to: u32, ty: &TypeRef) {
        if let Expr::Local { var, ty: t } = e {
            if *var == from {
                *var = to;
                *t = ty.clone();
            }
        }
        match e {
            Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
                args.iter_mut().for_each(|a| rw_expr(a, from, to, ty))
            }
            Expr::Method { owner, args, .. } => {
                if let Some(o) = owner {
                    rw_expr(o, from, to, ty);
                }
                args.iter_mut().for_each(|a| rw_expr(a, from, to, ty));
            }
            Expr::Field { owner: Some(o), .. } => rw_expr(o, from, to, ty),
            Expr::ArrayIndex { array, index } => {
                rw_expr(array, from, to, ty);
                rw_expr(index, from, to, ty);
            }
            Expr::Cast { e, .. } | Expr::InstanceOf { e, .. } | Expr::Un { e, .. } => {
                rw_expr(e, from, to, ty)
            }
            Expr::Bin { l, r, .. } => {
                rw_expr(l, from, to, ty);
                rw_expr(r, from, to, ty);
            }
            Expr::Cond { c, t, f } => {
                rw_expr(c, from, to, ty);
                rw_expr(t, from, to, ty);
                rw_expr(f, from, to, ty);
            }
            Expr::Assign { target, value, .. } => {
                rw_expr(target, from, to, ty);
                rw_expr(value, from, to, ty);
            }
            Expr::PreIncDec { e, .. } | Expr::PostIncDec { e, .. } => rw_expr(e, from, to, ty),
            Expr::Lambda(l) => l.captures.iter_mut().for_each(|c| rw_expr(c, from, to, ty)),
            Expr::StringConcat(parts) => parts.iter_mut().for_each(|p| {
                if let crate::expr::ConcatPart::Str(inner) = p {
                    rw_expr(inner, from, to, ty);
                }
            }),
            Expr::Invokedynamic { args, .. } => args.iter_mut().for_each(|a| rw_expr(a, from, to, ty)),
            Expr::NewArray { dims, init, .. } => {
                dims.iter_mut().for_each(|d| rw_expr(d, from, to, ty));
                if let Some(vals) = init {
                    vals.iter_mut().for_each(|v| rw_expr(v, from, to, ty));
                }
            }
            _ => {}
        }
    }
    let ty = TypeRef::J(JavaType::Object("java/lang/Throwable".into()));
    match s {
        Stmt::Block(v) => v.iter_mut().for_each(|x| rewrite_var(x, from, to)),
        Stmt::ExprStmt(e) => rw_expr(e, from, to, &ty),
        Stmt::LocalDef { var, init, .. } => {
            if *var == from {
                *var = to;
            }
            if let Some(e) = init {
                rw_expr(e, from, to, &ty);
            }
        }
        Stmt::Return(e) => {
            if let Some(x) = e {
                rw_expr(x, from, to, &ty);
            }
        }
        Stmt::Throw(e) => rw_expr(e, from, to, &ty),
        Stmt::If { cond, then_stmt, else_stmt } => {
            rw_expr(cond, from, to, &ty);
            rewrite_var(then_stmt, from, to);
            if let Some(x) = else_stmt {
                rewrite_var(x, from, to);
            }
        }
        Stmt::While { cond, body } => {
            rw_expr(cond, from, to, &ty);
            rewrite_var(body, from, to);
        }
        Stmt::DoWhile { body, cond } => {
            rewrite_var(body, from, to);
            rw_expr(cond, from, to, &ty);
        }
        Stmt::For { init, cond, update, body } => {
            init.iter_mut().for_each(|i| rewrite_var(i, from, to));
            if let Some(c) = cond {
                rw_expr(c, from, to, &ty);
            }
            update.iter_mut().for_each(|u| rw_expr(u, from, to, &ty));
            rewrite_var(body, from, to);
        }
        Stmt::ForEach { var, iterable, body, .. } => {
            if *var == from {
                *var = to;
            }
            rw_expr(iterable, from, to, &ty);
            rewrite_var(body, from, to);
        }
        Stmt::Switch { selector, cases, default, .. } => {
            rw_expr(selector, from, to, &ty);
            for c in cases {
                c.body.iter_mut().for_each(|st| rewrite_var(st, from, to));
            }
            if let Some(d) = default {
                rewrite_var(d, from, to);
            }
        }
        Stmt::Try { body, catches, finally } => {
            rewrite_var(body, from, to);
            for c in catches {
                if c.var == from {
                    c.var = to;
                }
                rewrite_var(&mut c.body, from, to);
            }
            if let Some(f) = finally {
                rewrite_var(f, from, to);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { rewrite_var(res, from, to); }
            rewrite_var(body, from, to);
            for c in catches {
                if c.var == from {
                    c.var = to;
                }
                rewrite_var(&mut c.body, from, to);
            }
            if let Some(f) = finally {
                rewrite_var(f, from, to);
            }
        }
        Stmt::Synchronized { lock, body } => {
            rw_expr(lock, from, to, &ty);
            rewrite_var(body, from, to);
        }
        Stmt::Labeled { body, .. } => rewrite_var(body, from, to),
        Stmt::MonitorEnter(e) | Stmt::MonitorExit(e) => rw_expr(e, from, to, &ty),
        _ => {}
    }
}

fn first_stmt_peek(s: &Stmt) -> Stmt {
    match s {
        Stmt::Block(v) => v.first().cloned().unwrap_or(Stmt::Block(vec![])),
        other => other.clone(),
    }
}

fn first_stmt_mut(s: &mut Stmt) -> Option<&mut Stmt> {
    let mut cur = s;
    loop {
        match cur {
            Stmt::Block(v) => match v.first_mut() {
                Some(first) => cur = first,
                None => return None,
            },
            other => return Some(other),
        }
    }
}

fn remove_first_stmt(s: &mut Stmt) {
    let cur = s;
    loop {
        match cur {
            Stmt::Block(v) => {
                if v.is_empty() {
                    return;
                }
                if matches!(v[0], Stmt::Block(_)) {
                    // descend; afterwards drop emptied inner blocks
                    let first_is_block = true;
                    if first_is_block {
                        // temporarily take to recurse
                        let mut inner = std::mem::replace(&mut v[0], Stmt::Block(vec![]));
                        remove_first_stmt(&mut inner);
                        if inner.is_empty_block() {
                            v.remove(0);
                        } else {
                            v[0] = inner;
                        }
                        return;
                    }
                }
                v.remove(0);
                return;
            }
            other => {
                *other = Stmt::Block(vec![]);
                return;
            }
        }
    }
}

/// Reconstruct `synchronized (lock) { body }` from the javac pattern:
/// `monitorenter; try { body; monitorexit; } catch (any) { monitorexit; throw; }`
/// Remove the leftover `mon = lockExpr;` stores that fed monitorenter:
/// after `synchronized (lockExpr) {...}` reconstruction the synthetic
/// monitor local is dead, and its declared type may not even accept the
/// lock value (slot reuse).
fn drop_monitor_stores(s: &mut Stmt, vt: &VarTable) {
    fn rec(s: &mut Stmt, vt: &VarTable) {
        match s {
            Stmt::Block(v) => {
                let mut i = 0;
                while i + 1 < v.len() {
                    let store = match &v[i] {
                        Stmt::ExprStmt(Expr::Assign { target, value, .. }) => {
                            match &**target {
                                Expr::Local { var, .. } => Some((*var, &**value)),
                                _ => None,
                            }
                        }
                        Stmt::LocalDef { var, init: Some(e), .. } => Some((*var, e)),
                        _ => None,
                    };
                    let drop = match (store, &v[i + 1]) {
                        (Some((var, val)), Stmt::Synchronized { lock, body })
                            if vt.var(var).synthetic_name
                                && (lock == val
                                    || matches!(lock, Expr::Local { var: lv, .. } if *lv == var))
                                && !stmt_uses_var(body, var)
                                && !v[i + 2..].iter().any(|st| stmt_uses_var(st, var)) =>
                        {
                            true
                        }
                        _ => false,
                    };
                    if drop {
                        v.remove(i);
                    } else {
                        rec(&mut v[i], vt);
                        i += 1;
                    }
                }
                if let Some(last) = v.last_mut() {
                    rec(last, vt);
                }
            }
            Stmt::If { then_stmt, else_stmt, .. } => {
                rec(then_stmt, vt);
                if let Some(e) = else_stmt {
                    rec(e, vt);
                }
            }
            Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => rec(body, vt),
            Stmt::For { init, body, .. } => {
                init.iter_mut().for_each(|x| rec(x, vt));
                rec(body, vt);
            }
            Stmt::ForEach { body, .. } => rec(body, vt),
            Stmt::Switch { cases, default, .. } => {
                for c in cases.iter_mut() {
                    c.body.iter_mut().for_each(|x| rec(x, vt));
                }
                if let Some(d) = default {
                    rec(d, vt);
                }
            }
            Stmt::Try { body, catches, finally } => {
                rec(body, vt);
                for c in catches.iter_mut() {
                    rec(&mut c.body, vt);
                }
                if let Some(f) = finally {
                    rec(f, vt);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                for r in resources.iter_mut() {
                    rec(r, vt);
                }
                rec(body, vt);
                for c in catches.iter_mut() {
                    rec(&mut c.body, vt);
                }
                if let Some(f) = finally {
                    rec(f, vt);
                }
            }
            Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => rec(body, vt),
            _ => {}
        }
    }
    rec(s, vt);
}

fn reconstruct_synchronized(s: &mut Stmt) {
    match s {
        Stmt::Block(v) => {
            // Splice nested plain blocks so MonitorEnter/Try adjacency
            // holds across sub-block boundaries (switch cases, etc.).
            if v.iter().any(|x| matches!(x, Stmt::Block(_))) {
                let old = std::mem::take(v);
                for x in old {
                    match x {
                        Stmt::Block(inner) => v.extend(inner),
                        other => v.push(other),
                    }
                }
            }
            let mut i = 0;
            while i < v.len() {
                reconstruct_synchronized(&mut v[i]);
                // Pattern: MonitorEnter followed by Try with catch-all whose
                // handler exits the monitor.
                if i + 1 < v.len() {
                    if let (Stmt::MonitorEnter(_), Stmt::Try { .. }) = (&v[i], &v[i + 1]) {
                        let r = try_make_synchronized(&v[i], &v[i + 1]);
                        if std::env::var("JCDC_DBG_SYNC").is_ok() {
                            eprintln!("SYNC pair direct ok={}", r.is_some());
                        }
                        if let Some(sync) = r {
                            v[i] = Stmt::Block(vec![]);
                            v[i + 1] = sync;
                        }
                    } else if matches!(&v[i + 1], Stmt::Try { .. }) {
                        // javac may sink the monitorenter into the tail of a
                        // preceding branch (`if (...) { ...; monitorenter }`
                        // followed by the sync region). Extract a trailing
                        // MonitorEnter leaf and pair it with the Try.
                        let taken = take_trailing_monitor(&mut v[i]);
                        if std::env::var("JCDC_DBG_SYNC").is_ok() {
                            let d = format!("{:?}", &v[i]);
                            eprintln!("SYNC trailing probe i={} taken={} head={}", i, taken.is_some(), d.lines().next().unwrap_or(""));
                        }
                        if let Some(lock) = taken {
                            let enter = Stmt::MonitorEnter(lock);
                            let r2 = try_make_synchronized(&enter, &v[i + 1]);
                            if std::env::var("JCDC_DBG_SYNC").is_ok() {
                                eprintln!("SYNC trailing pair ok={}", r2.is_some());
                            }
                            if let Some(sync) = r2 {
                                v[i + 1] = sync;
                            } else {
                                // Not a sync pattern after all: put it back.
                                restore_trailing_monitor(&mut v[i], enter);
                            }
                        }
                    }
                }
                i += 1;
            }
            v.retain(|x| !x.is_empty_block());
        }
        Stmt::Try { body, catches, finally } => {
            reconstruct_synchronized(body);
            for c in catches {
                reconstruct_synchronized(&mut c.body);
            }
            if let Some(f) = finally {
                reconstruct_synchronized(f);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { reconstruct_synchronized(res); }
            reconstruct_synchronized(body);
            for c in catches {
                reconstruct_synchronized(&mut c.body);
            }
            if let Some(f) = finally {
                reconstruct_synchronized(f);
            }
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            reconstruct_synchronized(then_stmt);
            if let Some(e) = else_stmt {
                reconstruct_synchronized(e);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => reconstruct_synchronized(body),
        Stmt::For { body, .. } | Stmt::ForEach { body, .. } => reconstruct_synchronized(body),
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                // Pair matching needs sibling adjacency: wrap the case body
                // in a block so MonitorEnter+Try sequences are seen.
                let mut blk = Stmt::Block(std::mem::take(&mut c.body));
                reconstruct_synchronized(&mut blk);
                c.body = match blk {
                    Stmt::Block(v) => v,
                    other => vec![other],
                };
            }
            if let Some(d) = default {
                reconstruct_synchronized(d);
            }
        }
        Stmt::Synchronized { body, .. } => reconstruct_synchronized(body),
        _ => {}
    }
}

fn try_make_synchronized(enter: &Stmt, try_stmt: &Stmt) -> Option<Stmt> {
    if std::env::var("JCDC_DBG_SYNC").is_ok() {
        match (enter, try_stmt) {
            (Stmt::MonitorEnter(_), Stmt::Try { catches, finally, .. }) => {
                eprintln!("SYNC shape catches={} finally={} exc0={:?}", catches.len(), finally.is_some(),
                    catches.first().map(|c| c.exc.len()));
            }
            _ => eprintln!("SYNC shape enter={} try={}", matches!(enter, Stmt::MonitorEnter(_)), matches!(try_stmt, Stmt::Try{..})),
        }
    }
    let Stmt::MonitorEnter(lock) = enter else { return None };
    let Stmt::Try { body, catches, finally } = try_stmt else { return None };
    let only_exit_throw = |stmts: &[Stmt]| -> bool {
        stmts.iter().all(|h| {
            matches!(h, Stmt::MonitorExit(_))
                || matches!(h, Stmt::Throw(_))
                || matches!(h, Stmt::LocalDef { .. })
                || matches!(h, Stmt::ExprStmt(Expr::Assign { .. }))
                || h.is_empty_block()
        })
    };
    fn to_stmts(s: &Stmt) -> Vec<Stmt> {
        fn flat(s: &Stmt, out: &mut Vec<Stmt>) {
            match s {
                Stmt::Block(v) => {
                    for x in v {
                        flat(x, out);
                    }
                }
                other => out.push(other.clone()),
            }
        }
        let mut out = Vec::new();
        flat(s, &mut out);
        out.retain(|x| !x.is_empty_block());
        out
    }
    // Two accepted shapes:
    //  a) Try with a single catch-all handler of monitorexit+rethrow and no
    //     finally (the classic javac pattern), or
    //  b) Try whose finally (and/or catch-all) consists only of monitorexit
    //     (+ rethrow) — produced when the handler was already merged into a
    //     finally by earlier structuring.
    #[allow(unused_assignments)]
    let mut has_exit = false;
    match (catches.len(), finally) {
        (1, None) => {
            let c = &catches[0];
            if !c.exc.is_empty() {
                return None;
            }
            let handler_stmts = to_stmts(&c.body);
            has_exit = handler_stmts.iter().any(|h| matches!(h, Stmt::MonitorExit(_)));
            if !has_exit || !only_exit_throw(&handler_stmts) {
                return None;
            }
        }
        (0, Some(f)) | (1, Some(f)) => {
            let fin_stmts = to_stmts(f);
            let fin_exit = fin_stmts.iter().any(|h| matches!(h, Stmt::MonitorExit(_)));
            if !fin_exit || !only_exit_throw(&fin_stmts) {
                return None;
            }
            if catches.len() == 1 {
                let c = &catches[0];
                if !c.exc.is_empty() {
                    return None;
                }
                let handler_stmts = to_stmts(&c.body);
                if !only_exit_throw(&handler_stmts) {
                    return None;
                }
            }
            has_exit = true;
        }
        _ => return None,
    }
    if !has_exit {
        return None;
    }
    // Body must end with monitorexit (possibly before a trailing statement).
    let mut body_stmts = match &**body {
        Stmt::Block(v) => v.clone(),
        other => vec![other.clone()],
    };
    // Remove trailing MonitorExit statements.
    while let Some(Stmt::MonitorExit(_)) = body_stmts.last() {
        body_stmts.pop();
    }
    // Also remove interior MonitorExit on normal-flow paths (single-level).
    body_stmts.retain(|x| !matches!(x, Stmt::MonitorExit(_)));
    Some(Stmt::Synchronized { lock: lock.clone(), body: Box::new(Stmt::Block(body_stmts)) })
}

/// Structural cleanup: flatten nested plain blocks, drop empties, merge
/// single-statement blocks where safe.
fn cleanup(s: &mut Stmt) {
    match s {
        Stmt::Block(v) => {
            for x in v.iter_mut() {
                cleanup(x);
            }
            // flatten nested blocks that are pure sequences
            let mut out: Vec<Stmt> = Vec::new();
            for x in v.drain(..) {
                match x {
                    Stmt::Block(inner) => out.extend(inner),
                    other => out.push(other),
                }
            }
            out.retain(|x| !x.is_empty_block());
            *v = out;
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            cleanup(then_stmt);
            if let Some(e) = else_stmt {
                cleanup(e);
            }
        }
        Stmt::Try { body, catches, finally } => {
            // A try with no catch and no finally is not valid Java; it can
            // be left behind by handler-removal passes — unwrap the body.
            if catches.is_empty() && finally.is_none() {
                let inner = std::mem::replace(body.as_mut(), Stmt::Block(vec![]));
                *s = inner;
                cleanup(s);
                return;
            }
            cleanup(body);
            for c in catches {
                cleanup(&mut c.body);
            }
            if let Some(f) = finally {
                cleanup(f);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { cleanup(res); }
            cleanup(body);
            for c in catches {
                cleanup(&mut c.body);
            }
            if let Some(f) = finally {
                cleanup(f);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => cleanup(body),
        Stmt::For { body, init, .. } => {
            for i in init {
                cleanup(i);
            }
            cleanup(body);
        }
        Stmt::ForEach { body, .. } => cleanup(body),
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                for st in c.body.iter_mut() {
                    cleanup(st);
                }
            }
            if let Some(d) = default {
                cleanup(d);
            }
        }
        Stmt::Synchronized { body, .. } => cleanup(body),
        _ => {}
    }
    if let Stmt::Block(v) = s {
        if v.len() == 1 {
            if matches!(v[0], Stmt::Block(_)) {
                *s = v.pop().unwrap();
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Stack variable hoisting
// ---------------------------------------------------------------------------

/// Convert stack-variable `LocalDef`s into plain assignments and insert one
/// bare declaration per used stack variable at the top of the method body.
/// Single traversal; declarations at method top are always scope-correct.
#[allow(dead_code)]
fn hoist_stack_var(_body: &mut Stmt, vars: &[u32]) {
    let _ = vars;
}

fn hoist_stack_vars(body: &mut Stmt, vars: &[u32]) {
    if vars.is_empty() {
        return;
    }
    let varset: std::collections::HashSet<u32> = vars.iter().copied().collect();
    let mut used: std::collections::HashSet<u32> = std::collections::HashSet::new();
    convert_defs_and_collect(body, &varset, &mut used);
    // Vars declared as try-with-resources keep their declaration there;
    // hoisting a second bare declaration would shadow-conflict.
    let mut res_vars: std::collections::HashSet<u32> = std::collections::HashSet::new();
    fn collect_res_vars(s: &Stmt, out: &mut std::collections::HashSet<u32>) {
        match s {
            Stmt::TryWithResources { resources, body, catches, finally } => {
                for r in resources {
                    if let Stmt::LocalDef { var, .. } = r {
                        out.insert(*var);
                    }
                }
                collect_res_vars(body, out);
                for c in catches {
                    collect_res_vars(&c.body, out);
                }
                if let Some(f) = finally {
                    collect_res_vars(f, out);
                }
            }
            Stmt::Block(v) => v.iter().for_each(|x| collect_res_vars(x, out)),
            Stmt::If { then_stmt, else_stmt, .. } => {
                collect_res_vars(then_stmt, out);
                if let Some(e) = else_stmt {
                    collect_res_vars(e, out);
                }
            }
            Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => collect_res_vars(body, out),
            Stmt::For { init, body, .. } => {
                init.iter().for_each(|i| collect_res_vars(i, out));
                collect_res_vars(body, out);
            }
            Stmt::ForEach { body, .. } => collect_res_vars(body, out),
            Stmt::Switch { cases, default, .. } => {
                for c in cases {
                    c.body.iter().for_each(|x| collect_res_vars(x, out));
                }
                if let Some(d) = default {
                    collect_res_vars(d, out);
                }
            }
            Stmt::Try { body, catches, finally } => {
                collect_res_vars(body, out);
                for c in catches {
                    collect_res_vars(&c.body, out);
                }
                if let Some(f) = finally {
                    collect_res_vars(f, out);
                }
            }
            Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => {
                collect_res_vars(body, out)
            }
            _ => {}
        }
    }
    collect_res_vars(body, &mut res_vars);
    used.retain(|v| !res_vars.contains(v));
    if used.is_empty() {
        return;
    }
    let mut decls: Vec<Stmt> = used.into_iter().map(bare_def).collect();
    decls.sort_by_key(|s| match s {
        Stmt::LocalDef { var, .. } => *var,
        _ => 0,
    });
    prepend_decls(body, decls);
}

/// A merge variable whose every assigned value is `this` carries no
/// information: replace its reads with `this` and drop the assignments.
/// Qualified `v.field = x` writes through such a variable are illegal for
/// final fields in constructors (JLS definite assignment only accepts
/// plain `field = x` / `this.field = x`), so the rewrite is required for
/// recompilation, not just cosmetics.
fn fold_this_stack_vars(body: &mut Stmt, vt: &VarTable, stack_vars: &[u32]) {
    use std::collections::HashMap;
    if stack_vars.is_empty() {
        return;
    }
    // Phase 1: gather every assigned value per stack var.
    let mut vals: HashMap<u32, Vec<bool>> = HashMap::new();
    fn collect(s: &Stmt, vals: &mut HashMap<u32, Vec<bool>>) {
        match s {
            Stmt::Block(v) => v.iter().for_each(|x| collect(x, vals)),
            Stmt::LocalDef { var, init: Some(e), .. } => {
                vals.entry(*var).or_default().push(matches!(e, Expr::This));
            }
            Stmt::ExprStmt(Expr::Assign { target, value, .. }) => {
                if let Expr::Local { var, .. } = &**target {
                    vals.entry(*var).or_default().push(matches!(&**value, Expr::This));
                }
                collect_value(value, vals);
            }
            Stmt::If { cond, then_stmt, else_stmt } => {
                collect_value(cond, vals);
                collect(then_stmt, vals);
                if let Some(e) = else_stmt {
                    collect(e, vals);
                }
            }
            Stmt::While { cond, body } | Stmt::DoWhile { body, cond } => {
                collect_value(cond, vals);
                collect(body, vals);
            }
            Stmt::For { init, cond, update, body } => {
                init.iter().for_each(|i| collect(i, vals));
                if let Some(c) = cond {
                    collect_value(c, vals);
                }
                update.iter().for_each(|u| collect_value(u, vals));
                collect(body, vals);
            }
            Stmt::ForEach { iterable, body, .. } => {
                collect_value(iterable, vals);
                collect(body, vals);
            }
            Stmt::Switch { selector, cases, default, .. } => {
                collect_value(selector, vals);
                for c in cases {
                    c.body.iter().for_each(|x| collect(x, vals));
                }
                if let Some(d) = default {
                    collect(d, vals);
                }
            }
            Stmt::Try { body, catches, finally } => {
                collect(body, vals);
                for c in catches {
                    collect(&c.body, vals);
                }
                if let Some(f) = finally {
                    collect(f, vals);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                for res in resources.iter() { collect(res, vals); }
                collect(body, vals);
                for c in catches {
                    collect(&c.body, vals);
                }
                if let Some(f) = finally {
                    collect(f, vals);
                }
            }
            Stmt::Synchronized { lock, body } => {
                collect_value(lock, vals);
                collect(body, vals);
            }
            Stmt::Labeled { body, .. } => collect(body, vals),
            Stmt::Return(e) => {
                if let Some(x) = e {
                    collect_value(x, vals);
                }
            }
            Stmt::Throw(e) => collect_value(e, vals),
            _ => {}
        }
    }
    // Assignments embedded in expressions (rare) disqualify the var.
    fn collect_value(_e: &Expr, _vals: &mut HashMap<u32, Vec<bool>>) {}
    collect(body, &mut vals);

    let this_only: std::collections::HashSet<u32> = stack_vars
        .iter()
        .filter(|v| {
            vals.get(v).map(|vs| !vs.is_empty() && vs.iter().all(|&b| b)).unwrap_or(false)
        })
        .copied()
        .collect();
    let _ = vt;
    if this_only.is_empty() {
        return;
    }
    // Phase 2: drop the assignments and rewrite reads to `this`.
    fn rewrite(s: &mut Stmt, set: &std::collections::HashSet<u32>) {
        match s {
            Stmt::Block(v) => {
                for x in v.iter_mut() {
                    rewrite(x, set);
                }
                v.retain(|x| !x.is_empty_block());
            }
            Stmt::LocalDef { var, init, .. } => {
                if set.contains(var) && init.is_some() {
                    *s = Stmt::Block(vec![]);
                    return;
                }
                if let Some(e) = init {
                    rw_expr(e, set);
                }
            }
            Stmt::ExprStmt(e) => {
                let drop = matches!(e, Expr::Assign { target, .. }
                    if matches!(&**target, Expr::Local { var, .. } if set.contains(var)));
                if drop {
                    *s = Stmt::Block(vec![]);
                    return;
                }
                rw_expr(e, set);
            }
            Stmt::If { cond, then_stmt, else_stmt } => {
                rw_expr(cond, set);
                rewrite(then_stmt, set);
                if let Some(e) = else_stmt {
                    rewrite(e, set);
                }
            }
            Stmt::While { cond, body } | Stmt::DoWhile { body, cond } => {
                rw_expr(cond, set);
                rewrite(body, set);
            }
            Stmt::For { init, cond, update, body } => {
                init.iter_mut().for_each(|i| rewrite(i, set));
                if let Some(c) = cond {
                    rw_expr(c, set);
                }
                update.iter_mut().for_each(|u| rw_expr(u, set));
                rewrite(body, set);
            }
            Stmt::ForEach { iterable, body, .. } => {
                rw_expr(iterable, set);
                rewrite(body, set);
            }
            Stmt::Switch { selector, cases, default, .. } => {
                rw_expr(selector, set);
                for c in cases.iter_mut() {
                    c.body.iter_mut().for_each(|x| rewrite(x, set));
                }
                if let Some(d) = default {
                    rewrite(d, set);
                }
            }
            Stmt::Try { body, catches, finally } => {
                rewrite(body, set);
                for c in catches.iter_mut() {
                    rewrite(&mut c.body, set);
                }
                if let Some(f) = finally {
                    rewrite(f, set);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                for res in resources.iter_mut() { rewrite(res, set); }
                rewrite(body, set);
                for c in catches.iter_mut() {
                    rewrite(&mut c.body, set);
                }
                if let Some(f) = finally {
                    rewrite(f, set);
                }
            }
            Stmt::Synchronized { lock, body } => {
                rw_expr(lock, set);
                rewrite(body, set);
            }
            Stmt::Labeled { body, .. } => rewrite(body, set),
            Stmt::Return(e) => {
                if let Some(x) = e {
                    rw_expr(x, set);
                }
            }
            Stmt::Throw(e) => rw_expr(e, set),
            _ => {}
        }
    }
    fn rw_expr(e: &mut Expr, set: &std::collections::HashSet<u32>) {
        if let Expr::Local { var, .. } = e {
            if set.contains(var) {
                *e = Expr::This;
                return;
            }
        }
        match e {
            Expr::Method { owner, args, .. } => {
                if let Some(o) = owner {
                    rw_expr(o, set);
                }
                args.iter_mut().for_each(|a| rw_expr(a, set));
            }
            Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
                args.iter_mut().for_each(|a| rw_expr(a, set));
            }
            Expr::Field { owner: Some(o), .. } => rw_expr(o, set),
            Expr::ArrayIndex { array, index } => {
                rw_expr(array, set);
                rw_expr(index, set);
            }
            Expr::Cast { e: i, .. } | Expr::InstanceOf { e: i, .. } | Expr::Un { e: i, .. }
            | Expr::PreIncDec { e: i, .. } | Expr::PostIncDec { e: i, .. } => rw_expr(i, set),
            Expr::Bin { l, r, .. } => {
                rw_expr(l, set);
                rw_expr(r, set);
            }
            Expr::Cond { c, t, f } => {
                rw_expr(c, set);
                rw_expr(t, set);
                rw_expr(f, set);
            }
            Expr::Assign { target, value, .. } => {
                rw_expr(target, set);
                rw_expr(value, set);
            }
            Expr::NewArray { dims, init, .. } => {
                dims.iter_mut().for_each(|d| rw_expr(d, set));
                if let Some(vals) = init {
                    vals.iter_mut().for_each(|v| rw_expr(v, set));
                }
            }
            Expr::StringConcat(parts) => parts.iter_mut().for_each(|p| {
                if let crate::expr::ConcatPart::Str(i) = p {
                    rw_expr(i, set);
                }
            }),
            Expr::Lambda(l) => l.captures.iter_mut().for_each(|c| rw_expr(c, set)),
            Expr::Invokedynamic { args, .. } => args.iter_mut().for_each(|a| rw_expr(a, set)),
            _ => {}
        }
    }
    rewrite(body, &this_only);
}

/// Prepend declarations to a body, but never before a leading super()/
/// this() call: statements before the delegation are illegal before
/// Java 25 ("flexible constructors").
fn prepend_decls(body: &mut Stmt, mut decls: Vec<Stmt>) {
    if decls.is_empty() {
        return;
    }
    match body {
        Stmt::Block(v) => {
            let lead = match v.first() {
                Some(Stmt::ExprStmt(Expr::Method { name, .. })) if name == "<init>" => 1,
                _ => 0,
            };
            let mut out: Vec<Stmt> = v.drain(..lead).collect();
            out.append(&mut decls);
            out.append(v);
            *v = out;
        }
        other => {
            let old = std::mem::replace(other, Stmt::Block(vec![]));
            decls.push(old);
            *other = Stmt::Block(decls);
        }
    }
}

fn bare_def(v: u32) -> Stmt {
    Stmt::LocalDef { var: v, init: None, is_final: false, force_type: true }
}

/// One traversal: rewrite LocalDef(stack var) → assignment, record used vars.
fn convert_defs_and_collect(s: &mut Stmt, vars: &std::collections::HashSet<u32>, used: &mut std::collections::HashSet<u32>) {
    if let Stmt::LocalDef { var, init: Some(e), .. } = s {
        if vars.contains(var) {
            let v = *var;
            let val = std::mem::replace(e, Expr::Const(crate::expr::ConstVal::Null));
            *s = Stmt::ExprStmt(Expr::Assign {
                target: Box::new(Expr::Local { var: v, ty: crate::expr::TypeRef::J(jcdc_jvm::JavaType::Int) }),
                op: crate::expr::AssignOp::Plain,
                value: Box::new(val),
            });
        }
    }
    // collect refs from expressions and recurse
    match s {
        Stmt::Block(v) => v.iter_mut().for_each(|x| convert_defs_and_collect(x, vars, used)),
        Stmt::ExprStmt(e) => collect_expr(e, vars, used),
        Stmt::LocalDef { var, init, .. } => {
            if vars.contains(var) {
                used.insert(*var);
            }
            if let Some(e) = init {
                collect_expr(e, vars, used);
            }
        }
        Stmt::Return(e) => {
            if let Some(x) = e {
                collect_expr(x, vars, used);
            }
        }
        Stmt::Throw(e) => collect_expr(e, vars, used),
        Stmt::If { cond, then_stmt, else_stmt } => {
            collect_expr(cond, vars, used);
            convert_defs_and_collect(then_stmt, vars, used);
            if let Some(x) = else_stmt {
                convert_defs_and_collect(x, vars, used);
            }
        }
        Stmt::While { cond, body } => {
            collect_expr(cond, vars, used);
            convert_defs_and_collect(body, vars, used);
        }
        Stmt::DoWhile { body, cond } => {
            convert_defs_and_collect(body, vars, used);
            collect_expr(cond, vars, used);
        }
        Stmt::For { init, cond, update, body } => {
            init.iter_mut().for_each(|i| convert_defs_and_collect(i, vars, used));
            if let Some(c) = cond {
                collect_expr(c, vars, used);
            }
            update.iter_mut().for_each(|u| collect_expr(u, vars, used));
            convert_defs_and_collect(body, vars, used);
        }
        Stmt::ForEach { var, iterable, body, .. } => {
            if vars.contains(var) {
                used.insert(*var);
            }
            collect_expr(iterable, vars, used);
            convert_defs_and_collect(body, vars, used);
        }
        Stmt::Switch { selector, cases, default, .. } => {
            collect_expr(selector, vars, used);
            for c in cases {
                c.body.iter_mut().for_each(|st| convert_defs_and_collect(st, vars, used));
            }
            if let Some(d) = default {
                convert_defs_and_collect(d, vars, used);
            }
        }
        Stmt::Try { body, catches, finally } => {
            convert_defs_and_collect(body, vars, used);
            for c in catches {
                convert_defs_and_collect(&mut c.body, vars, used);
            }
            if let Some(f) = finally {
                convert_defs_and_collect(f, vars, used);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            // Resource LocalDefs ARE the declaration site; hoisting them
            // would emit `try ()` plus a duplicate bare declaration. Only
            // walk their initializers for references.
            for res in resources.iter_mut() {
                if let Stmt::LocalDef { init: Some(e), .. } = res {
                    collect_expr(e, vars, used);
                } else {
                    convert_defs_and_collect(res, vars, used);
                }
            }
            convert_defs_and_collect(body, vars, used);
            for c in catches {
                convert_defs_and_collect(&mut c.body, vars, used);
            }
            if let Some(f) = finally {
                convert_defs_and_collect(f, vars, used);
            }
        }
        Stmt::Synchronized { lock, body } => {
            collect_expr(lock, vars, used);
            convert_defs_and_collect(body, vars, used);
        }
        Stmt::MonitorEnter(e) | Stmt::MonitorExit(e) => collect_expr(e, vars, used),
        _ => {}
    }
}

fn collect_expr(e: &Expr, vars: &std::collections::HashSet<u32>, used: &mut std::collections::HashSet<u32>) {
    if let Expr::Local { var, .. } = e {
        if vars.contains(var) {
            used.insert(*var);
        }
    }
    expr_refs_var_walk(e, vars, used);
}

fn expr_refs_var_walk(e: &Expr, vars: &std::collections::HashSet<u32>, used: &mut std::collections::HashSet<u32>) {
    match e {
        Expr::Local { var, .. } => {
            if vars.contains(var) {
                used.insert(*var);
            }
        }
        Expr::Const(_) | Expr::This | Expr::Raw(_) | Expr::RawT(..) => {}
        Expr::New { args, .. } | Expr::AnonNew { args, .. } => args.iter().for_each(|a| expr_refs_var_walk(a, vars, used)),
        Expr::NewArray { dims, init, .. } => {
            dims.iter().for_each(|d| expr_refs_var_walk(d, vars, used));
            if let Some(vals) = init {
                vals.iter().for_each(|v| expr_refs_var_walk(v, vars, used));
            }
        }
        Expr::NewMultiArray { dims, .. } => dims.iter().for_each(|d| expr_refs_var_walk(d, vars, used)),
        Expr::Field { owner: Some(o), .. } => expr_refs_var_walk(o, vars, used),
        Expr::Field { .. } => {}
        Expr::Method { owner, args, .. } => {
            if let Some(o) = owner {
                expr_refs_var_walk(o, vars, used);
            }
            args.iter().for_each(|a| expr_refs_var_walk(a, vars, used));
        }
        Expr::ArrayIndex { array, index } => {
            expr_refs_var_walk(array, vars, used);
            expr_refs_var_walk(index, vars, used);
        }
        Expr::Cast { e, .. } | Expr::InstanceOf { e, .. } | Expr::Un { e, .. } => expr_refs_var_walk(e, vars, used),
        Expr::Bin { l, r, .. } => {
            expr_refs_var_walk(l, vars, used);
            expr_refs_var_walk(r, vars, used);
        }
        Expr::Cond { c, t, f } => {
            expr_refs_var_walk(c, vars, used);
            expr_refs_var_walk(t, vars, used);
            expr_refs_var_walk(f, vars, used);
        }
        Expr::Assign { target, value, .. } => {
            expr_refs_var_walk(target, vars, used);
            expr_refs_var_walk(value, vars, used);
        }
        Expr::PreIncDec { e, .. } | Expr::PostIncDec { e, .. } => expr_refs_var_walk(e, vars, used),
        Expr::Lambda(l) => l.captures.iter().for_each(|c| expr_refs_var_walk(c, vars, used)),
        Expr::StringConcat(parts) => parts.iter().for_each(|p| {
            if let crate::expr::ConcatPart::Str(inner) = p {
                expr_refs_var_walk(inner, vars, used);
            }
        }),
        Expr::Invokedynamic { args, .. } => args.iter().for_each(|a| expr_refs_var_walk(a, vars, used)),
    }
}



// ---------------------------------------------------------------------------
// Type inference for synthetic variables
// ---------------------------------------------------------------------------

#[derive(Clone)]
enum Evidence {
    T(JavaType),
    /// Assignment of `this`: the value type is the enclosing class, which
    /// must not be confused with the plain-Object unknown marker.
    OfThis,
    BoolCandidate,
}

fn infer_var_types(vt: &mut VarTable, body: &mut Stmt, ret_ty: &JavaType, pc: &PoolClass) {
    let n = vt.vars.len();
    let mut ev: Vec<Vec<Evidence>> = vec![Vec::new(); n];
    let mut bool_vars: std::collections::HashSet<u32> = std::collections::HashSet::new();
    gather_evidence(body, &mut ev, ret_ty, &mut bool_vars);
    let mut changed: Vec<Option<JavaType>> = vec![None; n];
    for (v, evs) in ev.iter().enumerate() {
        if !vt.vars[v].synthetic_name || vt.vars[v].is_param {
            continue;
        }
        let types: Vec<&JavaType> = evs
            .iter()
            .filter_map(|e| match e {
                Evidence::T(t) => Some(t),
                _ => None,
            })
            .collect();
        let has_bool_ev = types.iter().any(|t| matches!(t, JavaType::Boolean));
        let only_int_bool = !types.is_empty()
            && types
                .iter()
                .all(|t| matches!(t, JavaType::Int | JavaType::Boolean));
        let inferred = if (bool_vars.contains(&(v as u32))
            && types.iter().all(|t| matches!(t, JavaType::Int))
            && !types.is_empty())
            || (has_bool_ev && only_int_bool)
        {
            Some(JavaType::Boolean)
        } else {
            combine_types(&types)
        };
        if let Some(t) = inferred {
            if t != JavaType::Int || vt.vars[v].ty.erased() == JavaType::Int {
                changed[v] = Some(t);
            }
        }
    }
    for (v, t) in changed.iter().enumerate() {
        if let Some(t) = t {
            let old = vt.vars[v].ty.erased();
            if std::env::var("JCDC_DBG_MERGE").is_ok() && vt.stack_vars.contains(&(v as u32)) {
                eprintln!("INFER stackvar v={} old={:?} t={:?} wide={}", v, old, t, vt.wide_stack_vars.contains(&(v as u32)));
            }
            if vt.wide_stack_vars.contains(&(v as u32)) {
                // Branches disagreed (or carried a generic/Object value);
                // keep the wide type so every assignment type-checks —
                // unless every observed value has one concrete type (plus
                // nulls): then narrowing is safe and often required
                // (`return stackN;` against a typed return).
                // `this` carries the enclosing class type, not Object.
                let ev_types: Vec<JavaType> = ev[v]
                    .iter()
                    .filter_map(|e| match e {
                        Evidence::T(t) => Some(t.clone()),
                        Evidence::OfThis => Some(JavaType::Object(pc.internal_name.clone())),
                        _ => None,
                    })
                    .collect();
                let ev_types: Vec<&JavaType> = ev_types.iter().collect();
                let plain_object = |t: &&JavaType| {
                    matches!(t, JavaType::Object(n) if n == "java/lang/Object")
                };
                let uniform = ev_types.windows(2).all(|w| w[0] == w[1]);
                // Array covariance: `return sharedTail;` merges e.g. Class[]
                // and Type[] branch values; when the method return type is
                // an array and every observed value is an array, the return
                // type accepts them all.
                let covariant_ret_array = matches!(ret_ty, JavaType::Array(_))
                    && !ev_types.is_empty()
                    && ev_types.iter().all(|t| matches!(t, JavaType::Array(_)));
                let concrete = !ev_types.is_empty()
                    && !ev_types.iter().any(plain_object)
                    && (uniform || covariant_ret_array);
                if std::env::var("JCDC_DBG_MERGE").is_ok() {
                    eprintln!("WIDENARROW v={} ev={:?} concrete={}", v, ev_types, concrete);
                }
                if !concrete {
                    continue;
                }
            }
            let newt = if vt.stack_vars.contains(&(v as u32)) {
                // Explicit boolean inference (return/branch context) wins
                // over the 0/1-carrying Int merge type.
                if matches!(t, JavaType::Boolean) && matches!(old, JavaType::Int) {
                    JavaType::Boolean
                } else if vt.wide_stack_vars.contains(&(v as u32)) {
                    // Widened merges narrowed here take the evidence type
                    // directly; joining with the plain-Object placeholder
                    // could miss array covariance.
                    t.clone()
                } else {
                    join_types(&old, t)
                }
            } else {
                t.clone()
            };
            if std::env::var("JCDC_DBG_MERGE").is_ok() && vt.stack_vars.contains(&(v as u32)) {
                eprintln!("INFER-SET v={} newt={:?}", v, newt);
            }
            vt.vars[v].ty = TypeRef::J(newt);
        }
    }
    // Slot-reuse splitting: a synthetic local that receives values of
    // different concrete types over time (javac reuses the slot) must
    // become distinct variables, or emission loses array/exception types.
    split_reassigned_synthetic(vt, body);
    // Boolean propagation through plain copies: `boolean b = w;` (or
    // `b = w;`) makes an int-typed synthetic source variable boolean, so
    // its 0/1 stores print as false/true.
    for _ in 0..4 {
        let mut changed2 = false;
        propagate_bool_copies(body, vt, &mut changed2);
        if !changed2 {
            break;
        }
    }
    if std::env::var("JCDC_DBG_MERGE").is_ok() {
        for v in &vt.stack_vars {
            eprintln!("POSTINFER stackvar v={} ty={:?}", v, vt.vars[*v as usize].ty);
        }
    }
    // Rewrite embedded Local types.
    let types: Vec<TypeRef> = vt.vars.iter().map(|vi| vi.ty.clone()).collect();
    rewrite_local_types(body, &types);
}

/// `byte b = intExpr;` — the JVM computes byte/short/char values as ints;
/// when the declared target is narrower, source needs an explicit
/// narrowing cast (constants in range are already legal without one).
fn cast_narrowing_assigns(vt: &VarTable, s: &mut Stmt) {
    fn narrow(t: &JavaType) -> bool {
        matches!(t, JavaType::Byte | JavaType::Short | JavaType::Char)
    }
    fn fix(value: &mut Expr, want: &JavaType) {
        // Conditionals included: `byte b = c ? 5 : 9;` is a LOSSY int
        // conditional even though both constants fit — the source worked
        // because the branches were byte-typed CONSTANT VARIABLES
        // (jdk17 MemberName `clazz.isInterface() ? REF_invokeInterface :
        // REF_invokeVirtual`); with the constants inlined the whole
        // conditional needs the narrowing cast.
        if !matches!(value, Expr::Local { .. } | Expr::Method { .. } | Expr::Field { .. } | Expr::ArrayIndex { .. } | Expr::Cond { .. }) {
            return;
        }
        if value.type_ref().erased() != JavaType::Int {
            return;
        }
        if matches!(value, Expr::Cast { .. }) {
            return;
        }
        let inner = std::mem::replace(value, Expr::This);
        *value = Expr::Cast { ty: TypeRef::J(want.clone()), e: Box::new(inner) };
    }
    fn rec(s: &mut Stmt, vt: &VarTable) {
        match s {
            Stmt::Block(v) => v.iter_mut().for_each(|x| rec(x, vt)),
            Stmt::LocalDef { var, init: Some(e), .. } => {
                let t = vt.var(*var).ty.erased();
                if narrow(&t) {
                    fix(e, &t);
                }
            }
            Stmt::ExprStmt(Expr::Assign { target, value, .. }) => {
                let t = match &**target {
                    Expr::Local { var, .. } => vt.var(*var).ty.erased(),
                    Expr::ArrayIndex { array, .. } => match array.type_ref().erased() {
                        JavaType::Array(elem) => *elem,
                        _ => return,
                    },
                    _ => return,
                };
                if narrow(&t) {
                    fix(value, &t);
                }
            }
            Stmt::If { then_stmt, else_stmt, .. } => {
                rec(then_stmt, vt);
                if let Some(e) = else_stmt {
                    rec(e, vt);
                }
            }
            Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => rec(body, vt),
            Stmt::For { init, body, .. } => {
                init.iter_mut().for_each(|i| rec(i, vt));
                rec(body, vt);
            }
            Stmt::ForEach { body, .. } => rec(body, vt),
            Stmt::Switch { cases, default, .. } => {
                for c in cases.iter_mut() {
                    c.body.iter_mut().for_each(|x| rec(x, vt));
                }
                if let Some(d) = default {
                    rec(d, vt);
                }
            }
            Stmt::Try { body, catches, finally } => {
                rec(body, vt);
                for c in catches.iter_mut() {
                    rec(&mut c.body, vt);
                }
                if let Some(f) = finally {
                    rec(f, vt);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                for r in resources.iter_mut() {
                    rec(r, vt);
                }
                rec(body, vt);
                for c in catches.iter_mut() {
                    rec(&mut c.body, vt);
                }
                if let Some(f) = finally {
                    rec(f, vt);
                }
            }
            Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => rec(body, vt),
            _ => {}
        }
    }
    rec(s, vt);
}

/// `return stackN;` where the merge variable stayed wide Object but the
/// method returns a concrete reference type: the bytecode verifier
/// guarantees the value is assignable, so an erased cast always holds.
fn cast_object_returns(s: &mut Stmt, ret_ty: &JavaType) {
    let want = match ret_ty {
        JavaType::Object(n) if n != "java/lang/Object" => ret_ty.clone(),
        JavaType::Array(_) => ret_ty.clone(),
        _ => return,
    };
    fn fix(e: &mut Expr, want: &JavaType) {
        // Only plain value reads (locals/merge vars, calls, field reads):
        // casting a lambda or a lambda-bearing conditional would take it
        // out of its poly-expression context.
        if !matches!(e, Expr::Local { .. } | Expr::Method { .. } | Expr::Field { .. } | Expr::ArrayIndex { .. }) {
            return;
        }
        // A generically-typed value (typevar/parameterized) is NOT a plain
        // Object even though a typevar's erasure renders as one: casting
        // `return castResult` (M extends Map<K,D>) to the descriptor
        // erasure produced `return (Map) castResult` inside the groupingBy
        // finisher lambda — Map无法转换为M (jdk17 Collectors x2, x2 per
        // tree with groupingByConcurrent).
        if matches!(e.type_ref(), TypeRef::G(_)) {
            return;
        }
        if e.type_ref().erased() == JavaType::Object("java/lang/Object".into()) {
            let inner = std::mem::replace(e, Expr::This);
            *e = Expr::Cast { ty: TypeRef::J(want.clone()), e: Box::new(inner) };
        }
    }
    fn rec(s: &mut Stmt, want: &JavaType) {
        match s {
            Stmt::Block(v) => v.iter_mut().for_each(|x| rec(x, want)),
            Stmt::Return(Some(e)) => fix(e, want),
            Stmt::If { then_stmt, else_stmt, .. } => {
                rec(then_stmt, want);
                if let Some(e) = else_stmt {
                    rec(e, want);
                }
            }
            Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => rec(body, want),
            Stmt::For { init, body, .. } => {
                init.iter_mut().for_each(|i| rec(i, want));
                rec(body, want);
            }
            Stmt::ForEach { body, .. } => rec(body, want),
            Stmt::Switch { cases, default, .. } => {
                for c in cases.iter_mut() {
                    c.body.iter_mut().for_each(|x| rec(x, want));
                }
                if let Some(d) = default {
                    rec(d, want);
                }
            }
            Stmt::Try { body, catches, finally } => {
                rec(body, want);
                for c in catches.iter_mut() {
                    rec(&mut c.body, want);
                }
                if let Some(f) = finally {
                    rec(f, want);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                for r in resources.iter_mut() {
                    rec(r, want);
                }
                rec(body, want);
                for c in catches.iter_mut() {
                    rec(&mut c.body, want);
                }
                if let Some(f) = finally {
                    rec(f, want);
                }
            }
            Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => rec(body, want),
            _ => {}
        }
    }
    rec(s, &want);
}

fn propagate_bool_copies(s: &Stmt, vt: &mut VarTable, changed: &mut bool) {
    fn note(target: &Expr, value: &Expr, vt: &mut VarTable, changed: &mut bool) {
        if let (Expr::Local { var: tv, .. }, Expr::Local { var: vv, .. }) = (target, value) {
            let t_bool = matches!(vt.vars[*tv as usize].ty.erased(), JavaType::Boolean);
            let v_int = matches!(vt.vars[*vv as usize].ty.erased(), JavaType::Int);
            if t_bool && v_int && vt.vars[*vv as usize].synthetic_name {
                vt.vars[*vv as usize].ty = TypeRef::J(JavaType::Boolean);
                *changed = true;
            }
        }
    }
    match s {
        Stmt::Block(v) => {
            for x in v.iter() {
                propagate_bool_copies(x, vt, changed);
            }
        }
        Stmt::LocalDef { init: Some(e), .. } => {
            let target = Expr::Local {
                var: match s {
                    Stmt::LocalDef { var, .. } => *var,
                    _ => unreachable!(),
                },
                ty: TypeRef::J(JavaType::Int),
            };
            note(&target, e, vt, changed);
        }
        Stmt::ExprStmt(Expr::Assign { target, value, op: crate::expr::AssignOp::Plain, .. }) => {
            note(target, value, vt, changed);
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            propagate_bool_copies(then_stmt, vt, changed);
            if let Some(e) = else_stmt {
                propagate_bool_copies(e, vt, changed);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => {
            propagate_bool_copies(body, vt, changed)
        }
        Stmt::For { init, body, .. } => {
            for i in init {
                propagate_bool_copies(i, vt, changed);
            }
            propagate_bool_copies(body, vt, changed);
        }
        Stmt::ForEach { body, .. } => propagate_bool_copies(body, vt, changed),
        Stmt::Try { body, catches, finally } => {
            propagate_bool_copies(body, vt, changed);
            for c in catches {
                propagate_bool_copies(&c.body, vt, changed);
            }
            if let Some(f) = finally {
                propagate_bool_copies(f, vt, changed);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter() { propagate_bool_copies(res, vt, changed); }
            propagate_bool_copies(body, vt, changed);
            for c in catches {
                propagate_bool_copies(&c.body, vt, changed);
            }
            if let Some(f) = finally {
                propagate_bool_copies(f, vt, changed);
            }
        }
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                for st in &c.body {
                    propagate_bool_copies(st, vt, changed);
                }
            }
            if let Some(d) = default {
                propagate_bool_copies(d, vt, changed);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => {
            propagate_bool_copies(body, vt, changed)
        }
        _ => {}
    }
}

fn combine_types(types: &[&JavaType]) -> Option<JavaType> {
    if types.is_empty() {
        return None;
    }
    let mut acc: Option<JavaType> = None;
    // A join that fell back to plain Object from two CONCRETE types is a
    // true LUB — later joins must not "recover" concreteness from it
    // (the plain-Object placeholder rule would join lub(Iterator,
    // KeyStore)=Object with the next KeyStore evidence into KeyStore,
    // typing jdk11 KeyStore.getInstance's iterator gap var as KeyStore).
    let mut lub_object = false;
    let plain_object = |t: &JavaType| matches!(t, JavaType::Object(n) if n == "java/lang/Object");
    for t in types {
        acc = Some(match acc {
            None => (*t).clone(),
            Some(a) => {
                let j = join_types(&a, t);
                if plain_object(&j) && !plain_object(&a) && !plain_object(t) {
                    lub_object = true;
                }
                j
            }
        });
    }
    if lub_object {
        return Some(JavaType::Object("java/lang/Object".into()));
    }
    acc
}

fn join_types(a: &JavaType, b: &JavaType) -> JavaType {
    use JavaType::*;
    if a == b {
        return a.clone();
    }
    // `java/lang/Throwable` only appears as the conservative type of a
    // rethrow; any concrete exception type is narrower, so prefer it.
    if matches!(a, Object(n) if n == "java/lang/Throwable") {
        return b.clone();
    }
    if matches!(b, Object(n) if n == "java/lang/Throwable") {
        return a.clone();
    }
    let num_rank = |t: &JavaType| -> i8 {
        match t {
            Boolean | Byte | Char | Short | Int => 1,
            Long => 2,
            Float => 3,
            Double => 4,
            _ => -1,
        }
    };
    let (ra, rb) = (num_rank(a), num_rank(b));
    if ra >= 1 && rb >= 1 {
        return if ra >= rb { a.clone() } else { b.clone() };
    }
    if matches!(a, Object(_) | Array(_)) && matches!(b, Object(_) | Array(_)) {
        if a == b {
            return a.clone();
        }
        // A plain java/lang/Object value (null literal, `this` before
        // class typing, uninitialized placeholder) joins anything: the
        // other side carries the real information.
        if let Object(n) = a {
            if n == "java/lang/Object" {
                return b.clone();
            }
        }
        if let Object(n) = b {
            if n == "java/lang/Object" {
                return a.clone();
            }
        }
        // no hierarchy access here; fall back to Object
        return Object("java/lang/Object".into());
    }
    // numeric mixed with reference: the numeric side is a placeholder
    if matches!(a, Object(_) | Array(_)) && rb == -1 {
        return a.clone();
    }
    if matches!(b, Object(_) | Array(_)) && ra == -1 {
        return b.clone();
    }
    a.clone()
}

fn gather_evidence(
    s: &Stmt,
    ev: &mut Vec<Vec<Evidence>>,
    ret_ty: &JavaType,
    bool_vars: &mut std::collections::HashSet<u32>,
) {
    match s {
        Stmt::Block(v) => v.iter().for_each(|x| gather_evidence(x, ev, ret_ty, bool_vars)),
        Stmt::ExprStmt(e) => gather_expr(e, ev, None, bool_vars),
        Stmt::LocalDef { var, init, .. } => {
            if let Some(e) = init {
                // A null literal carries no type information; pushing its
                // erased Object type would poison the join for variables
                // that also receive genuinely Object-typed values.
                if matches!(e, Expr::This) {
                    push_ev(ev, *var, Evidence::OfThis);
                } else if !matches!(e, Expr::Const(ConstVal::Null))
                    && !matches!(e, Expr::Lambda(_))
                {
                    // Lambda/method-ref values carry NO static type (their
                    // target comes from context): recording their Object
                    // placeholder poisons the merge join and pins the
                    // stack var to Object, where `stackN = sink::accept`
                    // then fails ("Object 不是函数接口", jdk26
                    // DoublePipeline.flatMapDouble). Skipping them lets
                    // the sibling branch's concrete type (DoubleConsumer)
                    // win the narrowing.
                    let t = e.type_ref().erased();
                    if !matches!(t, JavaType::Void) {
                        push_ev(ev, *var, Evidence::T(t));
                    }
                    cond_branch_evidence(e, *var, ev);
                }
                if let Expr::Const(ConstVal::Int(n)) = e {
                    if *n == 0 || *n == 1 {
                        push_ev(ev, *var, Evidence::BoolCandidate);
                    }
                }
                gather_expr(e, ev, Some(*var), bool_vars);
            }
        }
        Stmt::Return(e) => {
            if let Some(x) = e {
                gather_expr(x, ev, None, bool_vars);
                // return type as evidence for locals inside
                if let Expr::Local { var, .. } = x {
                    push_ev(ev, *var, Evidence::T(ret_ty.clone()));
                }
            }
        }
        Stmt::Throw(e) => {
            gather_expr(e, ev, None, bool_vars);
            // A thrown local must be a Throwable.
            if let Expr::Local { var, .. } = e {
                push_ev(
                    ev,
                    *var,
                    Evidence::T(JavaType::Object("java/lang/Throwable".into())),
                );
            }
        }
        Stmt::If { cond, then_stmt, else_stmt } => {
            mark_bool_cond(cond, bool_vars);
            gather_expr(cond, ev, None, bool_vars);
            gather_evidence(then_stmt, ev, ret_ty, bool_vars);
            if let Some(x) = else_stmt {
                gather_evidence(x, ev, ret_ty, bool_vars);
            }
        }
        Stmt::While { cond, body } => {
            mark_bool_cond(cond, bool_vars);
            gather_expr(cond, ev, None, bool_vars);
            gather_evidence(body, ev, ret_ty, bool_vars);
        }
        Stmt::DoWhile { body, cond } => {
            mark_bool_cond(cond, bool_vars);
            gather_expr(cond, ev, None, bool_vars);
            gather_evidence(body, ev, ret_ty, bool_vars);
        }
        Stmt::For { init, cond, update, body } => {
            init.iter().for_each(|i| gather_evidence(i, ev, ret_ty, bool_vars));
            if let Some(c) = cond {
                mark_bool_cond(c, bool_vars);
                gather_expr(c, ev, None, bool_vars);
            }
            update.iter().for_each(|u| gather_expr(u, ev, None, bool_vars));
            gather_evidence(body, ev, ret_ty, bool_vars);
        }
        Stmt::ForEach { iterable, body, .. } => {
            gather_expr(iterable, ev, None, bool_vars);
            gather_evidence(body, ev, ret_ty, bool_vars);
        }
        Stmt::Switch { selector, cases, default, .. } => {
            gather_expr(selector, ev, None, bool_vars);
            for c in cases {
                c.body.iter().for_each(|st| gather_evidence(st, ev, ret_ty, bool_vars));
            }
            if let Some(d) = default {
                gather_evidence(d, ev, ret_ty, bool_vars);
            }
        }
        Stmt::Try { body, catches, finally } => {
            gather_evidence(body, ev, ret_ty, bool_vars);
            for c in catches {
                gather_evidence(&c.body, ev, ret_ty, bool_vars);
            }
            if let Some(f) = finally {
                gather_evidence(f, ev, ret_ty, bool_vars);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter() { gather_evidence(res, ev, ret_ty, bool_vars); }
            gather_evidence(body, ev, ret_ty, bool_vars);
            for c in catches {
                gather_evidence(&c.body, ev, ret_ty, bool_vars);
            }
            if let Some(f) = finally {
                gather_evidence(f, ev, ret_ty, bool_vars);
            }
        }
        Stmt::Synchronized { lock, body } => {
            gather_expr(lock, ev, None, bool_vars);
            gather_evidence(body, ev, ret_ty, bool_vars);
        }
        _ => {}
    }
}

fn mark_bool_cond(c: &Expr, bool_vars: &mut std::collections::HashSet<u32>) {
    // `v == 0`, `v != 0`, `v == 1` on a bare local: boolean candidate.
    if let Expr::Bin { op: crate::expr::BinOp::Eq | crate::expr::BinOp::Ne, l, r, .. } = c {
        if let (Expr::Local { var, .. }, Expr::Const(ConstVal::Int(n))) = (&**l, &**r) {
            if *n == 0 || *n == 1 {
                bool_vars.insert(*var);
            }
        }
    }
    if let Expr::Un { op: crate::expr::UnOp::Not, e } = c {
        if let Expr::Local { var, .. } = &**e {
            bool_vars.insert(*var);
        }
    }
}

fn push_ev(ev: &mut Vec<Vec<Evidence>>, v: u32, e: Evidence) {
    if let Some(slot) = ev.get_mut(v as usize) {
        slot.push(e);
    }
}

/// A conditional assigned to a variable contributes BOTH branch types:
/// `var = c ? new Small32(..) : new Fast32(..)` must join to the LUB
/// (Object here — no hierarchy access), not keep the first branch's
/// concrete type (jdk17 CodePointTrie: the decl printed Small32 and the
/// Fast32 branch became "条件表达式中的类型错误").
fn cond_branch_evidence(e: &Expr, var: u32, ev: &mut Vec<Vec<Evidence>>) {
    if let Expr::Cond { t, f, .. } = e {
        for br in [t.as_ref(), f.as_ref()] {
            if matches!(br, Expr::Const(ConstVal::Null) | Expr::Lambda(_)) {
                continue;
            }
            let bt = br.type_ref().erased();
            if !matches!(bt, JavaType::Void) {
                push_ev(ev, var, Evidence::T(bt));
            }
        }
    }
}

fn gather_expr(e: &Expr, ev: &mut Vec<Vec<Evidence>>, assign_target: Option<u32>, bool_vars: &mut std::collections::HashSet<u32>) {
    match e {
        Expr::Raw(_) | Expr::RawT(..) => {}
        Expr::Local { var, .. } => {
            if let Some(t) = assign_target {
                // self-reference guard: x = x contributes nothing new
                if t != *var {
                    let _ = ev;
                }
            }
        }
        Expr::Assign { target, value, .. } => {
            if let Expr::Local { var, .. } = &**target {
                // RHS type is evidence for the variable; string concat is
                // always String even though its parts look numeric.
                if matches!(&**value, Expr::This) {
                    push_ev(ev, *var, Evidence::OfThis);
                } else if !matches!(&**value, Expr::Const(ConstVal::Null))
                    && !matches!(&**value, Expr::Lambda(_))
                {
                    let t = if matches!(&**value, Expr::StringConcat(_)) {
                        JavaType::Object("java/lang/String".into())
                    } else {
                        value.type_ref().erased()
                    };
                    if !matches!(t, JavaType::Void) {
                        push_ev(ev, *var, Evidence::T(t));
                    }
                    cond_branch_evidence(value, *var, ev);
                }
                if let Expr::Const(ConstVal::Int(n)) = &**value {
                    if *n == 0 || *n == 1 {
                        push_ev(ev, *var, Evidence::BoolCandidate);
                    }
                }
            }
            gather_expr(target, ev, None, bool_vars);
            gather_expr(value, ev, None, bool_vars);
        }
        Expr::Method { args, desc, .. } => {
            for (a, pt) in args.iter().zip(desc.args.iter()) {
                if let Expr::Local { var, .. } = a {
                    push_ev(ev, *var, Evidence::T(pt.clone()));
                }
                gather_expr(a, ev, None, bool_vars);
            }
        }
        Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
            args.iter().for_each(|a| gather_expr(a, ev, None, bool_vars));
        }
        Expr::Bin { l, r, .. } => {
            gather_expr(l, ev, None, bool_vars);
            gather_expr(r, ev, None, bool_vars);
        }
        Expr::Un { e: inner, .. } | Expr::Cast { e: inner, .. } | Expr::InstanceOf { e: inner, .. } => {
            gather_expr(inner, ev, None, bool_vars)
        }
        Expr::Cond { c, t, f } => {
            gather_expr(c, ev, None, bool_vars);
            gather_expr(t, ev, None, bool_vars);
            gather_expr(f, ev, None, bool_vars);
        }
        Expr::ArrayIndex { array, index } => {
            gather_expr(array, ev, None, bool_vars);
            gather_expr(index, ev, None, bool_vars);
        }
        Expr::Field { owner: Some(o), .. } => gather_expr(o, ev, None, bool_vars),
        Expr::PreIncDec { e: inner, .. } | Expr::PostIncDec { e: inner, .. } => {
            gather_expr(inner, ev, None, bool_vars)
        }
        Expr::StringConcat(parts) => parts.iter().for_each(|p| {
            if let crate::expr::ConcatPart::Str(inner) = p {
                gather_expr(inner, ev, None, bool_vars);
            }
        }),
        Expr::Lambda(l) => l.captures.iter().for_each(|c| gather_expr(c, ev, None, bool_vars)),
        _ => {}
    }
    let _ = assign_target;
}

pub(crate) fn rewrite_local_types(s: &mut Stmt, types: &[TypeRef]) {
    match s {
        Stmt::Block(v) => v.iter_mut().for_each(|x| rewrite_local_types(x, types)),
        Stmt::ExprStmt(e) => rewrite_expr(e, types),
        Stmt::LocalDef { init: Some(e), .. } => rewrite_expr(e, types),
        Stmt::Return(Some(e)) | Stmt::Throw(e) => rewrite_expr(e, types),
        Stmt::If { cond, then_stmt, else_stmt } => {
            rewrite_expr(cond, types);
            rewrite_local_types(then_stmt, types);
            if let Some(x) = else_stmt {
                rewrite_local_types(x, types);
            }
        }
        Stmt::While { cond, body } => {
            rewrite_expr(cond, types);
            rewrite_local_types(body, types);
        }
        Stmt::DoWhile { body, cond } => {
            rewrite_local_types(body, types);
            rewrite_expr(cond, types);
        }
        Stmt::For { init, cond, update, body } => {
            init.iter_mut().for_each(|i| rewrite_local_types(i, types));
            if let Some(c) = cond {
                rewrite_expr(c, types);
            }
            update.iter_mut().for_each(|u| rewrite_expr(u, types));
            rewrite_local_types(body, types);
        }
        Stmt::ForEach { iterable, body, .. } => {
            rewrite_expr(iterable, types);
            rewrite_local_types(body, types);
        }
        Stmt::Switch { selector, cases, default, .. } => {
            rewrite_expr(selector, types);
            for c in cases {
                c.body.iter_mut().for_each(|st| rewrite_local_types(st, types));
            }
            if let Some(d) = default {
                rewrite_local_types(d, types);
            }
        }
        Stmt::Try { body, catches, finally } => {
            rewrite_local_types(body, types);
            for c in catches {
                rewrite_local_types(&mut c.body, types);
            }
            if let Some(f) = finally {
                rewrite_local_types(f, types);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { rewrite_local_types(res, types); }
            rewrite_local_types(body, types);
            for c in catches {
                rewrite_local_types(&mut c.body, types);
            }
            if let Some(f) = finally {
                rewrite_local_types(f, types);
            }
        }
        Stmt::Synchronized { lock, body } => {
            rewrite_expr(lock, types);
            rewrite_local_types(body, types);
        }
        _ => {}
    }
}

fn rewrite_expr(e: &mut Expr, types: &[TypeRef]) {
    if let Expr::Local { var, ty } = e {
        if let Some(t) = types.get(*var as usize) {
            *ty = t.clone();
        }
    }
    match e {
        Expr::New { args, .. } | Expr::AnonNew { args, .. } => args.iter_mut().for_each(|a| rewrite_expr(a, types)),
        Expr::Method { owner, args, .. } => {
            if let Some(o) = owner {
                rewrite_expr(o, types);
            }
            args.iter_mut().for_each(|a| rewrite_expr(a, types));
        }
        Expr::Field { owner: Some(o), .. } => rewrite_expr(o, types),
        Expr::ArrayIndex { array, index } => {
            rewrite_expr(array, types);
            rewrite_expr(index, types);
        }
        Expr::Cast { e: inner, .. } | Expr::InstanceOf { e: inner, .. } | Expr::Un { e: inner, .. } => {
            rewrite_expr(inner, types)
        }
        Expr::Bin { l, r, .. } => {
            rewrite_expr(l, types);
            rewrite_expr(r, types);
        }
        Expr::Cond { c, t, f } => {
            rewrite_expr(c, types);
            rewrite_expr(t, types);
            rewrite_expr(f, types);
        }
        Expr::Assign { target, value, .. } => {
            rewrite_expr(target, types);
            rewrite_expr(value, types);
        }
        Expr::PreIncDec { e: inner, .. } | Expr::PostIncDec { e: inner, .. } => rewrite_expr(inner, types),
        Expr::Lambda(l) => l.captures.iter_mut().for_each(|c| rewrite_expr(c, types)),
        Expr::StringConcat(parts) => parts.iter_mut().for_each(|p| {
            if let crate::expr::ConcatPart::Str(inner) = p {
                rewrite_expr(inner, types);
            }
        }),
        Expr::Invokedynamic { args, .. } => args.iter_mut().for_each(|a| rewrite_expr(a, types)),
        Expr::NewArray { dims, init, .. } => {
            dims.iter_mut().for_each(|d| rewrite_expr(d, types));
            if let Some(vals) = init {
                vals.iter_mut().for_each(|v| rewrite_expr(v, types));
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Escaped variable hoisting
// ---------------------------------------------------------------------------

/// True when any decl/use of `var` appears in this subtree.
fn mentions_var(s: &Stmt, var: u32) -> bool {
    let mut d: std::collections::HashSet<u32> = std::collections::HashSet::new();
    let mut u: std::collections::HashSet<u32> = std::collections::HashSet::new();
    collect_decl_use(s, &mut d, &mut u);
    d.contains(&var) || u.contains(&var)
}

/// True when a lambda's capture list references `v` anywhere in this
/// statement tree (the loop-decl-slot gate: a lambda-captured local
/// assigned inside a loop must be declared per-iteration to stay
/// effectively final — jdk17 Loader.initRemotePackageMap's `other`).
fn captured_by_lambda(s: &Stmt, v: u32) -> bool {
    fn refs(e: &Expr, v: u32) -> bool {
        match e {
            Expr::Local { var, .. } => *var == v,
            Expr::Method { owner, args, .. } => {
                owner.as_deref().map(|o| refs(o, v)).unwrap_or(false)
                    || args.iter().any(|a| refs(a, v))
            }
            Expr::Field { owner: Some(o), .. } => refs(o, v),
            Expr::Bin { l, r, .. } | Expr::Assign { target: l, value: r, .. } => {
                refs(l, v) || refs(r, v)
            }
            Expr::Cond { c, t, f } => refs(c, v) || refs(t, v) || refs(f, v),
            Expr::Un { e: x, .. }
            | Expr::Cast { e: x, .. }
            | Expr::InstanceOf { e: x, .. }
            | Expr::PreIncDec { e: x, .. }
            | Expr::PostIncDec { e: x, .. } => refs(x, v),
            Expr::ArrayIndex { array, index } => refs(array, v) || refs(index, v),
            Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
                args.iter().any(|a| refs(a, v))
            }
            Expr::NewArray { dims, init, .. } => {
                dims.iter().any(|d| refs(d, v))
                    || init
                        .as_ref()
                        .map(|vals| vals.iter().any(|x| refs(x, v)))
                        .unwrap_or(false)
            }
            Expr::StringConcat(parts) => parts.iter().any(|pp| match pp {
                crate::expr::ConcatPart::Str(x) => refs(x, v),
                _ => false,
            }),
            Expr::Lambda(l) => l.captures.iter().any(|a| refs(a, v)),
            Expr::Invokedynamic { args, .. } => args.iter().any(|a| refs(a, v)),
            _ => false,
        }
    }
    fn ex(e: &Expr, v: u32) -> bool {
        match e {
            Expr::Lambda(l) => l.captures.iter().any(|a| refs(a, v)),
            Expr::Method { owner, args, .. } => {
                owner.as_deref().map(|o| ex(o, v)).unwrap_or(false)
                    || args.iter().any(|a| ex(a, v))
            }
            Expr::Field { owner: Some(o), .. } => ex(o, v),
            Expr::Bin { l, r, .. } | Expr::Assign { target: l, value: r, .. } => {
                ex(l, v) || ex(r, v)
            }
            Expr::Cond { c, t, f } => ex(c, v) || ex(t, v) || ex(f, v),
            Expr::Un { e: x, .. }
            | Expr::Cast { e: x, .. }
            | Expr::InstanceOf { e: x, .. }
            | Expr::PreIncDec { e: x, .. }
            | Expr::PostIncDec { e: x, .. } => ex(x, v),
            Expr::ArrayIndex { array, index } => ex(array, v) || ex(index, v),
            Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
                args.iter().any(|a| ex(a, v))
            }
            Expr::NewArray { dims, init, .. } => {
                dims.iter().any(|d| ex(d, v))
                    || init
                        .as_ref()
                        .map(|vals| vals.iter().any(|x| ex(x, v)))
                        .unwrap_or(false)
            }
            Expr::StringConcat(parts) => parts.iter().any(|pp| match pp {
                crate::expr::ConcatPart::Str(x) => ex(x, v),
                _ => false,
            }),
            Expr::Invokedynamic { args, .. } => args.iter().any(|a| ex(a, v)),
            _ => false,
        }
    }
    fn st(s: &Stmt, v: u32) -> bool {
        match s {
            Stmt::Block(x) => x.iter().any(|i| st(i, v)),
            Stmt::ExprStmt(e) => ex(e, v),
            Stmt::LocalDef { init: Some(e), .. } => ex(e, v),
            Stmt::Return(Some(e)) | Stmt::Throw(e) => ex(e, v),
            Stmt::If { cond, then_stmt, else_stmt } => {
                ex(cond, v)
                    || st(then_stmt, v)
                    || else_stmt.as_deref().map(|e2| st(e2, v)).unwrap_or(false)
            }
            Stmt::While { cond, body } | Stmt::DoWhile { body, cond } => ex(cond, v) || st(body, v),
            Stmt::For { init, cond, update, body } => {
                init.iter().any(|i| st(i, v))
                    || cond.as_ref().map(|c| ex(c, v)).unwrap_or(false)
                    || update.iter().any(|u| ex(u, v))
                    || st(body, v)
            }
            Stmt::ForEach { iterable, body, .. } => ex(iterable, v) || st(body, v),
            Stmt::Switch { selector, cases, default, .. } => {
                ex(selector, v)
                    || cases.iter().any(|c| c.body.iter().any(|b| st(b, v)))
                    || default.as_deref().map(|d| st(d, v)).unwrap_or(false)
            }
            Stmt::Try { body, catches, finally } => {
                st(body, v)
                    || catches.iter().any(|c| st(&c.body, v))
                    || finally.as_deref().map(|f| st(f, v)).unwrap_or(false)
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                resources.iter().any(|r| st(r, v))
                    || st(body, v)
                    || catches.iter().any(|c| st(&c.body, v))
                    || finally.as_deref().map(|f| st(f, v)).unwrap_or(false)
            }
            Stmt::Synchronized { lock, body } => ex(lock, v) || st(body, v),
            Stmt::Labeled { body, .. } => st(body, v),
            Stmt::Assert { cond, msg } => {
                ex(cond, v) || msg.as_ref().map(|m| ex(m, v)).unwrap_or(false)
            }
            _ => false,
        }
    }
    st(s, v)
}

/// Path step to a child subtree (for the loop-decl-slot search).
#[derive(Clone, Copy)]
enum SlotStep {
    LoopBody,
    VecChild(usize),
    TryBody,
    Catch(usize),
    Finally,
    Then,
    Else,
    WrapperBody,
}

/// Immutable search: path from `s` to the innermost LOOP BODY that hosts
/// all mentions of `var` (all mentions assumed inside `s`). A loop body
/// gives per-iteration variable freshness — required for captured locals
/// assigned inside the loop to stay effectively final.
fn find_loop_decl_path(s: &Stmt, var: u32) -> Option<Vec<SlotStep>> {
    match s {
        Stmt::While { body, .. }
        | Stmt::DoWhile { body, .. }
        | Stmt::For { body, .. }
        | Stmt::ForEach { body, .. } => {
            if !mentions_var(body, var) {
                return None;
            }
            let mut p = vec![SlotStep::LoopBody];
            match find_loop_decl_path(body, var) {
                Some(mut d) => {
                    p.append(&mut d);
                    Some(p)
                }
                None => Some(p),
            }
        }
        Stmt::Block(v) => {
            let hits: Vec<usize> = v
                .iter()
                .enumerate()
                .filter(|(_, x)| mentions_var(x, var))
                .map(|(i, _)| i)
                .collect();
            if hits.len() != 1 {
                return None;
            }
            let i = hits[0];
            let mut p = find_loop_decl_path(&v[i], var)?;
            p.insert(0, SlotStep::VecChild(i));
            Some(p)
        }
        Stmt::Try { body, catches, finally }
        | Stmt::TryWithResources { body, catches, finally, .. } => {
            let mut hits: Vec<(SlotStep, &Stmt)> = Vec::new();
            if mentions_var(body, var) {
                hits.push((SlotStep::TryBody, body));
            }
            for (i, c) in catches.iter().enumerate() {
                if mentions_var(&c.body, var) {
                    hits.push((SlotStep::Catch(i), &c.body));
                }
            }
            if let Some(f) = finally {
                if mentions_var(f, var) {
                    hits.push((SlotStep::Finally, f));
                }
            }
            if hits.len() != 1 {
                return None;
            }
            let (step, sub) = hits.into_iter().next().unwrap();
            let mut p = find_loop_decl_path(sub, var)?;
            p.insert(0, step);
            Some(p)
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            let t = mentions_var(then_stmt, var);
            let e = else_stmt.as_deref().map(|x| mentions_var(x, var)).unwrap_or(false);
            let (step, sub) = match (t, e) {
                (true, false) => (SlotStep::Then, &**then_stmt),
                (false, true) => (SlotStep::Else, else_stmt.as_deref().unwrap()),
                _ => return None,
            };
            let mut p = find_loop_decl_path(sub, var)?;
            p.insert(0, step);
            Some(p)
        }
        Stmt::Labeled { body, .. } | Stmt::Synchronized { body, .. } => {
            if !mentions_var(body, var) {
                return None;
            }
            let mut p = find_loop_decl_path(body, var)?;
            p.insert(0, SlotStep::WrapperBody);
            Some(p)
        }
        _ => None,
    }
}

/// Mutable follow of a path produced by `find_loop_decl_path`.
fn follow_slot_path<'a>(s: &'a mut Stmt, path: &[SlotStep]) -> &'a mut Stmt {
    let mut cur = s;
    for step in path {
        cur = match step {
            SlotStep::LoopBody | SlotStep::WrapperBody => match cur {
                Stmt::While { body, .. }
                | Stmt::DoWhile { body, .. }
                | Stmt::For { body, .. }
                | Stmt::ForEach { body, .. }
                | Stmt::Labeled { body, .. }
                | Stmt::Synchronized { body, .. } => body,
                _ => unreachable!("path/shape mismatch (loop/wrapper)"),
            },
            SlotStep::VecChild(i) => match cur {
                Stmt::Block(v) => &mut v[*i],
                _ => unreachable!("path/shape mismatch (vec)"),
            },
            SlotStep::TryBody => match cur {
                Stmt::Try { body, .. } | Stmt::TryWithResources { body, .. } => body,
                _ => unreachable!("path/shape mismatch (try)"),
            },
            SlotStep::Catch(i) => match cur {
                Stmt::Try { catches, .. } | Stmt::TryWithResources { catches, .. } => {
                    &mut catches[*i].body
                }
                _ => unreachable!("path/shape mismatch (catch)"),
            },
            SlotStep::Finally => match cur {
                Stmt::Try { finally, .. } | Stmt::TryWithResources { finally, .. } => {
                    finally.as_mut().expect("path/shape mismatch (finally)")
                }
                _ => unreachable!("path/shape mismatch (finally)"),
            },
            SlotStep::Then => match cur {
                Stmt::If { then_stmt, .. } => then_stmt,
                _ => unreachable!("path/shape mismatch (then)"),
            },
            SlotStep::Else => match cur {
                Stmt::If { else_stmt, .. } => {
                    else_stmt.as_mut().expect("path/shape mismatch (else)")
                }
                _ => unreachable!("path/shape mismatch (else)"),
            },
        };
    }
    cur
}

/// If a variable is declared inside a nested scope (try/if/loop body) but
/// referenced after that scope closes, move its declaration to the method
/// top and demote the inner declaration to an assignment.
fn hoist_escaped_vars(body: &mut Stmt, vt: &VarTable) {
    let mut declared_open: Vec<std::collections::HashSet<u32>> = vec![std::collections::HashSet::new()];
    let mut declared_ever: std::collections::HashSet<u32> = std::collections::HashSet::new();
    let mut escaped: std::collections::HashSet<u32> = std::collections::HashSet::new();
    escape_scan(body, &mut declared_open, &mut declared_ever, &mut escaped);
    // Second pass with `declared_ever` fully populated: uses of a variable
    // that appear BEFORE (or in a sibling branch of) its declaration are
    // flagged as escaped too, so the declaration hoists above them.
    declared_open = vec![std::collections::HashSet::new()];
    escape_scan(body, &mut declared_open, &mut declared_ever, &mut escaped);
    // A `throw x` inside a try whose catch (binding x) sits in an enclosing
    // scope is a javac rethrow-around-handler artifact: drop it, since the
    // enclosing catch will handle the exception.
    drop_rethrows(body);
    escaped.retain(|v| *v != u32::MAX);
    if std::env::var("JCDC_DBG_HOIST").is_ok() {
        eprintln!("HOIST escaped={:?}", escaped);
    }
    if escaped.is_empty() {
        return;
    }
    // A captured var whose EVERY mention lives inside one loop body must
    // be declared at that loop body's top, not at method top: a blank
    // method-scope decl assigned inside the loop is assigned once per
    // iteration — NOT effectively final — and the anon/lambda capture
    // goes illegal (从内部类引用的本地变量必须是最终变量或实际上的最终
    // 变量 — jdk17 URLClassPath$JarLoader.getResource: `url` is defined
    // in the try inside the do-while and read after the try in the same
    // iteration; method-top hoisting broke the doPrivileged anon's
    // capture). Loop-body-top keeps a fresh blank per iteration — the
    // source shape.
    // Paths are computed BEFORE demote_defs (which rewrites LocalDefs in
    // place, preserving block indices), applied AFTER it so the inserted
    // blank decl is not itself demoted.
    //
    // Deterministic iteration: `escaped` is a HashSet and each loop decl
    // is insert(0)'d into its loop-body slot — random iteration order
    // swapped sibling blank decls across runs (jdk11 module Resolver
    // `requiresTransitive;`/`reads;` flip-flopped between two outputs on
    // the SAME binary). Descending var-id iteration + head insertion
    // yields ascending var-id layout, matching the method-top hoist's
    // sort_unstable convention below.
    let mut loop_paths: Vec<(u32, Vec<SlotStep>)> = Vec::new();
    let mut esc_sorted: Vec<u32> = escaped.iter().copied().collect();
    esc_sorted.sort_unstable_by(|a, b| b.cmp(a));
    for var in esc_sorted {
        if !captured_by_anon(body, var) && !captured_by_lambda(body, var) {
            continue;
        }
        if let Some(path) = find_loop_decl_path(body, var) {
            loop_paths.push((var, path));
        }
    }
    demote_defs(body, &escaped, vt);
    let mut loop_declared: std::collections::HashSet<u32> = std::collections::HashSet::new();
    for (var, path) in loop_paths {
        let slot = follow_slot_path(body, &path);
        if let Stmt::Block(items) = slot {
            items.insert(
                0,
                Stmt::LocalDef { var, init: None, is_final: false, force_type: true },
            );
        } else {
            let old = std::mem::replace(slot, Stmt::Block(vec![]));
            *slot = Stmt::Block(vec![
                Stmt::LocalDef { var, init: None, is_final: false, force_type: true },
                old,
            ]);
        }
        loop_declared.insert(var);
    }
    escaped.retain(|v| !loop_declared.contains(v));
    if escaped.is_empty() {
        return;
    }
    let mut decls: Vec<Stmt> = {
        let mut v: Vec<u32> = escaped.into_iter().collect();
        v.sort_unstable();
        v.into_iter()
            .map(|var| Stmt::LocalDef {
                var,
                // Anon/lambda-captured locals must stay effectively final:
                // a `= null` default plus the branch assignments makes the
                // capture illegal ("从内部类引用的本地变量必须是最终变量
                // 或实际上的最终变量", jdk11 Subject.populateSet iterator).
                // The source used a blank declaration assigned once per
                // path; javac's definite-assignment check re-proves it.
                init: if captured_by_anon(body, var) && !assigns_null_to(body, var) {
                    None
                } else if captured_by_anon(body, var) && !straight_null_init(body, var) {
                    // Branch-internal null assignments are exclusive
                    // definite assignments (the bytecode verifier proves
                    // every read is dominated by its store), so the blank
                    // decl stays effectively final for the capture — the
                    // `= null` default plus the branch stores made it
                    // non-effectively-final (jdk26 DateTimePrintContext
                    // adjustSlow's blank `final ChronoLocalDate
                    // effectiveDate` assigned null/value per branch:
                    // 从内部类引用的本地变量必须是最终变量 x24).
                    None
                } else {
                    default_init_for(vt, var)
                },
                is_final: false,
                force_type: true,
            })
            .collect()
    };
    match body {
        Stmt::Block(items) => {
            let lead = match items.first() {
                Some(Stmt::ExprStmt(Expr::Method { name, .. })) if name == "<init>" => 1,
                _ => 0,
            };
            let mut out: Vec<Stmt> = items.drain(..lead).collect();
            out.append(&mut decls);
            out.append(items);
            *items = out;
        }
        other => {
            let old = std::mem::replace(other, Stmt::Block(vec![]));
            decls.push(old);
            *other = Stmt::Block(decls);
        }
    }
}

/// Remove `throw x;` statements inside try bodies where `x` is bound by an
/// enclosing catch clause (artifact of javac's handler threading).
fn drop_rethrows(s: &mut Stmt) {
    match s {
        Stmt::Block(v) => v.iter_mut().for_each(drop_rethrows),
        Stmt::Try { body, catches, finally } => {
            let bound: std::collections::HashSet<u32> =
                catches.iter().map(|c| c.var).filter(|v| *v != u32::MAX).collect();
            strip_throws_of(body, &bound);
            drop_rethrows(body);
            for c in catches {
                drop_rethrows(&mut c.body);
            }
            if let Some(f) = finally {
                drop_rethrows(f);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            let bound: std::collections::HashSet<u32> =
                catches.iter().map(|c| c.var).filter(|v| *v != u32::MAX).collect();
            for res in resources {
                strip_throws_of(res, &bound);
            }
            strip_throws_of(body, &bound);
            drop_rethrows(body);
            for c in catches {
                drop_rethrows(&mut c.body);
            }
            if let Some(f) = finally {
                drop_rethrows(f);
            }
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            drop_rethrows(then_stmt);
            if let Some(e) = else_stmt {
                drop_rethrows(e);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => drop_rethrows(body),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(drop_rethrows);
            drop_rethrows(body);
        }
        Stmt::ForEach { body, .. } => drop_rethrows(body),
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(drop_rethrows);
            }
            if let Some(d) = default {
                drop_rethrows(d);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => drop_rethrows(body),
        _ => {}
    }
}

fn strip_throws_of(s: &mut Stmt, vars: &std::collections::HashSet<u32>) {
    if vars.is_empty() {
        return;
    }
    match s {
        Stmt::Block(v) => {
            v.retain(|st| !matches!(st, Stmt::Throw(Expr::Local { var, .. }) if vars.contains(var)));
            v.iter_mut().for_each(|x| strip_throws_of(x, vars));
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            strip_throws_of(then_stmt, vars);
            if let Some(e) = else_stmt {
                strip_throws_of(e, vars);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => strip_throws_of(body, vars),
        Stmt::For { body, .. } | Stmt::ForEach { body, .. } => strip_throws_of(body, vars),
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(|st| strip_throws_of(st, vars));
            }
            if let Some(d) = default {
                strip_throws_of(d, vars);
            }
        }
        Stmt::Try { body, .. } => strip_throws_of(body, vars),
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => strip_throws_of(body, vars),
        _ => {}
    }
}

fn in_open(scopes: &[std::collections::HashSet<u32>], v: u32) -> bool {
    scopes.iter().any(|s| s.contains(&v))
}

fn escape_scan(
    s: &Stmt,
    scopes: &mut Vec<std::collections::HashSet<u32>>,
    declared_ever: &mut std::collections::HashSet<u32>,
    escaped: &mut std::collections::HashSet<u32>,
) {
    match s {
        Stmt::LocalDef { var, init, .. } => {
            if let Some(e) = init {
                expr_uses_collect(e, declared_ever, escaped, scopes);
            }
            if in_open(scopes, *var) {
                // duplicate in same scope: ignore (dedupe handles)
            } else {
                scopes.last_mut().unwrap().insert(*var);
                declared_ever.insert(*var);
            }
        }
        Stmt::Block(v) => {
            scopes.push(std::collections::HashSet::new());
            for x in v {
                escape_scan(x, scopes, declared_ever, escaped);
            }
            scopes.pop();
        }
        Stmt::ExprStmt(e) => expr_uses_collect(e, declared_ever, escaped, scopes),
        Stmt::Return(e) => {
            if let Some(x) = e {
                expr_uses_collect(x, declared_ever, escaped, scopes);
            }
        }
        Stmt::Throw(e) => expr_uses_collect(e, declared_ever, escaped, scopes),
        Stmt::If { cond, then_stmt, else_stmt } => {
            expr_uses_collect(cond, declared_ever, escaped, scopes);
            // Each branch is its own lexical scope even when it is not a
            // Block statement.
            scopes.push(std::collections::HashSet::new());
            escape_scan(then_stmt, scopes, declared_ever, escaped);
            scopes.pop();
            if let Some(x) = else_stmt {
                scopes.push(std::collections::HashSet::new());
                escape_scan(x, scopes, declared_ever, escaped);
                scopes.pop();
            }
        }
        Stmt::While { cond, body } => {
            expr_uses_collect(cond, declared_ever, escaped, scopes);
            scopes.push(std::collections::HashSet::new());
            escape_scan(body, scopes, declared_ever, escaped);
            scopes.pop();
        }
        Stmt::DoWhile { body, cond } => {
            scopes.push(std::collections::HashSet::new());
            escape_scan(body, scopes, declared_ever, escaped);
            scopes.pop();
            expr_uses_collect(cond, declared_ever, escaped, scopes);
        }
        Stmt::For { init, cond, update, body } => {
            scopes.push(std::collections::HashSet::new());
            init.iter().for_each(|i| escape_scan(i, scopes, declared_ever, escaped));
            if let Some(c) = cond {
                expr_uses_collect(c, declared_ever, escaped, scopes);
            }
            update.iter().for_each(|u| expr_uses_collect(u, declared_ever, escaped, scopes));
            escape_scan(body, scopes, declared_ever, escaped);
            scopes.pop();
        }
        Stmt::ForEach { var, iterable, body, .. } => {
            expr_uses_collect(iterable, declared_ever, escaped, scopes);
            scopes.push(std::collections::HashSet::new());
            scopes.last_mut().unwrap().insert(*var);
            declared_ever.insert(*var);
            escape_scan(body, scopes, declared_ever, escaped);
            scopes.pop();
        }
        Stmt::Switch { selector, cases, default, .. } => {
            expr_uses_collect(selector, declared_ever, escaped, scopes);
            for c in cases {
                scopes.push(std::collections::HashSet::new());
                c.body.iter().for_each(|st| escape_scan(st, scopes, declared_ever, escaped));
                scopes.pop();
            }
            if let Some(d) = default {
                escape_scan(d, scopes, declared_ever, escaped);
            }
        }
        Stmt::Try { body, catches, finally } => {
            escape_scan(body, scopes, declared_ever, escaped);
            for c in catches {
                scopes.push(std::collections::HashSet::new());
                if c.var != u32::MAX {
                    scopes.last_mut().unwrap().insert(c.var);
                    declared_ever.insert(c.var);
                }
                escape_scan(&c.body, scopes, declared_ever, escaped);
                scopes.pop();
            }
            if let Some(f) = finally {
                escape_scan(f, scopes, declared_ever, escaped);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            scopes.push(std::collections::HashSet::new());
            for r in resources {
                escape_scan(r, scopes, declared_ever, escaped);
            }
            escape_scan(body, scopes, declared_ever, escaped);
            for c in catches {
                scopes.push(std::collections::HashSet::new());
                if c.var != u32::MAX {
                    scopes.last_mut().unwrap().insert(c.var);
                    declared_ever.insert(c.var);
                }
                escape_scan(&c.body, scopes, declared_ever, escaped);
                scopes.pop();
            }
            if let Some(f) = finally {
                escape_scan(f, scopes, declared_ever, escaped);
            }
            scopes.pop();
        }
        Stmt::Synchronized { lock, body } => {
            expr_uses_collect(lock, declared_ever, escaped, scopes);
            escape_scan(body, scopes, declared_ever, escaped);
        }
        Stmt::Labeled { body, .. } => escape_scan(body, scopes, declared_ever, escaped),
        Stmt::MonitorEnter(e) | Stmt::MonitorExit(e) => expr_uses_collect(e, declared_ever, escaped, scopes),
        _ => {}
    }
}

fn expr_uses_collect(
    e: &Expr,
    declared_ever: &std::collections::HashSet<u32>,
    escaped: &mut std::collections::HashSet<u32>,
    scopes: &[std::collections::HashSet<u32>],
) {
    if let Expr::Local { var, .. } = e {
        if !in_open(scopes, *var) && declared_ever.contains(var) {
            escaped.insert(*var);
        }
    }
    // recurse
    match e {
        Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
            args.iter().for_each(|a| expr_uses_collect(a, declared_ever, escaped, scopes))
        }
        Expr::Method { owner, args, .. } => {
            if let Some(o) = owner {
                expr_uses_collect(o, declared_ever, escaped, scopes);
            }
            args.iter().for_each(|a| expr_uses_collect(a, declared_ever, escaped, scopes));
        }
        Expr::Field { owner: Some(o), .. } => expr_uses_collect(o, declared_ever, escaped, scopes),
        Expr::ArrayIndex { array, index } => {
            expr_uses_collect(array, declared_ever, escaped, scopes);
            expr_uses_collect(index, declared_ever, escaped, scopes);
        }
        Expr::Cast { e, .. } | Expr::InstanceOf { e, .. } | Expr::Un { e, .. } => {
            expr_uses_collect(e, declared_ever, escaped, scopes)
        }
        Expr::Bin { l, r, .. } => {
            expr_uses_collect(l, declared_ever, escaped, scopes);
            expr_uses_collect(r, declared_ever, escaped, scopes);
        }
        Expr::Cond { c, t, f } => {
            expr_uses_collect(c, declared_ever, escaped, scopes);
            expr_uses_collect(t, declared_ever, escaped, scopes);
            expr_uses_collect(f, declared_ever, escaped, scopes);
        }
        Expr::Assign { target, value, .. } => {
            expr_uses_collect(target, declared_ever, escaped, scopes);
            expr_uses_collect(value, declared_ever, escaped, scopes);
        }
        Expr::PreIncDec { e, .. } | Expr::PostIncDec { e, .. } => {
            expr_uses_collect(e, declared_ever, escaped, scopes)
        }
        Expr::Lambda(l) => l
            .captures
            .iter()
            .for_each(|c| expr_uses_collect(c, declared_ever, escaped, scopes)),
        Expr::StringConcat(parts) => parts.iter().for_each(|p| {
            if let crate::expr::ConcatPart::Str(inner) = p {
                expr_uses_collect(inner, declared_ever, escaped, scopes);
            }
        }),
        Expr::Invokedynamic { args, .. } => {
            args.iter().for_each(|a| expr_uses_collect(a, declared_ever, escaped, scopes))
        }
        Expr::NewArray { dims, init, .. } => {
            dims.iter().for_each(|d| expr_uses_collect(d, declared_ever, escaped, scopes));
            if let Some(vals) = init {
                vals.iter().for_each(|v| expr_uses_collect(v, declared_ever, escaped, scopes));
            }
        }
        _ => {}
    }
}

fn demote_defs(s: &mut Stmt, vars: &std::collections::HashSet<u32>, vt: &VarTable) {
    match s {
        Stmt::LocalDef { var, init, .. } if vars.contains(var) => match init.take() {
            Some(e) => {
                *s = Stmt::ExprStmt(Expr::Assign {
                    target: Box::new(Expr::Local {
                        var: *var,
                        ty: vt.var(*var).ty.clone(),
                    }),
                    op: crate::expr::AssignOp::Plain,
                    value: Box::new(e),
                });
            }
            None => *s = Stmt::Block(vec![]),
        },
        Stmt::Block(v) => v.iter_mut().for_each(|x| demote_defs(x, vars, vt)),
        Stmt::If { then_stmt, else_stmt, .. } => {
            demote_defs(then_stmt, vars, vt);
            if let Some(e) = else_stmt {
                demote_defs(e, vars, vt);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => demote_defs(body, vars, vt),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(|i| demote_defs(i, vars, vt));
            demote_defs(body, vars, vt);
        }
        Stmt::ForEach { body, .. } => demote_defs(body, vars, vt),
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(|st| demote_defs(st, vars, vt));
            }
            if let Some(d) = default {
                demote_defs(d, vars, vt);
            }
        }
        Stmt::Try { body, catches, finally } => {
            demote_defs(body, vars, vt);
            for c in catches {
                demote_defs(&mut c.body, vars, vt);
            }
            if let Some(f) = finally {
                demote_defs(f, vars, vt);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() {
                // Resource declarations stay declarations (demote would
                // turn `try (X x = ...)` into an assignment).
                if !matches!(res, Stmt::LocalDef { .. }) {
                    demote_defs(res, vars, vt);
                }
            }
            demote_defs(body, vars, vt);
            for c in catches {
                demote_defs(&mut c.body, vars, vt);
            }
            if let Some(f) = finally {
                demote_defs(f, vars, vt);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => demote_defs(body, vars, vt),
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// finally deduplication
// ---------------------------------------------------------------------------

/// javac duplicates the finally body at the try's normal exit and after each
/// catch. Pattern: Try whose last catch is catch-all ending with
/// `throw <var>` → convert to `finally` and strip the trailing duplicate
/// from the body and each typed catch.
fn dedupe_finally(s: &mut Stmt) {
    match s {
        Stmt::Try { body, catches, finally } => {
            dedupe_finally(body);
            for c in catches.iter_mut() {
                dedupe_finally(&mut c.body);
            }
            if let Some(f) = finally.as_deref_mut() {
                dedupe_finally(f);
            }
            if finally.is_none() && !catches.is_empty() {
                let li = catches.len() - 1;
                let is_catchall = catches[li].exc.is_empty();
                if is_catchall {
                    let rethrow_var = trailing_rethrow_var(&catches[li].body);
                    if let Some(rv) = rethrow_var {
                        // finally content = handler statements minus trailing throw
                        let mut fin = stmt_vec_take(&mut catches[li].body);
                        remove_trailing_throw(&mut fin);
                        for st in fin.iter_mut() {
                            remove_trailing_rethrow_stmt(st, rv);
                        }
                        // the exception store may remain as first stmt; drop it
                        if matches!(fin.first(), Some(Stmt::LocalDef { .. }) | Some(Stmt::ExprStmt(Expr::Assign { .. }))) {
                            // keep only if it references rv beyond the throw...
                            // conservative: drop a leading `rv = ...` assign
                            if let Some(Stmt::ExprStmt(Expr::Assign { target, .. })) = fin.first() {
                                if matches!(&**target, Expr::Local { var, .. } if *var == rv) {
                                    fin.remove(0);
                                }
                            }
                            if let Some(Stmt::LocalDef { var, .. }) = fin.first() {
                                if *var == rv {
                                    fin.remove(0);
                                }
                            }
                        }
                        let removed = fin.len();
                        if removed > 0 {
                            strip_trailing_copies(body, &fin);
                            for c in catches.iter_mut().take(li) {
                                strip_trailing_copies(&mut c.body, &fin);
                            }
                        }
                        *finally = Some(Box::new(Stmt::Block(fin)));
                        catches.pop();
                    }
                }
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { dedupe_finally(res); }
            dedupe_finally(body);
            for c in catches.iter_mut() {
                dedupe_finally(&mut c.body);
            }
            if let Some(f) = finally.as_deref_mut() {
                dedupe_finally(f);
            }
            if finally.is_none() && !catches.is_empty() {
                let li = catches.len() - 1;
                let is_catchall = catches[li].exc.is_empty();
                if is_catchall {
                    let rethrow_var = trailing_rethrow_var(&catches[li].body);
                    if let Some(rv) = rethrow_var {
                        // finally content = handler statements minus trailing throw
                        let mut fin = stmt_vec_take(&mut catches[li].body);
                        remove_trailing_throw(&mut fin);
                        for st in fin.iter_mut() {
                            remove_trailing_rethrow_stmt(st, rv);
                        }
                        // the exception store may remain as first stmt; drop it
                        if matches!(fin.first(), Some(Stmt::LocalDef { .. }) | Some(Stmt::ExprStmt(Expr::Assign { .. }))) {
                            // keep only if it references rv beyond the throw...
                            // conservative: drop a leading `rv = ...` assign
                            if let Some(Stmt::ExprStmt(Expr::Assign { target, .. })) = fin.first() {
                                if matches!(&**target, Expr::Local { var, .. } if *var == rv) {
                                    fin.remove(0);
                                }
                            }
                            if let Some(Stmt::LocalDef { var, .. }) = fin.first() {
                                if *var == rv {
                                    fin.remove(0);
                                }
                            }
                        }
                        let removed = fin.len();
                        if removed > 0 {
                            strip_trailing_copies(body, &fin);
                            for c in catches.iter_mut().take(li) {
                                strip_trailing_copies(&mut c.body, &fin);
                            }
                        }
                        *finally = Some(Box::new(Stmt::Block(fin)));
                        catches.pop();
                    }
                }
            }
        }
        Stmt::Block(v) => {
            v.iter_mut().for_each(dedupe_finally);
            // finally copies inlined on the normal-exit continuation right
            // after the try are redundant once a real `finally` exists.
            let mut i = 0;
            while i < v.len() {
                let fin: Option<Vec<Stmt>> = match &v[i] {
                    Stmt::Try { finally: Some(f), .. } => Some(match &**f {
                        Stmt::Block(inner) => inner.clone(),
                        other => vec![other.clone()],
                    }),
                    _ => None,
                };
                if let Some(fin) = fin {
                    if !fin.is_empty() {
                        // Compare in normalized form: the inline normal-path
                        // copy and the handler copy bind DIFFERENT catch vars
                        // (jdk11 FilterOutputStream.close: e5 vs e4) and the
                        // inline copy's branches end in the method's trailing
                        // `return;` the handler copy lacks. Remap local ids
                        // by traversal order, erase catch var names, and drop
                        // value-less trailing Return/Throw at block tails.
                        let mut fin_norm = fin.clone();
                        {
                            let mut map: HashMap<u32, u32> = HashMap::new();
                            let mut next = 0u32;
                            for st in fin_norm.iter_mut() {
                                norm_stmt_for_dedupe(st, &mut map, &mut next);
                            }
                        }
                        let mut j = i + 1;
                        let mut k = 0;
                        while j < v.len() && k < fin_norm.len() {
                            let mut cand = v[j].clone();
                            let mut map: HashMap<u32, u32> = HashMap::new();
                            let mut next = 0u32;
                            norm_stmt_for_dedupe(&mut cand, &mut map, &mut next);
                            if cand != fin_norm[k] {
                                break;
                            }
                            j += 1;
                            k += 1;
                        }
                        if k == fin_norm.len() && k > 0 {
                            v.drain(i + 1..j);
                        }
                    }
                }
                i += 1;
            }
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            dedupe_finally(then_stmt);
            if let Some(e) = else_stmt {
                dedupe_finally(e);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => dedupe_finally(body),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(dedupe_finally);
            dedupe_finally(body);
        }
        Stmt::ForEach { body, .. } => dedupe_finally(body),
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(dedupe_finally);
            }
            if let Some(d) = default {
                dedupe_finally(d);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => dedupe_finally(body),
        _ => {}
    }
}

fn stmt_vec_take(s: &mut Stmt) -> Vec<Stmt> {
    match std::mem::replace(s, Stmt::Block(vec![])) {
        Stmt::Block(v) => v,
        other => vec![other],
    }
}

/// Normalize a statement for finally-copy dedupe comparison: remap local
/// var ids by traversal order (two structurally identical finally copies
/// bind different catch vars), erase per-copy catch var names, and drop
/// value-less trailing Return/Throw at block tails (the normal-path copy
/// ends in the method's `return;`, the handler copy in the rethrow).
fn norm_stmt_for_dedupe(s: &mut Stmt, map: &mut HashMap<u32, u32>, next: &mut u32) {
    fn bind(map: &mut HashMap<u32, u32>, next: &mut u32, v: u32) -> u32 {
        if let Some(&i) = map.get(&v) {
            return i;
        }
        let i = *next;
        *next += 1;
        map.insert(v, i);
        i
    }
    fn ne(e: &mut Expr, map: &mut HashMap<u32, u32>, next: &mut u32) {
        match e {
            Expr::Local { var, .. } => {
                *var = bind(map, next, *var);
            }
            Expr::Cond { c, t, f } => {
                ne(c, map, next);
                ne(t, map, next);
                ne(f, map, next);
            }
            Expr::Bin { l, r, .. } => {
                ne(l, map, next);
                ne(r, map, next);
            }
            Expr::Un { e: x, .. }
            | Expr::Cast { e: x, .. }
            | Expr::InstanceOf { e: x, .. }
            | Expr::PreIncDec { e: x, .. }
            | Expr::PostIncDec { e: x, .. } => ne(x, map, next),
            Expr::Assign { target, value, .. } => {
                ne(target, map, next);
                ne(value, map, next);
            }
            Expr::Method { owner, args, .. } => {
                if let Some(o) = owner {
                    ne(o, map, next);
                }
                args.iter_mut().for_each(|a| ne(a, map, next));
            }
            Expr::Field { owner: Some(o), .. } => ne(o, map, next),
            Expr::ArrayIndex { array, index } => {
                ne(array, map, next);
                ne(index, map, next);
            }
            Expr::New { args, .. } => args.iter_mut().for_each(|a| ne(a, map, next)),
            Expr::NewArray { dims, init, .. } => {
                dims.iter_mut().for_each(|d| ne(d, map, next));
                if let Some(vals) = init {
                    vals.iter_mut().for_each(|x| ne(x, map, next));
                }
            }
            Expr::StringConcat(parts) => {
                for p in parts.iter_mut() {
                    if let crate::expr::ConcatPart::Str(x) = p {
                        ne(x, map, next);
                    }
                }
            }
            Expr::Lambda(l) => l.captures.iter_mut().for_each(|c| ne(c, map, next)),
            _ => {}
        }
    }
    match s {
        Stmt::Block(v) => {
            for x in v.iter_mut() {
                norm_stmt_for_dedupe(x, map, next);
            }
            while matches!(
                v.last(),
                Some(Stmt::Return(None)) | Some(Stmt::Throw(_))
            ) {
                v.pop();
            }
        }
        Stmt::ExprStmt(e) => ne(e, map, next),
        Stmt::LocalDef { var, init, .. } => {
            *var = bind(map, next, *var);
            if let Some(i) = init {
                ne(i, map, next);
            }
        }
        Stmt::Return(Some(e)) => ne(e, map, next),
        Stmt::Throw(e) => ne(e, map, next),
        Stmt::If { cond, then_stmt, else_stmt } => {
            ne(cond, map, next);
            norm_stmt_for_dedupe(then_stmt, map, next);
            if let Some(x) = else_stmt {
                norm_stmt_for_dedupe(x, map, next);
            }
        }
        Stmt::While { cond, body } | Stmt::DoWhile { body, cond } => {
            ne(cond, map, next);
            norm_stmt_for_dedupe(body, map, next);
        }
        Stmt::For { init, cond, update, body } => {
            init.iter_mut().for_each(|x| norm_stmt_for_dedupe(x, map, next));
            if let Some(c) = cond {
                ne(c, map, next);
            }
            update.iter_mut().for_each(|u| ne(u, map, next));
            norm_stmt_for_dedupe(body, map, next);
        }
        Stmt::ForEach { iterable, body, .. } => {
            ne(iterable, map, next);
            norm_stmt_for_dedupe(body, map, next);
        }
        Stmt::Switch { selector, cases, default, .. } => {
            ne(selector, map, next);
            for c in cases.iter_mut() {
                c.body.iter_mut().for_each(|x| norm_stmt_for_dedupe(x, map, next));
            }
            if let Some(d) = default {
                norm_stmt_for_dedupe(d, map, next);
            }
        }
        Stmt::Try { body, catches, finally } => {
            norm_stmt_for_dedupe(body, map, next);
            for c in catches.iter_mut() {
                c.var = bind(map, next, c.var);
                c.var_name = None;
                norm_stmt_for_dedupe(&mut c.body, map, next);
            }
            if let Some(f) = finally {
                norm_stmt_for_dedupe(f, map, next);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            resources.iter_mut().for_each(|r| norm_stmt_for_dedupe(r, map, next));
            norm_stmt_for_dedupe(body, map, next);
            for c in catches.iter_mut() {
                c.var = bind(map, next, c.var);
                c.var_name = None;
                norm_stmt_for_dedupe(&mut c.body, map, next);
            }
            if let Some(f) = finally {
                norm_stmt_for_dedupe(f, map, next);
            }
        }
        Stmt::Synchronized { lock, body } => {
            ne(lock, map, next);
            norm_stmt_for_dedupe(body, map, next);
        }
        Stmt::Labeled { body, .. } => norm_stmt_for_dedupe(body, map, next),
        _ => {}
    }
}

fn trailing_rethrow_var(s: &Stmt) -> Option<u32> {
    match s {
        Stmt::Throw(Expr::Local { var, .. }) => Some(*var),
        Stmt::Block(v) => v.last().and_then(trailing_rethrow_var),
        // The shared rethrow tail of a finally copy can be distributed
        // INTO the branches of a trailing if/else by the structurer
        // (jdk11 FilterOutputStream.close: both arms end `throw e3`):
        // recognize the shape when both branches rethrow the same var.
        Stmt::If { then_stmt, else_stmt: Some(e), .. } => {
            let a = trailing_rethrow_var(then_stmt)?;
            let b = trailing_rethrow_var(e)?;
            if a == b {
                Some(a)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Remove every trailing `throw rv` at the tail positions of `s` (the
/// distributed finally-rethrow shape: nested if/else branch tails).
fn remove_trailing_rethrow_stmt(s: &mut Stmt, rv: u32) {
    match s {
        Stmt::Throw(Expr::Local { var, .. }) if *var == rv => *s = Stmt::Block(vec![]),
        Stmt::Block(v) => {
            while matches!(v.last(), Some(Stmt::Throw(Expr::Local { var, .. })) if *var == rv) {
                v.pop();
            }
            if let Some(last) = v.last_mut() {
                remove_trailing_rethrow_stmt(last, rv);
            }
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            remove_trailing_rethrow_stmt(then_stmt, rv);
            if let Some(e) = else_stmt {
                remove_trailing_rethrow_stmt(e, rv);
            }
        }
        _ => {}
    }
}

fn remove_trailing_throw(s: &mut Vec<Stmt>) {
    while matches!(s.last(), Some(Stmt::Throw(_))) {
        s.pop();
    }
}

/// Remove a trailing copy of `fin` from the statement tree `s` (at any
/// nesting tail position). Returns true if a copy was removed.
fn strip_trailing_copies(s: &mut Stmt, fin: &[Stmt]) -> bool {
    if fin.is_empty() {
        return false;
    }
    match s {
        Stmt::Block(v) => {
            if v.len() >= fin.len() {
                let start = v.len() - fin.len();
                if v[start..] == fin[..] {
                    v.truncate(start);
                    return true;
                }
            }
            // copies followed by a trailing return/throw
            if let Some(last) = v.last() {
                if matches!(last, Stmt::Return(_) | Stmt::Throw(_)) && v.len() > fin.len() {
                    let start = v.len() - 1 - fin.len();
                    if v[start..start + fin.len()] == fin[..] {
                        let tail = v.remove(start + fin.len());
                        v.truncate(start);
                        v.push(tail);
                        return true;
                    }
                }
            }
            // descend into the last child tail
            if let Some(last) = v.last_mut() {
                if strip_trailing_copies(last, fin) {
                    return true;
                }
            }
            false
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            let a = strip_trailing_copies(then_stmt, fin);
            let b = else_stmt.as_mut().map(|e| strip_trailing_copies(e, fin)).unwrap_or(false);
            a || b
        }
        Stmt::Try { body, catches, finally } => {
            let mut r = strip_trailing_copies(body, fin);
            for c in catches.iter_mut() {
                r |= strip_trailing_copies(&mut c.body, fin);
            }
            if let Some(f) = finally {
                r |= strip_trailing_copies(f, fin);
            }
            r
        }
        Stmt::TryWithResources { body, catches, finally, .. } => {
            let mut r = strip_trailing_copies(body, fin);
            for c in catches.iter_mut() {
                r |= strip_trailing_copies(&mut c.body, fin);
            }
            if let Some(f) = finally {
                r |= strip_trailing_copies(f, fin);
            }
            r
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => strip_trailing_copies(body, fin),
        Stmt::For { body, .. } | Stmt::ForEach { body, .. } => strip_trailing_copies(body, fin),
        Stmt::Switch { cases, default, .. } => {
            let mut r = false;
            for c in cases.iter_mut() {
                for st in c.body.iter_mut() {
                    r |= strip_trailing_copies(st, fin);
                }
            }
            if let Some(d) = default {
                r |= strip_trailing_copies(d, fin);
            }
            r
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => strip_trailing_copies(body, fin),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// try-with-resources (J11+ shape)
// ---------------------------------------------------------------------------

/// J11+ TWR: `try { R r = init; body } catch (Throwable t) { r.close();
/// t.addSuppressed... }` where the catch is compiler boilerplate. Detect the
/// boilerplate (only calls to close/addSuppressed/getSuppressed/Throwable
/// ctor + rethrow) and drop the catch, adding the close call to a finally.
fn twr_j11(s: &mut Stmt) {
    match s {
        Stmt::Try { body, catches, finally } => {
            twr_j11(body);
            for c in catches.iter_mut() {
                twr_j11(&mut c.body);
            }
            if let Some(f) = finally.as_deref_mut() {
                twr_j11(f);
            }
            if finally.is_none() && catches.len() == 1 {
                let c = &catches[0];
                let is_throwable = c.exc.iter().any(|e| e == "java/lang/Throwable");
                if is_throwable && is_twr_boilerplate(&c.body) {
                    // Extract the close call(s) from the handler.
                    let closes = extract_close_calls(&c.body);
                    if !closes.is_empty() {
                        catches.clear();
                        *finally = Some(Box::new(Stmt::Block(closes)));
                    }
                }
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { twr_j11(res); }
            twr_j11(body);
            for c in catches.iter_mut() {
                twr_j11(&mut c.body);
            }
            if let Some(f) = finally.as_deref_mut() {
                twr_j11(f);
            }
            if finally.is_none() && catches.len() == 1 {
                let c = &catches[0];
                let is_throwable = c.exc.iter().any(|e| e == "java/lang/Throwable");
                if is_throwable && is_twr_boilerplate(&c.body) {
                    // Extract the close call(s) from the handler.
                    let closes = extract_close_calls(&c.body);
                    if !closes.is_empty() {
                        catches.clear();
                        *finally = Some(Box::new(Stmt::Block(closes)));
                    }
                }
            }
        }
        Stmt::Block(v) => {
            v.iter_mut().for_each(twr_j11);
            // Remove statements duplicating a try's fresh finally closes.
            let mut i = 0;
            while i < v.len() {
                if let Stmt::Try { finally: Some(f), .. } = &v[i] {
                    let closes = extract_close_calls(f);
                    if !closes.is_empty() {
                        let j = i + 1;
                        while j < v.len() {
                            if closes.iter().any(|c| *c == v[j]) {
                                v.remove(j);
                            } else {
                                break;
                            }
                        }
                    }
                }
                i += 1;
            }
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            twr_j11(then_stmt);
            if let Some(e) = else_stmt {
                twr_j11(e);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => twr_j11(body),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(twr_j11);
            twr_j11(body);
        }
        Stmt::ForEach { body, .. } => twr_j11(body),
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(twr_j11);
            }
            if let Some(d) = default {
                twr_j11(d);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => twr_j11(body),
        _ => {}
    }
}

fn is_twr_boilerplate(s: &Stmt) -> bool {
    let v = stmt_vec_ref(s);
    if v.is_empty() {
        return false;
    }
    v.iter().all(|st| match st {
        Stmt::Throw(_) => true,
        Stmt::If { cond, then_stmt, else_stmt } => {
            is_null_check(cond)
                && is_twr_boilerplate(then_stmt)
                && else_stmt.as_ref().map(|e| is_twr_boilerplate(e)).unwrap_or(true)
        }
        Stmt::ExprStmt(Expr::Method { name, cls, .. }) => {
            name == "close"
                || name == "addSuppressed"
                || name == "getSuppressed"
                || name == "<init>" && cls == "java/lang/Throwable"
        }
        Stmt::ExprStmt(Expr::Assign { .. }) => true,
        Stmt::LocalDef { .. } => true,
        Stmt::Block(inner) => inner.iter().all(|x| is_twr_boilerplate(x)),
        _ => false,
    })
}

fn stmt_vec_ref(s: &Stmt) -> Vec<Stmt> {
    match s {
        Stmt::Block(v) => v.clone(),
        other => vec![other.clone()],
    }
}

fn is_null_check(e: &Expr) -> bool {
    matches!(e, Expr::Bin { op: crate::expr::BinOp::RefEq | crate::expr::BinOp::RefNe, r, .. }
        if matches!(&**r, Expr::Const(ConstVal::Null)))
}

/// Pull `x.close()` calls out of the boilerplate handler.
fn extract_close_calls(s: &Stmt) -> Vec<Stmt> {
    let mut out = Vec::new();
    collect_close(s, &mut out);
    out
}

fn collect_close(s: &Stmt, out: &mut Vec<Stmt>) {
    match s {
        Stmt::Block(v) => v.iter().for_each(|x| collect_close(x, out)),
        Stmt::If { then_stmt, else_stmt, .. } => {
            collect_close(then_stmt, out);
            if let Some(e) = else_stmt {
                collect_close(e, out);
            }
        }
        Stmt::ExprStmt(e @ Expr::Method { name, .. }) if name == "close" => {
            out.push(Stmt::ExprStmt(e.clone()));
        }
        _ => {}
    }
}


// Recursively fold 0/1-valued conditionals whose branches are both
// constants into plain boolean expressions, bottom-up. Runs after all
// diamond folds so nested chains booleanize correctly.
thread_local! {
    /// Depth of arithmetic/bitwise Bin nodes currently being booleanized;
    /// `c ? 1 : 0` must not collapse to `c` inside one.
    static NUMERIC_CTX: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Under a numeric parent, a booleanized condition must re-wrap as an
/// int `? 1 : 0` conditional; otherwise the boolean form is returned.
fn wrap_num(numeric_parent: bool, b: crate::expr::Expr) -> crate::expr::Expr {
    use crate::expr::{ConstVal, Expr};
    if !numeric_parent {
        return b;
    }
    Expr::Cond {
        c: Box::new(b),
        t: Box::new(Expr::Const(ConstVal::Int(1))),
        f: Box::new(Expr::Const(ConstVal::Int(0))),
    }
}

/// Fold an already-built condition's nested 0/1 int diamonds to boolean
/// form (`isLinker ? (customized ? 0 : 1) : 0` -> `isLinker && !customized`).
fn boolify_cond_deep(e: crate::expr::Expr) -> crate::expr::Expr {
    use crate::expr::{ConstVal, Expr, UnOp};
    let mk_not = |x: Expr| match x {
        Expr::Un { op: UnOp::Not, e } => *e,
        other => Expr::Un { op: UnOp::Not, e: Box::new(other) },
    };
    match e {
        Expr::Cond { c, t, f } => {
            let c2 = boolify_cond_deep(*c);
            let one_zero = matches!(&*t, Expr::Const(ConstVal::Int(1)))
                && matches!(&*f, Expr::Const(ConstVal::Int(0)));
            let zero_one = matches!(&*t, Expr::Const(ConstVal::Int(0)))
                && matches!(&*f, Expr::Const(ConstVal::Int(1)));
            if one_zero {
                return c2;
            }
            if zero_one {
                return mk_not(c2);
            }
            let is01 = |x: &Expr| {
                matches!(x, Expr::Const(ConstVal::Int(0 | 1)))
                    || matches!(x, Expr::Cond { t: tt, f: ff, .. }
                        if matches!(&**tt, Expr::Const(ConstVal::Int(0 | 1)))
                            && matches!(&**ff, Expr::Const(ConstVal::Int(0 | 1))))
            };
            let bool_of = |x: Expr| -> Expr {
                if let Expr::Cond { c: xc, t: xt, f: xf } = &x {
                    let oz = matches!(&**xt, Expr::Const(ConstVal::Int(1)))
                        && matches!(&**xf, Expr::Const(ConstVal::Int(0)));
                    let zo = matches!(&**xt, Expr::Const(ConstVal::Int(0)))
                        && matches!(&**xf, Expr::Const(ConstVal::Int(1)));
                    if oz {
                        return boolify_cond_deep((**xc).clone());
                    }
                    if zo {
                        return mk_not(boolify_cond_deep((**xc).clone()));
                    }
                }
                boolify_cond_deep(x)
            };
            let t_is1 = matches!(&*t, Expr::Const(ConstVal::Int(1)));
            let t_is0 = matches!(&*t, Expr::Const(ConstVal::Int(0)));
            let f_is1 = matches!(&*f, Expr::Const(ConstVal::Int(1)));
            let f_is0 = matches!(&*f, Expr::Const(ConstVal::Int(0)));
            if t_is1 && is01(&f) {
                Expr::Bin { op: crate::expr::BinOp::LogOr, l: Box::new(c2), r: Box::new(bool_of(*f)), ty: None }
            } else if t_is0 && is01(&f) {
                Expr::Bin { op: crate::expr::BinOp::LogAnd, l: Box::new(mk_not(c2)), r: Box::new(bool_of(*f)), ty: None }
            } else if is01(&t) && f_is1 {
                Expr::Bin { op: crate::expr::BinOp::LogOr, l: Box::new(mk_not(c2)), r: Box::new(bool_of(*t)), ty: None }
            } else if is01(&t) && f_is0 {
                Expr::Bin { op: crate::expr::BinOp::LogAnd, l: Box::new(c2), r: Box::new(bool_of(*t)), ty: None }
            } else {
                Expr::Cond { c: Box::new(c2), t: boolify_cond_deep(*t).into(), f: boolify_cond_deep(*f).into() }
            }
        }
        other => other,
    }
}

fn booleanize_deep(e: &mut crate::expr::Expr) {
    use crate::expr::{BinOp, ConstVal, Expr, UnOp};
    match e {
        Expr::Cond { c, t, f } => {
            booleanize_deep(c);
            // A branch holding a non-0/1 int makes this an arithmetic
            // ternary: the sibling `c ? 1 : 0` must not collapse to a
            // boolean (`x >= y ? x != y : -1` is ill-typed).
            let sibling_numeric = |x: &Expr| -> bool {
                match x {
                    Expr::Const(ConstVal::Int(n)) => *n != 0 && *n != 1,
                    Expr::Const(ConstVal::Long(_)) => true,
                    Expr::Cond { .. } | Expr::Un { .. } | Expr::InstanceOf { .. } => false,
                    other => {
                        let e = other.type_ref().erased();
                        matches!(
                            e,
                            JavaType::Int | JavaType::Long | JavaType::Short
                                | JavaType::Byte | JavaType::Char | JavaType::Float
                                | JavaType::Double
                        )
                    }
                }
            };
            let numeric_branches = sibling_numeric(t) || sibling_numeric(f);
            if numeric_branches {
                NUMERIC_CTX.with(|n| n.set(n.get() + 1));
            }
            booleanize_deep(t);
            booleanize_deep(f);
            if numeric_branches {
                NUMERIC_CTX.with(|n| n.set(n.get() - 1));
            }
            fn mk_not(x: Expr) -> Expr {
                if let Expr::Un { op: UnOp::Not, e } = x {
                    *e
                } else {
                    Expr::Un { op: UnOp::Not, e: Box::new(x) }
                }
            }
            let cc = (**c).clone();
            let is_true = |x: &Expr| {
                matches!(x, Expr::Const(ConstVal::Int(1)))
            };
            let is_false = |x: &Expr| {
                matches!(x, Expr::Const(ConstVal::Int(0)))
            };
            let is_bool = |x: &Expr| {
                x.type_ref().erased() == JavaType::Boolean
                    || matches!(x, Expr::Cond { t, f, .. }
                        if (matches!(&**t, Expr::Const(ConstVal::Int(0 | 1)))
                            && matches!(&**f, Expr::Const(ConstVal::Int(0 | 1)))))
            };
            // A 0/1 ternary glued into a logical operator must appear in
            // BOOLEAN form (`a && (b ? 0 : 1)` is "二元运算符&&的操作数
            // 类型错误", jdk17 Invokers INARG_LIMIT): `x ? 1 : 0` -> x,
            // `x ? 0 : 1` -> !x.
            let boolify = |x: &Expr| -> Expr {
                if let Expr::Cond { c: xc, t: xt, f: xf } = x {
                    let one_zero = matches!(&**xt, Expr::Const(ConstVal::Int(1)))
                        && matches!(&**xf, Expr::Const(ConstVal::Int(0)));
                    let zero_one = matches!(&**xt, Expr::Const(ConstVal::Int(0)))
                        && matches!(&**xf, Expr::Const(ConstVal::Int(1)));
                    if one_zero {
                        return (**xc).clone();
                    }
                    if zero_one {
                        return mk_not((**xc).clone());
                    }
                }
                x.clone()
            };
            // `c ? 1 : 0` may only collapse to `c` when the value is used
            // as a truth value; under arithmetic/bitwise operators the int
            // form must survive (`refKind * 2 + (isInterface ? 1 : 0)`).
            let numeric_parent = NUMERIC_CTX.with(|n| n.get() > 0);
            let repl = match (&**t, &**f) {
                (t_, f_) if is_true(t_) && is_false(f_) && !numeric_parent => Some(cc.clone()),
                (t_, f_) if is_false(t_) && is_true(f_) && !numeric_parent => Some(mk_not(cc.clone())),
                // Under arithmetic/bitwise parents the int `? 1 : 0` /
                // `? 0 : 1` form must SURVIVE as an int; fold only the
                // condition to its boolean shape (jdk17 Invokers:
                // `OUTARG_LIMIT + (isLinker && !customized ? 1 : 0)`).
                (t_, f_) if is_true(t_) && is_false(f_) && numeric_parent => {
                    Some(Expr::Cond {
                        c: Box::new(boolify_cond_deep(cc.clone())),
                        t: Box::new(Expr::Const(ConstVal::Int(1))),
                        f: Box::new(Expr::Const(ConstVal::Int(0))),
                    })
                }
                (t_, f_) if is_false(t_) && is_true(f_) && numeric_parent => {
                    Some(Expr::Cond {
                        c: Box::new(mk_not(boolify_cond_deep(cc.clone()))),
                        t: Box::new(Expr::Const(ConstVal::Int(1))),
                        f: Box::new(Expr::Const(ConstVal::Int(0))),
                    })
                }
                // Mixed: one side is a boolean constant, the other a
                // boolean expression → short-circuit operator.
                (t_, f_) if is_true(t_) && is_bool(f_) => Some(wrap_num(
                    numeric_parent,
                    Expr::Bin {
                        op: BinOp::LogOr, l: Box::new(cc.clone()), r: Box::new(boolify(f_)), ty: None,
                    },
                )),
                (t_, f_) if is_false(t_) && is_bool(f_) => Some(wrap_num(
                    numeric_parent,
                    Expr::Bin {
                        op: BinOp::LogAnd,
                        l: Box::new(mk_not(cc.clone())),
                        r: Box::new(boolify(f_)), ty: None,
                    },
                )),
                (t_, f_) if is_bool(t_) && is_true(f_) => Some(wrap_num(
                    numeric_parent,
                    Expr::Bin {
                        op: BinOp::LogOr,
                        l: Box::new(mk_not(cc.clone())),
                        r: Box::new(boolify(t_)), ty: None,
                    },
                )),
                (t_, f_) if is_bool(t_) && is_false(f_) => Some(wrap_num(
                    numeric_parent,
                    Expr::Bin {
                        op: BinOp::LogAnd, l: Box::new(cc.clone()), r: Box::new(boolify(t_)), ty: None,
                    },
                )),
                _ => None,
            };
            if let Some(r) = repl {
                *e = r;
            }
        }
        Expr::Un { e: inner, .. } => {
            booleanize_deep(inner);
            if let Expr::Un { op: UnOp::Not, e: inner2 } = &**inner {
                let x = (**inner2).clone();
                *e = x;
            }
        }
        Expr::Bin { op, l, r, ty } => {
            // For and/or/xor the operand kind decides: a boolean side (or a
            // 0/1 ternary facing a boolean side) makes it a logical
            // operator, where `c ? 1 : 0` may still collapse to `c`.
            let bool_side = |x: &Expr, other: &Expr| {
                let zero_one_tern = |t: &Expr, f: &Expr| {
                    matches!(t, Expr::Const(ConstVal::Int(0 | 1)))
                        && matches!(f, Expr::Const(ConstVal::Int(0 | 1)))
                };
                match x {
                    Expr::Un { op: UnOp::Not, .. } | Expr::InstanceOf { .. } => true,
                    Expr::Bin { op: xo, .. } => matches!(
                        xo,
                        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Ge | BinOp::Gt
                            | BinOp::Le | BinOp::RefEq | BinOp::RefNe
                            | BinOp::LogAnd | BinOp::LogOr
                    ),
                    Expr::Cond { t, f, .. } => {
                        zero_one_tern(t, f)
                            && matches!(other.type_ref().erased(), JavaType::Boolean)
                    }
                    _ => x.type_ref().erased() == JavaType::Boolean,
                }
            };
            // Ordering comparisons are numeric-only in Java: their operand
            // positions must keep int `? 1 : 0` forms (jdk26
            // FloatingDecimal: `i - start > (pt != 0 ? 1 : 0)` folded the
            // RHS to boolean — "二元运算符 '<=' 的操作数类型错误").
            // Eq/Ne operands are numeric when either side is a primitive
            // number (bool==bool stays foldable).
            let cmp_numeric = |a: &Expr, b: &Expr| {
                let prim = |x: &Expr| {
                    matches!(
                        x.type_ref().erased(),
                        JavaType::Int | JavaType::Long | JavaType::Short
                            | JavaType::Byte | JavaType::Char | JavaType::Float
                            | JavaType::Double
                    )
                };
                // Any boolean side makes the comparison a BOOLEAN context:
                // a facing 0/1 ternary must fold to bool (`flag == (c ? 1
                // : 0)` → `flag == c`; keeping the int form is "二元运算
                // 符 '==' 的操作数类型错误"). Only pure-primitive equality
                // keeps int operands.
                let bool_ish = |x: &Expr| {
                    matches!(x.type_ref().erased(), JavaType::Boolean)
                        || matches!(
                            x,
                            Expr::Un { op: crate::expr::UnOp::Not, .. } | Expr::InstanceOf { .. }
                        )
                };
                if bool_ish(a) || bool_ish(b) {
                    return false;
                }
                prim(a) || prim(b)
            };
            let numeric = match op {
                BinOp::Lt | BinOp::Ge | BinOp::Gt | BinOp::Le => true,
                BinOp::Eq | BinOp::Ne => cmp_numeric(l, r),
                BinOp::RefEq | BinOp::RefNe | BinOp::LogAnd | BinOp::LogOr
                | BinOp::StrCat => false,
                BinOp::And | BinOp::Or | BinOp::Xor => !(bool_side(l, r) || bool_side(r, l)),
                _ => true,
            };
            if numeric {
                NUMERIC_CTX.with(|n| n.set(n.get() + 1));
            }
            booleanize_deep(l);
            booleanize_deep(r);
            if numeric {
                NUMERIC_CTX.with(|n| n.set(n.get() - 1));
            }
            // Java-level boolean expressions: comparisons and logical ops
            // are boolean regardless of the Int merge type the builder
            // records for their operands.
            fn boolish(x: &Expr) -> bool {
                match x {
                    Expr::Un { op: UnOp::Not, .. } | Expr::InstanceOf { .. } => true,
                    Expr::Bin { op, l, r, .. } => match op {
                        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Ge | BinOp::Gt
                        | BinOp::Le | BinOp::RefEq | BinOp::RefNe | BinOp::LogAnd
                        | BinOp::LogOr => true,
                        BinOp::And | BinOp::Or | BinOp::Xor => boolish(l) && boolish(r),
                        _ => false,
                    },
                    _ => x.type_ref().erased() == JavaType::Boolean,
                }
            }
            // A bitwise and/or/xor whose sides booleanized to boolean
            // expressions is a Java boolean operator: drop the Int merge
            // type so `|`/`&` type-check (and `!= 0` can collapse).
            if matches!(op, BinOp::And | BinOp::Or | BinOp::Xor) && boolish(l) && boolish(r) {
                *ty = None;
            }
            // `b == 0` / `b != 0` on booleans collapse to !b / b.
            if matches!(op, BinOp::Eq | BinOp::Ne)
                && matches!(&**r, Expr::Const(ConstVal::Int(0)))
                && (l.type_ref().erased() == JavaType::Boolean || boolish(l))
            {
                let inner = (**l).clone();
                *e = match op {
                    BinOp::Eq => Expr::Un { op: UnOp::Not, e: Box::new(inner) },
                    _ => inner,
                };
            }
        }
        Expr::Assign { target, value, .. } => {
            booleanize_deep(target);
            booleanize_deep(value);
        }
        Expr::StringConcat(parts) => {
            for p in parts.iter_mut() {
                match p {
                    crate::expr::ConcatPart::Str(x) => booleanize_deep(x),
                    _ => {}
                }
            }
        }
        Expr::Method { args, desc, .. } => {
            // An argument at an INT-typed parameter position must keep its
            // int form: `out.write(v ? 1 : 0)` folded to `out.write(v)`
            // selects no overload ("对于write(boolean), 找不到合适的方法",
            // jdk11 DataOutputStream.writeBoolean; Formatter
            // localizedMagnitude's int offset param). Boolean parameters
            // (and reference positions, which are rare for 0/1 ternaries)
            // keep the collapse.
            for (i, a) in args.iter_mut().enumerate() {
                let numeric_param = desc
                    .args
                    .get(i)
                    .map(|p| {
                        matches!(
                            p,
                            JavaType::Int | JavaType::Long | JavaType::Short
                                | JavaType::Byte | JavaType::Char | JavaType::Float
                                | JavaType::Double
                        )
                    })
                    .unwrap_or(false);
                if numeric_param {
                    NUMERIC_CTX.with(|n| n.set(n.get() + 1));
                    booleanize_deep(a);
                    NUMERIC_CTX.with(|n| n.set(n.get() - 1));
                } else {
                    booleanize_deep(a);
                }
            }
        }
        Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
            for a in args.iter_mut() {
                booleanize_deep(a);
            }
        }
        Expr::NewArray { dims, init, .. } => {
            // Sizes are int positions: no boolean collapse.
            for d in dims.iter_mut() {
                NUMERIC_CTX.with(|n| n.set(n.get() + 1));
                booleanize_deep(d);
                NUMERIC_CTX.with(|n| n.set(n.get() - 1));
            }
            if let Some(vals) = init {
                vals.iter_mut().for_each(booleanize_deep);
            }
        }
        Expr::ArrayIndex { array, index } => {
            booleanize_deep(array);
            NUMERIC_CTX.with(|n| n.set(n.get() + 1));
            booleanize_deep(index);
            NUMERIC_CTX.with(|n| n.set(n.get() - 1));
        }
        Expr::Cast { ty, e: x } => {
            // A cast to a numeric primitive is an int context: the inner
            // 0/1 ternary must survive as int (`(long) (c ? 1 : 0)` —
            // jdk11 Year/MinguoDate getEraYear; folding to boolean gave
            // "boolean无法转换为long").
            let numeric = matches!(
                ty.erased(),
                JavaType::Long | JavaType::Int | JavaType::Short | JavaType::Byte
                    | JavaType::Char | JavaType::Float | JavaType::Double
            );
            if numeric {
                NUMERIC_CTX.with(|n| n.set(n.get() + 1));
            }
            booleanize_deep(x);
            if numeric {
                NUMERIC_CTX.with(|n| n.set(n.get() - 1));
            }
        }
        Expr::InstanceOf { e: x, .. } => booleanize_deep(x),
        Expr::Field { owner: Some(o), .. } => booleanize_deep(o),
        _ => {}
    }
}

fn booleanize_deep_stmt(s: &mut Stmt) {
    booleanize_deep_stmt_r(s, false, &jcdc_jvm::JavaType::Int)
}

/// `numeric_ret`: the enclosing method returns a numeric (non-boolean)
/// type. A booleanized top-level return expression is then re-wrapped as
/// `e ? 1 : 0` — a poly conditional whose constant branches narrow to the
/// target type, so `byte bool2byte(boolean b)` keeps compiling instead of
/// emitting `return b;` (boolean -> byte error, jdk Unsafe family).
fn booleanize_deep_stmt_r(s: &mut Stmt, numeric_ret: bool, ret_ty: &jcdc_jvm::JavaType) {
    match s {
        Stmt::Block(v) => v.iter_mut().for_each(|x| booleanize_deep_stmt_r(x, numeric_ret, ret_ty)),
        Stmt::ExprStmt(e) => booleanize_deep(e),
        Stmt::LocalDef { init: Some(e), .. } => booleanize_deep(e),
        Stmt::Return(Some(e)) => {
            booleanize_deep(e);
            if numeric_ret && e.type_ref().erased() == jcdc_jvm::JavaType::Boolean {
                let c = std::mem::replace(e, crate::expr::Expr::Const(crate::expr::ConstVal::Null));
                // byte/short returns need narrowed constants: a plain
                // `b ? 1 : 0` poly conditional does NOT narrow through
                // the return conversion (jdk Unsafe.copyMemory family:
                // "possible lossy conversion from int to byte").
                let mk = |n: i32| {
                    let k = crate::expr::Expr::Const(crate::expr::ConstVal::Int(n));
                    match ret_ty {
                        jcdc_jvm::JavaType::Byte | jcdc_jvm::JavaType::Short => {
                            crate::expr::Expr::Cast {
                                ty: crate::expr::TypeRef::J(ret_ty.clone()),
                                e: Box::new(k),
                            }
                        }
                        _ => k,
                    }
                };
                *e = crate::expr::Expr::Cond {
                    c: Box::new(c),
                    t: Box::new(mk(1)),
                    f: Box::new(mk(0)),
                };
            }
        }
        Stmt::Throw(e) => booleanize_deep(e),
        Stmt::If { cond, then_stmt, else_stmt } => {
            booleanize_deep(cond);
            booleanize_deep_stmt_r(then_stmt, numeric_ret, ret_ty);
            if let Some(x) = else_stmt {
                booleanize_deep_stmt_r(x, numeric_ret, ret_ty);
            }
        }
        Stmt::While { cond, body } | Stmt::DoWhile { cond, body } => {
            booleanize_deep(cond);
            booleanize_deep_stmt_r(body, numeric_ret, ret_ty);
        }
        Stmt::For { init, cond, update, body } => {
            init.iter_mut().for_each(|x| booleanize_deep_stmt_r(x, numeric_ret, ret_ty));
            if let Some(c) = cond {
                booleanize_deep(c);
            }
            update.iter_mut().for_each(booleanize_deep);
            booleanize_deep_stmt_r(body, numeric_ret, ret_ty);
        }
        Stmt::ForEach { .. } => {}
        Stmt::Labeled { body, .. } | Stmt::Synchronized { body, .. } => {
            booleanize_deep_stmt_r(body, numeric_ret, ret_ty)
        }
        Stmt::Try { body, catches, finally } => {
            booleanize_deep_stmt_r(body, numeric_ret, ret_ty);
            for c in catches {
                booleanize_deep_stmt_r(&mut c.body, numeric_ret, ret_ty);
            }
            if let Some(f) = finally {
                booleanize_deep_stmt_r(f, numeric_ret, ret_ty);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { booleanize_deep_stmt_r(res, numeric_ret, ret_ty); }
            booleanize_deep_stmt_r(body, numeric_ret, ret_ty);
            for c in catches {
                booleanize_deep_stmt_r(&mut c.body, numeric_ret, ret_ty);
            }
            if let Some(f) = finally {
                booleanize_deep_stmt_r(f, numeric_ret, ret_ty);
            }
        }
        Stmt::Switch { selector, cases, default, .. } => {
            booleanize_deep(selector);
            for c in cases {
                c.body.iter_mut().for_each(|x| booleanize_deep_stmt_r(x, numeric_ret, ret_ty));
            }
            if let Some(d) = default {
                booleanize_deep_stmt_r(d, numeric_ret, ret_ty);
            }
        }
        Stmt::Assert { cond, msg } => {
            booleanize_deep(cond);
            if let Some(m) = msg {
                booleanize_deep(m);
            }
        }
        _ => {}
    }
}


// ---------------------------------------------------------------------------
// try-with-resources (J7 shape)
// ---------------------------------------------------------------------------

/// Restore javac 7 try-with-resources:
/// ```text
/// R in = new R(...);
/// Throwable $p = null;
/// try { body }
/// catch (Throwable t) { $p = t; throw t; }
/// finally { <guarded in.close() with $p checks> }
/// <normal-path close scaffolding on in / $p>
/// ```
/// becomes `try (R in = new R(...)) { body }`.
fn twr_j7(s: &mut Stmt) {
    match s {
        Stmt::Block(v) => {
            let mut i = 0;
            while i < v.len() {
                twr_j7(&mut v[i]);
                if std::env::var("JCDC_DBG_TWR").is_ok() {
                    if let Stmt::Try { catches, finally, .. } = &v[i] {
                        eprintln!("TWR scan i={} catches={} excs={:?} finally={}", i, catches.len(),
                            catches.iter().map(|c| c.exc.clone()).collect::<Vec<_>>(), finally.is_some());
                    }
                }
                let plan = match &v[i] {
                    Stmt::Try { .. } => match_j7(v, i),
                    _ => None,
                };
                if let Some(plan) = plan {
                    apply_j7(v, i, &plan);
                    // Drop the consumed resource/primary-init statements and
                    // the trailing normal-path close scaffolding.
                    v.retain(|x| !x.is_empty_block());
                    i = v
                        .iter()
                        .position(|x| matches!(x, Stmt::TryWithResources { .. }))
                        .map(|p| p + 1)
                        .unwrap_or(i);
                    while i < v.len() {
                        let ok = is_close_scaffold_stmt(&v[i]);
                        if std::env::var("JCDC_DBG_TWR").is_ok() {
                            let d = format!("{:?}", &v[i]);
                            eprintln!("TWR strip i={} ok={} head={}", i, ok, d.lines().next().unwrap_or(""));
                        }
                        if !ok {
                            break;
                        }
                        v.remove(i);
                    }
                    // Statements between the (now removed) scaffolding and
                    // the next control-flow boundary executed only on the
                    // try's normal path — inside the try they keep that
                    // semantics, and code after an all-terminating switch
                    // would be unreachable.
                    let twr_at = v
                        .iter()
                        .position(|x| matches!(x, Stmt::TryWithResources { .. }));
                    // Absorption is only sound when the try body ends in a
                    // switch whose every arm terminates (then the following
                    // statements ran exclusively on one of those arms).
                    fn switch_terminates(b: &Stmt) -> bool {
                        let mut cur = b;
                        loop {
                            match cur {
                                Stmt::Block(v) => match v.last() {
                                    Some(x) => cur = x,
                                    None => return false,
                                },
                                Stmt::Switch { cases, default, .. } => {
                                    let arm_ok = |s: &Stmt| -> bool {
                                        let mut c = s;
                                        loop {
                                            match c {
                                                Stmt::Block(v) => match v.last() {
                                                    Some(x) => c = x,
                                                    None => return false,
                                                },
                                                Stmt::Return(_) | Stmt::Throw(_) => return true,
                                                _ => return false,
                                            }
                                        }
                                    };
                                    return cases.iter().all(|c| {
                                        c.body.iter().all(|x| arm_ok(x)) || c.body.is_empty()
                                    }) && match default {
                                        Some(d) => arm_ok(d),
                                        None => false,
                                    };
                                }
                                _ => return false,
                            }
                        }
                    }
                    let body_ends_switch = twr_at
                        .and_then(|ti| match &v[ti] {
                            Stmt::TryWithResources { body, .. } => Some(switch_terminates(body)),
                            _ => None,
                        })
                        .unwrap_or(false);
                    if let Some(ti) = twr_at.filter(|_| body_ends_switch) {
                        let mut j = ti + 1;
                        let mut absorb: Vec<Stmt> = Vec::new();
                        while j < v.len() {
                            let is_plain = matches!(&v[j],
                                Stmt::ExprStmt(_) | Stmt::LocalDef { .. } | Stmt::Return(_) | Stmt::Throw(_));
                            if !is_plain {
                                break;
                            }
                            absorb.push(std::mem::replace(&mut v[j], Stmt::Block(vec![])));
                            j += 1;
                        }
                        // Only safe when the absorbed run ends the block
                        // with a terminator: otherwise the statements may
                        // belong to an enclosing finally-dedup pattern or
                        // to the post-try flow.
                        let ends_terminating = matches!(
                            absorb.last(),
                            Some(Stmt::Return(_)) | Some(Stmt::Throw(_))
                        );
                        if !ends_terminating {
                            for (k, st) in absorb.into_iter().enumerate() {
                                v[ti + 1 + k] = st;
                            }
                            absorb = Vec::new();
                        }
                        if !absorb.is_empty() {
                            if let Stmt::TryWithResources { body, .. } = &mut v[ti] {
                                match &mut **body {
                                    Stmt::Block(bv) => bv.append(&mut absorb),
                                    other => {
                                        let old = std::mem::replace(other, Stmt::Block(vec![]));
                                        let mut bv = vec![old];
                                        bv.append(&mut absorb);
                                        *other = Stmt::Block(bv);
                                    }
                                }
                            }
                            v.retain(|x| !x.is_empty_block());
                        }
                    }
                    continue;
                }
                i += 1;
            }
        }
        Stmt::Try { body, catches, finally } => {
            twr_j7(body);
            for c in catches.iter_mut() {
                twr_j7(&mut c.body);
            }
            if let Some(f) = finally {
                twr_j7(f);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { twr_j7(res); }
            twr_j7(body);
            for c in catches.iter_mut() {
                twr_j7(&mut c.body);
            }
            if let Some(f) = finally {
                twr_j7(f);
            }
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            twr_j7(then_stmt);
            if let Some(e) = else_stmt {
                twr_j7(e);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => twr_j7(body),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(twr_j7);
            twr_j7(body);
        }
        Stmt::ForEach { body, .. } => twr_j7(body),
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(twr_j7);
            }
            if let Some(d) = default {
                twr_j7(d);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => twr_j7(body),
        _ => {}
    }
}

fn flatten_stmts(s: &Stmt) -> Vec<Stmt> {
    let mut out = Vec::new();
    fn rec(s: &Stmt, out: &mut Vec<Stmt>) {
        match s {
            Stmt::Block(v) => v.iter().for_each(|x| rec(x, out)),
            other => out.push(other.clone()),
        }
    }
    rec(s, &mut out);
    out.retain(|x| !x.is_empty_block());
    out
}

/// Find the close target (`X.close()`) inside a finally scaffold.
fn close_target(f: &Stmt) -> Option<u32> {
    fn rec(e: &Expr) -> Option<u32> {
        match e {
            Expr::Method { name, owner, args, .. } if name == "close" && args.is_empty() => {
                match owner.as_deref() {
                    Some(Expr::Local { var, .. }) => return Some(*var),
                    _ => {}
                }
            }
            Expr::Method { owner: Some(o), args, .. } => {
                if let Some(v) = rec(o) {
                    return Some(v);
                }
                for a in args {
                    if let Some(v) = rec(a) {
                        return Some(v);
                    }
                }
            }
            _ => {}
        }
        None
    }
    for st in flatten_stmts(f) {
        match &st {
            Stmt::ExprStmt(e) => {
                if let Some(v) = rec(e) {
                    return Some(v);
                }
            }
            Stmt::If { cond, then_stmt, else_stmt } => {
                for sub in std::iter::once(then_stmt.as_ref()).chain(else_stmt.as_deref()) {
                    if let Some(v) = close_target(sub) {
                        return Some(v);
                    }
                }
                let _ = cond;
            }
            Stmt::Try { body, catches, finally } => {
                if let Some(v) = close_target(body) {
                    return Some(v);
                }
                for c in catches {
                    if let Some(v) = close_target(&c.body) {
                        return Some(v);
                    }
                }
                if let Some(f2) = finally {
                    if let Some(v) = close_target(f2) {
                        return Some(v);
                    }
                }
            }
        Stmt::TryWithResources { body, catches, finally, .. } => {
                if let Some(v) = close_target(body) {
                    return Some(v);
                }
                for c in catches {
                    if let Some(v) = close_target(&c.body) {
                        return Some(v);
                    }
                }
                if let Some(f2) = finally {
                    if let Some(v) = close_target(f2) {
                        return Some(v);
                    }
                }
            }
            _ => {}
        }
    }
    None
}

struct J7Plan {
    res_idx: usize,
    init_idxs: Vec<usize>,
    keep_catches: Vec<crate::stmt::Catch>,
    #[allow(dead_code)]
    try_idx: usize,
}

/// Read-only match of the javac-7 TWR shape at `v[i]`. The close scaffold
/// sits either in a `finally` (after dedupe) or in a trailing catch-all
/// handler (before dedupe).
fn match_j7(v: &[Stmt], i: usize) -> Option<J7Plan> {
    let dbg = std::env::var("JCDC_DBG_TWR").is_ok();
    let (body, catches, finally) = match &v[i] {
        Stmt::Try { body, catches, finally } => (body.as_ref(), catches.as_slice(), finally.as_deref()),
        _ => return None,
    };
    let mut primary_var: Option<u32> = None;
    let mut keep_catches: Vec<crate::stmt::Catch> = Vec::new();
    let mut scaffold: Option<&Stmt> = None;
    for c in catches {
        let hs = flatten_stmts(&c.body);
        // synthetic `$p = t; throw t;` rethrow catch
        let mut synth = hs.iter().any(|h| matches!(h, Stmt::Throw(_)));
        for h in &hs {
            match h {
                Stmt::ExprStmt(Expr::Assign { target, value, .. }) => {
                    let mut note = |tv: u32, ev: u32| {
                        if ev == c.var {
                            match primary_var {
                                Some(p) if p == tv => {}
                                None => primary_var = Some(tv),
                                _ => synth = false,
                            }
                        } else {
                            synth = false;
                        }
                    };
                    match (&**target, &**value) {
                        (Expr::Local { var: tv, .. }, Expr::Local { var: ev, .. }) => note(*tv, *ev),
                        _ => synth = false,
                    }
                }
                Stmt::LocalDef { var: tv, init: Some(Expr::Local { var: ev, .. }), .. } => {
                    if *ev == c.var {
                        match primary_var {
                            Some(p) if p == *tv => {}
                            None => primary_var = Some(*tv),
                            _ => synth = false,
                        }
                    } else {
                        synth = false;
                    }
                }
                Stmt::Throw(e) => {
                    if !matches!(e, Expr::Local { var, .. } if *var == c.var) {
                        synth = false;
                    }
                }
                _ => synth = false,
            }
        }
        if synth {
            continue; // dropped
        }
        // catch-all (or Throwable-typed) handler holding the close
        // scaffolding (pre-dedupe finally shapes)
        let scaffolding_exc = c.exc.is_empty()
            || (c.exc.len() == 1 && c.exc[0] == "java/lang/Throwable");
        if scaffolding_exc && finally.is_none() && scaffold.is_none() {
            let ok = is_close_scaffold_stmt(&c.body);
            if dbg && !ok {
                for h in flatten_stmts(&c.body) {
                    let d = format!("{:?}", h);
                    eprintln!("TWR scaffold stmt: {}", d.lines().next().unwrap_or(""));
                }
            }
            if ok {
                scaffold = Some(&c.body);
                continue; // dropped
            }
        }
        keep_catches.push(c.clone());
    }
    let close_src = match (finally, scaffold) {
        (Some(f), _) => f,
        (None, Some(sc)) => sc,
        (None, None) => {
            if dbg { eprintln!("TWR reject: no close source at {}", i); }
            return None;
        }
    };
    let Some(r_var) = close_target(close_src) else {
        if dbg { eprintln!("TWR reject: no close target"); }
        return None;
    };
    if dbg { eprintln!("TWR r_var={} primary={:?}", r_var, primary_var); }
    // Locate preceding statements: optional primary-init, required resource def.
    let mut res_idx: Option<usize> = None;
    let mut init_idxs: Vec<usize> = Vec::new();
    let mut j = i;
    while j > 0 {
        j -= 1;
        match &v[j] {
            Stmt::LocalDef { var, init, .. } if *var == r_var && init.is_some() && res_idx.is_none() => {
                res_idx = Some(j);
                break;
            }
            Stmt::LocalDef { var, init, .. }
                if Some(*var) == primary_var
                    && matches!(init, None | Some(Expr::Const(ConstVal::Null))) =>
            {
                init_idxs.push(j);
            }
            Stmt::LocalDef { .. } | Stmt::ExprStmt(_) => {}
            _ => break,
        }
    }
    let Some(ri) = res_idx else {
        if dbg { eprintln!("TWR reject: no resource def found"); }
        return None;
    };
    // A TWR resource is FINAL: reassignment inside the body means a
    // hand-rolled try (sun PKCS7: `bais = new ByteArrayInputStream(..);
    // ..; bais.close(); bais = null;` inside a plain try/catch — the
    // bogus `try (bais = null)` form fails with "resource may not have
    // been assigned" x13). And a real TWR resource decl is never
    // initialized to null.
    if stmt_assigns_var(body, r_var) {
        if dbg { eprintln!("TWR reject: resource reassigned in body"); }
        return None;
    }
    if matches!(&v[ri], Stmt::LocalDef { init: Some(Expr::Const(ConstVal::Null)), .. }) {
        if dbg { eprintln!("TWR reject: null resource init"); }
        return None;
    }
    // Body must not mention the primary var (user code never sees it).
    if let Some(pv) = primary_var {
        if stmt_uses_var(body, pv) {
            if dbg { eprintln!("TWR reject: body uses primary var"); }
            return None;
        }
    }
    // A TWR resource cannot escape the try statement: uses after the try
    // are only legitimate as trailing close scaffolding. Anything else
    // means a hand-written try/catch with a close in the handler.
    if v[i + 1..]
        .iter()
        .any(|st| !is_close_scaffold_stmt(st) && stmt_uses_var(st, r_var))
    {
        if dbg { eprintln!("TWR reject: resource var escapes try"); }
        return None;
    }
    // A kept (user) catch must not reference the resource either: in a
    // real try-with-resources the resource is out of scope in the catch.
    // A hand-rolled try whose handler closes the stream (MimeLauncher
    // `catch (IOException e1) { os.close(); .. }`) is not TWR.
    if keep_catches.iter().any(|c| stmt_uses_var(&c.body, r_var)) {
        if dbg { eprintln!("TWR reject: kept catch uses resource var"); }
        return None;
    }
    if dbg { eprintln!("TWR MATCH res_idx={} inits={:?} keep={}", ri, init_idxs, keep_catches.len()); }
    Some(J7Plan { res_idx: ri, init_idxs, keep_catches, try_idx: i })
}

fn apply_j7(v: &mut Vec<Stmt>, i: usize, plan: &J7Plan) {
    let resource = std::mem::replace(&mut v[plan.res_idx], Stmt::Block(vec![]));
    for &j in &plan.init_idxs {
        v[j] = Stmt::Block(vec![]);
    }
    let old = std::mem::replace(&mut v[i], Stmt::Block(vec![]));
    if let Stmt::Try { body, .. } = old {
        v[i] = Stmt::TryWithResources {
            resources: vec![resource],
            body,
            catches: plan.keep_catches.clone(),
            finally: None,
        };
    }
}

/// True when any nested statement ASSIGNS to `var` (target position).
fn stmt_assigns_var(s: &Stmt, var: u32) -> bool {
    fn eu(e: &Expr, var: u32) -> bool {
        match e {
            Expr::Assign { target, .. } => {
                matches!(&**target, Expr::Local { var: v, .. } if *v == var)
            }
            Expr::PreIncDec { e: i, .. } | Expr::PostIncDec { e: i, .. } => {
                matches!(&**i, Expr::Local { var: v, .. } if *v == var)
            }
            _ => false,
        }
    }
    fn ex(e: &Expr, var: u32) -> bool {
        if eu(e, var) {
            return true;
        }
        match e {
            Expr::Assign { value, .. } => ex(value, var),
            Expr::Method { owner, args, .. } => {
                owner.as_deref().map(|o| ex(o, var)).unwrap_or(false)
                    || args.iter().any(|a| ex(a, var))
            }
            Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
                args.iter().any(|a| ex(a, var))
            }
            Expr::Bin { l, r, .. } => ex(l, var) || ex(r, var),
            Expr::Cond { c, t, f } => ex(c, var) || ex(t, var) || ex(f, var),
            Expr::Cast { e: i, .. } | Expr::Un { e: i, .. }
            | Expr::PreIncDec { e: i, .. } | Expr::PostIncDec { e: i, .. } => ex(i, var),
            Expr::ArrayIndex { array, index } => ex(array, var) || ex(index, var),
            Expr::Field { owner: Some(o), .. } => ex(o, var),
            Expr::NewArray { dims, init, .. } => {
                dims.iter().any(|d| ex(d, var))
                    || init.as_ref().map(|vals| vals.iter().any(|x| ex(x, var))).unwrap_or(false)
            }
            _ => false,
        }
    }
    match s {
        Stmt::Block(v) => v.iter().any(|x| stmt_assigns_var(x, var)),
        Stmt::ExprStmt(e) => ex(e, var),
        Stmt::LocalDef { init: Some(e), .. } => ex(e, var),
        Stmt::Return(Some(e)) | Stmt::Throw(e) => ex(e, var),
        Stmt::If { cond, then_stmt, else_stmt } => {
            ex(cond, var)
                || stmt_assigns_var(then_stmt, var)
                || else_stmt.as_ref().map(|e| stmt_assigns_var(e, var)).unwrap_or(false)
        }
        Stmt::While { cond, body } | Stmt::DoWhile { body, cond } => {
            ex(cond, var) || stmt_assigns_var(body, var)
        }
        Stmt::For { init, cond, update, body } => {
            init.iter().any(|i| stmt_assigns_var(i, var))
                || cond.as_ref().map(|c| ex(c, var)).unwrap_or(false)
                || update.iter().any(|u| ex(u, var))
                || stmt_assigns_var(body, var)
        }
        Stmt::ForEach { iterable, body, .. } => ex(iterable, var) || stmt_assigns_var(body, var),
        Stmt::Switch { selector, cases, default, .. } => {
            ex(selector, var)
                || cases.iter().any(|c| c.body.iter().any(|st| stmt_assigns_var(st, var)))
                || default.as_ref().map(|d| stmt_assigns_var(d, var)).unwrap_or(false)
        }
        Stmt::Try { body, catches, finally } => {
            stmt_assigns_var(body, var)
                || catches.iter().any(|c| stmt_assigns_var(&c.body, var))
                || finally.as_ref().map(|f| stmt_assigns_var(f, var)).unwrap_or(false)
        }
        Stmt::TryWithResources { body, catches, finally, .. } => {
            stmt_assigns_var(body, var)
                || catches.iter().any(|c| stmt_assigns_var(&c.body, var))
                || finally.as_ref().map(|f| stmt_assigns_var(f, var)).unwrap_or(false)
        }
        Stmt::Synchronized { lock, body } => ex(lock, var) || stmt_assigns_var(body, var),
        Stmt::Labeled { body, .. } => stmt_assigns_var(body, var),
        _ => false,
    }
}

fn stmt_uses_var(s: &Stmt, var: u32) -> bool {
    fn eu(e: &Expr, var: u32) -> bool {
        match e {
            Expr::Local { var: v, .. } => *v == var,
            Expr::Method { owner, args, .. } => {
                owner.as_deref().map(|o| eu(o, var)).unwrap_or(false)
                    || args.iter().any(|a| eu(a, var))
            }
            Expr::New { args, .. } => args.iter().any(|a| eu(a, var)),
            Expr::Bin { l, r, .. } | Expr::Assign { target: l, value: r, .. } => {
                eu(l, var) || eu(r, var)
            }
            Expr::Cond { c, t, f } => eu(c, var) || eu(t, var) || eu(f, var),
            Expr::Un { e: x, .. }
            | Expr::Cast { e: x, .. }
            | Expr::InstanceOf { e: x, .. }
            | Expr::PreIncDec { e: x, .. }
            | Expr::PostIncDec { e: x, .. } => eu(x, var),
            Expr::ArrayIndex { array, index } => eu(array, var) || eu(index, var),
            Expr::Field { owner: Some(o), .. } => eu(o, var),
            _ => false,
        }
    }
    match s {
        Stmt::Block(v) => v.iter().any(|x| stmt_uses_var(x, var)),
        Stmt::ExprStmt(e) => eu(e, var),
        Stmt::LocalDef { var: v, init, .. } => *v == var || init.as_ref().map(|e| eu(e, var)).unwrap_or(false),
        Stmt::Return(Some(e)) | Stmt::Throw(e) => eu(e, var),
        Stmt::If { cond, then_stmt, else_stmt } => {
            eu(cond, var)
                || stmt_uses_var(then_stmt, var)
                || else_stmt.as_ref().map(|e| stmt_uses_var(e, var)).unwrap_or(false)
        }
        Stmt::While { cond, body } | Stmt::DoWhile { cond, body } => {
            eu(cond, var) || stmt_uses_var(body, var)
        }
        Stmt::For { init, cond, update, body } => {
            init.iter().any(|i| stmt_uses_var(i, var))
                || cond.as_ref().map(|c| eu(c, var)).unwrap_or(false)
                || update.iter().any(|u| eu(u, var))
                || stmt_uses_var(body, var)
        }
        Stmt::Try { body, catches, finally } => {
            stmt_uses_var(body, var)
                || catches.iter().any(|c| stmt_uses_var(&c.body, var))
                || finally.as_ref().map(|f| stmt_uses_var(f, var)).unwrap_or(false)
        }
        Stmt::TryWithResources { body, catches, finally, .. } => {
            stmt_uses_var(body, var)
                || catches.iter().any(|c| stmt_uses_var(&c.body, var))
                || finally.as_ref().map(|f| stmt_uses_var(f, var)).unwrap_or(false)
        }
        _ => false,
    }
}

/// True for the normal-path close scaffolding javac 7 emits after the TWR
/// try: null/primary-var guards around `in.close()` (+ suppressed handling).
fn is_close_scaffold_stmt(s: &Stmt) -> bool {
    scaffold_check(s, false)
}

fn scaffold_check(s: &Stmt, nested: bool) -> bool {
    match s {
        Stmt::Block(v) => v.iter().all(|x| scaffold_check(x, true)),
        Stmt::LocalDef { .. } => true,
        Stmt::ExprStmt(Expr::Method { name, .. }) if name == "close" => true,
        Stmt::ExprStmt(Expr::Assign { target, .. })
            if matches!(&**target, Expr::Local { .. }) => true,
        Stmt::If { cond, then_stmt, else_stmt } => {
            let cond_ok = matches!(
                cond,
                Expr::Bin { op: crate::expr::BinOp::Eq | crate::expr::BinOp::Ne | crate::expr::BinOp::RefEq | crate::expr::BinOp::RefNe, r, .. }
                    if matches!(&**r, Expr::Const(ConstVal::Null))
            ) || matches!(cond, Expr::Un { op: crate::expr::UnOp::Not, .. });
            if !cond_ok {
                return false;
            }
            // The null-guard shape is javac's close scaffolding signature;
            // copy-walked tails may embed arbitrary cleanup copies inside
            // the branches, so accept their content wholesale.
            let _ = (then_stmt, else_stmt);
            true
        }
        Stmt::Try { body, catches, finally } => {
            scaffold_check(body, true)
                && finally.as_deref().map(|f| scaffold_check(f, true)).unwrap_or(true)
                && catches.iter().all(|c| {
                    flatten_stmts(&c.body).iter().all(|h| match h {
                        Stmt::ExprStmt(Expr::Method { name, .. })
                            if name == "addSuppressed" || name == "close" => true,
                        Stmt::Throw(_) | Stmt::Return(_) => true,
                        Stmt::ExprStmt(Expr::Assign { .. }) => true,
                        Stmt::LocalDef { .. } => true,
                        Stmt::Goto(_) | Stmt::Break(_) | Stmt::Continue(_) => true,
                        _ => false,
                    })
                })
        }
        Stmt::TryWithResources { body, catches, finally, .. } => {
            scaffold_check(body, true)
                && finally.as_deref().map(|f| scaffold_check(f, true)).unwrap_or(true)
                && catches.iter().all(|c| {
                    flatten_stmts(&c.body).iter().all(|h| match h {
                        Stmt::ExprStmt(Expr::Method { name, .. })
                            if name == "addSuppressed" || name == "close" => true,
                        Stmt::Throw(_) | Stmt::Return(_) => true,
                        Stmt::ExprStmt(Expr::Assign { .. }) => true,
                        Stmt::LocalDef { .. } => true,
                        Stmt::Goto(_) | Stmt::Break(_) | Stmt::Continue(_) => true,
                        _ => false,
                    })
                })
        }
        Stmt::Throw(_) => true,
        Stmt::Goto(_) => true,
        Stmt::Break(_) => true,
        Stmt::Continue(_) => true,
        // A return INSIDE the scaffold's if/try nesting is part of the
        // copied tail; a bare top-level return is the method's own.
        Stmt::Return(_) => nested,
        _ => false,
    }
}


/// Inside a reconstructed `synchronized` block, monitorexit instructions
/// are implicit (Java unlocks on every exit path, including return/throw/
/// break). Drop leftover MonitorExit statements at any depth; also drop
/// MonitorEnter statements (they only appear when reconstruction consumed
/// the matching region).
fn strip_monitors_in_sync(s: &mut Stmt) {
    // Orphaned monitorenters (their region's exits vanished during
    // structuring) cannot be reconstructed; emitting them is invalid Java
    // and dropping them is harmless because the matching exits are gone.
    if !stmt_has_kind(s, false) {
        strip_kind(s, true);
    }
    if !stmt_has_kind(s, true) {
        strip_kind(s, false);
    }
    match s {
        Stmt::Synchronized { body, .. } => {
            strip_all_monitors(body);
        }
        Stmt::Try { body, catches, finally } => {
            // Empty synchronized block `synchronized (x) {}`: javac emits
            // monitorenter immediately followed by monitorexit with no
            // user code between. The pair is a JVM no-op (same monitor,
            // reentrant); drop both so the stray statements cannot poison
            // surrounding loop/try structuring.
            let dominated_by_exit = matches!(
                &**body,
                Stmt::Block(b) if !b.is_empty()
                    && b.iter().all(|x| matches!(x, Stmt::MonitorExit(_) | Stmt::Comment(_)))
            ) || matches!(&**body, Stmt::MonitorExit(_));
            let handler_is_exit_throw = catches.len() == 1
                && finally.is_none()
                && {
                    let c = &catches[0];
                    c.exc.is_empty()
                        && flatten_stmts_local(&c.body)
                            .iter()
                            .all(|h| matches!(h, Stmt::MonitorExit(_) | Stmt::Throw(_) | Stmt::LocalDef { .. }))
                };
            if dominated_by_exit && handler_is_exit_throw {
                *s = Stmt::Block(vec![]);
                return;
            }
            strip_monitors_in_sync(body);
            for c in catches {
                strip_monitors_in_sync(&mut c.body);
            }
            if let Some(f) = finally {
                strip_monitors_in_sync(f);
            }
        }
        Stmt::Block(v) => v.iter_mut().for_each(strip_monitors_in_sync),
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { strip_monitors_in_sync(res); }
            strip_monitors_in_sync(body);
            for c in catches {
                strip_monitors_in_sync(&mut c.body);
            }
            if let Some(f) = finally {
                strip_monitors_in_sync(f);
            }
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            strip_monitors_in_sync(then_stmt);
            if let Some(e) = else_stmt {
                strip_monitors_in_sync(e);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => strip_monitors_in_sync(body),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(strip_monitors_in_sync);
            strip_monitors_in_sync(body);
        }
        Stmt::ForEach { body, .. } => strip_monitors_in_sync(body),
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(strip_monitors_in_sync);
            }
            if let Some(d) = default {
                strip_monitors_in_sync(d);
            }
        }
        Stmt::Labeled { body, .. } => strip_monitors_in_sync(body),
        _ => {}
    }
}

fn strip_all_monitors(s: &mut Stmt) {
    match s {
        Stmt::Block(v) => {
            v.iter_mut().for_each(strip_all_monitors);
            v.retain(|x| !matches!(x, Stmt::MonitorEnter(_) | Stmt::MonitorExit(_)));
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            strip_all_monitors(then_stmt);
            if let Some(e) = else_stmt {
                strip_all_monitors(e);
            }
        }
        Stmt::Try { body, catches, finally } => {
            strip_all_monitors(body);
            for c in catches {
                strip_all_monitors(&mut c.body);
            }
            if let Some(f) = finally {
                strip_all_monitors(f);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { strip_all_monitors(res); }
            strip_all_monitors(body);
            for c in catches {
                strip_all_monitors(&mut c.body);
            }
            if let Some(f) = finally {
                strip_all_monitors(f);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => strip_all_monitors(body),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(strip_all_monitors);
            strip_all_monitors(body);
        }
        Stmt::ForEach { body, .. } => strip_all_monitors(body),
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(strip_all_monitors);
            }
            if let Some(d) = default {
                strip_all_monitors(d);
            }
        }
        Stmt::Labeled { body, .. } | Stmt::Synchronized { body, .. } => strip_all_monitors(body),
        other => {
            if matches!(other, Stmt::MonitorEnter(_) | Stmt::MonitorExit(_)) {
                *other = Stmt::Block(vec![]);
            }
        }
    }
}


// ---------------------------------------------------------------------------
// assert restoration
// ---------------------------------------------------------------------------

/// `Some(true)` when `e` denotes "$assertionsDisabled is true",
/// `Some(false)` for its negation, `None` when unrelated. Handles the
/// boolean-field forms `$AD`, `!$AD`, `$AD != 0` and `$AD == 0`.
fn ad_polarity(e: &Expr) -> Option<bool> {
    use crate::expr::BinOp;
    match e {
        Expr::Field { name, .. } if name == "$assertionsDisabled" => Some(true),
        Expr::Un { op: crate::expr::UnOp::Not, e } => ad_polarity(e).map(|p| !p),
        Expr::Bin { op: BinOp::Ne, l, r, .. }
            if matches!(&**r, Expr::Const(crate::expr::ConstVal::Int(0))) =>
        {
            ad_polarity(l)
        }
        Expr::Bin { op: BinOp::Eq, l, r, .. }
            if matches!(&**r, Expr::Const(crate::expr::ConstVal::Int(0))) =>
        {
            ad_polarity(l).map(|p| !p)
        }
        _ => None,
    }
}

fn as_assert_throw(s: &Stmt) -> Option<Option<Expr>> {
    let stmts = match s {
        Stmt::Block(v) => v,
        other => {
            if matches!(other, Stmt::Throw(_)) {
                std::slice::from_ref(other)
            } else {
                return None;
            }
        }
    };
    let mut msg = None;
    let mut seen = false;
    for st in stmts {
        match st {
            Stmt::Throw(e) => {
                if let Expr::New { cls, args, .. } = e {
                    if cls == "java/lang/AssertionError" {
                        msg = args.first().cloned();
                        seen = true;
                        continue;
                    }
                }
                return None;
            }
            _ => return None,
        }
    }
    if seen {
        Some(msg)
    } else {
        None
    }
}

/// `if ($assertionsDisabled) {} else if (!c) {} else { throw new AssertionError(m); }`
/// (and mirror forms) become `assert c : m;`.
fn restore_asserts(s: &mut Stmt) {
    if let Stmt::Block(v) = s {
        let mut i = 0;
        while i < v.len() {
            restore_asserts(&mut v[i]);
            if std::env::var("JCDC_DBG_ASSERT").is_ok() {
                if let Stmt::If { cond, .. } = &v[i] {
                    let d = format!("{:?}", cond);
                    if d.contains("assert") || d.contains("Assertion") || d.contains("Field") {
                        eprintln!("ASSERT scan if cond ~ {}", &d[..d.len().min(160)]);
                    }
                }
            }
            if let Some(a) = match_assert(&v[i]) {
                v[i] = a;
            }
            i += 1;
        }
        return;
    }
    match s {
        Stmt::If { then_stmt, else_stmt, .. } => {
            restore_asserts(then_stmt);
            if let Some(e) = else_stmt {
                restore_asserts(e);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => restore_asserts(body),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(restore_asserts);
            restore_asserts(body);
        }
        Stmt::ForEach { body, .. } => restore_asserts(body),
        Stmt::Try { body, catches, finally } => {
            restore_asserts(body);
            for c in catches {
                restore_asserts(&mut c.body);
            }
            if let Some(f) = finally {
                restore_asserts(f);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { restore_asserts(res); }
            restore_asserts(body);
            for c in catches {
                restore_asserts(&mut c.body);
            }
            if let Some(f) = finally {
                restore_asserts(f);
            }
        }
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(restore_asserts);
            }
            if let Some(d) = default {
                restore_asserts(d);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => restore_asserts(body),
        _ => {}
    }
}

fn match_assert(s: &Stmt) -> Option<Stmt> {
    let (cond, then_stmt, else_stmt) = match s {
        Stmt::If { cond, then_stmt, else_stmt } => (cond, then_stmt, else_stmt),
        _ => return None,
    };
    let Some(positive) = ad_polarity(cond) else { return None };
    // The guarded side runs when assertions are ENABLED.
    let guarded: &Stmt = if positive {
        // if (AD) {must be empty} else <guarded>
        if !then_stmt.is_empty_block() {
            return None;
        }
        match else_stmt {
            Some(g) => g,
            None => return None,
        }
    } else {
        // if (!AD) <guarded>
        if else_stmt.as_ref().map(|e| !e.is_empty_block()).unwrap_or(false) {
            return None;
        }
        then_stmt
    };
    // guarded forms:
    //   a) throw new AssertionError(m)          → assert false : m
    //   b) if (g) {} else { throw AE(m) }       → assert g : m
    //   c) if (g) { throw AE(m) }               → assert !g : m
    if let Some(msg) = as_assert_throw(guarded) {
        return Some(Stmt::Assert {
            cond: Expr::Const(crate::expr::ConstVal::Int(0)),
            msg,
        });
    }
    if let Stmt::If { cond: g, then_stmt: gt, else_stmt: ge } = guarded {
        if gt.is_empty_block() {
            if let Some(msg) = ge.as_ref().and_then(|e| as_assert_throw(e)) {
                return Some(Stmt::Assert { cond: (*g).clone(), msg });
            }
        }
        if ge.as_ref().map(|e| e.is_empty_block()).unwrap_or(true) {
            if let Some(msg) = as_assert_throw(gt) {
                return Some(Stmt::Assert {
                    cond: crate::convert::negate((*g).clone()),
                    msg,
                });
            }
        }
    }
    // Block-wrapped guarded body with a single If/Throw.
    if let Stmt::Block(v) = guarded {
        if v.len() == 1 {
            return match_assert_inner(&v[0]);
        }
    }
    None
}

fn match_assert_inner(s: &Stmt) -> Option<Stmt> {
    if let Some(msg) = as_assert_throw(s) {
        return Some(Stmt::Assert {
            cond: Expr::Const(crate::expr::ConstVal::Int(0)),
            msg,
        });
    }
    if let Stmt::If { cond: g, then_stmt: gt, else_stmt: ge } = s {
        if gt.is_empty_block() {
            if let Some(msg) = ge.as_ref().and_then(|e| as_assert_throw(e)) {
                return Some(Stmt::Assert { cond: (*g).clone(), msg });
            }
        }
        if ge.as_ref().map(|e| e.is_empty_block()).unwrap_or(true) {
            if let Some(msg) = as_assert_throw(gt) {
                return Some(Stmt::Assert {
                    cond: crate::convert::negate((*g).clone()),
                    msg,
                });
            }
        }
    }
    None
}


/// Remove and return a MonitorEnter that sits at the trailing leaf of `s`
/// (last statement of nested blocks, or the then-branch of a trailing If
/// with no else).
fn take_trailing_monitor(s: &mut Stmt) -> Option<Expr> {
    match s {
        Stmt::MonitorEnter(e) => Some(std::mem::replace(e, Expr::This)),
        Stmt::Block(v) => {
            // A loop-exit `break` may sit between the monitorenter and the
            // protected region that follows the loop; step over it.
            let mut k = v.len();
            while k > 0 {
                k -= 1;
                match &v[k] {
                    x if x.is_empty_block() => {
                        v.remove(k);
                        continue;
                    }
                    Stmt::Break(None) | Stmt::Continue(None) => continue,
                    Stmt::MonitorEnter(_) => break,
                    _ => break,
                }
            }
            if k >= v.len() {
                return None;
            }
            if matches!(&v[k], Stmt::MonitorEnter(_)) {
                let mut enter = v.remove(k);
                match &mut enter {
                    Stmt::MonitorEnter(e) => Some(std::mem::replace(e, Expr::This)),
                    _ => None,
                }
            } else {
                take_trailing_monitor(&mut v[k])
            }
        }
        Stmt::If { then_stmt, else_stmt: None, .. } => take_trailing_monitor(then_stmt),
        // javac can leave the monitorenter of a sync region that FOLLOWS a
        // loop at the tail of that loop's body (the empty-synchronized
        // busy-wait shape in Sun's SeedGenerator). Pairing it with the
        // following Try restores the intended region.
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => take_trailing_monitor(body),
        Stmt::Labeled { body, .. } | Stmt::Synchronized { body, .. } => {
            take_trailing_monitor(body)
        }
        _ => None,
    }
}

/// Inverse of take_trailing_monitor for the non-sync case: append the
/// statement back at the trailing position.
fn restore_trailing_monitor(s: &mut Stmt, enter: Stmt) {
    match s {
        Stmt::Block(v) => v.push(enter),
        other => {
            let old = std::mem::replace(other, Stmt::Block(vec![]));
            *other = Stmt::Block(vec![old, enter]);
        }
    }
}


fn flatten_stmts_local(s: &Stmt) -> Vec<Stmt> {
    let mut out = Vec::new();
    fn rec(s: &Stmt, out: &mut Vec<Stmt>) {
        match s {
            Stmt::Block(v) => v.iter().for_each(|x| rec(x, out)),
            other => out.push(other.clone()),
        }
    }
    rec(s, &mut out);
    out
}


/// Scan for MonitorEnter (want=true) or MonitorExit (want=false) statements.
fn stmt_has_kind(s: &Stmt, want: bool) -> bool {
    let mut found = false;
    fn rec(s: &Stmt, want: bool, found: &mut bool) {
        if *found {
            return;
        }
        match s {
            Stmt::MonitorEnter(_) if want => *found = true,
            Stmt::MonitorExit(_) if !want => *found = true,
            Stmt::Block(v) => v.iter().for_each(|x| rec(x, want, found)),
            Stmt::If { then_stmt, else_stmt, .. } => {
                rec(then_stmt, want, found);
                if let Some(e) = else_stmt {
                    rec(e, want, found);
                }
            }
            Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => rec(body, want, found),
            Stmt::For { init, body, .. } => {
                init.iter().for_each(|i| rec(i, want, found));
                rec(body, want, found);
            }
            Stmt::ForEach { body, .. } => rec(body, want, found),
            Stmt::Try { body, catches, finally } => {
                rec(body, want, found);
                for c in catches {
                    rec(&c.body, want, found);
                }
                if let Some(f) = finally {
                    rec(f, want, found);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                for res in resources {
                    rec(res, want, found);
                }
                rec(body, want, found);
                for c in catches {
                    rec(&c.body, want, found);
                }
                if let Some(f) = finally {
                    rec(f, want, found);
                }
            }
            Stmt::Switch { cases, default, .. } => {
                for c in cases {
                    c.body.iter().for_each(|st| rec(st, want, found));
                }
                if let Some(d) = default {
                    rec(d, want, found);
                }
            }
            Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => rec(body, want, found),
            _ => {}
        }
    }
    rec(s, want, &mut found);
    found
}

/// Remove all MonitorEnter (enters=true) or MonitorExit (enters=false)
/// statements at any depth.
fn strip_kind(s: &mut Stmt, enters: bool) {
    match s {
        Stmt::Block(v) => {
            v.iter_mut().for_each(|x| strip_kind(x, enters));
            v.retain(|x| {
                if enters {
                    !matches!(x, Stmt::MonitorEnter(_))
                } else {
                    !matches!(x, Stmt::MonitorExit(_))
                }
            });
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            strip_kind(then_stmt, enters);
            if let Some(e) = else_stmt {
                strip_kind(e, enters);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => strip_kind(body, enters),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(|i| strip_kind(i, enters));
            strip_kind(body, enters);
        }
        Stmt::ForEach { body, .. } => strip_kind(body, enters),
        Stmt::Try { body, catches, finally } => {
            strip_kind(body, enters);
            for c in catches {
                strip_kind(&mut c.body, enters);
            }
            if let Some(f) = finally {
                strip_kind(f, enters);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { strip_kind(res, enters); }
            strip_kind(body, enters);
            for c in catches {
                strip_kind(&mut c.body, enters);
            }
            if let Some(f) = finally {
                strip_kind(f, enters);
            }
        }
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(|st| strip_kind(st, enters));
            }
            if let Some(d) = default {
                strip_kind(d, enters);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => strip_kind(body, enters),
        other => {
            let hit = if enters {
                matches!(other, Stmt::MonitorEnter(_))
            } else {
                matches!(other, Stmt::MonitorExit(_))
            };
            if hit {
                *other = Stmt::Block(vec![]);
            }
        }
    }
}


/// Default initializer for synthetic (compiler-temporary) variables so the
/// decompiled method passes javac's definite-assignment checks. Real LVT
/// variables keep bare declarations (their source form).
/// True when `v` flows into an anonymous-class ctor argument (a val$
/// capture) or a lambda capture list: such locals must remain effectively
/// final in source form.
/// True when some statement assigns `null` to `v`: the hoisted `= null`
/// default then duplicates a real store — the var is NOT a blank-final
/// split-lineage shape and must keep its initializer (dropping it broke
/// definite assignment: jdk11/17 ObjectInputFilter patternFilter3).
/// True when `v` receives a null assignment on the STRAIGHT-LINE prefix of
/// the body (before any control-flow statement): a genuine `v = null;`
/// initializer the source carried at the declaration. Null stores INSIDE
/// branches do not count — they are per-path definite assignments.
fn straight_null_init(s: &Stmt, v: u32) -> bool {
    let Stmt::Block(items) = s else { return false };
    for st in items {
        match st {
            Stmt::ExprStmt(Expr::Assign { target, value, .. })
                if matches!(&**target, Expr::Local { var, .. } if *var == v) =>
            {
                return matches!(&**value, Expr::Const(ConstVal::Null));
            }
            Stmt::LocalDef { var, init, .. } if *var == v => {
                return matches!(init, Some(Expr::Const(ConstVal::Null)));
            }
            Stmt::ExprStmt(_) | Stmt::LocalDef { .. } | Stmt::Comment(_) => {}
            _ => return false,
        }
    }
    false
}

fn assigns_null_to(s: &Stmt, v: u32) -> bool {
    match s {
        Stmt::Block(x) => x.iter().any(|i| assigns_null_to(i, v)),
        Stmt::ExprStmt(Expr::Assign { target, value, .. }) => {
            matches!(&**target, Expr::Local { var, .. } if *var == v)
                && matches!(&**value, Expr::Const(ConstVal::Null))
        }
        Stmt::LocalDef { var, init: Some(e), .. } => {
            *var == v && matches!(e, Expr::Const(ConstVal::Null))
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            assigns_null_to(then_stmt, v)
                || else_stmt.as_deref().map(|x| assigns_null_to(x, v)).unwrap_or(false)
        }
        Stmt::While { body, .. }
        | Stmt::DoWhile { body, .. }
        | Stmt::ForEach { body, .. }
        | Stmt::Labeled { body, .. }
        | Stmt::Synchronized { body, .. } => assigns_null_to(body, v),
        Stmt::For { init, body, .. } => {
            init.iter().any(|i| assigns_null_to(i, v)) || assigns_null_to(body, v)
        }
        Stmt::Switch { cases, default, .. } => {
            cases.iter().any(|c| c.body.iter().any(|b| assigns_null_to(b, v)))
                || default.as_deref().map(|d| assigns_null_to(d, v)).unwrap_or(false)
        }
        Stmt::Try { body, catches, finally } => {
            assigns_null_to(body, v)
                || catches.iter().any(|c| assigns_null_to(&c.body, v))
                || finally.as_deref().map(|f| assigns_null_to(f, v)).unwrap_or(false)
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            resources.iter().any(|r| assigns_null_to(r, v))
                || assigns_null_to(body, v)
                || catches.iter().any(|c| assigns_null_to(&c.body, v))
                || finally.as_deref().map(|f| assigns_null_to(f, v)).unwrap_or(false)
        }
        _ => false,
    }
}

fn captured_by_anon(s: &Stmt, v: u32) -> bool {
    fn refs(e: &Expr, v: u32) -> bool {
        match e {
            Expr::Local { var, .. } => *var == v,
            Expr::Method { owner, args, .. } => {
                owner.as_deref().map(|o| refs(o, v)).unwrap_or(false)
                    || args.iter().any(|a| refs(a, v))
            }
            Expr::Field { owner: Some(o), .. } => refs(o, v),
            Expr::Bin { l, r, .. } | Expr::Assign { target: l, value: r, .. } => {
                refs(l, v) || refs(r, v)
            }
            Expr::Cond { c, t, f } => refs(c, v) || refs(t, v) || refs(f, v),
            Expr::Un { e: x, .. }
            | Expr::Cast { e: x, .. }
            | Expr::InstanceOf { e: x, .. }
            | Expr::PreIncDec { e: x, .. }
            | Expr::PostIncDec { e: x, .. } => refs(x, v),
            Expr::ArrayIndex { array, index } => refs(array, v) || refs(index, v),
            Expr::New { args, .. } | Expr::AnonNew { args, .. } => {
                args.iter().any(|a| refs(a, v))
            }
            Expr::NewArray { dims, init, .. } => {
                dims.iter().any(|d| refs(d, v))
                    || init
                        .as_ref()
                        .map(|vals| vals.iter().any(|x| refs(x, v)))
                        .unwrap_or(false)
            }
            Expr::StringConcat(parts) => parts.iter().any(|pp| match pp {
                crate::expr::ConcatPart::Str(x) => refs(x, v),
                _ => false,
            }),
            Expr::Lambda(l) => l.captures.iter().any(|a| refs(a, v)),
            _ => false,
        }
    }
    fn is_anon_cls(cls: &str) -> bool {
        if cls.starts_with('\u{2}') {
            return true;
        }
        cls.rsplit('$')
            .next()
            .map(|t| !t.is_empty() && t.chars().all(|c| c.is_ascii_digit()))
            .unwrap_or(false)
    }
    fn ex(e: &Expr, v: u32) -> bool {
        match e {
            Expr::New { cls, args, .. } if is_anon_cls(cls) => {
                args.iter().any(|a| refs(a, v))
            }
            Expr::AnonNew { args, .. } => args.iter().any(|a| refs(a, v)),
            // Lambda captures deliberately DO NOT count: the lambda
            // capture-snapshot pass copies reassigned locals into
            // effectively-final `name$capN` snapshots, so the hoisted
            // `= null` default is safe there (jdk11/17 ObjectInputFilter
            // patternFilter3 needs it for definite assignment). Only
            // anonymous-class ctor args (val$ captures, no snapshot
            // machinery) require the blank-declaration shape.
            Expr::Method { owner, args, .. } => {
                owner.as_deref().map(|o| ex(o, v)).unwrap_or(false)
                    || args.iter().any(|a| ex(a, v))
            }
            Expr::Field { owner: Some(o), .. } => ex(o, v),
            Expr::Bin { l, r, .. } | Expr::Assign { target: l, value: r, .. } => {
                ex(l, v) || ex(r, v)
            }
            Expr::Cond { c, t, f } => ex(c, v) || ex(t, v) || ex(f, v),
            Expr::Un { e: x, .. }
            | Expr::Cast { e: x, .. }
            | Expr::InstanceOf { e: x, .. }
            | Expr::PreIncDec { e: x, .. }
            | Expr::PostIncDec { e: x, .. } => ex(x, v),
            Expr::ArrayIndex { array, index } => ex(array, v) || ex(index, v),
            Expr::New { args, .. } => args.iter().any(|a| ex(a, v)),
            Expr::NewArray { dims, init, .. } => {
                dims.iter().any(|d| ex(d, v))
                    || init
                        .as_ref()
                        .map(|vals| vals.iter().any(|x| ex(x, v)))
                        .unwrap_or(false)
            }
            Expr::StringConcat(parts) => parts.iter().any(|pp| match pp {
                crate::expr::ConcatPart::Str(x) => ex(x, v),
                _ => false,
            }),
            _ => false,
        }
    }
    fn st(s: &Stmt, v: u32) -> bool {
        match s {
            Stmt::Block(x) => x.iter().any(|i| st(i, v)),
            Stmt::ExprStmt(e) => ex(e, v),
            Stmt::LocalDef { init: Some(e), .. } => ex(e, v),
            Stmt::Return(Some(e)) | Stmt::Throw(e) => ex(e, v),
            Stmt::If { cond, then_stmt, else_stmt } => {
                ex(cond, v)
                    || st(then_stmt, v)
                    || else_stmt.as_deref().map(|e2| st(e2, v)).unwrap_or(false)
            }
            Stmt::While { cond, body } | Stmt::DoWhile { body, cond } => ex(cond, v) || st(body, v),
            Stmt::For { init, cond, update, body } => {
                init.iter().any(|i| st(i, v))
                    || cond.as_ref().map(|c| ex(c, v)).unwrap_or(false)
                    || update.iter().any(|u| ex(u, v))
                    || st(body, v)
            }
            Stmt::ForEach { iterable, body, .. } => ex(iterable, v) || st(body, v),
            Stmt::Switch { selector, cases, default, .. } => {
                ex(selector, v)
                    || cases.iter().any(|c| c.body.iter().any(|b| st(b, v)))
                    || default.as_deref().map(|d| st(d, v)).unwrap_or(false)
            }
            Stmt::Try { body, catches, finally } => {
                st(body, v)
                    || catches.iter().any(|c| st(&c.body, v))
                    || finally.as_deref().map(|f| st(f, v)).unwrap_or(false)
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                resources.iter().any(|r| st(r, v))
                    || st(body, v)
                    || catches.iter().any(|c| st(&c.body, v))
                    || finally.as_deref().map(|f| st(f, v)).unwrap_or(false)
            }
            Stmt::Synchronized { lock, body } => ex(lock, v) || st(body, v),
            Stmt::Labeled { body, .. } => st(body, v),
            _ => false,
        }
    }
    st(s, v)
}

fn default_init_for(vt: &VarTable, v: u32) -> Option<Expr> {
    default_init_for_vt(vt, v)
}

#[allow(dead_code)]
fn default_init_for_v(vt: &VarTable, v: u32) -> Option<Expr> {
    default_init_for_vt(vt, v)
}

fn default_init_for_vt(vt: &VarTable, v: u32) -> Option<Expr> {
    let info = vt.var(v);
    if info.is_param {
        return None;
    }
    // Bare hoisted declarations always get a default: javac's
    // definite-assignment analysis rejects `int i;` uses that the bytecode
    // guarantees are initialized on all reaching paths but the decompiled
    // control flow cannot prove.
    Some(match info.ty.erased() {
        jcdc_jvm::JavaType::Int
        | jcdc_jvm::JavaType::Short
        | jcdc_jvm::JavaType::Byte
        | jcdc_jvm::JavaType::Char
        | jcdc_jvm::JavaType::Boolean => Expr::Const(crate::expr::ConstVal::Int(0)),
        jcdc_jvm::JavaType::Long => Expr::Const(crate::expr::ConstVal::Long(0)),
        jcdc_jvm::JavaType::Float => Expr::Const(crate::expr::ConstVal::Float(0.0)),
        jcdc_jvm::JavaType::Double => Expr::Const(crate::expr::ConstVal::Double(0.0)),
        _ => Expr::Const(crate::expr::ConstVal::Null),
    })
}


/// Rotate `if (c) {} else { E } <terminator>` into
/// `if (c) { <terminator> } else { E }`. Guard-chain decompilation leaves
/// empty then-branches followed by a throw/return that the else-side flow
/// jumps over; rotation restores the source-level if/else semantics.
fn rotate_empty_then(s: &mut Stmt) {
    if let Stmt::Block(v) = s {
        let mut i = 0;
        while i + 1 < v.len() {
            let ok = match &v[i] {
                Stmt::If { then_stmt, else_stmt: Some(_), .. } => then_stmt.is_empty_block(),
                _ => false,
            };
            let term = matches!(&v[i + 1], Stmt::Throw(_) | Stmt::Return(_));
            if ok && term {
                // CLONE the terminator into the empty then-branch and keep
                // the original in place: guard chains share one throw/return
                // block, and every empty then needs its own copy. The
                // retained original is unreachable from the rotated then
                // (the clone terminates) and still serves later siblings;
                // prune_unreachable drops it when it follows a terminator.
                let t = v[i + 1].clone();
                if let Stmt::If { then_stmt, .. } = &mut v[i] {
                    *then_stmt = Box::new(t);
                }
                i += 1;
                continue;
            }
            rotate_empty_then(&mut v[i]);
            i += 1;
        }
        if let Some(last) = v.last_mut() {
            rotate_empty_then(last);
        }
        return;
    }
    match s {
        Stmt::If { then_stmt, else_stmt, .. } => {
            rotate_empty_then(then_stmt);
            if let Some(e) = else_stmt {
                rotate_empty_then(e);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => rotate_empty_then(body),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(rotate_empty_then);
            rotate_empty_then(body);
        }
        Stmt::ForEach { body, .. } => rotate_empty_then(body),
        Stmt::Try { body, catches, finally } => {
            rotate_empty_then(body);
            for c in catches {
                rotate_empty_then(&mut c.body);
            }
            if let Some(f) = finally {
                rotate_empty_then(f);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { rotate_empty_then(res); }
            rotate_empty_then(body);
            for c in catches {
                rotate_empty_then(&mut c.body);
            }
            if let Some(f) = finally {
                rotate_empty_then(f);
            }
        }
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(rotate_empty_then);
            }
            if let Some(d) = default {
                rotate_empty_then(d);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => rotate_empty_then(body),
        _ => {}
    }
}


/// Remove `throw <in-flight exception>` statements inside finally blocks.
/// javac duplicates the cleanup for the exceptional path and ends it with
/// an `athrow` of the exception in flight; in Java source, a finally that
/// does not throw propagates it implicitly, so the explicit rethrow must
/// not appear (it would also widen the method's throws clause).
fn prune_finally_rethrows(s: &mut Stmt) {
    match s {
        Stmt::Block(v) => v.iter_mut().for_each(prune_finally_rethrows),
        Stmt::Try { body, catches, finally } => {
            let inflight = catch_vars_of(catches);
            prune_finally_rethrows(body);
            for c in catches.iter_mut() {
                prune_finally_rethrows(&mut c.body);
            }
            if let Some(f) = finally {
                // A `throw v` where v is THIS try's own in-flight slot (a
                // catch-all/pending handler var) is the bytecode's
                // explicit pending-rethrow: the Java finally propagates it
                // implicitly, so the copy must go (leaving it fights the
                // dual-terminator retry-tail shape). A throw of any OTHER
                // Throwable local is a real source throw (the ThreadDeath
                // override `throw t`) and stays.
                strip_inflight_throws(f, &inflight);
                prune_finally_rethrows(f);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { prune_finally_rethrows(res); }
            let inflight = catch_vars_of(catches);
            prune_finally_rethrows(body);
            for c in catches.iter_mut() {
                prune_finally_rethrows(&mut c.body);
            }
            if let Some(f) = finally {
                strip_inflight_throws(f, &inflight);
                prune_finally_rethrows(f);
            }
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            prune_finally_rethrows(then_stmt);
            if let Some(e) = else_stmt {
                prune_finally_rethrows(e);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => prune_finally_rethrows(body),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(prune_finally_rethrows);
            prune_finally_rethrows(body);
        }
        Stmt::ForEach { body, .. } => prune_finally_rethrows(body),
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(prune_finally_rethrows);
            }
            if let Some(d) = default {
                prune_finally_rethrows(d);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => {
            prune_finally_rethrows(body)
        }
        _ => {}
    }
}

fn catch_vars_of(catches: &[crate::stmt::Catch]) -> std::collections::HashSet<u32> {
    catches
        .iter()
        .filter(|c| c.exc.is_empty())
        .map(|c| c.var)
        .collect()
}

fn strip_inflight_throws(s: &mut Stmt, inflight: &std::collections::HashSet<u32>) {
    match s {
        Stmt::Block(v) => {
            v.iter_mut().for_each(|x| strip_inflight_throws(x, inflight));
            v.retain(|x| !is_inflight_throw(x, inflight));
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            // An in-flight rethrow AS a whole branch becomes an empty
            // block (rotate/cleanup collapse it afterwards).
            if is_inflight_throw(then_stmt, inflight) {
                *then_stmt = Box::new(Stmt::Block(vec![]));
            } else {
                strip_inflight_throws(then_stmt, inflight);
            }
            if let Some(e) = else_stmt {
                if is_inflight_throw(e, inflight) {
                    *e = Box::new(Stmt::Block(vec![]));
                } else {
                    strip_inflight_throws(e, inflight);
                }
            }
        }
        // The finally duplication nests: javac's ThreadDeath-retry
        // scaffolding wraps the cleanup in try/catch/loop copies, and the
        // in-flight `throw t` rethrows sit INSIDE those (jdk26
        // ForkJoinWorkerThread.run: `catch (Throwable e5) { .. throw e4; }
        // finally { deregisterWorker }` — 未报告的异常错误Throwable x2).
        Stmt::Try { body, catches, finally, .. }
        | Stmt::TryWithResources { body, catches, finally, .. } => {
            strip_inflight_throws(body, inflight);
            for c in catches.iter_mut() {
                strip_inflight_throws(&mut c.body, inflight);
            }
            if let Some(f) = finally {
                strip_inflight_throws(f, inflight);
            }
        }
        Stmt::While { body, .. }
        | Stmt::DoWhile { body, .. }
        | Stmt::ForEach { body, .. }
        | Stmt::Labeled { body, .. }
        | Stmt::Synchronized { body, .. } => strip_inflight_throws(body, inflight),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(|x| strip_inflight_throws(x, inflight));
            strip_inflight_throws(body, inflight);
        }
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(|x| strip_inflight_throws(x, inflight));
            }
            if let Some(d) = default {
                strip_inflight_throws(d, inflight);
            }
        }
        _ => {}
    }
}

/// A `throw t` where `t` is a plain Throwable-typed local inside a finally
/// is the bytecode's in-flight exception rethrow (an artifact of javac's
/// finally duplication), never source-level code.
fn is_inflight_throw(s: &Stmt, _inflight: &std::collections::HashSet<u32>) -> bool {
    match s {
        Stmt::Throw(Expr::Local { ty, .. }) => {
            matches!(ty, crate::expr::TypeRef::J(JavaType::Object(n)) if n == "java/lang/Throwable")
        }
        _ => false,
    }
}




/// Java forbids a local declaration from shadowing another local of the
/// SAME method in an enclosing scope. When two distinct variables (slots)
/// share an LVT name and end up nested, rename the inner one.
/// Breaks/continues whose labels are DEFINED nowhere in the method are
/// structurizer residue: a `break L31` targeting a following switch case
/// is the bytecode's fall-through edge (jdk11 Pattern slice case 0 →
/// default; "未定义的标签"), and a continue targeting a lost loop header
/// still means "the enclosing loop". Demote: drop the break where it
/// sits as the case's tail (fall-through), collapse `if (c) { X } else
/// { break L; }` to `if (!c) { X }` at case tail, and strip labels from
/// continues (nearest enclosing loop is the only candidate left).
pub(crate) fn demote_undefined_label_jumps(s: &mut Stmt) {
    fn defined_labels(s: &Stmt, out: &mut HashSet<String>, ids: &mut HashSet<u32>) {
        match s {
            Stmt::Label(id) => {
                ids.insert(*id);
            }
            Stmt::Goto(_) | Stmt::Break(_) | Stmt::Continue(_) => {}
            Stmt::Labeled { label, body } => {
                out.insert(label.clone());
                defined_labels(body, out, ids);
            }
            Stmt::Block(v) => v.iter().for_each(|x| defined_labels(x, out, ids)),
            Stmt::If { then_stmt, else_stmt, .. } => {
                defined_labels(then_stmt, out, ids);
                if let Some(e) = else_stmt {
                    defined_labels(e, out, ids);
                }
            }
            Stmt::While { body, .. }
            | Stmt::DoWhile { body, .. }
            | Stmt::ForEach { body, .. }
            | Stmt::Synchronized { body, .. } => defined_labels(body, out, ids),
            Stmt::For { init, body, .. } => {
                init.iter().for_each(|x| defined_labels(x, out, ids));
                defined_labels(body, out, ids);
            }
            Stmt::Switch { cases, default, .. } => {
                for c in cases {
                    c.body.iter().for_each(|x| defined_labels(x, out, ids));
                }
                if let Some(d) = default {
                    defined_labels(d, out, ids);
                }
            }
            Stmt::Try { body, catches, finally } => {
                defined_labels(body, out, ids);
                for c in catches {
                    defined_labels(&c.body, out, ids);
                }
                if let Some(f) = finally {
                    defined_labels(f, out, ids);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                resources.iter().for_each(|x| defined_labels(x, out, ids));
                defined_labels(body, out, ids);
                for c in catches {
                    defined_labels(&c.body, out, ids);
                }
                if let Some(f) = finally {
                    defined_labels(f, out, ids);
                }
            }
            _ => {}
        }
    }
    let mut defined: HashSet<String> = HashSet::new();
    let mut defined_ids: HashSet<u32> = HashSet::new();
    defined_labels(s, &mut defined, &mut defined_ids);
    fn undefined_jump(s: &Stmt, defined: &HashSet<String>, ids: &HashSet<u32>) -> bool {
        match s {
            Stmt::Break(Some(l)) | Stmt::Continue(Some(l)) => !defined.contains(l),
            Stmt::Goto(id) => !ids.contains(id),
            _ => false,
        }
    }
    /// The single statement wrapped in (possibly nested) single-element blocks.
    fn unwrap_single(v: &Stmt) -> &Stmt {
        let mut cur = v;
        loop {
            match cur {
                Stmt::Block(inner) if inner.len() == 1 => cur = &inner[0],
                other => return other,
            }
        }
    }
    fn try_fold_tail_if(st: &mut Stmt, defined: &HashSet<String>, ids: &HashSet<u32>) -> bool {
        if let Stmt::Block(v) = st {
            if v.len() == 1 {
                return try_fold_tail_if(&mut v[0], defined, ids);
            }
            return false;
        }
        let Stmt::If { cond, then_stmt, else_stmt: Some(e) } = st else {
            return false;
        };
        let then_undef = undefined_jump(unwrap_single(then_stmt), defined, ids);
        let else_undef = undefined_jump(unwrap_single(e), defined, ids);
        if then_undef == else_undef {
            // neither, or both (ambiguous — leave for the switch restorer)
            return false;
        }
        let c = cond.clone();
        *st = if then_undef {
            Stmt::If {
                cond: crate::convert::negate(c),
                then_stmt: e.clone(),
                else_stmt: None,
            }
        } else {
            Stmt::If {
                cond: c,
                then_stmt: then_stmt.clone(),
                else_stmt: None,
            }
        };
        true
    }
    fn fix_vec(v: &mut Vec<Stmt>, defined: &HashSet<String>, ids: &HashSet<u32>, in_loop: bool) {
        let mut i = 0;
        while i < v.len() {
            // Trailing undefined jump — or, outside any loop/switch, a
            // trailing bare break/continue (an orphan goto the structurizer
            // parked at the method end; bare breaks are illegal there and
            // dropping them is exactly the exit fall-through, jdk11
            // Resolver: `} while (changed); break;`).
            if i + 1 == v.len()
                && (undefined_jump(&v[i], defined, ids)
                    || (!in_loop
                        && matches!(&v[i], Stmt::Break(None) | Stmt::Continue(None))))
            {
                v.remove(i);
                continue;
            }
            // Tail if/else where ONE branch is an undefined-label break
            // (the switch fall-through edge): keep the other branch under
            // the (possibly negated) condition and fall through.
            if i + 1 == v.len() && try_fold_tail_if(&mut v[i], defined, ids) {
                if v[i].is_empty_block() {
                    v.remove(i);
                    continue;
                }
            }
            fix_stmt(&mut v[i], defined, ids, in_loop);
            i += 1;
        }
    }
    fn fix_stmt(s: &mut Stmt, defined: &HashSet<String>, ids: &HashSet<u32>, in_loop: bool) {
        match s {
            Stmt::Break(Some(l)) if !defined.contains(l) => {
                *s = if in_loop { Stmt::Break(None) } else { Stmt::Block(vec![]) };
            }
            Stmt::Continue(Some(l)) if !defined.contains(l) => {
                *s = if in_loop { Stmt::Continue(None) } else { Stmt::Block(vec![]) };
            }
            Stmt::Goto(id) if !ids.contains(id) => {
                *s = if in_loop { Stmt::Break(None) } else { Stmt::Block(vec![]) };
            }
            Stmt::Block(v) => fix_vec(v, defined, ids, in_loop),
            Stmt::If { then_stmt, else_stmt, .. } => {
                fix_stmt(then_stmt, defined, ids, in_loop);
                if let Some(e) = else_stmt {
                    fix_stmt(e, defined, ids, in_loop);
                }
            }
            Stmt::While { body, .. } | Stmt::DoWhile { body, .. } | Stmt::ForEach { body, .. } => {
                fix_stmt(body, defined, ids, true);
            }
            Stmt::For { init, body, .. } => {
                init.iter_mut().for_each(|x| fix_stmt(x, defined, ids, in_loop));
                fix_stmt(body, defined, ids, true);
            }
            Stmt::Labeled { body, .. } | Stmt::Synchronized { body, .. } => {
                fix_stmt(body, defined, ids, in_loop);
            }
            Stmt::Switch { cases, default, .. } => {
                for c in cases.iter_mut() {
                    fix_vec(&mut c.body, defined, ids, true);
                }
                if let Some(d) = default {
                    fix_stmt(d, defined, ids, true);
                }
            }
            Stmt::Try { body, catches, finally } => {
                fix_stmt(body, defined, ids, in_loop);
                for c in catches.iter_mut() {
                    fix_stmt(&mut c.body, defined, ids, in_loop);
                }
                if let Some(f) = finally {
                    fix_stmt(f, defined, ids, in_loop);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                resources.iter_mut().for_each(|x| fix_stmt(x, defined, ids, in_loop));
                fix_stmt(body, defined, ids, in_loop);
                for c in catches.iter_mut() {
                    fix_stmt(&mut c.body, defined, ids, in_loop);
                }
                if let Some(f) = finally {
                    fix_stmt(f, defined, ids, in_loop);
                }
            }
            _ => {}
        }
    }
    fix_stmt(s, &defined, &defined_ids, false);
    // Removed orphan jumps can leave empty blocks behind.
    fn strip_empty(v: &mut Stmt) {
        if let Stmt::Block(items) = v {
            items.iter_mut().for_each(strip_empty);
            items.retain(|x| !x.is_empty_block());
        }
    }
    strip_empty(s);
}

/// `L: do {..} while (c); break L;` — loop-exit edges materialized as a
/// labeled break right AFTER the loop they name are do-while rotation
/// residue: illegal Java ("在 switch 或 loop 外部中断") and redundant
/// (control already falls through). Drop them (jdk17 GregorianCalendar
/// cutover-month case; xml Parser state machine).
pub(crate) fn prune_post_loop_label_breaks(s: &mut Stmt) {
    fn clear_break(st: &mut Stmt) {
        match st {
            s @ Stmt::Break(Some(_)) => {
                *s = Stmt::Block(vec![]);
            }
            Stmt::Block(inner) => {
                if !inner.is_empty() {
                    clear_break(&mut inner[0]);
                    inner.retain(|x| !x.is_empty_block());
                }
            }
            _ => {}
        }
    }
    fn unwrap_single(v: &Stmt) -> &Stmt {
        let mut cur = v;
        loop {
            match cur {
                Stmt::Block(inner) if inner.len() == 1 => cur = &inner[0],
                other => return other,
            }
        }
    }
    fn is_break_of(st: &Stmt, label: &str) -> bool {
        match unwrap_single(st) {
            Stmt::Break(Some(l)) => l == label,
            _ => false,
        }
    }
    fn label_of(st: &Stmt) -> Option<&str> {
        match st {
            Stmt::Labeled { label, body } => match unwrap_single(body) {
                Stmt::While { .. } | Stmt::DoWhile { .. } | Stmt::For { .. } | Stmt::ForEach { .. } => {
                    Some(label.as_str())
                }
                _ => None,
            },
            _ => None,
        }
    }
    fn prune_in(v: &mut Vec<Stmt>) {
        let mut i = 0;
        while i + 1 < v.len() {
            let label_owned = label_of(&v[i]).map(|l| l.to_string());
            if std::env::var("JCDC_DBG_PRUNE").is_ok() {
                if let Some(l) = &label_owned {
                    eprintln!("PRUNE label={} next_is_break={}", l, is_break_of(&v[i + 1], l));
                }
            }
            if let Some(label) = label_owned {
                if is_break_of(&v[i + 1], &label) {
                    clear_break(&mut v[i + 1]);
                    if v[i + 1].is_empty_block() {
                        v.remove(i + 1);
                    }
                    continue;
                }
            }
            i += 1;
        }
        for x in v.iter_mut() {
            prune_post_loop_label_breaks(x);
        }
    }
    if let Stmt::Block(v) = s {
        prune_in(v);
    } else {
        match s {
            Stmt::If { then_stmt, else_stmt, .. } => {
                prune_post_loop_label_breaks(then_stmt);
                if let Some(e) = else_stmt {
                    prune_post_loop_label_breaks(e);
                }
            }
            Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => {
                prune_post_loop_label_breaks(body);
            }
            Stmt::For { init, body, .. } => {
                init.iter_mut().for_each(prune_post_loop_label_breaks);
                prune_post_loop_label_breaks(body);
            }
            Stmt::ForEach { body, .. } => prune_post_loop_label_breaks(body),
            Stmt::Labeled { label, body } => {
                // The printer pins the label to the body's FIRST line: a
                // Block([loop, break label]) prints as `label: do..while;
                // break label;` — the break escapes its own label scope
                // ("未定义的标签"). Drop the redundant break right after
                // the loop (fall-through is the same edge).
                if let Stmt::Block(v) = body.as_mut() {
                    let mut i = 0;
                    while i + 1 < v.len() {
                        let is_loop = matches!(
                            unwrap_single(&v[i]),
                            Stmt::While { .. } | Stmt::DoWhile { .. } | Stmt::For { .. }
                                | Stmt::ForEach { .. }
                        );
                        if is_loop && is_break_of(&v[i + 1], label) {
                            clear_break(&mut v[i + 1]);
                            if v[i + 1].is_empty_block() {
                                v.remove(i + 1);
                            }
                            continue;
                        }
                        i += 1;
                    }
                }
                prune_post_loop_label_breaks(body);
            }
            Stmt::Synchronized { body, .. } => {
                prune_post_loop_label_breaks(body);
            }
            Stmt::Switch { cases, default, .. } => {
                for c in cases.iter_mut() {
                    prune_in(&mut c.body);
                }
                if let Some(d) = default {
                    prune_post_loop_label_breaks(d);
                }
            }
            Stmt::Try { body, catches, finally } => {
                prune_post_loop_label_breaks(body);
                for c in catches.iter_mut() {
                    prune_post_loop_label_breaks(&mut c.body);
                }
                if let Some(f) = finally {
                    prune_post_loop_label_breaks(f);
                }
            }
            Stmt::TryWithResources { resources, body, catches, finally } => {
                resources.iter_mut().for_each(prune_post_loop_label_breaks);
                prune_post_loop_label_breaks(body);
                for c in catches.iter_mut() {
                    prune_post_loop_label_breaks(&mut c.body);
                }
                if let Some(f) = finally {
                    prune_post_loop_label_breaks(f);
                }
            }
            _ => {}
        }
    }
}

fn disambiguate_nested_locals(vt: &mut VarTable, body: &Stmt) {
    // var id -> current printed name
    let mut scopes: Vec<std::collections::HashMap<String, u32>> =
        vec![std::collections::HashMap::new()];
    // Names ever given to OTHER vars (renames mutate vt globally, so a
    // var's EARLIER decl sites print under the new name too): a rename
    // candidate must avoid all of them, not just the visible scopes
    // (asm ClassReader: var43 re-declared under var42 took "x1" from a
    // popped sibling scope where var44 already held it — var43's first
    // decl then collided with var44's in a still-enclosing scope).
    let mut used: std::collections::HashMap<String, u32> = std::collections::HashMap::new();
    disambig_walk(vt, body, &mut scopes, &mut used);
}

fn visible_name_owner(scopes: &[std::collections::HashMap<String, u32>], name: &str) -> Option<u32> {
    scopes.iter().rev().find_map(|sc| sc.get(name).copied())
}

fn disambig_walk(
    vt: &mut VarTable,
    s: &Stmt,
    scopes: &mut Vec<std::collections::HashMap<String, u32>>,
    used: &mut std::collections::HashMap<String, u32>,
) {
    fn declare(
        vt: &mut VarTable,
        var: u32,
        scopes: &mut Vec<std::collections::HashMap<String, u32>>,
        used: &mut std::collections::HashMap<String, u32>,
    ) {
        let name = vt.vars[var as usize].name.clone();
        if let Some(owner) = visible_name_owner(scopes, &name) {
            if owner != var {
                // collision with an enclosing different variable: rename
                let mut k = 1;
                loop {
                    let cand = format!("{}{}", name, k);
                    let taken_visible = visible_name_owner(scopes, &cand).is_some();
                    let taken_used = used
                        .get(&cand)
                        .map(|o| *o != var)
                        .unwrap_or(false);
                    if !taken_visible && !taken_used {
                        vt.vars[var as usize].name = cand.clone();
                        scopes.last_mut().unwrap().insert(cand.clone(), var);
                        used.insert(cand, var);
                        return;
                    }
                    k += 1;
                }
            }
        }
        scopes.last_mut().unwrap().insert(name.clone(), var);
        used.insert(name, var);
    }
    match s {
        Stmt::Block(v) => {
            scopes.push(std::collections::HashMap::new());
            for x in v {
                disambig_walk(vt, x, scopes, used);
            }
            scopes.pop();
        }
        Stmt::LocalDef { var, init, .. } => {
            if let Some(e) = init {
                let _ = e;
            }
            declare(vt, *var, scopes, used);
        }
        Stmt::ForEach { var, iterable, body, .. } => {
            let _ = iterable;
            scopes.push(std::collections::HashMap::new());
            declare(vt, *var, scopes, used);
            disambig_walk(vt, body, scopes, used);
            scopes.pop();
        }
        Stmt::For { init, body, .. } => {
            scopes.push(std::collections::HashMap::new());
            for i in init {
                disambig_walk(vt, i, scopes, used);
            }
            disambig_walk(vt, body, scopes, used);
            scopes.pop();
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            disambig_walk(vt, then_stmt, scopes, used);
            if let Some(e) = else_stmt {
                disambig_walk(vt, e, scopes, used);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => disambig_walk(vt, body, scopes, used),
        Stmt::Try { body, catches, finally } => {
            disambig_walk(vt, body, scopes, used);
            for c in catches {
                scopes.push(std::collections::HashMap::new());
                if c.var != u32::MAX && (c.var as usize) < vt.vars.len() {
                    declare(vt, c.var, scopes, used);
                }
                disambig_walk(vt, &c.body, scopes, used);
                scopes.pop();
            }
            if let Some(f) = finally {
                disambig_walk(vt, f, scopes, used);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources {
                disambig_walk(vt, res, scopes, used);
            }
            disambig_walk(vt, body, scopes, used);
            for c in catches {
                scopes.push(std::collections::HashMap::new());
                if c.var != u32::MAX && (c.var as usize) < vt.vars.len() {
                    declare(vt, c.var, scopes, used);
                }
                disambig_walk(vt, &c.body, scopes, used);
                scopes.pop();
            }
            if let Some(f) = finally {
                disambig_walk(vt, f, scopes, used);
            }
        }
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                scopes.push(std::collections::HashMap::new());
                for st in &c.body {
                    disambig_walk(vt, st, scopes, used);
                }
                scopes.pop();
            }
            if let Some(d) = default {
                disambig_walk(vt, d, scopes, used);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => {
            disambig_walk(vt, body, scopes, used)
        }
        _ => {}
    }
}


fn collect_assigned_vars(s: &Stmt, out: &mut HashSet<u32>) {
    match s {
        Stmt::LocalDef { var, .. } => {
            out.insert(*var);
        }
        Stmt::ExprStmt(Expr::Assign { target, .. }) => {
            if let Expr::Local { var, .. } = &**target {
                out.insert(*var);
            }
        }
        _ => {}
    }
}

fn collect_expr_locals(e: &Expr, out: &mut HashSet<u32>) {
    match e {
        Expr::Local { var, .. } => {
            out.insert(*var);
        }
        Expr::Cond { c, t, f } => {
            collect_expr_locals(c, out);
            collect_expr_locals(t, out);
            collect_expr_locals(f, out);
        }
        Expr::Bin { l, r, .. } | Expr::Assign { target: l, value: r, .. } => {
            collect_expr_locals(l, out);
            collect_expr_locals(r, out);
        }
        Expr::Un { e: x, .. }
        | Expr::Cast { e: x, .. }
        | Expr::InstanceOf { e: x, .. }
        | Expr::PreIncDec { e: x, .. }
        | Expr::PostIncDec { e: x, .. } => collect_expr_locals(x, out),
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
        _ => {}
    }
}


fn split_reassigned_synthetic(vt: &mut VarTable, body: &mut Stmt) {
    use std::collections::HashMap;
    let n = vt.vars.len();
    let synth: Vec<bool> = (0..n).map(|v| vt.vars[v].synthetic_name && !vt.vars[v].is_param).collect();
    let mut active: HashMap<u32, u32> = HashMap::new(); // original -> current id
    let mut cur_ty: HashMap<u32, JavaType> = HashMap::new();
    let mut cur_concrete: HashMap<u32, JavaType> = HashMap::new();
    let mut seq = 0usize;
    split_walk(body, vt, &synth, &mut active, &mut cur_ty, &mut cur_concrete, &mut seq);
}

fn value_concrete_type(e: &Expr) -> Option<JavaType> {
    match e.type_ref().erased() {
        JavaType::Void => None,
        t => Some(t.clone()),
    }
}

fn split_walk(
    s: &mut Stmt,
    vt: &mut VarTable,
    synth: &[bool],
    active: &mut HashMap<u32, u32>,
    cur_ty: &mut HashMap<u32, JavaType>,
    cur_concrete: &mut HashMap<u32, JavaType>,
    seq: &mut usize,
) {
    // Rewrite all Local refs in an expression to the active id.
    fn rw(e: &mut Expr, active: &HashMap<u32, u32>) {
        match e {
            Expr::Local { var, .. } => {
                if let Some(&a) = active.get(var) {
                    *var = a;
                }
            }
            Expr::Cond { c, t, f } => {
                rw(c, active);
                rw(t, active);
                rw(f, active);
            }
            Expr::Bin { l, r, .. } => {
                rw(l, active);
                rw(r, active);
            }
            Expr::Assign { target, value, .. } => {
                // target handled by caller for the split decision; rewrite
                // nested parts here
                match &mut **target {
                    Expr::ArrayIndex { array, index } => {
                        rw(array, active);
                        rw(index, active);
                    }
                    Expr::Field { owner: Some(o), .. } => rw(o, active),
                    other => rw(other, active),
                }
                rw(value, active);
            }
            Expr::Un { e: x, .. }
            | Expr::Cast { e: x, .. }
            | Expr::InstanceOf { e: x, .. }
            | Expr::PreIncDec { e: x, .. }
            | Expr::PostIncDec { e: x, .. } => rw(x, active),
            Expr::Method { owner, args, .. } => {
                if let Some(o) = owner {
                    rw(o, active);
                }
                args.iter_mut().for_each(|a| rw(a, active));
            }
            Expr::Field { owner: Some(o), .. } => rw(o, active),
            Expr::ArrayIndex { array, index } => {
                rw(array, active);
                rw(index, active);
            }
            Expr::New { args, .. } => args.iter_mut().for_each(|a| rw(a, active)),
            Expr::NewArray { dims, init, .. } => {
                dims.iter_mut().for_each(|d| rw(d, active));
                if let Some(vals) = init {
                    vals.iter_mut().for_each(|v| rw(v, active));
                }
            }
            _ => {}
        }
    }

    fn handle_assign(
        var: u32,
        value: &Expr,
        vt: &mut VarTable,
        synth: &[bool],
        active: &mut HashMap<u32, u32>,
        cur_ty: &mut HashMap<u32, JavaType>,
        cur_concrete: &mut HashMap<u32, JavaType>,
        seq: &mut usize,
    ) -> u32 {
        let cur = active.get(&var).copied().unwrap_or(var);
        if !synth.get(var as usize).copied().unwrap_or(false) {
            return cur;
        }
        // Wide merge variables deliberately receive values of DIFFERENT types
        // across mutually-exclusive branches (switch cases, diamond arms); the
        // merge join already widened them to Object. Splitting them per
        // assigned type — as sequential slot-reuse would — shatters the single
        // merge into several apparent vars, so the post-merge read sees only
        // the last branch's var (e.g. DirectMethodHandle.make returned the
        // default-case value for every refKind). Keep them as one identity.
        if vt.wide_stack_vars.contains(&var) {
            return cur;
        }
        // `null` is assignable to every reference lineage: a branch that
        // stores null into a merge variable must NOT split it off from the
        // concrete-typed side. Splitting renamed only the null def (Object
        // stackN1 = null) while every read kept the cast-side identity --
        // the null path read a definitely-unassigned variable (jdk26
        // SplitConstantPool.classEntry's `isArray && typeSym instanceof
        // ClassDesc cd ? cd : null` ctor-arg diamond:
        // 可能尚未初始化变量stack476).
        if matches!(value, Expr::Const(crate::expr::ConstVal::Null)) {
            return cur;
        }
        let Some(nt) = value_concrete_type(value) else { return cur };
        let numeric = |t: &JavaType| {
            matches!(
                t,
                JavaType::Boolean
                    | JavaType::Byte
                    | JavaType::Char
                    | JavaType::Short
                    | JavaType::Int
                    | JavaType::Long
                    | JavaType::Float
                    | JavaType::Double
            )
        };
        let unknown = |t: &JavaType| {
            matches!(t, JavaType::Object(n) if n == "java/lang/Object")
        };
        let need_split = match cur_ty.get(&var) {
            Some(prev) => {
                if *prev == nt {
                    false
                } else if !unknown(prev) {
                    // Numeric-to-numeric reuse is handled by type joining;
                    // everything else (array vs iterator, int vs reference,
                    // distinct classes) needs a distinct variable.
                    !(numeric(prev) && numeric(&nt))
                } else if !unknown(&nt) {
                    // Unknown->concrete: split only when the variable
                    // already CARRIED a different concrete type earlier
                    // (jdk11 KeyStore.getInstance slot 6: null -> Iterator
                    // -> KeyStore; without the split the inferred Object
                    // var serves both lineages and neither declaration
                    // type-checks).
                    let carried = cur_concrete.get(&var).map(|c| *c != nt).unwrap_or(false);
                    if carried && !numeric(&nt) {
                        true
                    } else {
                        if !numeric(&nt) {
                            cur_ty.insert(var, nt.clone());
                            // Narrow a plain-Object synthetic to its first
                            // concrete lineage type so the declaration and
                            // the loop calls type-check (var6_80 serves the
                            // Iterator lineage until the split).
                            if !vt.wide_stack_vars.contains(&var) {
                                if let JavaType::Object(n) = vt.vars[cur as usize].ty.erased() {
                                    if n == "java/lang/Object" {
                                        vt.vars[cur as usize].ty = TypeRef::J(nt.clone());
                                    }
                                }
                            }
                        }
                        false
                    }
                } else {
                    false
                }
            }
            None => {
                // First concrete assignment: narrow a plain-Object
                // synthetic (gap) variable to the assigned type. Wide
                // merge variables must stay Object (they receive values
                // of several incompatible types across branches).
                if !vt.wide_stack_vars.contains(&var) {
                    if let JavaType::Object(n) = vt.vars[cur as usize].ty.erased() {
                        if n == "java/lang/Object" {
                            if std::env::var("JCDC_DBG_MERGE").is_ok() {
                                eprintln!("SPLITNARROW v={} -> {:?}", cur, nt);
                            }
                            vt.vars[cur as usize].ty = TypeRef::J(nt.clone());
                        }
                    }
                }
                false
            }
        };
        if !unknown(&nt) {
            cur_concrete.insert(var, nt.clone());
        }
        if need_split {
            let base_slot = vt.vars[cur as usize].slot;
            *seq += 1;
            let id = vt.add_split(base_slot, format!("{}{}", vt.vars[cur as usize].name, seq), TypeRef::J(nt.clone()));
            active.insert(var, id);
            cur_ty.insert(var, nt.clone());
            cur_concrete.insert(var, nt);
            id
        } else {
            cur_ty.entry(var).or_insert(nt);
            cur
        }
    }

    match s {
        Stmt::Block(v) => {
            for x in v.iter_mut() {
                split_walk(x, vt, synth, active, cur_ty, cur_concrete, seq);
            }
        }
        Stmt::LocalDef { var, init, .. } => {
            if let Some(e) = init {
                let id = handle_assign(*var, e, vt, synth, active, cur_ty, cur_concrete, seq);
                rw(e, active);
                *var = id;
            }
        }
        Stmt::ExprStmt(e) => {
            if let Expr::Assign { target, value, .. } = e {
                if let Expr::Local { var, .. } = &**target {
                    let v = *var;
                    let id = handle_assign(v, value, vt, synth, active, cur_ty, cur_concrete, seq);
                    rw(value, active);
                    if let Expr::Assign { target, .. } = e {
                        if let Expr::Local { var, ty } = &mut **target {
                            *var = id;
                            *ty = vt.vars[id as usize].ty.clone();
                        }
                    }
                    return;
                }
            }
            rw(e, active);
        }
        Stmt::Return(Some(x)) => rw(x, active),
        Stmt::Throw(e) => rw(e, active),
        Stmt::If { cond, then_stmt, else_stmt } => {
            rw(cond, active);
            // Branches may diverge; keep it simple and process then/else
            // with the same mapping (slot reuse across branches is rare).
            split_walk(then_stmt, vt, synth, active, cur_ty, cur_concrete, seq);
            if let Some(e) = else_stmt {
                split_walk(e, vt, synth, active, cur_ty, cur_concrete, seq);
            }
        }
        Stmt::While { cond, body } => {
            rw(cond, active);
            split_walk(body, vt, synth, active, cur_ty, cur_concrete, seq);
        }
        Stmt::DoWhile { body, cond } => {
            split_walk(body, vt, synth, active, cur_ty, cur_concrete, seq);
            rw(cond, active);
        }
        Stmt::For { init, cond, update, body } => {
            for i in init {
                split_walk(i, vt, synth, active, cur_ty, cur_concrete, seq);
            }
            if let Some(c) = cond {
                rw(c, active);
            }
            split_walk(body, vt, synth, active, cur_ty, cur_concrete, seq);
            update.iter_mut().for_each(|u| rw(u, active));
        }
        Stmt::ForEach { iterable, body, .. } => {
            rw(iterable, active);
            split_walk(body, vt, synth, active, cur_ty, cur_concrete, seq);
        }
        Stmt::Try { body, catches, finally } => {
            split_walk(body, vt, synth, active, cur_ty, cur_concrete, seq);
            for c in catches {
                split_walk(&mut c.body, vt, synth, active, cur_ty, cur_concrete, seq);
            }
            if let Some(f) = finally {
                split_walk(f, vt, synth, active, cur_ty, cur_concrete, seq);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { split_walk(res, vt, synth, active, cur_ty, cur_concrete, seq); }
            split_walk(body, vt, synth, active, cur_ty, cur_concrete, seq);
            for c in catches {
                split_walk(&mut c.body, vt, synth, active, cur_ty, cur_concrete, seq);
            }
            if let Some(f) = finally {
                split_walk(f, vt, synth, active, cur_ty, cur_concrete, seq);
            }
        }
        Stmt::Switch { selector, cases, default, .. } => {
            rw(selector, active);
            for c in cases {
                c.body.iter_mut().for_each(|st| split_walk(st, vt, synth, active, cur_ty, cur_concrete, seq));
            }
            if let Some(d) = default {
                split_walk(d, vt, synth, active, cur_ty, cur_concrete, seq);
            }
        }
        Stmt::Synchronized { lock, body } => {
            rw(lock, active);
            split_walk(body, vt, synth, active, cur_ty, cur_concrete, seq);
        }
        Stmt::Labeled { body, .. } => split_walk(body, vt, synth, active, cur_ty, cur_concrete, seq),
        _ => {}
    }
}


/// Variables whose declared type is generic (`T[]`, `List<E>`) receive
/// erased values from the bytecode; reinsert the source-level cast so the
/// declaration compiles (`T[] r = (T[]) copyOf(...);`).
pub(crate) fn classsig_internal(cs: &jcdc_jvm::ClassSig) -> String {
    let joined = cs
        .parts
        .iter()
        .map(|p| p.name.as_str())
        .collect::<Vec<_>>()
        .join("$");
    if cs.package.is_empty() {
        joined
    } else {
        format!("{}/{}", cs.package, joined)
    }
}

pub(crate) fn contains_typevar(t: &jcdc_jvm::GenericType) -> bool {
    use jcdc_jvm::GenericType as G;
    match t {
        G::TypeVar(_) => true,
        G::Array(i) => contains_typevar(i),
        G::Class(cs) => cs.parts.iter().any(|p| p.args.iter().any(contains_typevar)),
        G::Wildcard(jcdc_jvm::WildcardBound::Extends(i))
        | G::Wildcard(jcdc_jvm::WildcardBound::Super(i)) => contains_typevar(i),
        _ => false,
    }
}

pub(crate) fn subst_typevars(
    t: &jcdc_jvm::GenericType,
    params: &[jcdc_jvm::TypeParam],
    args: &[jcdc_jvm::GenericType],
) -> jcdc_jvm::GenericType {
    use jcdc_jvm::GenericType as G;
    match t {
        G::TypeVar(n) => params
            .iter()
            .position(|p| &p.name == n)
            .and_then(|i| args.get(i).cloned())
            .unwrap_or_else(|| t.clone()),
        G::Array(i) => G::Array(Box::new(subst_typevars(i, params, args))),
        G::Class(cs) => G::Class(jcdc_jvm::ClassSig {
            package: cs.package.clone(),
            parts: cs
                .parts
                .iter()
                .map(|p| jcdc_jvm::ClassSigPart {
                    name: p.name.clone(),
                    args: p.args.iter().map(|a| subst_typevars(a, params, args)).collect(),
                })
                .collect(),
        }),
        G::Wildcard(jcdc_jvm::WildcardBound::Extends(i)) => {
            G::Wildcard(jcdc_jvm::WildcardBound::Extends(Box::new(
                subst_typevars(i, params, args),
            )))
        }
        G::Wildcard(jcdc_jvm::WildcardBound::Super(i)) => {
            G::Wildcard(jcdc_jvm::WildcardBound::Super(Box::new(
                subst_typevars(i, params, args),
            )))
        }
        other => other.clone(),
    }
}

/// Java forbids nested wildcards (`? super ? extends T`): an instantiation
/// producing one is unusable as a printed type.
pub(crate) fn has_nested_wildcard(t: &jcdc_jvm::GenericType) -> bool {
    use jcdc_jvm::GenericType as G;
    match t {
        G::Wildcard(jcdc_jvm::WildcardBound::Extends(i))
        | G::Wildcard(jcdc_jvm::WildcardBound::Super(i)) => {
            matches!(i.as_ref(), G::Wildcard(_)) || has_nested_wildcard(i)
        }
        G::Array(i) => has_nested_wildcard(i),
        G::Class(cs) => cs.parts.iter().any(|p| p.args.iter().any(has_nested_wildcard)),
        _ => false,
    }
}

/// The generic type of instance field `name` as instantiated by the owner
/// expression's parameterization (e.g. owner `Entry<K,V>` + field
/// `next: Entry<TK,TV>` → `Entry<K,V>`). None when not resolvable or when
/// the field type carries no type variables (no cast could be needed).
pub(crate) fn instantiated_field_type(
    owner: Option<&Expr>,
    cls: &str,
    name: &str,
    pool: &ClassPool,
    pc: &PoolClass,
) -> Option<TypeRef> {
    let (decl, args): (String, Vec<jcdc_jvm::GenericType>) = match owner {
        Some(Expr::This) => {
            let cs = pc.class_attr("Signature").and_then(|b| {
                if b.len() < 2 {
                    return None;
                }
                let idx = u16::from_be_bytes([b[0], b[1]]);
                pc.utf8(idx)
                    .and_then(|s| jcdc_jvm::parse_class_signature(s))
            })?;
            let args = cs.params.iter().map(|p| jcdc_jvm::GenericType::TypeVar(p.name.clone())).collect();
            (pc.internal_name.clone(), args)
        }
        Some(o) => match o.type_ref() {
            TypeRef::G(jcdc_jvm::GenericType::Class(cs)) => {
                let args = cs.parts.last()?.args.clone();
                (classsig_internal(&cs), args)
            }
            t => match t.erased() {
                JavaType::Object(n) => (n, Vec::new()),
                _ => return None,
            },
        },
        None => (cls.to_string(), Vec::new()),
    };
    // Field lookup walks the super chain carrying per-hop instantiation:
    // an F-bounded inherited field (jdk11 Nodes.CollectorTask.leftChild:
    // declared on AbstractTask<P_IN,P_OUT,R,K> as K, instantiated to
    // CollectorTask<P_IN,P_OUT,T_NODE,T_BUILDER>) must resolve through the
    // declaring superclass, not just the receiver class's own fields.
    let mut queue: std::collections::VecDeque<(String, Vec<jcdc_jvm::GenericType>)> =
        std::collections::VecDeque::new();
    queue.push_back((decl, args));
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
        let Some(f) = dref.cf.fields.iter().find(|f| {
            !f.access_flags.contains(jcdc_classfile::FieldAccessFlags::STATIC)
                && dref.utf8(f.name_index) == Some(name)
        }) else {
            queue.extend(crate::classdec::class_supers_args(dref, &cur_args));
            continue;
        };
        let sig_bytes = f.attributes.iter().find_map(|a| {
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
        let sig_str = dref.utf8(idx)?;
        let ft = jcdc_jvm::parse_field_signature(sig_str)?;
        if !contains_typevar(&ft) {
            // Concrete parameterizations still upgrade the read
            // (Hashtable<String,SocketPermission> perms: the source-level
            // values() type Collection<SocketPermission> drives the
            // inconvertible-cast raw fallback); only bare/raw forms bail.
            let is_parameterized = match &ft {
                jcdc_jvm::GenericType::Class(cs) => {
                    cs.parts.iter().any(|p| !p.args.is_empty())
                }
                jcdc_jvm::GenericType::Array(_) => true,
                _ => false,
            };
            if !is_parameterized {
                return None;
            }
        }
        let params = dref
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
        if cur_args.len() != params.len() {
            return None;
        }
        let inst = subst_typevars(&ft, &params, &cur_args);
        // Substituting a captured (wildcard) owner argument can nest wildcards
        // (`? super ? extends T`), which is not valid Java; leave such writes
        // with their raw checkcast.
        if has_nested_wildcard(&inst) {
            return None;
        }
        return Some(TypeRef::G(inst));
    }
    None
}

/// The Signature return type variable of a generic method call, when the
/// callee's return IS a bare type variable (inference at the assignment
/// position binds it to the target — no cast needed, and an erasure cast
/// would be illegal against a type-var target).
fn generic_call_ret_typevar(a: &Expr, pool: &ClassPool) -> Option<String> {
    let (cls, name, desc) = match a {
        Expr::Method { cls, name, desc, .. } => (cls.as_str(), name.as_str(), desc),
        _ => return None,
    };
    let mut s = String::new();
    for t in &desc.args {
        s.push_str(&t.to_descriptor());
    }
    let want_desc = format!("({}){}", s, desc.ret.to_descriptor());
    let dpc = pool.get(cls)?;
    let mi = (0..dpc.cf.methods.len()).find(|&i| {
        dpc.method_name(i) == Some(name) && dpc.method_desc(i) == Some(want_desc.as_str())
    })?;
    let sig_bytes = dpc.cf.methods[mi].attributes.iter().find_map(|at| {
        if dpc.utf8(at.attribute_name_index) == Some("Signature") {
            Some(at.info.as_slice())
        } else {
            None
        }
    })?;
    if sig_bytes.len() < 2 {
        return None;
    }
    let idx = u16::from_be_bytes([sig_bytes[0], sig_bytes[1]]);
    let msig = dpc
        .utf8(idx)
        .and_then(|x| jcdc_jvm::parse_method_signature(x))?;
    match msig.ret {
        jcdc_jvm::GenericType::TypeVar(v) => Some(v),
        _ => None,
    }
}

fn cast_generic_locals(vt: &VarTable, pool: &ClassPool, pc: &PoolClass, s: &mut Stmt) {
    fn target_ty(e: &Expr, vt: &VarTable) -> Option<TypeRef> {
        match e {
            Expr::Local { var, .. } => Some(vt.var(*var).ty.clone()),
            _ => None,
        }
    }
    fn compatible_erasure(have: &JavaType, want_er: &JavaType) -> bool {
        match (have, want_er) {
            (JavaType::Array(_), JavaType::Array(_)) => true,
            (JavaType::Object(x), JavaType::Object(y)) => x == y,
            _ => false,
        }
    }
    fn fix(value: &mut Expr, want: &TypeRef, pool: &ClassPool, pc: &PoolClass) {
        if matches!(value, Expr::Const(_)) {
            return;
        }
        // @PolymorphicSignature calls (JVMS 2.9 closed set on
        // MethodHandle/VarHandle) get their descriptor-return cast at EMIT
        // level (classdec::polymorphic_ret_cast); wrapping here too would
        // double-cast. Nothing else to fix up on these values.
        if matches!(value, Expr::Method { cls, name, .. }
            if crate::classdec::is_spec_polymorphic(cls, name))
        {
            return;
        }
        // A GENERICS-ONLY cast around a generic call breaks target-type
        // inference (`(Map<K,V>) Map.ofEntries(...)`); javac emits no
        // checkcast for a generics-only cast at all (erasure unchanged), so
        // such an AST cast is our own synthesis — drop it. A cast whose
        // erasure DIFFERS from the call's descriptor return came from a real
        // bytecode checkcast and was in the source: `(ByteBuffer)
        // Objects.requireNonNull(obb)` — dropping it leaves requireNonNull's
        // T with lower bound Object (the arg) and upper bound ByteBuffer
        // (the local's type): "inference variable T has incompatible
        // bounds" (jdk11 VarHandleByteArrayAs*, 31 errors per sibling).
        if let Expr::Cast { ty, e: ce } = value {
            // Only a GENERICS-ONLY G-typed cast can be synthetic (javac
            // emits no checkcast when the erasure is unchanged); a
            // J-typed cast is a REAL bytecode checkcast and must survive
            // here so cast_generic_returns can retype it to the generic
            // target: `a = (T[]) Arrays.copyOfRange(items, ..,
            // a.getClass())` (jdk11 ArrayBlockingQueue.toArray) has a
            // real checkcast Object[] that this branch used to drop —
            // 推论变量 T#1 具有不兼容的上限 x2 trees. For G casts over
            // generic calls, a typevar/array-of-typevar cast erases to
            // its BOUND, not the bare descriptor return: compare against
            // that too before calling it synthetic.
            let bound_er = match ty {
                TypeRef::G(jcdc_jvm::GenericType::TypeVar(n)) => {
                    crate::classdec::typevar_bound_erasure_in(n, &[], pc)
                }
                TypeRef::G(jcdc_jvm::GenericType::Array(inner)) => {
                    match inner.as_ref() {
                        jcdc_jvm::GenericType::TypeVar(n) => {
                            crate::classdec::typevar_bound_erasure_in(n, &[], pc)
                                .map(|b| jcdc_jvm::JavaType::Array(Box::new(b)))
                        }
                        _ => None,
                    }
                }
                _ => None,
            };
            let real_checkcast = matches!(ty, TypeRef::J(_))
                || matches!(&**ce, Expr::Method { desc, .. } if {
                    desc.ret != ty.erased()
                        || match (&desc.ret, &bound_er) {
                            (
                                jcdc_jvm::JavaType::Object(x),
                                Some(jcdc_jvm::JavaType::Object(y)),
                            ) => x != y,
                            (
                                jcdc_jvm::JavaType::Array(x),
                                Some(jcdc_jvm::JavaType::Array(y)),
                            ) => x != y,
                            _ => false,
                        }
                });
            if !real_checkcast && crate::classdec::is_generic_call(ce, pool) {
                let inner = std::mem::replace(value, Expr::This);
                if let Expr::Cast { e: ce2, .. } = inner {
                    *value = *ce2;
                }
                return;
            }
        }
        // An upgraded precise G cast can be INVARIANT-INCONVERTIBLE to the
        // assignment target (jdk26 Properties.store0:
        // (Set<Map.Entry<Object,Object>>) entrySet() against a
        // Collection<Map.Entry<String,String>> local — the source bridges
        // with a RAW intermediate: (Set<Map.Entry<String,String>>) (Set)
        // entrySet()). Demote the existing cast to its erasure and wrap
        // with the target: the raw hop makes both steps legal unchecked
        // conversions.
        if let (Expr::Cast { ty, .. }, TypeRef::G(wg @ jcdc_jvm::GenericType::Class(wc))) =
            (&*value, want)
        {
            if let TypeRef::G(jcdc_jvm::GenericType::Class(cc)) = ty {
                let args_differ = match (cc.parts.last(), wc.parts.last()) {
                    (Some(a), Some(b)) => a.args != b.args,
                    _ => false,
                };
                let cc_internal = crate::method::classsig_internal(cc);
                let wc_internal = crate::method::classsig_internal(wc);
                let convertible_classes = cc_internal == wc_internal
                    || crate::classdec::is_subtype_of(
                        pool,
                        &jcdc_jvm::JavaType::Object(cc_internal.clone()),
                        &wc_internal,
                    );
                if args_differ
                    && convertible_classes
                    && !crate::classdec::g_has_wildcard(&jcdc_jvm::GenericType::Class(cc.clone()))
                    && !crate::classdec::g_has_wildcard(wg)
                {
                    let raw = ty.erased();
                    let wc2 = wc.clone();
                    let wg2 = wg.clone();
                    let _ = wc2;
                    if let Expr::Cast { ty: inner_ty, .. } = value {
                        *inner_ty = TypeRef::J(raw);
                    }
                    let v = std::mem::replace(value, Expr::This);
                    *value = Expr::Cast { ty: TypeRef::G(wg2), e: Box::new(v) };
                    return;
                }
            }
        }
        let TypeRef::G(_) = want else {
            // A boolean value flowing into an int slot was `b ? 1 : 0` in
            // source (the JVM stores both as ints); into a byte/short
            // slot it additionally needs the narrowing cast (jdk11
            // StringCoding.Result.with: `this.coder = (byte)
            // (!String.COMPACT_STRINGS ? 1 : 0)` folded to ixor —
            // boolean无法转换为byte).
            if matches!(
                want,
                TypeRef::J(JavaType::Int | JavaType::Byte | JavaType::Short)
            ) && value.type_ref().erased() == JavaType::Boolean
                && !matches!(value, Expr::Const(_))
            {
                let inner = std::mem::replace(value, Expr::This);
                let mut cond = Expr::Cond {
                    c: Box::new(inner),
                    t: Box::new(Expr::Const(crate::expr::ConstVal::Int(1))),
                    f: Box::new(Expr::Const(crate::expr::ConstVal::Int(0))),
                };
                if !matches!(want, TypeRef::J(JavaType::Int)) {
                    let ty = want.clone();
                    cond = Expr::Cast { ty, e: Box::new(cond) };
                }
                *value = cond;
                return;
            }
            // Concrete target, unknown (plain Object) value: the flow
            // guarantees assignability; make it explicit.
            if let JavaType::Object(n) = want.erased() {
                if n != "java/lang/Object"
                    && value.type_ref().erased() == JavaType::Object("java/lang/Object".into())
                    && matches!(value, Expr::Local { .. } | Expr::Method { .. } | Expr::Field { .. } | Expr::ArrayIndex { .. })
                {
                    let inner = std::mem::replace(value, Expr::This);
                    *value = Expr::Cast { ty: want.clone(), e: Box::new(inner) };
                }
            }
            return;
        };
        // An existing checkcast carries the erasure (`(Object[])`); retype
        // it to the generic target (`(T[])`) when the erasures line up.
        if let Expr::Cast { ty, .. } = value {
            if *ty != *want && compatible_erasure(&ty.erased(), &want.erased()) {
                *ty = want.clone();
            }
            return;
        }
        if value.type_ref() == *want {
            return;
        }
        // A generic call whose signature return IS the target type
        // variable needs no cast at all: the assignment position already
        // types it (`topSpecies = findSpecies(tsk)`; any erasure cast is
        // illegal there — "SpeciesData无法转换为S", jdk26 ClassSpecializer).
        // The match must be through the OWNER's instantiation, not the
        // declared typevar NAME: `Map.Entry<?,?>.getKey()` declares K but
        // returns CAP#1 — the name-only check conflated it with TreeMap's
        // K and dropped the source's `(K)entry.getKey()` cast
        // (CAP#1无法转换为K/V x2 per tree, TreeMap.buildFromSorted).
        if let TypeRef::G(tv_g @ jcdc_jvm::GenericType::TypeVar(tv)) = want {
            if generic_call_ret_typevar(value, pool).as_deref() == Some(tv.as_str()) {
                let skip = match crate::classdec::instantiated_method_ret(value, pool, pc) {
                    Some(inst) => &inst == tv_g,
                    // Unresolvable owner: keep the historical name-based
                    // skip (a wrong cast here broke ClassSpecializer).
                    None => true,
                };
                if skip {
                    return;
                }
            }
        }
        // A call whose SOURCE-level return — instantiated through the
        // owner and the declaring super chain — IS the target type also
        // needs no cast: `SliceTask<P_IN,P_OUT> parent = getParent()`
        // (AbstractTask.getParent returns K := SliceTask<P_IN,P_OUT> for
        // a SliceTask receiver; strip_selftype_checkcasts already dropped
        // the raw erasure cast). Without this, the fallback below cast to
        // the value's own erasure — `(AbstractTask)` — inconvertible to
        // the target (AbstractTask无法转换为SliceTask<P_IN,P_OUT>, jdk11
        // SliceOps.isLeftCompleted x2 per tree).
        if matches!(value, Expr::Method { .. }) && matches!(want, TypeRef::G(_)) {
            if let Some(inst) = crate::classdec::instantiated_method_ret(value, pool, pc) {
                if TypeRef::G(inst) == *want {
                    return;
                }
            }
        }
        // Erasures must line up (both arrays, or same class name).
        let have = value.type_ref().erased();
        let want_er = want.erased();
        if compatible_erasure(&have, &want_er) {
            // A generic call at a parameterized local whose typevar formal
            // is fed by a WILDCARD-carrying actual cannot unify (S := CAP#1
            // from the arg vs S := ResourceBundleProvider from the target —
            // jdk17 Bundles: the source casts
            // (ServiceLoader<ResourceBundleProvider>) loadInstalled(type);
            // the generics-only cast leaves no checkcast): synthesize the
            // target cast.
            let generic_here = crate::classdec::is_generic_call(value, pool);
            let wild_call_cast = match (&*value, want) {
                (Expr::Method { args, .. }, TypeRef::G(jcdc_jvm::GenericType::Class(wcs)))
                    if generic_here
                        && wcs.parts.iter().any(|p| !p.args.is_empty())
                        && args.iter().any(|a| {
                            matches!(a.type_ref(), TypeRef::G(g)
                                if crate::classdec::g_has_wildcard(&g))
                        }) =>
                {
                    Some(want.clone())
                }
                _ => None,
            };
            if let Some(ty) = wild_call_cast {
                let inner = std::mem::replace(value, Expr::This);
                *value = Expr::Cast { ty, e: Box::new(inner) };
                return;
            }
            // Generic calls infer their type from the assignment target;
            // a frozen cast would sabotage that (and javac emitted none).
            // EXCEPTION — the reflective-array idiom: a getClass() actual
            // pins the callee's array typevar at the ERASURE while the
            // target wants T[] (`a = (T[]) Arrays.copyOfRange(items, ..,
            // a.getClass())` — without the source cast T#1 collects
            // bounds {T, Object}, 推论变量 T#1 具有不兼容的上限, jdk11
            // ArrayBlockingQueue.toArray x2 trees); the cast is the only
            // denotable resolution.
            let reflective_array = matches!(
                want,
                TypeRef::G(jcdc_jvm::GenericType::Array(b))
                    if matches!(b.as_ref(), jcdc_jvm::GenericType::TypeVar(_))
            ) && matches!(value, Expr::Method { args, .. } if args.iter().any(|x| {
                matches!(x, Expr::Method { name, args: ga, .. } if name == "getClass" && ga.is_empty())
            }));
            // A WILDCARD-bearing target over a generic call also needs
            // the cast: the bare assignment lets the call's typevar
            // collect the target's capture as a lower bound against its
            // declared bound (jdk11 SortedOps.OfRef: source `(Comparator
            // <? super T>) Comparator.naturalOrder()` — bare, T#1 gets
            // 上限 Comparable<? super T#1> vs 下限 T#2). Map.ofEntries-style
            // concrete targets keep the bare inference form.
            let wildcard_want = matches!(want, TypeRef::G(jcdc_jvm::GenericType::Class(wcs))
                if wcs.parts.iter().any(|p| p.args.iter().any(|a| {
                    matches!(a, jcdc_jvm::GenericType::Wildcard(_))
                })));
            // A CLASS-LITERAL actual pins the callee's typevar to a
            // concrete class while the target binds the SAME typevar to
            // something else: bare inference collects both equalities and
            // dies (jdk11/17/26 RandomGeneratorFactory.of:
            // `RandomGeneratorFactory<T> f = factoryOf(name,
            // RandomGenerator.class)` — T#1 := T#2 from the target vs
            // T#1 := RandomGenerator from the Class<T#1> formal; the
            // source casts (RandomGeneratorFactory<T>)).
            let class_lit_conflict = generic_here
                && matches!(value, Expr::Method { args, .. } if args.iter().any(|a| {
                    matches!(a, Expr::Const(crate::expr::ConstVal::ClassLit(_)))
                }))
                && crate::classdec::classlit_want_conflict(value, want, pool);
            // Target-driven inference violating a callee bound needs the
            // source's cast (the standalone inference + unchecked hop):
            // jdk26 ReverseOrderSortedSetView `(Comparator<E>)
            // Comparator.naturalOrder()`.
            let bound_conflict = generic_here
                && crate::classdec::target_binding_bound_conflict(value, want, pool, pc);
            if !crate::classdec::is_generic_call(value, pool)
                || reflective_array
                || (wildcard_want && bound_conflict)
                || class_lit_conflict
                || bound_conflict
            {
                let inner = std::mem::replace(value, Expr::This);
                *value = Expr::Cast { ty: want.clone(), e: Box::new(inner) };
            }
            return;
        }
        // Source-level raw cast fallback: a value of one collection type
        // assigned to an unrelated generic collection type came through a
        // raw `(Collection)`-style cast, which leaves no bytecode trace.
        // Re-insert it as a cast to the raw erasure (unchecked but legal).
        if let (JavaType::Object(hn), JavaType::Object(_)) = (&have, &want_er) {
            // A diamond new is only safe to cast when the target is a
            // TYPEVAR (unchecked (T) — the source form of jdk11
            // IdentityHashMap.toArray `a[ti++] = (T) new SimpleEntry<>
            // (unmaskNull(key), tab[si+1])`, elided because T erases to
            // Object): under a CLASS cast a diamond loses its target and
            // infers Object bounds (see Printer.suppress_diamond).
            let valueish = matches!(
                value,
                Expr::Method { .. } | Expr::Local { .. } | Expr::Field { .. } | Expr::ArrayIndex { .. }
            ) || (matches!(value, Expr::New { .. } | Expr::AnonNew { .. })
                && matches!(want, TypeRef::G(jcdc_jvm::GenericType::TypeVar(_))
                    | TypeRef::G(jcdc_jvm::GenericType::Array(_))));
            if valueish && hn != "java/lang/Object" && hn != "java/lang/String" {
                let inner = std::mem::replace(value, Expr::This);
                // A type-var target needs the cast to the VARIABLE: the
                // raw value-erasure cast is not assignable to it
                // ("SpeciesData无法转换为S", jdk26 ClassSpecializer).
                // A parameterized target keeps the RAW value cast — a
                // `(G<args>)` cast of a differently-parameterized value
                // is inconvertible, while the raw form assigns unchecked.
                let cast_ty = if matches!(want, TypeRef::G(jcdc_jvm::GenericType::TypeVar(_))) {
                    want.clone()
                } else {
                    TypeRef::J(have.clone())
                };
                *value = Expr::Cast { ty: cast_ty, e: Box::new(inner) };
            }
        }
    }
    match s {
        Stmt::Block(v) => v.iter_mut().for_each(|x| cast_generic_locals(vt, pool, pc, x)),
        Stmt::LocalDef { var, init: Some(e), .. } => {
            let want = vt.var(*var).ty.clone();
            fix(e, &want, pool, pc);
        }
        Stmt::ExprStmt(Expr::Assign { target, value, .. }) => {
            match &**target {
                Expr::Local { var, .. } => {
                    let want = vt.var(*var).ty.clone();
                    fix(value, &want, pool, pc);
                }
                // `e.next = (Entry<K,V>) x;` — a generic field write whose
                // cast erases away; re-insert against the instantiated
                // field type.
                Expr::Field { owner, cls, name, ty, is_static: false, .. } => {
                    // Fall back to the raw field type for non-generic
                    // fields: an int field assigned a boolean expression
                    // needs the `? 1 : 0` rewrap (jdk26 BigInteger
                    // `this.signum = this.mag.length != 0;`).
                    let want = instantiated_field_type(owner.as_deref(), cls, name, pool, pc)
                        .unwrap_or_else(|| ty.clone());
                    fix(value, &want, pool, pc);
                }
                // `tArr[i] = (T) v;` — the element cast erases away.
                Expr::ArrayIndex { array, .. } => {
                    let aty = match &**array {
                        Expr::Local { var, .. } => vt.var(*var).ty.clone(),
                        other => other.type_ref(),
                    };
                    match &aty {
                        TypeRef::G(jcdc_jvm::GenericType::Array(comp)) => {
                            let want = TypeRef::G((**comp).clone());
                            fix(value, &want, pool, pc);
                        }
                        // Primitive-element stores need the same value
                        // fixups as locals: booleanize folds `b ? 1 : 0`
                        // to `b` and the int element slot needs the
                        // conditional rewrapped (jdk11 Calendar.readObject
                        // `stamp[i] = isSet[i]` — boolean无法转换为int).
                        TypeRef::J(jcdc_jvm::JavaType::Array(elem)) => {
                            let want = TypeRef::J((**elem).clone());
                            fix(value, &want, pool, pc);
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
            let _ = target_ty;
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            cast_generic_locals(vt, pool, pc, then_stmt);
            if let Some(e) = else_stmt {
                cast_generic_locals(vt, pool, pc, e);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => cast_generic_locals(vt, pool, pc, body),
        Stmt::For { init, body, .. } => {
            init.iter_mut().for_each(|i| cast_generic_locals(vt, pool, pc, i));
            cast_generic_locals(vt, pool, pc, body);
        }
        Stmt::ForEach { body, .. } => cast_generic_locals(vt, pool, pc, body),
        Stmt::Try { body, catches, finally } => {
            cast_generic_locals(vt, pool, pc, body);
            for c in catches {
                cast_generic_locals(vt, pool, pc, &mut c.body);
            }
            if let Some(f) = finally {
                cast_generic_locals(vt, pool, pc, f);
            }
        }
        Stmt::TryWithResources { resources, body, catches, finally } => {
            for res in resources.iter_mut() { cast_generic_locals(vt, pool, pc, res); }
            cast_generic_locals(vt, pool, pc, body);
            for c in catches {
                cast_generic_locals(vt, pool, pc, &mut c.body);
            }
            if let Some(f) = finally {
                cast_generic_locals(vt, pool, pc, f);
            }
        }
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                c.body.iter_mut().for_each(|st| cast_generic_locals(vt, pool, pc, st));
            }
            if let Some(d) = default {
                cast_generic_locals(vt, pool, pc, d);
            }
        }
        Stmt::Synchronized { body, .. } | Stmt::Labeled { body, .. } => {
            cast_generic_locals(vt, pool, pc, body)
        }
        _ => {}
    }
}
