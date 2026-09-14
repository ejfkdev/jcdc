//! Local variable allocation: maps bytecode slots (possibly reused across
//! disjoint pc ranges) to named variables.

use jcdc_classfile::{parse_specialized_attribute, CodeAttribute, ParsedAttribute};
use std::collections::HashSet;
use jcdc_jvm::{
    parse_field_descriptor, parse_field_signature, GenericType, JavaType, MethodDescriptor, PoolClass,
};

use crate::expr::TypeRef;

#[derive(Debug, Clone)]
pub struct VarInfo {
    pub id: u32,
    pub slot: u16,
    pub name: String,
    pub ty: TypeRef,
    pub is_param: bool,
    /// pc range where this variable is live (from LVT; method end when open).
    pub range_start: u16,
    pub range_end: u16,
    /// Set when the name was synthesized (no LVT entry).
    pub synthetic_name: bool,
}

#[derive(Debug, Clone, Default)]
pub struct VarTable {
    pub vars: Vec<VarInfo>,
    /// Per slot: (range_start, range_end, var_id), sorted by range_start.
    pub by_slot: Vec<Vec<(u16, u16, u32)>>,
    pub has_lvt: bool,
    /// Synthetic stack-merge variables (need declaration hoisting).
    pub stack_vars: Vec<u32>,
    /// Merge variables whose branches disagreed on type (or carried a
    /// generic/plain-Object value); they must stay Object so every branch
    /// assignment type-checks. Evidence inference may not narrow them.
    pub wide_stack_vars: HashSet<u32>,
    /// Exception-table handler start pcs: an LVT range beginning at one
    /// (or at its astore + 1/2) is a catch parameter binding. Such
    /// ranges never receive forward store attribution — a store just
    /// BEFORE a handler initializes the try-body variable, not the
    /// catch param (jdk11 HostnameChecker.matchDNS: `sni = new
    /// SNIHostName(..)` at pc 8 landed on `iae` whose handler range
    /// starts at 14, within the 8-byte lead-in — SNIHostName无法转换为
    /// IllegalArgumentException).
    pub handler_starts: Vec<u16>,
}

/// Pull the typed Code attribute out of a method, if any.
pub fn code_attribute(pc: &PoolClass, m_idx: usize) -> Option<CodeAttribute> {
    let m = pc.cf.methods.get(m_idx)?;
    m.attributes.iter().find_map(|a| {
        match parse_specialized_attribute(a, &pc.cf.constant_pool) {
            ParsedAttribute::Code(c) => Some(c),
            _ => None,
        }
    })
}

impl VarTable {
    /// Build the variable table for a method.
    pub fn build(
        pc: &PoolClass,
        m_idx: usize,
        desc: &MethodDescriptor,
        is_static: bool,
        max_locals: u16,
        code_len: u16,
    ) -> VarTable {
        let mut vt = VarTable::default();

        // Extract LVT / LVTT from the Code attribute when present.
        // (start, end, name, descriptor, slot)
        let mut lvt: Vec<(u16, u16, String, String, u16)> = Vec::new();
        // (start, end, signature, slot)
        let mut lvtt: Vec<(u16, u16, String, u16)> = Vec::new();
        if let Some(code) = code_attribute(pc, m_idx) {
            for sub in &code.attributes {
                match parse_specialized_attribute(sub, &pc.cf.constant_pool) {
                    ParsedAttribute::LocalVariableTable(t) => {
                        for e in &t.local_variable_table {
                            let name = pc.utf8(e.name_index).unwrap_or("?").to_string();
                            let d = pc.utf8(e.descriptor_index).unwrap_or("I").to_string();
                            let end = e.start_pc.saturating_add(e.length);
                            lvt.push((e.start_pc, end, name, d, e.index));
                        }
                    }
                    ParsedAttribute::LocalVariableTypeTable(t) => {
                        for e in &t.local_variable_type_table {
                            if let Some(sig) = pc.utf8(e.signature_index) {
                                let end = e.start_pc.saturating_add(e.length);
                                lvtt.push((e.start_pc, end, sig.to_string(), e.index));
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        // Merge LVT entries of the same source variable that javac split
        // into multiple ranges (branchy definitions): same slot+name+desc
        // with overlapping or near ranges become one variable.
        {
            // Synthetic exception temporaries (javac names them like `x2`,
            // `e$1`) reuse a slot for genuinely distinct variables, so they
            // only merge when their ranges are adjacent. Ordinary names are
            // the same source variable split into multiple ranges by the
            // compiler (e.g. around try-with-resources scaffolding) and
            // merge when the ranges are near or the gap between them is
            // clean (no foreign occupant, no accesses).
            fn synthetic_name(n: &str) -> bool {
                let b = n.as_bytes();
                b.iter().all(|c| c.is_ascii_alphanumeric() || *c == b'$' || *c == b'_')
                    && b.first().map(|c| *c == b'x' || *c == b'e' || c.is_ascii_digit())
                        .unwrap_or(false)
                    && b.iter().any(|c| c.is_ascii_digit())
            }
            let mut merged: Vec<(u16, u16, String, String, u16)> = Vec::new();
            lvt.sort_by_key(|(s0, _, _, _, sl)| (*sl, *s0));
            let all = lvt.clone();
            let lvtt_ref = &lvtt;
            // Handler start pcs: an LVT range beginning at one is a catch
            // parameter binding — scope-local by nature, never a split
            // live range of an outer variable.
            let handler_starts: Vec<u16> = code_attribute(pc, m_idx)
                .map(|code| code.exception_table.iter().map(|t| t.handler_pc).collect())
                .unwrap_or_default();
            vt.handler_starts = handler_starts.clone();
            // (slot, pc, is_store) for every typed local access, in pc
            // order — used to keep a long-gap merge honest about accesses
            // inside the gap.
            let accesses: Vec<(u16, u16, bool)> = code_attribute(pc, m_idx)
                .map(|code| {
                    use jcdc_classfile::instruction::{decode_all, Opcode};
                    decode_all(&code.code)
                        .into_iter()
                        .filter_map(|ins| {
                            let (slot, is_store) = match ins.op {
                                Opcode::Iinc => (ins.a as u16, true),
                                Opcode::Iload => (ins.a as u16, false),
                                Opcode::Istore => (ins.a as u16, true),
                                Opcode::Iload0 => (0, false),
                                Opcode::Istore0 => (0, true),
                                Opcode::Iload1 => (1, false),
                                Opcode::Istore1 => (1, true),
                                Opcode::Iload2 => (2, false),
                                Opcode::Istore2 => (2, true),
                                Opcode::Iload3 => (3, false),
                                Opcode::Istore3 => (3, true),
                                Opcode::Lload => (ins.a as u16, false),
                                Opcode::Lstore => (ins.a as u16, true),
                                Opcode::Lload0 => (0, false),
                                Opcode::Lstore0 => (0, true),
                                Opcode::Lload1 => (1, false),
                                Opcode::Lstore1 => (1, true),
                                Opcode::Lload2 => (2, false),
                                Opcode::Lstore2 => (2, true),
                                Opcode::Lload3 => (3, false),
                                Opcode::Lstore3 => (3, true),
                                Opcode::Fload => (ins.a as u16, false),
                                Opcode::Fstore => (ins.a as u16, true),
                                Opcode::Fload0 => (0, false),
                                Opcode::Fstore0 => (0, true),
                                Opcode::Fload1 => (1, false),
                                Opcode::Fstore1 => (1, true),
                                Opcode::Fload2 => (2, false),
                                Opcode::Fstore2 => (2, true),
                                Opcode::Fload3 => (3, false),
                                Opcode::Fstore3 => (3, true),
                                Opcode::Dload => (ins.a as u16, false),
                                Opcode::Dstore => (ins.a as u16, true),
                                Opcode::Dload0 => (0, false),
                                Opcode::Dstore0 => (0, true),
                                Opcode::Dload1 => (1, false),
                                Opcode::Dstore1 => (1, true),
                                Opcode::Dload2 => (2, false),
                                Opcode::Dstore2 => (2, true),
                                Opcode::Dload3 => (3, false),
                                Opcode::Dstore3 => (3, true),
                                Opcode::Aload => (ins.a as u16, false),
                                Opcode::Astore => (ins.a as u16, true),
                                Opcode::Aload0 => (0, false),
                                Opcode::Astore0 => (0, true),
                                Opcode::Aload1 => (1, false),
                                Opcode::Astore1 => (1, true),
                                Opcode::Aload2 => (2, false),
                                Opcode::Astore2 => (2, true),
                                Opcode::Aload3 => (3, false),
                                Opcode::Astore3 => (3, true),
                                _ => return None,
                            };
                            Some((slot, ins.pc, is_store))
                        })
                        .collect()
                })
                .unwrap_or_default();
            for e in lvt.drain(..) {
                let same_var = |m: &(u16, u16, String, String, u16)| {
                    if m.4 != e.4 || m.2 != e.2 || m.3 != e.3 {
                        return false;
                    }
                    // Ranges whose generic signatures DIFFER are distinct
                    // source declarations that merely share name+slot
                    // (jdk11 Subject.toString `pI`: Iterator<Principal>
                    // then Iterator<Object> — merging types every later
                    // assignment against the first signature and forces
                    // an inconvertible cast).
                    if let Some(base) = parse_field_descriptor(&e.3) {
                        let sm = sig_type_at(lvtt_ref, m.0, e.4, &base);
                        let se = sig_type_at(lvtt_ref, e.0, e.4, &base);
                        if sm.is_some() && se.is_some() && sm != se {
                            return false;
                        }
                    }
                    if synthetic_name(&e.2) {
                        return e.0 <= m.1 + 16 && m.0 <= e.1 + 16;
                    }
                    let near = m.0 <= e.1 + 16 && e.0 <= m.1 + 16;
                    // Same ordinary name in one slot across a LONG gap:
                    // javac splits a variable's live range around
                    // try-with-resources exception scaffolding (jdk7
                    // Legacy7.twr: r[53..86] and r[129..149] — the gap
                    // holds the close/addSuppressed duplication). Merge
                    // anyway when the gap is CLEAN: no foreign LVT
                    // occupant (checked below) and no bytecode access to
                    // the slot strictly inside the gap. The 8-byte store
                    // lead-in of e's own range is exempt (javac starts
                    // the range just after the storing instruction).
                    // Without the merge the two identities declare the
                    // same name in nested scopes: disambiguation renames
                    // the body decl (r1) and the post-try read binds the
                    // hoisted `= null` twin — twr() returned null.
                    // Catch-parameter ranges (starting at a handler pc or
                    // just after its astore — the LVT range begins where
                    // the binding is live, one or two bytes past the
                    // handler pc) never long-gap merge: same-named catch
                    // params of sibling handlers are DISTINCT variables
                    // (jdk17 UnixUserDefinedFileAttributeView.size: two
                    // `x: UnixException` handlers at 37 and 68 merged
                    // across the int return temp's gap — the bogus
                    // identity's hoisted decl hijacked the int store and
                    // swallowed the catch binding, int↔UnixException x2).
                    // Disjoint ranges whose gap is NOT clean still must
                    // not merge: that fabricates liveness across the gap
                    // and swallows other slot occupants there (jdk11
                    // ResourceBundle.getCandidateLocales: two sibling
                    // `for (String v : variants)` loops merged, and the
                    // string-switch int index living in the gap between
                    // them became `v = -1` on a String).
                    let at_handler = |rs: u16| {
                        handler_starts
                            .iter()
                            .any(|h| rs == *h || rs == h + 1 || rs == h + 2)
                    };
                    let gap_clean = m.1 <= e.0
                        && !at_handler(m.0)
                        && !at_handler(e.0)
                        && !accesses.iter().any(|(sl, apc, _)| {
                            *sl == e.4
                                && *apc > m.1
                                && *apc < e.0
                                && e.0.saturating_sub(*apc) > 8
                        });
                    if !near && !gap_clean {
                        return false;
                    }
                    let lo = m.1.min(e.1);
                    let hi = m.0.max(e.0);
                    !all.iter().any(|o| {
                        o.4 == e.4
                            && (o.2 != e.2 || o.3 != e.3)
                            && o.0 < hi
                            && o.1 > lo
                    })
                };
                if let Some(m) = merged.iter_mut().find(|m| same_var(m)) {
                    m.0 = m.0.min(e.0);
                    m.1 = m.1.max(e.1);
                } else {
                    merged.push(e);
                }
            }
            lvt = merged;
        }
        vt.has_lvt = !lvt.is_empty();

        // Parameters (their LVT entries start at pc 0).
        let mut slot: u16 = 0;
        let mut param_slots: Vec<u16> = Vec::new();
        if !is_static {
            vt.add(slot, "this".into(), JavaType::Object(pc.internal_name.clone()).into(), true, 0, code_len, false);
            param_slots.push(slot);
            slot += 1;
        }
        // MethodParameters attribute names (fallback order: LVT > MP > argN).
        let mp_names: Vec<Option<String>> = {
            let m = &pc.cf.methods[m_idx];
            let mut names = Vec::new();
            for a in &m.attributes {
                if let ParsedAttribute::MethodParameters(mp) = parse_specialized_attribute(a, &pc.cf.constant_pool) {
                    names = mp
                        .parameters
                        .iter()
                        .map(|p| {
                            if p.name_index == 0 {
                                None
                            } else {
                                pc.utf8(p.name_index).map(|s| s.to_string())
                            }
                        })
                        .collect();
                }
            }
            names
        };
        for (i, a) in desc.args.iter().enumerate() {
            let name = lvt
                .iter()
                .find(|(s, _, _, _, sl)| *s == 0 && *sl == slot)
                .map(|(_, _, n, _, _)| n.clone())
                .or_else(|| mp_names.get(i).cloned().flatten())
                .unwrap_or_else(|| format!("arg{}", i));
            let ty = sig_type_at(&lvtt, 0, slot, a).unwrap_or_else(|| TypeRef::J(a.clone()));
            param_slots.push(slot);
            vt.add(slot, name, ty, true, 0, code_len, false);
            slot += a.slot_size() as u16;
        }

        // Remaining LVT entries, sorted by (slot, start).
        lvt.sort_by_key(|(s, _, _, _, sl)| (*sl, *s));
        for (start, end, name, d, s) in &lvt {
            if param_slots.contains(s) && *start == 0 {
                continue;
            }
            let base_ty = parse_field_descriptor(d).unwrap_or(JavaType::Int);
            let ty = sig_type_at(&lvtt, *start, *s, &base_ty).unwrap_or(TypeRef::J(base_ty));
            vt.add(*s, name.clone(), ty, false, *start, (*end).max(*start + 1), false);
        }

        // Accesses that fall in GAPS between LVT ranges (compiler
        // temporaries, e.g. the subject of a pattern-match `instanceof`)
        // must not borrow an unrelated neighbouring variable's name and
        // type: synthesize a per-gap variable instead.
        if let Some(code) = code_attribute(pc, m_idx) {
            use jcdc_classfile::instruction::{decode_all, Opcode};
            let all_ins: Vec<_> = decode_all(&code.code).into_iter().collect();
            // Producer evidence for a reference STORE gap access: the
            // static type of the value being stored, read off the
            // producing instruction (invoke return descriptor, copied
            // slot's LVT type, field descriptor, checkcast class). Gap
            // identities spanning two stores with CONFLICTING evidence
            // are distinct compiler temporaries sharing a reused slot —
            // merging them forces one wrong declared type (com/sun/java/
            // util/jar/pack/Driver main: the fileProps.entrySet()
            // foreach iterator at pc 739 merged with the string-switch
            // dispatch copy of `opt` at pc 965; the merged identity
            // declared String and the iterator's hasNext/next lost
            // their receiver, 找不到符号 x2).
            fn concrete_ev(t: JavaType) -> Option<JavaType> {
                match &t {
                    JavaType::Object(n) if n != "java/lang/Object" => Some(t),
                    JavaType::Array(_) => Some(t),
                    _ => None,
                }
            }
            let mut gaps: Vec<(u16, u16, u16, JavaType, Option<JavaType>)> = Vec::new();
            for (ii, ins) in all_ins.iter().enumerate() {
                let a = ins.a as u16;
                let (slot, ty, is_store) = match ins.op {
                    Opcode::Iinc => (a, JavaType::Int, true),
                    Opcode::Iload => (a, JavaType::Int, false),
                    Opcode::Istore => (a, JavaType::Int, true),
                    Opcode::Iload0 => (0, JavaType::Int, false),
                    Opcode::Istore0 => (0, JavaType::Int, true),
                    Opcode::Iload1 => (1, JavaType::Int, false),
                    Opcode::Istore1 => (1, JavaType::Int, true),
                    Opcode::Iload2 => (2, JavaType::Int, false),
                    Opcode::Istore2 => (2, JavaType::Int, true),
                    Opcode::Iload3 => (3, JavaType::Int, false),
                    Opcode::Istore3 => (3, JavaType::Int, true),
                    Opcode::Lload => (a, JavaType::Long, false),
                    Opcode::Lstore => (a, JavaType::Long, true),
                    Opcode::Lload0 => (0, JavaType::Long, false),
                    Opcode::Lstore0 => (0, JavaType::Long, true),
                    Opcode::Lload1 => (1, JavaType::Long, false),
                    Opcode::Lstore1 => (1, JavaType::Long, true),
                    Opcode::Lload2 => (2, JavaType::Long, false),
                    Opcode::Lstore2 => (2, JavaType::Long, true),
                    Opcode::Lload3 => (3, JavaType::Long, false),
                    Opcode::Lstore3 => (3, JavaType::Long, true),
                    Opcode::Fload => (a, JavaType::Float, false),
                    Opcode::Fstore => (a, JavaType::Float, true),
                    Opcode::Fload0 => (0, JavaType::Float, false),
                    Opcode::Fstore0 => (0, JavaType::Float, true),
                    Opcode::Fload1 => (1, JavaType::Float, false),
                    Opcode::Fstore1 => (1, JavaType::Float, true),
                    Opcode::Fload2 => (2, JavaType::Float, false),
                    Opcode::Fstore2 => (2, JavaType::Float, true),
                    Opcode::Fload3 => (3, JavaType::Float, false),
                    Opcode::Fstore3 => (3, JavaType::Float, true),
                    Opcode::Dload => (a, JavaType::Double, false),
                    Opcode::Dstore => (a, JavaType::Double, true),
                    Opcode::Dload0 => (0, JavaType::Double, false),
                    Opcode::Dstore0 => (0, JavaType::Double, true),
                    Opcode::Dload1 => (1, JavaType::Double, false),
                    Opcode::Dstore1 => (1, JavaType::Double, true),
                    Opcode::Dload2 => (2, JavaType::Double, false),
                    Opcode::Dstore2 => (2, JavaType::Double, true),
                    Opcode::Dload3 => (3, JavaType::Double, false),
                    Opcode::Dstore3 => (3, JavaType::Double, true),
                    Opcode::Aload => (a, JavaType::Object("java/lang/Object".into()), false),
                    Opcode::Astore => (a, JavaType::Object("java/lang/Object".into()), true),
                    Opcode::Aload0 => (0, JavaType::Object("java/lang/Object".into()), false),
                    Opcode::Astore0 => (0, JavaType::Object("java/lang/Object".into()), true),
                    Opcode::Aload1 => (1, JavaType::Object("java/lang/Object".into()), false),
                    Opcode::Astore1 => (1, JavaType::Object("java/lang/Object".into()), true),
                    Opcode::Aload2 => (2, JavaType::Object("java/lang/Object".into()), false),
                    Opcode::Astore2 => (2, JavaType::Object("java/lang/Object".into()), true),
                    Opcode::Aload3 => (3, JavaType::Object("java/lang/Object".into()), false),
                    Opcode::Astore3 => (3, JavaType::Object("java/lang/Object".into()), true),
                    _ => continue,
                };
                let pc0 = ins.pc;
                let covered = vt
                    .by_slot
                    .get(slot as usize)
                    .map(|segs| {
                        segs.iter().any(|(rs, re, _)| {
                            (pc0 >= *rs && pc0 < *re)
                                // javac starts an LVT range just AFTER the
                                // storing instruction, so a nearby STORE
                                // belongs to the next range. A nearby LOAD
                                // does not: it reads a value stored EARLIER
                                // (a return-value temp whose iload sits just
                                // before the next catch param's LVT range,
                                // jdk17 ForkJoinTask.exec `return rex` —
                                // forward attribution turned `return true`
                                // into returning the exception). A range
                                // starting AT a handler is a catch param:
                                // the store before it belongs to the
                                // try-body variable (HostnameChecker sni).
                                || (is_store
                                    && pc0 < *rs
                                    && *rs - pc0 <= 8
                                    && !vt.handler_starts.iter().any(|h| {
                                        *rs == *h || *rs == h + 1 || *rs == h + 2
                                    }))
                        })
                    })
                    .unwrap_or(false);
                if !covered {
                    let ev = if is_store
                        && matches!(
                            ins.op,
                            Opcode::Astore
                                | Opcode::Astore0
                                | Opcode::Astore1
                                | Opcode::Astore2
                                | Opcode::Astore3
                        ) {
                        let prev = if ii > 0 { Some(&all_ins[ii - 1]) } else { None };
                        match prev.map(|p| p.op) {
                            Some(Opcode::Invokevirtual)
                            | Some(Opcode::Invokespecial)
                            | Some(Opcode::Invokestatic)
                            | Some(Opcode::Invokeinterface) => {
                                let p = prev.unwrap();
                                pc.member_ref(p.a as u16)
                                    .and_then(|(_, _, d)| {
                                        jcdc_jvm::parse_method_descriptor(d)
                                    })
                                    .and_then(|md| concrete_ev(md.ret))
                            }
                            Some(Opcode::Aload)
                            | Some(Opcode::Aload0)
                            | Some(Opcode::Aload1)
                            | Some(Opcode::Aload2)
                            | Some(Opcode::Aload3) => {
                                let p = prev.unwrap();
                                let pslot = match p.op {
                                    Opcode::Aload0 => 0u16,
                                    Opcode::Aload1 => 1,
                                    Opcode::Aload2 => 2,
                                    Opcode::Aload3 => 3,
                                    _ => p.a as u16,
                                };
                                vt.at(pslot, pc0)
                                    .map(|id| vt.var(id).ty.erased())
                                    .and_then(concrete_ev)
                            }
                            Some(Opcode::Getfield) | Some(Opcode::Getstatic) => {
                                let p = prev.unwrap();
                                pc.member_ref(p.a as u16)
                                    .and_then(|(_, _, d)| parse_field_descriptor(d))
                                    .and_then(concrete_ev)
                            }
                            Some(Opcode::Checkcast) => {
                                let p = prev.unwrap();
                                pc.class_name(p.a as u16)
                                    .map(|n| JavaType::Object(n.to_string()))
                            }
                            _ => None,
                        }
                    } else {
                        None
                    };
                    // Carry the STATIC access class (primitive vs
                    // reference) so a primitive-typed identity never
                    // adopts reference evidence and vice versa: the
                    // same slot often hosts an int counter temp and a
                    // later reference temp (keytool Main foreach
                    // `length`/index ints merged with the String[]
                    // being iterated — adopting the evidence retyped
                    // `int var = arr.length` to `String[] var = ...`).
                    let ev = match (&ev, &ty) {
                        (None, JavaType::Object(_)) => None,
                        (None, _) => Some(ty.clone()),
                        (Some(_), JavaType::Object(_)) => ev,
                        // primitive store with stray ref evidence: keep primitive
                        (_ev, prim) => Some(prim.clone()),
                    };
                    let ty = match &ev {
                        Some(e) => e.clone(),
                        None => ty,
                    };
                    gaps.push((slot, pc0, pc0.saturating_add(ins.size), ty, ev));
                }
            }
            gaps.sort_by_key(|(sl, p, _, _, _)| (*sl, *p));
            // Gap accesses on the same slot belong to one temporary unless
            // a real LVT range starts between them.
            let seg_starts: Vec<(u16, Vec<u16>)> = vt
                .by_slot
                .iter()
                .enumerate()
                .map(|(sl, segs)| {
                    let mut v: Vec<u16> = segs.iter().map(|(rs, _, _)| *rs).collect();
                    v.sort_unstable();
                    (sl as u16, v)
                })
                .collect();
            let mut merged_gaps: Vec<(u16, u16, u16, JavaType, Option<JavaType>)> = Vec::new();
            for g in gaps {
                if let Some(m) = merged_gaps.last_mut() {
                    if m.0 == g.0 {
                        let starts = seg_starts
                            .iter()
                            .find(|(sl, _)| *sl == g.0)
                            .map(|(_, v)| v.as_slice())
                            .unwrap_or(&[]);
                        let crosses = starts.iter().any(|rs| *rs > m.1 && *rs <= g.1);
                        // Conflicting store evidence = distinct temporaries
                        // on a reused slot: never merge across them.
                        let conflict = match (&m.4, &g.4) {
                            (Some(a), Some(b)) => a != b,
                            _ => false,
                        };
                        if !crosses && !conflict {
                            m.2 = m.2.max(g.2);
                            if m.4.is_none() {
                                if let Some(e) = g.4.clone() {
                                    m.3 = e.clone();
                                    m.4 = Some(e);
                                }
                            }
                            continue;
                        }
                    }
                }
                merged_gaps.push(g);
            }
            for (sl, rs, re, ty, _) in merged_gaps {
                vt.add(
                    sl,
                    format!("var{}_{}", sl, rs),
                    TypeRef::J(ty),
                    false,
                    rs,
                    re.max(rs + 1),
                    true,
                );
            }
        }

        // Slots without any LVT coverage: synthesize one var spanning the method.
        let slots_needed = max_locals.max(slot);
        for s in 0..slots_needed {
            let covered = vt.by_slot.get(s as usize).map(|v| !v.is_empty()).unwrap_or(false);
            if !covered {
                let name = if !is_static && s == 0 { "this".to_string() } else { format!("var{}", s) };
                vt.add(s, name, TypeRef::J(JavaType::Int), !is_static && s == 0, 0, code_len, true);
            }
        }
        for v in vt.by_slot.iter_mut() {
            v.sort_by_key(|(s, _, _)| *s);
        }
        if std::env::var("JCDC_DBG_PVAR").is_ok() {
            for vi in &vt.vars {
                eprintln!("PVAR {} id={} ty={:?} synth={} range=({},{})", vi.name, vi.id, vi.ty, vi.synthetic_name, vi.range_start, vi.range_end);
            }
        }
        vt
    }

    /// Allocate a synthetic stack-merge variable (not backed by a real slot).
    pub fn add_stack_var(&mut self, slot: u16, name: String, ty: TypeRef) -> u32 {
        let id = self.add(slot, name, ty, false, 0, u16::MAX, true);
        self.stack_vars.push(id);
        id
    }

    /// Allocate a synthetic variable that is NOT a stack-merge temp (e.g. a
    /// catch parameter); it must not be hoisted by the stack-var pass.
    /// Add a new variable identity for slot-reuse splitting (post-build;
    /// not registered in pc-range lookups).
    pub fn add_split(&mut self, slot: u16, name: String, ty: TypeRef) -> u32 {
        let id = self.vars.len() as u32;
        self.vars.push(VarInfo {
            id,
            slot,
            name,
            ty,
            is_param: false,
            range_start: 0,
            range_end: u16::MAX,
            synthetic_name: true,
        });
        id
    }

    pub fn add_catch_var(&mut self, slot: u16, name: String, ty: TypeRef) -> u32 {
        self.add(slot, name, ty, false, 0, u16::MAX, true)
    }

    fn add(&mut self, slot: u16, name: String, ty: TypeRef, is_param: bool, rs: u16, re: u16, synth: bool) -> u32 {
        let id = self.vars.len() as u32;
        self.vars.push(VarInfo { id, slot, name, ty, is_param, range_start: rs, range_end: re, synthetic_name: synth });
        while self.by_slot.len() <= slot as usize {
            self.by_slot.push(Vec::new());
        }
        self.by_slot[slot as usize].push((rs, re, id));
        id
    }

    /// Resolve the variable live at (pc, slot). Falls back to the nearest
    /// preceding range, then to any var on the slot.
    pub fn at(&self, slot: u16, pc: u16) -> Option<u32> {
        let segs = self.by_slot.get(slot as usize)?;
        for (rs, re, id) in segs {
            if pc >= *rs && pc < *re {
                return Some(*id);
            }
        }
        // javac often starts an LVT range just AFTER the storing
        // instruction; attribute a nearby access to the next range before
        // falling back to the previous one (keeps slot-reuse splits like
        // `byte[] dst` / `int b` on one slot apart). Never forward-
        // attribute into a catch-param range (starts at a handler pc or
        // its astore+1/+2): the store before a handler initializes the
        // try-body variable (jdk11 HostnameChecker.matchDNS `sni = new
        // SNIHostName(..)` was typed IllegalArgumentException).
        for (rs, _, id) in segs {
            if *rs > pc
                && *rs - pc <= 8
                && !self.handler_starts.iter().any(|h| {
                    *rs == *h || *rs == h + 1 || *rs == h + 2
                })
            {
                return Some(*id);
            }
        }
        let mut best: Option<u32> = None;
        for (rs, _, id) in segs {
            if *rs <= pc {
                best = Some(*id);
            }
        }
        best.or_else(|| segs.first().map(|(_, _, id)| *id))
    }

    /// The single variable covering a slot (when the slot is not reused).
    pub fn sole_on_slot(&self, slot: u16) -> Option<u32> {
        let segs = self.by_slot.get(slot as usize)?;
        if segs.len() == 1 {
            Some(segs[0].2)
        } else {
            None
        }
    }

    pub fn vars_on_slot(&self, slot: u16) -> &[(u16, u16, u32)] {
        self.by_slot.get(slot as usize).map(|v| v.as_slice()).unwrap_or(&[])
    }

    pub fn var(&self, id: u32) -> &VarInfo {
        static DUMMY: std::sync::OnceLock<VarInfo> = std::sync::OnceLock::new();
        self.vars.get(id as usize).unwrap_or_else(|| {
            DUMMY.get_or_init(|| VarInfo {
                id,
                slot: u16::MAX,
                name: format!("var{}", id),
                ty: TypeRef::J(jcdc_jvm::JavaType::Int),
                is_param: false,
                range_start: 0,
                range_end: 0,
                synthetic_name: true,
            })
        })
    }

    pub fn var_mut(&mut self, id: u32) -> &mut VarInfo {
        &mut self.vars[id as usize]
    }
}

fn sig_type_at(
    lvtt: &[(u16, u16, String, u16)],
    start: u16,
    slot: u16,
    base: &JavaType,
) -> Option<TypeRef> {
    lvtt
        .iter()
        .find(|(s, _, _, sl)| *s == start && *sl == slot)
        .and_then(|(_, _, sig, _)| parse_field_signature(sig).map(TypeRef::G))
        // Reject signatures that cannot describe the descriptor type (a
        // merged LVT range can accidentally align with an unrelated
        // generic entry, e.g. a type variable E over a concrete class).
        .filter(|tr| sig_matches_base(tr, base))
}

fn sig_matches_base(tr: &TypeRef, base: &JavaType) -> bool {
    let g = match tr {
        TypeRef::G(g) => g,
        TypeRef::J(_) => return true,
    };
    match g {
        // A type variable erases to its bound (Object or a concrete
        // class), so any reference descriptor is compatible.
        jcdc_jvm::GenericType::TypeVar(_) => matches!(base, JavaType::Object(_)),
        jcdc_jvm::GenericType::Class(cs) => {
            matches!(base, JavaType::Object(n) if *n == cs.internal_name())
        }
        jcdc_jvm::GenericType::Primitive(c) => base.primitive_char() == Some(*c),
        jcdc_jvm::GenericType::Array(_) => matches!(base, JavaType::Array(_)),
        jcdc_jvm::GenericType::Wildcard(_) => false,
    }
}

/// Placeholder type used when the builder cannot infer a better one.
pub fn unknown_ref_type() -> TypeRef {
    TypeRef::G(GenericType::Class(jcdc_jvm::ClassSig {
        package: "java/lang".into(),
        parts: vec![jcdc_jvm::ClassSigPart { name: "Object".into(), args: vec![] }],
    }))
}
