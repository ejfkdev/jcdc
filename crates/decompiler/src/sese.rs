//! From-scratch SESE / dominator-tree control-flow structurer.
//!
//! Replaces the heuristic `walk` with a monotone region decomposition:
//! * follows are TRUE immediate post-dominators (computed once per method via a
//!   sentinel-virtual-exit reverse CHK), fixing the compound-condition
//!   `if (A || B) then; tail` mis-follow at the root;
//! * every block is structured EXACTLY ONCE — guarded by a `consumed` set and a
//!   "reached-from-this-region's-entry" check. A branch that runs into an
//!   already-consumed block, or into a block it does not reach (a shared merge
//!   owned by a sibling/follow), emits `Goto{block}` instead of re-walking it.
//!   There is NO fresh-claimed shared-tail copy, so the decomposition cannot
//!   diverge (the failure mode of every incremental patch on `walk`).
//!
//! Gated behind `JCDC_SESE`; `structure_method` falls back to `walk` when unset.
//! Milestone 1: straight-line, Cond (if/else + value-diamond/ternary), natural
//! loops. Switch/Try reuse the existing (pub(crate)) region builders next.

use std::collections::{HashMap, HashSet};

use crate::builder::Term;
use crate::expr::Expr;
use crate::stmt::Stmt;

use crate::structure::{
    compute_dominators, compute_postdominators, reachable_within, DomInfo,
    Region, Structurer,
};

/// Per-method precomputation for the SESE decomposition.
thread_local! {
    /// Set when a matexit splice committed in the current method; read by
    /// decompile_method's post-pipeline pathology retry.
    pub static MATEXIT_FIRED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// Method-local kill switch for the retry pass.
    pub static MATEXIT_DISABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

struct SeseCtx {
    universe: HashSet<usize>,
    idom: DomInfo,
    /// block -> immediate post-dominator (== vx when only the virtual exit).
    ipdom: HashMap<usize, usize>,
    /// sentinel virtual-exit id.
    vx: usize,
    /// loop headers (back-edge targets that dominate the source).
    loop_headers: HashSet<usize>,
    /// loop headers whose back edge is EXCEPTION-mediated (the retry jump
    /// originates in handler flow, invisible to normal dominance at the
    /// group-yield check).
    exc_retry_headers: HashSet<usize>,
    /// header -> natural-loop member set.
    loop_members: HashMap<usize, HashSet<usize>>,
    /// blocks consumed (structured exactly once) across the whole method.
    consumed: HashSet<usize>,
    /// loop headers currently being structured (a back-edge to one is a
    /// `continue`, never a copy_walk target).
    loop_stack: Vec<usize>,
    /// Outermost try groups (mirrors walk's `top_groups`): the `active`
    /// candidate list threaded into walk-based sub-builders so a try group
    /// that STARTS inside a switch case or a copied tail still fires there
    /// (URL$DefaultFactory.createURLStreamHandler: the reflection try lives
    /// entirely inside the stage-2 switch default case; with active=[] the
    /// case walk structured it bare and the catch was orphaned -> unreported
    /// checked exceptions, a jdk11/17 corpus blocker).
    top_groups: Vec<usize>,
    /// recursion depth (safety bound).
    depth: usize,
}

impl<'a> Structurer<'a> {
    /// Structure the whole method via SESE decomposition.
    /// Catch-and-retry header detection shared by both structurizers.
    /// A catch-and-retry handler has NO normal-flow preds, so the
    /// dominator tree roots it and its `goto header` back edge is
    /// invisible to natural-loop detection. Returns the per-header
    /// handler-flow back-edge sources and (as a side effect) marks the
    /// headers in `loop_headers` and `self.sese_exc_retry_headers`.
    /// The WALK structurer consumes sese_exc_retry_headers (its
    /// loop-structuring branch + single_enclosing_succ) — in walk-only
    /// mode it was never computed, so exc-mediated retry loops unrolled
    /// into nested try copies (jdk11/17 ObjectInputStream.auditSubclass
    /// lost the retry loop and its tail return — 缺少返回语句 x2 trees;
    /// SESE rendered it correctly).
    pub(crate) fn precompute_exc_retry(
        &mut self,
        universe: &HashSet<usize>,
        idom: &crate::structure::DomInfo,
        loop_headers: &mut HashSet<usize>,
    ) -> HashMap<usize, Vec<usize>> {
        let mut exc_back_sources: HashMap<usize, Vec<usize>> = HashMap::new();
        let mut exc_retry_only: HashSet<usize> = HashSet::new();
        for e in &self.cfg.exc_edges {
            if !(universe.contains(&e.from) && universe.contains(&e.to)) {
                continue;
            }
            let c = e.to;
            if !self.cfg.blocks[c].pred.is_empty() {
                continue; // normally reachable: real dominators apply
            }
            // Handler-flow closure: blocks whose normal preds all stay
            // within the handler flow. The retry back edge may originate
            // deeper than the handler entry (`catch { if (rem > 0)
            // sleep(..); rem = ..; if (rem > 0) goto head; }` — jdk11
            // Process.waitFor: the back edge sits at the while-test two
            // hops down; the direct-succ scan missed it, the retry loop
            // never structured, and the back-edge arrival copy_walked the
            // try head into 5 nested duplicate tries with the final
            // `return false` lost — 缺少返回语句). Blocks with a normal pred
            // from OUTSIDE the handler flow (shared merges) stop the
            // closure; they belong to the enclosing flow.
            let mut hf: HashSet<usize> = HashSet::new();
            hf.insert(c);
            {
                let mut q: std::collections::VecDeque<usize> = std::collections::VecDeque::new();
                q.push_back(c);
                while let Some(b) = q.pop_front() {
                    for &s in &self.cfg.blocks[b].succ {
                        if hf.contains(&s)
                            || !universe.contains(&s)
                            || self.handler_group.contains_key(&s)
                        {
                            continue;
                        }
                        if self.cfg.blocks[s]
                            .pred
                            .iter()
                            .all(|p| hf.contains(p) || self.handler_group.contains_key(p))
                        {
                            hf.insert(s);
                            q.push_back(s);
                        }
                    }
                }
            }
            for &b in hf.iter() {
                for &h in &self.cfg.blocks[b].succ {
                    if hf.contains(&h) {
                        continue;
                    }
                    if universe.contains(&h) && idom.dominates(h, e.from) {
                        loop_headers.insert(h);
                        exc_retry_only.insert(h);
                        let srcs = exc_back_sources.entry(h).or_default();
                        for &m in hf.iter() {
                            if !srcs.contains(&m) {
                                srcs.push(m);
                            }
                        }
                    }
                }
            }
        }
        if std::env::var("JCDC_DBG_IF").is_ok() && !exc_retry_only.is_empty() {
            let mut v: Vec<usize> = exc_retry_only.iter().copied().collect();
            v.sort_unstable();
            eprintln!("EXCRETRY headers={:?}", v);
        }
        self.sese_exc_retry_headers = exc_retry_only;
        exc_back_sources
    }

    pub fn structure_method_sese(&mut self) -> Region {
        let universe: HashSet<usize> = self
            .cfg
            .blocks
            .iter()
            .filter(|b| !b.ins.is_empty())
            .map(|b| b.id)
            .collect();
        let idom = compute_dominators(self.cfg, &universe, self.cfg.entry);
        let (vx, ipdom) = compute_postdominators(self.cfg, &universe);

        // Natural loops from back edges (h dominates u => u->h is a back edge).
        let mut loop_headers: HashSet<usize> = HashSet::new();
        for &u in universe.iter() {
            for &s in &self.cfg.blocks[u].succ {
                if universe.contains(&s) && s != u && idom.dominates(s, u) {
                    loop_headers.insert(s);
                }
                if s == u {
                    loop_headers.insert(u); // self loop
                }
            }
        }
        let exc_back_sources = self.precompute_exc_retry(&universe, &idom, &mut loop_headers);
        // Exception-edge predecessors: handler -> protected blocks. A protected
        // block reaches its handler only on a throw (an exception edge, not a
        // normal pred), so when the handler loops back to the header, the
        // protected block is part of the loop too. Without this, a
        // `while(..){ try{ return }catch{ ..loop.. } }` drops the try out of
        // the loop (the SecureRandom.getInstanceStrong regression).
        let mut exc_preds: HashMap<usize, Vec<usize>> = HashMap::new();
        for e in &self.cfg.exc_edges {
            if universe.contains(&e.from) && universe.contains(&e.to) {
                exc_preds.entry(e.to).or_default().push(e.from);
            }
        }
        let mut loop_members: HashMap<usize, HashSet<usize>> = HashMap::new();
        for &h in loop_headers.iter() {
            let mut members: HashSet<usize> = HashSet::new();
            members.insert(h);
            // Collect every TRUE back-edge source for h (u -> h where h
            // dominates u; without the dominance check a forward entry edge
            // like a pre-loop init guard -> header pollutes the member set
            // and the whole enclosing chain gets swallowed, Integer blk10),
            // then walk predecessors (normal AND exception) within the
            // universe until reaching h.
            let mut stack: Vec<usize> = Vec::new();
            for &u in universe.iter() {
                let is_self_loop = u == h && self.cfg.blocks[h].succ.contains(&h);
                let is_back_edge = u != h && idom.dominates(h, u);
                if self.cfg.blocks[u].succ.contains(&h) && (is_self_loop || is_back_edge) {
                    if members.insert(u) {
                        stack.push(u);
                    }
                }
            }
            if let Some(srcs) = exc_back_sources.get(&h) {
                for &c in srcs {
                    if members.insert(c) {
                        stack.push(c);
                    }
                }
            }
            while let Some(b) = stack.pop() {
                // Do NOT traverse the header's own predecessors: the natural
                // loop is {h} u {nodes reaching a back-edge source without
                // going through h}. Walking h's preds would pull in the
                // pre-loop code (entry, guards) and duplicate it inside the
                // body region.
                if b == h {
                    continue;
                }
                for &p in &self.cfg.blocks[b].pred {
                    if universe.contains(&p) && members.insert(p) {
                        stack.push(p);
                    }
                }
                if let Some(xp) = exc_preds.get(&b) {
                    for &p in xp {
                        if members.insert(p) {
                            stack.push(p);
                        }
                    }
                }
            }
            loop_members.insert(h, members);
        }

        let top_groups: Vec<usize> = (0..self.groups.len())
            .filter(|gi| {
                let g = &self.groups[*gi];
                !self.groups.iter().enumerate().any(|(oj, og)| {
                    oj != *gi
                        && og.start <= g.start
                        && og.end >= g.end
                        && (og.start != g.start || og.end != g.end)
                })
            })
            .collect();
        self.sese_loop_headers = loop_headers.clone();
        let mut ctx = SeseCtx {
            universe,
            idom,
            ipdom,
            vx,
            exc_retry_headers: exc_back_sources.keys().copied().collect(),
            loop_headers,
            loop_members,
            consumed: HashSet::new(),
            loop_stack: Vec::new(),
            top_groups,
            depth: 0,
        };
        let r = self.sese_region(self.cfg.entry, &HashSet::new(), &mut ctx);
        r
    }

    /// Immediate post-dominator of `b` (None if only the virtual exit, i.e. all
    /// paths from b leave the universe / return / throw).
    fn sese_ipdom(&self, ctx: &SeseCtx, b: usize) -> Option<usize> {
        match ctx.ipdom.get(&b).copied() {
            Some(p) if p != ctx.vx && p != b => Some(p),
            _ => None,
        }
    }

    /// Convergent merge of a set of branch/case targets within a region: the
    /// nearest block (by linear layout) forward-reachable from ALL targets,
    /// not in `stop`, and not yet consumed. This recovers a shared
    /// continuation that is NOT a post-dominator because the targets diverge
    /// to different terminals (a loop `break` -> exit, a `return`/`throw`, or
    /// a loop tail -> header back-edge that only post-dominates at the virtual
    /// exit). Examples: the loop tail after `if (a==2 && b==2) break outer;`
    /// (Legacy6), and the shared `++i` tail after every `case` of a switch
    /// inside a loop (EnumSwitch — without it the first case swallows the tail
    /// as `++i; continue` and the remaining cases spin forever).
    fn convergent_merge(
        &self,
        ctx: &SeseCtx,
        targets: &[usize],
        stop: &HashSet<usize>,
    ) -> Option<usize> {
        if targets.is_empty() {
            return None;
        }
        // Floor = the branch block's own position, NOT max(target starts): a
        // branch target may sit EARLIER in the layout than the branch (a
        // backward jump to a fixup, Integer.toString C1 -> FIXUP), and a
        // max-of-targets floor then hides the true nearest confluence and
        // lets a far block inside the branch body be chosen as follow.
        let floor = targets
            .iter()
            .filter_map(|&t| self.cfg.blocks[t].pred.iter().map(|&p| self.cfg.blocks[p].start as usize).max())
            .max()
            .unwrap_or(0);
        // Multi-block condition chains (`while (c1 || c2) body;` compiled as
        // H1: if c1 goto BODY; H2: if c2 goto BODY; else EXIT; BODY: ..; goto
        // H1): the confluence of H1's branches is the NEXT TEST block, which
        // is itself one of the targets. Prefer it before the general scan —
        // the dominance guards below would (correctly in general) reject it,
        // but here the sibling target IS the chain continuation; picking it
        // flattens the body to `if (c1) continue; if (c2) continue; else
        // exit;`, the shape extract_compound_do_while / the CLASSIFY2 fold
        // consume (jdk8 Random.internalNextInt). Legacy6 is unaffected: its
        // fall target (the tail) is reachable from the sibling, so the
        // sibling is not a confluence there.
        for &t in targets.iter() {
            if stop.contains(&t)
                || ctx.consumed.contains(&t)
                || ctx.loop_stack.contains(&t)
            {
                if std::env::var("JCDC_DBG_LM").is_ok() {
                    eprintln!("CM-SKIP t={} stop={} consumed={} lstack={} targets={:?}", t,
                        stop.contains(&t), ctx.consumed.contains(&t), ctx.loop_stack.contains(&t), targets);
                }
                continue;
            }
            if targets
                .iter()
                .all(|&o| o == t || self.reaches_within(ctx, o, t, stop))
            {
                if std::env::var("JCDC_DBG_LM").is_ok() {
                    eprintln!("CM-RET {} targets={:?}", t, targets);
                }
                return Some(t);
            }
        }
        let mut best: Option<usize> = None;
        let mut best_start = usize::MAX;
        for &x in ctx.universe.iter() {
            let xs = self.cfg.blocks[x].start as usize;
            if xs < floor || xs >= best_start {
                continue;
            }
            if stop.contains(&x) || ctx.consumed.contains(&x) {
                continue;
            }
            // A loop header is never a merge candidate WHILE INSIDE its
            // loop: a branch that jumps to it is a `continue` (the back
            // edge fires on the NEXT iteration), not a fall-through
            // confluence. During a body walk the header sits on the
            // loop_stack, so this guard keeps StringUTF16.codePointCount's
            // `continue`s. OUTSIDE the loop (switch cases that all
            // `goto` a loop head laid out after the switch — jdk11
            // Subject.populateSet) the header IS the switch follow: the
            // cases break into it and the loop structures ONCE after the
            // switch instead of being copy-duplicated into every case.
            if ctx.loop_stack.contains(&x) {
                continue;
            }
            // A candidate that DOMINATES ANY branch target (reflexively: is
            // a target) is an ancestor
            // confluence (a fixup block the branches jump back/up to, e.g.
            // `if (A || B) radix = 10;` where the fixup dominates the cond),
            // not a follow: choosing it empties a branch and loses the
            // post-fixup continuation (Integer.toString). Such shapes need
            // follow=None so the branches are walked naturally and the
            // re-reached continuation is duplicated by copy_walk (walk
            // parity). Genuine shared tails (Legacy6/EnumSwitch) are
            // dominated BY their targets, never dominate them.
            if targets.iter().any(|&t| t != x && ctx.idom.dominates(x, t)) {
                continue;
            }
            // ... and reject a candidate that IS a branch target while
            // ANOTHER target sits strictly above it in the dominator tree
            // (`if (A || B) fixup; main;` — fixup dominates main): choosing
            // the lower target as follow empties the jump branch and orphans
            // the fixup (Integer.toString C2 -> empty `if (radix <= 36)`).
            // A genuine shared tail (Legacy6) is dominated BY its sibling
            // branch, not the other way around, so it survives both guards.
            if targets.contains(&x)
                && targets
                    .iter()
                    .any(|&t| t != x && ctx.idom.dominates(t, x))
            {
                continue;
            }
            if targets.iter().all(|&t| self.reaches_within(ctx, t, x, stop)) {
                best = Some(x);
                best_start = xs;
            }
        }
        best
    }

    /// Can `from` reach `target` stepping only through blocks not in `stop`
    /// (target itself may be in `stop` — it is the destination), AND without
    /// re-entering an enclosing loop? Reaching a loop header on `loop_stack`
    /// is a back-edge (loop re-entry): anything past it is a *later iteration*,
    /// not a forward merge. Restricting to forward reach is what lets
    /// convergent_merge recover a shared loop tail (Legacy6: B2 -> TAIL is a
    /// forward edge) while refusing to invent a follow across a `continue`
    /// (ControlFlow.nestedLoops: the `++j;continue` block only reaches `++c`
    /// via the header back-edge, so `++c` is correctly NOT a merge).
    /// Nearest block (by start) that every NON-TERMINATING successor
    /// reaches within `stop` — unlike convergent_merge this MAY return a
    /// stop member: a switch/if inside a loop body whose branches break
    /// to the loop increment (a body_stop exit) still has a well-defined
    /// merge; refusing it strands breaks as RawGotos and drops shared
    /// tails (ObjectStreamClass.computeFieldOffsets, Long$LongCache
    /// clinit). Cm's dominance guards still apply: a candidate that
    /// (properly) dominates a live target is an ancestor confluence
    /// (Integer.toString fixup), not a follow.
    fn live_merge(
        &self,
        ctx: &SeseCtx,
        succs: &[usize],
        stop: &HashSet<usize>,
    ) -> Option<usize> {
        let live: Vec<usize> = succs
            .iter()
            .copied()
            .filter(|&t| !matches!(self.results[t].term, Term::Return(_) | Term::Throw(_)))
            .collect();
        // Require 2+ live branches: a single live target trivially
        // "merges with itself" — for a loop condition that makes the
        // body entry the follow, emptying the else branch and degrading
        // ControlFlow.breakInLoop's `return i` to `break`. One-live
        // shapes must keep follow=None so branches structure naturally.
        if live.len() < 2 {
            return None;
        }
        // A branch target that every live branch flows to IS the merge
        // (the sibling completes normally into it and the branch is an
        // empty fallthrough) — prefer it even when it is a shared
        // terminator; scanning by nearest-start would otherwise pick a
        // non-target confluence and strand the tail (Fin/Long$LongCache:
        // `cache = archivedCache; return` must be the follow, not a
        // branch-body copy with the top-level tail lost). ONLY with 2+
        // live targets: a loop condition (one live body entry, one exit
        // branch) must keep follow=None so both branches structure
        // naturally — otherwise the body entry becomes the "follow", the
        // else branch empties, and ControlFlow.breakInLoop's `return i`
        // degrades to `break`.
        if live.len() >= 2 {
            for &t in succs.iter() {
                if stop.contains(&t) {
                    if std::env::var("JCDC_DBG_LM").is_ok() {
                        eprintln!("LM-SKIP t={} stop succs={:?}", t, succs);
                    }
                    continue;
                }
                if ctx.consumed.contains(&t) {
                    if std::env::var("JCDC_DBG_LM").is_ok() {
                        eprintln!("LM-SKIP t={} consumed succs={:?}", t, succs);
                    }
                    continue;
                }
                if live
                    .iter()
                    .all(|&o| o == t || self.reaches_within(ctx, o, t, stop))
                {
                    if std::env::var("JCDC_DBG_LM").is_ok() {
                        eprintln!("LM-RET {} succs={:?} live={:?}", t, succs, live);
                    }
                    return Some(t);
                }
            }
        }
        let mut best: Option<usize> = None;
        for &cand in ctx.universe.iter() {
            if ctx.consumed.contains(&cand) || ctx.loop_stack.contains(&cand) {
                continue;
            }
            // (Shared terminators ARE eligible here: a branch merging at
            // a return block is a normal follow — Long$LongCache's tail.
            // The escape filter downstream in the follow chain rejects
            // the cases where a branch jumps OUT instead, jdk17 String.)
            if live.iter().any(|&t| t != cand && ctx.idom.dominates(cand, t)) {
                continue;
            }
            if live.contains(&cand)
                && live.iter().any(|&t| t != cand && ctx.idom.dominates(t, cand))
            {
                continue;
            }
            if live
                .iter()
                .all(|&t| t == cand || self.reaches_within(ctx, t, cand, stop))
            {
                match best {
                    None => best = Some(cand),
                    Some(b) if self.cfg.blocks[cand].start < self.cfg.blocks[b].start => {
                        best = Some(cand)
                    }
                    _ => {}
                }
            }
        }
        best
    }

    /// True when `cur` (a stop member) flows through single-successor
    /// blocks to an already-consumed terminator: the chain is safe to
    /// copy here because its endpoint was structured elsewhere and the
    /// copy is this path's sole continuation.
    fn sese_stop_chain_to_claimed_terminator(
        &self,
        cur: usize,
        stop: &HashSet<usize>,
        ctx: &SeseCtx,
    ) -> bool {
        let mut x = cur;
        for _ in 0..8 {
            if matches!(self.results[x].term, Term::Return(_) | Term::Throw(_)) {
                // Statement-bearing claimed terminators are the post-loop
                // continuation tail (shared clinit tails get claimed by the
                // first arrival), NOT absorbed restart-loop scaffolding —
                // copying them into the exit test duplicates blank-final
                // assignments inside the loop (SecurityProviderConstants
                // 可能在 loop 中分配了变量 x18). See the walk-side twin.
                return ctx.consumed.contains(&x) && self.results[x].stmts.is_empty();
            }
            if !matches!(self.results[x].term, Term::Fallthrough | Term::Goto) {
                return false;
            }
            if !self.results[x].stmts.is_empty() && !ctx.consumed.contains(&x) {
                return false;
            }
            let succs = &self.cfg.blocks[x].succ;
            if succs.len() != 1 {
                return false;
            }
            let n = succs[0];
            if n == x || ctx.loop_stack.contains(&n) {
                return false;
            }
            let _ = stop;
            x = n;
        }
        false
    }

    /// Loop-tail switch follow recovery. A switch inside a loop whose cases
    /// either `break` the SWITCH into a shared epilogue that flows back to
    /// the header, exit the LOOP (stop), `continue` (header), or terminate:
    /// ipdom post-dominates only at the virtual exit and the forward-merge
    /// resolvers refuse header-reaching paths, so follow=None — the epilogue
    /// is consumed by the first case walk that arrives, sibling cases lose
    /// their `break`, and the post-loop continuation is stranded (jdk26
    /// Pattern.sequence/expr: lost `node = closure(node)` epilogue and
    /// post-loop `if (head == null) return end; root = tail; return head;`
    /// → 缺少返回语句). E is the nearest block every case target SETTLES at:
    /// each path from each target reaches E forward (no stop/header steps),
    /// escapes to a stop (outer break), continues into an enclosing loop
    /// header, or terminates (return/throw).
    fn loop_tail_switch_follow(
        &self,
        ctx: &SeseCtx,
        cur: usize,
        stop: &HashSet<usize>,
    ) -> Option<usize> {
        if ctx.loop_stack.is_empty() {
            return None;
        }
        let targets: Vec<usize> = self.cfg.blocks[cur].succ.clone();
        if targets.is_empty() {
            return None;
        }
        // Candidates: the DESTINATIONS of case-terminal transfers only —
        // each case region's trailing `goto X` targets and fallthrough
        // successors whose source block has multiple in-region succ paths
        // (a full forward closure would offer every case-internal block,
        // and a private `continue` stub settling on all paths could win
        // the start-pc contest: Pattern.sequence case 40's `goto 4` block).
        let mut cands: Vec<usize> = Vec::new();
        {
            let mut seen: HashSet<usize> = HashSet::new();
            let mut stack: Vec<usize> = targets.clone();
            let mut visited: HashSet<usize> = HashSet::new();
            while let Some(b) = stack.pop() {
                if stop.contains(&b) || ctx.loop_stack.contains(&b) || !visited.insert(b) {
                    continue;
                }
                let succs = &self.cfg.blocks[b].succ;
                match self.results[b].term {
                    crate::builder::Term::Goto => {
                        // A case-terminal jump: its destination is a
                        // break/continue/epilogue candidate.
                        if let Some(&t) = succs.first() {
                            if !targets.contains(&t)
                                && !ctx.loop_stack.contains(&t)
                                && !stop.contains(&t)
                                && seen.insert(t)
                            {
                                cands.push(t);
                            }
                        }
                    }
                    crate::builder::Term::Fallthrough => {
                        if let Some(&t) = succs.first() {
                            // Fallthrough into a block with preds from
                            // ELSEWHERE in the switch (a shared epilogue
                            // head): candidate. Purely linear flow keeps
                            // walking (the case's own body).
                            let shared = self.cfg.blocks[t].pred.iter().any(|&p| {
                                p != b && (targets.contains(&p) || visited.contains(&p))
                            });
                            if shared
                                && !targets.contains(&t)
                                && !ctx.loop_stack.contains(&t)
                                && !stop.contains(&t)
                                && seen.insert(t)
                            {
                                cands.push(t);
                            }
                            stack.push(t);
                        }
                    }
                    crate::builder::Term::Cond { .. } | crate::builder::Term::Switch { .. } => {
                        stack.extend(succs.iter().copied());
                    }
                    // A case body can END in straight-line fallthrough into
                    // the shared epilogue (Pattern.sequence case 92 flows
                    // into the `node = closure(node)` tail): keep walking
                    // non-branching blocks so its destination surfaces.
                    _ if succs.len() == 1 && !matches!(self.results[b].term,
                        crate::builder::Term::Return(_) | crate::builder::Term::Throw(_)) => {
                        stack.extend(succs.iter().copied());
                    }
                    // Return/Throw: no continuation candidate.
                    _ => {}
                }
            }
        }
        let mut best: Option<usize> = None;
        let mut best_score: Option<(usize, u16)> = None;
        for &e in &cands {
            if stop.contains(&e) || ctx.consumed.contains(&e) {
                continue;
            }
            // E must flow back to an enclosing loop header (it IS the loop
            // tail) — otherwise the switch-break confluence is a plain
            // post-switch block the forward resolvers would have found.
            let mut to_header = false;
            {
                let mut seen: HashSet<usize> = HashSet::new();
                let mut stack: Vec<usize> = vec![e];
                while let Some(b) = stack.pop() {
                    if !seen.insert(b) {
                        continue;
                    }
                    for &s in &self.cfg.blocks[b].succ {
                        if ctx.loop_stack.contains(&s) {
                            to_header = true;
                            break;
                        }
                        if !stop.contains(&s) {
                            stack.push(s);
                        }
                    }
                    if to_header {
                        break;
                    }
                }
            }
            if !to_header {
                continue;
            }
            if targets
                .iter()
                .all(|&t| self.settles_at(ctx, stop, t, e, 0))
            {
                // Score = how many DISTINCT case targets reach `e` forward:
                // the switch-break confluence collects every breaking case,
                // while a case-private merge/continue stub is reached only
                // by its own case (Pattern.sequence b7 [case 40's
                // `tail = root; goto EPI`] vs the true epilogue EPI which
                // all eight breaking cases flow into). Ties: nearest by
                // start pc (the epilogue's own head block).
                let score = targets
                    .iter()
                    .filter(|&&t| self.reaches_fwd(ctx, stop, t, e, 0))
                    .count();
                best = match best_score {
                    None => {
                        best_score = Some((score, self.cfg.blocks[e].start));
                        Some(e)
                    }
                    Some((bs, bstart)) => {
                        let better = score > bs
                            || (score == bs && self.cfg.blocks[e].start < bstart);
                        if better {
                            best_score = Some((score, self.cfg.blocks[e].start));
                            Some(e)
                        } else {
                            best
                        }
                    }
                };
            }
        }
        best
    }

    /// Some forward path from `t` reaches `e` without stepping on stop
    /// members or enclosing loop headers.
    fn reaches_fwd(
        &self,
        ctx: &SeseCtx,
        stop: &HashSet<usize>,
        t: usize,
        e: usize,
        depth: usize,
    ) -> bool {
        if depth > 4096 {
            return false;
        }
        if t == e {
            return true;
        }
        if stop.contains(&t) || ctx.loop_stack.contains(&t) {
            return false;
        }
        self.cfg.blocks[t]
            .succ
            .iter()
            .any(|&s| self.reaches_fwd(ctx, stop, s, e, depth + 1))
    }

    /// Every path from `t` settles at `e`: reaches it forward, escapes to a
    /// stop (outer break), continues into an enclosing loop header, or
    /// terminates (return/throw). See `loop_tail_switch_follow`.
    fn settles_at(
        &self,
        ctx: &SeseCtx,
        stop: &HashSet<usize>,
        t: usize,
        e: usize,
        depth: usize,
    ) -> bool {
        if depth > 4096 {
            return false;
        }
        if t == e {
            return true;
        }
        if stop.contains(&t) || ctx.loop_stack.contains(&t) {
            return true; // outer break / continue: structured elsewhere
        }
        let succs = &self.cfg.blocks[t].succ;
        if succs.is_empty() {
            return matches!(
                self.results[t].term,
                crate::builder::Term::Return(_) | crate::builder::Term::Throw(_)
            );
        }
        succs.iter().all(|&s| self.settles_at(ctx, stop, s, e, depth + 1))
    }

    /// Stronger sibling check for a branch-target follow candidate: EVERY
    /// bounded route from `from` passes through `target` or leaves abruptly
    /// (return/throw/stop-jump/loop re-entry). Used ONLY as the trigger
    /// for the false-merge reconciliation below (never as a standalone
    /// follow filter — the documented-failed variants 1-7 in memory
    /// ocsp-sese-follow-diagnosis rejected follows outright and traded
    /// OCSPResponse against BasicImageReader/keytool/Locale/Throwable/
    /// ConcurrentHashMap families): a sibling route that completes
    /// normally PAST the parked target's emission point is the crossing
    /// that makes the empty-arm contract unsound.
    fn all_routes_via(
        &self,
        ctx: &SeseCtx,
        from: usize,
        target: usize,
        stop: &HashSet<usize>,
    ) -> bool {
        if from == target {
            return true;
        }
        let mut post = crate::structure::reachable_within(self.cfg, target, stop);
        post.remove(&target);
        let mut seen: HashSet<usize> = HashSet::new();
        let mut stack: Vec<usize> = vec![from];
        let mut budget = 4096usize;
        while let Some(c) = stack.pop() {
            if c == target || seen.contains(&c) {
                continue;
            }
            if budget == 0 {
                return false;
            }
            budget -= 1;
            seen.insert(c);
            if post.contains(&c) {
                return false; // bypass into the post-target flow
            }
            if stop.contains(&c) || ctx.loop_stack.contains(&c) {
                continue; // abrupt escape: jump/continue, never falls through
            }
            if matches!(
                self.results[c].term,
                crate::builder::Term::Return(_) | crate::builder::Term::Throw(_)
            ) {
                continue;
            }
            let succs: Vec<usize> = self.cfg.blocks[c]
                .succ
                .iter()
                .copied()
                .filter(|&sx| ctx.universe.contains(&sx))
                .collect();
            if succs.is_empty() {
                continue; // leaves the region: abrupt from this If's view
            }
            for sx in succs {
                if ctx.loop_headers.contains(&sx) && !seen.contains(&sx) {
                    // Re-entry into a loop header is a back-edge jump
                    // (continue), not a fallthrough — abrupt.
                    if self.cfg.blocks[c].succ.iter().any(|&o| o == sx) && sx != target {
                        if self.cfg.blocks[sx].start <= self.cfg.blocks[c].start {
                            continue;
                        }
                    }
                }
                stack.push(sx);
            }
        }
        true
    }

    fn reaches_within(&self, ctx: &SeseCtx, from: usize, target: usize, stop: &HashSet<usize>) -> bool {
        if from == target {
            return true;
        }
        // A branch that jumps straight to a stop block LEAVES the region
        // (sibling/follow owns it); it contributes no in-region confluence.
        // Without this, Integer's C2 (`radix <= 36`) "reaches" the subtree
        // through the fixup stop in one hop and cm picks the subtree head as
        // follow, emptying the branch and losing the fixup+copy shape.
        if stop.contains(&from) {
            return false;
        }
        let mut seen = HashSet::new();
        let mut stack = vec![from];
        seen.insert(from);
        while let Some(c) = stack.pop() {
            for &s in &self.cfg.blocks[c].succ {
                if s == target {
                    return true;
                }
                // Not expandable: stop blocks (region boundaries — a sibling
                // branch owns them; routing through one is not a confluence of
                // THIS branch set: Integer C2 whose fixup target is the C1
                // follow must not "reach" the subtree through it) and loop
                // headers (re-entering a loop body is a later iteration, not a
                // forward merge: ControlFlow.nestedLoops).
                if stop.contains(&s)
                    || ctx.loop_stack.contains(&s)
                    || ctx.loop_headers.contains(&s)
                {
                    continue;
                }
                if seen.insert(s) {
                    stack.push(s);
                }
            }
        }
        false
    }

    /// Structure the region starting at `entry`, stopping at any block in
    /// `stop` (region exits / follows / enclosing barriers) or at the first
    /// block not reached-from-`entry`-without-stop (a shared merge owned by a
    /// sibling or the follow). Each block is consumed exactly once.
    fn sese_region(
        &mut self,
        entry: usize,
        stop: &HashSet<usize>,
        ctx: &mut SeseCtx,
    ) -> Region {
        let reach = reachable_within(self.cfg, entry, stop);
        self.sese_region_with_scope(entry, stop, reach, ctx)
    }

    /// Region walk with an explicit scope (`reach`). Normally the scope is
    /// reachable_within(entry, stop); loop bodies pass the same set computed
    /// once at the loop site so nested walks/copies share one bound.
    /// Loop-level materialization of statement-bearing exits (jdk17
    /// AQS.cleanQueue's dropped CAS-unlink phase). Runs AFTER the loop
    /// body region is fully built, so the body's claims/consumed history
    /// is untouched — the arm-site copy experiment perturbed sibling
    /// structuring mid-walk (cancelAcquire regressed, cleanQueue's
    /// advance path was swallowed) and was reverted; this pass is pure
    /// region-tree post-processing. Each exit E carrying statement/branch
    /// CONTENT (exit_has_content; stub-chain exits like Pattern.clazz's
    /// switch-case goto stubs are exempt and keep their bare breaks) gets
    /// its cascade structured ONCE on a clean barriered scope (all exits
    /// + loop members + enclosing headers), then every `Goto{E}` in the
    /// body becomes `Seq[cascade-copy, Goto{E}]`: the break keeps its
    /// conversion binding while the cascade runs before it — the golden
    /// shape (CAS unlink executes, then break restarts the outer loop).
    /// Cascades whose flow ends at another exit or an enclosing back edge
    /// render that jump as the matching break/continue (conversion
    /// resolves against the enclosing loop stack; a cascade reaching an
    /// UNENCLOSED header falls back to the bare break).
    pub(crate) fn materialize_content_exits(
        &mut self,
        body: &mut Region,
        header: usize,
        exits: &[usize],
        members: &HashSet<usize>,
        natural: &HashSet<usize>,
        ctx_universe: &HashSet<usize>,
        ctx_loop_stack: &[usize],
        ctx_loop_headers: &HashSet<usize>,
        ctx_top_groups: &[usize],
        outer_stop: &HashSet<usize>,
        reach: &HashSet<usize>,
        consumed: &HashSet<usize>,
        natural_follow_empty: bool,
    ) {
        if MATEXIT_DISABLED.with(|d| d.get()) {
            return;
        }
        let mut barriers: HashSet<usize> = exits.iter().copied().collect();
        barriers.extend(members.iter().copied());
        barriers.extend(ctx_loop_stack.iter().copied());
        barriers.extend(ctx_loop_headers.iter().copied());
        // PARENT-CONTINUATION fold: replicate the post-loop follow_pick's
        // minimal candidate (lowest-start unconsumed in-reach exit) — when
        // natural_follow is empty the parent continues at THAT exit and
        // renders its flow once; materializing it double-renders the
        // territory (ois readSerialData e=45: the cleanup-continuation
        // copy re-bound catch identities downstream, markException(null)).
        let mut natural: HashSet<usize> = natural.iter().copied().collect();
        if natural_follow_empty {
            // Full follow_pick replication (incl. the continue-stub
            // filter): the parent's post-loop continuation is exactly
            // this block, parent-rendered once — never materialize it.
            let claim_cands: HashSet<usize> = exits
                .iter()
                .copied()
                .filter(|e| {
                    !consumed.contains(e)
                        && !outer_stop.contains(e)
                        && ctx_universe.contains(e)
                        && reach.contains(e)
                        && !self.is_handler(*e)
                        && *e != header
                })
                .collect();
            let mut cands: Vec<usize> = exits
                .iter()
                .copied()
                .filter(|e| {
                    !consumed.contains(e)
                        && !outer_stop.contains(e)
                        && ctx_universe.contains(e)
                        && reach.contains(e)
                        && !self.is_handler(*e)
                        && *e != header
                        && !ctx_loop_stack.iter().any(|h| {
                            h != e
                                && self.is_stmt_free_chain_to_block(*e, *h)
                                && !self.stub_chain_claims_continuation(
                                    *e,
                                    *h,
                                    &claim_cands,
                                )
                        })
                })
                .collect();
            cands.sort_by_key(|x| self.cfg.blocks[*x].start);
            if let Some(f) = cands.first() {
                natural.insert(*f);
            }
        }
        let natural = &natural;
        if std::env::var("JCDC_DBG_SESE").is_ok() {
            let mut nv: Vec<usize> = natural.iter().copied().collect();
            nv.sort_unstable();
            eprintln!("MXNAT header={} exits={:?} natural={:?}", header, exits, nv);
        }
        // Baseline conversion of the un-spliced body: the trial
        // pathology scan compares against it (a splice that introduces a
        // NEW Stmt::Labeled changed classify_loop's rotation — the
        // ObjectInputStream readSerialData corruption route: the L2
        // re-rotation moved catch blocks across LVT ranges and varalloc
        // rebound the catch identity, markException(ex=null)).
        let base_labeled = {
            let mut conv = crate::convert::Converter::new(self.cfg, self.results)
                .with_copied_tails(self.copied_tails.clone())
                .with_final_fields(self.final_fields.clone());
            let base_stmt = conv.convert(body.clone());
            Self::count_labeled(&base_stmt)
        };
        let skip_e: Option<usize> = std::env::var("JCDC_MATEXIT_SKIP")
            .ok()
            .and_then(|v| v.parse().ok());
        for &e in exits {
            if Some(e) == skip_e {
                continue;
            }
            if members.contains(&e)
                || natural.contains(&e)
                || ctx_loop_stack.contains(&e)
                || ctx_loop_headers.contains(&e)
                || self.is_terminator_block(e)
                || !self.exit_has_content(e, &barriers)
            {
                continue;
            }
            let mut cstop = barriers.clone();
            cstop.remove(&e);
            cstop.extend(natural.iter().copied());
            // The NATURAL CONTINUATION'S forward closure is parent-
            // rendered territory: a cascade may not swallow it (ois
            // readSerialData e=45's tu dragged in the post-loop blocks
            // 50-57 — double-rendered flow re-bound catch identities
            // downstream, markException(ex=null)). Barriers for the
            // closure: exits, enclosing headers, members — the closure
            // must not wrap around the loop.
            {
                let mut cl_bar: HashSet<usize> = exits.iter().copied().collect();
                cl_bar.extend(members.iter().copied());
                cl_bar.extend(ctx_loop_stack.iter().copied());
                cl_bar.extend(ctx_loop_headers.iter().copied());
                let mut cl: HashSet<usize> = HashSet::new();
                let mut cq: Vec<usize> = natural.iter().copied().collect();
                while let Some(b) = cq.pop() {
                    if !cl.insert(b) {
                        continue;
                    }
                    for &n2 in &self.cfg.blocks[b].succ {
                        if !cl_bar.contains(&n2) {
                            cq.push(n2);
                        }
                    }
                }
                cstop.extend(cl.iter().copied());
                cstop.remove(&e);
            }
            // ORPHANED exits only: E must NOT be forward-reachable from
            // any natural exit's flow. When it is, the parent renders that
            // flow after the Loop (ordinary continuation or finally-copy
            // machinery) and the break lands into it — splicing a copy
            // duplicated ObjectInputStream.readSerialData's finally-cleanup
            // retry (3x catch(ThreadDeath ignored), 已在方法中定义了变量)
            // and stranded ConcurrentHashMap.getTable tails (无法访问的语句).
            // An orphaned E is rendered NOWHERE else: cleanQueue's CAS
            // unlink phase (reachable only via member jumps, its flow
            // restarts the outer loop) and TempFileHelper's
            // `hasPermissions = true` block (flow joins the post-loop
            // continuation only THROUGH the shared break stub).
            // Barriered forward reachability: the RAW can_reach wraps
            // around the loop through the restart backedge and makes
            // every exit "reachable" from every natural (cleanQueue 6→
            // 24→0→1→…→11) — barriers are the other exits, members and
            // enclosing headers.
            let orphaned = !natural.contains(&e) && {
                let mut seen_o: HashSet<usize> = HashSet::new();
                let mut qo: Vec<usize> = natural.iter().copied().collect();
                for x in &qo {
                    seen_o.insert(*x);
                }
                let mut found = false;
                while let Some(b) = qo.pop() {
                    for &n2 in &self.cfg.blocks[b].succ {
                        if n2 == e {
                            found = true;
                            break;
                        }
                        if barriers.contains(&n2) || n2 == header {
                            continue;
                        }
                        if seen_o.insert(n2) {
                            qo.push(n2);
                        }
                    }
                    if found {
                        break;
                    }
                }
                !found
            };
            if !orphaned {
                continue;
            }
            // SHARED-PRED gate: an exit that shares a normal-flow
            // predecessor with a loop member is a SIBLING CONTINUATION
            // branch (b24 flows to BOTH the member b25 and the exit 45 —
            // ois readSerialData's finally-cleanup fork), not an orphaned
            // break target: the outer region renders that territory once,
            // and copying it double-renders the flow (catch identities
            // rebound downstream: markException(ex=null)). cleanQueue's
            // CAS exit (preds all members), Bits' epilogue (pred = its
            // own test) and tfh/FJP/CHM restorations have no shared pred.
            let shared_pred = self.cfg.blocks[e].pred.iter().any(|&p| {
                p != header
                    && !members.contains(&p)
                    && self.cfg.blocks[p].succ.len() >= 2
            });
            if shared_pred {
                continue;
            }
            // UPDATE-BLOCK gate: an exit whose forward flow (barred by the
            // other exits, members, enclosing headers and the natural
            // continuation) reaches THIS loop's header is the iteration
            // update block — copying it into a jump arm inverts break into
            // advance+continue (Pattern split's `break` became `++x2;
            // offset += len; continue L3`). A genuine break exit receives
            // member edges too (the cond's exit side) but never flows back
            // to the header inside the barriers (cleanQueue's CAS exit
            // restarts via the OUTER stub, TempFileHelper's joins the
            // post-loop continuation).
            let is_update = {
                let mut bar: HashSet<usize> = barriers.clone();
                bar.extend(natural.iter().copied());
                bar.remove(&e);
                let mut seen2: HashSet<usize> = HashSet::new();
                let mut q2: Vec<usize> = vec![e];
                seen2.insert(e);
                let mut found = false;
                while let Some(b) = q2.pop() {
                    if self.cfg.blocks[b].succ.iter().any(|&n| n == header) {
                        found = true;
                        break;
                    }
                    for &n in &self.cfg.blocks[b].succ {
                        if !bar.contains(&n) && seen2.insert(n) {
                            q2.push(n);
                        }
                    }
                }
                found
            };
            if is_update {
                continue;
            }
            // GROUP-TERRITORY gate: an exit whose flow lies inside any try
            // group's protected span (or is a handler) belongs to the
            // finally/catch machinery — copying it competes with the
            // dedupe/catch-identity passes (ObjectInputStream
            // .readSerialData: the e=4 micro-cascade copy re-bound the
            // catch vars — `catch (ClassNotFoundException ignored)` +
            // `ex = null` made markException receive NULL instead of the
            // exception, and the triple `ignored` collided). cleanQueue
            // and TempFileHelper have no groups over their cascades.
            let in_group = self
                .groups
                .iter()
                .any(|g| self.cfg.blocks[e].start >= g.start && self.cfg.blocks[e].start < g.end)
                || self.body_group.contains_key(&e)
                || self.handler_group.contains_key(&e);
            if in_group {
                continue;
            }
            let tu = crate::structure::reachable_within(self.cfg, e, &cstop);
            if !tu.contains(&e) || tu.len() > 48 {
                continue;
            }
            // HANDLER/THROW-TERRITORY gate: a cascade whose blocks
            // include an exception-handler head or a throw site is
            // finally/pending-rethrow machinery — copying it re-renders
            // catch flow and the downstream naming passes rebind the
            // catch identity (ois readSerialData e=24: the retry cascade
            // copy turned `catch (ClassNotFoundException e1) {
            // markException(passHandle, e1) }` into `catch (... ignored)
            // { ex = null; markException(passHandle, ex) }` — NULL
            // instead of the exception — plus a triple-`ignored`
            // redefinition error; conversion-time trial checks cannot
            // see it: the corruption happens in the post-convert
            // varalloc/naming passes). Such exits keep the bare break.
            // The e=4 single-Basic cascade (a genuine dropped
            // `hasSpecialReadMethod = true` restoration, golden-verified)
            // has neither handler heads nor throws and stays.
            if tu.iter().any(|&b| {
                self.handler_group.contains_key(&b)
                    || matches!(self.results[b].term, Term::Throw(_))
            }) {
                continue;
            }
            let mut fresh: HashSet<usize> = HashSet::new();
            // The walk's stop carries the OUTER barriers too (not just
            // cstop): Goto regions targeting them resolve to
            // break/continue at conversion instead of materializing
            // foreign territory as RawGoto copies (the ois finally-cleanup
            // duplication route).
            let mut wstop: HashSet<usize> = cstop.clone();
            wstop.extend(barriers.iter().copied());
            wstop.extend(natural.iter().copied());
            wstop.remove(&e);
            // copied_tails isolation: the cascade walk's internal
            // copy_walks register shared tails; leaking those into the
            // method's set makes the PARENT's own gotos to them elide as
            // reaches_copy_tail fallthrough — UnixPath.normalize lost its
            // whole `while (i1 < count) ... return new UnixPath(..)`
            // continuation (缺少返回语句 x2 trees) after an ACCEPTED splice.
            // Restore unconditionally: the cascade's registrations are
            // arm-local; the arm-internal trailing gotos still elide via
            // goto_is_last inside the copy.
            let saved_tails = self.copied_tails.clone();
            let r = self.walk(e, &tu, &wstop, &ctx_top_groups, &mut fresh, true);
            self.copied_tails = saved_tails;
            if matches!(r, Region::Empty) {
                continue;
            }
            // SELF-CONTAINED-FLOW gate: every successor of every cascade
            // block must stay inside the cascade universe or land on a
            // declared barrier (another exit, an enclosing header, the
            // natural continuation). A flow escaping elsewhere (into a
            // handler region or foreign territory) gets mangled by the
            // copy's conversion context (ObjectInputStream readSerialData:
            // the finally-cleanup retry copied as bare blocks re-bound
            // catch identities — markException received a null `ex`).
            let self_contained = tu.iter().all(|&b| {
                self.cfg.blocks[b].succ.iter().all(|&n| {
                    tu.contains(&n)
                        || cstop.contains(&n)
                        || exits.contains(&n)
                        || natural.contains(&n)
                        || ctx_loop_stack.contains(&n)
                        || ctx_loop_headers.contains(&n)
                })
            });
            if !self_contained {
                continue;
            }
            // A cascade containing a Try cannot be spliced as a copy: the
            // duplicated catch parameter collides with the original's
            // scope (jdk11/17 ObjectInputStream.readSerialData 已在方法中
            // 定义了变量 ignored — an inner catch may not redeclare an
            // outer catch's variable). Renaming catch vars is a
            // Stmt-level concern the region copy cannot express; those
            // exits keep the bare break (pre-fix behavior).
            if Self::region_contains_try(&r) {
                continue;
            }
            if std::env::var("JCDC_DBG_SESE").is_ok() {
                let txt = format!("{:?}", r);
                eprintln!(
                    "MATEXIT e={} tu={} r={}",
                    e,
                    tu.len(),
                    &txt[..txt.len().min(300)]
                );
            }
            // REDUNDANT BACKEDGE TRIM: a trailing Goto to THIS loop's own
            // header is the fall-out-equivalent (the parent renders
            // `continue` right after the loop anyway) — kept in the copy
            // it makes the arm all-abrupt and strands that continue
            // (ForkJoinPool awaitDone 无法访问的语句). Drop it; the arm
            // then completes normally into the parent's backedge.
            fn trim_backedge(r: &mut Region, header: usize) {
                if let Region::Seq(v) = r {
                    if matches!(v.last(), Some(Region::Goto { target }) if *target == header) {
                        v.pop();
                    }
                    return;
                }
                if matches!(r, Region::Goto { target } if *target == header) {
                    *r = Region::Empty;
                }
            }
            let mut r = r;
            trim_backedge(&mut r, header);
            if matches!(r, Region::Empty) {
                continue;
            }
            // CONVERSION-AWARE VALIDATION (the gate the region-level
            // predicates could not express — two experiment rounds proved
            // the harm classes arise at conversion/Stmt level): trial-
            // splice into a CLONE, convert it in a throwaway Converter,
            // and scan the Stmt tree for splice pathologies:
            // (1) abrupt-stranding — a terminating statement followed by
            //     siblings in the same block (the spliced cascade's inner
            //     gotos resolved to break/continue at this site where the
            //     ORIGINAL Goto{E} elided as fallthrough; jdk26
            //     ConcurrentHashMap.getTable 无法访问的语句). prune_
            //     unreachable would silently DELETE the stranded siblings.
            // (2) duplicate catch exception types — the copy re-rendered
            //     handler flow whose catch identity the naming passes
            //     then rebind (jdk11 ObjectInputStream.readSerialData
            //     markException(ex=null) semantic corruption).
            // Clean → commit the splice; pathology → roll back this exit
            // (the clone is dropped; nothing outside was mutated).
            // Two-tier site policy validated by trial conversion: tier 1
            // (loose) splices arm/tail Goto sites even under enclosing
            // Seqs with live siblings (CHM putVal's addCount restoration
            // lives on such an arm); tier 2 (strict) restricts to the
            // true flow-end chain (Bits phase-1's catch-handler Goto{16}
            // is followed by the handler's Goto{7} retry — splicing the
            // terminating epilogue there strands it). Validate tier 1;
            // on pathology fall back to tier 2 and re-validate; reject
            // the exit only when both fail.
            //
            // A cascade whose every flow path already terminates
            // (return/throw inlined via term_copy) takes NO trailing
            // Goto{e} (the break would render after a return — dead);
            // non-terminating cascades keep it so the break binding
            // survives. In-loop normalization: when the loop's natural
            // continuation is itself a barrier (backedge stub / outer
            // header / exit), re-append Goto{e} so the fall-out arm
            // re-iterates explicitly like the golden `continue`.
            let mut replacement = if self.region_all_paths_terminate(&r) {
                r.clone()
            } else {
                Region::Seq(vec![r.clone(), Region::Goto { target: e }])
            };
            let natural_is_barrier = natural
                .iter()
                .all(|&n0| exits.contains(&n0) || ctx_loop_stack.contains(&n0));
            if natural_is_barrier
                && self.region_all_paths_terminate(&r)
                && !matches!(replacement, Region::Seq(_))
            {
                replacement =
                    Region::Seq(vec![replacement, Region::Goto { target: e }]);
            }
            let convert_trial = |tb: Region| -> (Stmt, usize) {
                let mut conv = crate::convert::Converter::new(self.cfg, self.results)
                    .with_copied_tails(self.copied_tails.clone())
                    .with_final_fields(self.final_fields.clone());
                let st = conv.convert(tb);
                let lab = Self::count_labeled(&st);
                (st, lab)
            };
            let trial1 = {
                let mut tb = body.clone();
                Self::splice_exit_copies_with(&mut tb, e, &replacement, false);
                self.replace_empty_arms_for(&mut tb, e, &replacement);
                tb
            };
            let (stmt1, lab1) = convert_trial(trial1);
            let strict = if !Self::stmt_splice_pathology(&stmt1) && lab1 == base_labeled {
                false
            } else {
                let trial2 = {
                    let mut tb = body.clone();
                    Self::splice_exit_copies_with(&mut tb, e, &replacement, true);
                    self.replace_empty_arms_for(&mut tb, e, &replacement);
                    tb
                };
                let (stmt2, lab2) = convert_trial(trial2);
                if Self::stmt_splice_pathology(&stmt2) || lab2 != base_labeled {
                    if std::env::var("JCDC_DBG_SESE").is_ok() {
                        eprintln!("MATEXIT-REJECT e={} both tiers pathological", e);
                    }
                    continue;
                }
                true
            };
            if std::env::var("JCDC_DBG_SESE").is_ok() {
                let mut tusize: Vec<usize> = tu.iter().copied().collect();
                tusize.sort_unstable();
                eprintln!("MATEXIT-ACCEPT e={} strict={} tu={:?}", e, strict, tusize);
                for (gi, g) in self.groups.iter().enumerate() {
                    let overlap: Vec<usize> = tusize.iter().copied().filter(|&b| {
                        self.cfg.blocks[b].start >= g.start && self.cfg.blocks[b].start < g.end
                    }).collect();
                    if !overlap.is_empty() {
                        eprintln!("MXGROUP gi={} span=({},{}) overlap={:?}", gi, g.start, g.end, overlap);
                    }
                }
                let bg: Vec<usize> = tusize.iter().copied().filter(|b| self.body_group.contains_key(b)).collect();
                let hg: Vec<usize> = tusize.iter().copied().filter(|b| self.handler_group.contains_key(b)).collect();
                eprintln!("MXGH body_group={:?} handler_group={:?}", bg, hg);
            }
            let h1 = Self::splice_exit_copies_with(body, e, &replacement, strict);
            let h2 = self.replace_empty_arms_for(body, e, &replacement);
            if h1 || h2 {
                MATEXIT_FIRED.with(|f| f.set(true));
            }
        }
    }

    /// True when every flow path through the region ends at a
    /// return/throw (Basic/CopyStmts of a terminator block, or a Goto
    /// whose target term-copies inline). Empty arms fall through, so an
    /// If only terminates when BOTH arms do; a Seq when its last element
    /// does.
    fn region_all_paths_terminate(&self, r: &Region) -> bool {
        match r {
            Region::Basic { block } | Region::CopyStmts { block } => {
                self.is_terminator_block(*block)
            }
            Region::Goto { target } => self.is_terminator_block(*target),
            Region::Seq(v) => v
                .last()
                .map(|x| self.region_all_paths_terminate(x))
                .unwrap_or(false),
            Region::If { then_r, else_r, .. } => {
                self.region_all_paths_terminate(then_r)
                    && self.region_all_paths_terminate(else_r)
            }
            Region::Try { body, catches, .. } => {
                self.region_all_paths_terminate(body)
                    && catches
                        .iter()
                        .all(|(_, _, h)| self.region_all_paths_terminate(h))
            }
            _ => false,
        }
    }

    /// Count Stmt::Labeled nodes in a converted tree (rotation-shape
    /// fingerprint for the trial comparison).
    fn count_labeled(s: &Stmt) -> usize {
        let mut n = match s {
            Stmt::Labeled { .. } => 1,
            _ => 0,
        };
        match s {
            Stmt::Block(v) => {
                for x in v {
                    n += Self::count_labeled(x);
                }
            }
            Stmt::If { then_stmt, else_stmt, .. } => {
                n += Self::count_labeled(then_stmt);
                if let Some(e) = else_stmt {
                    n += Self::count_labeled(e);
                }
            }
            Stmt::While { body, .. }
            | Stmt::DoWhile { body, .. }
            | Stmt::ForEach { body, .. }
            | Stmt::Labeled { body, .. }
            | Stmt::Synchronized { body, .. } => n += Self::count_labeled(body),
            Stmt::For { init, body, .. } => {
                for x in init {
                    n += Self::count_labeled(x);
                }
                n += Self::count_labeled(body);
            }
            Stmt::Try { body, catches, finally, .. } => {
                n += Self::count_labeled(body);
                for c in catches {
                    n += Self::count_labeled(&c.body);
                }
                if let Some(f) = finally {
                    n += Self::count_labeled(f);
                }
            }
            Stmt::Switch { cases, default, .. } => {
                for c in cases {
                    for x in &c.body {
                        n += Self::count_labeled(x);
                    }
                }
                if let Some(d) = default {
                    n += Self::count_labeled(d);
                }
            }
            _ => {}
        }
        n
    }

    /// Scan a converted Stmt tree for splice pathologies (see
    /// materialize_content_exits). Conservative: any hit rolls the exit
    /// back to the bare-break shape.
    pub(crate) fn stmt_splice_pathology(s: &Stmt) -> bool {
        Self::pathology_in(s, None)
    }

    /// Label-aware JLS-14.21 termination for the pathology scanner:
    /// `break L1` targeting an OUTER labeled loop escapes an inner
    /// `while (true)` WITHOUT letting it complete normally — only
    /// Break(None) or a break carrying THIS loop's own label does.
    /// stmt_terminates's any-labeled-break conservatism (correct for
    /// prune_unreachable's deletion side) false-negatived the
    /// ForwardingNode.find strand (无法访问的语句 x3 trees: the spliced
    /// cascade made the inner while(true) body all-abrupt, the outer
    /// break-through left the loop non-completing, and the parent's next
    /// sibling was unreachable).
    fn terminates_scoped(s: &Stmt, own: Option<&str>) -> bool {
        fn is_true_expr(c: &crate::expr::Expr) -> bool {
            matches!(c, crate::expr::Expr::Const(crate::expr::ConstVal::Int(1)))
        }
        fn deep_own_break(s: &Stmt, own: Option<&str>) -> bool {
            match s {
                Stmt::Break(None) => true,
                Stmt::Break(Some(l)) => Some(l.as_str()) == own,
                Stmt::Block(v) => v.iter().any(|x| deep_own_break(x, own)),
                Stmt::If { then_stmt, else_stmt, .. } => {
                    deep_own_break(then_stmt, own)
                        || else_stmt
                            .as_ref()
                            .map(|e| deep_own_break(e, own))
                            .unwrap_or(false)
                }
                Stmt::While { body, .. }
                | Stmt::DoWhile { body, .. }
                | Stmt::ForEach { body, .. }
                | Stmt::For { body, .. }
                | Stmt::Synchronized { body, .. }
                | Stmt::Labeled { body, .. } => deep_own_break(body, own),
                Stmt::Switch { cases, default, .. } => {
                    cases
                        .iter()
                        .any(|c| c.body.iter().any(|x| deep_own_break(x, own)))
                        || default
                            .as_ref()
                            .map(|d| deep_own_break(d, own))
                            .unwrap_or(false)
                }
                Stmt::Try { body, catches, finally, .. } => {
                    deep_own_break(body, own)
                        || catches.iter().any(|c| deep_own_break(&c.body, own))
                        || finally
                            .as_ref()
                            .map(|f| deep_own_break(f, own))
                            .unwrap_or(false)
                }
                Stmt::TryWithResources { resources, body, catches, finally, .. } => {
                    resources.iter().any(|r| deep_own_break(r, own))
                        || deep_own_break(body, own)
                        || catches.iter().any(|c| deep_own_break(&c.body, own))
                        || finally
                            .as_ref()
                            .map(|f| deep_own_break(f, own))
                            .unwrap_or(false)
                }
                _ => false,
            }
        }
        match s {
            Stmt::Return(_) | Stmt::Throw(_) | Stmt::Break(_) | Stmt::Continue(_) => true,
            Stmt::Block(v) => v
                .last()
                .map(|x| Structurer::terminates_scoped(x, own))
                .unwrap_or(false),
            Stmt::If { then_stmt, else_stmt: Some(e), .. } => {
                Structurer::terminates_scoped(then_stmt, own)
                    && Structurer::terminates_scoped(e, own)
            }
            Stmt::Synchronized { body, .. } => Structurer::terminates_scoped(body, own),
            Stmt::Labeled { label, body } => Structurer::terminates_scoped(body, Some(label)),
            Stmt::While { cond, body } | Stmt::DoWhile { body, cond }
                if is_true_expr(cond) && !deep_own_break(body, own) =>
            {
                true
            }
            Stmt::For { cond, body, .. }
                if match cond {
                    None => true,
                    Some(c) => is_true_expr(c),
                } && !deep_own_break(body, own) =>
            {
                true
            }
            Stmt::Try { body, catches, .. } => {
                Structurer::terminates_scoped(body, own)
                    && catches
                        .iter()
                        .all(|c| Structurer::terminates_scoped(&c.body, own))
            }
            _ => false,
        }
    }

    fn pathology_in(s: &Stmt, own: Option<&str>) -> bool {
        fn stmt_is_empty(x: &Stmt) -> bool {
            match x {
                Stmt::Block(v) => v.iter().all(stmt_is_empty),
                Stmt::Comment(_) => true,
                _ => false,
            }
        }
        fn dup_catch(catches: &[crate::stmt::Catch]) -> bool {
            for i in 0..catches.len() {
                for j in i + 1..catches.len() {
                    if !catches[i].exc.is_empty() && catches[i].exc == catches[j].exc {
                        return true;
                    }
                }
            }
            false
        }
        match s {
            Stmt::Block(v) => {
                if v.len() > 1 {
                    if let Some(pos) = v
                        .iter()
                        .position(|x| Structurer::terminates_scoped(x, own))
                    {
                        // EMPTY trailing blocks are conversion placeholders
                        // (elided gotos) that cleanup() removes before
                        // render — javac never sees them. Only NON-EMPTY
                        // stranded siblings are pathologies (the trial
                        // scans raw converter output; Bits phase-1's
                        // [terminating Try, Block([])] false positive
                        // vetoed the splice).
                        //
                        // EXCEPT when the terminator is an emit-level
                        // dead-end while(true): Printer::into_string runs
                        // truncate_dead_ends over the FINAL tree and
                        // strips everything after it, so javac never sees
                        // those siblings either — flagging them vetoed the
                        // matexit shape whose break-cascade arms carry the
                        // loop's real exits (jdk26 ConcurrentLinkedQueue
                        // .poll: the restart Continue(None) after the
                        // dead-end inner traversal forced the retry, whose
                        // matexit-OFF shape drops the cas-success p==h
                        // `return item` exit — the polled item was
                        // dequeued but never returned).
                        let scan_len =
                            if crate::emit::dead_end_infinite_while(&v[pos]) {
                                pos + 1
                            } else {
                                v.len()
                            };
                        if v[pos + 1..scan_len].iter().any(|x| !stmt_is_empty(x)) {
                            return true;
                        }
                        // Truncated siblings are invisible to javac — their
                        // interiors cannot be pathologies either.
                        return v[..scan_len]
                            .iter()
                            .any(|x| Structurer::pathology_in(x, own));
                    }
                }
                v.iter().any(|x| Structurer::pathology_in(x, own))
            }
            Stmt::If { then_stmt, else_stmt, .. } => {
                Structurer::pathology_in(then_stmt, own)
                    || else_stmt
                        .as_ref()
                        .map(|e| Structurer::pathology_in(e, own))
                        .unwrap_or(false)
            }
            // Loop bodies bind unlabeled breaks to themselves: the
            // enclosing label does NOT propagate in (an inner while(true)
            // under `L1:` is still non-completing when its body breaks
            // to L1 — the break escapes THROUGH it). Synchronized is
            // transparent.
            Stmt::While { body, .. }
            | Stmt::DoWhile { body, .. }
            | Stmt::ForEach { body, .. } => Structurer::pathology_in(body, None),
            Stmt::Synchronized { body, .. } => Structurer::pathology_in(body, own),
            Stmt::For { init, body, .. } => {
                init.iter().any(|x| Structurer::pathology_in(x, own))
                    || Structurer::pathology_in(body, None)
            }
            Stmt::Labeled { label, body } => Structurer::pathology_in(body, Some(label)),
            Stmt::Try { body, catches, finally, .. } => {
                dup_catch(catches)
                    || Structurer::pathology_in(body, own)
                    || catches
                        .iter()
                        .any(|c| Structurer::pathology_in(&c.body, own))
                    || finally
                        .as_ref()
                        .map(|f| Structurer::pathology_in(f, own))
                        .unwrap_or(false)
            }
            Stmt::TryWithResources { body, catches, finally, .. } => {
                dup_catch(catches)
                    || Structurer::pathology_in(body, own)
                    || catches
                        .iter()
                        .any(|c| Structurer::pathology_in(&c.body, own))
                    || finally
                        .as_ref()
                        .map(|f| Structurer::pathology_in(f, own))
                        .unwrap_or(false)
            }
            Stmt::Switch { cases, default, .. } => {
                cases
                    .iter()
                    .any(|c| c.body.iter().any(|x| Structurer::pathology_in(x, own)))
                    || default
                        .as_ref()
                        .map(|d| Structurer::pathology_in(d, own))
                        .unwrap_or(false)
            }
            _ => false,
        }
    }

    /// True when the region tree contains any Try.
    fn region_contains_try(r: &Region) -> bool {
        match r {
            Region::Try { .. } => true,
            Region::Seq(v) => v.iter().any(Self::region_contains_try),
            Region::If { then_r, else_r, .. } => {
                Self::region_contains_try(then_r) || Self::region_contains_try(else_r)
            }
            Region::Loop { body, .. } => Self::region_contains_try(body),
            Region::Switch { cases, default, .. } => {
                cases.iter().any(|(_, cr)| Self::region_contains_try(cr))
                    || default
                        .as_ref()
                        .map(|d| Self::region_contains_try(d))
                        .unwrap_or(false)
            }
            _ => false,
        }
    }

    /// Replace EMPTY If arms whose branch target is `e` with the
    /// replacement region: the Bits phase-1 shape has NO Goto{e} site at
    /// all — the COND's fall==follow==exit renders the success arm as
    /// Region::Empty and the body falls out to the backedge (re-loop).
    /// The empty arm IS the jump to e; materializing it restores the
    /// golden `if (!call) continue; else { epilogue; }`.
    fn replace_empty_arms_for(&self, r: &mut Region, e: usize, replacement: &Region) -> bool {
        match r {
            Region::If { block, then_r, else_r, .. } => {
                let succs = &self.cfg.blocks[*block].succ;
                let mut hit = false;
                if matches!(**then_r, Region::Empty) && succs.get(1) == Some(&e) {
                    *then_r = Box::new(replacement.clone());
                    hit = true;
                }
                if matches!(**else_r, Region::Empty) && succs.first() == Some(&e) {
                    *else_r = Box::new(replacement.clone());
                    hit = true;
                }
                hit |= self.replace_empty_arms_for(then_r, e, replacement);
                hit |= self.replace_empty_arms_for(else_r, e, replacement);
                hit
            }
            Region::Seq(v) => v
                .iter_mut()
                .fold(false, |h, x| h | self.replace_empty_arms_for(x, e, replacement)),
            Region::Try { body, catches, .. } => {
                let mut hit = self.replace_empty_arms_for(body, e, replacement);
                for (_, _, h) in catches.iter_mut() {
                    hit |= self.replace_empty_arms_for(h, e, replacement);
                }
                hit
            }
            Region::Loop { body, .. } => self.replace_empty_arms_for(body, e, replacement),
            Region::Switch { cases, default, .. } => {
                let mut hit = false;
                for (_, cr) in cases.iter_mut() {
                    hit |= self.replace_empty_arms_for(cr, e, replacement);
                }
                if let Some(d) = default {
                    hit |= self.replace_empty_arms_for(d, e, replacement);
                }
                hit
            }
            _ => false,
        }
    }

    /// Replace `Goto{e}` sites in the region tree with `replacement`
    /// (per-arrival copies; Region: Clone). `strict`: only sites on the
    /// true flow-end chain (every enclosing Seq position is last) are
    /// replaced; loose mode additionally replaces arm-internal sites
    /// whose enclosing Seq has live siblings. A MID-Seq Goto leaf is
    /// never replaced in either mode (live siblings follow it directly).
    fn splice_exit_copies_with(
        r: &mut Region,
        e: usize,
        replacement: &Region,
        strict: bool,
    ) -> bool {
        match r {
            Region::Goto { target } if *target == e => {
                *r = replacement.clone();
                true
            }
            Region::Seq(v) => {
                let mut hit = false;
                let n = v.len();
                for (i, x) in v.iter_mut().enumerate() {
                    let last = i + 1 == n;
                    if matches!(x, Region::Goto { target } if *target == e) {
                        if last {
                            *x = replacement.clone();
                            hit = true;
                        }
                    } else {
                        hit |= Self::splice_exit_copies_with(
                            x,
                            e,
                            replacement,
                            strict || !last,
                        );
                    }
                }
                hit
            }
            Region::If { then_r, else_r, .. } => {
                let a = Self::splice_exit_copies_with(then_r, e, replacement, strict);
                let b = Self::splice_exit_copies_with(else_r, e, replacement, strict);
                a | b
            }
            Region::Try { body, catches, .. } => {
                let mut hit = Self::splice_exit_copies_with(body, e, replacement, strict);
                for (_, _, h) in catches.iter_mut() {
                    hit |= Self::splice_exit_copies_with(h, e, replacement, strict);
                }
                hit
            }
            Region::Loop { body, .. } => {
                Self::splice_exit_copies_with(body, e, replacement, strict)
            }
            Region::Switch { cases, default, .. } => {
                let mut hit = false;
                for (_, cr) in cases.iter_mut() {
                    hit |= Self::splice_exit_copies_with(cr, e, replacement, strict);
                }
                if let Some(d) = default {
                    hit |= Self::splice_exit_copies_with(d, e, replacement, strict);
                }
                hit
            }
            _ => false,
        }
    }

    fn sese_region_with_scope(
        &mut self,
        entry: usize,
        stop: &HashSet<usize>,
        reach: HashSet<usize>,
        ctx: &mut SeseCtx,
    ) -> Region {
        ctx.depth += 1;
        let deep = ctx.depth > 400;
        let mut parts: Vec<Region> = Vec::new();
        let mut cur = entry;
        let mut guard = 0usize;
        // True when the walk advanced into `cur` through an explicit Goto
        // terminator (vs. natural fall-through): a jump into a stop must be
        // materialized as a Goto region (the converter resolves it to
        // break/continue, elides it as if-follow fallthrough, or inlines a
        // shared return/throw via term_copy) — silently ending the region
        // DROPS the jump (jdk17 String LATIN1 fast-path `goto 839` lost its
        // `return;` against the stop=shared-exit, double-assigning finals).
        let mut last_via_goto = false;
        loop {
            guard += 1;
            if std::env::var("JCDC_DBG_GOTO").is_ok() {
                eprintln!("SESETOP entry={} cur={} parts={} reach={} stop={} consumed={} last_via_goto={}",
                    entry, cur, parts.len(), reach.contains(&cur), stop.contains(&cur),
                    ctx.consumed.contains(&cur), last_via_goto);
            }
            if deep || guard > ctx.universe.len() * 4 + 64 {
                break;
            }
            // A try body reaches its tail through inlined/duplicated finally
            // copies, so reachable_within (normal succ only) can miss the
            // post-finally continuation even though it is a legitimate forward
            // tail (unconsumed, in-universe, not a stop). Structure it anyway;
            // monotonicity is preserved by the consumed check below (a block
            // owned by a sibling is consumed -> Goto, never re-structured).
            let forward_tail = !reach.contains(&cur)
                && ctx.universe.contains(&cur)
                && !ctx.consumed.contains(&cur)
                && !stop.contains(&cur);
            if !forward_tail
                && (stop.contains(&cur) || !ctx.universe.contains(&cur) || !reach.contains(&cur))
            {
                // A region whose ENTRY is itself a stop block was branched-to
                // deliberately (a cond branch / `break` to a loop exit, or a
                // jump to an enclosing follow). Emit Goto{entry} so the
                // converter resolves it to break/continue — or elides it as a
                // natural fallthrough when entry is the enclosing if-follow.
                // Without this, a `break outer` branch to a stop block renders
                // as an EMPTY branch and the loop exit is silently lost
                // (Legacy6 `if (a==2 && b==2) break outer;` -> infinite loop).
                if cur == entry && stop.contains(&entry) && parts.is_empty() {
                    parts.push(Region::Goto { target: entry });
                } else if last_via_goto && stop.contains(&cur) && !parts.is_empty() {
                    parts.push(Region::Goto { target: cur });
                }
                break;
            }
            if ctx.consumed.contains(&cur) {
                // Already structured (a shared merge owned by an earlier
                // sibling/region). A shared TERMINATOR (return/throw) is
                // safely duplicated inline at each arrival site (it has no
                // outgoing flow) — this is how `if (t || explode()) return 1;
                // return 2;` keeps the `return 1` on both the t-true and
                // explode-true paths. Anything else becomes a Goto (resolved
                // to break/continue/label at conversion), never a re-walk.
                if matches!(self.results[cur].term, Term::Return(_) | Term::Throw(_)) {
                    // Shared terminator: duplicate inline (no outgoing
                    // flow). Duplicating a final-field write is REQUIRED
                    // here: the paths are disjoint (each copy ends in the
                    // return), and eliding it would drop the assignment
                    // from this path entirely ("variable f might not have
                    // been assigned" — Fin/Long$LongCache fresh path).
                    parts.push(Region::CopyStmts { block: cur });
                } else if ctx.loop_stack.contains(&cur) {
                    // Back-edge to an enclosing loop header: a `continue`
                    // (resolved at conversion). NEVER copy_walk it — that would
                    // re-walk the whole loop as a nested duplicate. The Goto is
                    // emitted even when parts is empty: a branch region that
                    // IS the jump to the header (`if (c) continue;`) must not
                    // collapse to Empty — that silently dropped BOTH continues
                    // of StringUTF16.codePointCount, running the loop tail
                    // unconditionally.
                    parts.push(Region::Goto { target: cur });
                } else if let Some(&h) = ctx.loop_stack.iter().rev().find(|&&h| {
                    crate::structure::can_reach_cfg(self.cfg, cur, h, 4096)
                }) {
                    // The consumed block flows back into an enclosing loop
                    // (a catch's retry back-edge into the loop-top try,
                    // jdk11 ObjectStreamClass.getInheritableMethod): a
                    // copy_walk here unrolls the loop into nested duplicate
                    // tries (COPY_DEPTH-bounded, then wrong). Resolve as
                    // `continue` of the nearest such loop instead — walk's
                    // loops_stack guard equivalent (walk tracks its own
                    // stack; SESE keeps it in ctx).
                    parts.push(Region::Goto { target: h });
                } else if !stop.contains(&cur) {
                    // Shared non-terminator reached from a divergent sibling
                    // (e.g. the continuation after `if (A && B) return X;`):
                    // copy_walk re-structures it inline, COPY_DEPTH-bounded so
                    // nested shared chains stay monotone (no divergence). The
                    // copy is additionally barred from leaving THIS region's
                    // scope: reachable_within(copy) must not pick up blocks the
                    // enclosing walk could never consume (that is how the
                    // post-loop tail vanished from a copied loop branch).
                    // Falls back to a Goto when the cap is hit or it loops back.
                    let mut cstop: HashSet<usize> = stop.iter().copied().collect();
                    for &u in ctx.universe.iter() {
                        if !reach.contains(&u) {
                            cstop.insert(u);
                        }
                    }
                    let prev_allow = crate::structure::COPY_ALLOW_CONFLUENCE
                        .with(|c| c.replace(true));
                    let copied = self.copy_walk(cur, &cstop, &ctx.top_groups, usize::MAX);
                    crate::structure::COPY_ALLOW_CONFLUENCE
                        .with(|c| c.set(prev_allow));
                    match copied {
                        Some(r) => parts.push(r),
                        None => {
                            if !parts.is_empty() {
                                parts.push(Region::Goto { target: cur });
                            }
                        }
                    }
                } else if !stop.contains(&cur)
                    || !self.sese_stop_chain_to_claimed_terminator(cur, stop, ctx)
                {
                    if !parts.is_empty() {
                        parts.push(Region::Goto { target: cur });
                    }
                } else {
                    // A stop member whose forward flow is a single-succ chain
                    // into an ALREADY-CONSUMED terminator: copy the chain
                    // inline. The restart-loop switch (jdk26 DecimalFormat
                    // guarded typeSwitch): the guard-pass body is a loop exit
                    // that flows ONLY to the shared areturn every case region
                    // absorbed — `break L1` would land after the loop where
                    // nothing remains and the body is lost. Normal loop exits
                    // chain to UNCLAIMED continuations and keep the Goto
                    // (inlining those rewrote breaks into returns and
                    // degraded while-cond loops, ThreadPoolExecutor).
                    let mut cstop: HashSet<usize> = stop.iter().copied().collect();
                    for &u in ctx.universe.iter() {
                        if !reach.contains(&u) {
                            cstop.insert(u);
                        }
                    }
                    match self.copy_walk(cur, &cstop, &ctx.top_groups, usize::MAX) {
                        Some(r) => parts.push(r),
                        None => {
                            if !parts.is_empty() {
                                parts.push(Region::Goto { target: cur });
                            }
                        }
                    }
                }
                break;
            }
            // Value-diamond fold: when `cur` roots a pre-folded pure-value
            // diamond (computed by the builder), collapse it — consume the
            // absorbed branch blocks and continue at the merge, whose input
            // stack already holds the folded ternary. This is what turns
            // boolean short-circuits (`a && b`, `a || b`) and `c ? a : b`
            // into expressions instead of structuring them as control-flow
            // ifs with empty branches (the milestone-3 parity with walk).
            // A block that is ALSO the exact start of a try group must be
            // structured as the try first — walk checks groups before folds.
            // Collapsing it as a value diamond skips the try entirely and
            // orphans the handler (URL.createURLStreamHandler: stage-1 string
            // switch dispatch folded, try [5,86) never fired, bare reflective
            // call without its catch -> unreported checked exceptions; a jdk11/17
            // corpus blocker). The diamond is re-folded inside the try body walk.
            let fold_blocked_by_group = (0..self.groups.len()).any(|gi| {
                self.groups[gi].start == self.cfg.blocks[cur].start
                    && self.groups[gi].end >= self.cfg.blocks[cur].end
                    && !self.handler_group.contains_key(&cur)
            });
            if let Some(&merge) = self.fold_root_to_merge.get(&cur) {
                if !fold_blocked_by_group {
                if let Some((_root, vis)) = self.fold_regions.get(&merge) {
                    if !self.results[cur].stmts.is_empty() {
                        parts.push(Region::Basic { block: cur });
                    }
                    for &v in vis.iter() {
                        ctx.consumed.insert(v);
                    }
                    ctx.consumed.insert(cur);
                    cur = merge;
                    last_via_goto = false;
                    continue;
                }
                }
            }
            let b = &self.cfg.blocks[cur];
            if b.ins.is_empty() {
                ctx.consumed.insert(cur);
                match b.succ.first().copied() {
                    Some(n) => {
                        cur = n;
                        last_via_goto = false;
                        continue;
                    }
                    None => break,
                }
            }

            // Loop header? Structure the natural loop, then continue at its
            // follow (the exit the loop post-dominates toward).
            // Try group starting exactly here? Reuse the tuned try builder
            // (body/handlers structured by walk over their sub-scopes; the
            // handler regions and finally duplication are intricate). Pick the
            // OUTERMOST group starting at cur (largest span); structure_try
            // handles nested groups internally.
            {
                let bs = self.cfg.blocks[cur].start;
                let be = self.cfg.blocks[cur].end;
                let group_here = (0..self.groups.len())
                    .filter(|&gi| {
                        self.groups[gi].start == bs
                            && self.groups[gi].end >= be
                            && !self.handler_group.contains_key(&cur)
                    })
                    .max_by_key(|&gi| self.groups[gi].end);
                // The group starts at a LOOP HEADER whose back edge lies
                // OUTSIDE the protected span (`for (;;) { try { ... }
                // catch { ... } ...retry... }` — jdk26
                // ClassValue.getFromHashMap): the loop is the enclosing
                // construct. Structuring the try first consumes the
                // header and the back edge gets duplicated (3× unrolled
                // copies, lost retry loop, missing return). Let the
                // loop-header branch below win; the body walk re-finds
                // this group at its start. try{while} keeps group-first:
                // its back edge is INSIDE the protected span.
                //
                // FINALLY-WRAP exception: `try { while (true) { ... }
                // finally { ... } }` (jdk26 KQueuePort
                // EventHandlerTask.run) — javac splits the protection
                // around the inlined finally copies, so the FIRST range
                // ends mid-loop and the back edges sit outside it: the
                // ClassValue span shape. What separates the two is the
                // handler's TAIL: ClassValue's catch continues the
                // retry (the loop must own the header), while a finally
                // handler ends in a pending rethrow and never returns
                // to the header. Fingerprint: an `any`-range of this
                // group's handler set whose end extends INTO the handler
                // block — the protection blankets the whole loop up to
                // the handler entry (KQueuePort range 171..211 over
                // handler 209). Loop-first there nests the try inside
                // the loop and walks the loop's break-path finally copy
                // (pollTask()==null fall-out) as the post-loop
                // continuation — a second threadExit after the
                // all-paths-return while(true): 无法访问的语句 x3 trees.
                let finally_wrap = |gi: usize| -> bool {
                    let g = &self.groups[gi];
                    self.cfg.exc_ranges.iter().any(|r| {
                        r.catch_type.is_none()
                            && g.handlers.iter().any(|(h2, t2)| t2.is_none() && *h2 == r.handler)
                            && r.start < r.handler
                            && self.cfg.block_at(r.handler).is_some_and(|hb| {
                                r.end > self.cfg.blocks[hb].start
                                    && r.end < self.cfg.blocks[hb].end.saturating_add(8)
                            })
                    })
                };
                // The finally-wrap fingerprint overrides BOTH loop-first
                // rules (back-edge-outside-span and exc-retry-header):
                // KQueuePort's loop is also an exc-retry loop (the
                // InterruptedException handler's `goto 16` continue), and
                // the wrap still belongs outside it — structure_try's
                // body walk re-structures the loop at the header via
                // sese_exc_retry_headers (the parseBest mechanism). The
                // typed-catch retry shapes (parseBest DateTimeException,
                // Process.waitFor) have no `any` handler and never trip
                // the fingerprint.
                let group_here = group_here.filter(|&gi| {
                    !ctx.loop_headers.contains(&cur)
                        || finally_wrap(gi)
                        || (!ctx.exc_retry_headers.contains(&cur)
                            && !self.cfg.blocks[cur].pred.iter().any(|&p| {
                                p != cur
                                    && ctx.idom.dominates(cur, p)
                                    && (self.cfg.blocks[p].end <= self.groups[gi].start
                                        || self.cfg.blocks[p].start >= self.groups[gi].end)
                            }))
                });
                if let Some(gi) = group_here {
                    let outer_universe = ctx.universe.clone();
                    let mut claimed = ctx.consumed.clone();
                    let try_region =
                        self.structure_try(gi, &ctx.universe, &outer_universe, &mut claimed, stop);
                    ctx.consumed = claimed;
                    parts.push(try_region);
                    let gend = self.groups[gi].end;
                    // structure_try absorbs a trailing terminator sitting at
                    // exactly g.end into the body (the protected-range areturn
                    // javac excludes; ALL its preds are body blocks). It is
                    // now claimed and lives INSIDE the try; letting the
                    // continuation search below pick it (it passes
                    // start >= gend + consumed + is_term) re-emits the body's
                    // own return after the try (ObjectStreamClass
                    // getDeclaredSUID: trailing `return Long.valueOf(...)`
                    // duplicated outside, real `return null` tail lost).
                    // A shared terminator at gend that the CATCH also copied
                    // (nestedTry) has a handler pred, is not absorbed, and
                    // must still be re-copied here — hence the all-preds-
                    // in-body mirror of the absorption rule.
                    let absorbed_tail = self.cfg.block_at(gend).filter(|&b| {
                        matches!(
                            self.results[b].term,
                            Term::Return(_) | Term::Throw(_)
                        ) && self.results[b].stmts.is_empty()
                            && !self.handler_group.contains_key(&b)
                            && !self.cfg.blocks[b].pred.is_empty()
                            && self.cfg.blocks[b]
                                .pred
                                .iter()
                                .all(|p| self.body_group.get(p) == Some(&gi))
                    });
                    // Handler-flow-only blocks (the handler's private tail,
                    // e.g. the synchronized monitorexit-rethrow `aload t;
                    // athrow`) are NOT shared method tails: the is_term
                    // exception below exists for tails the NORMAL path also
                    // reaches (nestedTry's lost return). Copying a
                    // handler-only pending-rethrow after the try leaks
                    // `throw <pending>;` into the normal flow (jdk26
                    // LambdaFormEditor.putInCache: 未报告的异常错误Throwable).
                    let hf_after = self.handler_flow_only(gi);
                    // Blocks are in ascending-start order. The scan STOPS at
                    // the first stop (barrier) block: when the block right
                    // after the span is the enclosing loop's exit, the flow
                    // LEAVES this scope there (the try body's Goto resolved
                    // to break) — continuing at some later non-stop block
                    // pulls post-exit code into the loop body, whose
                    // duplicated return then trips body_done and strands the
                    // exit's own tail (jdk26 Future.resultNow: the normal
                    // finally-if + `return result` after the retry loop went
                    // missing — 缺少返回语句).
                    let mut next: Option<usize> = None;
                    let dbg_next = std::env::var("JCDC_DBG_SWF").is_ok();
                    for nb in self.cfg.blocks.iter() {
                        if nb.start < gend {
                            continue;
                        }
                        if dbg_next {
                            eprintln!("NEXTSCAN gend={} nb={} start={} absorbed={} hf={} univ={} stop={} handler={} consumed={} term={}",
                                gend, nb.id, nb.start, Some(nb.id) == absorbed_tail,
                                hf_after.contains(&nb.id), ctx.universe.contains(&nb.id),
                                stop.contains(&nb.id), self.handler_group.contains_key(&nb.id),
                                ctx.consumed.contains(&nb.id),
                                matches!(self.results[nb.id].term, crate::builder::Term::Return(_) | crate::builder::Term::Throw(_)));
                        }
                        if Some(nb.id) == absorbed_tail || hf_after.contains(&nb.id) {
                            continue;
                        }
                        if !ctx.universe.contains(&nb.id) {
                            continue;
                        }
                        if stop.contains(&nb.id) {
                            break;
                        }
                        let is_term = matches!(
                            self.results[nb.id].term,
                            Term::Return(_) | Term::Throw(_)
                        );
                        // A handler block is normally skipped (it belongs to
                        // the try's catch/finally), but a handler that is a
                        // shared return/throw is the method tail the finally
                        // copy jumps to — the normal (try-completes) path
                        // must still return it (nestedTry's lost return).
                        // THIS group's own handler is never that shared
                        // tail: its catch region already absorbed it, and
                        // re-walking it duplicated the handler as top-level
                        // statements after the try (jdk11
                        // ThreadedSeedGenerator.run: `Exception e = null;
                        // throw new InternalError(.., e);` after the
                        // catch-that-throws — 无法访问的语句).
                        if self.handler_group.contains_key(&nb.id)
                            && (!is_term || self.handler_group.get(&nb.id) == Some(&gi))
                        {
                            continue;
                        }
                        if ctx.consumed.contains(&nb.id) && !is_term {
                            continue;
                        }
                        next = Some(nb.id);
                        break;
                    }
                    match next {
                        // A consumed shared terminator right after the try is
                        // the method/region tail return that the catch also
                        // used; copy it inline so the normal (try-completes)
                        // path still returns (fixes nestedTry's lost return).
                        Some(nb) if ctx.consumed.contains(&nb) => {
                            parts.push(Region::CopyStmts { block: nb });
                            break;
                        }
                        Some(nb) => {
                            // Continue at the try's forward continuation even
                            // when it is not in this region's `reach` set: a
                            // try body reaches its tail through inlined/duplicated
                            // finally copies, so reachable_within (normal succ
                            // only) can miss the post-finally return block. The
                            // block is unconsumed and forward (start >= gend), so
                            // structuring it is monotone and recovers the tail
                            // return (nestedTry's `return sb.toString()`).
                            cur = nb;
                            last_via_goto = false;
                            continue;
                        }
                        None => break,
                    }
                }
            }
            let is_header =
                ctx.loop_headers.contains(&cur) && !self.handler_group.contains_key(&cur);
            if is_header {
                let members = ctx.loop_members.get(&cur).cloned().unwrap_or_default();
                // exits = EVERY member's out-edges leaving the loop: the
                // break-resolution set (a `break outer` from deep in the body
                // targets one of these; resolve_goto maps a Goto to the
                // OUTERMOST loop whose exits contain it -> labeled break).
                // A SWITCH-dispatch header never has a condition fall-out:
                // its out-of-loop target edges are per-case break stubs, so
                // extending exits cannot degrade a while-cond
                // classification (top-tested `while (i < n)` headers keep
                // their raw exits — String.contentEquals).
                let natural_follow_empty =
                    matches!(self.results[cur].term, crate::builder::Term::Switch { .. });
                let mut exits: Vec<usize> = Vec::new();
                for &m in members.iter() {
                    for &s in &self.cfg.blocks[m].succ {
                        if !members.contains(&s) && ctx.universe.contains(&s) && !exits.contains(&s)
                        {
                            exits.push(s);
                        }
                    }
                }
                // Bottom-tested loops ONLY (for(;;) / restart shapes): a
                // `break L` out of a deep switch compiles to a per-case
                // empty `goto TAIL` stub, so the member-boundary exits are
                // the stubs and the REAL continuation sits one hop behind
                // them — invisible to body_stop (the case region walks
                // through the stub and consumes the tail) and to the
                // post-loop continuation (stubs are consumed with
                // preds==header and filtered). See through pure-jump stubs
                // so exits name the semantic destination (jdk26
                // Pattern.sequence: `goto 609` stubs → the `if (head ==
                // null) return end; .. return head;` tail —
                // 缺少返回语句). Top-tested loops (String.contentEquals
                // `while (i < n)`) keep the raw exits: their header
                // fall-out exit drives the while-cond classification and
                // extending it degraded the loop to `while (true)` and
                // lost the post-loop return.
                if natural_follow_empty {
                    let mut extended: Vec<usize> = Vec::new();
                    for &x in exits.iter() {
                        let mut cur_x = x;
                        let mut guard = 0;
                        while matches!(self.results[cur_x].term, crate::builder::Term::Goto)
                            && self.results[cur_x].stmts.is_empty()
                            && self.cfg.blocks[cur_x].succ.len() == 1
                            && guard < 8
                        {
                            let n = self.cfg.blocks[cur_x].succ[0];
                            if members.contains(&n)
                                || !ctx.universe.contains(&n)
                                || ctx.loop_stack.contains(&n)
                                || ctx.loop_headers.contains(&n)
                            {
                                break;
                            }
                            cur_x = n;
                            guard += 1;
                        }
                        if !extended.contains(&cur_x) {
                            extended.push(cur_x);
                        }
                    }
                    exits = extended;
                }
                exits.sort_by_key(|e| self.cfg.blocks[*e].start);
                // natural_follow = the HEADER's own exits (the condition's
                // fall-out): where straight-line flow continues after the
                // loop. Other members' exits are body breaks and must NOT be
                // the continuation -- exits.first() over all members could be
                // a far-away early-return the body region never reaches,
                // silently dropping the post-loop tail (Integer.toString).
                let mut natural_follow: Vec<usize> = Vec::new();
                for &s in &self.cfg.blocks[cur].succ {
                    if !members.contains(&s) && ctx.universe.contains(&s) {
                        natural_follow.push(s);
                    }
                }
                // A top-tested Cond header's own fall-out is a LIVE normal
                // completion no matter what the body does: body_done (every
                // body path returns/continues) must not suppress it
                // (jdk11/17/26 AbstractPoller$Request.awaitResult: the
                // wait-retry body is all-continue, so the body_done veto
                // dropped the `!interrupted ? result : interrupt+result`
                // epilogue the condition falls into — 缺少返回语句 ×3
                // trees, latent behind OCSPResponse's FLOW mask). The
                // bottom-tested fallback below keeps the veto: for(;;)/
                // do-while exits are break landings the veto legitimately
                // owns (TempFileHelper.create's in-try areturn re-emission).
                let cond_exit_live = !natural_follow.is_empty()
                    && matches!(self.results[cur].term, Term::Cond { .. });
                if natural_follow.is_empty() {
                    // Bottom-tested loop (do-while): the header is the body
                    // entry whose only successor is inside the loop; the
                    // natural exit hangs off the condition member instead.
                    natural_follow = exits.clone();
                }
                natural_follow.sort_by_key(|e| self.cfg.blocks[*e].start);
                // Body: structure from the header; the loop's exits and the
                // enclosing stop bound it. The header is the body entry and is
                // NOT in the body stop (the back edge re-targets it -> Goto ->
                // `continue` at conversion).
                let mut body_stop: HashSet<usize> = stop.iter().copied().collect();
                body_stop.extend(exits.iter().copied());
                let header = cur;
                // Structure the body from the header, but drop the header from
                // loop_headers for the duration so the body region does not
                // re-detect it as a loop (infinite recursion). The back edge
                // (a body block whose succ is the header) hits the consumed
                // check -> Goto{header} -> `continue` at conversion.
                ctx.loop_headers.remove(&header);
                ctx.loop_stack.push(header);
                // Sync the walk-facing loops_stack so any walk-based sub-builder
                // reused inside the body (structure_try / structure_switch)
                // resolves a back-edge to this SESE loop header as a
                // `continue` (Goto{header}) instead of re-walking it as a new
                // nested loop (the catch-handler `while(true)` duplication).
                self.loops_stack.push(header);
                // The loop tail (back-edge source -> header) is reachable
                // from the header WITHOUT stepping on an exit only through
                // the body, so reachable_within(header, body_stop) always
                // contains every member; blocks of divergent shapes (a
                // pre-loop init guard whose branches rejoin after the loop,
                // Integer.toString blk9/10) are correctly NOT members. Pass
                // this exact set as the body sub-scope so nested copy_walks
                // (which bound their region by reachable_within) cannot lose
                // the post-loop tail.
                let body_scope = reachable_within(self.cfg, header, &body_stop);
                let body = self.sese_region_with_scope(header, &body_stop, body_scope, ctx);
                self.loops_stack.pop();
                ctx.loop_stack.pop();
                // A body that cannot complete normally (both arms of its
                // tail check inline the loop's terminator exits — the
                // finally-retry dual-throw shape, jdk11 ObjectInputStream
                // .readSerialData) makes the post-loop continuation
                // unreachable (无法访问的语句): emit the loop and stop.
                let handler_exits: Vec<usize> = exits
                    .iter()
                    .copied()
                    .filter(|e| self.is_handler(*e))
                    .collect();
                // Mirrors conv's break resolutions: a Goto to a loop exit
                // or to any block that cannot reach back to the header
                // converts to `break` — the loop is escapable.
                fn region_has_break_goto(
                    r: &Region,
                    s: &Structurer,
                    header: usize,
                    exits: &[usize],
                    members: &HashSet<usize>,
                ) -> bool {
                    let esc = |t: usize| {
                        if t == header || exits.contains(&t) {
                            return t != header;
                        }
                        // A jump onto another MEMBER is an internal
                        // landing (an inner construct's break/merge whose
                        // statements render mid-body — TempFileHelper
                        // .create's inner generatePath loop exit
                        // `goto 28`); it never leaves THIS loop, so it
                        // cannot make the loop completable.
                        if members.contains(&t) {
                            return false;
                        }
                        // A forward escape onto a shared return/throw
                        // terminator is NOT a break: conversion inlines
                        // the terminator at the arrival (if-follow inline
                        // or RawGoto term-copy), so the path completes
                        // abruptly right here (TempFileHelper.create's SE
                        // catch `if (dir != tmpdir) <goto throw-e>` — the
                        // old esc made body_done miss the non-completing
                        // for(;;) and the chain re-emitted an in-try
                        // areturn after the loop — 无法访问的语句 x2).
                        !matches!(
                            s.results[t].term,
                            crate::builder::Term::Return(_) | crate::builder::Term::Throw(_)
                        ) && !crate::structure::can_reach_cfg(s.cfg, t, header, 4096)
                    };
                    match r {
                        Region::Goto { target } => esc(*target),
                        Region::Seq(v) => v
                            .iter()
                            .any(|x| region_has_break_goto(x, s, header, exits, members)),
                        Region::If { then_r, else_r, .. } => {
                            region_has_break_goto(then_r, s, header, exits, members)
                                || region_has_break_goto(else_r, s, header, exits, members)
                        }
                        Region::Loop { body, .. } => {
                            region_has_break_goto(body, s, header, exits, members)
                        }
                        Region::Try { body, catches, .. } => {
                            region_has_break_goto(body, s, header, exits, members)
                                || catches.iter().any(|(_, _, cr)| {
                                    region_has_break_goto(cr, s, header, exits, members)
                                })
                        }
                        Region::Switch { cases, default, .. } => {
                            cases
                                .iter()
                                .any(|(_, cr)| region_has_break_goto(cr, s, header, exits, members))
                                || default
                                    .as_ref()
                                    .map(|d| region_has_break_goto(d, s, header, exits, members))
                                    .unwrap_or(false)
                        }
                        _ => false,
                    }
                }
                // A `break` inside the body means the loop CAN complete
                // normally: the post-loop follow is reachable through it
                // and must still be structured. region_terminates_ex is
                // Goto-blind (conservatively false for Goto parts), but a
                // body that absorbed an exit-landing return tail
                // (awaitTermination's `var7 = false; unlock; return var7;`
                // return-false path became the in-body continuation of the
                // header try) looks terminating while the state-test break
                // escapes — suppressing natural_follow there stranded the
                // return-true tail after the loop (缺少返回语句, jdk11/17
                // ThreadPoolExecutor.awaitTermination).
                // Loop-aware completion: a Goto back to the header is a
                // `continue` — abrupt, and it never lands past the loop —
                // so it counts as terminating HERE (the FAE retry catch of
                // TempFileHelper.create's for(;;); region_terminates_ex
                // cannot know the header).
                fn region_done_or_continues(
                    r: &Region,
                    s: &Structurer,
                    handler_exits: &[usize],
                    header: usize,
                ) -> bool {
                    match r {
                        Region::Goto { target } => {
                            *target == header
                                || crate::structure::region_terminates_ex(
                                    r,
                                    s.results,
                                    handler_exits,
                                )
                        }
                        Region::Seq(v) => v
                            .last()
                            .map(|x| region_done_or_continues(x, s, handler_exits, header))
                            .unwrap_or(false),
                        Region::If { then_r, else_r, .. } => {
                            region_done_or_continues(then_r, s, handler_exits, header)
                                && region_done_or_continues(else_r, s, handler_exits, header)
                        }
                        Region::Try { body, catches, .. } => {
                            region_done_or_continues(body, s, handler_exits, header)
                                && catches.iter().all(|(_, _, c)| {
                                    region_done_or_continues(c, s, handler_exits, header)
                                })
                        }
                        other => crate::structure::region_terminates_ex(
                            other,
                            s.results,
                            handler_exits,
                        ),
                    }
                }
                let body_done = region_done_or_continues(&body, self, &handler_exits, header)
                    && !region_has_break_goto(&body, self, header, &exits, &members);
                if std::env::var("JCDC_DBG_SESE").is_ok() {
                    eprintln!("BODYDONE header={} done={} term={} brk={} exits={:?} body={:#?}",
                        header, body_done,
                        region_done_or_continues(&body, self, &handler_exits, header),
                        region_has_break_goto(&body, self, header, &exits, &members),
                        exits, body);
                }
                if is_header {
                    ctx.loop_headers.insert(header);
                }
                for &m in members.iter() {
                    ctx.consumed.insert(m);
                }
                let mut body = body;
                if std::env::var("JCDC_NO_MATEXIT").is_err() {
                    // The header's own out-of-member successors are the
                    // NATURAL exits (the while-cond fall-out / bottom-test
                    // exit): the parent region renders them ONCE after the
                    // Loop. Materializing them inside the body rotated
                    // while-cond loops into while(true)+copied-break
                    // (TempFileHelper/HttpURLConnection clinit churn).
                    let mut natural: HashSet<usize> = self.cfg.blocks[header]
                        .succ
                        .iter()
                        .copied()
                        .filter(|x| !members.contains(x) && *x != header)
                        .collect();
                    // SESE's computed natural_follow is ALSO parent-owned
                    // continuation (it may differ from the header's raw
                    // succs — bottom-tested/exit-derived follows): splicing
                    // it copied UnixPath.normalize's whole join-and-return
                    // continuation into a break arm (nf=[36], 缺少返回语句
                    // x2 trees).
                    natural.extend(natural_follow.iter().copied());
                    self.materialize_content_exits(
                        &mut body,
                        header,
                        &exits,
                        &members,
                        &natural,
                        &ctx.universe,
                        &ctx.loop_stack,
                        &ctx.loop_headers,
                        &ctx.top_groups,
                        stop,
                        &reach,
                        &ctx.consumed,
                        natural_follow.is_empty(),
                    );
                }
                parts.push(Region::Loop { header, body: Box::new(body), members: members.clone(), exits: exits.clone() });
                // Continue after the loop at the header's natural exit (if it
                // is within this region's reach and not an enclosing stop).
                // A consumed candidate whose preds are ALL the header can
                // only have been emitted INSIDE the body (the header's
                // switch/if dispatched it — the restart loop's natural exits
                // ARE the case targets); hoisting it re-emits the first
                // case's body after the loop (jdk26 DecimalFormat
                // `Long l = ...` tail). A consumed candidate with other
                // preds is the genuine shared follow (Class.methodToString
                // `if (c) return X; else { loop }`) and keeps the loop-top
                // consumed policy below.
                let header_id = cur;
                // Two-level loop exits: `break LOOP` often compiles to a
                // dedicated `goto TAIL` stub, so the member-boundary exit
                // is the STUB, not the real continuation. When a stub exit
                // was consumed by the body walk (the switch case's Goto
                // resolved against it) and chains forward — through further
                // consumed single-succ stubs — to an unconsumed non-member
                // block, THAT block is the true post-loop follow (jdk26
                // Pattern.sequence: exits {goto-609 stubs, throw} all
                // consumed, the `if (head == null) return end; .. return
                // head;` tail stranded → 缺少返回语句).
                // Gate: ONLY when every candidate exit was consumed by the
                // body walk — the deep-switch break-stub shape (Pattern
                // .sequence: all exits are per-case `goto TAIL` stubs the
                // case regions absorbed, and the shared TAIL behind them is
                // the true continuation). A normal loop leaves its header
                // fall-out unconsumed; chain-walking it anyway degraded
                // String.contentEquals's `while (i < n)` classification and
                // dropped the post-loop `return true`.
                let all_consumed = !natural_follow.is_empty()
                    && natural_follow.iter().all(|f| ctx.consumed.contains(f));
                if std::env::var("JCDC_DBG_SESE").is_ok() && all_consumed {
                    eprintln!("CHAINWALK header={} nf={:?} succs={:?} cons49={:?}", header_id,
                        natural_follow,
                        natural_follow.iter().map(|f| self.cfg.blocks[*f].succ.clone()).collect::<Vec<_>>(),
                        natural_follow.iter().map(|f| ctx.consumed.contains(f)).collect::<Vec<_>>());
                }
                let natural_follow: Vec<usize> = if all_consumed {
                    natural_follow
                        .into_iter()
                        .map(|x| {
                            let mut cur_x = x;
                            let mut guard = 0;
                            while ctx.consumed.contains(&cur_x)
                                && self.cfg.blocks[cur_x].succ.len() == 1
                                && guard < 16
                            {
                                let n = self.cfg.blocks[cur_x].succ[0];
                                if ctx.consumed.contains(&n)
                                    || stop.contains(&n)
                                    || members.contains(&n)
                                    || ctx.loop_stack.contains(&n)
                                    || ctx.loop_headers.contains(&n)
                                {
                                    break;
                                }
                                cur_x = n;
                                guard += 1;
                            }
                            cur_x
                        })
                        .collect::<Vec<_>>()
                } else {
                    natural_follow
                };
                let natural_follow = natural_follow
                    .into_iter()
                    .filter(|f| {
                        // A top-tested Cond header's own fall-out stays the
                        // continuation even when the body walk consumed it
                        // (AbstractPoller$Request.awaitResult: the epilogue
                        // rode into the body as the inner retry loop's
                        // follow; dropping it left the condition-fall path
                        // falling off the method — 缺少返回语句 ×3). The
                        // restart-loop case-target policy only owns
                        // unconditional (for(;;)/Goto) headers.
                        cond_exit_live
                            || !ctx.consumed.contains(f)
                            || !self.cfg.blocks[*f]
                                .pred
                                .iter()
                                .all(|&p| p == header_id)
                    })
                    .collect::<Vec<_>>();
                if std::env::var("JCDC_DBG_SESE").is_ok() {
                    eprintln!("LOOPFOLLOW header={} exits={:?} natural_follow={:?} consumed_nf={:?}",
                        header_id, exits, natural_follow,
                        natural_follow.iter().map(|f| ctx.consumed.contains(f)).collect::<Vec<_>>());
                }
                if body_done && !cond_exit_live {
                    ctx.depth -= 1;
                    return match parts.len() {
                        0 => Region::Empty,
                        1 => parts.into_iter().next().unwrap(),
                        _ => Region::Seq(parts),
                    };
                }
                let follow_pick = match natural_follow.first().copied() {
                    // No `!consumed` gate: a follow already consumed by a
                    // sibling branch (the shared single-return block after
                    // `if (c) return X; else { loop }`, Class.methodToString)
                    // is handled by the loop-top consumed policy — a shared
                    // Return/Throw gets CopyStmts (inlined at this arrival),
                    // a header becomes `continue`, anything else copy_walk/
                    // Goto. Gating on !consumed silently dropped the else
                    // path's return (missing-return compile error; walk
                    // keeps the tail).
                    //
                    // body_done vetoes UNLESS the header's own condition
                    // fall-out is live (cond_exit_live): a top-tested
                    // while's condition exit is a normal completion even
                    // when every body path continues/returns
                    // (AbstractPoller$Request.awaitResult). The veto stays
                    // for the bottom-tested fallback's in-try areturn exits
                    // (the shared terminator CopyStmts policy re-emitted
                    // `return Files.createDirectory(..)` after the
                    // non-completing for(;;) — TempFileHelper.create
                    // 无法访问的语句 x2 trees).
                    Some(f) if (!body_done || cond_exit_live)
                        && !stop.contains(&f)
                        && reach.contains(&f) => Some(f),
                    _ => None,
                };
                let follow_pick = if body_done && !cond_exit_live { None } else { follow_pick.or_else(|| {
                    // Stranded break landing: an exit some in-body
                    // `break L` targeted but neither the body nor any
                    // follow consumed (a guarded-pattern case body sits
                    // outside the switch dispatch — jdk26
                    // NumberFormat.format's `case BigInteger bi when
                    // bi.bitLength() < 64` break-L1 landed on nothing:
                    // natural_follow was empty and the bi.longValue()
                    // body block was never structured — 缺少返回语句 x2
                    // methods).
                    // Pre-stub-filter candidate set for the
                    // shared-collector test (see the walk-side twin in
                    // structure.rs next_after_loop).
                    let claim_cands: HashSet<usize> = exits
                        .iter()
                        .copied()
                        .filter(|e| {
                            !ctx.consumed.contains(e)
                                && !stop.contains(e)
                                && ctx.universe.contains(e)
                                && reach.contains(e)
                                && !self.is_handler(*e)
                                && *e != header_id
                        })
                        .collect();
                    let mut cands: Vec<usize> = exits
                        .iter()
                        .copied()
                        .filter(|e| {
                            !ctx.consumed.contains(e)
                                && !stop.contains(e)
                                && ctx.universe.contains(e)
                                && reach.contains(e)
                                && !self.is_handler(*e)
                                && *e != header_id
                                // Continue-stub exits (statement-free jump
                                // chains back into an enclosing loop) are
                                // conditional break arms of the inner loop,
                                // already resolved inside the body — walking
                                // one as the continuation re-emits the jump
                                // unconditionally (jdk11
                                // FutureTask.removeWaiter `continue retry`
                                // stubs became an unconditional continue
                                // after the inner while — 无法访问的语句 on
                                // the tail return, x3 trees).
                                && !ctx.loop_stack.iter().any(|h| {
                                    h != e
                                        && self.is_stmt_free_chain_to_block(*e, *h)
                                        && !self.stub_chain_claims_continuation(
                                            *e,
                                            *h,
                                            &claim_cands,
                                        )
                                })
                        })
                        .collect();
                    cands.sort_by_key(|e| self.cfg.blocks[*e].start);
                    cands.first().copied()
                }) };
                match follow_pick {
                    Some(f) => {
                        cur = f;
                        continue;
                    }
                    None => {
                        // An exit that is an ENCLOSING loop's barrier must
                        // be materialized as a Goto (the labeled break of
                        // the enclosing loop); silently ending the body
                        // makes the inner loop's normal completion
                        // re-enter the outer (jdk11
                        // FutureTask.removeWaiter — see the walk-side
                        // twin in structure.rs).
                        if !body_done {
                            let barrier_exit = exits
                                .iter()
                                .copied()
                                .filter(|e| {
                                    stop.contains(e)
                                        && !ctx.loop_stack.contains(e)
                                        && ctx.universe.contains(e)
                                        && !self.is_handler(*e)
                                })
                                .min_by_key(|e| self.cfg.blocks[*e].start);
                            if let Some(e) = barrier_exit {
                                parts.push(Region::Goto { target: e });
                            }
                        }
                        break;
                    }
                }
            }

            ctx.consumed.insert(cur);
            match self.results[cur].term.clone() {
                Term::Cond { cond } => {
                    let succs = self.cfg.blocks[cur].succ.clone();
                    if succs.len() != 2 {
                        parts.push(Region::Basic { block: cur });
                        match succs.first().copied() {
                            Some(n) => {
                                cur = n;
                                continue;
                            }
                            None => break,
                        }
                    }
                    let (fall, taken) = (succs[0], succs[1]);
                    // Follow = true immediate post-dominator; when None (the
                    // branches diverge to different terminals) fall back to
                    // convergent_merge, which recovers a shared loop tail
                    // (Legacy6 `if (a==2 && b==2) break outer;`) but REFUSES
                    // candidates dominating a branch target — ancestor
                    // confluentes like `if (A || B) fixup;` (Integer.toString)
                    // keep follow=None so the branches are walked naturally
                    // and the re-reached continuation is duplicated by
                    // copy_walk (walk-parity shape).
                    let follow = self
                        .sese_ipdom(ctx, cur)
                        .filter(|f| ctx.universe.contains(f) && !stop.contains(f))
                        .or_else(|| self.live_merge(ctx, &[taken, fall], stop))
                        // A follow that IS one of the branch targets only
                        // works when the OTHER target flows to it — that
                        // branch completes normally and falls through
                        // (empty branch). When the sibling instead exits
                        // (return/throw) or escapes to a stop, the target
                        // is shared-tail code: choosing it as follow
                        // leaves the tail unstructured after the sibling
                        // consumes it (Fin/Long$LongCache: lost
                        // `cache = archivedCache;` tail => final
                        // double-assign in the branch copy / "variable f
                        // might not have been initialized"). follow=None
                        // keeps the tail inside the branch (walk parity).
                        .filter(|f| {
                            ![taken, fall].contains(f)
                                || [taken, fall].iter().any(|&t| {
                                    t != *f
                                        && (stop.contains(&t)
                                            || self.reaches_within(ctx, t, *f, stop))
                                })
                        })
                        // A shared TERMINATOR as follow means some branch
                        // never completes normally — it must be a branch that
                        // flows to f within this region's stop set. When a
                        // target instead escapes to a stop (a jump OUT: the
                        // enclosing if-follow / loop exit), f post-dominates
                        // only through the other branch, and choosing it
                        // elides that branch's terminator as "natural
                        // fall-through" while re-emitting it AFTER the if —
                        // jdk17 String(byte[],int,int,Charset) lost the
                        // LATIN1 fast-path `return;` (goto 839 = shared
                        // ctor-exit) inside `else { assigns }`, double-
                        // assigning the final fields ("variable value might
                        // already have been assigned") and blocking every
                        // jdk17 corpus family. follow=None keeps the return
                        // inside the branch (walk-parity).
                        .filter(|f| {
                            !matches!(self.results[*f].term, Term::Return(_) | Term::Throw(_))
                                || [taken, fall].iter().all(|&t| {
                                    stop.contains(&t)
                                        || ctx.consumed.contains(&t)
                                        || self.reaches_within(ctx, t, *f, stop)
                                })
                        })
                        // The convergent shortcut result gets the same two
                        // screens as the live_merge result: a branch-target
                        // follow needs a sibling route (reaches) and a
                        // shared-terminator follow needs every target to
                        // flow to it. (Empirically census-neutral; the
                        // stronger all_routes_via variant of screen #1 is
                        // documented-FAILED in memory
                        // ocsp-sese-follow-diagnosis — it trades OCSPResponse
                        // against BasicImageReader/keytool codegen cliffs.)
                        .or_else(|| self.convergent_merge(ctx, &[taken, fall], stop))
                        .filter(|f| {
                            ![taken, fall].contains(f)
                                || [taken, fall].iter().any(|&t| {
                                    t != *f
                                        && (stop.contains(&t)
                                            || self.reaches_within(ctx, t, *f, stop))
                                })
                        })
                        .filter(|f| {
                            !matches!(self.results[*f].term, Term::Return(_) | Term::Throw(_))
                                || [taken, fall].iter().all(|&t| {
                                    stop.contains(&t)
                                        || ctx.consumed.contains(&t)
                                        || self.reaches_within(ctx, t, *f, stop)
                                })
                        });
                    // FALSE-MERGE RECONCILIATION against the walk-side
                    // picker: a branch-target follow is exactly the class
                    // immediate_postdom's successor-candidate rejection
                    // was hardened against (OCSPResponse's parked
                    // UNSPECIFIED block — its sibling's values[reason]
                    // route bypasses it into the post-flow; the walk
                    // renders the golden arm-exclusive copies via this
                    // rejection). When the walk picker disagrees with the
                    // SESE resolvers, defer to it: adopt its confluence
                    // (BasicImageReader's `map!=null && MAP_ALL` chain —
                    // the shared else-arm block is a false merge whose
                    // real confluence is the third-conjunct test) or
                    // reject to None when it finds no merge at all. The
                    // walk's own gates (is_fall, same_body, group-owned
                    // exemption, stmt-free stubs, depth-capped bypass
                    // probe, big-tail exception) come along verbatim.
                    let recon_enabled = std::env::var("JCDC_NO_RECON").is_err();
                    let follow = match follow {
                        Some(f) if recon_enabled && (f == taken || f == fall)
                            // Switch-case territory keeps its own follow
                            // discipline: walk's picker REJECTS the case
                            // epilogue targets on purpose so each arm gets
                            // per-arrival try copies, while SESE parks them
                            // under the confluence bar (keytool doCommands'
                            // 28-pred TWR epilogue — deferring to the walk
                            // picker there re-armed the 12x copy storm,
                            // try 语句的代码过长 x525).
                            && self.switch_depth == 0
                            // Many-pred tail confluences are owned by the
                            // SESE copy/confluence-bar machinery for the
                            // same reason.
                            && !self.shared_tail_confluence(f)
                            // Only MULTI-PRED targets can be false merges:
                            // the pathology is arm CONTENT shared by both
                            // branch routes (OCSPResponse's UNSPECIFIED
                            // block has the two range-check arms as preds;
                            // BasicImageReader's channel-open else-arm has
                            // both conjunct tests). A SINGLE-pred taken
                            // target is an ordinary if-else-if chain arm
                            // entry whose parking IS the dispatch shape
                            // (keytool doCommands' command bodies — every
                            // reconciliation there, even pure-stub
                            // adoption, re-armed the epilogue copy storm).
                            && self.cfg.blocks[f].pred.len() >= 2
                            // AND the parked target must carry STATEMENTS:
                            // parking a statement-free test head is the
                            // healthy if-else-if chain flattening (keytool
                            // doGenCert's dispatch chain), not arm-content
                            // parking — there is nothing to cross.
                            && !self.results[f].stmts.is_empty()
                            // AND the sibling must actually BYPASS the
                            // parked target (a normal-completing route
                            // into its post-flow — the crossing that
                            // breaks the empty-arm contract). Without a
                            // bypass the parking is sound (every sibling
                            // route flows through the target and the empty
                            // arm falls into its emission correctly) and
                            // the SESE choice stands (keytool doPrintEntry
                            // dispatch parking).
                            && ![taken, fall].iter().any(|&t| {
                                t != f
                                    && (stop.contains(&t)
                                        || self.all_routes_via(ctx, t, f, stop))
                            }) =>
                        {
                            let w = self.postdom_ipdom(&ctx.universe, cur);
                            match w {
                                Some(x) if x != f
                                    && self.results[x].stmts.is_empty()
                                    && self.results[x].out_stack.is_empty()
                                    && self.cfg.blocks[x].succ.len() == 1
                                    && matches!(
                                        self.results[x].term,
                                        Term::Goto | Term::Fallthrough
                                    ) =>
                                {
                                    // Adopt only PURE GOTO/FALL STUB
                                    // confluentes: in the arm-content
                                    // parking pathology the false merge's
                                    // real continuation is the transparent
                                    // stub past the parked statements
                                    // (OCSPResponse cur=5: w=9, the
                                    // `goto 166` stub after the parked
                                    // UNSPECIFIED block — adopting it puts
                                    // the parked block in BOTH arms as
                                    // per-arrival copies, the golden
                                    // walk-parity shape). Statement-bearing
                                    // or test-head confluentes are
                                    // case-arm/dispatch entries whose
                                    // adoption dissolves the SESE
                                    // parked-arm architecture (keytool
                                    // doCommands: every broader adoption
                                    // re-armed the epilogue copy storm,
                                    // try 语句的代码过长 x524-540).
                                    if std::env::var("JCDC_DBG_WPD").is_ok() {
                                        eprintln!("WPD cur={} taken={} fall={} f={} ADOPT-STUB w={}", cur, taken, fall, f, x);
                                    }
                                    if ctx.universe.contains(&x)
                                        && !stop.contains(&x)
                                        && !ctx.consumed.contains(&x)
                                        && !ctx.loop_stack.contains(&x)
                                        // The stub must not be a loop
                                        // CONTINUE trampoline (backward
                                        // goto into a header): adopting it
                                        // as the follow re-routes the chain
                                        // into loop machinery (keytool
                                        // doGenCert's `goto 5` back-edge
                                        // stub).
                                        && !self.cfg.blocks[x].succ.iter().any(|&s| {
                                            ctx.loop_headers.contains(&s)
                                                && self.cfg.blocks[s].start
                                                    <= self.cfg.blocks[x].start
                                        })
                                    {
                                        Some(x)
                                    } else {
                                        Some(f)
                                    }
                                }
                                // w == None (walk rejects every confluence),
                                // w == f, or w not a pure stub: keep the
                                // SESE choice — walk's rejection/selection
                                // cues its own guard-walk architecture, not
                                // SESE's parked-follow + confluence-bar one.
                                _ => Some(f),
                            }
                        }
                        other => other,
                    };
                    let mut bstop: HashSet<usize> = stop.iter().copied().collect();
                    if let Some(f) = follow {
                        bstop.insert(f);
                    }
                    let then_r = self.sese_region(taken, &bstop, ctx);
                    let else_r = self.sese_region(fall, &bstop, ctx);
                    // Value-diamond / ternary: both branches are pure single
                    // pushes that merge — reuse the builder's folded merge so
                    // the ternary is recovered (parity with walk).
                    let ternary = self.sese_ternary(cur, taken, fall, follow, &then_r, &else_r);
                    parts.push(Region::If {
                        block: cur,
                        cond,
                        then_r: Box::new(then_r),
                        else_r: Box::new(else_r),
                        follow,
                        ternary,
                    });
                    match follow {
                        // A follow already consumed by the case regions (the
                        // shared terminator tail each case absorbed/duplicated)
                        // must not continue here — that would re-emit it after
                        // the switch.
                        Some(f) if reach.contains(&f) && !ctx.consumed.contains(&f) => {
                            cur = f;
                            last_via_goto = false;
                            continue;
                        }
                        _ => break,
                    }
                }
                Term::Goto | Term::Fallthrough => {
                    parts.push(Region::Basic { block: cur });
                    last_via_goto = matches!(self.results[cur].term, Term::Goto);
                    match self.cfg.blocks[cur].succ.first().copied() {
                        Some(n) => {
                            cur = n;
                            continue;
                        }
                        None => break,
                    }
                }
                Term::Return(_) | Term::Throw(_) => {
                    parts.push(Region::Basic { block: cur });
                    break;
                }
                Term::Switch { selector, targets } => {
                    // Reuse the tuned switch region builder (case fall-through,
                    // per-case epilogues). Case bodies are structured by walk
                    // over the case sub-scope; `consumed` is passed as the
                    // claimed set so SESE and the switch share consumption.
                    //
                    // follow = ipdom, else the convergent merge of all case
                    // targets. Inside a loop the shared tail (`++i`, back-edge)
                    // post-dominates the dispatch only at the virtual exit, so
                    // ipdom is None; convergent_merge recovers the tail as the
                    // follow so every case `break`s to it and it is structured
                    // ONCE after the switch (EnumSwitch — otherwise the first
                    // case swallows the tail as `++i; continue` and the rest
                    // spin forever).
                    let succs = self.cfg.blocks[cur].succ.clone();
                    if std::env::var("JCDC_DBG_GOTO").is_ok() {
                        eprintln!("SWFOLLOW cur={} ipdom={:?} vx={} succs={:?} stop={:?}",
                            cur, ctx.ipdom.get(&cur), ctx.vx, succs, stop);
                    }
                    let follow = self
                        .sese_ipdom(ctx, cur)
                        .filter(|f| !stop.contains(f))
                        // A switch inside a loop body whose cases all end in `break`
                        // merges at the loop increment (a body_stop exit),
                        // and a throwing default kills the plain ipdom —
                        // live_merge recovers it (ObjectStreamClass
                        // .computeFieldOffsets: fall-through cases and
                        // dangling break labels).
                        .or_else(|| self.live_merge(ctx, &succs, stop))
                        .or_else(|| self.convergent_merge(ctx, &succs, stop))
                        // Copied/shared-tail regions: the confluence lives
                        // in `stop` (enclosing flow owns it) — still the
                        // logical follow for case `break` resolution (jdk11
                        // Calendar.createCalendar catch-copy switch).
                        .or_else(|| self.switch_stop_confluence(cur, &ctx.universe, stop))
                        // Loop-tail epilogue: cases break the switch into a
                        // shared tail that flows back to the header; the
                        // forward resolvers refuse header-reaching paths
                        // (jdk26 Pattern.sequence lost the epilogue and the
                        // post-loop tail -> 缺少返回语句).
                        .or_else(|| self.loop_tail_switch_follow(ctx, cur, stop));
                    if std::env::var("JCDC_DBG_SWF").is_ok() {
                        eprintln!("SWF-RESOLVED cur={} follow={:?}", cur, follow);
                    }
                    // CROSSING follow: see the walk-side twin in
                    // structure.rs — a nested switch's stop-confluence
                    // belongs to an enclosing construct; region-level
                    // follow stays None so conversion binds the case-tail
                    // goto to the OWNER (labeled break), while `stop`
                    // still bounds the case walks at the confluence.
                    // Bindable exception (see switch_follow_bindable):
                    // when every route past the switch lands on the
                    // confluence anyway, rebuild with the follow so the
                    // arms get plain breaks (ClassPrinterImpl.toYaml/toXml
                    // 无法访问的语句 x2 trees).
                    let crossing = match follow {
                        Some(f) if stop.contains(&f) && self.switch_depth > 0 => Some(f),
                        _ => None,
                    };
                    let region_follow = match crossing {
                        Some(_) => None,
                        None => follow,
                    };
                    let mut claimed = ctx.consumed.clone();
                    self.switch_depth += 1;
                    let mut sw = self.structure_switch(
                        cur,
                        selector.clone(),
                        &targets,
                        &ctx.universe,
                        stop,
                        region_follow,
                        &ctx.top_groups,
                        &mut claimed,
                    );
                    if let Some(f) = crossing {
                        // See the walk-side twin: the post-switch
                        // continuation of THIS scope must already land on
                        // `f` (earlier parts abruptly complete, or the
                        // chain continues exactly at `f`).
                        let cont_dead = parts
                            .last()
                            .map(|p| crate::structure::region_terminates(p, self.results))
                            .unwrap_or(false);
                        let cont_is_f = reach.contains(&f);
                        let cont_via_case_break = self
                            .case_arm_ctx
                            .last()
                            .map(|&(head, ef, pat)| head == entry && pat && ef == Some(f))
                            .unwrap_or(false);
                        let bindable = (cont_dead || cont_is_f || cont_via_case_break)
                            && self.switch_follow_bindable(&sw, cur, &targets, f);
                        if std::env::var("JCDC_DBG_SWF").is_ok() {
                            eprintln!("SWBIND-SESE cur={} f={} cont_dead={} cont_is_f={} cont_case={} bindable={}",
                                cur, f, cont_dead, cont_is_f, cont_via_case_break, bindable);
                        }
                        if bindable {
                            let mut claimed2 = ctx.consumed.clone();
                            sw = self.structure_switch(
                                cur,
                                selector,
                                &targets,
                                &ctx.universe,
                                stop,
                                Some(f),
                                &ctx.top_groups,
                                &mut claimed2,
                            );
                            claimed = claimed2;
                        }
                    }
                    self.switch_depth -= 1;
                    ctx.consumed = claimed;
                    parts.push(sw);
                    if std::env::var("JCDC_DBG_GOTO").is_ok() {
                        eprintln!("SWCONT cur={} follow={:?} in_reach={:?} in_stop={:?} consumed={:?}",
                            cur, follow, follow.map(|f| reach.contains(&f)),
                            follow.map(|f| stop.contains(&f)), ctx.consumed);
                    }
                    match follow {
                        Some(f) if reach.contains(&f) => {
                            cur = f;
                            last_via_goto = false;
                            continue;
                        }
                        _ => break,
                    }
                }
                Term::Jsr | Term::Ret => {
                    parts.push(Region::Basic { block: cur });
                    break;
                }
            }
        }
        ctx.depth -= 1;
        match parts.len() {
            0 => Region::Empty,
            1 => parts.into_iter().next().unwrap(),
            _ => Region::Seq(parts),
        }
    }

    /// Recover a folded value-diamond (ternary) at a Cond whose two branches
    /// are pure single-value pushes merging at `follow`. Mirrors walk's ternary
    /// detection so `x = c ? a : b;` is preserved. Returns None when not a
    /// pure diamond (the common control-flow case).
    fn sese_ternary(
        &self,
        cur: usize,
        taken: usize,
        fall: usize,
        follow: Option<usize>,
        then_r: &Region,
        else_r: &Region,
    ) -> Option<(Expr, Expr)> {
        let merge = follow?;
        // Both branches must be a single pure block that falls into `merge`
        // leaving exactly one value, and `merge` must be a builder-folded
        // diamond merge.
        if !self.diamond_merges.contains(&merge) {
            return None;
        }
        let pure_one = |r: &Region, blk: usize| -> Option<Expr> {
            match r {
                Region::Basic { block } if *block == blk => {
                    let res = &self.results[blk];
                    if res.stmts.is_empty() && res.out_stack.len() == 1 {
                        match &res.term {
                            Term::Fallthrough => Some(res.out_stack[0].clone()),
                            Term::Goto if self.cfg.blocks[blk].succ == vec![merge] => {
                                Some(res.out_stack[0].clone())
                            }
                            _ => None,
                        }
                    } else {
                        None
                    }
                }
                Region::Empty => {
                    // Branch jumps straight to the merge (empty side).
                    let res = &self.results[blk];
                    if res.stmts.is_empty() && res.out_stack.len() == 1 {
                        Some(res.out_stack[0].clone())
                    } else {
                        None
                    }
                }
                _ => None,
            }
        };
        let tv = pure_one(then_r, taken)?;
        let fv = pure_one(else_r, fall)?;
        let _ = cur;
        Some((tv, fv))
    }
}
