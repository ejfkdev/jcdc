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
    compute_dominators, compute_postdominators, reachable_within, DomInfo, Region, Structurer,
};

/// Per-method precomputation for the SESE decomposition.
struct SeseCtx {
    universe: HashSet<usize>,
    idom: DomInfo,
    /// block -> immediate post-dominator (== vx when only the virtual exit).
    ipdom: HashMap<usize, usize>,
    /// sentinel virtual-exit id.
    vx: usize,
    /// loop headers (back-edge targets that dominate the source).
    loop_headers: HashSet<usize>,
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
        // A catch-and-retry handler has NO normal-flow preds, so the
        // dominator tree roots it and its `goto header` back edge is
        // invisible (jdk11 ObjectStreamClass.getInheritableMethod:
        // `while (defCl != null) { try { ..; break; } catch (NSME) {
        // defCl = super; } }` unrolled into nested try copies on BOTH
        // paths). Treat the handler as dominated via its protected
        // block: handler -> h with h dominating the protected block is
        // a back edge, and the handler joins the loop.
        let mut exc_back_sources: HashMap<usize, Vec<usize>> = HashMap::new();
        for e in &self.cfg.exc_edges {
            if !(universe.contains(&e.from) && universe.contains(&e.to)) {
                continue;
            }
            let c = e.to;
            if !self.cfg.blocks[c].pred.is_empty() {
                continue; // normally reachable: real dominators apply
            }
            for &h in &self.cfg.blocks[c].succ {
                if h != c && universe.contains(&h) && idom.dominates(h, e.from) {
                    loop_headers.insert(h);
                    exc_back_sources.entry(h).or_default().push(c);
                }
            }
        }
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
        let mut ctx = SeseCtx {
            universe,
            idom,
            ipdom,
            vx,
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
                || ctx.loop_headers.contains(&t)
            {
                continue;
            }
            if targets
                .iter()
                .all(|&o| o == t || self.reaches_within(ctx, o, t, stop))
            {
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
            // A loop header is never a merge candidate: a branch that jumps
            // to it is a `continue` (the back edge fires on the NEXT
            // iteration), not a fall-through confluence. During a body walk
            // the header is not yet consumed, so without this guard a pair of
            // continue-branches "merges" at the header or at each other
            // THROUGH the header, both branch regions elide to empty, and the
            // real tail runs unconditionally (StringUTF16.codePointCount
            // losing both `continue`s).
            if ctx.loop_headers.contains(&x) || ctx.loop_stack.contains(&x) {
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
                if stop.contains(&t) || ctx.consumed.contains(&t) {
                    continue;
                }
                if live
                    .iter()
                    .all(|&o| o == t || self.reaches_within(ctx, o, t, stop))
                {
                    return Some(t);
                }
            }
        }
        let mut best: Option<usize> = None;
        for &cand in ctx.universe.iter() {
            if ctx.consumed.contains(&cand)
                || ctx.loop_headers.contains(&cand)
                || ctx.loop_stack.contains(&cand)
            {
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
                    match self.copy_walk(cur, &cstop, &ctx.top_groups, usize::MAX) {
                        Some(r) => parts.push(r),
                        None => {
                            if !parts.is_empty() {
                                parts.push(Region::Goto { target: cur });
                            }
                        }
                    }
                } else if !parts.is_empty() {
                    parts.push(Region::Goto { target: cur });
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
                let group_here = group_here.filter(|&gi| {
                    !ctx.loop_headers.contains(&cur)
                        || !self.cfg.blocks[cur].pred.iter().any(|&p| {
                            p != cur
                                && ctx.idom.dominates(cur, p)
                                && (self.cfg.blocks[p].end <= self.groups[gi].start
                                    || self.cfg.blocks[p].start >= self.groups[gi].end)
                        })
                });
                if let Some(gi) = group_here {
                    let outer_universe = ctx.universe.clone();
                    let mut claimed = ctx.consumed.clone();
                    let try_region =
                        self.structure_try(gi, &ctx.universe, &outer_universe, &mut claimed);
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
                    let next = self.cfg.blocks.iter().find(|nb| {
                        let is_term = matches!(
                            self.results[nb.id].term,
                            Term::Return(_) | Term::Throw(_)
                        );
                        nb.start >= gend
                            && Some(nb.id) != absorbed_tail
                            && ctx.universe.contains(&nb.id)
                            && !stop.contains(&nb.id)
                            // A handler block is normally skipped (it belongs to
                            // the try's catch/finally), but a handler that is a
                            // shared return/throw is the method tail the finally
                            // copy jumps to — the normal (try-completes) path
                            // must still return it (nestedTry's lost return).
                            && (!self.handler_group.contains_key(&nb.id) || is_term)
                            && (!ctx.consumed.contains(&nb.id) || is_term)
                    });
                    match next {
                        // A consumed shared terminator right after the try is
                        // the method/region tail return that the catch also
                        // used; copy it inline so the normal (try-completes)
                        // path still returns (fixes nestedTry's lost return).
                        Some(nb) if ctx.consumed.contains(&nb.id) => {
                            parts.push(Region::CopyStmts { block: nb.id });
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
                            cur = nb.id;
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
                let mut exits: Vec<usize> = Vec::new();
                for &m in members.iter() {
                    for &s in &self.cfg.blocks[m].succ {
                        if !members.contains(&s) && ctx.universe.contains(&s) && !exits.contains(&s)
                        {
                            exits.push(s);
                        }
                    }
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
                if is_header {
                    ctx.loop_headers.insert(header);
                }
                for &m in members.iter() {
                    ctx.consumed.insert(m);
                }
                parts.push(Region::Loop { header, body: Box::new(body), members, exits: exits.clone() });
                // Continue after the loop at the header's natural exit (if it
                // is within this region's reach and not an enclosing stop).
                match natural_follow.first().copied() {
                    // No `!consumed` gate: a follow already consumed by a
                    // sibling branch (the shared single-return block after
                    // `if (c) return X; else { loop }`, Class.methodToString)
                    // is handled by the loop-top consumed policy — a shared
                    // Return/Throw gets CopyStmts (inlined at this arrival),
                    // a header becomes `continue`, anything else copy_walk/
                    // Goto. Gating on !consumed silently dropped the else
                    // path's return (missing-return compile error; walk
                    // keeps the tail).
                    Some(f) if !stop.contains(&f) && reach.contains(&f) => {
                        cur = f;
                        continue;
                    }
                    _ => break,
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
                        .or_else(|| self.convergent_merge(ctx, &[taken, fall], stop));
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
                        Some(f) if reach.contains(&f) => {
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
                        .or_else(|| self.convergent_merge(ctx, &succs, stop));
                    let mut claimed = ctx.consumed.clone();
                    let sw = self.structure_switch(
                        cur,
                        selector,
                        &targets,
                        &ctx.universe,
                        stop,
                        follow,
                        &ctx.top_groups,
                        &mut claimed,
                    );
                    ctx.consumed = claimed;
                    parts.push(sw);
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
