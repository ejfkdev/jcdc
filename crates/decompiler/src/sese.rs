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
            // Collect every back-edge source for h, then walk predecessors
            // (normal AND exception) within the universe until reaching h.
            let mut stack: Vec<usize> = Vec::new();
            for &u in universe.iter() {
                if self.cfg.blocks[u].succ.contains(&h) && (u != h || self.cfg.blocks[h].succ.contains(&h)) {
                    if members.insert(u) {
                        stack.push(u);
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

        let mut ctx = SeseCtx {
            universe,
            idom,
            ipdom,
            vx,
            loop_headers,
            loop_members,
            consumed: HashSet::new(),
            loop_stack: Vec::new(),
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
        let floor = targets
            .iter()
            .map(|&t| self.cfg.blocks[t].start as usize)
            .max()
            .unwrap();
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
    fn reaches_within(&self, ctx: &SeseCtx, from: usize, target: usize, stop: &HashSet<usize>) -> bool {
        if from == target {
            return true;
        }
        let mut seen = HashSet::new();
        let mut stack = vec![from];
        seen.insert(from);
        while let Some(c) = stack.pop() {
            for &s in &self.cfg.blocks[c].succ {
                if s == target {
                    return true;
                }
                if stop.contains(&s) || ctx.loop_stack.contains(&s) {
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
        ctx.depth += 1;
        let deep = ctx.depth > 400;
        // Blocks this region may consume: reachable from entry without stepping
        // on `stop`. Anything outside is a boundary -> Goto.
        let reach = reachable_within(self.cfg, entry, stop);
        let mut parts: Vec<Region> = Vec::new();
        let mut cur = entry;
        let mut guard = 0usize;
        loop {
            guard += 1;
            if deep || guard > ctx.universe.len() * 4 + 64 {
                break;
            }
            if stop.contains(&cur) || !ctx.universe.contains(&cur) || !reach.contains(&cur) {
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
                    // Shared terminator: duplicate inline (no outgoing flow).
                    parts.push(Region::CopyStmts { block: cur });
                } else if ctx.loop_stack.contains(&cur) {
                    // Back-edge to an enclosing loop header: a `continue`
                    // (resolved at conversion). NEVER copy_walk it — that would
                    // re-walk the whole loop as a nested duplicate.
                    if !parts.is_empty() {
                        parts.push(Region::Goto { target: cur });
                    }
                } else if !stop.contains(&cur) {
                    // Shared non-terminator reached from a divergent sibling
                    // (e.g. the continuation after `if (A && B) return X;`):
                    // copy_walk re-structures it inline, COPY_DEPTH-bounded so
                    // nested shared chains stay monotone (no divergence). Falls
                    // back to a Goto when the cap is hit or it loops back.
                    match self.copy_walk(cur, stop, &[], usize::MAX) {
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
            if let Some(&merge) = self.fold_root_to_merge.get(&cur) {
                if let Some((_root, vis)) = self.fold_regions.get(&merge) {
                    if !self.results[cur].stmts.is_empty() {
                        parts.push(Region::Basic { block: cur });
                    }
                    for &v in vis.iter() {
                        ctx.consumed.insert(v);
                    }
                    ctx.consumed.insert(cur);
                    cur = merge;
                    continue;
                }
            }
            let b = &self.cfg.blocks[cur];
            if b.ins.is_empty() {
                ctx.consumed.insert(cur);
                match b.succ.first().copied() {
                    Some(n) => {
                        cur = n;
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
                if let Some(gi) = group_here {
                    let outer_universe = ctx.universe.clone();
                    let mut claimed = ctx.consumed.clone();
                    let try_region =
                        self.structure_try(gi, &ctx.universe, &outer_universe, &mut claimed);
                    ctx.consumed = claimed;
                    parts.push(try_region);
                    let gend = self.groups[gi].end;
                    let next = self.cfg.blocks.iter().find(|nb| {
                        nb.start >= gend
                            && ctx.universe.contains(&nb.id)
                            && !stop.contains(&nb.id)
                            && !self.handler_group.contains_key(&nb.id)
                            && (!ctx.consumed.contains(&nb.id)
                                || matches!(
                                    self.results[nb.id].term,
                                    Term::Return(_) | Term::Throw(_)
                                ))
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
                            cur = nb.id;
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
                let body = self.sese_region(header, &body_stop, ctx);
                self.loops_stack.pop();
                ctx.loop_stack.pop();
                if is_header {
                    ctx.loop_headers.insert(header);
                }
                for &m in members.iter() {
                    ctx.consumed.insert(m);
                }
                parts.push(Region::Loop { header, body: Box::new(body), members, exits: exits.clone() });
                // Continue after the loop at its primary exit (if it is within
                // this region's reach and not an enclosing stop).
                match exits.first().copied() {
                    Some(f) if !stop.contains(&f) && reach.contains(&f) && !ctx.consumed.contains(&f) => {
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
                    // True follow = immediate post-dominator. When that is None
                    // the branches diverge to different terminals — but they may
                    // still reconverge on a shared in-region continuation while
                    // one path leaves (a loop `break` -> exit, or return/throw).
                    // convergent_merge recovers that shared follow (the loop
                    // tail after `if (a==2 && b==2) break outer;`), without
                    // which the tail folds into one branch and the other falls
                    // through empty -> infinite loop (Legacy6).
                    let follow = self
                        .sese_ipdom(ctx, cur)
                        .filter(|f| ctx.universe.contains(f) && !stop.contains(f))
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
                        Some(f) if reach.contains(&f) && !ctx.consumed.contains(&f) => {
                            cur = f;
                            continue;
                        }
                        _ => break,
                    }
                }
                Term::Goto | Term::Fallthrough => {
                    parts.push(Region::Basic { block: cur });
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
                        .or_else(|| self.convergent_merge(ctx, &succs, stop));
                    let mut claimed = ctx.consumed.clone();
                    let sw = self.structure_switch(
                        cur,
                        selector,
                        &targets,
                        &ctx.universe,
                        stop,
                        follow,
                        &[],
                        &mut claimed,
                    );
                    ctx.consumed = claimed;
                    parts.push(sw);
                    match follow {
                        Some(f) if reach.contains(&f) && !ctx.consumed.contains(&f) => {
                            cur = f;
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
