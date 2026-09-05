//! Control flow structuring: CFG of basic blocks → nested region tree.
//!
//! Strategy:
//! 1. Iterative dominator computation (Cooper-Harvey-Kennedy).
//! 2. Exception ranges grouped by (start, end) span → try regions carved out
//!    first; bodies and handlers are structured recursively.
//! 3. Inside each flow scope, walk blocks from the entry:
//!    - loop header (back-edge target that dominates the source) → natural
//!      loop region,
//!    - conditional terminal → If region (branches structured up to the
//!      immediate post-dominator),
//!    - switch terminal → Switch region with per-case sub-scopes,
//!    - forward goto within scope → continue walking at the target,
//!    - edges that leave the scope → Goto nodes (resolved to
//!      break/continue/labels in the conversion pass).

use std::collections::{HashMap, HashSet, VecDeque};

use crate::block::Cfg;
use crate::builder::{BlockResult, SwitchTargets, Term};
use crate::expr::Expr;

// ---------------------------------------------------------------------------
// Dominators & flow queries
// ---------------------------------------------------------------------------

pub struct DomInfo {
    pub idom: Vec<usize>,
}

impl DomInfo {
    pub fn dominates(&self, a: usize, b: usize) -> bool {
        let n = self.idom.len();
        if a >= n || b >= n {
            return false;
        }
        let mut cur = b;
        let mut guard = 0;
        loop {
            if cur == a {
                return true;
            }
            let next = self.idom[cur];
            if next == cur || guard > n + 1 {
                return false;
            }
            guard += 1;
            cur = next;
        }
    }
}

pub fn reverse_postorder(cfg: &Cfg, entry: usize, universe: &HashSet<usize>) -> Vec<usize> {
    let mut visited = vec![false; cfg.blocks.len()];
    let mut out = Vec::new();
    if !universe.contains(&entry) {
        return out;
    }
    let mut stack: Vec<(usize, usize)> = vec![(entry, 0)];
    visited[entry] = true;
    while let Some((b, idx)) = stack.last_mut() {
        let b = *b;
        if *idx < cfg.blocks[b].succ.len() {
            let s = cfg.blocks[b].succ[*idx];
            *idx += 1;
            if !visited[s] && universe.contains(&s) {
                visited[s] = true;
                stack.push((s, 0));
            }
        } else {
            out.push(b);
            stack.pop();
        }
    }
    out.reverse();
    out
}

pub fn compute_dominators(cfg: &Cfg, universe: &HashSet<usize>, entry: usize) -> DomInfo {
    let n = cfg.blocks.len();
    let mut idom = vec![usize::MAX; n];
    if universe.contains(&entry) {
        idom[entry] = entry;
    }
    let rpo = reverse_postorder(cfg, entry, universe);
    let mut rpo_num = vec![usize::MAX; n];
    for (i, &b) in rpo.iter().enumerate() {
        rpo_num[b] = i;
    }
    let mut changed = true;
    while changed {
        changed = false;
        for &b in &rpo {
            if b == entry {
                continue;
            }
            let mut new_idom = usize::MAX;
            for &p in &cfg.blocks[b].pred {
                if rpo_num[p] == usize::MAX || idom[p] == usize::MAX {
                    continue;
                }
                new_idom = if new_idom == usize::MAX {
                    p
                } else {
                    intersect(new_idom, p, &idom, &rpo_num)
                };
            }
            if new_idom != usize::MAX && idom[b] != new_idom {
                idom[b] = new_idom;
                changed = true;
            }
        }
    }
    for i in 0..n {
        if idom[i] == usize::MAX {
            idom[i] = i;
        }
    }
    DomInfo { idom }
}

fn intersect(mut a: usize, mut b: usize, idom: &[usize], rpo_num: &[usize]) -> usize {
    let mut guard = 0;
    while a != b && guard < 1_000_000 {
        guard += 1;
        while rpo_num[a] > rpo_num[b] {
            a = idom[a];
        }
        while rpo_num[b] > rpo_num[a] {
            b = idom[b];
        }
    }
    a
}

/// Blocks normally reachable from `entry` without entering `stop`.
pub fn reachable_within(cfg: &Cfg, entry: usize, stop: &HashSet<usize>) -> HashSet<usize> {
    let mut seen = HashSet::new();
    if stop.contains(&entry) {
        return seen;
    }
    let mut q = VecDeque::new();
    q.push_back(entry);
    seen.insert(entry);
    while let Some(b) = q.pop_front() {
        for &s in &cfg.blocks[b].succ {
            if !stop.contains(&s) && seen.insert(s) {
                q.push_back(s);
            }
        }
    }
    seen
}

/// Immediate post-dominator of `entry` within `universe`, approximated as
/// the nearest reconvergence point: the block (other than entry) reachable
/// from ALL of entry's in-universe successors with the smallest total BFS
/// distance. Blocks whose in-universe successors are empty are exits.
pub fn immediate_postdom(cfg: &Cfg, universe: &HashSet<usize>, entry: usize) -> Option<usize> {
    let succs: Vec<usize> = cfg.blocks[entry]
        .succ
        .iter()
        .copied()
        .filter(|s| universe.contains(s))
        .collect();
    if succs.len() < 2 {
        return None;
    }
    // BFS distances from each successor. The entry block acts as a barrier:
    // paths that loop back through it do not constitute reconvergence.
    let mut dists: Vec<HashMap<usize, u32>> = Vec::with_capacity(succs.len());
    for &s0 in &succs {
        let mut d: HashMap<usize, u32> = HashMap::new();
        let mut q: VecDeque<(usize, u32)> = VecDeque::new();
        d.insert(s0, 0);
        q.push_back((s0, 0));
        while let Some((b, db)) = q.pop_front() {
            for &s in &cfg.blocks[b].succ {
                if s != entry && universe.contains(&s) && !d.contains_key(&s) {
                    d.insert(s, db + 1);
                    q.push_back((s, db + 1));
                }
            }
        }
        dists.push(d);
    }
    // Candidates: blocks present in all BFS maps (except entry itself), and
    // NOT a direct successor of entry. A direct successor is one of the
    // branches, never the merge: it is "reachable from all successors" only
    // because it reaches itself (distance 0). Rejecting it is the compound
    // `if (A || B) then;` fix (the `then` body is a successor that the BFS
    // heuristic otherwise picks over the true follow further out). Skipped for
    // self-loops (a loop header is its own successor; there the nearest
    // confluence is the loop exit and must stay).
    // Candidates: blocks present in all BFS maps (except entry itself).
    let mut best: Option<(u32, usize)> = None;
    for (&cand, &d0) in dists[0].iter() {
        if cand == entry {
            continue;
        }
        let mut total = d0;
        let mut ok = true;
        for d in &dists[1..] {
            match d.get(&cand) {
                Some(x) => total += x,
                None => {
                    ok = false;
                    break;
                }
            }
        }
        if ok {
            let better = match best {
                None => true,
                Some((bd, bc)) => {
                    total < bd || (total == bd && cfg.blocks[cand].start < cfg.blocks[bc].start)
                }
            };
            if better {
                best = Some((total, cand));
            }
        }
    }
    best.map(|(_, c)| c)
}

// ---------------------------------------------------------------------------
// Try groups
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct TryGroup {
    pub start: u16,
    pub end: u16,
    /// (handler pc, catch type) in exception-table order.
    pub handlers: Vec<(u16, Option<String>)>,
    pub ranges: Vec<usize>,
}

pub fn group_exceptions(cfg: &Cfg) -> Vec<TryGroup> {
    let mut groups: Vec<TryGroup> = Vec::new();
    for (ri, r) in cfg.exc_ranges.iter().enumerate() {
        if let Some(g) = groups.iter_mut().find(|g| g.start == r.start && g.end == r.end) {
            g.handlers.push((r.handler, r.catch_type.clone()));
            g.ranges.push(ri);
        } else {
            groups.push(TryGroup {
                start: r.start,
                end: r.end,
                handlers: vec![(r.handler, r.catch_type.clone())],
                ranges: vec![ri],
            });
        }
    }
    groups.sort_by_key(|g| (g.start, std::cmp::Reverse(g.end)));
    // javac splits one protected region into several exception ranges that
    // share identical handlers (e.g. around every `return` inside a
    // synchronized block). Merge adjacent such spans into one group so the
    // region structures as a single try. The handler's self-protection
    // range (start == handler pc) never merges into its own group.
    fn handler_key(g: &TryGroup) -> Vec<(u16, Option<String>)> {
        let mut v: Vec<(u16, Option<String>)> = g
            .handlers
            .iter()
            .map(|(h, t)| (*h, t.clone()))
            .collect();
        v.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
        v.dedup();
        v
    }
    loop {
        let mut merged_any = false;
        'outer: for i in 0..groups.len() {
            for j in (i + 1)..groups.len() {
                let (a, b) = if groups[i].start <= groups[j].start { (i, j) } else { (j, i) };
                if handler_key(&groups[a]) != handler_key(&groups[b]) {
                    continue;
                }
                if groups[b].start > groups[a].end.saturating_add(4) {
                    continue;
                }
                if groups[a].handlers.iter().any(|(h, _)| *h == groups[b].start) {
                    continue;
                }
                let new_start = groups[a].start.min(groups[b].start);
                let new_end = groups[a].end.max(groups[b].end);
                let mut ranges = groups[a].ranges.clone();
                ranges.extend(groups[b].ranges.iter().copied());
                groups[a].start = new_start;
                groups[a].end = new_end;
                groups[a].ranges = ranges;
                groups.remove(b);
                merged_any = true;
                break 'outer;
            }
        }
        if !merged_any {
            break;
        }
    }
    groups.sort_by_key(|g| (g.start, std::cmp::Reverse(g.end)));
    groups
}

// ---------------------------------------------------------------------------
// Region tree
// ---------------------------------------------------------------------------

#[derive(Debug)]
pub enum Region {
    /// Statements of one basic block; terminal handled by the enclosing region.
    Basic { block: usize },
    Seq(Vec<Region>),
    If {
        /// block carrying the conditional terminal
        block: usize,
        cond: Expr,
        /// taken (true) branch
        then_r: Box<Region>,
        /// fallthrough (false) branch
        else_r: Box<Region>,
        follow: Option<usize>,
        /// Folded value-diamond: (then value, else value) — both branches
        /// are pure expression pushes that merge on the operand stack.
        ternary: Option<(Expr, Expr)>,
    },
    Loop {
        header: usize,
        body: Box<Region>,
        members: HashSet<usize>,
        exits: Vec<usize>,
    },
    Switch {
        block: usize,
        selector: Expr,
        cases: Vec<(Vec<i64>, Region)>,
        default: Option<Box<Region>>,
        follow: Option<usize>,
    },
    Try {
        group_idx: usize,
        body: Box<Region>,
        /// (catch types [multi-catch merged], handler block, region) in table order
        catches: Vec<(Vec<String>, usize, Box<Region>)>,
    },
    /// Jump to a block outside the current region (resolved later).
    Goto { target: usize },
    /// Duplicate of an already-claimed pure block's statements (shared
    /// value block reached from multiple branches).
    CopyStmts { block: usize },
    Empty,
}

pub struct Structurer<'a> {
    pub cfg: &'a Cfg,
    pub results: &'a Vec<BlockResult>,
    /// Blocks whose operand stack was folded from a pure value diamond.
    pub diamond_merges: std::collections::HashSet<usize>,
    /// Folded diamond regions: merge block -> (root header, absorbed blocks).
    /// When the walk reaches a root header, the whole region collapses: the
    /// absorbed blocks are claimed and the walk continues at the merge.
    pub fold_regions: HashMap<usize, (usize, HashSet<usize>)>,
    /// Reverse index: root header -> merge block.
    pub fold_root_to_merge: HashMap<usize, usize>,
    /// Heads of shared-tail regions that were copy-walked into a scope
    /// (a RawGoto targeting one is natural fallthrough at conversion).
    pub copied_tails: HashSet<usize>,
    /// Headers of loops currently being structured (nesting barriers).
    pub loops_stack: Vec<usize>,
    /// Current `walk` recursion depth (hang guard for pathological methods
    /// whose shared-tail / branch decomposition does not converge).
    walk_depth: usize,
    pub groups: Vec<TryGroup>,
    /// Outermost group index owning each body block.
    pub body_group: HashMap<usize, usize>,
    /// Group index owning each handler head block.
    pub handler_group: HashMap<usize, usize>,
}

impl<'a> Structurer<'a> {
    /// Strip a trailing handler `Goto{t}` that merges into the post-try
    /// flow: t starts at/after the group end and is not a handler head.
    fn strip_handler_exit_goto(&self, r: &mut Region, end_pc: u16) {
        let ok = |t: usize| {
            self.cfg.blocks.get(t).map(|b| b.start >= end_pc).unwrap_or(false)
                && !self.is_handler(t)
        };
        match r {
            Region::Goto { target: t } if ok(*t) => *r = Region::Empty,
            Region::Seq(v) => {
                if let Some(last) = v.last_mut() {
                    self.strip_handler_exit_goto(last, end_pc);
                }
                if matches!(v.last(), Some(Region::Empty)) {
                    v.pop();
                }
            }
            Region::If { then_r, else_r, .. } => {
                self.strip_handler_exit_goto(then_r, end_pc);
                self.strip_handler_exit_goto(else_r, end_pc);
            }
            _ => {}
        }
    }

    /// First unclaimed non-handler block at or after `pc`.
    fn continuation_after(&self, pc: u16, universe: &HashSet<usize>, claimed: &HashSet<usize>) -> Option<usize> {
        self.cfg
            .blocks
            .iter()
            .find(|nb| {
                nb.start >= pc
                    && universe.contains(&nb.id)
                    && !claimed.contains(&nb.id)
                    && !self.is_handler(nb.id)
            })
            .map(|nb| nb.id)
    }
}

/// Strip a trailing `Goto{target}` from a region (at any tail position:
/// end of a sequence, or the tail of an if/else branch).
fn strip_trailing_goto_to(r: &mut Region, target: usize) {
    match r {
        Region::Goto { target: t } if *t == target => *r = Region::Empty,
        Region::Seq(v) => {
            if let Some(last) = v.last_mut() {
                strip_trailing_goto_to(last, target);
            }
            if matches!(v.last(), Some(Region::Empty)) {
                v.pop();
            }
        }
        Region::If { then_r, else_r, .. } => {
            strip_trailing_goto_to(then_r, target);
            strip_trailing_goto_to(else_r, target);
        }
        _ => {}
    }
}



/// Remove a trailing `Goto` to a sibling case head (Java fallthrough).
fn strip_fallthrough_goto(r: Region, heads: &HashSet<usize>) -> Region {
    match r {
        Region::Goto { target } if heads.contains(&target) => Region::Empty,
        Region::Seq(mut v) => {
            if let Some(last) = v.last() {
                if let Region::Goto { target } = last {
                    if heads.contains(target) {
                        v.pop();
                    }
                }
            }
            match v.len() {
                0 => Region::Empty,
                1 => v.pop().unwrap(),
                _ => Region::Seq(v),
            }
        }
        other => other,
    }
}

impl<'a> Structurer<'a> {
    pub fn new(cfg: &'a Cfg, results: &'a Vec<BlockResult>) -> Structurer<'a> {
        Self::with_diamonds(cfg, results, Default::default(), Default::default())
    }

    pub fn with_diamonds(
        cfg: &'a Cfg,
        results: &'a Vec<BlockResult>,
        diamond_merges: std::collections::HashSet<usize>,
        fold_regions: HashMap<usize, (usize, HashSet<usize>)>,
    ) -> Structurer<'a> {
        let groups = group_exceptions(cfg);
        let mut body_group = HashMap::new();
        let mut handler_group = HashMap::new();
        // Groups are sorted outer-first (start asc, end desc); later
        // (more nested) groups overwrite so each block maps to its
        // INNERMOST containing try body.
        for (gi, g) in groups.iter().enumerate() {
            for b in &cfg.blocks {
                if b.ins.is_empty() {
                    continue;
                }
                if b.start >= g.start && b.end <= g.end.max(g.start + 1) {
                    body_group.insert(b.id, gi);
                }
            }
            for (hpc, _) in &g.handlers {
                if let Some(hb) = cfg.block_at(*hpc) {
                    handler_group.entry(hb).or_insert(gi);
                }
            }
        }
        // Reverse index: fold root -> merge block.
        let mut fold_root_to_merge = HashMap::new();
        for (&merge, (root, _vis)) in &fold_regions {
            fold_root_to_merge.insert(*root, merge);
        }
        Structurer { cfg, results, groups, body_group, handler_group, diamond_merges, fold_regions, fold_root_to_merge, copied_tails: HashSet::new(), loops_stack: Vec::new(), walk_depth: 0 }
    }

    /// Immediate post-dominator of `entry` within `universe`. Delegates to the
    /// O(n) `immediate_postdom` (BFS nearest-confluence with successor-candidate
    /// rejection); kept as a `&mut self` method for call-site convenience.
    fn postdom_ipdom(&mut self, universe: &HashSet<usize>, entry: usize) -> Option<usize> {
        immediate_postdom(self.cfg, universe, entry)
    }

    /// True if `b` is an exception-handler head; such blocks must only be
    /// entered through their Try region, never through the normal flow.
    fn is_handler(&self, b: usize) -> bool {
        self.handler_group.contains_key(&b)
    }

    fn term(&self, b: usize) -> &Term {
        &self.results[b].term
    }

    /// Sub-scope for a branch walk: reachable region minus already-claimed
    /// blocks (e.g. the surrounding loop header reached via a back edge).
    fn sub_scope(
        &self,
        from: usize,
        universe: &HashSet<usize>,
        stop: &HashSet<usize>,
        claimed: &HashSet<usize>,
    ) -> HashSet<usize> {
        let mut sub = reachable_within(self.cfg, from, stop);
        // Restrict to the current region's universe so branch walks cannot
        // escape their scope (e.g. out of a try body into the loop header).
        // Blocks inside a try group whose start is in the universe are kept
        // even if their predecessors are outside: their flow is carved out
        // by the Try region and continues at the group's end.
        let mut eff = universe.clone();
        for &b in universe {
            if let Some(&gi) = self.body_group.get(&b) {
                let g = &self.groups[gi];
                for nb in &self.cfg.blocks {
                    if !nb.ins.is_empty()
                        && nb.start >= g.start
                        && nb.end <= g.end.max(g.start + 1)
                    {
                        eff.insert(nb.id);
                    }
                }
            }
        }
        sub.retain(|b| eff.contains(b) && !claimed.contains(b) && !self.is_handler(*b));
        sub.insert(from);
        sub
    }

    /// `cur` is a loop header if some in-universe, unclaimed predecessor has
    /// an edge back to `cur` and `cur` dominates it, or `cur` self-loops.
    fn is_loop_header(
        &self,
        cur: usize,
        universe: &HashSet<usize>,
        dom: &DomInfo,
    ) -> bool {
        for &p in &self.cfg.blocks[cur].pred {
            if p == cur {
                return true;
            }
            if universe.contains(&p) && dom.dominates(cur, p) {
                return true;
            }
        }
        false
    }

    /// Structure the whole method.
    pub fn structure_method(&mut self) -> Region {
        let universe: HashSet<usize> = self
            .cfg
            .blocks
            .iter()
            .filter(|b| !b.ins.is_empty())
            .map(|b| b.id)
            .collect();

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

        let mut claimed = HashSet::new();
        self.walk(self.cfg.entry, &universe, &HashSet::new(), &top_groups, &mut claimed, true)
    }

    /// Walk a scope starting at `entry`.
    ///
    /// * `universe` — blocks eligible for inclusion,
    /// * `stop`     — exclusive boundary,
    /// * `active`   — try groups that may start inside this scope,
    /// * `claimed`  — blocks consumed (in/out; pre-seed for loop bodies),
    /// * `allow_claimed_entry` — process `entry` even if already claimed
    ///   (loop headers are pre-claimed).
    fn walk(
        &mut self,
        entry: usize,
        universe: &HashSet<usize>,
        stop: &HashSet<usize>,
        active: &[usize],
        claimed: &mut HashSet<usize>,
        allow_claimed_entry: bool,
    ) -> Region {
        // Hang guard: pathological methods (e.g. keytool's `doCommands`, with
        // thousands of blocks and a long shared-tail chain) can drive unbounded
        // `walk` recursion. Cap the depth; beyond it, fall back to a Goto at
        // the entry so conversion still emits a valid jump instead of hanging
        // or overflowing the stack.
        if self.walk_depth >= 256 {
            return Region::Goto { target: entry };
        }
        self.walk_depth += 1;
        let r = self.walk_inner(entry, universe, stop, active, claimed, allow_claimed_entry);
        self.walk_depth -= 1;
        r
    }

    fn walk_inner(
        &mut self,
        entry: usize,
        universe: &HashSet<usize>,
        stop: &HashSet<usize>,
        active: &[usize],
        claimed: &mut HashSet<usize>,
        allow_claimed_entry: bool,
    ) -> Region {
        if !universe.contains(&entry) {
            return Region::Empty;
        }
        let dom = compute_dominators(self.cfg, universe, entry);
        // When the entry was pre-claimed (loop header), skip the loop-header
        // check for the entry block itself to avoid re-structuring the same
        // loop recursively.
        let entry_preclaimed = claimed.contains(&entry);
        if std::env::var("JCDC_DBG_IF").is_ok() {
            eprintln!("WALK entry={} universe={:?} stop={:?} claimed={:?}", entry, universe, stop, claimed);
        }
        let mut parts: Vec<Region> = Vec::new();
        let mut cur = entry;
        let mut first = true;
        let mut guard = 0usize;
        let _ = &mut first;
        loop {
            guard += 1;
            if guard > 100_000 || stop.contains(&cur) || !universe.contains(&cur) {
                break;
            }
            if claimed.contains(&cur) && !(first && allow_claimed_entry) {
                // Flow re-entered an already structured block.
                if std::env::var("JCDC_DBG_IF").is_ok() {
                    eprintln!("GOTO-CLAIMED cur={} entry={} parts={}", cur, entry, parts.len());
                }
                if !parts.is_empty() {
                    if self.is_terminator_block(cur) && !stop.contains(&cur) {
                        parts.push(Region::CopyStmts { block: cur });
                    } else if !stop.contains(&cur) && !self.loops_stack.contains(&cur) {
                        match self.copy_walk(cur, stop, active, entry) {
                            Some(r) => parts.push(r),
                            None => parts.push(Region::Goto { target: cur }),
                        }
                    } else {
                        parts.push(Region::Goto { target: cur });
                    }
                }
                break;
            }
            if !first && self.is_handler(cur) && active.is_empty() {
                // Handler head reached by a stray normal edge; it belongs to
                // its Try region.
                break;
            }
            first = false;
            let b = &self.cfg.blocks[cur];
            if b.ins.is_empty() {
                match b.succ.first().copied() {
                    Some(n) => {
                        cur = n;
                        continue;
                    }
                    None => break,
                }
            }

            // Try group starting exactly here? Match by span (the block may
            // belong to a more deeply nested group in body_group); active
            // lists are ordered outer-first so the first match is the
            // outermost group starting here.
            let group_here = active
                .iter()
                .find(|&&gi| {
                    self.groups[gi].start == b.start
                        && self.groups[gi].end >= b.end
                        && !self.handler_group.contains_key(&cur)
                })
                .copied();
            if let Some(gi) = group_here {
                let outer_universe = universe.clone();
                let try_region = self.structure_try(gi, universe, &outer_universe, claimed);
                parts.push(try_region);
                let gend = self.groups[gi].end;
                let next = self.cfg.blocks.iter().find(|nb| {
                    nb.start >= gend
                        && universe.contains(&nb.id)
                        && !stop.contains(&nb.id)
                        && !claimed.contains(&nb.id)
                        && !self.is_handler(nb.id)
                });
                match next {
                    Some(nb) => {
                        cur = nb.id;
                        continue;
                    }
                    None => break,
                }
            }

            // Loop header? (skip for a pre-claimed entry: that loop is the
            // one we are currently structuring)
            let at_preclaimed_entry = entry_preclaimed && cur == entry && parts.is_empty();
            if !at_preclaimed_entry && self.is_loop_header(cur, universe, &dom) {
                let loop_r = self.structure_loop(cur, universe, stop, active, claimed, &dom);
                let next = self.next_after_loop(&loop_r, universe, stop, claimed);
                let loop_exits = match &loop_r {
                    Region::Loop { exits, .. } => exits.clone(),
                    _ => Vec::new(),
                };
                parts.push(loop_r);
                match next {
                    Some(n) => {
                        cur = n;
                        continue;
                    }
                    None => {
                        // The loop exits into a block this walk cannot
                        // continue at (claimed by a sibling branch or out
                        // of the universe). When that block is a shared
                        // terminator (return/throw), copy it here so this
                        // path does not silently fall through.
                        for &e in &loop_exits {
                            if !stop.contains(&e) && self.is_terminator_block(e) {
                                parts.push(Region::CopyStmts { block: e });
                                break;
                            }
                        }
                        break;
                    }
                }
            }

            // Folded diamond root: collapse the whole region — claim the
            // absorbed blocks and continue at the merge. The folded ternary
            // already lives in the merge's input stack.
            if let Some(&merge) = self.fold_root_to_merge.get(&cur) {
                if let Some((_root, vis)) = self.fold_regions.get(&merge) {
                    if !self.results[cur].stmts.is_empty() {
                        parts.push(Region::Basic { block: cur });
                    }
                    claimed.extend(vis.iter().copied());
                    claimed.insert(merge);
                    claimed.insert(cur);
                    if std::env::var("JCDC_DBG_IF").is_ok() {
                        eprintln!("FOLD-COLLAPSE root={} merge={}", cur, merge);
                    }
                    cur = merge;
                    // The merge itself must still be processed (it is now
                    // claimed, so allow it explicitly on the next iteration).
                    first = false;
                    // Process the merge block in this same walk: temporarily
                    // allowed because we just claimed it; jump back through
                    // the loop top with the claimed-entry exception.
                    // (Handled below by processing `merge` directly.)
                    // Continue the loop; the claimed check at top would
                    // break, so instead process merge via a sub-walk splice:
                    // simplest is to unclaim merge and let normal flow claim
                    // it.
                    claimed.remove(&merge);
                    continue;
                }
            }

            claimed.insert(cur);
            if std::env::var("JCDC_DBG_CLAIM").is_ok() {
                eprintln!("CLAIM blk={} entry={} term_is_cond={}", cur, entry, matches!(self.term(cur), Term::Cond{..}));
            }
            match self.term(cur).clone() {
                Term::Cond { cond } => {
                    let succs = b.succ.clone();
                    if succs.len() != 2 {
                        // Degenerate conditional (both branches jump to the
                        // same block, e.g. javac 7's empty `continue`):
                        // emit the statements and walk on into the single
                        // successor.
                        parts.push(Region::Basic { block: cur });
                        match succs.first().copied() {
                            Some(nxt)
                                if universe.contains(&nxt)
                                    && !stop.contains(&nxt)
                                    && !claimed.contains(&nxt) =>
                            {
                                cur = nxt;
                                continue;
                            }
                            _ => break,
                        }
                    }
                    let (fall, taken) = (succs[0], succs[1]);
                    let mut pd = self.postdom_ipdom(universe, cur);
                    // A shared return/throw block is a poor If-follow: the
                    // branch that flows into it should carry its own copy of
                    // the terminator, and jumps past it from the other
                    // branch stay natural fallthrough. Only treat it as the
                    // follow when BOTH branches land on it (the If truly
                    // merges there).
                    if let Some(p) = pd {
                        if self.is_terminator_block(p) && p != taken && p != fall {
                            pd = None;
                        }
                    }

                    // Appendix fold: when the post-dominator is unwalkable
                    // (None or claimed), the value-diamond continuation
                    // between here and the enclosing barrier block M is an
                    // "appendix". Fold it into this If's follow so the walk
                    // continues at M instead of emitting raw Gotos into
                    // already-claimed merge blocks.
                    let mut follow = pd;
                    let follow_walkable = follow
                        .map(|f| {
                            universe.contains(&f)
                                && !stop.contains(&f)
                                && !claimed.contains(&f)
                        })
                        .unwrap_or(false);
                    // Never fold an appendix at a pre-claimed loop header:
                    // the stop set there is the loop exit, and the header's
                    // branch-out must stay a loop exit, not an If follow.
                    if !follow_walkable && !at_preclaimed_entry {
                        let m = self.appendix_target(cur, universe, stop, claimed);
                        if std::env::var("JCDC_DBG_IF").is_ok() {
                            eprintln!("COND cur={} pd={:?} unwalkable appendix->{:?}", cur, pd, m);
                        }
                        if let Some(m) = m {
                            follow = Some(m);
                        }
                    }
                    let mut bstop = stop.clone();
                    if let Some(f) = follow {
                        bstop.insert(f);
                    }

                    // Chained boolean/ternary: both branch targets lead
                    // (through pure value-push blocks) to a common merge
                    // whose input stack was folded into ternaries during
                    // block building. The true merge is the end of the
                    // pure-value tail chain (the post-dominator may be a
                    // push block itself when the diamond carries trailing
                    // values). Skip the scaffolding and continue at the merge.
                    let mut diamond_jump: Option<usize> = None;
                    {
                        // Candidate merges: nearest block reachable from BOTH
                        // branches (true confluence), then the taken-side
                        // pure chain end, then the post-dominator.
                        let mut cands: Vec<usize> = Vec::new();
                        {
                            // Deterministic candidate order (HashSet
                            // iteration varies per process).
                            let mut dms: Vec<usize> = self
                                .diamond_merges
                                .iter()
                                .copied()
                                .filter(|dm| {
                                    *dm != cur && universe.contains(dm) && !stop.contains(dm)
                                })
                                .collect();
                            dms.sort_unstable_by_key(|b| self.cfg.blocks[*b].start);
                            cands.extend(dms);
                        }
                        if let Some(m) = self.branch_confluence(fall, taken, universe) {
                            if !cands.contains(&m) {
                                cands.push(m);
                            }
                        }
                        if let Some(m) = self.pure_chain_end(taken, universe, stop, claimed) {
                            if !cands.contains(&m) {
                                cands.push(m);
                            }
                        }
                        if let Some(m) = pd {
                            if !cands.contains(&m) {
                                cands.push(m);
                            }
                        }
                        for m in cands {
                            if m == cur {
                                continue;
                            }
                            let mut vis_t: HashSet<usize> = HashSet::new();
                            let mut vis_f: HashSet<usize> = HashSet::new();
                            if self.diamond_side(taken, m, universe, &bstop, claimed, &mut vis_t, 0)
                                && self.diamond_side(fall, m, universe, &bstop, claimed, &mut vis_f, 0)
                            {
                                let mut vis = vis_t;
                                vis.extend(vis_f);
                                // the merge block itself stays available as
                                // the next walk position
                                vis.remove(&m);
                                claimed.extend(vis.iter().copied());
                                diamond_jump = Some(m);
                                break;
                            }
                        }
                    }
                    if let Some(m) = diamond_jump {
                        // The header block's own statements (if any) still
                        // execute; only its conditional terminal is folded
                        // into the merge value.
                        if !self.results[cur].stmts.is_empty() {
                            parts.push(Region::Basic { block: cur });
                        }
                        cur = m;
                        continue;
                    }
                    if std::env::var("JCDC_DBG_IF").is_ok() {
                        eprintln!("COND cur={} follow={:?}", cur, follow);
                    }
                    let then_r = if Some(taken) == follow && !stop.contains(&taken) {
                        Region::Empty
                    } else if Some(taken) == follow
                        && stop.contains(&taken)
                        && !self.is_terminator_block(taken)
                    {
                        // The "follow" is an enclosing barrier (loop exit):
                        // the branch is a jump out, not a fallthrough.
                        // Terminator exits stay Empty — the return/throw is
                        // emitted after the loop.
                        Region::Goto { target: taken }
                    } else if let Some(absorbed) = self.absorb_pure(taken, universe, &bstop, claimed) {
                        absorbed
                    } else if universe.contains(&taken)
                        && !bstop.contains(&taken)
                        && !claimed.contains(&taken)
                        && !(self.is_handler(taken) && active.is_empty())
                    {
                        let branch_universe = self.owner_scope(taken, universe);
                        let sub = self.sub_scope(taken, &branch_universe, &bstop, claimed);
                        self.walk(taken, &sub, &bstop, active, claimed, false)
                    } else {
                        // Target is the follow (empty), or already structured
                        // (loop header → continue; loop exit → break).
                        if self.is_terminator_block(taken) && !stop.contains(&taken) {
                            // Shared return/throw block: inline a copy at
                            // this branch (safe — terminators have no
                            // outgoing flow). Loop-exit terminators (in
                            // `stop`) must stay jumps so they resolve to
                            // break/while conditions.
                            Region::CopyStmts { block: taken }
                        } else if claimed.contains(&taken) {
                            if !stop.contains(&taken)
                                && !bstop.contains(&taken)
                                && !self.loops_stack.contains(&taken)
                            {
                                match self.copy_walk(taken, &bstop, active, cur) {
                                    Some(r) => r,
                                    None => Region::Goto { target: taken },
                                }
                            } else {
                                Region::Goto { target: taken }
                            }
                        } else if stop.contains(&taken) && !self.is_terminator_block(taken) {
                            // Jump to an enclosing loop's exit (or other
                            // barrier): keep it as a Goto so conversion
                            // resolves it to `break`.
                            Region::Goto { target: taken }
                        } else {
                            Region::Empty
                        }
                    };
                    let else_r = if Some(fall) == follow && !stop.contains(&fall) {
                        if std::env::var("JCDC_DBG_IF").is_ok() {
                            eprintln!("IF cur={} else Empty (fall==follow {})", cur, fall);
                        }
                        Region::Empty
                    } else if Some(fall) == follow
                        && stop.contains(&fall)
                        && !self.is_terminator_block(fall)
                    {
                        // The "follow" is an enclosing barrier (loop exit):
                        // the branch is a jump out, not a fallthrough.
                        // Terminator exits stay Empty — the return/throw is
                        // emitted after the loop.
                        Region::Goto { target: fall }
                    } else if let Some(absorbed) = self.absorb_pure(fall, universe, &bstop, claimed) {
                        absorbed
                    } else if universe.contains(&fall)
                        && !bstop.contains(&fall)
                        && !claimed.contains(&fall)
                        && !(self.is_handler(fall) && active.is_empty())
                    {
                        let branch_universe = self.owner_scope(fall, universe);
                        let sub = self.sub_scope(fall, &branch_universe, &bstop, claimed);
                        if std::env::var("JCDC_DBG_IF").is_ok() {
                            eprintln!("IF cur={} else walk fall={} sub={:?}", cur, fall, sub);
                        }
                        self.walk(fall, &sub, &bstop, active, claimed, false)
                    } else if self.is_terminator_block(fall) && !stop.contains(&fall) {
                        Region::CopyStmts { block: fall }
                    } else if claimed.contains(&fall) {
                        if !stop.contains(&fall)
                            && !bstop.contains(&fall)
                            && !self.loops_stack.contains(&fall)
                        {
                            if let Some(r) = self.copy_walk(fall, &bstop, active, cur) {
                                r
                            } else {
                                if std::env::var("JCDC_DBG_IF").is_ok() {
                                    eprintln!("IF cur={} else Goto(claimed) fall={}", cur, fall);
                                }
                                Region::Goto { target: fall }
                            }
                        } else {
                            if std::env::var("JCDC_DBG_IF").is_ok() {
                                eprintln!("IF cur={} else Goto(claimed) fall={}", cur, fall);
                            }
                            Region::Goto { target: fall }
                        }
                    } else if self.is_terminator_block(fall) && !stop.contains(&fall) {
                        Region::CopyStmts { block: fall }
                    } else if stop.contains(&fall) && !self.is_terminator_block(fall) {
                        // Jump to an enclosing loop's exit (or other
                        // barrier): keep it as a Goto so conversion
                        // resolves it to `break`.
                        Region::Goto { target: fall }
                    } else {
                        if std::env::var("JCDC_DBG_IF").is_ok() {
                            eprintln!(
                                "IF cur={} else Empty fall={} univ={} bstop={} handler={}",
                                cur, fall, universe.contains(&fall), bstop.contains(&fall),
                                self.is_handler(fall)
                            );
                        }
                        Region::Empty
                    };
                    // Value-diamond detection: both branches are pure
                    // (no statements, no exits) and leave exactly one value.
                    // A branch may be `Basic` or `Seq[Basic, Goto{follow}]`
                    // (javac often uses an explicit goto to the merge).
                    fn pure_block(r: &crate::builder::BlockResult, succs: &[usize], follow: Option<usize>) -> bool {
                        r.stmts.is_empty()
                            && r.out_stack.len() == 1
                            && match &r.term {
                                crate::builder::Term::Fallthrough => true,
                                crate::builder::Term::Goto => {
                                    follow.map(|f| succs == [f]).unwrap_or(false)
                                }
                                _ => false,
                            }
                    }
                    fn region_pure_block(rg: &Region, results: &Vec<BlockResult>, cfg: &Cfg, follow: Option<usize>) -> Option<usize> {
                        match rg {
                            Region::Basic { block } => {
                                if pure_block(&results[*block], &cfg.blocks[*block].succ, follow) {
                                    Some(*block)
                                } else {
                                    None
                                }
                            }
                            Region::Seq(v) if v.len() == 2 => {
                                if let (Region::Basic { block }, Region::Goto { target }) = (&v[0], &v[1]) {
                                    if follow == Some(*target)
                                        && pure_block(&results[*block], &cfg.blocks[*block].succ, follow)
                                    {
                                        return Some(*block);
                                    }
                                }
                                None
                            }
                            _ => None,
                        }
                    }
                    let ternary = if follow.is_some() {
                        match (
                            region_pure_block(&then_r, self.results, self.cfg, follow),
                            region_pure_block(&else_r, self.results, self.cfg, follow),
                        ) {
                            (Some(tb), Some(fb)) => Some((
                                self.results[tb].out_stack[0].clone(),
                                self.results[fb].out_stack[0].clone(),
                            )),
                            _ => None,
                        }
                    } else {
                        None
                    };
                    if ternary.is_some() {
                        // consume the branch blocks (Basic or Seq[Basic,Goto])
                        for rg in [&then_r, &else_r] {
                            match rg {
                                Region::Basic { block } => {
                                    claimed.insert(*block);
                                }
                                Region::Seq(v) => {
                                    for x in v {
                                        if let Region::Basic { block } = x {
                                            claimed.insert(*block);
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                    parts.push(Region::If {
                        block: cur,
                        cond,
                        then_r: Box::new(then_r),
                        else_r: Box::new(else_r),
                        follow,
                        ternary,
                    });
                    match follow {
                        Some(f) if universe.contains(&f) && !stop.contains(&f) && !claimed.contains(&f) => {
                            cur = f;
                            continue;
                        }
                        Some(f)
                            if universe.contains(&f)
                                && !stop.contains(&f)
                                && !self.loops_stack.contains(&f)
                                && !can_reach_cfg(self.cfg, f, cur, 4096) =>
                        {
                            // The merge block was already structured inside
                            // one branch (a shared tail). Every branch exit
                            // re-executes the whole tail, so re-walk it
                            // with a fresh claimed set (a structural copy)
                            // and splice the region in here.
                            let mut barriers = stop.clone();
                            barriers.insert(cur);
                            let tail_universe = reachable_within(self.cfg, f, &barriers);
                            let mut fresh: HashSet<usize> = HashSet::new();
                            let r = self.walk(f, &tail_universe, &stop, active, &mut fresh, true);
                            self.copied_tails.insert(f);
                            parts.push(r);
                            break;
                        }
                        _ => break,
                    }
                }
                Term::Switch { selector, targets } => {
                    // A switch's follow is the confluence of the cases that
                    // do NOT terminate (return/throw). `immediate_postdom`
                    // would yield None whenever any case always exits (e.g.
                    // a throwing default), losing break resolution for the
                    // remaining cases.
                    let follow = self.postdom_ipdom(universe, cur)
                        .or_else(|| self.switch_follow(cur, universe));
                    let sw = self.structure_switch(cur, selector, &targets, universe, stop, follow, active, claimed);
                    parts.push(sw);
                    match follow {
                        Some(f) if universe.contains(&f) && !stop.contains(&f) && !claimed.contains(&f) => {
                            cur = f;
                            continue;
                        }
                        _ => break,
                    }
                }
                Term::Goto => {
                    let t = b.succ.first().copied();
                    match t {
                        Some(t)
                            if universe.contains(&t)
                                && !stop.contains(&t)
                                && !claimed.contains(&t)
                                && !(self.is_handler(t) && active.is_empty()) =>
                        {
                            // Forward jump within scope: keep this block's
                            // statements, continue walking at the target.
                            parts.push(Region::Basic { block: cur });
                            cur = t;
                            continue;
                        }
                        Some(t) if universe.contains(&t) && !stop.contains(&t)
                            && claimed.contains(&t) && dom.dominates(t, cur) => {
                            // Back edge into an already-structured block:
                            // emit statements + goto (→ continue/break).
                            parts.push(Region::Basic { block: cur });
                            if self.is_terminator_block(t) && !stop.contains(&t) {
                                parts.push(Region::CopyStmts { block: t });
                            } else if !stop.contains(&t) && !self.loops_stack.contains(&t) {
                                match self.copy_walk(t, stop, active, cur) {
                                    Some(r) => parts.push(r),
                                    None => parts.push(Region::Goto { target: t }),
                                }
                            } else {
                                parts.push(Region::Goto { target: t });
                            }
                            break;
                        }
                        Some(t) => {
                            if std::env::var("JCDC_DBG_IF").is_ok() {
                                eprintln!("GOTO-FALL cur={} t={} univ={} stop={} claimed={} entry={}", cur, t, universe.contains(&t), stop.contains(&t), claimed.contains(&t), entry);
                            }
                            parts.push(Region::Basic { block: cur });
                            if self.is_terminator_block(t) && !stop.contains(&t) {
                                parts.push(Region::CopyStmts { block: t });
                            } else if !stop.contains(&t) && !self.loops_stack.contains(&t) {
                                match self.copy_walk(t, stop, active, cur) {
                                    Some(r) => parts.push(r),
                                    None => parts.push(Region::Goto { target: t }),
                                }
                            } else {
                                parts.push(Region::Goto { target: t });
                            }
                            break;
                        }
                        None => {
                            parts.push(Region::Basic { block: cur });
                            break;
                        }
                    }
                }
                Term::Return(_) | Term::Throw(_) | Term::Ret | Term::Jsr => {
                    parts.push(Region::Basic { block: cur });
                    break;
                }
                Term::Fallthrough => {
                    parts.push(Region::Basic { block: cur });
                    match b.succ.first().copied() {
                        Some(n)
                            if universe.contains(&n)
                                && !stop.contains(&n)
                                && !(self.is_handler(n) && active.is_empty()) =>
                        {
                            cur = n;
                            continue;
                        }
                        Some(n) if self.is_handler(n) && active.is_empty() => break,
                        Some(n) => {
                            if std::env::var("JCDC_DBG_IF").is_ok() {
                                eprintln!("GOTO-FT cur={} n={} univ={} stop={} claimed={} entry={}", cur, n, universe.contains(&n), stop.contains(&n), claimed.contains(&n), entry);
                            }
                            parts.push(Region::Goto { target: n });
                            break;
                        }
                        None => break,
                    }
                }
            }
        }
        if std::env::var("JCDC_DBG_IF").is_ok() {
            eprintln!("WALK END entry={} nparts={} claimed={:?}", entry, parts.len(), claimed);
        }
        match parts.len() {
            0 => Region::Empty,
            1 => parts.pop().unwrap(),
            _ => Region::Seq(parts),
        }
    }

    /// Scope for a branch starting at `b`: when `b` belongs to a try group
    /// body, exclude blocks owned by OTHER (sibling) groups — they are
    /// structured by their own Try regions — but keep unowned blocks (the
    /// post-try continuation flow) and nested groups of `gi`.
    fn owner_scope(&self, b: usize, universe: &HashSet<usize>) -> HashSet<usize> {
        match self.body_group.get(&b) {
            Some(gi) => {
                let g = &self.groups[*gi];
                universe
                    .iter()
                    .copied()
                    .filter(|x| match self.body_group.get(x) {
                        None => true,
                        Some(og) => {
                            *og == *gi
                                || (self.groups[*og].start >= g.start
                                    && self.groups[*og].end <= g.end)
                        }
                    })
                    .collect()
            }
            None => universe.clone(),
        }
    }

    /// If `blk` is a pure value block (no statements, one stack value out,
    /// single successor) and its successor is not walkable here (stop,
    /// claimed, or out of universe), absorb the block into this scope:
    /// return Basic(blk) and mark it claimed. This materializes chained
    /// boolean diamonds (`a && b || c`) whose shared push blocks would
    /// otherwise be consumed silently by the first reaching branch.
    /// Confluence block of a switch's non-terminating case flows.
    fn switch_follow(&self, cur: usize, universe: &HashSet<usize>) -> Option<usize> {
        let mut dists: Vec<HashMap<usize, u32>> = Vec::new();
        for &s0 in &self.cfg.blocks[cur].succ {
            if !universe.contains(&s0) {
                continue;
            }
            let mut d: HashMap<usize, u32> = HashMap::new();
            let mut q: VecDeque<(usize, u32)> = VecDeque::new();
            d.insert(s0, 0);
            q.push_back((s0, 0));
            while let Some((b, db)) = q.pop_front() {
                for &s in &self.cfg.blocks[b].succ {
                    if s != cur && universe.contains(&s) && !d.contains_key(&s) {
                        d.insert(s, db + 1);
                        q.push_back((s, db + 1));
                    }
                }
            }
            // Cases that always terminate (return/throw with no flow
            // onward) contribute no reconvergence point.
            let terminates = d.len() <= 1
                && self.cfg.blocks[s0]
                    .succ
                    .iter()
                    .all(|s| !universe.contains(s));
            if !terminates {
                dists.push(d);
            }
        }
        if dists.is_empty() {
            return None;
        }
        if dists.len() == 1 {
            // Single non-terminating case flow: its exit out of the case
            // region is the switch follow.
            let d = &dists[0];
            let mut best: Option<usize> = None;
            for &cand in d.keys() {
                if self.cfg.blocks[cand].pred.len() >= 2
                    && best.map(|b| self.cfg.blocks[cand].start < self.cfg.blocks[b].start).unwrap_or(true)
                {
                    best = Some(cand);
                }
            }
            return best;
        }
        let mut best: Option<(u32, usize)> = None;
        for (&cand, &d0) in dists[0].iter() {
            if cand == cur {
                continue;
            }
            let mut total = d0;
            let mut ok = true;
            for d in &dists[1..] {
                match d.get(&cand) {
                    Some(x) => total += x,
                    None => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                let better = match best {
                    None => true,
                    Some((bd, bc)) => {
                        total < bd
                            || (total == bd && self.cfg.blocks[cand].start < self.cfg.blocks[bc].start)
                    }
                };
                if better {
                    best = Some((total, cand));
                }
            }
        }
        best.map(|(_, c)| c)
    }

    /// Re-walk an already-claimed region with a throwaway claimed set,
    /// producing a structural copy. Used when flow re-enters a shared
    /// region that Java cannot express with a jump (no labelable target):
    /// re-executing the blocks matches the bytecode's per-arrival
    /// semantics. Bounded by depth and a no-reentry check.
    fn copy_walk(
        &mut self,
        t: usize,
        stop: &HashSet<usize>,
        active: &[usize],
        guard_against: usize,
    ) -> Option<Region> {
        use std::cell::Cell;
        thread_local! {
            static COPY_DEPTH: Cell<u32> = const { Cell::new(0) };
        }
        if COPY_DEPTH.with(|c| c.get()) >= 4 {
            return None;
        }
        if can_reach_cfg(self.cfg, t, guard_against, 4096) {
            return None;
        }
        // Targets that flow back into an enclosing loop (or are loop
        // exits) resolve to continue/break at conversion; never copy them.
        for h in &self.loops_stack {
            if *h == t || can_reach_cfg(self.cfg, t, *h, 4096) {
                return None;
            }
        }
        let mut barriers = stop.clone();
        barriers.extend(self.loops_stack.iter().copied());
        barriers.insert(guard_against);
        let tu = reachable_within(self.cfg, t, &barriers);
        if !tu.contains(&t) {
            return None;
        }
        COPY_DEPTH.with(|c| c.set(c.get() + 1));
        let mut fresh: HashSet<usize> = HashSet::new();
        let r = self.walk(t, &tu, stop, active, &mut fresh, true);
        COPY_DEPTH.with(|c| c.set(c.get() - 1));
        self.copied_tails.insert(t);
        Some(r)
    }

    /// True when the block ends in a return/throw (a shared terminator that
    /// can be safely duplicated at each arrival site).
    fn is_terminator_block(&self, b: usize) -> bool {
        matches!(
            self.results[b].term,
            Term::Return(_) | Term::Throw(_)
        )
    }

    /// Unique enclosing barrier block reachable from `cur`'s branch region.
    /// Barriers = stop ∪ claimed. Used by the appendix fold: when exactly
    /// one *stop* block is reachable, it is the enclosing merge M.
    fn appendix_target(
        &self,
        cur: usize,
        universe: &HashSet<usize>,
        stop: &HashSet<usize>,
        claimed: &HashSet<usize>,
    ) -> Option<usize> {
        if stop.is_empty() {
            return None;
        }
        let mut barriers: HashSet<usize> = stop.union(claimed).copied().collect();
        barriers.remove(&cur);
        let mut hits: HashSet<usize> = HashSet::new();
        let mut seen: HashSet<usize> = HashSet::new();
        let _ = universe;
        let mut q: VecDeque<usize> = self.cfg.blocks[cur].succ.iter().copied().collect();
        while let Some(b) = q.pop_front() {
            if !seen.insert(b) {
                continue;
            }
            if barriers.contains(&b) {
                hits.insert(b);
                continue;
            }
            q.extend(self.cfg.blocks[b].succ.iter().copied());
        }
        let mut stop_hits = hits.iter().copied().filter(|h| stop.contains(h));
        let m = stop_hits.next()?;
        if stop_hits.next().is_some() {
            return None; // ambiguous
        }
        // Non-stop hits (claimed blocks) are fine: the appendix region
        // merges into them, and folding makes this If their owner.
        Some(m)
    }

    fn absorb_pure(
        &mut self,
        blk: usize,
        universe: &HashSet<usize>,
        bstop: &HashSet<usize>,
        claimed: &mut HashSet<usize>,
    ) -> Option<Region> {
        if !universe.contains(&blk) {
            return None;
        }
        let dbg_absorb = std::env::var("JCDC_DBG_ABSORB").is_ok();
        let succ_walkable;
        {
            let b = &self.cfg.blocks[blk];
            let r = &self.results[blk];
            if b.ins.is_empty() || b.succ.len() != 1 {
                if dbg_absorb {
                    eprintln!("absorb EARLY blk={} ins={} succ={} out={}", blk, b.ins.is_empty(), b.succ.len(), r.out_stack.len());
                }
                return None;
            }
            // Statements must be empty or only stack-merge stores.
            let stmts_ok = r.stmts.iter().all(|st| match st {
                crate::stmt::Stmt::LocalDef { init: Some(_), .. } => true,
                crate::stmt::Stmt::ExprStmt(crate::expr::Expr::Assign { target, .. }) => {
                    matches!(&**target, crate::expr::Expr::Local { .. })
                }
                _ => false,
            });
            if !stmts_ok {
                return None;
            }
            // Only fallthrough blocks may be absorbed: an explicit goto to
            // a barrier is a real jump (loop continue / break) that must
            // stay a Region::Goto so it resolves to a jump statement.
            if !matches!(r.term, crate::builder::Term::Fallthrough) {
                return None;
            }
            let succ = b.succ[0];
            succ_walkable = universe.contains(&succ) && !bstop.contains(&succ);
        }
        if succ_walkable {
            if std::env::var("JCDC_DBG_ABSORB").is_ok() {
                eprintln!("absorb REJECT blk={} succ walkable (univ={}, bstop={})", blk,
                    universe.contains(&self.cfg.blocks[blk].succ[0]),
                    bstop.contains(&self.cfg.blocks[blk].succ[0]));
            }
            return None; // normal flow continues; not our case
        }
        if std::env::var("JCDC_DBG_ABSORB").is_ok() {
            eprintln!("absorb ACCEPT blk={} claimed={}", blk, claimed.contains(&blk));
        }
        // Shared pure blocks (reached from several branches) get their
        // statements duplicated into each branch — exactly the bytecode
        // semantics, since the block re-executes per arrival.
        if claimed.contains(&blk) {
            let r = &self.results[blk];
            if r.stmts.is_empty() {
                return Some(Region::Empty);
            }
            return Some(Region::CopyStmts { block: blk });
        }
        claimed.insert(blk);
        Some(Region::Basic { block: blk })
    }

    /// Nearest block reachable from both `a` and `b` (min total BFS dist).
    fn branch_confluence(&self, a: usize, b: usize, universe: &HashSet<usize>) -> Option<usize> {
        let bfs = |s0: usize| -> HashMap<usize, u32> {
            let mut d: HashMap<usize, u32> = HashMap::new();
            let mut q: VecDeque<(usize, u32)> = VecDeque::new();
            d.insert(s0, 0);
            q.push_back((s0, 0));
            while let Some((x, dx)) = q.pop_front() {
                for &s in &self.cfg.blocks[x].succ {
                    if universe.contains(&s) && !d.contains_key(&s) {
                        d.insert(s, dx + 1);
                        q.push_back((s, dx + 1));
                    }
                }
            }
            d
        };
        let da = bfs(a);
        let db = bfs(b);
        let mut best: Option<(u32, usize)> = None;
        for (&c, &x) in &da {
            if let Some(&y) = db.get(&c) {
                let t = x + y;
                let better = match best {
                    None => true,
                    Some((bt, bc)) => t < bt || (t == bt && self.cfg.blocks[c].start < self.cfg.blocks[bc].start),
                };
                if better {
                    best = Some((t, c));
                }
            }
        }
        best.map(|(_, c)| c)
    }

    /// Follow a chain of pure value-producing blocks (no statements, one
    /// stack value out, fallthrough/goto terminals) and return the first
    /// block that is NOT pure — the real merge point of a value diamond.
    fn pure_chain_end(
        &self,
        start: usize,
        universe: &HashSet<usize>,
        stop: &HashSet<usize>,
        claimed: &HashSet<usize>,
    ) -> Option<usize> {
        let mut cur = start;
        let mut steps = 0;
        loop {
            steps += 1;
            if steps > 10_000 || !universe.contains(&cur) || stop.contains(&cur) {
                return None;
            }
            let b = &self.cfg.blocks[cur];
            let r = &self.results[cur];
            let pure = !b.ins.is_empty()
                && r.stmts.is_empty()
                && !r.out_stack.is_empty()
                && matches!(r.term, crate::builder::Term::Fallthrough | crate::builder::Term::Goto)
                && b.succ.len() == 1;
            if !pure {
                return Some(cur);
            }
            if claimed.contains(&cur) {
                return None;
            }
            cur = b.succ[0];
        }
    }

    /// Check that both `a` and `b` flow to `merge` through blocks that are
    /// pure value producers (no statements; terminals are fallthrough or
    /// goto), possibly via nested diamond headers. All traversed blocks are
    /// added to `visited` so the caller can claim them.
#[allow(dead_code)]
    fn branches_are_diamond(
        &self,
        a: usize,
        b: usize,
        merge: usize,
        universe: &HashSet<usize>,
        stop: &HashSet<usize>,
        claimed: &HashSet<usize>,
        visited: &mut HashSet<usize>,
    ) -> bool {
        self.diamond_side(a, merge, universe, stop, claimed, visited, 0)
            && self.diamond_side(b, merge, universe, stop, claimed, visited, 0)
    }

    fn diamond_side(
        &self,
        blk: usize,
        merge: usize,
        universe: &HashSet<usize>,
        stop: &HashSet<usize>,
        claimed: &HashSet<usize>,
        visited: &mut HashSet<usize>,
        depth: usize,
    ) -> bool {
        if depth > 32 {
            return false;
        }
        let mut cur = blk;
        let mut steps = 0;
        loop {
            steps += 1;
            if steps > 10_000 {
                return false;
            }
            if cur == merge {
                return true;
            }
            if stop.contains(&cur) || claimed.contains(&cur) || !universe.contains(&cur) {
                return false;
            }
            let b = &self.cfg.blocks[cur];
            if b.ins.is_empty() {
                match b.succ.first() {
                    Some(&n) => {
                        visited.insert(cur);
                        cur = n;
                        continue;
                    }
                    None => return false,
                }
            }
            match self.term(cur) {
                Term::Fallthrough | Term::Goto => {
                    let r = &self.results[cur];
                    // pure = no statements and exactly one successor (the
                    // value it leaves may be any stack depth >= 0)
                    if !r.stmts.is_empty() || b.succ.len() != 1 {
                        return false;
                    }
                    let n = b.succ[0];
                    visited.insert(cur);
                    cur = n;
                }
                Term::Cond { .. } if b.succ.len() == 2 => {
                    // nested diamond header: both sides must reach merge
                    if !self.results[cur].stmts.is_empty() {
                        return false;
                    }
                    visited.insert(cur);
                    let s0 = b.succ[0];
                    let s1 = b.succ[1];
                    let mut v2 = HashSet::new();
                    let ok = self.diamond_side(s0, merge, universe, stop, claimed, &mut v2, depth + 1)
                        && self.diamond_side(s1, merge, universe, stop, claimed, &mut v2, depth + 1);
                    if ok {
                        visited.extend(v2);
                        return true;
                    }
                    return false;
                }
                _ => return false,
            }
        }
    }

    fn next_after_loop(
        &self,
        loop_r: &Region,
        universe: &HashSet<usize>,
        stop: &HashSet<usize>,
        claimed: &HashSet<usize>,
    ) -> Option<usize> {
        let exits = match loop_r {
            Region::Loop { exits, .. } => exits.clone(),
            _ => return None,
        };
        let _ = claimed;
        exits
            .into_iter()
            .filter(|e| universe.contains(e) && !stop.contains(e))
            .min_by_key(|e| self.cfg.blocks[*e].start)
    }

    fn structure_loop(
        &mut self,
        header: usize,
        universe: &HashSet<usize>,
        stop: &HashSet<usize>,
        active: &[usize],
        claimed: &mut HashSet<usize>,
        dom: &DomInfo,
    ) -> Region {
        // Dominators rooted at the loop header (the incoming dom is rooted
        // at the enclosing walk entry and would misjudge inner loops).
        let dom_owned = compute_dominators(self.cfg, universe, header);
        let _dom = &dom_owned;
        // Loop body = blocks forward-reachable from the header without
        // re-entering it, EXCLUDING:
        // * blocks not dominated by the header,
        // * the header's own exiting branch (direct successor that cannot
        //   loop back),
        // * break-outer targets (cannot loop back and the branching block
        //   only escapes through them),
        // * blocks whose way back to the header requires an ENCLOSING loop's
        //   back edge (e.g. the outer increment block of nested loops).
        let mut barriers: HashSet<usize> = HashSet::new();
        for l in &self.loops_stack {
            barriers.insert(*l);
        }
        barriers.insert(header);
        // Exception successors (NOT filtered by `universe`): the handler that
        // loops back is carved out of this region's universe because it is
        // structured separately by structure_try, yet it is real control flow.
        // A protected block whose normal successors all return/throw can still
        // reach the header through that handler. Without these edges the
        // membership reachability below misclassifies the try head as a loop
        // EXIT and hoists the whole try/catch out of the loop body.
        let mut exc_succ: HashMap<usize, Vec<usize>> = HashMap::new();
        for e in &self.cfg.exc_edges {
            exc_succ.entry(e.from).or_default().push(e.to);
        }
        let mut members: HashSet<usize> = HashSet::new();
        members.insert(header);
        {
            let mut q: VecDeque<usize> = VecDeque::new();
            q.push_back(header);
            while let Some(b) = q.pop_front() {
                for &s in &self.cfg.blocks[b].succ {
                    if barriers.contains(&s) && s != header {
                        // enclosing loop header: never absorb it
                        continue;
                    }
                    if s == header || !universe.contains(&s) || stop.contains(&s) {
                        continue;
                    }
                    if !dom.dominates(header, s) {
                        continue;
                    }
                    let reaches =
                        can_reach_cfg_barred(self.cfg, &exc_succ, s, header, &barriers, 8192);
                    if !reaches {
                        // `s` cannot loop back on its own. It is the loop's
                        // exit merge when the header branches to it directly
                        // or some predecessor reaches it as its dedicated
                        // escape jump. A body-internal terminator tail
                        // (return/throw whose predecessor only falls into
                        // it) stays a member.
                        let preds = self.cfg.blocks[s].pred.clone();
                        let mut exit_edge = preds.iter().any(|&p| {
                            p == header
                                || !can_reach_avoiding(self.cfg, &exc_succ, p, header, s, 8192)
                        });
                        if !exit_edge {
                            // Confluence of dedicated escape jumps: every
                            // predecessor also branches to another exit
                            // candidate that cannot reach the header.
                            exit_edge = !preds.is_empty()
                                && preds.iter().all(|&p| {
                                    self.cfg.blocks[p].succ.iter().any(|&q| {
                                        q != s
                                            && !can_reach_cfg_barred(
                                                self.cfg, &exc_succ, q, header, &barriers, 8192,
                                            )
                                    })
                                });
                        }
                        if exit_edge || preds.is_empty() {
                            // Last chance: a protected terminator tail. The
                            // JVM splits `try { return f(); }` into a call
                            // block (inside the range, has an exc edge) and a
                            // bare `return` block starting exactly at the
                            // range end (no exc edge of its own). Such a
                            // return is body-internal — keep it when its
                            // predecessors are already members sharing a try
                            // range. Without this, the in-loop try's arm
                            // region ends at the call block and the return is
                            // lost.
                            let protected_tail = self.cfg.blocks[s].succ.is_empty()
                                && !preds.is_empty()
                                && preds.iter().all(|&p| {
                                    members.contains(&p)
                                        && self.cfg.exc_ranges.iter().any(|r| {
                                            r.start <= self.cfg.blocks[p].start
                                                && self.cfg.blocks[p].start < r.end
                                                && self.cfg.blocks[s].start <= r.end
                                                && self.cfg.blocks[s].start
                                                    > self.cfg.blocks[p].start
                                        })
                                });
                            if !protected_tail {
                                continue;
                            }
                        }
                    }
                    if members.insert(s) {
                        q.push_back(s);
                    }
                }
            }
        }
        let mut exits: Vec<usize> = Vec::new();
        for &m in &members {
            for &s in &self.cfg.blocks[m].succ {
                if !members.contains(&s) && !exits.contains(&s) {
                    exits.push(s);
                }
            }
        }
        exits.sort_by_key(|e| self.cfg.blocks[*e].start);

        let mut inner_stop: HashSet<usize> = stop.iter().copied().filter(|s| members.contains(s)).collect();
        inner_stop.extend(exits.iter().copied());
        // NOTE: header is NOT in inner_stop — the walk starts there and the
        // claimed-guard stops re-entry (back edges become Goto{header}).
        if std::env::var("JCDC_DBG_IF").is_ok() {
            eprintln!("structure_loop header={} members={:?} exits={:?}", header, members, exits);
        }
        if std::env::var("JCDC_DBG_LOOP").is_ok() {
            eprintln!("LOOP header={} members={:?} inner_stop={:?}", header, members, inner_stop);
        }
        claimed.insert(header);
        self.loops_stack.push(header);
        let body = self.walk(header, &members, &inner_stop, active, claimed, true);
        if std::env::var("JCDC_DBG_LOOP").is_ok() {
            eprintln!("LOOP body region: {:#?}", body);
        }
        self.loops_stack.pop();
        claimed.extend(members.iter().copied());
        Region::Loop { header, body: Box::new(body), members, exits }
    }

    fn structure_switch(
        &mut self,
        block: usize,
        selector: Expr,
        targets: &SwitchTargets,
        universe: &HashSet<usize>,
        stop: &HashSet<usize>,
        follow: Option<usize>,
        active: &[usize],
        claimed: &mut HashSet<usize>,
    ) -> Region {
        let last = self.cfg.blocks[block].ins.last();
        let (pairs, default_pc): (Vec<(i64, u16)>, u16) =
            match (targets, last.and_then(|i| i.switch_data.as_deref())) {
                (SwitchTargets::Table { .. }, Some(jcdc_classfile::SwitchData::Table { default, low, targets: ts })) => (
                    ts.iter().enumerate().map(|(i, &t)| (*low as i64 + i as i64, t)).collect(),
                    *default,
                ),
                (SwitchTargets::Lookup { .. }, Some(jcdc_classfile::SwitchData::Lookup { default, pairs: ps })) => {
                    (ps.iter().map(|(m, t)| (*m as i64, *t)).collect(), *default)
                }
                _ => (Vec::new(), 0),
            };
        // If the default target is the switch follow (confluence), there is
        // no explicit default region — flow just continues after the switch.
        let default_block = self.cfg.block_at(default_pc).filter(|d| Some(*d) != follow);

        let mut case_groups: Vec<(Vec<i64>, usize, bool)> = Vec::new(); // (vals, block, is_follow)
        for (v, t) in &pairs {
            let Some(tb) = self.cfg.block_at(*t) else { continue };
            if Some(tb) == default_block {
                continue;
            }
            if Some(tb) == follow {
                // Case that jumps straight to the confluence: empty body + break.
                if let Some(g) = case_groups.iter_mut().find(|(_, gb, f)| *gb == tb && *f) {
                    g.0.push(*v);
                } else {
                    case_groups.push((vec![*v], tb, true));
                }
                continue;
            }
            if let Some(g) = case_groups.iter_mut().find(|(_, gb, f)| *gb == tb && !*f) {
                g.0.push(*v);
            } else {
                case_groups.push((vec![*v], tb, false));
            }
        }
        case_groups.sort_by_key(|(_, b, _)| self.cfg.blocks[*b].start);

        let mut case_stop = stop.clone();
        if let Some(f) = follow {
            case_stop.insert(f);
        }
        for (_, b, is_follow) in &case_groups {
            if !is_follow {
                case_stop.insert(*b);
            }
        }
        if let Some(d) = default_block {
            case_stop.insert(d);
        }

        // All case/default head blocks: a trailing Goto to one of them is a
        // switch fallthrough (no statement in Java).
        let mut head_set: HashSet<usize> = HashSet::new();
        for (_, b, is_follow) in &case_groups {
            if !is_follow {
                head_set.insert(*b);
            }
        }
        if let Some(d) = default_block {
            head_set.insert(d);
        }

        let mut cases = Vec::new();
        for (vals, b, is_follow) in case_groups {
            if is_follow {
                // Empty case that breaks out to the confluence.
                cases.push((vals, Region::Goto { target: b }));
                continue;
            }
            if !universe.contains(&b) || claimed.contains(&b) {
                // A case jumping into an already-structured terminator tail
                // gets its own copy (per-case epilogues are javac's normal
                // return-path duplication).
                let copied = if !stop.contains(&b) && !self.loops_stack.contains(&b) {
                    let mut cstop = case_stop.clone();
                    cstop.remove(&b);
                    self.copy_walk(b, &cstop, active, block)
                } else {
                    None
                };
                if std::env::var("JCDC_DBG_GOTO").is_ok() {
                    eprintln!("SWCASE b={} univ={} claimed={} stop={} follow={:?} loops={:?} copied={}", b,
                        universe.contains(&b), claimed.contains(&b), case_stop.contains(&b), follow,
                        self.loops_stack, copied.is_some());
                }
                cases.push((vals, copied.unwrap_or(Region::Goto { target: b })));
                continue;
            }
            // The case's own head must not be in its stop set.
            let mut cstop = case_stop.clone();
            cstop.remove(&b);
            let sub = self.sub_scope(b, universe, &cstop, claimed);
            let r = self.walk(b, &sub, &cstop, active, claimed, false);
            cases.push((vals, strip_fallthrough_goto(r, &head_set)));
        }
        let default = default_block.map(|d| {
            if !universe.contains(&d) || claimed.contains(&d) {
                let copied = if !stop.contains(&d) && !self.loops_stack.contains(&d) {
                    let mut cstop = case_stop.clone();
                    cstop.remove(&d);
                    self.copy_walk(d, &cstop, active, block)
                } else {
                    None
                };
                return Box::new(copied.unwrap_or(Region::Goto { target: d }));
            }
            let mut cstop = case_stop.clone();
            cstop.remove(&d);
            let sub = reachable_within(self.cfg, d, &cstop);
            let r = self.walk(d, &sub, &cstop, active, claimed, false);
            Box::new(strip_fallthrough_goto(r, &head_set))
        });
        Region::Switch { block, selector, cases, default, follow }
    }

    fn structure_try(
        &mut self,
        gi: usize,
        universe: &HashSet<usize>,
        outer_universe: &HashSet<usize>,
        claimed: &mut HashSet<usize>,
    ) -> Region {
        let g = self.groups[gi].clone();
        let nested: Vec<usize> = (0..self.groups.len())
            .filter(|&j| j != gi && self.groups[j].start >= g.start && self.groups[j].end <= g.end)
            .collect();
        // Body universe includes nested groups' blocks so the walk reaches
        // their start and carves out inner Try regions.
        let body_universe: HashSet<usize> = universe
            .iter()
            .copied()
            .filter(|b| {
                match self.body_group.get(b) {
                    Some(ogi) => *ogi == gi || nested.contains(ogi),
                    None => false,
                }
            })
            .collect();
        if std::env::var("JCDC_DBG_IF").is_ok() {
            eprintln!(
                "structure_try gi={} span=({},{}) body_universe={:?} nested={:?}",
                gi, g.start, g.end, body_universe, nested
            );
        }
        // javac often excludes the final `areturn` from the protected span
        // (it cannot throw). When that trailing terminator's only entry is
        // the protected flow, it semantically belongs to the try body —
        // absorb it so `return f();` stays inside the try and the catches
        // remain legal.
        let mut body_universe = body_universe;
        if let Some(cb) = self.cfg.block_at(g.end) {
            if !body_universe.contains(&cb)
                && self.is_terminator_block(cb)
                && self.results[cb].stmts.is_empty()
                && !self.handler_group.contains_key(&cb)
                && !self.cfg.blocks[cb].pred.is_empty()
                && self.cfg.blocks[cb]
                    .pred
                    .iter()
                    .all(|p| self.body_group.get(p) == Some(&gi))
            {
                body_universe.insert(cb);
            }
        }
        let body = match self.cfg.block_at(g.start) {
            Some(entry) if body_universe.contains(&entry) => {
                let mut r = self.walk(entry, &body_universe, &HashSet::new(), &nested, claimed, false);
                // Flow leaving the try body to the post-try continuation is
                // natural fallthrough (the outer walk picks it up there).
                let cont = self.continuation_after(g.end, outer_universe, claimed);
                if std::env::var("JCDC_DBG_IF").is_ok() {
                    eprintln!("try gi={} cont={:?} universe_has_blocks_after_end={}", gi, cont,
                        universe.iter().filter(|b| self.cfg.blocks[**b].start >= g.end).count());
                }
                if let Some(c) = cont {
                    strip_trailing_goto_to(&mut r, c);
                }
                r
            }
            _ => Region::Empty,
        };

        // Merge multi-catch: consecutive handlers with the same handler block
        // become one catch with multiple types.
        let mut merged_handlers: Vec<(Vec<String>, u16, usize)> = Vec::new(); // types, hpc, hb
        for (hpc, ty) in &g.handlers {
            let Some(hb) = self.cfg.block_at(*hpc) else { continue };
            if self.handler_group.get(&hb) != Some(&gi) {
                continue;
            }
            if let Some(last) = merged_handlers.last_mut() {
                if last.2 == hb {
                    if let Some(t) = ty {
                        last.0.push(t.clone());
                    }
                    continue;
                }
            }
            merged_handlers.push((ty.clone().into_iter().collect(), *hpc, hb));
        }
        let mut catches = Vec::new();
        for (tys, _hpc, hb) in &merged_handlers {
            let mut hstop: HashSet<usize> = HashSet::new();
            for b in universe.iter().copied() {
                if self.body_group.get(&b) == Some(&gi) {
                    hstop.insert(b);
                }
            }
            for (h2, _) in &g.handlers {
                if let Some(hb2) = self.cfg.block_at(*h2) {
                    if hb2 != *hb {
                        hstop.insert(hb2);
                    }
                }
            }
            let mut huniverse = reachable_within(self.cfg, *hb, &hstop);
            // Keep the handler walk out of try-body blocks that start before
            // this group's end (real protected code), and out of other
            // handlers' heads. Blocks past the group end may legitimately
            // belong to an enclosing group's span while being part of this
            // handler's flow (nested try-with-resources).
            huniverse.retain(|b| {
                let body_before_end = self
                    .body_group
                    .get(b)
                    .map(|_ogi| self.cfg.blocks[*b].start < g.end)
                    .unwrap_or(false);
                !body_before_end && (!self.handler_group.contains_key(b) || *b == *hb)
            });
            // Also exclude the post-try continuation flow: blocks reachable
            // from the group's end are shared with the normal path and must
            // not be absorbed into the handler.
            if let Some(cont) = self.cfg.block_at(g.end) {
                let tail = reachable_within(self.cfg, cont, &HashSet::new());
                huniverse.retain(|b| !tail.contains(b));
            }
            huniverse.insert(*hb);
            // Exception groups nested inside the handler region (e.g. a
            // synchronized block within a catch) must be visible to the
            // handler walk so they get carved out as their own Try regions.
            let hmin = huniverse
                .iter()
                .map(|b| self.cfg.blocks[*b].start)
                .min()
                .unwrap_or(u16::MAX);
            let hmax = huniverse
                .iter()
                .map(|b| self.cfg.blocks[*b].end)
                .max()
                .unwrap_or(0);
            let h_active: Vec<usize> = (0..self.groups.len())
                .filter(|&j| {
                    if j == gi {
                        return false;
                    }
                    let gj = &self.groups[j];
                    if gj.start < hmin || gj.end > hmax {
                        return false;
                    }
                    // Handler self-protection ranges (the handler guards its
                    // own monitorexit) are not separate regions.
                    !gj.handlers.iter().all(|(h, _)| *h == gj.start)
                })
                .collect();
            let mut r = self.walk(*hb, &huniverse, &HashSet::new(), &h_active, claimed, false);
            // Handler exits into the post-try flow: any forward target that
            // is not part of a try body is a natural merge (the outer walk
            // emits those blocks after this region).
            self.strip_handler_exit_goto(&mut r, g.end);
            catches.push((tys.clone(), *hb, Box::new(r)));
        }
        Region::Try { group_idx: gi, body: Box::new(body), catches }
    }
}

/// Reachability from `from` to `to` via normal edges, with a work budget.
pub fn can_reach_cfg(cfg: &Cfg, from: usize, to: usize, budget: usize) -> bool {
    if from == to {
        return true;
    }
    let mut seen = std::collections::HashSet::new();
    let mut q = std::collections::VecDeque::new();
    q.push_back(from);
    seen.insert(from);
    let mut n = 0;
    while let Some(b) = q.pop_front() {
        n += 1;
        if n > budget {
            return false;
        }
        for &s in &cfg.blocks[b].succ {
            if s == to {
                return true;
            }
            if seen.insert(s) {
                q.push_back(s);
            }
        }
    }
    false
}

/// True if `to` is reachable from `from` without stepping on `avoid`.
pub fn can_reach_avoiding(
    cfg: &Cfg,
    exc_succ: &HashMap<usize, Vec<usize>>,
    from: usize,
    to: usize,
    avoid: usize,
    budget: usize,
) -> bool {
    if from == to {
        return true;
    }
    let mut seen = std::collections::HashSet::new();
    let mut q = std::collections::VecDeque::new();
    if from != avoid {
        q.push_back(from);
        seen.insert(from);
    }
    let mut n = 0;
    while let Some(b) = q.pop_front() {
        n += 1;
        if n > budget {
            return false;
        }
        for &s in &cfg.blocks[b].succ {
            if s == to {
                return true;
            }
            if s != avoid && seen.insert(s) {
                q.push_back(s);
            }
        }
        if let Some(xs) = exc_succ.get(&b) {
            for &s in xs {
                if s == to {
                    return true;
                }
                if s != avoid && seen.insert(s) {
                    q.push_back(s);
                }
            }
        }
    }
    false
}

/// Reachability from `from` to `to` that never steps on barrier blocks
/// (other than `from` itself). Follows normal AND exception successors
/// (`exc_succ`), so a protected block whose normal exits all return/throw is
/// still seen to loop back through its handler.
pub fn can_reach_cfg_barred(
    cfg: &Cfg,
    exc_succ: &HashMap<usize, Vec<usize>>,
    from: usize,
    to: usize,
    barriers: &HashSet<usize>,
    budget: usize,
) -> bool {
    if from == to {
        return true;
    }
    let mut seen = std::collections::HashSet::new();
    let mut q = std::collections::VecDeque::new();
    q.push_back(from);
    seen.insert(from);
    let mut n = 0;
    while let Some(b) = q.pop_front() {
        n += 1;
        if n > budget {
            return false;
        }
        for &s in &cfg.blocks[b].succ {
            if s == to {
                return true;
            }
            if !barriers.contains(&s) && seen.insert(s) {
                q.push_back(s);
            }
        }
        if let Some(xs) = exc_succ.get(&b) {
            for &s in xs {
                if s == to {
                    return true;
                }
                if !barriers.contains(&s) && seen.insert(s) {
                    q.push_back(s);
                }
            }
        }
    }
    false
}
