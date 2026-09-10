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

/// Compute immediate post-dominators over `universe` via the standard
/// Cooper-Harvey-Kennedy iterative dataflow on the REVERSED cfg, rooted at a
/// single sentinel VIRTUAL EXIT (`vx`) that every block leaving the universe
/// (a terminator, or an edge out of `universe`) flows to. Returns
/// (vx, block_id -> ipdom_id). The single sentinel root makes the reverse RPO
/// well-defined and the post-dominator forest a single tree, so the CHK
/// `intersect` walk always terminates (it climbs toward `vx`).
pub(crate) fn compute_postdominators(cfg: &Cfg, universe: &HashSet<usize>) -> (usize, HashMap<usize, usize>) {
    let vx = cfg.blocks.len();
    let leaves_universe = |b: usize| -> bool {
        cfg.blocks[b].succ.is_empty()
            || cfg.blocks[b].succ.iter().any(|s| !universe.contains(s))
    };
    let succs_of = |b: usize| -> Vec<usize> {
        let mut v: Vec<usize> = cfg.blocks[b]
            .succ
            .iter()
            .copied()
            .filter(|s| universe.contains(s))
            .collect();
        if leaves_universe(b) {
            v.push(vx);
        }
        v
    };
    // Reverse-post-order over the reversed graph rooted at vx (vx's reversed
    // successors are the exit blocks; b's reversed successors are its forward
    // preds).
    let mut order: Vec<usize> = Vec::new();
    {
        let mut visited: HashSet<usize> = HashSet::new();
        visited.insert(vx);
        let mut stack: Vec<usize> = Vec::new();
        let mut state: HashMap<usize, usize> = HashMap::new();
        let mut seeds: Vec<usize> =
            universe.iter().copied().filter(|&b| leaves_universe(b)).collect();
        seeds.sort_unstable_by_key(|b| cfg.blocks[*b].start);
        for s in seeds.iter().rev() {
            if visited.insert(*s) {
                stack.push(*s);
            }
        }
        while let Some(&n) = stack.last() {
            let idx = *state.entry(n).or_insert(0);
            let ps: Vec<usize> = cfg.blocks[n]
                .pred
                .iter()
                .copied()
                .filter(|p| universe.contains(p))
                .collect();
            if idx < ps.len() {
                *state.get_mut(&n).unwrap() += 1;
                let p = ps[idx];
                if visited.insert(p) {
                    stack.push(p);
                }
            } else {
                order.push(n);
                stack.pop();
            }
        }
        order.reverse();
        order.push(vx);
    }
    let mut rpo_num: HashMap<usize, usize> = HashMap::new();
    for (i, &b) in order.iter().enumerate() {
        rpo_num.insert(b, i);
    }
    let mut ipdom: HashMap<usize, usize> = HashMap::new();
    ipdom.insert(vx, vx);
    for &b in universe.iter() {
        ipdom.insert(b, vx);
    }
    let cap = universe.len() + 2;
    let intersect = |mut a: usize, mut b: usize, ipdom: &HashMap<usize, usize>| -> usize {
        let mut guard = 0usize;
        while a != b {
            guard += 1;
            if guard > cap {
                return vx;
            }
            let na = rpo_num.get(&a).copied().unwrap_or(0);
            let nb = rpo_num.get(&b).copied().unwrap_or(0);
            if na < nb {
                a = *ipdom.get(&a).unwrap_or(&vx);
            } else {
                b = *ipdom.get(&b).unwrap_or(&vx);
            }
        }
        a
    };
    let mut changed = true;
    let mut iter = 0;
    while changed && iter < 64 {
        changed = false;
        iter += 1;
        for &b in order.iter().rev() {
            if b == vx {
                continue;
            }
            let ss = succs_of(b);
            if ss.is_empty() {
                continue;
            }
            let mut new_ipdom = ss[0];
            for &s in &ss[1..] {
                new_ipdom = intersect(new_ipdom, s, &ipdom);
            }
            if ipdom.get(&b).copied().unwrap_or(vx) != new_ipdom {
                ipdom.insert(b, new_ipdom);
                changed = true;
            }
        }
    }
    (vx, ipdom)
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
    group_exceptions_with(cfg, None)
}

/// True when any expression in these statements calls
/// `Throwable.addSuppressed` — the fingerprint of try-with-resources
/// close scaffolding.
fn stmts_mention_addsuppressed(stmts: &[crate::stmt::Stmt]) -> bool {
    fn ex(e: &crate::expr::Expr) -> bool {
        use crate::expr::Expr as E;
        match e {
            E::Method { name, owner, args, .. } => {
                name == "addSuppressed"
                    || owner.as_deref().map(ex).unwrap_or(false)
                    || args.iter().any(ex)
            }
            E::Field { owner: Some(o), .. } => ex(o),
            E::Bin { l, r, .. } | E::Assign { target: l, value: r, .. } => ex(l) || ex(r),
            E::Cond { c, t, f } => ex(c) || ex(t) || ex(f),
            E::Un { e: x, .. }
            | E::Cast { e: x, .. }
            | E::InstanceOf { e: x, .. }
            | E::PreIncDec { e: x, .. }
            | E::PostIncDec { e: x, .. } => ex(x),
            E::ArrayIndex { array, index } => ex(array) || ex(index),
            E::New { args, .. } | E::AnonNew { args, .. } => args.iter().any(ex),
            E::NewArray { dims, init, .. } => {
                dims.iter().any(ex)
                    || init.as_ref().map(|v| v.iter().any(ex)).unwrap_or(false)
            }
            E::StringConcat(parts) => parts
                .iter()
                .any(|pp| matches!(pp, crate::expr::ConcatPart::Str(x) if ex(x))),
            E::Invokedynamic { args, .. } => args.iter().any(ex),
            E::Lambda(l) => l.captures.iter().any(ex),
            _ => false,
        }
    }
    fn st(s: &crate::stmt::Stmt) -> bool {
        use crate::stmt::Stmt as S;
        match s {
            S::Block(v) => v.iter().any(st),
            S::ExprStmt(e) => ex(e),
            S::LocalDef { init: Some(e), .. } => ex(e),
            S::Return(e) => e.as_ref().map(ex).unwrap_or(false),
            S::Throw(e) => ex(e),
            S::If { cond, then_stmt, else_stmt } => {
                ex(cond)
                    || st(then_stmt)
                    || else_stmt.as_deref().map(st).unwrap_or(false)
            }
            S::While { cond, body } | S::DoWhile { body, cond } => ex(cond) || st(body),
            S::For { init, cond, update, body } => {
                init.iter().any(st)
                    || cond.as_ref().map(ex).unwrap_or(false)
                    || update.iter().any(ex)
                    || st(body)
            }
            S::ForEach { iterable, body, .. } => ex(iterable) || st(body),
            S::Switch { selector, cases, default, .. } => {
                ex(selector)
                    || cases.iter().any(|c| c.body.iter().any(st))
                    || default.as_deref().map(st).unwrap_or(false)
            }
            S::Try { body, catches, finally } | S::TryWithResources { body, catches, finally, .. } => {
                st(body)
                    || catches.iter().any(|c| st(&c.body))
                    || finally.as_deref().map(st).unwrap_or(false)
            }
            S::Synchronized { lock, body } => ex(lock) || st(body),
            S::Labeled { body, .. } => st(body),
            S::Assert { cond, msg } => {
                ex(cond) || msg.as_ref().map(ex).unwrap_or(false)
            }
            _ => false,
        }
    }
    stmts.iter().any(st)
}

pub fn group_exceptions_with(cfg: &Cfg, results: Option<&Vec<crate::builder::BlockResult>>) -> Vec<TryGroup> {
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
                    // Same-handler ranges separated by MORE than 4 bytes
                    // still belong to one try when every block strictly
                    // between them is a terminator (no normal succ):
                    // those are the handler's own inline finally copies
                    // (`unlock; return false`) that javac excludes from
                    // the protected ranges (jdk17 LinkedBlockingQueue
                    // .offer(E,long,TimeUnit): ranges (37,59)+(67,122)
                    // split around the 8-byte return-false copy — the
                    // unmerged first range made the try body {3,4,5},
                    // cutting the wait loop's backedge block out of the
                    // body universe; the loop exit got inlined as an
                    // if-arm inside the loop and the post-loop return
                    // was stranded in it — 缺少返回语句 x2 methods).
                    // The gap must not swallow ANOTHER group's handler:
                    // TWR nesting (try(a){try(b){..}}) puts the inner
                    // handler entry exactly at the seam between the outer
                    // resource's split ranges (feat Exceptions
                    // .tryWithResources2: outer ranges (10,56)+(62,78)
                    // share handler 78, and 62 is the inner group's
                    // handler — merging collapsed the nested TWR into one
                    // span with an empty catch(Throwable), 缺少返回语句
                    // across the whole features battery). A foreign
                    // handler INSIDE the gap fails the same way.
                    let own_handlers: Vec<u16> =
                        groups[a].handlers.iter().map(|(h, _)| *h).collect();
                    let seam_clear_of_foreign_handlers =
                        !cfg.exc_ranges.iter().any(|r| {
                            !own_handlers.contains(&r.handler)
                                && r.handler > groups[a].end
                                && r.handler <= groups[b].start
                        });
                    // The gap blocks themselves must be pure terminator
                    // flow (the handler's inline finally copies —
                    // `unlock; return false`) with no TWR close
                    // scaffolding (addSuppressed calls indicate resource
                    // copies whose removal from the exception topology
                    // misplaces the closes).
                    let gap_terminator_only = seam_clear_of_foreign_handlers
                        && cfg
                            .blocks
                            .iter()
                            .filter(|bl| !bl.ins.is_empty())
                            .filter(|bl| {
                                bl.start >= groups[a].end && bl.end <= groups[b].start
                            })
                            .all(|bl| {
                                bl.succ.is_empty()
                                    && results
                                        .map(|rs| {
                                            !stmts_mention_addsuppressed(&rs[bl.id].stmts)
                                        })
                                        .unwrap_or(true)
                            });
                    if !gap_terminator_only {
                        continue;
                    }
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

#[derive(Debug, Clone)]
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

impl Region {
    /// Top-level parts of this region (the Seq's elements, or the region
    /// itself as a single part).
    fn iter_parts(&self) -> &[Region] {
        match self {
            Region::Seq(v) => v.as_slice(),
            _ => std::slice::from_ref(self),
        }
    }

    /// True when ANY flow path leaving this region does so via a Goto to
    /// a target other than `taken` — i.e. the path BYPASSES the parked
    /// follow block `taken` and would fall into the parked sibling
    /// statements at render time instead of reaching its real target.
    /// Regions ending without a Goto (Basic/CopyStmts/Empty/Loop/Try
    /// fallout) leave the arm by natural fallthrough INTO the parked
    /// chain — exactly the empty-arm contract, no bypass.
    fn bypasses_exempt(
        r: &Region,
        taken: usize,
        exempt: &std::collections::HashSet<usize>,
    ) -> bool {
        match r {
            Region::Goto { target } => *target != taken && !exempt.contains(target),
            Region::Seq(v) => v
                .last()
                .map(|l| Region::bypasses_exempt(l, taken, exempt))
                .unwrap_or(false),
            Region::If { then_r, else_r, .. } => {
                Region::bypasses_exempt(then_r, taken, exempt)
                    || Region::bypasses_exempt(else_r, taken, exempt)
            }
            Region::Try { body, catches, .. } => {
                Region::bypasses_exempt(body, taken, exempt)
                    || catches
                        .iter()
                        .any(|(_, _, h)| Region::bypasses_exempt(h, taken, exempt))
            }
            _ => false,
        }
    }

    /// Collect loop headers/exits and Switch follows embedded in a region
    /// tree: Gotos targeting them resolve to continue/break statements at
    /// conversion — jumps that never fall through, so they are not
    /// parked-chain bypasses (completing after them would emit
    /// unreachable code).
    fn jump_targets(r: &Region, out: &mut std::collections::HashSet<usize>) {
        match r {
            Region::Loop { header, body, exits, .. } => {
                out.insert(*header);
                out.extend(exits.iter().copied());
                Region::jump_targets(body, out);
            }
            Region::Switch { cases, default, follow, .. } => {
                if let Some(f) = follow {
                    out.insert(*f);
                }
                for (_, cr) in cases {
                    Region::jump_targets(cr, out);
                }
                if let Some(d) = default {
                    Region::jump_targets(d, out);
                }
            }
            Region::Seq(v) => {
                for x in v {
                    Region::jump_targets(x, out);
                }
            }
            Region::If { then_r, else_r, .. } => {
                Region::jump_targets(then_r, out);
                Region::jump_targets(else_r, out);
            }
            Region::Try { body, catches, .. } => {
                Region::jump_targets(body, out);
                for (_, _, h) in catches {
                    Region::jump_targets(h, out);
                }
            }
            _ => {}
        }
    }
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
    /// Nesting depth of structure_switch case walks: >0 while walking
    /// inside another switch's case regions. A stop-confluence follow of
    /// a NESTED switch crosses construct boundaries (it is typically the
    /// ENCLOSING switch's own follow) — passing it as this switch's
    /// follow makes conversion resolve the case-tail goto to a bare
    /// `break` that binds to the WRONG (inner) switch.
    pub switch_depth: usize,
    /// Innermost switch case-arm walk context: (case head block, that
    /// switch's region follow, selector is a Java 21+ typeSwitch pattern
    /// switch). A nested switch whose stop-confluence equals the ENCLOSING
    /// pattern switch's follow may keep the plain-break binding when it is
    /// the LAST construct of the case arm AND the arm walk is the case-arm
    /// walk itself: the pattern-switch restoration appends the case's
    /// terminal `break;`, which lands on the outer follow == the
    /// confluence, so both bindings are equivalent and the plain one keeps
    /// the appended outer break reachable (ClassPrinterImpl.toYaml/toXml).
    /// Classic switches get NO appended break (case fall-through) — the
    /// crossing nulling must stay for them (bkeyword's inner default
    /// `return '?'` must not degrade to `break` + fall-through).
    pub case_arm_ctx: Vec<(usize, Option<usize>, bool)>,
    /// Loop headers detected at the SESE method level (including
    /// exception-edge back edges from no-normal-pred retry handlers).
    /// Walk-based sub-builders consult this so a retry `goto header`
    /// keeps loop precedence and resolves to `continue` (jdk26
    /// Future.exceptionNow).
    pub sese_loop_headers: std::collections::HashSet<usize>,
    /// Subset of sese_loop_headers discovered via EXCEPTION-mediated back
    /// edges (handler-flow retry gotos). The walk loop branch trusts only
    /// this subset: normal back edges must keep failing the scoped
    /// dominance check (the loop belongs to an enclosing scope then —
    /// structuring it from the inner scope degraded ThreadPoolExecutor /
    /// the blocking-queue family: int-boolean conditions, catch-less
    /// tries x6 per tree).
    pub sese_exc_retry_headers: std::collections::HashSet<usize>,
    /// Current `walk` recursion depth (hang guard for pathological methods
    /// whose shared-tail / branch decomposition does not converge).
    walk_depth: usize,
    pub groups: Vec<TryGroup>,
    /// Outermost group index owning each body block.
    pub body_group: HashMap<usize, usize>,
    /// Group index owning each handler head block.
    pub handler_group: HashMap<usize, usize>,
    /// Final fields of the emitting class: SESE must not duplicate a
    /// shared terminator block that assigns one (a final accepts exactly
    /// one assignment per path — jdk17 Long$LongCache clinit tail
    /// `cache = archivedCache; return;` copied into a branch =
    /// "variable cache might already have been assigned").
    pub final_fields: std::collections::HashSet<String>,
    /// Groups whose structure_try is currently on the stack: the
    /// group_here fallback must not re-fire a group inside its OWN body
    /// walk (structure_try passes `nested` — which excludes the group —
    /// as the body's active, so the primary find already declines there).
    structuring_groups: std::cell::RefCell<Vec<usize>>,
}

impl<'a> Structurer<'a> {
    /// Remove a trailing `Goto{target}` from a region (at any tail
    /// position: end of a sequence, or the tail of an if/else branch).
    /// A trailing `Goto{s}` also strips when `s` is a statement-free
    /// Fallthrough/Goto chain into `target`: the body walk hops such
    /// stubs via copy_walk (the stub is not in the body universe), and
    /// the copy must go when the real continuation is the stripped
    /// target — otherwise the post-try statement executes twice (jdk26
    /// UntrustedCertificates clinit: `algorithm = getProperty` inside the
    /// try AND after it — 可能已分配变量algorithm on the blank final).
    fn strip_trailing_goto_to(&self, r: &mut Region, target: usize) {
        self.strip_trailing_goto_chain(r, target, &mut HashSet::new())
    }

    fn strip_trailing_goto_chain(&self, r: &mut Region, target: usize, seen: &mut HashSet<usize>) {
        match r {
            Region::Goto { target: t } if *t == target => *r = Region::Empty,
            Region::Goto { target: t } if self.is_stmt_free_chain_to(*t, target, seen) => {
                *r = Region::Empty
            }
            Region::Seq(v) => {
                if let Some(last) = v.last_mut() {
                    self.strip_trailing_goto_chain(last, target, seen);
                }
                if matches!(v.last(), Some(Region::Empty)) {
                    v.pop();
                }
            }
            Region::If { then_r, else_r, .. } => {
                self.strip_trailing_goto_chain(then_r, target, seen);
                self.strip_trailing_goto_chain(else_r, target, seen);
            }
            _ => {}
        }
    }

    /// True when `t` lies at/after the span end of one of the ACTIVE
    /// groups: it is that group's post-try continuation, owned by the
    /// enclosing walk (structure_try strips the trailing Goto and the
    /// scope continues there). Copy-walking it from inside the body
    /// duplicates the continuation statement (jdk26
    /// UntrustedCertificates clinit: `algorithm = getProperty` inside the
    /// try AND after it — 可能已分配变量algorithm on the blank final).
    fn is_active_group_continuation(&self, t: usize, active: &[usize]) -> bool {
        let ts = self.cfg.blocks[t].start;
        active.iter().any(|&gi| {
            ts >= self.groups[gi].end
                && self.body_group.get(&t) != Some(&gi)
                && !self.handler_group.contains_key(&t)
        })
    }

    /// True when `from` reaches `to` through statement-free
    /// Fallthrough/Goto blocks (pure jump stubs).
    fn is_stmt_free_chain_to(&self, from: usize, to: usize, seen: &mut HashSet<usize>) -> bool {
        let mut x = from;
        for _ in 0..8 {
            if x == to {
                return true;
            }
            if !seen.insert(x) {
                return false;
            }
            if !self.results[x].stmts.is_empty() {
                return false;
            }
            if !matches!(self.results[x].term, Term::Fallthrough | Term::Goto) {
                return false;
            }
            let succs = self.cfg.blocks[x].succ.clone();
            if succs.len() != 1 {
                return false;
            }
            x = succs[0];
        }
        false
    }

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

    /// Blocks reachable from this group's handler entries whose EVERY
    /// normal pred stays within handler flow: the handler's private tail
    /// (`if (interrupted) selfInterrupt(); throw t;` — jdk11 AQS
    /// .acquireQueued). They are NOT the post-try continuation: treating
    /// them as one emits the handler tail as a top-level sibling after the
    /// try (未报告的异常错误Throwable on the leaked `throw t`) and strips it
    /// out of the handler universe. A merge with any pred from normal code
    /// (jdk26 AlgorithmId.getName's shared return tail) is NOT handler-flow.
    pub(crate) fn handler_flow_only(&self, gi: usize) -> HashSet<usize> {
        let hf = self.handler_flow_only_inner(gi);
        if std::env::var("JCDC_DBG_HF").is_ok() {
            let g = &self.groups[gi];
            let mut hs: Vec<usize> = hf.iter().copied().collect();
            hs.sort();
            eprintln!(
                "HF gi={} span=({},{}) handlers={:?} hf={:?}",
                gi, g.start, g.end, g.handlers, hs
            );
        }
        hf
    }

    fn handler_flow_only_inner(&self, gi: usize) -> HashSet<usize> {
        let g = &self.groups[gi];
        let mut hf: HashSet<usize> = HashSet::new();
        let mut q: VecDeque<usize> = VecDeque::new();
        for (h, _) in &g.handlers {
            if let Some(hb) = self.cfg.block_at(*h) {
                q.push_back(hb);
            }
        }
        let in_body = |b: usize| matches!(self.body_group.get(&b), Some(&og) if og == gi);
        while let Some(b) = q.pop_front() {
            for &s in &self.cfg.blocks[b].succ {
                if hf.contains(&s) || in_body(s) || self.handler_group.contains_key(&s) {
                    continue;
                }
                // Never classify a LOOP HEADER as handler-flow-only: a
                // loop is an independent construct that some scope must
                // structure — when the fixpoint swallowed one, every
                // hf-keyed consumer inherited the whole loop as
                // "private tail" (jdk17 Files.createDirectories: the
                // parent-check handler's hf ran 10→12→16→17 absorbing
                // the iterator loop, restrict_handler_branch then
                // truncated the if-arm walk to universe {16,3}, and the
                // loop plus its `return child` tail were never
                // structured at the top level — 缺少返回语句 x2 trees).
                // Stopping AT the header keeps the handler's real
                // private blocks (Module's goto-pending stub, accept's
                // assert-throw/return chain, acquireQueued's
                // selfInterrupt+athrow) while the loop's enclosing scope
                // structures it and the post-If continuation copies
                // handle the rest.
                if self.sese_loop_headers.contains(&s)
                    || self.loops_stack.contains(&s)
                {
                    continue;
                }
                if self.cfg.blocks[s]
                    .pred
                    .iter()
                    .all(|p| hf.contains(p) || in_body(*p) || self.handler_group.contains_key(p))
                {
                    hf.insert(s);
                    q.push_back(s);
                }
            }
        }
        hf
    }

    /// A handler scope's COND branch walk must stay inside the handler's
    /// OWN flow: sub_scope's group expansion keys off body_group
    /// membership of a block, and a handler-adjacent block owned by an
    /// ENCLOSING try body widens the branch to the whole enclosing span --
    /// the post-handler continuation re-walked with the handler's (empty)
    /// group visibility emits its nested tries BARE (jdk17
    /// SignerInfo.verify's catch(Exception) debug arm swallowed the rest
    /// of the method: the initVerifyWithParam multi-catch copy lost its
    /// try -- 未报告的异常错误InvalidAlgorithmParameterException). Blocks
    /// outside the handler flow fall to the Goto arms instead;
    /// strip_handler_exit_goto renders forward ones as the natural
    /// fallthrough into the outer continuation.
    fn restrict_handler_branch(&self, sub: &mut HashSet<usize>, entry: usize) {
        let Some(&gi) = self.handler_group.get(&entry) else {
            return;
        };
        let hf = self.handler_flow_only(gi);
        // Handler-EXCLUSIVE blocks: normal flow from the method entry,
        // barred at EVERY handler head, never reaches them — their only
        // entry is through exception flow. No normal-path walk ever
        // emits them, so dropping them from the arm strands them in no
        // region: jdk17 Files.createDirectories' outermost
        // NoSuchFileException retry level lost the iterator loop +
        // `return dir` tail (blocks past a loop header are invisible to
        // the hf fixpoint — the header's pred chain crosses the
        // break-stub merge that body flow also reaches, and the
        // loop-header skip stops the fixpoint at the header itself);
        // SESE's bottom fallback then re-peeled the orphaned loop
        // without its exit return — 缺少返回语句 x2 trees. Loops whose
        // header is handler-exclusive structure normally inside the arm
        // walk (structure_loop keys off sese_loop_headers). A pred-based
        // closure cannot compute this: the loop header and its body
        // preds form a cycle that never bootstraps.
        let mut normal_reach: HashSet<usize> = HashSet::new();
        let mut q: VecDeque<usize> = VecDeque::new();
        if !self.handler_group.contains_key(&self.cfg.entry) {
            q.push_back(self.cfg.entry);
            normal_reach.insert(self.cfg.entry);
        }
        while let Some(b) = q.pop_front() {
            for &s in &self.cfg.blocks[b].succ {
                if normal_reach.contains(&s) || self.handler_group.contains_key(&s) {
                    continue;
                }
                normal_reach.insert(s);
                q.push_back(s);
            }
        }
        sub.retain(|b| {
            *b == entry
                || hf.contains(b)
                || !normal_reach.contains(b)
                || self.handler_group.get(b) == Some(&gi)
        });
        sub.insert(entry);
    }

    /// True when block `n` is the post-try continuation of some group
    /// currently being structured (or active in this walk): the owner
    /// walk emits it at the right level after the Try region, so a
    /// claimed-arrival Goto must stay a bare Goto (conversion strips it
    /// as the try-follow fallthrough) instead of an inline copy. The
    /// forward scan tolerates already-claimed blocks: by the time a
    /// sibling body path arrives at `n`, an earlier arm may have walked
    /// it (jdk11 Module.loadModuleInfoClass: block pc 20 was claimed by
    /// the if-then arm walk, yet it is gi=1's cont — copying at the
    /// fallthrough arrival duplicated the close+return chain into the
    /// body and defeated twr_j11's fold).
    fn is_cont_of_active_group(
        &self,
        n: usize,
        stop: &HashSet<usize>,
        claimed: &HashSet<usize>,
        active: &[usize],
    ) -> bool {
        let scan = |a: usize| -> bool {
            let gend = self.groups[a].end;
            for nb in self.cfg.blocks.iter() {
                if (nb.start as u32) < gend as u32 {
                    continue;
                }
                if stop.contains(&nb.id) {
                    return false;
                }
                if nb.id == n {
                    return true;
                }
                if !claimed.contains(&nb.id) && !self.is_handler(nb.id) {
                    return false;
                }
            }
            false
        };
        active.iter().copied().any(scan)
            || self.structuring_groups.borrow().iter().copied().any(scan)
    }

    /// First unclaimed non-handler block at or after `pc` that the outer
    /// walk will actually continue at. `exclude` carries the enclosing
    /// scope's barriers (loop exits, follows): a barrier block is never the
    /// outer continuation (the post-Try `next` search skips stop blocks),
    /// so naming one here would strip the try body's trailing `Goto` for a
    /// continuation that never happens -- the jump silently vanishes and
    /// the path falls into whatever the scope walks next (jdk17
    /// ResourceBundle.loadBundle: the break stub `goto 323` at the
    /// protected-span end was stripped because cont resolved to the stub
    /// itself, a loop exit in stop; the break path then fell into the null
    /// path's `continue` -- 无法访问的语句 on the real tail return).
    fn continuation_after(
        &self,
        pc: u16,
        universe: &HashSet<usize>,
        claimed: &HashSet<usize>,
        exclude: &HashSet<usize>,
    ) -> Option<usize> {
        // Blocks are in ascending-start order; the scan STOPS at the first
        // barrier (exclude) block: a continuation can never lie beyond a
        // barrier — flow reaching it leaves this scope (loop-exit break,
        // enclosing follow), and picking a block past it misroutes the
        // post-try walk (jdk26 Future.resultNow).
        for nb in self.cfg.blocks.iter() {
            if nb.start < pc {
                continue;
            }
            if exclude.contains(&nb.id) {
                return None;
            }
            if universe.contains(&nb.id) && !claimed.contains(&nb.id) && !self.is_handler(nb.id) {
                return Some(nb.id);
            }
        }
        None
    }
}

/// Strip a trailing `Goto{target}` from a region (at any tail position:
/// end of a sequence, or the tail of an if/else branch).
/// True when every flow path out of this region ends in a terminator
/// (return/throw): the region cannot complete normally, so a following
/// continuation would be unreachable (javac: 无法访问的语句). Goto/Empty
/// are conservative negatives (a Goto may resolve to a fallthrough).
/// `active` minus the groups the current walk scope already structured.
fn active_filtered(active: &[usize], structured: &HashSet<usize>) -> Vec<usize> {
    if structured.is_empty() {
        return active.to_vec();
    }
    active.iter().copied().filter(|g| !structured.contains(g)).collect()
}

pub(crate) fn region_terminates(r: &Region, results: &[crate::builder::BlockResult]) -> bool {
    region_terminates_ex(r, results, &[])
}

/// Like `region_terminates`, but a `Goto` into `handler_exits` (loop exits
/// that are exception-handler entries) also counts as terminating: inside
/// the finally-retry loop such a Goto converts to `break`, and the exit it
/// targets is the bytecode's explicit pending-exception rethrow — the
/// enclosing Java finally propagates it implicitly, so NOTHING may be
/// rendered after the loop (the continuation would copy the wrong exit's
/// throw onto the break path). A break toward a NON-handler exit is a real
/// loop completion and must NOT suppress the continuation.
pub(crate) fn region_terminates_ex(
    r: &Region,
    results: &[crate::builder::BlockResult],
    handler_exits: &[usize],
) -> bool {
    match r {
        Region::CopyStmts { block } | Region::Basic { block } => matches!(
            results[*block].term,
            crate::builder::Term::Return(_) | crate::builder::Term::Throw(_)
        ),
        // A Goto into a handler exit counts (see fn doc); so does a Goto
        // whose TARGET is a shared return/throw terminator — conversion
        // inlines those at the arrival site (term copy), so the flow is
        // abrupt here too (TempFileHelper.create's SE catch
        // `if (dir != tmpdir) <goto throw-e>; ...`).
        Region::Goto { target } => {
            handler_exits.contains(target)
                || matches!(
                    results[*target].term,
                    crate::builder::Term::Return(_) | crate::builder::Term::Throw(_)
                )
        }
        Region::Seq(v) => v
            .last()
            .map(|x| region_terminates_ex(x, results, handler_exits))
            .unwrap_or(false),
        Region::If { then_r, else_r, .. } => {
            region_terminates_ex(then_r, results, handler_exits)
                && region_terminates_ex(else_r, results, handler_exits)
        }
        // A try completes abruptly when its body does and every catch
        // does (no finally — with one, the finally's completion governs;
        // stay conservative). This is exact for region trees: a Goto
        // part names its block's terminal edge, and an If part is
        // abrupt only when BOTH branches are (jdk11/17
        // TempFileHelper.create: the for(;;) retry body =
        // try(generatePath){both IPE arms throw} + try(create){4 abrupt
        // catch arms + if/else of two areturns} — the old `_ => false`
        // made body_done miss it, the bottom-tested natural_follow
        // fallback named the IN-TRY areturns as the loop's follow, and
        // the top chain re-emitted `return Files.createDirectory(..)`
        // after the non-completing loop — 无法访问的语句 x2 trees).
        Region::Try { body, catches, .. } => {
            region_terminates_ex(body, results, handler_exits)
                && catches.iter().all(|(_, _, c)| {
                    region_terminates_ex(c, results, handler_exits)
                })
        }
        _ => false,
    }
}

/// Can a rendered Switch region complete normally (flow out of its
/// follow)? JLS 14.11: yes when the selector can match no case (no
/// default region rendered), or when the default arm does not complete
/// abruptly, or when any case arm does not (its `break` exits the
/// switch). An arm whose terminal edge is `Goto{follow}` IS the break —
/// normal completion — even when the follow block itself is a shared
/// return/throw terminator (region_terminates would call that Goto
/// abrupt: the term-copy inlining applies to gotos ACROSS scopes, not
/// to a switch's own follow binding). region_terminates is `_ => false`
/// for nested Switch, so those conservatively count as completing.
fn switch_completes_normally(
    r: &Region,
    follow: usize,
    results: &[crate::builder::BlockResult],
) -> bool {
    fn breaks_out(r: &Region, follow: usize) -> bool {
        match r {
            Region::Goto { target } => *target == follow,
            Region::Seq(v) => v.last().map(|x| breaks_out(x, follow)).unwrap_or(false),
            Region::Empty => true,
            _ => false,
        }
    }
    fn arm_abrupt(
        r: &Region,
        follow: usize,
        results: &[crate::builder::BlockResult],
    ) -> bool {
        !breaks_out(r, follow) && region_terminates(r, results)
    }
    match r {
        Region::Switch { cases, default, .. } => {
            (match default.as_deref() {
                None => true,
                Some(d) => !arm_abrupt(d, follow, results),
            }) || cases.iter().any(|(_, c)| !arm_abrupt(c, follow, results))
        }
        _ => !region_terminates(r, results),
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

/// Debug helper: first block id a region starts at (usize::MAX if none).
fn region_head_block(r: &Region) -> usize {
    match r {
        Region::Basic { block } => *block,
        Region::Seq(v) => v.first().map(region_head_block).unwrap_or(usize::MAX),
        Region::If { block, .. } => *block,
        Region::Loop { header, .. } => *header,
        Region::Switch { block, .. } => *block,
        _ => usize::MAX,
    }
}

/// Debug helper: compact variant shape of a region for traces.
fn region_shape(r: &Region) -> String {
    match r {
        Region::Basic { block } => format!("Basic({})", block),
        Region::Seq(v) => format!(
            "Seq{}[{}]",
            v.len(),
            v.iter().map(region_shape).collect::<Vec<_>>().join(",")
        ),
        Region::If { block, .. } => format!("If({})", block),
        Region::Loop { header, exits, .. } => format!("Loop({} exits={:?})", header, exits),
        Region::Switch { block, cases, default, .. } => format!(
            "Switch({} cases={} def={})",
            block,
            cases.len(),
            default.is_some()
        ),
        Region::Goto { target } => format!("Goto({})", target),
        Region::Empty => "Empty".to_string(),
        Region::Try { group_idx, .. } => format!("Try(g{})", group_idx),
        Region::CopyStmts { block } => format!("Copy({})", block),
        _ => "?".to_string(),
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
        let groups = group_exceptions_with(cfg, Some(results));
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
        Structurer { cfg, results, groups, body_group, handler_group, diamond_merges, fold_regions, fold_root_to_merge, copied_tails: HashSet::new(), loops_stack: Vec::new(), switch_depth: 0, case_arm_ctx: Vec::new(), sese_loop_headers: std::collections::HashSet::new(), sese_exc_retry_headers: std::collections::HashSet::new(), walk_depth: 0, final_fields: HashSet::new(), structuring_groups: std::cell::RefCell::new(Vec::new()) }
    }

    /// Immediate post-dominator of `entry` within `universe`. Delegates to the
    /// O(n) `immediate_postdom` (BFS nearest-confluence with successor-candidate
    /// rejection); kept as a `&mut self` method for call-site convenience.
    fn postdom_ipdom(&mut self, universe: &HashSet<usize>, entry: usize) -> Option<usize> {
        immediate_postdom(self.cfg, universe, entry)
    }

    /// True if `b` is an exception-handler head; such blocks must only be
    /// entered through their Try region, never through the normal flow.
    /// True when one of the handlers protecting `cur` is a retry
    /// trampoline: a handler with NO normal preds whose only out-edge
    /// returns to `cur`, sitting at/after the group's span end (outside
    /// the protected range). The normal-pred back-edge scan misses it
    /// (the edge INTO the handler is exceptional), so the group-vs-loop
    /// precedence wrongly lets the try carve out the header and the retry
    /// `goto` inlines as an unprotected copy of the body (jdk26
    /// Future.exceptionNow: `catch (InterruptedException e) { interrupted
    /// = true; get(); throw ..; }` — 未报告的异常错误 InterruptedException;
    /// the source is `while (true) { try { get(); .. } catch (IE) {
    /// interrupted = true; } }`).
    pub(crate) fn exc_retry_back_edge(&self, cur: usize, gi: usize) -> bool {
        let g = &self.groups[gi];
        self.cfg.exc_edges.iter().any(|e| {
            e.from == cur
                && e.to != cur
                && self.cfg.blocks[e.to].pred.is_empty()
                && self.cfg.blocks[e.to].succ.len() == 1
                && self.cfg.blocks[e.to].succ[0] == cur
                && self.cfg.blocks[e.to].start >= g.end
        })
    }

    pub(crate) fn is_handler(&self, b: usize) -> bool {
        self.handler_group.contains_key(&b)
    }

    fn term(&self, b: usize) -> &Term {
        &self.results[b].term
    }

    /// Sub-scope for a branch walk: reachable region minus already-claimed
    /// blocks (e.g. the surrounding loop header reached via a back edge).
    /// Branch region for a dual-terminator stop exit (both If targets are
    /// terminator blocks in `stop` — the check tail of javac's finally
    /// retry idiom, jdk11 ObjectInputStream.readSerialData copy2:
    /// `if (t != null) throw t; <rethrow pending>`). Inside a loop: a
    /// Goto resolves to `break` — for a handler-entry exit the pending
    /// exception is already in flight and the enclosing Java finally
    /// rethrows it implicitly, so breaking out of the retry loop IS the
    /// source semantics (the explicit `throw pending` copy would be
    /// stripped as in-flight scaffolding, leaving an empty branch that
    /// traps the loop forever → the whole post-finally flow 无法访问).
    /// Outside a loop: inline the throw (the handler's own rethrow tail).
    fn dual_terminator_branch(&self, target: usize, active: &[usize]) -> Region {
        let _ = active;
        if !self.loops_stack.is_empty() && self.is_pending_rethrow(target) {
            // Inside the finally-retry loop, an exit that rethrows the
            // PENDING exception (the local a handler entry stored) is the
            // bytecode's explicit in-flight rethrow — the enclosing Java
            // finally propagates it implicitly, so `break` out of the
            // retry loop is the source-equivalent exit (the copied
            // `throw pending` is out of lexical scope in the finally AND
            // strip_inflight_throws eats it, leaving an empty branch that
            // traps the loop forever — jdk11 ObjectInputStream
            // .readSerialData 无法访问的语句). Any other terminator exit
            // is a real source throw (the ThreadDeath override `throw t`
            // — t is a plain method local, not a handler store): inline.
            return Region::Goto { target };
        }
        Region::CopyStmts { block: target }
    }

    /// True when `b`'s terminal is `throw v` where some exception-handler
    /// entry block stores `v` (the in-flight/pending exception slot).
    fn is_pending_rethrow(&self, b: usize) -> bool {
        let var = match &self.results[b].term {
            crate::builder::Term::Throw(Expr::Local { var, .. }) => *var,
            _ => return false,
        };
        // The store must be the CATCH-PARAMETER store itself (the handler
        // entry's incoming stack is the null exception placeholder): the
        // retry idiom's accumulator `t` is also handler-stored, but from a
        // Local (`catch (ThreadDeath e) { t = e; }`) — inlining `throw t`
        // must stay (it is the source's ThreadDeath override), only the
        // pending-slot rethrow becomes the implicit-propagation break.
        self.cfg.exc_edges.iter().any(|e| {
            self.results[e.to].stmts.iter().any(|s| match s {
                crate::stmt::Stmt::LocalDef { var: v, init, .. } => {
                    *v == var && matches!(init, Some(crate::expr::Expr::Const(crate::expr::ConstVal::Null)))
                }
                crate::stmt::Stmt::ExprStmt(crate::expr::Expr::Assign { target, value, .. }) => {
                    matches!(target.as_ref(), crate::expr::Expr::Local { var: v, .. } if *v == var)
                        && matches!(&**value, crate::expr::Expr::Const(crate::expr::ConstVal::Null))
                }
                _ => false,
            })
        })
    }

/// Is `t` the header of a natural loop containing a back edge from `cur`-side
/// flow? Approximation used by the walk's back-edge arm: `t` dominates the
/// edge source (the arm's entry condition) AND some predecessor path of the
/// current region loops — but the simple, robust signal here is: the Goto arm
/// only runs when `dom.dominates(t, cur)` already held (see caller), so a
/// terminator `t` that also has an incoming exc-handler back edge is a retry
/// loop header. Callers pass the structurer for cfg access.
fn ctx_is_loop_header(s: &Structurer, t: usize) -> bool {
    // EXACT retry idiom only: t's protected range is caught by a handler
    // with no normal preds whose sole out-edge returns to t (Future
    // .exceptionNow: range (40,57) caught at 57, `goto 40`). Broader
    // "any handler flows to t" shapes matched shared RETURN tails whose
    // arrivals legitimately need the terminator copy (jdk26 Resolver
    // 缺少返回语句 x2 regression).
    s.cfg.exc_edges.iter().any(|e| {
        e.from == t
            && e.to != t
            && s.cfg.blocks[e.to].pred.is_empty()
            && s.cfg.blocks[e.to].succ.len() == 1
            && s.cfg.blocks[e.to].succ[0] == t
    }) && matches!(
        s.results[t].term,
        crate::builder::Term::Return(_) | crate::builder::Term::Throw(_)
    )
}

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
        // The walk root itself seeds the group expansion even when it lies
        // OUTSIDE the passed universe: a protected branch target from a
        // smaller group's body walk (jdk11 SocketChannelImpl.finishConnect's
        // `if (!isConnected())` then-arm — block pc 39 belongs to the
        // readLock/writeLock finally groups (39..174)/(39..167)/(46..105)
        // but the If sits inside group (14..23), whose body universe is
        // {2,3}; owner_scope then filtered everything and the expansion
        // loop had nothing to key off) got sub = {from} alone — the arm
        // emitted Goto{pc 46} and the ENTIRE connect-retry body (loop,
        // endFinishConnect, return true) vanished, leaving the
        // catch(IOException) try body unable to throw (不能抛出异常错误) and
        // the blocking/connected locals dangling. The holds_start guard
        // still blocks mid-group roots from ballooning (getInputStream0).
        eff.insert(from);
        let seed = eff.clone();
        for &b in &seed {
            if let Some(&gi) = self.body_group.get(&b) {
                let g = &self.groups[gi];
                // Expand to the full span ONLY when the scope holds the
                // group's START block: a walk rooted mid-group (a
                // handler-restricted arm at a single continuation block,
                // jdk11 getInputStream0's RT-catch arm -> block 33) must
                // not balloon to the whole enclosing span — it dragged the
                // entire method body into the catch with the handler's
                // (nested-less) group visibility, emitting the reflection
                // try's call bare (未报告的异常错误NoSuchFieldException).
                let holds_start = self
                    .cfg
                    .blocks
                    .iter()
                    .any(|nb| nb.start == g.start && seed.contains(&nb.id));
                if !holds_start {
                    continue;
                }
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
    /// True when the normal edge `p -> cur` closes a cycle at `cur`:
    /// either `cur` dominates `p` in the scope's normal-flow dominator
    /// tree, or `p` is exception-only reachable (compute_dominators'
    /// RPO walks normal succ edges only, so handler-flow blocks keep
    /// the idom[p]==p sentinel) and `cur` reaches `p` over the
    /// exc-augmented CFG — the catch-and-retry back edge (jdk11
    /// AbstractClassLoaderValue.putIfAbsent: the Throwable handler's
    /// `goto H` is the retry loop's only inbound edge to H besides the
    /// pre-loop init; jdk11/17 ObjectInputStream$1.run's superclass
    /// walk update block). The scope's dom root is excluded: its idom
    /// is itself too, and root->cur with cur reaching the root is just
    /// the enclosing scope's circulation.
    fn closes_back_edge(
        &self,
        cur: usize,
        p: usize,
        dom: &DomInfo,
        entry: usize,
        use_exc: bool,
    ) -> bool {
        if p == cur {
            return true;
        }
        if dom.dominates(cur, p) {
            return true;
        }
        if !use_exc {
            return false;
        }
        // Exclusions: `p == entry` is the scope root's forward edge
        // (root→cur with cur reaching the root is the enclosing scope's
        // circulation, not a loop at cur), and an exc-only `cur` that is
        // not the root is a mid-cycle handler-flow member (jdk11
        // Process.waitFor's sleep block — the genuine header sits two
        // hops up). The root itself (cur == entry, idom[root]==root by
        // construction) stays eligible: jdk26 Future.exceptionNow's
        // finally-group body walk is rooted AT the retry header.
        if dom.idom[p] == p && p != entry {
            let root_walk = cur == entry;
            if root_walk {
                // A sub-scope root whose sentinel pred is the sub-scope's
                // own branch head is an if-ARM walk: the head-to-root
                // "cycle" runs out through the ENCLOSING loop's iterator
                // (jdk11 FileDescriptor.closeAll: spurious
                // while(true){addSuppressed;break} arm wrappers). The
                // genuine root-walk retry header (jdk26
                // Future.exceptionNow's finally-group body walk rooted AT
                // the protected-span start) has its back-edge source as a
                // DIRECT exception successor: require that exact edge.
                if !self.cfg.exc_edges.iter().any(|e| e.from == cur && e.to == p)
                {
                    return false;
                }
            } else if dom.idom[cur] == cur {
                // Exc-only mid-cycle member (jdk11 Process.waitFor's
                // sleep block): the genuine header sits upstream.
                return false;
            }
            let mut xs: HashMap<usize, Vec<usize>> = HashMap::new();
            for e in &self.cfg.exc_edges {
                xs.entry(e.from).or_default().push(e.to);
            }
            return can_reach_cfg_barred(self.cfg, &xs, cur, p, &HashSet::new(), 8192);
        }
        false
    }

    fn is_loop_header(
        &self,
        cur: usize,
        universe: &HashSet<usize>,
        dom: &DomInfo,
        entry: usize,
        use_exc: bool,
    ) -> bool {
        // Enclosing-loop circulation artifact: a walk entry whose only
        // successor is an ENCLOSING loop header (a `st = -1; goto head`
        // case stub) reaches every in-universe block through that header,
        // so the scope-rooted dominator makes `cur` dominate its own
        // switch-dispatch preds and the back-edge test fires on a cycle
        // that belongs to the enclosing loop — a spurious single-member
        // `while (true) { st = -1; continue L1; }` (jdk26 xml
        // impl.Parser.xml's default-case wrappers: the switch lost its
        // default semantics, sibling cases fell through, and the
        // post-switch tail went unreachable — 无法访问的语句). The pred
        // only counts when it is reachable from `cur` WITHOUT passing
        // through the enclosing header (a genuine loop of `cur`).
        let single_enclosing_succ = self.cfg.blocks[cur].succ.len() == 1
            && {
                let x = self.cfg.blocks[cur].succ[0];
                x != cur
                    && (self.loops_stack.contains(&x)
                        || self.sese_loop_headers.contains(&x)
                        || self.sese_exc_retry_headers.contains(&x))
            };
        // Exc-only-reachable preds (handlers and their downstream blocks)
        // never get a normal-flow dominator: compute_dominators' RPO walks
        // normal succ edges only, so such a block keeps the idom[p]==p
        // sentinel and every dominates() query on it is false. When it
        // carries a NORMAL edge back into `cur`, that is a genuine back
        // edge of a catch-and-retry loop whose cycle runs through a throw
        // (jdk11/17 ObjectInputStream$1.run: `for (cl = subcl; cl !=
        // ObjectInputStream.class; cl = cl.getSuperclass())` — the update
        // block's only inbound edge is try2's exception edge; walk missed
        // the loop, copy_walk unrolled 5 nested copies and the tail
        // `return TRUE` was lost — 缺少返回语句). Verify the cycle on the
        // exc-augmented CFG (same view structure_loop's membership scan
        // uses). The scope's dom root is excluded: idom[root]==root too,
        // and root→cur with cur⇝root is just the enclosing loop's normal
        // circulation, not a loop at `cur`.
        let mut exc_succ: Option<HashMap<usize, Vec<usize>>> = None;
        for &p in &self.cfg.blocks[cur].pred {
            if p == cur {
                return true;
            }
            // In-scope arrivals only: a pred outside this walk's
            // universe belongs to a sibling region (a handler arm being
            // structured by structure_try). Its back edge is the retry
            // loop of the ENCLOSING scope — claiming it here wraps the
            // protected block in a spurious inner while(true) whose
            // header never lands in loops_stack when the handler arm
            // walks, so the retry `goto head` lost its continue (jdk26
            // Future.exceptionNow: catch(IE){interrupted=true} fell off
            // the method — 缺少返回语句). The dominance branch never saw
            // such preds either (out-of-universe preds have sentinel
            // idoms); the exc-augmented branch must keep the same view.
            if universe.contains(&p) && self.closes_back_edge(cur, p, dom, entry, use_exc) {
                if single_enclosing_succ {
                    let x = self.cfg.blocks[cur].succ[0];
                    let mut barriers: HashSet<usize> = HashSet::new();
                    barriers.insert(x);
                    if !can_reach_cfg_barred(
                        self.cfg,
                        &HashMap::new(),
                        cur,
                        p,
                        &barriers,
                        8192,
                    ) {
                        continue;
                    }
                }
                return true;
            }
        }
        false
    }

    /// Structure the whole method.
    pub fn structure_method(&mut self) -> Region {
        // From-scratch SESE/dominator-tree structurer (rewrite), gated so the
        // default path is the verified `walk` baseline.
        let dbg_regions = std::env::var("JCDC_DBG_REGIONS").is_ok();
        if std::env::var("JCDC_SESE").is_ok() {
            let r = self.structure_method_sese();
            if dbg_regions {
                eprintln!("REGIONS_SESE {:#?}", r);
            }
            return r;
        }
        let universe: HashSet<usize> = self
            .cfg
            .blocks
            .iter()
            .filter(|b| !b.ins.is_empty())
            .map(|b| b.id)
            .collect();

        // Exc-mediated retry headers must be known to the walk too: its
        // loop-structuring branch and back-edge scans consult
        // sese_exc_retry_headers, which only the SESE precompute used to
        // fill — in walk-only mode catch-and-retry loops unrolled into
        // nested try copies (ois auditSubclass 缺少返回语句 x2 trees).
        // sese_loop_headers stays EMPTY here on purpose: feeding walk the
        // full natural-header set regressed 6/6/6 (the 1969e0bb lesson —
        // walk-side consumers must use the exc-only subset).
        {
            let idom = compute_dominators(self.cfg, &universe, self.cfg.entry);
            let mut lh: HashSet<usize> = HashSet::new();
            self.precompute_exc_retry(&universe, &idom, &mut lh);
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
    pub(crate) fn walk(
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
        // Groups this scope has already structured: their continuations
        // are OWNED by this walk from structure_try's `cont` step on —
        // the active-group-continuation guards must no longer defer to
        // an owner that IS this scope (jdk11/17 TimeZone.setDefaultZone:
        // the post-try fall-out `goto tail` was elided as "the owner
        // will emit it" and the shared `return tz` tail vanished from
        // the try's normal path — 缺少返回语句 x2 trees).
        let mut structured_here: HashSet<usize> = HashSet::new();
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
                            None => {
                                // copy_walk refused (typically the
                                // re-entry guard: `cur` flows back into
                                // this walk's entry region). When `cur`
                                // is a STATEMENT-BEARING back-edge
                                // preheader — its flow re-enters an
                                // open loop header — a bare Goto
                                // resolves to `continue` and SILENTLY
                                // DROPS cur's statements at this
                                // arrival (jdk26 ClassPrinterImpl
                                // toYaml/toXml BLOCK case: the shared
                                // toYaml(ternary-indent, ..) merge
                                // block was claimed by the sibling
                                // arm's copy; the indent+1 arm lost
                                // the call and left a dangling
                                // `stack0 = indent + 1`). Copy the
                                // statements and keep the Goto for the
                                // continue (KeyStore backedge-stub
                                // pattern).
                                if !self.results[cur].stmts.is_empty()
                                    && self.cfg.blocks[cur].succ.iter().any(|&s2| {
                                        self.loops_stack.contains(&s2)
                                            || self.sese_loop_headers.contains(&s2)
                                            || can_reach_cfg(self.cfg, s2, entry, 4096)
                                    })
                                {
                                    parts.push(Region::Seq(vec![
                                        Region::CopyStmts { block: cur },
                                        Region::Goto { target: cur },
                                    ]));
                                } else if self.results[cur].stmts.is_empty()
                                    && matches!(self.results[cur].term, Term::Fallthrough)
                                    && self.cfg.blocks[cur].succ.len() == 1
                                    && universe.contains(&self.cfg.blocks[cur].succ[0])
                                    && !stop.contains(&self.cfg.blocks[cur].succ[0])
                                    && parts
                                        .iter()
                                        .any(|p| region_head_block(p) == self.cfg.blocks[cur].succ[0])
                                {
                                    // Fall-into-sibling: `cur` is a
                                    // statement-free fallthrough whose
                                    // successor is THIS walk's immediate
                                    // next part — an if-else chain's
                                    // inner block boundary (jdk17
                                    // JarFile.getBytes: the readNBytes
                                    // A-arm's tail merge block 6 starts
                                    // the B-arm copy that follows the
                                    // chain; the plain Goto{6} was
                                    // elided as a natural fallthrough
                                    // and the A-arm ran straight into
                                    // readAllBytes — double read +
                                    // spurious EOFException). Materialize
                                    // the jump so the sibling copy is
                                    // skipped.
                                    parts.push(Region::Goto { target: cur });
                                } else {
                                    parts.push(Region::Goto { target: cur });
                                }
                            }
                        }
                    } else {
                        parts.push(Region::Goto { target: cur });
                    }
                } else if self.loops_stack.contains(&cur)
                    || self.sese_loop_headers.contains(&cur)
                {
                    // An EMPTY region arriving at an enclosing loop header
                    // IS the back edge (jdk26 Future.exceptionNow's
                    // `catch (InterruptedException e) { interrupted =
                    // true; }` retry — the handler's only out-edge is
                    // `goto head`): emit the Goto so conversion resolves
                    // it to `continue`. Dropping it lets the handler fall
                    // out of the try silently.
                    parts.push(Region::Goto { target: cur });
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
                .copied()
                .or_else(|| {
                    // A group starting at `cur` that `active` does not
                    // carry: under SESE only OUTERMOST groups are active at
                    // the top level, and handler-arm scopes inherit the
                    // handler's (span-limited) visibility — a nested group
                    // reached there was emitted BARE, losing its try
                    // (jdk11 HttpURLConnection.getInputStream0: the RT-catch
                    // arm re-walked the continuation and the reflection
                    // try/catch(IllegalAccessException|NoSuchFieldException)
                    // vanished — 未报告的异常错误). Carve it out unless an
                    // ACTIVE group strictly enclosing `cur` owns the
                    // carve-out (the intact enclosing body walk case).
                    let covered_by_active = self.groups.iter().enumerate().any(|(oj, og)| {
                        active.contains(&oj)
                            && og.start <= b.start
                            && og.end > b.start
                            && !(og.start == b.start && og.end >= b.end)
                    });
                    if covered_by_active || self.handler_group.contains_key(&cur) {
                        return None;
                    }
                    self.groups
                        .iter()
                        .enumerate()
                        .filter(|(gi, g)| {
                            g.start == b.start
                                && g.end >= b.end
                                && !self.structuring_groups.borrow().contains(gi)
                        })
                        .max_by_key(|(_, g)| g.end)
                        .map(|(gi, _)| gi)
                });
            // The group starts at a LOOP HEADER whose back edge lies
            // OUTSIDE the protected span (`for (;;) { try { ... } catch
            // { ... } ...retry... }` — jdk26 ClassValue.getFromHashMap):
            // the loop is the enclosing construct. Structuring the try
            // first consumes the header and leaves the back edge to be
            // duplicated or dropped (walk: silent lost retry loop +
            // missing return; SESE: 3× unrolled copies). Let the
            // loop-header branch below win; the body walk re-finds this
            // group at its start. try{while} keeps group-first: its back
            // edge is INSIDE the protected span.
            let group_here = group_here.filter(|&gi| {
                entry_preclaimed
                    || !(self.is_loop_header(cur, universe, &dom, entry, true)
                        || self.sese_loop_headers.contains(&cur)
                        // Exc-retry headers count too: the retry loop of
                        // `for(;;){try{..}catch{.. goto head}}` wraps the
                        // try even when the try's protected span starts
                        // AT the header (jdk26 Future.exceptionNow: the
                        // finally-group body walk must structure the loop
                        // around the inner IE/EE try so the IE handler's
                        // `goto head` resolves to `continue` against
                        // loops_stack — without it the inner group won,
                        // a degenerate while(true){get();throw} absorbed
                        // the protected block, and catch(IE){interrupted
                        // =true} fell off the method — 缺少返回语句).
                        || self.sese_exc_retry_headers.contains(&cur))
                    || !self.cfg.blocks[cur].pred.iter().any(|&p| {
                        // No universe filter: an exc-mediated retry back
                        // edge's source is handler flow — carved OUT of
                        // this body walk's universe by construction
                        // (Future.exceptionNow's IE handler at pc 57).
                        p != cur
                            && self.closes_back_edge(cur, p, &dom, entry, true)
                            && (self.cfg.blocks[p].end <= self.groups[gi].start
                                || self.cfg.blocks[p].start >= self.groups[gi].end)
                    })
            });
            if let Some(gi) = group_here {
                let outer_universe = universe.clone();
                let try_region = self.structure_try(gi, universe, &outer_universe, claimed, stop);
                parts.push(try_region);
                structured_here.insert(gi);
                let gend = self.groups[gi].end;
                let hf_next = self.handler_flow_only(gi);
                let next = self.cfg.blocks.iter().find(|nb| {
                    nb.start >= gend
                        && universe.contains(&nb.id)
                        && !stop.contains(&nb.id)
                        && !claimed.contains(&nb.id)
                        && !self.is_handler(nb.id)
                        && !hf_next.contains(&nb.id)
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
            // sese_loop_headers carries the exception-mediated retry
            // headers (handler-flow back edges invisible to this scope's
            // normal dominance): a try-group body walk that reaches the
            // header of an enclosing `for(;;){try{..}catch{..continue}}`
            // must structure the loop, else the handler's `goto head`
            // copy_walks the head into nested duplicate tries (jdk26
            // DateTimeFormatter.parseBest unrolled 5 deep, the
            // loop-exhausted `throw DateTimeException` lost —
            // 缺少返回语句 x3 trees).
            if !at_preclaimed_entry
                && (self.is_loop_header(cur, universe, &dom, entry, true)
                    || self.sese_exc_retry_headers.contains(&cur))
            {
                let loop_r = self.structure_loop(cur, universe, stop, active, claimed, &dom);
                // A body that cannot complete normally (both arms of its
                // tail check inline the loop's terminator exits — the
                // finally-retry dual-throw shape, jdk11 ObjectInputStream
                // .readSerialData) makes any post-loop continuation
                // unreachable (无法访问的语句): neither continue at a
                // follow nor copy a terminator exit after it.
                let body_done = match &loop_r {
                    Region::Loop { body, exits, .. } => {
                        let handler_exits: Vec<usize> = exits
                            .iter()
                            .copied()
                            .filter(|e| self.is_handler(*e))
                            .collect();
                        region_terminates_ex(body, self.results, &handler_exits)
                    }
                    _ => false,
                };
                let next = if body_done {
                    None
                } else {
                    self.next_after_loop(&loop_r, universe, stop, claimed)
                };
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
                        if !body_done {
                            for &e in &loop_exits {
                                if !stop.contains(&e) && self.is_terminator_block(e) {
                                    parts.push(Region::CopyStmts { block: e });
                                    break;
                                }
                            }
                        }
                        // An exit that is an ENCLOSING loop's barrier (in
                        // `stop`) must still be materialized as a Goto: it
                        // converts to the labeled break of the enclosing
                        // loop. Dropping it lets the enclosing loop body
                        // end in an implicit continue — the normal
                        // completion of the inner loop re-entered the
                        // outer instead of leaving it (jdk11
                        // FutureTask.removeWaiter spun forever; javac:
                        // 无法访问的语句 on the tail return once the
                        // continue-stub walks were filtered).
                        if !body_done
                            && parts
                                .last()
                                .map(|r| !matches!(r, Region::Goto { .. }))
                                .unwrap_or(true)
                        {
                            if let Some(&e) = loop_exits
                                .iter()
                                .filter(|e| {
                                    stop.contains(e)
                                        && !self.loops_stack.contains(e)
                                        && universe.contains(e)
                                })
                                .min_by_key(|e| self.cfg.blocks[**e].start)
                            {
                                parts.push(Region::Goto { target: e });
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
                    // EXCEPTION — the terminator carries blank-final field
                    // assignments: those must execute EXACTLY once on every
                    // path, and every copy route (CopyStmts, term copy,
                    // SWTAIL) refuses final-writers, so no arm can absorb
                    // the tail. Nulling the follow lets the FIRST arm's
                    // walk flow into the merge and claim it, and the
                    // sibling arms fall off without the assignments
                    // (jdk11 LocaleProviderAdapter clinit:
                    // adapterPreference/NONEXISTENT_ADAPTER assigned only
                    // in the typeList.isEmpty() arm; jdk26
                    // ObjectInputFilter$Config clinit:
                    // invalidFactoryMessage — 可能尚未初始化变量).
                    if let Some(p) = pd {
                        if self.is_terminator_block(p)
                            && p != taken
                            && p != fall
                            && !self.terminator_writes_final(p)
                        {
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
                    if std::env::var("JCDC_DBG_IF").is_ok() {
                        // absorb_pure is &mut and CLAIMS the absorbed block
                        // — calling it here for the printout pre-claimed the
                        // taken arm and flipped the real decision below
                        // (JarFile.getBytes rendered a different shape under
                        // JCDC_DBG_IF than in production). Debug must be
                        // pure observation.
                        eprintln!(
                            "THENDECIDE cur={} taken={} fall={} follow={:?} stop_t={} stop_f={} term_t={} term_f={} univ_t={} claim_t={}",
                            cur, taken, fall, follow, stop.contains(&taken), stop.contains(&fall),
                            self.is_terminator_block(taken), self.is_terminator_block(fall),
                            universe.contains(&taken), claimed.contains(&taken)
                        );
                    }
                    let then_r = if Some(taken) == follow && !stop.contains(&taken) {
                        Region::Empty
                    } else if Some(taken) == follow
                        && stop.contains(&taken)
                        && self.is_terminator_block(taken)
                        && !self.loops_stack.is_empty()
                        && self.loops_stack[self.loops_stack.len() - 1] != cur
                    {
                        // Loop-bottom exit test with a TERMINATOR exit
                        // (`if (i >= n) <return-tail>; else <digit; goto
                        // head>;`): the then arm must materialize as
                        // `break`. Leaving it Empty relies on the tail copy
                        // after the loop, but a `while (true)` body without
                        // any break is a JLS non-completing loop —
                        // prune_unreachable then deletes the tail copy
                        // (jdk11/17 InstantPrinterParser.format's second
                        // loop copy lost `append('Z'); return true` —
                        // 缺少返回语句). classify_loop's split_leading_if
                        // still rotates a HEADER test into the while
                        // condition (cur != header guard keeps top-tested
                        // shapes on the old Empty path).
                        Region::Goto { target: taken }
                    } else if Some(taken) == follow
                        && stop.contains(&taken)
                        && !self.is_terminator_block(taken)
                    {
                        // The "follow" is an enclosing barrier (loop exit):
                        // the branch is a jump out, not a fallthrough.
                        // Terminator exits stay Empty — the return/throw is
                        // emitted after the loop. UNLESS the exit chains into
                        // an already-claimed terminator (restart-loop guarded
                        // case: breaking lands after the loop where nothing
                        // remains; jdk26 DecimalFormat case 6).
                        if !self.loops_stack.contains(&taken)
                            && self.stop_chain_to_claimed_terminator(taken, claimed)
                        {
                            // `taken` is the if-follow and sits in bstop;
                            // copy_walk's reachable_within would exclude the
                            // entry itself — lift it for the copy.
                            let mut cstop = bstop.clone();
                            cstop.remove(&taken);
                            match self.copy_walk(taken, &cstop, active, cur) {
                                Some(r) => r,
                                None => Region::Goto { target: taken },
                            }
                        } else {
                            Region::Goto { target: taken }
                        }
                    } else if let Some(absorbed) = self.absorb_pure(taken, universe, &bstop, claimed, active) {
                        absorbed
                    } else if universe.contains(&taken)
                        && !bstop.contains(&taken)
                        && !claimed.contains(&taken)
                        && !(self.is_handler(taken) && active.is_empty())
                    {
                        let branch_universe = self.owner_scope(taken, universe);
                        let mut sub = self.sub_scope(taken, &branch_universe, &bstop, claimed);
                        self.restrict_handler_branch(&mut sub, entry);
                        self.walk(taken, &sub, &bstop, active, claimed, false)
                    } else if !stop.contains(&taken)
                        && !claimed.contains(&taken)
                        && !self.is_terminator_block(taken)
                        && self.cfg.exc_edges.iter().any(|e| e.from == taken)
                    {
                        // A PROTECTED branch target outside this scope's
                        // universe (an enclosing try body split it into
                        // another owner group): walking it gives the flow
                        // its own try carve-out and materializes its
                        // statements. Region::Empty here silently deleted
                        // the branch AND left the group unstructured —
                        // jdk17 HttpURLConnection.getOutputStream's
                        // `return getOutputStream0()` arm vanished and the
                        // doPrivileged call lost its
                        // catch(PrivilegedActionException)
                        // (未报告的异常错误 x2 methods, sj17 tree).
                        let branch_universe = self.owner_scope(taken, universe);
                        let mut sub = self.sub_scope(taken, &branch_universe, &bstop, claimed);
                        self.restrict_handler_branch(&mut sub, entry);
                        self.walk(taken, &sub, &bstop, active, claimed, false)
                    } else {
                        // Target is the follow (empty), or already structured
                        // (loop header → continue; loop exit → break).
                        if self.is_terminator_block(taken)
                            && !stop.contains(&taken)
                            && !self.terminator_writes_final(taken)
                        {
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
                                && !self.terminator_writes_final(taken)
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
                            // resolves it to `break` — UNLESS the exit chains
                            // into an already-claimed terminator (the
                            // restart-loop guarded case: breaking would land
                            // after the loop where nothing remains and the
                            // body is lost; jdk26 DecimalFormat case 6).
                            if !self.loops_stack.contains(&taken)
                                && self.stop_chain_to_claimed_terminator(taken, claimed)
                            {
                                let mut cstop = bstop.clone();
                                cstop.remove(&taken);
                                match self.copy_walk(taken, &cstop, active, cur) {
                                    Some(r) => r,
                                    None => Region::Goto { target: taken },
                                }
                            } else {
                                Region::Goto { target: taken }
                            }
                        } else if self.is_terminator_block(taken)
                            && stop.contains(&taken)
                            && self.is_terminator_block(fall)
                            && stop.contains(&fall)
                        {
                            self.dual_terminator_branch(taken, active)
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
                        && self.is_terminator_block(fall)
                        && !self.loops_stack.is_empty()
                        && self.loops_stack[self.loops_stack.len() - 1] != cur
                    {
                        // Loop-bottom exit test, inverted orientation: the
                        // FALL side is the terminator exit (see the taken
                        // side).
                        Region::Goto { target: fall }
                    } else if Some(fall) == follow
                        && stop.contains(&fall)
                        && !self.is_terminator_block(fall)
                    {
                        // The "follow" is an enclosing barrier (loop exit):
                        // the branch is a jump out, not a fallthrough.
                        // Terminator exits stay Empty — the return/throw is
                        // emitted after the loop. See the taken side for the
                        // claimed-terminator-chain exception.
                        if !self.loops_stack.contains(&fall)
                            && self.stop_chain_to_claimed_terminator(fall, claimed)
                        {
                            let mut cstop = bstop.clone();
                            cstop.remove(&fall);
                            match self.copy_walk(fall, &cstop, active, cur) {
                                Some(r) => r,
                                None => Region::Goto { target: fall },
                            }
                        } else {
                            Region::Goto { target: fall }
                        }
                    } else if let Some(absorbed) = self.absorb_pure(fall, universe, &bstop, claimed, active) {
                        absorbed
                    } else if Some(taken) == follow
                        && !stop.contains(&taken)
                        && universe.contains(&taken)
                        && !claimed.contains(&taken)
                        && !self.is_terminator_block(taken)
                        && !self.results[taken].stmts.is_empty()
                        && !self.loops_stack.contains(&taken)
                        && !(self.is_handler(taken) && active.is_empty())
                        && !bstop.contains(&fall)
                        && !claimed.contains(&fall)
                        && universe.contains(&fall)
                        && !(self.is_handler(fall) && active.is_empty())
                    {
                        // PARKED-ELSE COMPLETION (the systemic empty-arm
                        // family): `taken` is the If's follow AND a
                        // statement-bearing in-universe block — the
                        // if-else-if chain shape javac emits for a shared
                        // else body (`if (t1) goto B; if (t2) goto B; A;
                        // goto M; B: ...; M: ...`). The then-arm renders
                        // Region::Empty (correct: it falls into B's
                        // statements parked after the chain), but the ELSE
                        // arm's flow continues PAST B — its terminal
                        // Goto{M} is elided at conversion (goto_is_last)
                        // and the arm falls INTO the parked B statements:
                        // double execution on the else path and B skipped
                        // on its real predecessors' path (jdk17
                        // JarFile.getBytes: the readNBytes A-arm ran
                        // straight into readAllBytes; Pattern.clazz's
                        // Bound arm, DatagramChannelImpl.receive,
                        // SocketChannelImpl, HttpURLConnection carry the
                        // same latent shape). Complete the else arm with
                        // its OWN copy of the parked chain — exactly what
                        // the GOTO-FT/GOTO-CLAIMED shared-tail arrivals
                        // already do for claimed targets: per-arrival
                        // copies are the bytecode semantics.
                        let branch_universe = self.owner_scope(fall, universe);
                        let mut sub = self.sub_scope(fall, &branch_universe, &bstop, claimed);
                        self.restrict_handler_branch(&mut sub, entry);
                        let arm = self.walk(fall, &sub, &bstop, active, claimed, false);
                        // BYPASS DISCRIMINATOR: completion is needed only
                        // when some arm path's terminal flow skips the
                        // parked follow (a trailing Goto targeting
                        // something other than `taken`, at any nesting
                        // depth — JarFile's A-arm ends at Goto{epilogue
                        // 11}, not the parked B 6). Exempt targets are
                        // TRUE JUMPS, never fallthrough bypasses: loop
                        // headers/exits and switch follows embedded in
                        // the arm (resolve to continue/break), the
                        // enclosing loops_stack and case_arm_ctx
                        // follows, and this scope's barriers (bstop —
                        // enclosing loop exits resolve to break at
                        // conversion; Files.walkFileTree's TERMINATE
                        // arm ends at Goto{loop-exit} and inverted when
                        // wrongly completed). NOT exempt: an active
                        // group's post-try continuation when the parked
                        // follow's statements still sit between the arm
                        // and it at render time (JarFile's b11 — the
                        // owner emits the follow chain BEFORE the cont,
                        // so the bare fallthrough would cross the parked
                        // B statements). The ordinary empty-then `if`
                        // (every arm path flows into the follow
                        // naturally) needs no copy — completing it would
                        // duplicate the tail through every such if in
                        // the corpus (25-class matrix churn).
                        let mut jump_exempt: HashSet<usize> = HashSet::new();
                        Region::jump_targets(&arm, &mut jump_exempt);
                        jump_exempt.extend(self.loops_stack.iter().copied());
                        jump_exempt.extend(
                            self.case_arm_ctx.iter().filter_map(|c| c.1),
                        );
                        jump_exempt.extend(bstop.iter().copied());
                        let bypass = Region::bypasses_exempt(&arm, taken, &jump_exempt);
                        // The parked chain: statement blocks flowing from
                        // `taken` up to the blocks this arm already copied
                        // (their per-arrival copies render inside the arm;
                        // the sibling emits the rest).
                        let mut chain: HashSet<usize> = HashSet::new();
                        if bypass {
                            let mut b = taken;
                            for _ in 0..64 {
                                if chain.contains(&b)
                                    || b == cur
                                    // bstop holds the follow == the chain
                                    // head itself; only deeper barriers
                                    // (loop exits) end the chain.
                                    || (b != taken && bstop.contains(&b))
                                    || self.loops_stack.contains(&b)
                                    || self.is_handler(b)
                                    || claimed.contains(&b)
                                    || self.terminator_writes_final(b)
                                {
                                    break;
                                }
                                if arm.iter_parts().iter().any(|p| region_head_block(p) == b) {
                                    break;
                                }
                                let term = self.results[b].term.clone();
                                let stmts_ok = !self.results[b].stmts.is_empty()
                                    || matches!(term, Term::Fallthrough | Term::Goto);
                                if !stmts_ok {
                                    break;
                                }
                                chain.insert(b);
                                match term {
                                    Term::Fallthrough | Term::Goto
                                        if self.cfg.blocks[b].succ.len() == 1 =>
                                    {
                                        b = self.cfg.blocks[b].succ[0];
                                    }
                                    _ => break,
                                }
                            }
                        }
                        if chain.is_empty() {
                            if std::env::var("JCDC_DBG_IF").is_ok() {
                                eprintln!("PARKCHAIN cur={} chain=EMPTY arm={}", cur, region_shape(&arm));
                            }
                            arm
                        } else {
                            // The chain walk must stay a SIMPLE tail
                            // reproduction: universe = chain + forward
                            // flow closure under the FULL parent
                            // barriers (stop ∪ bstop minus the chain
                            // itself, plus every enclosing loop header —
                            // back edges into open loops belong to the
                            // loop's own structuring, never to an arm
                            // copy: huc getInputStream0's follow 41
                            // flows around the auth retry loop and the
                            // unbarriered closure restructured
                            // Loop(41)+5 regions inside the else arm).
                            let mut cu: HashSet<usize> = chain.clone();
                            {
                                let mut q: Vec<usize> = chain.iter().copied().collect();
                                let mut seen: HashSet<usize> = chain.clone();
                                while let Some(b) = q.pop() {
                                    for &s2 in &self.cfg.blocks[b].succ {
                                        if bstop.contains(&s2)
                                            || stop.contains(&s2)
                                            || self.loops_stack.contains(&s2)
                                        {
                                            continue;
                                        }
                                        if seen.insert(s2) {
                                            cu.insert(s2);
                                            q.push(s2);
                                        }
                                    }
                                }
                            }
                            let mut cstop: HashSet<usize> = bstop.union(stop).copied().collect();
                            cstop.extend(self.loops_stack.iter().copied());
                            cstop.retain(|x| !chain.contains(x));
                            // SCRATCH claimed set: a rejected completion
                            // must leave no claims behind (an abandoned
                            // exploratory walk claiming the follow would
                            // degrade the parent's parked-sibling arrival
                            // to a bare elided Goto — the very statement
                            // loss the completion exists to prevent).
                            // copied_tails must roll back too: conversion's
                            // reaches_copy_tail elides RawGotos targeting
                            // copy-walked tails, and the exploratory walk's
                            // copy_walks poisoned that set for the parent's
                            // own (identical-shape) walk.
                            let saved_claims = claimed.clone();
                            let mut scratch = claimed.clone();
                            let saved_tails = self.copied_tails.clone();
                            let saved_groups = self.structuring_groups.borrow().clone();
                            let saved_loops = self.loops_stack.clone();
                            let saved_switch_depth = self.switch_depth;
                            let saved_case_ctx = self.case_arm_ctx.clone();
                            let saved_walk_depth = self.walk_depth;
                            let taken_r = self.walk(taken, &cu, &cstop, active, &mut scratch, false);
                            if std::env::var("JCDC_DBG_IF").is_ok() {
                                eprintln!(
                                    "PARKCHAIN cur={} chain={:?} cu={} cstop={:?} taken_r={}",
                                    cur, chain, cu.len(), cstop, region_shape(&taken_r)
                                );
                            }
                            // Accept only SIMPLE completions (linear
                            // blocks, copied tails, elision-safe gotos,
                            // plain if-diamonds). A Loop/Try/Switch in
                            // the result means the parked flow is
                            // structural territory the PARENT walk must
                            // own — back off and keep the historical
                            // shape (adding a copy anyway lost huc's
                            // serverAuthentication.addToCache: the arm
                            // claimed the follow, the parent's arrival
                            // degraded to a bare elided Goto).
                            fn simple_completion(r: &Region) -> bool {
                                match r {
                                    Region::Basic { .. }
                                    | Region::CopyStmts { .. }
                                    | Region::Empty
                                    | Region::Goto { .. } => true,
                                    Region::Seq(v) => v.iter().all(simple_completion),
                                    Region::If { then_r, else_r, .. } => {
                                        simple_completion(then_r)
                                            && simple_completion(else_r)
                                    }
                                    _ => false,
                                }
                            }
                            // CONTINUATION COHERENCE: the chain copy's
                            // own walk must end where the bypassing arm
                            // path jumps (its continuation walk starts at
                            // the bypass target). When they diverge (huc
                            // getInputStream0: bypass Goto{117} but the
                            // parked 109-chain continues into the auth
                            // retry loop territory), splicing the copy
                            // into the arm flips conv's goto_is_last for
                            // the arm's internal gotos (a nested elided
                            // Goto{108} materialized as Continue) and
                            // prune_unreachable then ate the tail copy
                            // (serverAuthentication.addToCache lost).
                            let coherent = {
                                fn chain_cont(r: &Region) -> Option<usize> {
                                    match r {
                                        Region::Goto { target } => Some(*target),
                                        Region::Seq(v) => v.last().and_then(chain_cont),
                                        _ => None,
                                    }
                                }
                                fn bypass_targets(r: &Region, out: &mut Vec<usize>) {
                                    match r {
                                        Region::Goto { target } => out.push(*target),
                                        Region::Seq(v) => {
                                            if let Some(l) = v.last() { bypass_targets(l, out); }
                                        }
                                        Region::If { then_r, else_r, .. } => {
                                            bypass_targets(then_r, out);
                                            bypass_targets(else_r, out);
                                        }
                                        Region::Try { body, catches, .. } => {
                                            bypass_targets(body, out);
                                            for (_, _, h) in catches { bypass_targets(h, out); }
                                        }
                                        _ => {}
                                    }
                                }
                                let mut bts = Vec::new();
                                bypass_targets(&arm, &mut bts);
                                // A copy ending in a Goto to somewhere
                                // OTHER than the bypass target re-routes
                                // the path away from the arm's real
                                // continuation (huc). A copy with NO
                                // trailing Goto (it ends inside a
                                // terminator or a full tail walk past
                                // the target — JarFile's chain flows
                                // through b11 into the close/return
                                // epilogue) preserves it.
                                match chain_cont(&taken_r) {
                                    Some(c) => bts.iter().all(|t| *t == c),
                                    None => true,
                                }
                            };
                            if matches!(taken_r, Region::Empty)
                                || !simple_completion(&taken_r)
                                || !coherent
                            {
                                // Full state rollback: the exploratory walk
                                // mutates Structurer state beyond `claimed`
                                // (copied_tails feeds conversion's
                                // reaches_copy_tail elision; the group/loop/
                                // switch stacks feed scope decisions) — huc
                                // getInputStream0 lost addToCache with only
                                // claimed+tails restored.
                                self.copied_tails = saved_tails;
                                *claimed = saved_claims;
                                *self.structuring_groups.borrow_mut() = saved_groups;
                                self.loops_stack = saved_loops;
                                self.switch_depth = saved_switch_depth;
                                self.case_arm_ctx = saved_case_ctx;
                                self.walk_depth = saved_walk_depth;
                                arm
                            } else {
                                claimed.extend(scratch.iter().copied());
                                Region::Seq(vec![arm, taken_r])
                            }
                        }
                    } else if universe.contains(&fall)
                        && !bstop.contains(&fall)
                        && !claimed.contains(&fall)
                        && !(self.is_handler(fall) && active.is_empty())
                    {
                        let branch_universe = self.owner_scope(fall, universe);
                        let mut sub = self.sub_scope(fall, &branch_universe, &bstop, claimed);
                        self.restrict_handler_branch(&mut sub, entry);
                        if std::env::var("JCDC_DBG_IF").is_ok() {
                            eprintln!("IF cur={} else walk fall={} sub={:?}", cur, fall, sub);
                        }
                        self.walk(fall, &sub, &bstop, active, claimed, false)
                    } else if self.is_terminator_block(fall)
                        && !stop.contains(&fall)
                        && !self.terminator_writes_final(fall)
                    {
                        Region::CopyStmts { block: fall }
                    } else if claimed.contains(&fall) {
                        if !stop.contains(&fall)
                            && !bstop.contains(&fall)
                            && !self.loops_stack.contains(&fall)
                            && !self.terminator_writes_final(fall)
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
                    } else if self.is_terminator_block(fall)
                        && !stop.contains(&fall)
                        && !self.terminator_writes_final(fall)
                    {
                        Region::CopyStmts { block: fall }
                    } else if stop.contains(&fall) && !self.is_terminator_block(fall) {
                        // Jump to an enclosing loop's exit (or other
                        // barrier): keep it as a Goto so conversion
                        // resolves it to `break` — unless the exit chains
                        // into an already-claimed terminator (see the
                        // taken side; jdk26 DecimalFormat guarded case).
                        if !self.loops_stack.contains(&fall)
                            && self.stop_chain_to_claimed_terminator(fall, claimed)
                        {
                            let mut cstop = bstop.clone();
                            cstop.remove(&fall);
                            match self.copy_walk(fall, &cstop, active, cur) {
                                Some(r) => r,
                                None => Region::Goto { target: fall },
                            }
                        } else {
                            Region::Goto { target: fall }
                        }
                    } else if self.is_terminator_block(fall)
                        && stop.contains(&fall)
                        && self.is_terminator_block(taken)
                        && stop.contains(&taken)
                    {
                        // Dual-terminator stop exits: see the taken side
                        // (jdk11 ObjectInputStream.readSerialData).
                        self.dual_terminator_branch(fall, active)
                    } else if !stop.contains(&fall)
                        && !claimed.contains(&fall)
                        && self.cfg.exc_edges.iter().any(|e| e.from == fall)
                    {
                        // Protected branch target outside the scope — see
                        // the taken side (getOutputStream p==null arm).
                        let branch_universe = self.owner_scope(fall, universe);
                        let mut sub = self.sub_scope(fall, &branch_universe, &bstop, claimed);
                        self.restrict_handler_branch(&mut sub, entry);
                        self.walk(fall, &sub, &bstop, active, claimed, false)
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
                            //
                            // UNLESS the follow is a loop BACKEDGE STUB
                            // (`reset(); goto head`): the fresh walk would
                            // re-walk the ENTIRE loop from the header
                            // (fresh claimed knows nothing) and paste the
                            // loop body into this branch (jdk11 KeyStore
                            // .getInstance(File)'s IOException catch
                            // swallowed the provider loop with an
                            // unprotected Security.getImpl — 未报告的异常
                            // 错误NoSuchProviderException). Copy the stub's
                            // own statements and attach an explicit Goto
                            // to the header — conversion resolves it to
                            // `continue`; a fall-through must NOT reach
                            // the head (it would re-run the loop test).
                            let stub_header =
                                if matches!(self.results[f].term, Term::Goto)
                                    && self.cfg.blocks[f].succ.len() == 1
                                {
                                    let t = self.cfg.blocks[f].succ[0];
                                    self.loops_stack
                                        .iter()
                                        .chain(self.sese_loop_headers.iter())
                                        .find(|&&h| {
                                            h == t || self.is_stmt_free_chain_to_block(t, h)
                                        })
                                        .copied()
                                } else {
                                    None
                                };
                            if let Some(h) = stub_header {
                                parts.push(Region::Seq(vec![
                                    Region::CopyStmts { block: f },
                                    Region::Goto { target: h },
                                ]));
                                break;
                            }
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
                        .or_else(|| self.switch_follow(cur, universe))
                        // Inside a copied/shared-tail region the confluence
                        // sits in `stop` (the enclosing flow owns it), so
                        // the universe-bound searches miss it and every
                        // case's terminal goto degrades to fall-through
                        // (jdk11 Calendar.createCalendar catch-copy switch
                        // lost its breaks). A stop block that ALL live
                        // cases escape to is still the logical follow for
                        // break resolution.
                        .or_else(|| self.switch_stop_confluence(cur, universe, stop));
                    // CROSSING follow: a stop-confluence of a NESTED
                    // switch belongs to an enclosing construct (jdk26 xml
                    // impl.Parser.bappend: the inner switch(ch)'s cases
                    // break to the OUTER switch(mode)'s follow — passing
                    // it as the inner follow resolved the default's goto
                    // to a bare `break` binding the inner switch, case
                    // 105 fell through into case 99 and the outer tail
                    // went unreachable). With follow=None the conversion's
                    // labeled-break logic binds it to the outer switch
                    // (`break L1`); the confluence still bounds the case
                    // walks via `stop`. Calendar (depth 0) keeps Some(f).
                    // EXCEPTION — when every route past the built switch
                    // lands on the confluence anyway (the switch is the
                    // last construct of an abruptly-completing outer case
                    // arm), the plain inner-break binding is equivalent
                    // AND renderable: the labeled one makes the inner
                    // switch non-completing and the outer case's appended
                    // `break;` unreachable (ClassPrinterImpl.toYaml/toXml
                    // 无法访问的语句 x2 trees). Rebuild with the follow.
                    let crossing = match follow {
                        Some(f) if stop.contains(&f) && self.switch_depth > 0 => Some(f),
                        _ => None,
                    };
                    let region_follow = match crossing {
                        Some(_) => None,
                        None => follow,
                    };
                    self.switch_depth += 1;
                    let claimed_save = claimed.clone();
                    let mut sw = self.structure_switch(cur, selector.clone(), &targets, universe, stop, region_follow, active, claimed);
                    if let Some(f) = crossing {
                        // What this scope does RIGHT AFTER the switch must
                        // already land on `f`: either the scope's earlier
                        // parts complete abruptly (nothing can fall through
                        // the switch), or the walk's own next-step rule
                        // continues exactly at `f` (an in-universe follow).
                        // Anything else means the bare-break binding drops
                        // flow into the enclosing continuation, re-running
                        // code the bytecode skipped (bappend's outer tail,
                        // bkeyword's case fall-through losing `return '?'`).
                        let cont_dead = parts
                            .last()
                            .map(|p| region_terminates(p, self.results))
                            .unwrap_or(false);
                        let cont_is_f = universe.contains(&f)
                            && !stop.contains(&f)
                            && !claimed_save.contains(&f);
                        // This walk IS a pattern-switch case arm and the
                        // confluence is that switch's follow: the arm
                        // renderer appends the case's terminal `break;`
                        // (restore_one_switch), landing on the outer
                        // follow == f — the plain-break binding is
                        // equivalent and keeps the appended break
                        // reachable (ClassPrinterImpl.toYaml/toXml).
                        let cont_via_case_break = self
                            .case_arm_ctx
                            .last()
                            .map(|&(head, ef, pat)| head == entry && pat && ef == Some(f))
                            .unwrap_or(false);
                        let bindable = (cont_dead || cont_is_f || cont_via_case_break)
                            && self.switch_follow_bindable(&sw, cur, &targets, f);
                        if std::env::var("JCDC_DBG_SWF").is_ok() {
                            eprintln!("SWBIND cur={} f={} cont_dead={} cont_is_f={} cont_case={} bindable={}",
                                cur, f, cont_dead, cont_is_f, cont_via_case_break, bindable);
                        }
                        if bindable {
                            *claimed = claimed_save;
                            sw = self.structure_switch(cur, selector, &targets, universe, stop, Some(f), active, claimed);
                        }
                    }
                    self.switch_depth -= 1;
                    // A follow already CLAIMED by a sibling arm (a shared
                    // terminator tail copied there first) still binds this
                    // switch's `break`s — but nothing after the switch
                    // renders the tail, so a normally-completing switch
                    // fell off the enclosing arm (jdk11 MethodTypeForm
                    // .canonicalize: the Void.TYPE lookupswitch's default
                    // `goto return-null` became `break` with the tail
                    // claimed by the tableswitch arm — 缺少返回语句). Copy
                    // the terminator at the confluence, mirroring the
                    // GOTO-CLAIMED shared-tail rule. Only when the switch
                    // can complete normally (JLS 14.11: an open default
                    // route, a non-terminating default, or any
                    // non-terminating case) — else the copy is unreachable
                    // (无法访问的语句).
                    if let Some(f) = follow {
                        if std::env::var("JCDC_DBG_SWF").is_ok() {
                            eprintln!("SWTAIL cur={} f={} claimed={} stop={} loops={} term={} loophdr={} finw={} completes={}",
                                cur, f, claimed.contains(&f), stop.contains(&f),
                                self.loops_stack.contains(&f), self.is_terminator_block(f),
                                Self::ctx_is_loop_header(self, f), self.terminator_writes_final(f),
                                switch_completes_normally(&sw, f, self.results));
                        }
                        if claimed.contains(&f)
                            && !stop.contains(&f)
                            && !self.loops_stack.contains(&f)
                            && self.is_terminator_block(f)
                            && !Self::ctx_is_loop_header(self, f)
                            && !self.terminator_writes_final(f)
                            && switch_completes_normally(&sw, f, self.results)
                        {
                            parts.push(sw);
                            parts.push(Region::CopyStmts { block: f });
                            break;
                        }
                    }
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
                            if self.is_terminator_block(t)
                                && !stop.contains(&t)
                                && !self.loops_stack.contains(&t)
                                && !Self::ctx_is_loop_header(self, t)
                            {
                                // A shared TERMINATOR tail (return/throw) is
                                // copied at each arrival — but NOT when the
                                // target is a LOOP HEADER: the back edge is
                                // a `continue`, and copying a header whose
                                // body ends in a throw inlines the body into
                                // the handler unprotected (jdk26 Future
                                // .exceptionNow: the InterruptedException
                                // retry `goto 40` copied `get(); throw ISE`
                                // into the catch — 未报告的异常错误
                                // InterruptedException).
                                parts.push(Region::CopyStmts { block: t });
                            } else if !stop.contains(&t) && !self.loops_stack.contains(&t) && !Self::ctx_is_loop_header(self, t) {
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
                            if std::env::var("JCDC_DBG_GOTO").is_ok() {
                                eprintln!("GFALL-ARM cur={} t={} term={} stop={} loophdr={}",
                                    cur, t, self.is_terminator_block(t), stop.contains(&t),
                                    Self::ctx_is_loop_header(self, t));
                            }
                            if self.is_terminator_block(t)
                                && !stop.contains(&t)
                                && !Self::ctx_is_loop_header(self, t)
                                && !self.terminator_writes_final(t)
                            {
                                // Shared terminator tail — but NOT a retry
                                // loop header (a handler-entry `goto head`
                                // re-executes the protected body; copying a
                                // throw-terminated header inlines it
                                // unprotected: jdk26 Future.exceptionNow
                                // catch(IE) got `get(); throw ISE` —
                                // 未报告的异常错误 InterruptedException).
                                parts.push(Region::CopyStmts { block: t });
                            } else if !stop.contains(&t)
                                && !self.loops_stack.contains(&t)
                                && !Self::ctx_is_loop_header(self, t)
                                && !self.is_active_group_continuation(
                                    t,
                                    &active_filtered(active, &structured_here),
                                )
                            {
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
                            // Shared-tail arrival: `n` is CLAIMED (hence
                            // out of this walk's universe — sub_scope
                            // retains unclaimed blocks only). A bare Goto
                            // here is elided at conversion as the walk's
                            // last part (goto_is_last), silently severing
                            // this path's flow into the shared tail (jdk26
                            // DatagramChannelImpl.innerJoin's IPv4 arm:
                            // `key = new Type4(..)` fell off the method
                            // without the `registry.add(key); return key;`
                            // copy — 缺少返回语句 x3 trees). Per-arrival
                            // copies are exactly the bytecode semantics.
                            // Shared-tail arrival: `n` is CLAIMED, so no
                            // walk here will ever emit it again. A bare
                            // Goto is elided at conversion as the walk's
                            // last part (goto_is_last), silently severing
                            // this path's flow into the tail (jdk26
                            // DatagramChannelImpl.innerJoin's IPv4 arm:
                            // `key = new Type4(..)` fell off the method
                            // without the `registry.add(key); return key;`
                            // copy — 缺少返回语句 x3 trees) — UNLESS `n`
                            // is an ACTIVE group's post-try continuation:
                            // the owner walk emits it at the right level
                            // after the Try region (jdk11 Module
                            // .loadModuleInfoClass's in.close() block is
                            // gi=1's cont — copying it here duplicated the
                            // close+return chain into the body, defeated
                            // twr_j11's try-with-resources fold, and the
                            // pending-rethrow scaffolding leaked —
                            // 未报告的异常错误Throwable x2 trees). The
                            // conversion's strip_trailing_goto(try_follow)
                            // renders the Goto as the natural fallthrough.
                            let owned_cont = self.is_cont_of_active_group(
                                n,
                                stop,
                                claimed,
                                &active_filtered(active, &structured_here),
                            );
                            if claimed.contains(&n)
                                && !owned_cont
                                && !stop.contains(&n)
                                && !self.loops_stack.contains(&n)
                                && !self.is_handler(n)
                                && !self.terminator_writes_final(n)
                            {
                                if self.is_terminator_block(n) {
                                    parts.push(Region::CopyStmts { block: n });
                                    break;
                                }
                                if let Some(r) = self.copy_walk(n, stop, active, cur) {
                                    parts.push(r);
                                    break;
                                }
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
                                // Blocks owned by a group ENCLOSING `gi`
                                // are the arm's post-try continuation, not
                                // a sibling's territory: a nested try whose
                                // protected span ends before the enclosing
                                // monitor/group span leaves its monitorexit
                                // + return tail owned by the outer group,
                                // and filtering it stranded the tail in no
                                // region (jdk26 ZipFile.getComment: the
                                // `return zipCoder.toString(comment)` value
                                // block walked alone, its Goto into the
                                // tail elided at conversion — empty try
                                // body AND a missing return).
                                || (self.groups[*og].start <= g.start
                                    && self.groups[*og].end >= g.end)
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
    /// The single stop/out-of-universe block that every live (non
    /// return/throw) case target escapes to. Used as a switch follow for
    /// break resolution when the real confluence lies beyond the current
    /// region's universe.
    pub(crate) fn switch_stop_confluence(
        &self,
        cur: usize,
        universe: &HashSet<usize>,
        stop: &HashSet<usize>,
    ) -> Option<usize> {
        let mut common: Option<usize> = None;
        let mut saw_live = false;
        for &t in &self.cfg.blocks[cur].succ {
            if self.is_terminator_block(t) {
                continue;
            }
            saw_live = true;
            // Forward BFS within the universe; collect the first blocks
            // that leave it (stop members or out-of-universe succs).
            let mut escapes: HashSet<usize> = HashSet::new();
            let mut seen: HashSet<usize> = HashSet::new();
            let mut q: Vec<usize> = vec![t];
            seen.insert(t);
            while let Some(b) = q.pop() {
                for &s2 in &self.cfg.blocks[b].succ {
                    if !universe.contains(&s2) || stop.contains(&s2) {
                        escapes.insert(s2);
                    } else if seen.insert(s2) {
                        q.push(s2);
                    }
                }
            }
            // A live target that IS itself a stop/out-of-universe block
            // (the default jumping straight to the confluence) escapes to
            // itself.
            if !universe.contains(&t) || stop.contains(&t) {
                escapes.clear();
                escapes.insert(t);
            }
            if escapes.is_empty() {
                // The case flow terminates ENTIRELY inside the universe
                // (every exit is a return/throw leaf — no edge leaves it):
                // an always-terminating case contributes no escape and
                // must not veto the confluence of the others (jdk26 xml
                // impl.Parser.bappend: the whitespace case's
                // if/else-if/else chain all-returns zeroed the escape set
                // and the whole-switch None made the inner switch's
                // `break`-to-outer-follow default unresolvable — the case
                // fell through into `case 99`, corrupting the outer
                // switch's completion and stranding its follow —
                // 无法访问的语句).
                continue;
            }
            if escapes.len() != 1 {
                return None;
            }
            let e = *escapes.iter().next().unwrap();
            match common {
                None => common = Some(e),
                Some(c) if c == e => {}
                Some(_) => return None,
            }
        }
        if saw_live { common } else { None }
    }

    /// For a NESTED switch whose confluence `f` is a stop block owned by
    /// an enclosing construct (the CROSSING shape), decide whether `f` may
    /// still be passed as the switch's OWN follow (case arms then resolve
    /// to plain `break`s) or must be nulled (labeled breaks bind the
    /// enclosing switch). The plain-break binding is safe ONLY when every
    /// way flow could naturally continue past this switch inside the
    /// enclosing region lands on `f` anyway: otherwise a case the bytecode
    /// sends straight to `f` would fall out of the switch into that
    /// continuation and re-execute code the bytecode skipped (jdk26 xml
    /// impl.Parser.bappend: the inner switch(ch)'s cases break to the
    /// OUTER switch(mode)'s follow, jumping over the outer case's tail —
    /// nulling keeps `break L1`). When the switch is the LAST construct of
    /// an abruptly-completing case arm both bindings land at `f` and the
    /// plain inner break is the renderable one — binding the outer label
    /// makes the inner switch unable to complete normally and the
    /// pattern-switch restoration's appended outer-case `break;` becomes
    /// unreachable (jdk26 ClassPrinterImpl.toYaml/toXml: the MapNode/List
    /// inner ordinal switches have NO default stub — every arm `goto`s the
    /// shared return directly — so the inner switch rendered `default:
    /// break L1` + outer case `break;` — 无法访问的语句 x2 trees).
    pub(crate) fn switch_follow_bindable(
        &self,
        sw: &Region,
        block: usize,
        targets: &SwitchTargets,
        f: usize,
    ) -> bool {
        let (cases, default) = match sw {
            Region::Switch { cases, default, .. } => (cases, default.as_deref()),
            _ => return false,
        };
        let last = self.cfg.blocks[block].ins.last();
        let default_pc = match (targets, last.and_then(|i| i.switch_data.as_deref())) {
            (SwitchTargets::Table { .. }, Some(jcdc_classfile::SwitchData::Table { default, .. })) => *default,
            (SwitchTargets::Lookup { .. }, Some(jcdc_classfile::SwitchData::Lookup { default, .. })) => *default,
            _ => return false,
        };
        // The default route: the rendered default region must itself bind
        // to `f`. `default_pc == f` is NOT automatically bindable: with
        // the follow passed, structure_switch filters the default region
        // away and unmatched-selector flow falls out of the switch into
        // the ENCLOSING continuation (bkeyword's outer case then fell
        // through into the next case, dropping the shared `return '?'`).
        let default_ok = match default {
            Some(d) => self.arm_binds_to(d, f),
            None => false,
        };
        // Case arms in emission order. An Empty group is a fallthrough
        // label: its route is the NEXT group's (checked in its own
        // iteration), or the default's when it is the last group.
        let n = cases.len();
        let cases_ok = cases.iter().enumerate().all(|(i, (_, r))| {
            if matches!(r, Region::Empty) {
                return i + 1 < n || default_ok;
            }
            let ok = self.arm_binds_to(r, f);
            if std::env::var("JCDC_DBG_SWF").is_ok() {
                eprintln!("SWBIND-CASE i={} block={} f={} ok={} region={:?}", i,
                    region_head_block(r), f, ok, region_shape(r));
            }
            ok
        });
        if std::env::var("JCDC_DBG_SWF").is_ok() {
            eprintln!("SWBIND-DEF block={} default_pc={} f={} default_ok={} cases_ok={}",
                block, default_pc, f, default_ok, cases_ok);
        }
        default_ok && cases_ok
    }

    /// Every completion path of this arm region lands on `f`: a trailing
    /// goto to it, a block whose terminal edge is that goto, an if whose
    /// both branches bind, a loop whose every exit IS `f`, or a nested
    /// switch that is itself bindable.
    fn arm_binds_to(&self, r: &Region, f: usize) -> bool {
        match r {
            Region::Basic { .. } => true,
            Region::Goto { target } => *target == f,
            Region::Empty => false,
            Region::Seq(v) => v
                .last()
                .map(|x| self.arm_binds_to(x, f))
                .unwrap_or(false),
            Region::If { then_r, else_r, .. } => {
                self.arm_binds_to(then_r, f) && self.arm_binds_to(else_r, f)
            }
            // The loop arm binds when ALL its exits are `f`: loop
            // completion falls out of the switch (follow == `f`) and any
            // in-body break targets an exit == `f` (ClassPrinterImpl's
            // BLOCK-case iterator loop exits straight to the shared
            // return — no default stub).
            Region::Loop { exits, .. } => !exits.is_empty() && exits.iter().all(|&e| e == f),
            Region::Switch { block, .. } => {
                if let Term::Switch { targets, .. } = &self.results[*block].term {
                    self.switch_follow_bindable(r, *block, targets, f)
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    /// True when `cur` flows through single-successor blocks to an
    /// already-claimed terminator: the chain is safe to copy inline because
    /// its endpoint was structured elsewhere (the restart-loop switch: the
    /// guard-pass body flows ONLY to the shared areturn every case region
    /// absorbed) and the copy is this path's sole continuation. Normal loop
    /// exits chain to UNCLAIMED continuations (the post-loop follow) and
    /// must stay jumps — inlining those rewrites breaks into returns and
    /// degrades while-cond loops (jdk26 ThreadPoolExecutor regression).
    /// True when a loop-exit target heads real CONTENT: a statement or a
    /// branch cascade, not a statement-free stub chain into a barrier
    /// (loop header / another exit / out of scope). Breaking to a stub
    /// exit loses nothing (Pattern.clazz's switch-case goto stubs must
    /// stay bare breaks). Breaking to a content exit drops its whole
    /// flow: jdk17 AQS.cleanQueue's `q.status < 0` arm breaks to the
    /// CAS-unlink cascade (casTail/casPrev/casNext/signalNext flowing to
    /// the outer restart stub) and the bare break silently deleted the
    /// phase (semantic, compile-clean).
    pub(crate) fn exit_has_content(&self, e: usize, stop: &HashSet<usize>) -> bool {
        let mut b = e;
        for _ in 0..16 {
            if !self.results[b].stmts.is_empty() {
                return true;
            }
            match &self.results[b].term {
                Term::Cond { .. } | Term::Switch { .. } => return true,
                Term::Return(_) | Term::Throw(_) => return false,
                Term::Fallthrough | Term::Goto
                    if self.cfg.blocks[b].succ.len() == 1 =>
                {
                    let n = self.cfg.blocks[b].succ[0];
                    if n == e || stop.contains(&n) || self.loops_stack.contains(&n) {
                        return false;
                    }
                    b = n;
                }
                _ => return false,
            }
        }
        false
    }

    fn stop_chain_to_claimed_terminator(&self, cur: usize, claimed: &HashSet<usize>) -> bool {
        let mut x = cur;
        for _ in 0..8 {
            if matches!(self.results[x].term, Term::Return(_) | Term::Throw(_)) {
                // The restart-loop guarded case is a chain of EMPTY jump
                // stubs into an absorbed terminator — breaking would land
                // where nothing remains. A STATEMENT-BEARING claimed
                // terminator is the post-loop continuation tail (a shared
                // clinit tail claimed early by the first arrival): the
                // enclosing walk structures it after the loop and the
                // barrier Goto must stay a `break`. Copying the tail into
                // the exit test put the blank-final assignments INSIDE the
                // for-each loop (javac: 可能在 loop 中分配了变量 x18,
                // SecurityProviderConstants) and duplicated them into the
                // catch.
                return claimed.contains(&x) && self.results[x].stmts.is_empty();
            }
            if !matches!(self.results[x].term, Term::Fallthrough | Term::Goto) {
                return false;
            }
            // An UNCLAIMED statement-bearing link means the chain is real
            // post-loop code, not absorbed scaffolding (see above).
            if !self.results[x].stmts.is_empty() && !claimed.contains(&x) {
                return false;
            }
            let succs = &self.cfg.blocks[x].succ;
            if succs.len() != 1 {
                return false;
            }
            let n = succs[0];
            if n == x || self.loops_stack.contains(&n) {
                return false;
            }
            x = n;
        }
        false
    }

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
            // Multi-pred blocks INSIDE a nested switch's span are that
            // switch's own merge, not this switch's follow (jdk26 xml
            // impl.Parser.dtdsub: switch(ch)'s case '!' flow merges the
            // nested switch(bkeyword) at the shared `st = 1; goto head`
            // stub — taking it as the follow put `st = 1` after the inner
            // switch in case '<' and left the arm without its continue,
            // falling through into case '%' — unreachable code past the
            // all-continue arms plus a corrupted state machine, 无法访问
            // 的语句 x5 methods x3 trees). A nested-switch merge is
            // claimed by that switch's own follow resolution.
            let in_nested_switch = |c: usize, d: &HashMap<usize, u32>| -> bool {
                let preds = &self.cfg.blocks[c].pred;
                if preds.len() < 2 {
                    return false;
                }
                self.cfg.blocks.iter().any(|b| {
                    if b.id == cur
                        || !matches!(self.results[b.id].term, Term::Switch { .. })
                        || !d.contains_key(&b.id)
                    {
                        return false;
                    }
                    preds.iter().all(|&p| {
                        b.succ.iter().any(|&t| {
                            let mut seen: HashSet<usize> = HashSet::new();
                            let mut q: VecDeque<usize> = VecDeque::new();
                            q.push_back(t);
                            while let Some(x) = q.pop_front() {
                                if x == p {
                                    return true;
                                }
                                if !seen.insert(x) || !d.contains_key(&x) {
                                    continue;
                                }
                                for &sx in &self.cfg.blocks[x].succ {
                                    q.push_back(sx);
                                }
                            }
                            false
                        })
                    })
                })
            };
            // A RETURN/THROW merge whose preds all live inside this one
            // flow is the case's private terminator confluence, not the
            // switch's follow (jdk26 xml impl.Parser.bappend: the
            // whitespace case's if-chain arms all converge on the shared
            // `return` leaf; electing it follow made the switch "complete"
            // into a bogus `return;` and the case group fall through into
            // `case 99` — 无法访问的语句 on the outer tail). A shared
            // return that IS the lexical follow keeps preds from the
            // sibling (terminator-excluded) case flows and stays elected.
            // A candidate whose every flow-internal pred is a VALUE-STACK
            // diamond arm (statement-free, one stack value out, single
            // successor) is a folded-ternary merge INSIDE the case body,
            // not the switch follow (jdk26 xml impl.Parser.xml: case
            // 0xFEFF's `ch = val < 0 ? 0xFFFF : val` and `st = ch != '<'
            // ? -1 : 1` diamonds — electing the first merge split the
            // case body in half, the front fell through into `default`
            // and the back half went unreachable after the all-continue
            // switch — 无法访问的语句 x2 trees). In the single-flow
            // branch every other case terminates, so the true follow is
            // the flow's own exit; an interior diamond merge never is.
            let diamond_merge = |c: usize, d: &HashMap<usize, u32>| -> bool {
                let internal: Vec<usize> = self.cfg.blocks[c]
                    .pred
                    .iter()
                    .copied()
                    .filter(|p| d.contains_key(p))
                    .collect();
                !internal.is_empty()
                    && internal.iter().all(|&p| {
                        self.results[p].stmts.is_empty()
                            && self.results[p].out_stack.len() == 1
                            && self.cfg.blocks[p].succ.len() == 1
                    })
            };
            let private_terminator_merge = |c: usize, d: &HashMap<usize, u32>| -> bool {
                if !matches!(self.results[c].term, Term::Return(_) | Term::Throw(_)) {
                    return false;
                }
                if !self.cfg.blocks[c]
                    .pred
                    .iter()
                    .all(|p| d.contains_key(p) || *p == cur)
                {
                    return false;
                }
                // A SINGLE case target whose flow ends at this return IS
                // the lexical switch tail (`switch (x) { default: g(); }
                // return v;` — the default completes the switch into the
                // return): keep it as the follow. With two or more live
                // targets the return is one case's private confluence
                // (bappend's whitespace if-chain), not the follow.
                self.cfg.blocks[cur].succ.len() > 1
            };
            let mut best: Option<usize> = None;
            for &cand in d.keys() {
                if self.cfg.blocks[cand].pred.len() >= 2
                    && !in_nested_switch(cand, d)
                    && !diamond_merge(cand, d)
                    && !private_terminator_merge(cand, d)
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
    pub(crate) fn copy_walk(
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
        #[allow(unused_mut)]
        let mut tu = tu;
        COPY_DEPTH.with(|c| c.set(c.get() + 1));
        let mut fresh: HashSet<usize> = HashSet::new();
        // Try groups that START (and whose handler heads live) inside the
        // copied universe must fire inside the copy: SESE passes only the
        // top-level groups, so a copied loop-top try head re-walked from a
        // catch back-edge lost its try wrapper and emitted bare statements
        // (jdk11 ObjectStreamClass.getInheritableMethod: the retry
        // getDeclaredMethod call landed in the catch WITHOUT its
        // try/catch — "unreported exception NoSuchMethodException").
        // For walk callers `active` already covers the scope, so this is
        // a no-op there.
        let mut active2: Vec<usize> = active.to_vec();
        for gi in 0..self.groups.len() {
            if active2.contains(&gi) {
                continue;
            }
            let gs = self.groups[gi].start;
            let start_in = self
                .cfg
                .blocks
                .iter()
                .any(|b| b.start == gs && tu.contains(&b.id));
            if !start_in {
                continue;
            }
            // Pull the handler heads (and their forward flow up to the
            // group's end) into the copy universe: exception edges are
            // not followed by reachable_within, but structure_try needs
            // the handler blocks present to rebuild the catch.
            let heads: Vec<usize> = self
                .handler_group
                .iter()
                .filter(|(_, &g)| g == gi)
                .map(|(&hb, _)| hb)
                .collect();
            for h in heads {
                tu.insert(h);
            }
            active2.push(gi);
        }
        let r = self.walk(t, &tu, stop, &active2, &mut fresh, true);
        COPY_DEPTH.with(|c| c.set(c.get() - 1));
        self.copied_tails.insert(t);
        Some(r)
    }

    /// True when the block ends in a return/throw (a shared terminator that
    /// can be safely duplicated at each arrival site).
    pub(crate) fn is_terminator_block(&self, b: usize) -> bool {
        matches!(
            self.results[b].term,
            Term::Return(_) | Term::Throw(_)
        )
    }

    /// True when the block's statements assign a FINAL field of the
    /// emitting class: copying such a shared terminator at an extra
    /// arrival site duplicates the final's assignment (javac:
    /// 可能在 loop 中分配了变量 / 可能已分配变量 — jdk11
    /// SecurityProviderConstants clinit tail assigned its blank-final
    /// key sizes in the loop-exit copy AND the handler copy). Such
    /// arrivals emit a Goto instead — conversion's term_copy refuses it
    /// for the same final_fields reason and elides to the real tail the
    /// enclosing flow emits next.
    fn terminator_writes_final(&self, b: usize) -> bool {
        !self.final_fields.is_empty()
            && self.results[b].stmts.iter().any(|s| {
                matches!(
                    s,
                    crate::stmt::Stmt::ExprStmt(crate::expr::Expr::Assign { target, .. })
                        if matches!(
                            target.as_ref(),
                            crate::expr::Expr::Field { name, .. }
                                if self.final_fields.contains(name)
                        )
                )
            })
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
        active: &[usize],
    ) -> Option<Region> {
        if !universe.contains(&blk) {
            return None;
        }
        // A block that STARTS a try group visible to this walk must be
        // WALKED, not absorbed: absorption inlines its statements into
        // the branch and silently drops the group's exception protection
        // (jdk17 HttpURLConnection.getOutputStream: the
        // doPrivilegedWithCombiner call absorbed out of its
        // try/catch(PrivilegedActionException) into the `if (p == null)`
        // else arm — 未报告的异常错误PrivilegedActionException).
        let blk_start = self.cfg.blocks[blk].start;
        if self.groups.iter().enumerate().any(|(gi, g)| {
            g.start == blk_start && active.contains(&gi)
        }) {
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
        // The unwalkable successor is an already-CLAIMED block this arm's
        // normal walk would inline-copy (the shared `registry.add(key);
        // return key;` tail): absorbing blk ends the arm AT blk and the
        // path to the tail is silently severed — the enclosing walk
        // breaks at the if with follow=None and the method falls off
        // without a return on this path (jdk26
        // DatagramChannelImpl.innerJoin's IPv4 arm lost the tail after
        // `key = new Type4(..)` — 缺少返回语句 x3 trees). Refuse: the
        // normal walk branch emits Basic{blk} and, arriving at the
        // claimed successor, copies it per arrival — exactly the bytecode
        // semantics. Final-writing successors stay absorbed (copying
        // would double-assign the blank final — the UntrustedCertificates
        // discipline). NOTE: Module.loadModuleInfoClass's TWR fold needs
        // this refusal ABSENT when handler_flow_only carries the
        // ownership check — the working combination is this refusal +
        // the ORIGINAL f4472a5f fixpoint + the sole-entry private-tail
        // cont==hb strip (gate-matrix verified).
        {
            let succ = self.cfg.blocks[blk].succ[0];
            let succ_owned_cont =
                self.is_cont_of_active_group(succ, bstop, claimed, active);
            if claimed.contains(&succ)
                && !succ_owned_cont
                && !bstop.contains(&succ)
                && !self.loops_stack.contains(&succ)
                && !self.terminator_writes_final(succ)
            {
                if dbg_absorb {
                    eprintln!(
                        "absorb REJECT blk={} succ={} claimed inline-copy tail",
                        blk, succ
                    );
                }
                return None;
            }
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
        // Pre-stub-filter candidate set: the shared-collector test in
        // stub_chain_claims_continuation checks chain intermediates
        // against it.
        let pre: HashSet<usize> = exits
            .iter()
            .copied()
            .filter(|e| universe.contains(e) && !stop.contains(e))
            .collect();
        exits
            .into_iter()
            .filter(|e| universe.contains(e) && !stop.contains(e))
            // An exit that is a statement-free jump chain back into an
            // ENCLOSING loop is a `continue outer` stub — one of the inner
            // loop's conditional break arms, already resolved to a break
            // inside the body. Walking it as the straight-line continuation
            // re-emits the jump unconditionally after the inner loop
            // (jdk11 FutureTask.removeWaiter: the pred.thread/CAS-fail
            // `continue retry` stubs became an unconditional `continue`
            // after the inner while, the outer while(true) never completed
            // and the tail `return` went unreachable — 无法访问的语句 x3
            // trees). Real fall-out exits (post-loop code) are kept.
            .filter(|e| {
                !self.loops_stack.iter().any(|&h| {
                    h != *e
                        && self.is_stmt_free_chain_to_block(*e, h)
                        && !self.stub_chain_claims_continuation(*e, h, &pre)
                })
            })
            .min_by_key(|e| self.cfg.blocks[*e].start)
    }

    /// True when `from` reaches `to` through statement-free
    /// Fallthrough/Goto blocks (walk-side twin of the strip helper).
    pub(crate) fn is_stmt_free_chain_to_block(&self, from: usize, to: usize) -> bool {
        let mut x = from;
        let mut seen: HashSet<usize> = HashSet::new();
        for _ in 0..8 {
            if x == to {
                return true;
            }
            if !seen.insert(x) {
                return false;
            }
            if !self.results[x].stmts.is_empty() {
                return false;
            }
            if !matches!(self.results[x].term, Term::Fallthrough | Term::Goto) {
                return false;
            }
            let succs = self.cfg.blocks[x].succ.clone();
            if succs.len() != 1 {
                return false;
            }
            x = succs[0];
        }
        false
    }

    /// True when `from`'s statement-free jump chain into loop header `to`
    /// passes through a block that is ITSELF a continuation candidate for
    /// the just-structured loop (in-universe, non-stop, non-stub exit with
    /// multiple predecessors — a shared continue-collector). Such a chain
    /// is the loop's real backedge merge, not a disposable conditional
    /// break arm: filtering it lets a lower-priority candidate (a bare
    /// `return` escape) become the continuation and the loop body loses
    /// its trailing re-iteration (jdk17 AQS.cleanQueue: the traversal
    /// loop's exits are the return block and the `goto 171` stub; block
    /// 171 (`goto 0`) has 10 preds and is a candidate — dropping the stub
    /// picked the return, the outer for(;;) body lost its `continue`, and
    /// the do-while rotation relocated the CAS tail past the loop with
    /// bare continues — continue 在 loop 外部). Direct-header backedges
    /// (jdk11 FutureTask.removeWaiter's `goto retry` stubs, chain = the
    /// exit block alone) have no intermediate shared block and stay
    /// filtered: walking them re-emitted the conditional retry jump as an
    /// unconditional continue after the inner loop.
    pub(crate) fn stub_chain_claims_continuation(
        &self,
        from: usize,
        to: usize,
        cands: &HashSet<usize>,
    ) -> bool {
        let mut x = from;
        let mut seen: HashSet<usize> = HashSet::new();
        while x != to {
            if !seen.insert(x) {
                return false;
            }
            if x != from
                && cands.contains(&x)
                && self.cfg.blocks[x].pred.len() > 1
            {
                return true;
            }
            if !self.results[x].stmts.is_empty() {
                return false;
            }
            if !matches!(self.results[x].term, Term::Fallthrough | Term::Goto) {
                return false;
            }
            let succs = &self.cfg.blocks[x].succ;
            if succs.len() != 1 {
                return false;
            }
            x = succs[0];
        }
        false
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
                        // A pred OUTSIDE this walk's universe is a dedicated
                        // escape by definition: its flow belongs to the
                        // enclosing scope, so `s` is a shared merge the loop
                        // must not own. Without this, a copy_walk scope
                        // rooted at a branch target (entry 24, single succ =
                        // the loop header) makes the header dominate the
                        // shared tail, and every in-scope pred reaches the
                        // header around it -- the tail was absorbed as a
                        // member, exits emptied, and the post-loop
                        // `append('Z'); return true` landed INSIDE the
                        // while(true) (jdk11/17 DateTimeFormatterBuilder
                        // InstantPrinterParser.format: 缺少返回语句).
                        let mut exit_edge = preds.iter().any(|&p| {
                            p == header
                                || !universe.contains(&p)
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
        let mut body = self.walk(header, &members, &inner_stop, active, claimed, true);
        if std::env::var("JCDC_DBG_LOOP").is_ok() {
            eprintln!("LOOP body region: {:#?}", body);
        }
        // Walk-side twin of the SESE loop-site call: orphaned
        // statement-bearing exits materialized into the breaking arms
        // (jdk26 java.nio.Bits.reserveMemory's phase-1 success path —
        // `tryReserveOrClean` true falls to the interrupted-check +
        // return epilogue (blocks 16-18) which the bare-break rendering
        // dropped entirely: the success path RE-LOOPED, re-reserving
        // memory forever; javac can't see it, the walk path structures
        // this method, so the SESE-only pass never ran).
        if std::env::var("JCDC_NO_MATEXIT").is_err() {
            let natural: HashSet<usize> = self.cfg.blocks[header]
                .succ
                .iter()
                .copied()
                .filter(|x| !members.contains(x) && *x != header)
                .collect();
            let reach_all: HashSet<usize> =
                (0..self.cfg.blocks.len()).collect();
            let lh: HashSet<usize> = HashSet::new();
            self.materialize_content_exits(
                &mut body,
                header,
                &exits,
                &members,
                &natural,
                &members,
                &self.loops_stack.clone(),
                &lh,
                active,
                stop,
                &reach_all,
                claimed,
                false,
            );
        }
        self.loops_stack.pop();
        claimed.extend(members.iter().copied());
        Region::Loop { header, body: Box::new(body), members, exits }
    }

    pub(crate) fn structure_switch(
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
        if std::env::var("JCDC_DBG_GOTO").is_ok() {
            eprintln!("SWITCHENTRY block={} start={} follow={:?} universe={} stop={:?} claimed={:?}",
                block, self.cfg.blocks[block].start, follow, universe.len(), stop, claimed);
        }
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
        // Java 21+ pattern switch: the restoration pass re-appends each
        // labelled case's terminal `break;` — a case arm ending at a
        // nested switch lands on THIS switch's follow (see case_arm_ctx).
        let is_pattern = matches!(&selector, Expr::Invokedynamic { name, args, .. }
            if name == "typeSwitch" && !args.is_empty());
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
            self.case_arm_ctx.push((b, follow, is_pattern));
            let r = self.walk(b, &sub, &cstop, active, claimed, false);
            self.case_arm_ctx.pop();
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
            self.case_arm_ctx.push((d, follow, is_pattern));
            let r = self.walk(d, &sub, &cstop, active, claimed, false);
            self.case_arm_ctx.pop();
            Box::new(strip_fallthrough_goto(r, &head_set))
        });
        Region::Switch { block, selector, cases, default, follow }
    }

    pub(crate) fn structure_try(
        &mut self,
        gi: usize,
        universe: &HashSet<usize>,
        outer_universe: &HashSet<usize>,
        claimed: &mut HashSet<usize>,
        stop: &HashSet<usize>,
    ) -> Region {
        let g = self.groups[gi].clone();
        self.structuring_groups.borrow_mut().push(gi);
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
            // The absorbing tail must belong to THIS group's flow: a
            // loop-exit block parked at exactly g.end (jdk26
            // Future.resultNow's normal-path finally-if at pc 28, the
            // retry loop's break target) has the protected block as its
            // only pred but continues to the post-loop tail — absorbing it
            // hides the exit from the enclosing loop's continuation
            // (exits/natural_follow lose it) and strands `interrupt();
            // return result;` (缺少返回语句). Preds may be body blocks,
            // this group's handler heads, or handler-flow-only blocks
            // (the pending-rethrow copy shapes). Do NOT gate on
            // !stop.contains(cb): a shared return tail that is ALSO an
            // enclosing loop's exit must still absorb when its preds are
            // all group flow — refusing left ReflectionFactory
            // .getReplaceResolveForSerialization's copied inner-try
            // return as a Goto that resolved to `break` (the
            // IllegalAccessException catch lost its throwing call).
            // Future's exit block is ruled out by the pred test alone
            // (its succs continue past the group, so it is not a
            // terminator).
            let hf_own = self.handler_flow_only(gi);
            let pred_in_group_flow = |p: &usize| {
                self.body_group.get(p) == Some(&gi)
                    || self.handler_group.get(p) == Some(&gi)
                    || hf_own.contains(p)
                    || body_universe.contains(p)
            };
            if !body_universe.contains(&cb)
                && self.is_terminator_block(cb)
                && self.results[cb].stmts.is_empty()
                && !self.handler_group.contains_key(&cb)
                && !self.cfg.blocks[cb].pred.is_empty()
                && self.cfg.blocks[cb].pred.iter().all(pred_in_group_flow)
            {
                body_universe.insert(cb);
            }
        }
        // A protected VALUE PUSH whose consumer sits just past the span
        // must stay inside the try: javac excludes the monitorexit+areturn
        // tail from the protected range (jdk26 ZipFile.getComment's
        // `return zipCoder.toString(comment)`), so the body block ends in
        // Fallthrough with the value on the out-stack and the Return that
        // names the call lives outside — converting that split either
        // empties the try (checked catch illegal) or emits the throwing
        // call UNPROTECTED. Absorb the linear statements-free fallthrough
        // chain plus the single Return consumer. The return only runs
        // after the chain completes, so it is exception-equivalent to the
        // protected call; MonitorExit markers ride into the body where
        // reconstruct_synchronized strips them again.
        {
            let entry_blk = self
                .cfg
                .blocks
                .iter()
                .find(|b| b.start == g.start && body_universe.contains(&b.id))
                .map(|b| b.id);
            if let Some(eb) = entry_blk {
                let spans = |gi: usize, og: usize| {
                    self.groups[og].start <= self.groups[gi].start
                        && self.groups[og].end >= self.groups[gi].end
                };
                let ownable = |n: usize| match self.body_group.get(&n) {
                    None => true,
                    Some(&og) => {
                        og == gi
                            || (self.groups[og].start >= self.groups[gi].start
                                && self.groups[og].end <= self.groups[gi].end)
                            || spans(gi, og)
                    }
                };
                if matches!(self.results[eb].term, Term::Fallthrough)
                    && self.results[eb].out_stack.len() == 1
                {
                    let mut x = eb;
                    for _ in 0..4 {
                        let succs = self.cfg.blocks[x].succ.clone();
                        if succs.len() != 1 {
                            break;
                        }
                        let n = succs[0];
                        if body_universe.contains(&n)
                            || self.handler_group.contains_key(&n)
                            || !ownable(n)
                        {
                            break;
                        }
                        let r = &self.results[n];
                        // Monitor markers ride along (they are stripped by
                        // reconstruct_synchronized); any OTHER statement
                        // stops the chain — absorbing real code past the
                        // span would newly protect it (a checked catch
                        // would become illegal).
                        if !r.stmts.is_empty()
                            && !r
                                .stmts
                                .iter()
                                .all(|s| matches!(s, crate::stmt::Stmt::MonitorExit(_) | crate::stmt::Stmt::MonitorEnter(_)))
                        {
                            break;
                        }
                        match &r.term {
                            Term::Fallthrough => {
                                body_universe.insert(n);
                                x = n;
                            }
                            Term::Return(_) => {
                                body_universe.insert(n);
                                break;
                            }
                            _ => break,
                        }
                    }
                }
            }
        }
        let body = match self.cfg.block_at(g.start) {
            Some(entry) if body_universe.contains(&entry) => {
                // A group whose protected span starts AT an enclosing
                // loop's header arrives here with the header already
                // claimed (structure_loop / the SESE loop branch claim it
                // before walking the body, and the group-yield filter
                // deliberately lets the body walk re-find the group at
                // its start). The body walk must then tolerate the
                // claimed entry like structure_loop does — refusing it
                // collapsed the whole protected body into the back-edge
                // Goto and the try emitted as `try { continue; }`
                // (jdk11 HttpURLConnection$ErrorStream.getErrorStream:
                // the `len = is.read(..)` do-while body lost —
                // 在相应的try语句主体中不能抛出异常错误SocketTimeoutException).
                let allow = claimed.contains(&entry);
                let mut r = self.walk(entry, &body_universe, &HashSet::new(), &nested, claimed, allow);
                // Flow leaving the try body to the post-try continuation is
                // natural fallthrough (the outer walk picks it up there).
                let cont = self
                    .continuation_after(g.end, outer_universe, claimed, stop)
                    .filter(|c| {
                        !self.handler_flow_only(gi).contains(c)
                            && !body_universe.contains(c)
                    });
                if std::env::var("JCDC_DBG_IF").is_ok() {
                    eprintln!("try gi={} cont={:?} universe_has_blocks_after_end={} outer_universe={:?} stop={:?}", gi, cont,
                        universe.iter().filter(|b| self.cfg.blocks[**b].start >= g.end).count(),
                        outer_universe, stop);
                }
                if let Some(c) = cont {
                    self.strip_trailing_goto_to(&mut r, c);
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
            if std::env::var("JCDC_DBG_HUNIV").is_ok() {
                eprintln!("HUNIV0 gi={} hb={} hstop={:?} reach={:?}", gi, hb, {
                    let mut v: Vec<usize> = hstop.iter().copied().collect(); v.sort(); v
                }, {
                    let mut v: Vec<usize> = huniverse.iter().copied().collect(); v.sort(); v
                });
            }
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
            // not be absorbed into the handler. `block_at(g.end)` misses the
            // merge when the handler itself sits at the span end (javac
            // excludes the try body's trailing return from the protected
            // range: jdk26 AlgorithmId.getName span (27,62), areturn at 62,
            // handler astore at 63 -> block_at(62) resolves to the areturn,
            // and the `goto merge` tail from 63 drags the WHOLE shared
            // `if (o != null) return o.stdName(); else ...` merge into the
            // catch, leaving every other path without its return --
            // 缺少返回语句). Gate on the merge shape directly: an unclaimed
            // non-group block whose normal preds are already claimed by the
            // surrounding flow is the post-try merge -- the handler reaches
            // it only by jumping out, which strip_handler_exit_goto already
            // renders as the natural fallthrough.
            let hf = self.handler_flow_only(gi);
            // An enclosing loop's BACKEDGE STUB (a Goto block whose
            // single target is/leads to an open loop header — the
            // handler's `dataStream.reset(); goto head` continue tail)
            // is NOT a post-try merge: stripping it from the handler
            // universe leaves the handler's branch arms dangling
            // (Region::Empty) and the flow re-copies the whole loop body
            // into the catch (jdk11 KeyStore.getInstance(File)'s
            // IOException catch swallowed the provider loop with an
            // unprotected Security.getImpl — 未报告的异常错误
            // NoSuchProviderException; regression of the loop-header
            // circulation guard exposing this path).
            let backedge_stub = |b: usize| -> bool {
                if !matches!(self.results[b].term, Term::Goto) {
                    return false;
                }
                let succs = &self.cfg.blocks[b].succ;
                if succs.len() != 1 {
                    return false;
                }
                let t = succs[0];
                self.loops_stack
                    .iter()
                    .chain(self.sese_loop_headers.iter())
                    .any(|&h| h == t || self.is_stmt_free_chain_to_block(t, h))
            };
            let mut shared_merge: Vec<usize> = huniverse
                .iter()
                .copied()
                .filter(|b| {
                    *b != *hb
                        && !hf.contains(b)
                        && !claimed.contains(b)
                        && !backedge_stub(*b)
                        && self.body_group.get(b) != Some(&gi)
                        && self.handler_group.get(b) != Some(&gi)
                        && self.cfg.blocks[*b].pred.iter().any(|p| {
                            claimed.contains(p)
                                && !self.handler_group.contains_key(p)
                                && self.body_group.get(p) != Some(&gi)
                        })
                })
                .collect();
            // Deterministic pick: huniverse is a HashSet whose iteration
            // order varies per process, and shared_merge[0] selects the
            // post-try tail to strip. Without the sort, jdk8
            // JMXConnectorFactory.connect flip-flopped between the
            // correct nested-if shape and a broken else-if chain that
            // trapped the shared getProvider tail inside the IOException
            // catch (losing it on the null-classloader and normal paths).
            // Earliest-pc first: it is the flow confluence, and its
            // reachable tail is the superset covering later candidates.
            shared_merge.sort_by_key(|b| self.cfg.blocks[*b].start);
            if std::env::var("JCDC_DBG_HUNIV").is_ok() {
                eprintln!(
                    "HUNIV1 gi={} hb={} shared_merge={:?} huniverse={:?}",
                    gi, hb, shared_merge,
                    { let mut v: Vec<usize> = huniverse.iter().copied().collect(); v.sort(); v }
                );
            }
            if !shared_merge.is_empty() {
                let tail = reachable_within(self.cfg, shared_merge[0], &HashSet::new());
                huniverse.retain(|b| !tail.contains(b) || *b == *hb || hf.contains(b));
                if std::env::var("JCDC_DBG_HUNIV").is_ok() {
                    eprintln!("HUNIV2 gi={} after-strip={:?}", gi, {
                        let mut v: Vec<usize> = huniverse.iter().copied().collect(); v.sort(); v
                    });
                }
            }
            // The cont-tail exclusion must not fire when the block at the
            // span end IS the handler flow (javac excludes the body's
            // trailing return from the span, so the handler entry sits AT
            // g.end: jdk11 AQS.acquireQueued span (2,57) merged from
            // (2,37)+(38,57), handler at 57). Excluding reachable(handler)
            // there strips the handler's OWN tail (`selfInterrupt();
            // throw t;`) out of its universe -- the catch loses it and the
            // outer continuation emits it as a top-level sibling
            // (未报告的异常错误Throwable).
            if let Some(cont) = self.cfg.block_at(g.end) {
                if cont == *hb {
                    // The handler entry sits AT the span end (merged spans,
                    // javac excluding the body's trailing terminator). Keep
                    // the handler's PRIVATE tail — successors owned by no
                    // group and no other group's handler (AQS.acquireQueued
                    // `if (interrupted) selfInterrupt(); throw t;`) — and
                    // strip the rest: successors OWNED by an enclosing try
                    // are the shared post-try flow / inline finally copies
                    // (feat Exceptions nestedTry: the try body always
                    // throws, so the d/e/g/return chain is structurally
                    // handler-only but semantically the continuation —
                    // swallowing it into the catch snapshotted the return
                    // before the real finally g ran, output lost its g).
                    // Private-tail keep set: successors not owned by
                    // ANOTHER group (nor another group's handler) whose
                    // preds stay within the handler's own flow. Only for
                    // SOLE-ENTRY handlers (the body always completes
                    // abruptly — nestedTry); a multi-entry handler's
                    // reachable set mixes in the genuine shared
                    // continuation and stripping it starves the post-try
                    // walk (jdk Module TWR).

                    // Body-flow reachability per enclosing group: a block
                    // owned by group og that og's own body flow REACHES
                    // (from its span-start block, through blocks it owns,
                    // without stepping on handler heads) will be re-emitted
                    // by og's body walk — stripping it from this handler's
                    // universe is safe (feat Exceptions nestedTry: the
                    // d/e/g continuation chain is gi=0 body flow). A block
                    // merely GEOGRAPHICALLY inside og's span but reachable
                    // only through handler flow is this handler's private
                    // tail — stripping loses it entirely (jdk11
                    // ServerSocketAdaptor.accept: the catch(Exception)'s
                    // assert-throw / `return sc.socket()` tail sits inside
                    // the enclosing sync group's span but its body flow
                    // never reaches it — stripped, the catch fell off the
                    // method end: 缺少返回语句).
                    let mut og_body_reach: HashMap<usize, HashSet<usize>> = HashMap::new();
                    {
                        let mut by_og: HashMap<usize, Vec<usize>> = HashMap::new();
                        for (b, og) in self.body_group.iter() {
                            by_og.entry(*og).or_default().push(*b);
                        }
                        for (og, _) in by_og {
                            // Normal-flow reachability from the group's
                            // body entry, bounded by the group's span and
                            // barred at handler heads: nested groups'
                            // blocks lie on the body flow (the walk
                            // carves them out but continues after), so
                            // the BFS must pass through them.
                            let g = &self.groups[og];
                            let mut reach: HashSet<usize> = HashSet::new();
                            if let Some(entry) = self.cfg.block_at(g.start) {
                                let mut q: VecDeque<usize> = VecDeque::new();
                                q.push_back(entry);
                                reach.insert(entry);
                                // Groups carved out of this span: the
                                // body walk resumes at their post-try
                                // continuation, so the BFS hops the same
                                // way — BUT never onto handler-flow-only
                                // blocks of THIS structure_try's group
                                // (accept's gi=0 body cont would land on
                                // the catch's private assert-throw tail;
                                // the hf_after filter skips it there, and
                                // letting the BFS see it would mark the
                                // tail re-emittable and strip it).
                                let mut conts: HashMap<usize, usize> = HashMap::new();
                                for (j, gj) in self.groups.iter().enumerate() {
                                    if j == og {
                                        continue;
                                    }
                                    if gj.start < g.start || gj.end > g.end.max(g.start + 1) {
                                        continue;
                                    }
                                    // The exclusion set must be the
                                    // CARVED group's own hf (that is what
                                    // the body walk's continuation_after
                                    // filter consults), not this
                                    // structure_try's hf.
                                    let hf_j = self.handler_flow_only(j);
                                    let mut cont: Option<usize> = None;
                                    for nb in self.cfg.blocks.iter() {
                                        if nb.start < gj.end || nb.ins.is_empty() {
                                            continue;
                                        }
                                        if self.handler_group.contains_key(&nb.id) {
                                            continue;
                                        }
                                        if hf_j.contains(&nb.id) {
                                            continue;
                                        }
                                        cont = Some(nb.id);
                                        break;
                                    }
                                    if let Some(c) = cont {
                                        for nb in self.cfg.blocks.iter() {
                                            if !nb.ins.is_empty()
                                                && nb.start >= g.start
                                                && nb.end <= gj.end.max(gj.start + 1)
                                                && !self.handler_group.contains_key(&nb.id)
                                            {
                                                conts.entry(nb.id).or_insert(c);
                                            }
                                        }
                                    }
                                }
                                while let Some(x) = q.pop_front() {
                                    let mut edges: Vec<usize> =
                                        self.cfg.blocks[x].succ.clone();
                                    if let Some(&c) = conts.get(&x) {
                                        edges.push(c);
                                    }
                                    for sx in edges {
                                        let sb = &self.cfg.blocks[sx];
                                        if sb.start >= g.start
                                            && sb.end <= g.end.max(g.start + 1)
                                            && !self.handler_group.contains_key(&sx)
                                            && reach.insert(sx)
                                        {
                                            q.push_back(sx);
                                        }
                                    }
                                }
                            }
                            og_body_reach.insert(og, reach);
                        }
                    }
                    let mut private: HashSet<usize> = HashSet::new();
                    {
                        let mut pq: VecDeque<usize> = VecDeque::new();
                        for &s0 in &self.cfg.blocks[*hb].succ {
                            pq.push_back(s0);
                        }
                        while let Some(x) = pq.pop_front() {
                            if private.contains(&x) || x == *hb {
                                continue;
                            }
                            match self.body_group.get(&x) {
                                Some(og) if *og != gi => {
                                    // Owned by another group: private only
                                    // when that group's body flow cannot
                                    // re-emit it.
                                    if og_body_reach
                                        .get(og)
                                        .map(|r| r.contains(&x))
                                        .unwrap_or(false)
                                    {
                                        continue;
                                    }
                                }
                                _ => {}
                            }
                            if self.handler_group.get(&x).map(|og| *og != gi).unwrap_or(false) {
                                continue;
                            }
                            if self.cfg.blocks[x].pred.iter().all(|p| {
                                *p == *hb
                                    || private.contains(p)
                                    || self.handler_group.get(p) == Some(&gi)
                            }) {
                                private.insert(x);
                                for &s1 in &self.cfg.blocks[x].succ {
                                    pq.push_back(s1);
                                }
                            }
                        }
                    }
                    let sole_entry_hb = self.cfg.blocks[*hb]
                        .pred
                        .iter()
                        .all(|p| self.handler_group.contains_key(p));
                    let tail = reachable_within(self.cfg, cont, &HashSet::new());
                    if sole_entry_hb {
                        huniverse.retain(|b| !tail.contains(b) || private.contains(b));
                    }
                    // Multi-entry cont==hb: no strip (the f4472a5f shape —
                    // the shared_merge machinery and outer walks handle it).
                } else if !self.handler_group.contains_key(&cont) && !hf.contains(&cont) {
                    let tail = reachable_within(self.cfg, cont, &HashSet::new());
                    huniverse.retain(|b| !tail.contains(b) || hf.contains(b));
                }
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
        self.structuring_groups.borrow_mut().retain(|&x| x != gi);
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
