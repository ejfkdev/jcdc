//! Region tree → Stmt tree conversion.
//!
//! Responsibilities:
//! * weave in per-block statements and terminals (return/throw),
//! * resolve `Goto{target}` nodes against the enclosing loop/switch scope
//!   stack into `break` / `continue` / labeled goto,
//! * classify loops into while / do-while / infinite forms,
//! * assemble try/catch with exception parameter variables.

use std::collections::{HashMap, HashSet};

use crate::block::Cfg;
use crate::builder::{BlockResult, Term};
use crate::expr::{BinOp, ConstVal, Expr, UnOp};
use crate::stmt::{Catch, Stmt};
use crate::structure::Region;

/// A named Java statement for `break`/`continue` targets.
#[derive(Debug)]
pub enum Jump {
    Break(Option<String>),
    Continue(Option<String>),
    /// Continue of the loop at the given depth-from-innermost, prefixed by
    /// an emission of the target block's own statements (the jump re-runs
    /// a shared statement-bearing tail that flows back into the header;
    /// a bare Continue would skip those statements).
    ContinueVia(usize, Option<String>),
    /// Unstructured: emit `label:` + goto as comments (best effort).
    RawGoto(usize),
}

#[derive(Debug)]
struct LoopCtx {
    header: usize,
    exits: HashSet<usize>,
    label: String,
}

#[derive(Debug)]
struct SwitchCtx {
    follow: Option<usize>,
    label: String,
    /// Loop-stack depth when the switch was entered: a `break` from a case
    /// body only needs a label when the jump sits inside a loop that was
    /// opened WITHIN the switch (an enclosing loop does not intercept it).
    loops_depth: usize,
}

pub struct Converter<'a> {
    pub cfg: &'a Cfg,
    pub results: &'a Vec<BlockResult>,
    pub groups: Vec<crate::structure::TryGroup>,
    /// Dominators over the full method graph (for goto fallback decisions).
    pub dom: crate::structure::DomInfo,
    /// Block whose statements are currently being converted (for postdom
    /// checks in goto resolution).
    cur_block: usize,
    loops: Vec<LoopCtx>,
    switches: Vec<SwitchCtx>,
    /// Labels actually referenced by break/continue statements.
    used_labels: HashSet<String>,
    /// Follow block of each enclosing If region; a goto to the innermost
    /// follow is natural structured flow and disappears.
    if_follows: Vec<usize>,
    label_counter: usize,
    /// True while converting the last element of a Seq (a trailing Goto
    /// there may be inlined as a copy instead of an unemittable jump).
    goto_is_last: bool,
    /// The block whose emission IMMEDIATELY follows the current position:
    /// the innermost enclosing If's follow while converting its arms, or
    /// the next Seq sibling's head. A RawGoto may elide to fallthrough
    /// ONLY when its target is this block — the old stack-wide
    /// `if_follows.contains` check elided jumps to OUTER follows whose
    /// emission was separated by intervening follow/copy emissions
    /// (jdk17 DatagramChannelImpl.receive: the b15 fall arm's Goto{SET}
    /// elided into cur=14's follow emission, skipping
    /// `sender = sourceSocketAddress()` on the n==0&&isOpen path;
    /// sun.net.www.protocol.http HttpURLConnection.getInputStream0: the
    /// clone arms' Goto{addToCache} fell into the post-loop tail — the
    /// documented addToCache-skip residual).
    expect_next: std::cell::Cell<Option<usize>>,
    /// Set while converting a Seq element that DIRECTLY follows a
    /// CopyStmts of that same block: the back-edge-stub pattern
    /// [CopyStmts{b}, Goto{b}] already emitted b's statements, so the
    /// Goto must not inline them again (jdk11 HttpURLConnection
    /// getInputStream0: the clone tail rendered the clone/removeFromCache
    /// block twice — the second removeFromCache removed the just-cloned
    /// entry from the auth cache; a header-adjacent b would also make
    /// ContinueVia re-emit b's statements after the copy).
    prev_copy: std::cell::Cell<Option<usize>>,
    /// Heads of copy-walked shared tails (from the structurer).
    copied_tails: std::collections::HashSet<usize>,
    /// Collected label emissions: block target -> label name (for `Label` stmts).
    pub pending_labels: HashMap<usize, String>,
    /// Names of FINAL fields of the class being decompiled. A shared
    /// terminator block whose statements write one of them must never be
    /// inlined/copied at extra arrival sites: javac rejects a second
    /// assignment to a final field (sun.security.util.Debug `hexDigits`).
    final_fields: HashSet<String>,
}

/// Remove a trailing `Goto` whose target is the natural continuation.
fn strip_trailing_goto(s: &mut Stmt, follow: Option<usize>) {
    let Some(f) = follow else { return };
    let items = match s {
        Stmt::Block(v) => v,
        Stmt::Goto(t) if *t as usize == f => {
            *s = Stmt::Block(vec![]);
            return;
        }
        _ => return,
    };
    while let Some(last) = items.last_mut() {
        match last {
            Stmt::Goto(t) if *t as usize == f => {
                items.pop();
                return;
            }
            Stmt::Block(inner) if !inner.is_empty() => {
                // descend into trailing block
                let n = inner.len();
                if matches!(inner[n - 1], Stmt::Goto(t) if t as usize == f) {
                    inner.pop();
                    return;
                }
                break;
            }
            _ => break,
        }
    }
}

impl<'a> Converter<'a> {
    pub fn with_copied_tails(mut self, tails: std::collections::HashSet<usize>) -> Self {
        self.copied_tails = tails;
        self
    }

    pub fn with_final_fields(mut self, finals: HashSet<String>) -> Self {
        self.final_fields = finals;
        self
    }

    /// True when any statement assigns a final field of this class.
    fn stmts_write_final(&self, v: &[Stmt]) -> bool {
        v.iter().any(|s| match s {
            Stmt::ExprStmt(Expr::Assign { target, .. }) => {
                matches!(&**target, Expr::Field { name, .. } if self.final_fields.contains(name))
            }
            _ => false,
        })
    }

    /// Chain-aware twin of stmts_write_final for a tail HEAD: walks the
    /// linear single-succ Fall/Goto chain (bounded) so a blank-final write
    /// PAST the head still rejects the inline term-copy (URICertStore
    /// clinit's two-field tail; mirrors structure's
    /// terminator_writes_final chain probe).
    fn tail_chain_writes_final(&self, t: usize) -> bool {
        if self.final_fields.is_empty() {
            return false;
        }
        let mut x = t;
        let mut seen: std::collections::HashSet<usize> = std::collections::HashSet::new();
        for _ in 0..8 {
            if !seen.insert(x) {
                return false;
            }
            if self.stmts_write_final(&self.results[x].stmts) {
                return true;
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

    pub fn new(cfg: &'a Cfg, results: &'a Vec<BlockResult>) -> Self {
        let universe: HashSet<usize> = (0..cfg.blocks.len()).collect();
        let dom = crate::structure::compute_dominators(cfg, &universe, cfg.entry);
        Converter {
            cfg,
            results,
            groups: crate::structure::group_exceptions_with(cfg, Some(results)),
            dom,
            cur_block: usize::MAX,
            loops: Vec::new(),
            switches: Vec::new(),
            if_follows: Vec::new(),
            used_labels: HashSet::new(),
            label_counter: 0,
            goto_is_last: false,
            expect_next: std::cell::Cell::new(None),
            prev_copy: std::cell::Cell::new(None),
            copied_tails: std::collections::HashSet::new(),
            pending_labels: HashMap::new(),
            final_fields: HashSet::new(),
        }
    }

    fn next_label(&mut self) -> String {
        self.label_counter += 1;
        format!("L{}", self.label_counter)
    }

    fn groups_end(&self, gi: usize) -> Option<u16> {
        self.groups.get(gi).map(|g| g.end)
    }

    pub fn convert(&mut self, r: Region) -> Stmt {
        self.conv(r)
    }

    fn conv(&mut self, r: Region) -> Stmt {
        match r {
            Region::Empty => Stmt::Block(vec![]),
            Region::Basic { block } => {
                self.cur_block = block;
                if std::env::var("JCDC_DBG_BLOCKS").is_ok() {
                    eprintln!("conv Basic {} ({} stmts)", block, self.results[block].stmts.len());
                }
                self.block_stmts(block)
            }
            Region::CopyStmts { block } => {
                // Copies include the block's terminator when it is a
                // return/throw (shared terminator blocks are inlined at
                // every arrival site).
                let mut v = self.results[block].stmts.clone();
                match &self.results[block].term {
                    Term::Return(e) => v.push(Stmt::Return(e.clone())),
                    Term::Throw(e) => v.push(Stmt::Throw(e.clone())),
                    _ => {}
                }
                if v.len() == 1 {
                    v.into_iter().next().unwrap()
                } else {
                    Stmt::Block(v)
                }
            }
            Region::Seq(v) => {
                let mut out = Vec::new();
                let n = v.len();
                let heads: Vec<usize> = v
                    .iter()
                    .map(crate::structure::region_head_block)
                    .collect();
                let prev_copies: Vec<Option<usize>> = (0..n)
                    .map(|k| {
                        if k > 0 {
                            match &v[k - 1] {
                                Region::CopyStmts { block } => Some(*block),
                                _ => None,
                            }
                        } else {
                            None
                        }
                    })
                    .collect();
                for (k, x) in v.into_iter().enumerate() {
                    let save = self.goto_is_last;
                    self.goto_is_last = k + 1 == n;
                    let save_pc = self.prev_copy.get();
                    self.prev_copy.set(prev_copies[k]);
                    let save_exp = self.expect_next.get();
                    // Only override when the next emission is KNOWN: a
                    // headless tail (Goto/Empty — a jump out) must keep
                    // the inherited expectation, or a nested arm's Goto
                    // would elide against a phantom (jdk17 dci: Basic17's
                    // MAX head erased the follow expectation and Goto{16}
                    // elided past the SET).
                    if k + 1 < n && heads[k + 1] != usize::MAX {
                        self.expect_next.set(Some(heads[k + 1]));
                    }
                    out.push(self.conv(x));
                    self.expect_next.set(save_exp);
                    self.prev_copy.set(save_pc);
                    self.goto_is_last = save;
                }
                Stmt::Block(out)
            }
            Region::If { block, cond, then_r, else_r, follow, ternary } => {
                self.cur_block = block;
                let mut head = self.block_stmts_no_term(block);
                if let Some((_tv, _fv)) = ternary {
                    // Pure value diamond: the folded conditional flows into
                    // the merge block's rebuilt input stack; nothing to emit
                    // here (branch blocks are statement-free by definition).
                    let _ = cond;
                } else {
                    if let Some(f) = follow {
                        self.if_follows.push(f);
                    }
                    let save_exp = self.expect_next.get();
                    // follow=None keeps the inherited expectation: the
                    // flow leaving this If's arms continues to whatever
                    // follows the If itself.
                    self.expect_next.set(follow.or(save_exp));
                    let then_stmt = self.conv(*then_r);
                    let else_stmt = self.conv(*else_r);
                    self.expect_next.set(save_exp);
                    if follow.is_some() {
                        self.if_follows.pop();
                    }
                    let if_stmt = Stmt::If {
                        cond,
                        then_stmt: Box::new(then_stmt),
                        else_stmt: if else_stmt.is_empty_block() { None } else { Some(Box::new(else_stmt)) },
                    };
                    head.push(if_stmt);
                }
                if head.len() == 1 {
                    head.pop().unwrap()
                } else {
                    Stmt::Block(head)
                }
            }
            Region::Loop { header, body, members, exits } => {
                let label = self.next_label();
                self.loops.push(LoopCtx {
                    header,
                    exits: exits.iter().copied().collect(),
                    label: label.clone(),
                });
                let body_stmt = self.conv(*body);
                let ctx = self.loops.pop().unwrap();
                let _ = members;
                let mut st = self.classify_loop(header, body_stmt, ctx);
                if std::env::var("JCDC_DBG_LOOP").is_ok() {
                    let kind = match &st {
                        Stmt::While { .. } => "While".to_string(),
                        Stmt::DoWhile { .. } => "DoWhile".to_string(),
                        Stmt::For { .. } => "For".to_string(),
                        Stmt::Block(b) => format!("Block{}[{}]", b.len(), b.iter().map(|x| match x {
                            Stmt::DoWhile { .. } => "DoWhile",
                            Stmt::While { .. } => "While",
                            Stmt::Break(_) => "Break",
                            Stmt::Return(_) => "Return",
                            _ => "_",
                        }).collect::<Vec<_>>().join(",")),
                        Stmt::Labeled { .. } => "Labeled".to_string(),
                        _ => "Other".to_string(),
                    };
                    eprintln!("CLASSIFY-OUT header={} -> {}", header, kind);
                }
                if self.used_labels.contains(&label) {
                    st = Stmt::Labeled { label, body: Box::new(st) };
                }
                st
            }
            Region::Switch { block, selector, cases, default, follow } => {
                self.cur_block = block;
                let sw_label = self.next_label();
                self.switches.push(SwitchCtx {
                    follow,
                    label: sw_label.clone(),
                    loops_depth: self.loops.len(),
                });
                let mut case_groups = Vec::new();
                for (vals, r) in cases {
                    let s = self.conv(r);
                    case_groups.push(crate::stmt::CaseGroup {
                        labels: vals,
                        string_labels: vec![],
                        enum_labels: vec![],
                        raw_labels: vec![],
                        guard: None,
                        body: stmt_to_vec(s),
                    });
                }
                let default_stmt = default.map(|d| Box::new(self.conv(*d)));
                self.switches.pop();
                let mut head = self.block_stmts_no_term(block);
                let mut sw = Stmt::Switch {
                    selector,
                    cases: case_groups,
                    default: default_stmt,
                    on_string: false,
                };
                if self.used_labels.contains(&sw_label) {
                    sw = Stmt::Labeled { label: sw_label, body: Box::new(sw) };
                }
                head.push(sw);
                if head.len() == 1 {
                    head.pop().unwrap()
                } else {
                    Stmt::Block(head)
                }
            }
            Region::Try { group_idx, body, catches } => {
                let mut body_stmt = self.conv(*body);
                // Natural exits of the try body / handlers jump to the block
                // right after the try span; that is structured fallthrough.
                let gend = self.groups_end(group_idx);
                let try_follow = gend.and_then(|e| self.cfg.block_at(e));
                strip_trailing_goto(&mut body_stmt, try_follow);
                let mut catch_stmts = Vec::new();
                for (tys, _hblock, r) in catches {
                    let mut s = self.conv(*r);
                    strip_trailing_goto(&mut s, try_follow);
                    catch_stmts.push(Catch {
                        exc: tys,
                        var: u32::MAX, // assigned by the method pipeline (handler store)
                        var_name: None,
                        body: Box::new(s),
                    });
                }
                Stmt::Try { body: Box::new(body_stmt), catches: catch_stmts, finally: None }
            }
            Region::Goto { target } => {
                if std::env::var("JCDC_DBG_GOTO").is_ok() {
                    eprintln!("conv Goto target={} cur_block={} loops={:?} switches={} if_follows={:?}",
                        target, self.cur_block,
                        self.loops.iter().map(|l| (l.header, l.exits.len())).collect::<Vec<_>>(),
                        self.switches.len(), self.if_follows);
                }
                // A jump to an enclosing if's follow that TERMINATES
                // (return/throw) can be inlined: the copy ends this path
                // exactly like the jump would, without needing a label.
                // Same for a jump to a LOOP EXIT that heads a pure
                // terminator chain (stmt-bearing fall-through links
                // ending in return/throw): resolve_goto's loop-exit arm
                // would turn it into a bare `break`, silently dropping
                // the chain's statements between the loop end and the
                // shared return (jdk26 Bits.reserveMemory phase-1:
                // `if (interrupted) <goto interrupt-block>; ` rendered
                // as else-break and the Thread.currentThread()
                // .interrupt() vanished — interruption lost). The
                // inlined copy keeps the abrupt ending (no fall-out
                // duplication); a genuine fall-out exit still breaks.
                //
                let inline_terminator = self.if_follows.contains(&target)
                    && matches!(
                        self.results[target].term,
                        Term::Return(_) | Term::Throw(_)
                    )
                    && !self.tail_chain_writes_final(target);
                if inline_terminator {
                    // Copy the WHOLE terminator chain: the target's own
                    // statements plus every fall-through link down to
                    // the final return/throw (a single-block chain is
                    // the original if-follow case).
                    let mut v: Vec<Stmt> = Vec::new();
                    let mut t = target;
                    let mut guard = 0;
                    loop {
                        v.extend(self.results[t].stmts.clone());
                        match &self.results[t].term {
                            Term::Return(e) => {
                                v.push(Stmt::Return(e.clone()));
                                break;
                            }
                            Term::Throw(e) => {
                                v.push(Stmt::Throw(e.clone()));
                                break;
                            }
                            Term::Fallthrough | Term::Goto
                                if self.cfg.blocks[t].succ.len() == 1 && guard < 8 =>
                            {
                                t = self.cfg.blocks[t].succ[0];
                                guard += 1;
                            }
                            _ => break,
                        }
                    }
                    return if v.len() == 1 {
                        v.into_iter().next().unwrap()
                    } else {
                        Stmt::Block(v)
                    };
                }
                if let Some(j) = self.resolve_goto(target) {
                    match j {
                        Jump::Break(lbl) => {
                            if let Some(l) = &lbl {
                                self.used_labels.insert(l.clone());
                            }
                            Stmt::Break(lbl)
                        }
                        Jump::Continue(lbl) => {
                            if let Some(l) = &lbl {
                                self.used_labels.insert(l.clone());
                            }
                            Stmt::Continue(lbl)
                        }
                        Jump::ContinueVia(t, lbl) => {
                            if let Some(l) = &lbl {
                                self.used_labels.insert(l.clone());
                            }
                            let mut cv = if self.prev_copy.get() == Some(t) {
                                // Statements already emitted by the
                                // immediately preceding CopyStmts.
                                Vec::new()
                            } else {
                                self.results[t].stmts.clone()
                            };
                            cv.push(Stmt::Continue(lbl));
                            if cv.len() == 1 {
                                cv.into_iter().next().unwrap()
                            } else {
                                Stmt::Block(cv)
                            }
                        }
                        Jump::RawGoto(t) => {
                            if std::env::var("JCDC_DBG_GOTO").is_ok() {
                                eprintln!("RAWGOTO t={} copied_tails={:?} if_follows={:?} last={}", t, self.copied_tails, self.if_follows, self.goto_is_last);
                            }
                            // A Goto region is always the last part of its
                            // walk, so the jump either falls through to the
                            // enclosing merge or must be inlined.
                            let term_copy = matches!(
                                self.results[t].term,
                                Term::Return(_) | Term::Throw(_)
                            ) && !self.tail_chain_writes_final(t)
                            && !self.is_retry_loop_header(t);
                            if term_copy {
                                let mut cv = self.results[t].stmts.clone();
                                match &self.results[t].term {
                                    Term::Return(e) => cv.push(Stmt::Return(e.clone())),
                                    Term::Throw(e) => cv.push(Stmt::Throw(e.clone())),
                                    _ => {}
                                }
                                if cv.len() == 1 {
                                    cv.into_iter().next().unwrap()
                                } else {
                                    Stmt::Block(cv)
                                }
                            } else if self
                                .loops
                                .iter()
                                .any(|l| l.exits.contains(&t) || l.header == t)
                                && (self.goto_is_last || self.if_follows.contains(&t))
                            {
                                // The target is an ENCLOSING LOOP's exit:
                                // inside a loop body, falling out of an if
                                // continues the LOOP — the if-follow
                                // elision would silently drop the jump
                                // (jdk11 ObjectInputStream.readSerialData's
                                // finally-copy retry loop lost its `break`,
                                // the finally's while(true) never completed
                                // normally, and the tail went unreachable —
                                // 无法访问的语句 x2 trees). Materialize the
                                // break (innermost enclosing loop).
                                Stmt::Break(None)
                            } else if !matches!(
                                self.results[t].term,
                                Term::Return(_) | Term::Throw(_)
                            ) && !self.results[t].stmts.is_empty()
                                && !self.copied_tails.contains(&t)
                                && self.prev_copy.get() != Some(t)
                                && self
                                    .expect_next
                                    .get()
                                    .map(|nx| {
                                        // The next emission is a copy that
                                        // STARTS PAST t (at a successor of t
                                        // already in copied_tails): eliding
                                        // would silently skip t's own
                                        // statements, and no emitted copy
                                        // covers them. (sj17 receive:
                                        // Goto{16=SET}, expect=Some(17),
                                        // 17 copied, 16 not.) If t itself is
                                        // in copied_tails, an emitted full
                                        // copy already includes t's stmts —
                                        // inlining would double-emit (w26
                                        // receive: Goto{14}, 14 copied).
                                        let mut x = t;
                                        for _ in 0..8 {
                                            if x == nx {
                                                return x != t;
                                            }
                                            if self.copied_tails.contains(&x) {
                                                return false;
                                            }
                                            match self.cfg.blocks[x].succ.first() {
                                                Some(&n) => x = n,
                                                None => return false,
                                            }
                                        }
                                        false
                                    })
                                    .unwrap_or(false)
                                && (self.if_follows.iter().any(|f| {
                                    self.cfg.blocks[t].succ.contains(f)
                                }))
                            {
                                // Statement-bearing target FIRST: eliding
                                // (goto_is_last / expect / copy-tail) would
                                // silently skip t's own statements when the
                                // next emission is a copy of t's SUCCESSOR
                                // rather than t itself (jdk17
                                // DatagramChannelImpl.receive: Goto{16=
                                // `sender = sourceSocketAddress()`} elided
                                // via reaches_copy_tail(16->17) into the
                                // arm's Basic(17) copy — the n==0&&isOpen
                                // path returned a null sender). The inline
                                // below emits t's statements and then falls
                                // through to the same continuation.
                                let cv = self.results[t].stmts.clone();
                                if cv.len() == 1 {
                                    cv.into_iter().next().unwrap()
                                } else {
                                    Stmt::Block(cv)
                                }
                            } else if self.goto_is_last
                                || self.expect_next.get() == Some(t)
                                || self.reaches_copy_tail(t)
                            {
                                // Natural fallthrough reaches the same
                                // continuation the jump targeted.
                                Stmt::Block(vec![])
                            } else if !matches!(
                                self.results[t].term,
                                Term::Return(_) | Term::Throw(_)
                            ) && self.prev_copy.get() != Some(t)
                                && (self.if_follows.iter().any(|f| {
                                    self.cfg.blocks[t].succ.contains(f)
                                }))
                            {
                                // The jump re-enters an already-structured
                                // block whose flow ends at an enclosing
                                // if-follow: inline its statements; the
                                // natural continuation matches the jump's.
                                let cv = self.results[t].stmts.clone();
                                if cv.len() == 1 {
                                    cv.into_iter().next().unwrap()
                                } else {
                                    Stmt::Block(cv)
                                }
                            } else {
                                Stmt::Goto(t as u32)
                            }
                        }
                    }
                } else {
                    Stmt::Block(vec![])
                }
            }
        }
    }

    /// Statements of a block including its terminal (return/throw), but NOT
    /// the structural terminals (cond/switch/goto — handled by regions).
    fn block_stmts(&mut self, block: usize) -> Stmt {
        let mut v = self.block_stmts_no_term(block);
        match &self.results[block].term {
            Term::Return(e) => v.push(Stmt::Return(e.clone())),
            Term::Throw(e) => v.push(Stmt::Throw(e.clone())),
            Term::Jsr | Term::Ret => v.push(Stmt::Comment("// jsr/ret not supported".into())),
            _ => {}
        }
        if v.len() == 1 {
            v.pop().unwrap()
        } else {
            Stmt::Block(v)
        }
    }

    fn block_stmts_no_term(&self, block: usize) -> Vec<Stmt> {
        // Monitor markers are kept; synchronized reconstruction happens later.
        self.results[block].stmts.clone()
    }

    /// Resolve a goto target against the scope stack.
    fn resolve_goto(&mut self, target: usize) -> Option<Jump> {
        // continue: innermost loop whose header == target
        if let Some(i) = (0..self.loops.len()).rev().find(|&i| self.loops[i].header == target) {
            let depth = self.loops.len() - 1 - i;
            return Some(if depth == 0 {
                Jump::Continue(None)
            } else {
                Jump::Continue(Some(self.loops[i].label.clone()))
            });
        }
        // break out of a loop whose exit set contains the target; pick the
        // OUTERMOST such loop — an exit of nested loops (e.g. `break outer`)
        // belongs to every enclosing loop's exit set, and breaking only the
        // innermost would wrongly re-enter the outer loop.
        if let Some(li) = (0..self.loops.len()).find(|&i| self.loops[i].exits.contains(&target)) {
            // RESTART-STUB exit: the target chains through statement-free
            // stubs back into an enclosing-or-self loop HEADER — the jump
            // re-iterates THAT loop, it does not break out of anything
            // (jdk11/17/26 ConcurrentLinkedQueue.poll's p==q arm `goto
            // restartFromHead`: exit 12 is the `goto 0` stub; rendering
            // break+break fell to the post-loop tail and returned the
            // STALE item instead of restarting from head). The broad
            // walk-side continue-stub precedence was reverted once
            // (Pattern.clazz: switch-case goto stubs must stay
            // RawGoto-elided so the emitter re-appends case breaks) —
            // this form is scoped to genuine loop exits with no open
            // switch on the stack.
            if self.switches.is_empty() {
                let mut x = target;
                let mut guard = 0;
                let header_hit = loop {
                    if let Some(hi) = self.loops.iter().position(|l| l.header == x) {
                        if hi <= li {
                            break Some(hi);
                        }
                    }
                    if guard >= 8 {
                        break None;
                    }
                    let r = &self.results[x];
                    let stub = r.stmts.is_empty()
                        && r.out_stack.is_empty()
                        && matches!(r.term, Term::Fallthrough | Term::Goto)
                        && self.cfg.blocks[x].succ.len() == 1;
                    if !stub {
                        break None;
                    }
                    x = self.cfg.blocks[x].succ[0];
                    guard += 1;
                };
                if let Some(hi) = header_hit {
                    let depth = self.loops.len() - 1 - hi;
                    return Some(if depth == 0 {
                        Jump::Continue(None)
                    } else {
                        Jump::Continue(Some(self.loops[hi].label.clone()))
                    });
                }
            }
            // switches opened after that loop intercept a plain `break`
            let crosses_switch = !self.switches.is_empty();
            return Some(if li + 1 == self.loops.len() && !crosses_switch {
                Jump::Break(None)
            } else {
                Jump::Break(Some(self.loops[li].label.clone()))
            });
        }
        if let Some(si) = (0..self.switches.len()).rev().find(|&i| self.switches[i].follow == Some(target)) {
            return Some(if si + 1 == self.switches.len() && self.loops.len() == self.switches[si].loops_depth {
                Jump::Break(None)
            } else {
                Jump::Break(Some(self.switches[si].label.clone()))
            });
        }
        // Natural flow to the enclosing if's merge point: no statement.
        // Only the INNERMOST open follow qualifies — eliding a jump to an
        // outer follow would silently skip the statements between (e.g. a
        // shared throw at the end of an else-branch).
        if self.if_follows.last() == Some(&target) {
            return None;
        }
        // Inside a loop, a jump to an already-structured block that flows
        // back into the loop is a CONTINUE of the innermost such loop: the
        // target's statements were emitted earlier in this body, and the
        // natural continuation after this region is the loop bottom (an
        // if-follow or a fall-out exit), never the target. Eliding it as
        // fallthrough (the RawGoto `goto_is_last` arm) silently dropped the
        // iteration: jdk11/17 InstantPrinterParser.format's second loop
        // copy emitted `if (i >= fractionalDigits) {}` with no way out --
        // the digit append + back edge vanished (semantically an infinite
        // loop; javac: 缺少返回语句 on the method tail).
        // A target that is a loop EXIT keeps its RawGoto resolution (the
        // conv arm materializes the break): Pattern.clazz's switch-case
        // `break` targets sit on the loop-bottom path AND name exits —
        // continuing there made every switch exit abrupt and the post-
        // switch tail unreachable (无法访问的语句 x3 trees).
        let is_any_exit = self.loops.iter().any(|l| l.exits.contains(&target));
        if !is_any_exit && self.switches.is_empty() {
            // STUB-TARGET continue: a statement-free confluence stub that
            // can reach an enclosing header re-iterates that loop (its own
            // flow was emitted earlier in this body copy; IPP's can_reach
            // targets t=43/18/96/89/114/21/7 are all stubs).
            // HEADER-ADJACENT statement-bearing target: the jump re-runs a
            // shared tail whose statements were NOT emitted on this path —
            // inline them and continue (jdk11 BigInteger.nextProbablePrime
            // sieve arms: Goto{result=result.add(TWO)} flowing straight to
            // the header; a bare Continue skipped the advance and left
            // while(true) as the method's only completion: 缺少返回语句).
            // Statement-bearing targets with a BRANCHING or statement
            // bearing chain to the header keep RawGoto resolution (huc
            // getInputStream0's clone/getValue tails flow through shared
            // forward code — continuing there would skip it).
            let mut via_label: Option<Option<String>> = None;
            if self.results[target].stmts.is_empty() {
                if let Some(i) = (0..self.loops.len())
                    .rev()
                    .find(|&i| {
                        crate::structure::can_reach_cfg(self.cfg, target, self.loops[i].header, 4096)
                    })
                {
                    let depth = self.loops.len() - 1 - i;
                    via_label = Some(if depth == 0 {
                        None
                    } else {
                        Some(self.loops[i].label.clone())
                    });
                }
            } else {
                let mut x = target;
                for _ in 0..8 {
                    if let Some(hi) = self.loops.iter().position(|l| l.header == x) {
                        let depth = self.loops.len() - 1 - hi;
                        via_label = Some(if depth == 0 {
                            None
                        } else {
                            Some(self.loops[hi].label.clone())
                        });
                        break;
                    }
                    if !self.results[x].stmts.is_empty() && x != target {
                        break;
                    }
                    if self.cfg.blocks[x].succ.len() != 1 {
                        break;
                    }
                    x = self.cfg.blocks[x].succ[0];
                }
            }
            if let Some(lbl) = via_label {
                return Some(if self.results[target].stmts.is_empty() {
                    Jump::Continue(lbl)
                } else {
                    Jump::ContinueVia(target, lbl)
                });
            }
        }
        // Inside a loop, a forward escape that cannot reach back into the
        // loop is a break of the innermost loop.
        if !self.loops.is_empty()
            && !crate::structure::can_reach_cfg(
                self.cfg,
                target,
                self.loops[self.loops.len() - 1].header,
                4096,
            )
        {
            return Some(Jump::Break(None));
        }
        // Unstructured jump.
        Some(Jump::RawGoto(target))
    }

    /// True if `a` post-dominates `b` (every path from b exits through a).
    /// True when a jump to `t` is equivalent to natural fallthrough: `t`
    /// (or the end of a chain of statement-free blocks starting at `t`) is
    /// a copied shared tail or an open if-follow that the enclosing flow
    /// will emit next anyway.
    /// True when `t` is the head of a javac retry loop: some exception
    /// handler protecting `t` has no normal preds and flows straight back
    /// to `t` (`catch (InterruptedException e) { ..; goto head }`). A Goto
    /// to such a header re-executes the protected body — inlining the
    /// body's terminator as a "shared tail copy" drops it out of its try
    /// (jdk26 Future.exceptionNow: the IE catch got `get(); throw ISE`
    /// unprotected — 未报告的异常错误 InterruptedException).
    fn is_retry_loop_header(&self, t: usize) -> bool {
        self.cfg.exc_edges.iter().any(|e| {
            e.from == t
                && e.to != t
                && self.cfg.blocks[e.to].pred.is_empty()
                && self.cfg.blocks[e.to].succ.len() == 1
                && self.cfg.blocks[e.to].succ[0] == t
        })
    }

    fn reaches_copy_tail(&self, t: usize) -> bool {
        let mut x = t;
        for _ in 0..8 {
            if self.copied_tails.contains(&x) || self.if_follows.contains(&x) {
                return true;
            }
            if !self.results[x].stmts.is_empty() {
                return false;
            }
            match &self.results[x].term {
                Term::Fallthrough | Term::Goto => {
                    match self.cfg.blocks[x].succ.first() {
                        Some(&n) => x = n,
                        None => return false,
                    }
                }
                _ => return false,
            }
        }
        false
    }

#[allow(dead_code)]
    fn postdominates(&self, a: usize, b: usize, universe: &HashSet<usize>) -> bool {
        // BFS from b avoiding a; if no exit block is reachable, a post-dominates.
        let mut seen = HashSet::new();
        let mut q = std::collections::VecDeque::new();
        q.push_back(b);
        seen.insert(b);
        while let Some(x) = q.pop_front() {
            for &s in &self.cfg.blocks[x].succ {
                if s == a {
                    continue;
                }
                if !universe.contains(&s) {
                    continue;
                }
                if seen.insert(s) {
                    q.push_back(s);
                }
            }
            if self.cfg.blocks[x].succ.is_empty() && x != a && x != b {
                // reached an exit without passing through a
                return false;
            }
        }
        // also treat blocks leaving the universe as exits
        true
    }

    /// Classify a loop region into while / do-while / infinite and assemble
    /// the final statement.
    fn classify_loop(&mut self, header: usize, body_stmt: Stmt, ctx: LoopCtx) -> Stmt {
        let term = self.results[header].term.clone();
        let succs = self.cfg.blocks[header].succ.clone();

        match term {
            Term::Cond { cond } if succs.len() == 2 => {
                let taken = succs[1];
                let fall = succs[0];
                if taken == header && ctx.exits.contains(&fall) {
                    // Self-loop: the header block holds both the body and
                    // the trailing conditional back edge → do-while. The
                    // fallthrough side is the loop exit. (When the fall
                    // side is INTERIOR the self-edge is an in-body retry
                    // jump of a loop with no normal completion at all —
                    // rotating it into a do-while bottom invents an exit
                    // path: jdk11/17/26 DSAParameterGenerator.generatePandQ's
                    // `if (!resultQ.isProbablePrime(..)) goto <Q-gen>`
                    // self-retry falls through into the P-search interior;
                    // the fabricated do-while fell out to the method end —
                    // 缺少返回语句. Those shapes take the interior-diamond
                    // while(true) arm below.)
                    // A compound (multi-test) trailing condition folds first:
                    // `if(c1)continue; .. if(cN)continue; else exit;` becomes
                    // `do{body}while(c1||..||cN); exit`.
                    if let Some((stmts, c, exit)) = extract_compound_do_while(&body_stmt) {
                        // An extracted exit that is the loop's OWN unlabeled
                        // break must be dropped: the do-while condition false
                        // already exits, and re-emitting the break OUTSIDE the
                        // loop is a stray `break;` (compile error). SESE's
                        // explicit `Goto{header}` -> continue makes self-loop
                        // bodies hit this shape (`if (c) continue; else break;`).
                        // return/throw/labeled-break exits stay (real fall-out).
                        if matches!(exit, Stmt::Break(None)) {
                            return Stmt::DoWhile {
                                body: Box::new(Stmt::Block(stmts)),
                                cond: c,
                            };
                        }
                        return Stmt::Block(vec![
                            Stmt::DoWhile { body: Box::new(Stmt::Block(stmts)), cond: c },
                            exit,
                        ]);
                    }
                    let (stmts, c) = match extract_trailing_do_while(&body_stmt) {
                        Some(x) => x,
                        None => (stmt_to_vec(body_stmt), cond.clone()),
                    };
                    return Stmt::DoWhile {
                        body: Box::new(Stmt::Block(stmts)),
                        cond: c,
                    };
                }
                if fall == header && ctx.exits.contains(&taken) {
                    // Inverted self-loop: `while (!(c)) body` — the taken
                    // side exits, the fallthrough loops back.
                    let inner2 = strip_trailing_continue(body_stmt);
                    return Stmt::While {
                        cond: negate(cond.clone()),
                        body: Box::new(inner2),
                    };
                }
                let taken_is_exit = ctx.exits.contains(&taken);
                if std::env::var("JCDC_DBG_LOOP").is_ok() {
                    eprintln!("CLASSIFY2 header={} taken={} fall={} exits={:?}", header, taken, fall, ctx.exits);
                }
                if !taken_is_exit && !ctx.exits.contains(&fall) {
                    // Multi-block loop condition. The header's fallthrough
                    // may be a pure condition-continuation test block whose
                    // taken side is the loop exit and whose fall side rejoins
                    // the body (`taken`). javac compiles `while (cH || !cB)`
                    // exactly this way:
                    //   H: if cH goto body;  B: if cB goto exit;  body: ..; goto H
                    // Fold B into the while condition. Without this the body
                    // walk re-emits H and B as empty `if`s inside a
                    // `while(true)`, dropping the exit and leaving an infinite
                    // loop plus an unreachable trailing statement.
                    if self.results[fall].stmts.is_empty() {
                        if let Term::Cond { cond: cb } = &self.results[fall].term {
                            let bs = self.cfg.blocks[fall].succ.clone();
                            if bs.len() == 2 && ctx.exits.contains(&bs[1]) && bs[0] == taken {
                                let combined = Expr::Bin {
                                    op: BinOp::LogOr,
                                    l: Box::new(cond.clone()),
                                    r: Box::new(negate(cb.clone())),
                                    ty: None,
                                };
                                // The body is the converted region
                                // remainder, NOT the taken block's raw
                                // statements: when `taken` is wrapped in
                                // regions (a try/catch group around the
                                // body call), the raw-stmt body silently
                                // drops them (jdk11 SocketChannelImpl
                                // .implCloseSelectableChannel: the
                                // wait()-loop's try/catch(Interrupted
                                // Exception) region vanished — bare
                                // wait() — 未报告的异常错误). The
                                // leading guard If is the condition being
                                // folded here; strip it and keep the rest.
                                let mut parts = stmt_to_vec(body_stmt);
                                if matches!(parts.first(), Some(Stmt::If { .. })) {
                                    parts.remove(0);
                                }
                                let body = if parts.is_empty() {
                                    Stmt::Block(self.results[taken].stmts.clone())
                                } else {
                                    let rest = if parts.len() == 1 {
                                        parts.pop().unwrap()
                                    } else {
                                        Stmt::Block(parts)
                                    };
                                    strip_trailing_continue(rest)
                                };
                                if std::env::var("JCDC_DBG_LOOP").is_ok() {
                                    eprintln!(
                                        "CLASSIFY-CONDCHAIN header={} B={} body={} exits={:?}",
                                        header, fall, taken, ctx.exits
                                    );
                                }
                                return Stmt::While { cond: combined, body: Box::new(body) };
                            }
                        }
                    }
                    // Neither successor leaves the loop: the header's Cond
                    // is an interior diamond (e.g. a ternary inside an
                    // infinite `for(;;)` whose back edge targets the header
                    // top), not an exit test. Keep it in the body.
                    return Stmt::While {
                        cond: Expr::Const(ConstVal::Int(1)),
                        body: Box::new(body_stmt),
                    };
                }
                // The body walk re-emitted the header's own If region; unwrap
                // it so the loop reads `while (C) { else-part }`.
                let (inner, exit_stmts) = split_leading_if(&body_stmt, &cond);
                // A top test the structurer wrapped in a TRY (the header
                // block sits inside its handler's protected range — jdk26
                // Bits.reserveMemory's backoff retry loop tests
                // tryReserveOrClean(..) throws InterruptedException under
                // its own catch(IE) retry handler): rotating the test into
                // `while (C)` evaluates the call OUTSIDE every handler —
                // 未报告的异常错误InterruptedException. split_leading_if
                // deliberately cannot reach through the Try (the rotated
                // cond would still be unprotected), so keep the test where
                // the bytecode has it and stay on while(true). The earlier
                // implCloseSelectableChannel guard (raw-stmt bodies losing
                // the leading If's statements) does not apply: the If lives
                // intact inside the Try.

                if std::env::var("JCDC_DBG_LOOP").is_ok() {
                    eprintln!(
                        "CLASSIFY header={} taken_is_exit={} exit_stmts={}",
                        header,
                        taken_is_exit,
                        exit_stmts.len()
                    );
                }
                let inner = strip_trailing_continue(inner);
                let while_cond = if taken_is_exit { negate(cond.clone()) } else { cond.clone() };
                let plain_exit = exit_stmts.is_empty()
                    || matches!(exit_stmts.as_slice(), [Stmt::Break(_)])
                    || matches!(exit_stmts.as_slice(), [Stmt::Block(b)] if b.is_empty());
                if taken_is_exit && plain_exit {
                    match try_protected_dowhile(inner, &cond) {
                        Ok(dw) => dw,
                        Err(inner) => Stmt::While { cond: while_cond, body: Box::new(inner) },
                    }
                } else if taken_is_exit {
                    // Exit branch runs statements before leaving:
                    // while (true) { if (C_exit) { stmts; break; } body }
                    // `cond` IS the exit test here (the taken side exits —
                    // negate(cond) inverted the guard: jdk17 CHM
                    // comparableClassFor emitted `if (i < len) return null`
                    // inside while(true), inverting the loop). The break is
                    // only appended when the exit statements do not already
                    // terminate (return null + break = unreachable stmt).
                    let mut ex = exit_stmts;
                    let already_term = matches!(
                        ex.last(),
                        Some(Stmt::Return(_)) | Some(Stmt::Throw(_)) | Some(Stmt::Break(_))
                    );
                    if !already_term {
                        ex.push(Stmt::Break(None));
                    }
                    let guard = Stmt::If {
                        cond: cond.clone(),
                        then_stmt: Box::new(Stmt::Block(ex)),
                        else_stmt: None,
                    };
                    let mut v = vec![guard];
                    v.extend(stmt_to_vec(inner));
                    Stmt::While { cond: Expr::Const(ConstVal::Int(1)), body: Box::new(Stmt::Block(v)) }
                } else {
                    // Unusual orientation: the fallthrough side exits.
                    if exit_stmts.is_empty()
                        || matches!(exit_stmts.as_slice(), [Stmt::Break(_)])
                        || matches!(exit_stmts.as_slice(), [Stmt::Block(b)] if b.is_empty())
                    {
                        // then-side was the exit scaffolding; body is `inner`
                        match try_protected_dowhile(inner, &cond) {
                            Ok(dw) => dw,
                            Err(inner) => Stmt::While { cond: while_cond, body: Box::new(inner) },
                        }
                    } else {
                        // then-side carries the body ending with the back
                        // edge; fallthrough exits.
                        let body2 = strip_trailing_continue(stmts_to_stmt(exit_stmts));
                        Stmt::While { cond: while_cond, body: Box::new(body2) }
                    }
                }
            }
            Term::Goto | Term::Fallthrough => {
                // Possibly do-while: the body ends with a conditional jump
                // back to the header (`if (c) continue;` or inverted), or a
                // COMPOUND run of such tests ending in the loop exit.
                if let Some((stmts, c, exit)) = extract_compound_do_while(&body_stmt) {
                    // Same guard as the self-loop compound path above: an
                    // extracted exit that is the loop's OWN unlabeled break
                    // must be dropped — the do-while condition false already
                    // exits, and a `break;` re-emitted OUTSIDE the loop is a
                    // stray (it also makes stmt_terminates treat the sequence
                    // as terminated, so prune_unreachable drops the real
                    // tail: jdk26 Resolver.bind `return this` — 缺少返回语句).
                    // SESE's rotated do-whiles hit this shape: the tail test
                    // block becomes `if (c) continue; else break;`.
                    // return/throw/labeled-break exits stay (real fall-out).
                    if matches!(exit, Stmt::Break(None)) {
                        return Stmt::DoWhile {
                            body: Box::new(Stmt::Block(stmts)),
                            cond: c,
                        };
                    }
                    return Stmt::Block(vec![
                        Stmt::DoWhile { body: Box::new(Stmt::Block(stmts)), cond: c },
                        exit,
                    ]);
                }
                if let Some((stmts, c)) = extract_trailing_do_while(&body_stmt) {
                    return Stmt::DoWhile { body: Box::new(Stmt::Block(stmts)), cond: c };
                }
                Stmt::While {
                    cond: Expr::Const(ConstVal::Int(1)),
                    body: Box::new(body_stmt),
                }
            }
            _ => Stmt::While {
                cond: Expr::Const(ConstVal::Int(1)),
                body: Box::new(body_stmt),
            },
        }
    }

    /// True if `target` is inside the loop currently being classified
    /// (approximated: target can reach the header again).
#[allow(dead_code)]
    fn loop_contains(&self, header: usize, target: usize) -> bool {
        can_reach(self.cfg, target, header, 8192)
    }

#[allow(dead_code)]
    fn loop_exit_contains(&self, header: usize, target: usize) -> bool {
        // The loop currently being classified is the innermost on the stack
        // BEFORE it was popped; ctx.exits was consumed. Recompute cheaply:
        // target is an exit if it is not reachable-back-to-header within the
        // loop members — approximated by checking the parent scope recorded
        // in loops stack is empty here; use cfg: header's own successors that
        // leave... For the header itself, an exit is any successor that is
        // not dominated by header OR is not in the natural loop. Simple
        // approximation: a successor s is "in loop" if s can reach header
        // again via normal edges.
        can_reach(self.cfg, target, header, 4096).not()
    }
}

#[allow(dead_code)]
trait NotExt {
    fn not(self) -> bool;
}
impl NotExt for bool {
    fn not(self) -> bool {
        !self
    }
}

#[allow(dead_code)]
fn can_reach(cfg: &Cfg, from: usize, to: usize, budget: usize) -> bool {
    if from == to {
        return true;
    }
    let mut seen = HashSet::new();
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

/// If the body starts with the loop header's own `If` (same condition
/// expression), return (else-branch content, then-branch content).
/// Otherwise return (body, []).
fn stmts_to_stmt(v: Vec<Stmt>) -> Stmt {
    match v.len() {
        0 => Stmt::Block(vec![]),
        1 => v.into_iter().next().unwrap(),
        _ => Stmt::Block(v),
    }
}

/// When the loop's top test lives inside a Try in `inner` (the header
/// block sits in its handler's protected range — jdk26
/// Bits.reserveMemory's backoff retry loop tests
/// `tryReserveOrClean(..) throws InterruptedException` under its own
/// catch(IE) handler), the `while (C)` rotation would evaluate C
/// OUTSIDE every handler — 未报告的异常错误InterruptedException.
/// Rewrite as a do-while instead: inject `break` into the embedded
/// If's EMPTY arm (the exit side — the exit blocks live outside the
/// loop region as its continuation siblings, so the empty arm is the
/// fall-out) and loop unconditionally. The sibling tail then stays
/// reachable as the do-while's natural completion. Returns None when
/// the test is not try-wrapped (plain rotation applies) or when the
/// shape is ambiguous (both If arms materialized).
fn try_protected_dowhile(inner: Stmt, cond: &Expr) -> Result<Stmt, Stmt> {
    // The exit side of the embedded test: an Empty region conversion
    // (empty block / missing else) or an ALREADY-materialized plain
    // `break` (the merged-span shape walks the sleep region as the
    // then-arm and breaks on the exit side directly).
    fn is_empty(s: &Stmt) -> bool {
        match s {
            Stmt::Block(v) => v.is_empty() || (v.len() == 1 && is_empty(&v[0])),
            Stmt::Break(None) => false,
            _ => false,
        }
    }
    fn inject(s: &mut Stmt, cond: &Expr) -> bool {
        match s {
            Stmt::If { cond: c, then_stmt, else_stmt } if c == cond => {
                let then_empty = is_empty(then_stmt);
                let else_empty =
                    else_stmt.as_ref().map(|e| is_empty(e)).unwrap_or(true);
                if then_empty && !else_empty {
                    *then_stmt = Box::new(Stmt::Break(None));
                    true
                } else if else_empty && !then_empty {
                    *else_stmt = Some(Box::new(Stmt::Break(None)));
                    true
                } else {
                    false
                }
            }
            Stmt::Try { body, .. } | Stmt::TryWithResources { body, .. } => {
                inject(body, cond)
            }
            Stmt::Block(v) => v.first_mut().map(|f| inject(f, cond)).unwrap_or(false),
            Stmt::Labeled { body, .. } | Stmt::Synchronized { body, .. } => inject(body, cond),
            _ => false,
        }
    }
    let mut b = inner;
    if inject(&mut b, cond) {
        Ok(Stmt::DoWhile {
            body: Box::new(b),
            cond: Expr::Const(ConstVal::Int(1)),
        })
    } else {
        Err(b)
    }
}

fn split_leading_if(body: &Stmt, cond: &Expr) -> (Stmt, Vec<Stmt>) {
    let items = match body {
        Stmt::Block(v) => v,
        other => {
            return match other {
                Stmt::If { cond: c, then_stmt, else_stmt } if c == cond => (
                    else_stmt.as_ref().map(|e| (**e).clone()).unwrap_or(Stmt::Block(vec![])),
                    stmt_to_vec((**then_stmt).clone()),
                ),
                _ => (other.clone(), vec![]),
            };
        }
    };
    if let Some(first) = items.first() {
        if let Stmt::If { cond: c, then_stmt, else_stmt } = first {
            if c == cond {
                let inner = if items.len() == 1 {
                    else_stmt.as_ref().map(|e| (**e).clone()).unwrap_or(Stmt::Block(vec![]))
                } else {
                    let mut rest = vec![else_stmt
                        .as_ref()
                        .map(|e| (**e).clone())
                        .unwrap_or(Stmt::Block(vec![]))];
                    rest.extend(items[1..].iter().cloned());
                    Stmt::Block(rest)
                };
                return (inner, stmt_to_vec((**then_stmt).clone()));
            }
        }
    }
    (body.clone(), vec![])
}

/// Remove a trailing `continue;` (loop back-edge) from a statement list.
fn strip_trailing_continue(s: Stmt) -> Stmt {
    match s {
        Stmt::Block(mut v) => {
            while matches!(v.last(), Some(Stmt::Continue(None))) {
                v.pop();
            }
            if v.len() == 1 && matches!(v[0], Stmt::Block(_)) {
                let inner = match v.pop().unwrap() {
                    Stmt::Block(inner) => inner,
                    _ => unreachable!(),
                };
                return strip_trailing_continue(Stmt::Block(inner));
            }
            Stmt::Block(v)
        }
        Stmt::Continue(None) => Stmt::Block(vec![]),
        other => other,
    }
}

pub fn negate(e: Expr) -> Expr {
    match e {
        Expr::Un { op: UnOp::Not, e } => *e,
        // De Morgan for the short-circuit operators: !(A && B) =
        // !A || !B, !(A || B) = !A && !B — recursing through negate
        // keeps comparison operands cleanly inverted. An op-only swap
        // (the historical invert() LogAnd<->LogOr mapping) silently
        // changed the condition's meaning: Arrays.equals' folded
        // `a == null || a2 == null` inverted to `a == null && a2 ==
        // null`, NPE-ing the a2==null path.
        Expr::Bin { op: op @ (crate::expr::BinOp::LogAnd | crate::expr::BinOp::LogOr), l, r, ty } => {
            let swapped = if matches!(op, crate::expr::BinOp::LogAnd) {
                crate::expr::BinOp::LogOr
            } else {
                crate::expr::BinOp::LogAnd
            };
            Expr::Bin {
                op: swapped,
                l: Box::new(negate(*l)),
                r: Box::new(negate(*r)),
                ty,
            }
        }
        Expr::Bin { op, l, r, ty } => {
            if let Some(inv) = op.invert() {
                Expr::Bin { op: inv, l, r, ty }
            } else {
                Expr::Un { op: UnOp::Not, e: Box::new(Expr::Bin { op, l, r, ty }) }
            }
        }
        other => Expr::Un { op: UnOp::Not, e: Box::new(other) },
    }
}

/// True for a bare `continue;` (or a block wrapping just one).
fn is_continue_stmt(s: &Stmt) -> bool {
    matches!(s, Stmt::Continue(None))
        || matches!(s, Stmt::Block(v) if v.len() == 1 && matches!(v[0], Stmt::Continue(None)))
}

/// Detect a COMPOUND trailing do-while condition: the body ends with a run of
/// `if (c1) continue;` ... `if (cN) continue; else <exit>;`. javac emits this
/// for `do { body } while (c1 || ... || cN);` followed by the loop exit when
/// the condition is a short-circuit `||` whose tests each jump back to the
/// body head (e.g. `Random.internalNextInt`: `while (r < origin || r >=
/// bound)`). Fold the run into a single do-while whose condition is the `||`
/// of the tests, returning the body statements, that condition, and the exit
/// action (`<exit>`) to emit right after the loop.
fn extract_compound_do_while(body: &Stmt) -> Option<(Vec<Stmt>, Expr, Stmt)> {
    // Flatten nested straight-line blocks: the loop body may group the first
    // condition test(s) inside a nested Block (the self-loop header's region)
    // while later tests are siblings. Splicing pure sequence blocks is safe.
    fn flatten_seq(s: &Stmt) -> Vec<Stmt> {
        match s {
            Stmt::Block(v) => {
                let mut out = Vec::new();
                for x in v {
                    out.extend(flatten_seq(x));
                }
                out
            }
            other => vec![other.clone()],
        }
    }
    let mut stmts = flatten_seq(body);
    // Unnest the rendered if/else-if CHAIN spine: javac's bottom-tested
    // `if (c1) continue; if (c2) continue; ... else exit;` disjunct run
    // converts to ONE nested If whose else arms hold the remaining
    // tests — opaque to the backwards scan below, which would fold only
    // c1 and push the whole c2..cN chain out of the loop as the "exit"
    // (jdk26 ML_DSA.signInternal: `do { expandMask.. } while
    // (vectorNormBound(z,..));` with the c2/hint chain — and its
    // continue/break — stranded after the loop, continue 在 loop 外部
    // ×2). Splitting each continue-then If back into siblings restores
    // the flat run; semantics are identical (the then arm is a bare
    // continue with no fallthrough, and the LAST else is preserved as
    // the final statement's else = the loop's exit route).
    {
        let mut flat: Vec<Stmt> = Vec::new();
        for st in stmts.into_iter() {
            let mut cur = st;
            loop {
                match cur {
                    Stmt::If { cond, then_stmt, else_stmt: Some(e) }
                        if is_continue_stmt(&then_stmt) =>
                    {
                        flat.push(Stmt::If {
                            cond,
                            then_stmt,
                            else_stmt: None,
                        });
                        cur = *e;
                    }
                    other => {
                        flat.push(other);
                        break;
                    }
                }
            }
        }
        stmts = flat;
    }
    let n = stmts.len();
    if n < 2 {
        return None;
    }
    // Last statement: `if (c_last) continue; else <exit>` — the exit is the
    // loop's fall-out (a return/throw/break), NOT another continue.
    let (c_last, exit) = match &stmts[n - 1] {
        Stmt::If { cond, then_stmt, else_stmt: Some(e) }
            if is_continue_stmt(then_stmt) && !is_continue_stmt(e) =>
        {
            (cond.clone(), (**e).clone())
        }
        _ => return None,
    };
    // Walk backwards over preceding `if (ci) continue;` (no else) tests.
    let mut conds = vec![c_last];
    let mut i = n - 1;
    while i >= 1 {
        match &stmts[i - 1] {
            Stmt::If { cond, then_stmt, else_stmt: None } if is_continue_stmt(then_stmt) => {
                conds.push(cond.clone());
                i -= 1;
            }
            _ => break,
        }
    }
    let body_stmts: Vec<Stmt> = stmts[..i].to_vec();
    // cond = c1 || c2 || ... || c_last (conds currently reversed).
    let mut it = conds.into_iter().rev();
    let mut cond = it.next().unwrap();
    for c in it {
        cond = Expr::Bin { op: BinOp::LogOr, l: Box::new(c), r: Box::new(cond), ty: None };
    }
    Some((body_stmts, cond, exit))
}

/// Detect a trailing do-while condition at the end of a loop body:
/// `if (c) continue;` → cond c, or `if (c) {} else continue;` → cond !c.
fn extract_trailing_do_while(body: &Stmt) -> Option<(Vec<Stmt>, Expr)> {
    let mut stmts = match body {
        Stmt::Block(v) => v.clone(),
        other => vec![other.clone()],
    };
    if stmts.is_empty() {
        return None;
    }
    let n = stmts.len() - 1;
    if let Stmt::If { cond, then_stmt, else_stmt } = &stmts[n] {
        let then_is_cont = |s: &Stmt| {
            matches!(s, Stmt::Continue(None))
                || matches!(s, Stmt::Block(v) if v.len() == 1 && matches!(v[0], Stmt::Continue(None)))
        };
        if then_is_cont(then_stmt) && else_stmt.is_none() {
            let c = cond.clone();
            stmts.pop();
            return Some((stmts, c));
        }
        if else_stmt.as_ref().map(|e| then_is_cont(e)).unwrap_or(false)
            && (matches!(&**then_stmt, Stmt::Block(v) if v.is_empty()))
        {
            let c = negate(cond.clone());
            stmts.pop();
            return Some((stmts, c));
        }
    }
    None
}

/// If the body ends with `if (c) continue;` (Continue(None), no else),
/// strip it and return (body without trailing if, c).
#[allow(dead_code)]
fn extract_trailing_continue_if(body: &Stmt) -> Option<(Vec<Stmt>, Expr)> {
    let mut stmts = match body {
        Stmt::Block(v) => v.clone(),
        other => vec![other.clone()],
    };
    if stmts.is_empty() {
        return None;
    }
    let n = stmts.len() - 1;
    // Direct trailing `if (c) continue;`.
    let is_direct = match &stmts[n] {
        Stmt::If { then_stmt, else_stmt: None, .. } => {
            matches!(&**then_stmt, Stmt::Continue(None))
                || matches!(&**then_stmt, Stmt::Block(tb) if tb.len() == 1 && matches!(tb[0], Stmt::Continue(None)))
        }
        _ => false,
    };
    if is_direct {
        if let Stmt::If { cond, .. } = stmts.pop().unwrap() {
            return Some((stmts, cond));
        }
    }
    // Descend into a trailing block.
    if matches!(stmts.last(), Some(Stmt::Block(_))) {
        let last = stmts.pop().unwrap();
        if let Some((inner, c)) = extract_trailing_continue_if(&last) {
            if !inner.is_empty() {
                stmts.push(Stmt::Block(inner));
            }
            return Some((stmts, c));
        } else {
            stmts.push(last);
        }
    }
    None
}

/// Separate the first Basic block's statements from the rest of a body.
/// (Bodies built by `walk` start with the header's statements.)
#[allow(dead_code)]
fn split_first_block(body: Stmt) -> (Stmt, Option<usize>) {
    // The body is whatever the walk produced; we keep it intact — header
    // statements were already woven in by conv(Basic). Return as-is.
    (body, None)
}

fn stmt_to_vec(s: Stmt) -> Vec<Stmt> {
    match s {
        Stmt::Block(v) => v,
        other => vec![other],
    }
}
