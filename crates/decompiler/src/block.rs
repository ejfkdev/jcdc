//! Basic block splitting and control flow graph construction.

use jcdc_classfile::{decode_all, Instruction, Opcode};
use jcdc_jvm::PoolClass;

#[derive(Debug, Clone)]
pub struct Block {
    pub id: usize,
    /// First pc (inclusive).
    pub start: u16,
    /// End pc (exclusive).
    pub end: u16,
    pub ins: Vec<Instruction>,
    /// Successor block ids. For a conditional jump: [fallthrough, taken]
    /// (structurer may reorder based on the condition polarity).
    pub succ: Vec<usize>,
    pub pred: Vec<usize>,
    /// Exception table entries whose handler is this block.
    pub handlers: Vec<usize>,
}

impl Block {
    pub fn last(&self) -> Option<&Instruction> {
        self.ins.last()
    }

    /// True if the block ends with a conditional jump (two successors).
    pub fn ends_cond(&self) -> bool {
        matches!(self.succ.len(), 2)
    }

    pub fn is_exit(&self) -> bool {
        self.succ.is_empty()
    }
}

#[derive(Debug, Clone)]
pub struct ExcEdge {
    /// Index into `Cfg::exc_ranges`.
    pub range: usize,
    pub from: usize,
    pub to: usize,
}

#[derive(Debug, Clone)]
pub struct ExcRange {
    pub start: u16,
    pub end: u16,
    pub handler: u16,
    /// None = catch-all (finally).
    pub catch_type: Option<String>,
}

pub struct Cfg {
    pub blocks: Vec<Block>,
    pub entry: usize,
    pub exc_edges: Vec<ExcEdge>,
    pub exc_ranges: Vec<ExcRange>,
    /// Sorted block start pcs for binary search.
    starts: Vec<u16>,
}

impl Cfg {
    /// Build the CFG for one method body.
    pub fn build(pc: &PoolClass, code: &[u8], exception_table: &[(u16, u16, u16, u16)]) -> Cfg {
        let all = decode_all(code);
        let code_len = code.len() as u16;

        // 1. Collect leaders.
        let mut leaders: Vec<u16> = vec![0];
        for ins in &all {
            let next = ins.pc.saturating_add(ins.size);
            // Only jumps create a fallthrough leader (the instruction after
            // the jump is a possible branch target from elsewhere). Ordinary
            // instructions just continue their block.
            if ins.op.is_jump() && next <= code_len {
                leaders.push(next);
            }
            for t in ins.targets() {
                leaders.push(t);
            }
        }
        let mut ranges = Vec::new();
        for (i, (s, e, h, c)) in exception_table.iter().enumerate() {
            let _ = i;
            leaders.push(*s);
            if *e < code_len {
                leaders.push(*e);
            }
            leaders.push(*h);
            let catch = if *c == 0 {
                None
            } else {
                pc.class_name(*c).map(|s| s.to_string())
            };
            ranges.push(ExcRange { start: *s, end: *e, handler: *h, catch_type: catch });
        }
        leaders.retain(|&l| l < code_len || (l == 0 && code_len == 0));
        leaders.sort_unstable();
        leaders.dedup();
        if leaders.is_empty() {
            leaders.push(0);
        }

        // 2. Map pc -> block id.
        let block_of_pc = |p: u16| -> Option<usize> {
            // last leader <= p
            let i = leaders.partition_point(|&l| l <= p);
            if i == 0 {
                None
            } else {
                Some(i - 1)
            }
        };

        // 3. Create blocks with their instruction slices.
        let mut blocks: Vec<Block> = Vec::with_capacity(leaders.len());
        for (id, &start) in leaders.iter().enumerate() {
            let end = leaders.get(id + 1).copied().unwrap_or(code_len).max(start);
            let ins: Vec<Instruction> = all
                .iter()
                .filter(|i| i.pc >= start && (i.pc as u32 + i.size as u32) <= end as u32)
                .cloned()
                .collect();
            blocks.push(Block {
                id,
                start,
                end,
                ins,
                succ: Vec::new(),
                pred: Vec::new(),
                handlers: Vec::new(),
            });
        }

        // 4. Successors.
        for b in blocks.iter_mut() {
            let Some(last) = b.ins.last() else { continue };
            match last.op {
                Opcode::Goto | Opcode::GotoW => {
                    if let Some(t) = block_of_pc(last.a as u16) {
                        b.succ.push(t);
                    }
                }
                Opcode::Jsr | Opcode::JsrW => {
                    // jsr: falls into subroutine at target, returns after.
                    // Treat target as the only successor; ret handled in builder.
                    if let Some(t) = block_of_pc(last.a as u16) {
                        b.succ.push(t);
                    }
                }
                Opcode::Tableswitch | Opcode::Lookupswitch => {
                    // Order: [fallthrough? no] — default first, then targets in key order.
                    for t in last.targets() {
                        if let Some(tb) = block_of_pc(t) {
                            if !b.succ.contains(&tb) {
                                b.succ.push(tb);
                            }
                        }
                    }
                }
                Opcode::Ret => {}
                o if o.is_terminal() => {} // return / athrow: no successors
                _ => {
                    // Conditional jump or fallthrough.
                    let next_pc = last.pc + last.size;
                    if last.op.is_jump() {
                        if let Some(f) = block_of_pc(next_pc) {
                            b.succ.push(f);
                        }
                        if let Some(t) = block_of_pc(last.a as u16) {
                            b.succ.push(t);
                        }
                    } else if let Some(f) = block_of_pc(next_pc) {
                        b.succ.push(f);
                    }
                }
            }
        }
        // dedupe succ (e.g. both branches to same block)
        for b in blocks.iter_mut() {
            let mut seen = Vec::new();
            b.succ.retain(|s| {
                if seen.contains(s) {
                    false
                } else {
                    seen.push(*s);
                    true
                }
            });
        }

        // 5. Predecessors + handler back-references.
        for b in 0..blocks.len() {
            for &s in &blocks[b].succ.clone() {
                blocks[s].pred.push(b);
            }
        }
        let mut exc_edges = Vec::new();
        for (ri, r) in ranges.iter().enumerate() {
            let hb = block_of_pc(r.handler);
            if let Some(h) = hb {
                blocks[h].handlers.push(ri);
            }
            for b in &blocks {
                // Overlap semantics: a block is protected when its FIRST
                // instruction lies inside [start, end). Range boundaries are
                // always block leaders, so this never splits a block. Using
                // `b.start < r.end` (rather than `b.end <= r.end`) keeps
                // protected blocks whose trailing return/throw sits exactly at
                // the range boundary — e.g. `try { return f(); } catch ..`,
                // where the invokestatic is protected but the areturn lands at
                // r.end. Those blocks can still reach the loop header through
                // the handler, which loop membership must see.
                if b.start >= r.start && b.start < r.end && !b.ins.is_empty() {
                    if let Some(h) = hb {
                        exc_edges.push(ExcEdge { range: ri, from: b.id, to: h });
                    }
                }
            }
        }

        Cfg {
            blocks,
            entry: 0,
            exc_edges,
            exc_ranges: ranges,
            starts: leaders,
        }
    }

    /// Block containing a pc.
    pub fn block_at(&self, p: u16) -> Option<usize> {
        let i = self.starts.partition_point(|&l| l <= p);
        if i == 0 {
            None
        } else {
            Some(i - 1)
        }
    }

    /// Number of blocks.
    pub fn len(&self) -> usize {
        self.blocks.len()
    }

    pub fn is_empty(&self) -> bool {
        self.blocks.is_empty()
    }
}

impl Cfg {
    /// The machine-neutral view of this graph, for the shared structurer /
    /// converter (`jdc-core`). Block ids are preserved, so the two views are
    /// index-compatible and `BlockResult`s apply to both.
    pub fn to_core(&self) -> jdc_core::cfg::Cfg {
        if crate::dbg_flag!("JCDC_DBG_CFG") {
            for b in &self.blocks {
                eprintln!(
                    "JVM_CFG b={} start={} end={} ins={} succ={:?} pred={:?} handlers={:?}",
                    b.id, b.start, b.end, b.ins.len(), b.succ, b.pred, b.handlers
                );
            }
            for (i, r) in self.exc_ranges.iter().enumerate() {
                eprintln!("JVM_EXC r={} {}..{} -> {} type={:?}", i, r.start, r.end, r.handler, r.catch_type);
            }
            for e in &self.exc_edges {
                eprintln!("JVM_EDGE r={} from={} to={}", e.range, e.from, e.to);
            }
        }
        let blocks = self
            .blocks
            .iter()
            .map(|b| jdc_core::cfg::Block {
                id: b.id,
                start: b.start as u32,
                end: b.end as u32,
                ins_len: b.ins.len() as u32,
                succ: b.succ.clone(),
                pred: b.pred.clone(),
                handlers: b.handlers.iter().map(|&h| h as u32).collect(),
            })
            .collect();
        let ranges = self
            .exc_ranges
            .iter()
            .map(|r| jdc_core::cfg::ExcRange {
                start: r.start as u32,
                end: r.end as u32,
                handler: r.handler as u32,
                catch_type: r.catch_type.clone(),
            })
            .collect();
        let mut core = jdc_core::cfg::Cfg::from_blocks(blocks, self.entry, ranges);
        // The view must be EXACTLY this graph's — including predecessor and
        // handler lists as this Cfg has them. Passes mutate successors
        // (`short_circuit_prefold` rewires a folded branch) without updating
        // preds, and the structurer was calibrated against those lists, so
        // recomputing them here would change structuring decisions.
        for (cb, jb) in core.blocks.iter_mut().zip(self.blocks.iter()) {
            cb.pred = jb.pred.clone();
            cb.handlers = jb.handlers.iter().map(|&h| h as u32).collect();
        }
        core.exc_edges = self
            .exc_edges
            .iter()
            .map(|e| jdc_core::cfg::ExcEdge { range: e.range, from: e.from, to: e.to })
            .collect();
        core
    }
}
