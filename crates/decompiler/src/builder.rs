//! Bytecode → expression/statement building via per-block stack simulation.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use jcdc_classfile::{
    parse_specialized_attribute, ConstantPoolEntry, Instruction, Opcode, ParsedAttribute, SwitchData,
};
use jcdc_jvm::{parse_method_descriptor, ClassPool, JavaType, MethodDescriptor, PoolClass};

use crate::expr::{AssignOp, BinOp, ConcatPart, ConstVal, Expr, LambdaExpr, LambdaKind, TypeRef, UnOp};
use crate::stmt::Stmt;
use crate::varalloc::{code_attribute, VarTable};

thread_local! {
    /// Depths of ORIGINAL entries duplicated by a plain `dup` within the
    /// current basic block: a later store popping the clone is an inline
    /// `x = e` embedded in a larger expression; a popped
    /// `Objects.requireNonNull(clone)` over a survivor is javac's implicit
    /// null check (no source statement). Cleared on every pop at/above the
    /// depth and at each block start — stale marks would swallow unrelated
    /// stores.
    static DUP_MARKS: std::cell::RefCell<HashSet<usize>> =
        std::cell::RefCell::new(HashSet::new());
}

fn dup_marks_clear_at_or_above(depth: usize) {
    DUP_MARKS.with(|m| m.borrow_mut().retain(|&d| d < depth));
}

/// How a basic block ends.
#[derive(Debug, Clone)]
pub enum Term {
    Fallthrough,
    Goto,
    /// Jumps to succ[1] when `cond` is true; falls through to succ[0].
    Cond { cond: Expr },
    Switch { selector: Expr, targets: SwitchTargets },
    Return(Option<Expr>),
    Throw(Expr),
    Jsr,
    Ret,
}

#[derive(Debug, Clone)]
pub enum SwitchTargets {
    /// pc targets indexed by (key - low).
    Table { low: i32, targets: Vec<u16> },
    /// (match value, pc target) pairs.
    Lookup { pairs: Vec<(i32, u16)> },
}

#[derive(Debug, Clone)]
pub struct BlockResult {
    pub stmts: Vec<Stmt>,
    /// Operand stack contents at block exit (usually empty).
    pub out_stack: Vec<Expr>,
    pub term: Term,
}

#[derive(Debug)]
pub struct BuildError(pub String);

type BResult<T> = Result<T, BuildError>;

pub struct Builder<'a> {
    pub pc: &'a PoolClass,
    pub pool: &'a ClassPool,
    pub vt: &'a VarTable,
    pub desc: &'a MethodDescriptor,
    pub is_static: bool,
    /// Variables already declared (LocalDef emitted) in this method.
    declared: RefCell<Vec<u32>>,
    /// Pending array initializers keyed by (element type descriptor, dims
    /// literal string). Stores append values; uses materialize `new T[]{...}`.
    pub arrays: RefCell<HashMap<ArrayKey, Vec<Expr>>>,
}

/// Identity key for a freshly created array expression.
pub type ArrayKey = (String, String);

/// Structural key of an array expression if it is a foldable fresh array.
#[allow(dead_code)]
fn array_key(e: &Expr) -> Option<ArrayKey> {
    match e {
        Expr::NewArray { elem, dims, trailing_dims: 0, init: None } => {
            array_key_of(elem, dims, 0)
        }
        _ => None,
    }
}

fn array_key_of(elem: &TypeRef, dims: &[Expr], trailing_dims: u8) -> Option<ArrayKey> {
    if trailing_dims != 0 {
        return None;
    }
    let dl: Vec<String> = dims
        .iter()
        .map(|d| match d {
            Expr::Const(ConstVal::Int(i)) => i.to_string(),
            _ => "?".to_string(),
        })
        .collect();
    if dl.iter().any(|x| x == "?") {
        return None;
    }
    Some((elem.erased().to_descriptor(), dl.join(",")))
}

impl<'a> Builder<'a> {
    pub fn new(
        pc: &'a PoolClass,
        pool: &'a ClassPool,
        vt: &'a VarTable,
        desc: &'a MethodDescriptor,
        is_static: bool,
    ) -> Self {
        Builder {
            pc,
            pool,
            vt,
            desc,
            is_static,
            declared: RefCell::new(Vec::new()),
            arrays: RefCell::new(HashMap::new()),
        }
    }

    /// Build statements for one basic block, starting from `initial_stack`
    /// (the operand stack state at block entry, propagated from
    /// predecessors).
    pub fn build_block(&self, ins: &[Instruction], initial_stack: Vec<Expr>) -> BResult<BlockResult> {
        let mut stack: Vec<Expr> = initial_stack;
        DUP_MARKS.with(|m| m.borrow_mut().clear());
        let mut stmts: Vec<Stmt> = Vec::new();
        let mut term = Term::Fallthrough;

        let mut i = 0usize;
        while i < ins.len() {
            let in0 = ins[i].clone();
            i += 1;
            let op = in0.op;
            let next_pc = in0.pc + in0.size;
            match op {
                Opcode::Nop => {}

                // ---- constants ----
                Opcode::AconstNull => stack.push(Expr::Const(ConstVal::Null)),
                Opcode::IconstM1 => stack.push(int_const(-1)),
                Opcode::Iconst0 => stack.push(int_const(0)),
                Opcode::Iconst1 => stack.push(int_const(1)),
                Opcode::Iconst2 => stack.push(int_const(2)),
                Opcode::Iconst3 => stack.push(int_const(3)),
                Opcode::Iconst4 => stack.push(int_const(4)),
                Opcode::Iconst5 => stack.push(int_const(5)),
                Opcode::Lconst0 => stack.push(Expr::Const(ConstVal::Long(0))),
                Opcode::Lconst1 => stack.push(Expr::Const(ConstVal::Long(1))),
                Opcode::Fconst0 => stack.push(Expr::Const(ConstVal::Float(0.0))),
                Opcode::Fconst1 => stack.push(Expr::Const(ConstVal::Float(1.0))),
                Opcode::Fconst2 => stack.push(Expr::Const(ConstVal::Float(2.0))),
                Opcode::Dconst0 => stack.push(Expr::Const(ConstVal::Double(0.0))),
                Opcode::Dconst1 => stack.push(Expr::Const(ConstVal::Double(1.0))),
                Opcode::Bipush | Opcode::Sipush => stack.push(int_const(in0.a)),
                Opcode::Ldc => self.ldc(&mut stack, in0.a as u16)?,
                Opcode::LdcW => self.ldc(&mut stack, in0.a as u16)?,
                Opcode::Ldc2W => self.ldc2w(&mut stack, in0.a as u16)?,

                // ---- loads ----
                Opcode::Iload | Opcode::Lload | Opcode::Fload | Opcode::Dload | Opcode::Aload => {
                    let e = self.load(in0.a as u16, in0.pc)?;
                    stack.push(e);
                }
                Opcode::Iload0 | Opcode::Iload1 | Opcode::Iload2 | Opcode::Iload3 => {
                    let slot = (op as u8 - Opcode::Iload0 as u8) as u16;
                    stack.push(self.load(slot, in0.pc)?);
                }
                Opcode::Lload0 | Opcode::Lload1 | Opcode::Lload2 | Opcode::Lload3 => {
                    let slot = (op as u8 - Opcode::Lload0 as u8) as u16;
                    stack.push(self.load(slot, in0.pc)?);
                }
                Opcode::Fload0 | Opcode::Fload1 | Opcode::Fload2 | Opcode::Fload3 => {
                    let slot = (op as u8 - Opcode::Fload0 as u8) as u16;
                    stack.push(self.load(slot, in0.pc)?);
                }
                Opcode::Dload0 | Opcode::Dload1 | Opcode::Dload2 | Opcode::Dload3 => {
                    let slot = (op as u8 - Opcode::Dload0 as u8) as u16;
                    stack.push(self.load(slot, in0.pc)?);
                }
                Opcode::Aload0 | Opcode::Aload1 | Opcode::Aload2 | Opcode::Aload3 => {
                    let slot = (op as u8 - Opcode::Aload0 as u8) as u16;
                    stack.push(self.load(slot, in0.pc)?);
                }

                // ---- array loads ----
                Opcode::Iaload | Opcode::Laload | Opcode::Faload | Opcode::Daload
                | Opcode::Aaload | Opcode::Baload | Opcode::Caload | Opcode::Saload => {
                    let idx = pop(&mut stack)?;
                    let arr = pop(&mut stack)?;
                    stack.push(Expr::ArrayIndex { array: Box::new(arr), index: Box::new(idx) });
                }

                // ---- stores ----
                Opcode::Istore | Opcode::Lstore | Opcode::Fstore | Opcode::Dstore | Opcode::Astore => {
                    let slot = in0.a as u16;
                    let val = pop(&mut stack)?;
                    // `dup; astore N; monitorenter`: synchronized
                    // scaffolding holding the monitor for the exit paths —
                    // the structured Synchronized stmt owns the lock expr.
                    // Keeping it leaked a dead `varN_pc = monitor` stmt
                    // typed from the local the slot is later reused for
                    // (jdk11 SecurityManager String[] var = lockObj,
                    // KeepAliveCache Iterator var = this,
                    // AbstractSelectableChannel SelectionKey[] var =
                    // keyLock — X无法转换为Y x3).
                    if matches!(op, Opcode::Astore)
                        && matches!(ins.get(i).map(|x| x.op), Some(Opcode::Monitorenter))
                    {
                        continue;
                    }
                    match self.inline_dup_store(&mut stack, slot, in0.pc, next_pc, val) {
                        Some(left) => self.store(&mut stmts, slot, in0.pc, next_pc, left)?,
                        None => {}
                    }
                }
                Opcode::Istore0 | Opcode::Istore1 | Opcode::Istore2 | Opcode::Istore3 => {
                    let slot = (op as u8 - Opcode::Istore0 as u8) as u16;
                    let val = pop(&mut stack)?;
                    match self.inline_dup_store(&mut stack, slot, in0.pc, next_pc, val) {
                        Some(left) => self.store(&mut stmts, slot, in0.pc, next_pc, left)?,
                        None => {}
                    }
                }
                Opcode::Lstore0 | Opcode::Lstore1 | Opcode::Lstore2 | Opcode::Lstore3 => {
                    let slot = (op as u8 - Opcode::Lstore0 as u8) as u16;
                    let val = pop(&mut stack)?;
                    match self.inline_dup_store(&mut stack, slot, in0.pc, next_pc, val) {
                        Some(left) => self.store(&mut stmts, slot, in0.pc, next_pc, left)?,
                        None => {}
                    }
                }
                Opcode::Fstore0 | Opcode::Fstore1 | Opcode::Fstore2 | Opcode::Fstore3 => {
                    let slot = (op as u8 - Opcode::Fstore0 as u8) as u16;
                    let val = pop(&mut stack)?;
                    match self.inline_dup_store(&mut stack, slot, in0.pc, next_pc, val) {
                        Some(left) => self.store(&mut stmts, slot, in0.pc, next_pc, left)?,
                        None => {}
                    }
                }
                Opcode::Dstore0 | Opcode::Dstore1 | Opcode::Dstore2 | Opcode::Dstore3 => {
                    let slot = (op as u8 - Opcode::Dstore0 as u8) as u16;
                    let val = pop(&mut stack)?;
                    match self.inline_dup_store(&mut stack, slot, in0.pc, next_pc, val) {
                        Some(left) => self.store(&mut stmts, slot, in0.pc, next_pc, left)?,
                        None => {}
                    }
                }
                Opcode::Astore0 | Opcode::Astore1 | Opcode::Astore2 | Opcode::Astore3 => {
                    let slot = (op as u8 - Opcode::Astore0 as u8) as u16;
                    let val = pop(&mut stack)?;
                    // synchronized scaffolding (see the wide Astore arm).
                    if matches!(ins.get(i).map(|x| x.op), Some(Opcode::Monitorenter)) {
                        continue;
                    }
                    match self.inline_dup_store(&mut stack, slot, in0.pc, next_pc, val) {
                        Some(left) => self.store(&mut stmts, slot, in0.pc, next_pc, left)?,
                        None => {}
                    }
                }

                // ---- array stores ----
                Opcode::Iastore | Opcode::Lastore | Opcode::Fastore | Opcode::Dastore
                | Opcode::Aastore | Opcode::Bastore | Opcode::Castore | Opcode::Sastore => {
                    // Stack order: [arrayref, index, value] (value on top).
                    let val = pop(&mut stack)?;
                    let idx = pop(&mut stack)?;
                    let arr = pop(&mut stack)?;
                    // Array-initializer folding: javac emits
                    // `new T[n]; dup; <idx>; <val>; <store>` per element. The
                    // popped `arr` is the dup twin; fold the store into the
                    // structurally-equal fresh NewArray still on the operand
                    // stack. Identity is unambiguous this way — no global
                    // side table keyed by shape.
                    let mut folded = false;
                    if let Expr::Const(ConstVal::Int(i)) = &idx {
                        // The popped dup twin may already carry folded
                        // values (each `dup` clones the partially-filled
                        // expression), so freshness is judged on shape only.
                        if matches!(&arr, Expr::NewArray { .. }) {
                            if let Some(slot) = stack.iter_mut().rev().find(|e| {
                                match (&**e, &arr) {
                                    (
                                        Expr::NewArray { elem: e1, dims: d1, trailing_dims: t1, .. },
                                        Expr::NewArray { elem: e2, dims: d2, trailing_dims: t2, .. },
                                    ) => t1 == t2 && e1 == e2 && d1 == d2,
                                    _ => false,
                                }
                            }) {
                                if let Expr::NewArray { dims, init, .. } = slot {
                                    let cap = match dims.first() {
                                        Some(Expr::Const(ConstVal::Int(c))) => *c as usize,
                                        _ => usize::MAX,
                                    };
                                    let vals = init.get_or_insert_with(Vec::new);
                                    if *i as usize == vals.len()
                                        && vals.len() < cap
                                        && vals.len() < 65536
                                    {
                                        vals.push(val.clone());
                                        folded = true;
                                    }
                                }
                            }
                        }
                    }
                    if folded {
                        continue;
                    }
                    let target = Expr::ArrayIndex { array: Box::new(arr), index: Box::new(idx) };
                    stmts.push(Stmt::ExprStmt(Expr::Assign {
                        target: Box::new(target),
                        op: AssignOp::Plain,
                        value: Box::new(val),
                    }));
                }

// ---- stack ops ----
                Opcode::Pop => {
                    let v = pop(&mut stack)?;
                    // `dup; invokestatic Objects.requireNonNull; pop` over a
                    // surviving value is javac's implicit null check (jdk21+
                    // inner-ctor outer params, record components): no source
                    // statement. Emitting it inside a ctor lands BEFORE
                    // super()/this() ("对 this 的引用只能在显式调用构造器后
                    // 出现", jdk26 ClassSpecializer$Factory$1$1Var). An
                    // EXPLICIT requireNonNull statement has no dup survivor
                    // and keeps its ExprStmt.
                    let implicit_check = matches!(&v, Expr::Method { cls, name, .. }
                        if name == "requireNonNull" && cls == "java/util/Objects")
                        && !stack.is_empty()
                        && DUP_MARKS.with(|m| m.borrow().contains(&(stack.len() - 1)));
                    if !implicit_check && has_side_effects(&v) {
                        stmts.push(Stmt::ExprStmt(v));
                    }
                }
                Opcode::Pop2 => {
                    if let Some(top) = stack.last() {
                        if top.type_ref().is_wide() {
                            let v = stack.pop().unwrap();
                            dup_marks_clear_at_or_above(stack.len());
                            if has_side_effects(&v) {
                                stmts.push(Stmt::ExprStmt(v));
                            }
                        } else {
                            let v1 = stack.pop().unwrap();
                            dup_marks_clear_at_or_above(stack.len());
                            let v2 = pop(&mut stack)?;
                            // push order: v2 was below v1
                            if has_side_effects(&v2) {
                                stmts.push(Stmt::ExprStmt(v2));
                            }
                            if has_side_effects(&v1) {
                                stmts.push(Stmt::ExprStmt(v1));
                            }
                        }
                    }
                }
                Opcode::Dup => {
                    // Post-increment idioms where the dup'd value is the
                    // expression result (old value):
                    //   dup; <load x>; iconst_1; iadd; <store x>
                    //   dup (top = x); <const K>; iadd; <store x>
                    if let Some(inc_len) = self.postinc_ahead(ins, i) {
                        for k in 0..inc_len {
                            let step = ins[i + k].clone();
                            self.exec_postinc_step(&mut stack, &mut stmts, &step)?;
                        }
                        i += inc_len;
                    } else if let Some(k) = self.dup_add_store_ahead(ins, i, &stack) {
                        let (len, delta) = k;
                        let top = stack.pop().ok_or_else(|| BuildError("dup empty".into()))?;
                        dup_marks_clear_at_or_above(stack.len());
                        // consume the const/add/store instructions directly
                        // (they are fully described by the post-inc form)
                        let _ = &ins[i..i + len];
                        stack.push(Expr::PostIncDec { e: Box::new(top), delta, wide: false });
                        i += len;
                    } else {
                        let v = stack.last().cloned().ok_or_else(|| BuildError("dup on empty".into()))?;
                        let orig_depth = stack.len() - 1;
                        DUP_MARKS.with(|m| m.borrow_mut().insert(orig_depth));
                        stack.push(v);
                    }
                }
                Opcode::DupX1 => {
                    let a = pop(&mut stack)?;
                    let b = pop(&mut stack)?;
                    stack.push(a.clone());
                    stack.push(b);
                    stack.push(a);
                }
                Opcode::DupX2 => {
                    // form1 (3x cat1): v3 v2 v1 -> v1 v3 v2 v1
                    // form2 (v2 wide): v2 v1 -> v1 v2 v1
                    let v1 = pop(&mut stack)?;
                    if stack.last().map(|t| t.type_ref().is_wide()).unwrap_or(false) {
                        let v2 = pop(&mut stack)?;
                        stack.push(v1.clone());
                        stack.push(v2);
                        stack.push(v1);
                    } else {
                        let v2 = pop(&mut stack)?;
                        let v3 = pop(&mut stack)?;
                        stack.push(v1.clone());
                        stack.push(v3);
                        stack.push(v2);
                        stack.push(v1);
                    }
                }
                Opcode::Dup2 => {
                    if let Some(top) = stack.last().cloned() {
                        if top.type_ref().is_wide() {
                            stack.push(top);
                        } else {
                            let v2 = stack.pop().unwrap();
                            let v1 = stack.last().cloned().ok_or_else(|| BuildError("dup2".into()))?;
                            stack.push(v2.clone());
                            stack.push(v1);
                            stack.push(v2);
                        }
                    }
                }
                Opcode::Dup2X1 => {
                    let v1 = pop(&mut stack)?;
                    let v2 = pop(&mut stack)?;
                    if v1.type_ref().is_wide() {
                        stack.push(v1.clone());
                        stack.push(v2);
                        stack.push(v1);
                    } else {
                        let v3 = pop(&mut stack)?;
                        stack.push(v2.clone());
                        stack.push(v1.clone());
                        stack.push(v3);
                        stack.push(v2);
                        stack.push(v1);
                    }
                }
                Opcode::Dup2X2 => {
                    let v1 = pop(&mut stack)?;
                    if v1.type_ref().is_wide() {
                        let v2 = pop(&mut stack)?;
                        if v2.type_ref().is_wide() {
                            stack.push(v1.clone());
                            stack.push(v2);
                            stack.push(v1);
                        } else {
                            let v3 = pop(&mut stack)?;
                            stack.push(v1.clone());
                            stack.push(v3);
                            stack.push(v2);
                            stack.push(v1);
                        }
                    } else {
                        let v2 = pop(&mut stack)?;
                        if v2.type_ref().is_wide() {
                            let v3 = pop(&mut stack)?;
                            stack.push(v2.clone());
                            stack.push(v1.clone());
                            stack.push(v3);
                            stack.push(v2);
                            stack.push(v1);
                        } else {
                            let v3 = pop(&mut stack)?;
                            let v4 = pop(&mut stack)?;
                            stack.push(v2.clone());
                            stack.push(v1.clone());
                            stack.push(v4);
                            stack.push(v3);
                            stack.push(v2);
                            stack.push(v1);
                        }
                    }
                }
                Opcode::Swap => {
                    let a = pop(&mut stack)?;
                    let b = pop(&mut stack)?;
                    stack.push(a);
                    stack.push(b);
                }

                // ---- arithmetic ----
                Opcode::Iadd => self.arith(&mut stack, BinOp::Add, JavaType::Int)?,
                Opcode::Ladd => self.arith(&mut stack, BinOp::Add, JavaType::Long)?,
                Opcode::Fadd => self.arith(&mut stack, BinOp::Add, JavaType::Float)?,
                Opcode::Dadd => self.arith(&mut stack, BinOp::Add, JavaType::Double)?,
                Opcode::Isub => self.arith(&mut stack, BinOp::Sub, JavaType::Int)?,
                Opcode::Lsub => self.arith(&mut stack, BinOp::Sub, JavaType::Long)?,
                Opcode::Fsub => self.arith(&mut stack, BinOp::Sub, JavaType::Float)?,
                Opcode::Dsub => self.arith(&mut stack, BinOp::Sub, JavaType::Double)?,
                Opcode::Imul => self.arith(&mut stack, BinOp::Mul, JavaType::Int)?,
                Opcode::Lmul => self.arith(&mut stack, BinOp::Mul, JavaType::Long)?,
                Opcode::Fmul => self.arith(&mut stack, BinOp::Mul, JavaType::Float)?,
                Opcode::Dmul => self.arith(&mut stack, BinOp::Mul, JavaType::Double)?,
                Opcode::Idiv => self.arith(&mut stack, BinOp::Div, JavaType::Int)?,
                Opcode::Ldiv => self.arith(&mut stack, BinOp::Div, JavaType::Long)?,
                Opcode::Fdiv => self.arith(&mut stack, BinOp::Div, JavaType::Float)?,
                Opcode::Ddiv => self.arith(&mut stack, BinOp::Div, JavaType::Double)?,
                Opcode::Irem => self.arith(&mut stack, BinOp::Rem, JavaType::Int)?,
                Opcode::Lrem => self.arith(&mut stack, BinOp::Rem, JavaType::Long)?,
                Opcode::Frem => self.arith(&mut stack, BinOp::Rem, JavaType::Float)?,
                Opcode::Drem => self.arith(&mut stack, BinOp::Rem, JavaType::Double)?,
                Opcode::Ineg => self.neg(&mut stack, JavaType::Int)?,
                Opcode::Lneg => self.neg(&mut stack, JavaType::Long)?,
                Opcode::Fneg => self.neg(&mut stack, JavaType::Float)?,
                Opcode::Dneg => self.neg(&mut stack, JavaType::Double)?,
                Opcode::Ishl => self.arith(&mut stack, BinOp::Shl, JavaType::Int)?,
                Opcode::Lshl => self.arith(&mut stack, BinOp::Shl, JavaType::Long)?,
                Opcode::Ishr => self.arith(&mut stack, BinOp::Shr, JavaType::Int)?,
                Opcode::Lshr => self.arith(&mut stack, BinOp::Shr, JavaType::Long)?,
                Opcode::Iushr => self.arith(&mut stack, BinOp::Ushr, JavaType::Int)?,
                Opcode::Lushr => self.arith(&mut stack, BinOp::Ushr, JavaType::Long)?,
                Opcode::Iand => self.arith(&mut stack, BinOp::And, JavaType::Int)?,
                Opcode::Land => self.arith(&mut stack, BinOp::And, JavaType::Long)?,
                Opcode::Ior => self.arith(&mut stack, BinOp::Or, JavaType::Int)?,
                Opcode::Lor => self.arith(&mut stack, BinOp::Or, JavaType::Long)?,
                Opcode::Ixor => self.arith(&mut stack, BinOp::Xor, JavaType::Int)?,
                Opcode::Lxor => self.arith(&mut stack, BinOp::Xor, JavaType::Long)?,

                Opcode::Iinc => {
                    let v = self.var_at(in0.a as u16, in0.pc)?;
                    let delta = in0.b as i64;
                    // `iload v; iinc v,d; ...` — the loaded snapshot on the
                    // stack denotes the OLD value; fold the increment into a
                    // post-increment expression at that stack position.
                    let snapshot = stack.iter().rposition(|e| {
                        matches!(e, Expr::Local { var, .. } if *var == v)
                    });
                    if let Some(pos) = snapshot {
                        stack[pos] = Expr::PostIncDec {
                            e: Box::new(self.local_expr(v)),
                            delta,
                            wide: false,
                        };
                    } else {
                        // `iinc v,d; iload v` — pre-increment idiom: the
                        // load reads the incremented value; fold both into
                        // a pre-increment expression pushed on the stack.
                        let slot = self.vt.var(v).slot;
                        let next_load_same = match ins.get(i) {
                            Some(nx) => {
                                let ls = match nx.op {
                                    Opcode::Iload => Some(nx.a as u16),
                                    Opcode::Iload0 => Some(0),
                                    Opcode::Iload1 => Some(1),
                                    Opcode::Iload2 => Some(2),
                                    Opcode::Iload3 => Some(3),
                                    _ => None,
                                };
                                ls == Some(slot)
                            }
                            None => false,
                        };
                        let target = self.local_expr(v);
                        if next_load_same && (delta == 1 || delta == -1) {
                            stack.push(Expr::PreIncDec { e: Box::new(target), delta, wide: false });
                            // skip the folded load (`i` already points at it)
                            i += 1;
                        } else if delta == 1 || delta == -1 {
                            stmts.push(Stmt::ExprStmt(Expr::PreIncDec { e: Box::new(target), delta, wide: false }));
                        } else {
                            stmts.push(Stmt::ExprStmt(Expr::Assign {
                                target: Box::new(target),
                                op: AssignOp::Add,
                                value: Box::new(int_const(delta as i32)),
                            }));
                        }
                    }
                }

                // ---- conversions ----
                Opcode::I2l => self.convert(&mut stack, JavaType::Long)?,
                Opcode::I2f => self.convert(&mut stack, JavaType::Float)?,
                Opcode::I2d => self.convert(&mut stack, JavaType::Double)?,
                Opcode::L2i => self.convert(&mut stack, JavaType::Int)?,
                Opcode::L2f => self.convert(&mut stack, JavaType::Float)?,
                Opcode::L2d => self.convert(&mut stack, JavaType::Double)?,
                Opcode::F2i => self.convert(&mut stack, JavaType::Int)?,
                Opcode::F2l => self.convert(&mut stack, JavaType::Long)?,
                Opcode::F2d => self.convert(&mut stack, JavaType::Double)?,
                Opcode::D2i => self.convert(&mut stack, JavaType::Int)?,
                Opcode::D2l => self.convert(&mut stack, JavaType::Long)?,
                Opcode::D2f => self.convert(&mut stack, JavaType::Float)?,
                Opcode::I2b => self.convert(&mut stack, JavaType::Byte)?,
                Opcode::I2c => self.convert(&mut stack, JavaType::Char)?,
                Opcode::I2s => self.convert(&mut stack, JavaType::Short)?,

                // ---- comparisons feeding branches ----
                Opcode::Lcmp => self.cmp(&mut stack, JavaType::Long)?,
                Opcode::Fcmpl | Opcode::Fcmpg => self.cmp(&mut stack, JavaType::Float)?,
                Opcode::Dcmpl | Opcode::Dcmpg => self.cmp(&mut stack, JavaType::Double)?,

                Opcode::Ifeq | Opcode::IfNe | Opcode::IfLt | Opcode::IfGe | Opcode::IfGt | Opcode::IfLe => {
                    let v = pop(&mut stack)?;
                    let bop = match op {
                        Opcode::Ifeq => BinOp::Eq,
                        Opcode::IfNe => BinOp::Ne,
                        Opcode::IfLt => BinOp::Lt,
                        Opcode::IfGe => BinOp::Ge,
                        Opcode::IfGt => BinOp::Gt,
                        _ => BinOp::Le,
                    };
                    let (l, r, bop) = unfold_cmp(v, bop);
                    term = Term::Cond { cond: Expr::Bin { op: bop, l: Box::new(l), r: Box::new(r), ty: None } };
                }
                Opcode::IfIcmpEq | Opcode::IfIcmpNe | Opcode::IfIcmpLt | Opcode::IfIcmpGe
                | Opcode::IfIcmpGt | Opcode::IfIcmpLe => {
                    let r = pop(&mut stack)?;
                    let l = pop(&mut stack)?;
                    let bop = match op {
                        Opcode::IfIcmpEq => BinOp::Eq,
                        Opcode::IfIcmpNe => BinOp::Ne,
                        Opcode::IfIcmpLt => BinOp::Lt,
                        Opcode::IfIcmpGe => BinOp::Ge,
                        Opcode::IfIcmpGt => BinOp::Gt,
                        _ => BinOp::Le,
                    };
                    term = Term::Cond { cond: Expr::Bin { op: bop, l: Box::new(l), r: Box::new(r), ty: None } };
                }
                Opcode::IfAcmpeq | Opcode::IfAcmpne => {
                    let r = pop(&mut stack)?;
                    let l = pop(&mut stack)?;
                    let bop = if op == Opcode::IfAcmpeq { BinOp::RefEq } else { BinOp::RefNe };
                    term = Term::Cond { cond: Expr::Bin { op: bop, l: Box::new(l), r: Box::new(r), ty: None } };
                }
                Opcode::IfNull | Opcode::IfNonnull => {
                    let v = pop(&mut stack)?;
                    let bop = if op == Opcode::IfNull { BinOp::RefEq } else { BinOp::RefNe };
                    term = Term::Cond {
                        cond: Expr::Bin {
                            op: bop,
                            l: Box::new(v),
                            r: Box::new(Expr::Const(ConstVal::Null)),
                            ty: None,
                        },
                    };
                }

                // ---- jumps ----
                Opcode::Goto | Opcode::GotoW => term = Term::Goto,
                Opcode::Jsr | Opcode::JsrW => term = Term::Jsr,
                Opcode::Ret => term = Term::Ret,
                Opcode::Tableswitch | Opcode::Lookupswitch => {
                    let sel = pop(&mut stack)?;
                    let targets = match in0.switch_data.as_deref() {
                        Some(SwitchData::Table { low, targets, .. }) => {
                            SwitchTargets::Table { low: *low, targets: targets.clone() }
                        }
                        Some(SwitchData::Lookup { pairs, .. }) => {
                            SwitchTargets::Lookup { pairs: pairs.clone() }
                        }
                        _ => return Err(BuildError("switch without data".into())),
                    };
                    term = Term::Switch { selector: sel, targets };
                }

                // ---- returns ----
                Opcode::Ireturn | Opcode::Lreturn | Opcode::Freturn | Opcode::Dreturn | Opcode::Areturn => {
                    let v = pop(&mut stack)?;
                    // `x = e; return x;` (or `return <same expr as last
                    // assign value>`) merges into `return x = e;` so the
                    // value is evaluated exactly once, matching bytecode.
                    let merged = if let Some(Stmt::ExprStmt(Expr::Assign { target, op: AssignOp::Plain, value })) = stmts.last() {
                        if **value == v || **target == v {
                            Some(Expr::Assign { target: target.clone(), op: AssignOp::Plain, value: value.clone() })
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    if let Some(m) = merged {
                        stmts.pop();
                        term = Term::Return(Some(m));
                    } else {
                        term = Term::Return(Some(v));
                    }
                }
                Opcode::Return => term = Term::Return(None),
                Opcode::Athrow => {
                    let v = pop(&mut stack)?;
                    term = Term::Throw(v);
                }

                // ---- fields ----
                Opcode::Getstatic => {
                    let (cls, name, d) = self.member(in0.a as u16)?;
                    let ty = self.field_type(&cls, &name, &d);
                    stack.push(Expr::Field { owner: None, cls, name, ty, is_static: true });
                }
                Opcode::Putstatic => {
                    let val = pop(&mut stack)?;
                    let (cls, name, d) = self.member(in0.a as u16)?;
                    let ty = self.field_type(&cls, &name, &d);
                    let target = Expr::Field { owner: None, cls, name, ty, is_static: true };
                    stmts.push(mk_assign(target, val));
                }
                Opcode::Getfield => {
                    let obj = pop(&mut stack)?;
                    let (cls, name, d) = self.member(in0.a as u16)?;
                    let ty = self.field_type(&cls, &name, &d);
                    let owner = self.owner_expr(obj, &cls);
                    stack.push(Expr::Field { owner, cls, name, ty, is_static: false });
                }
                Opcode::Putfield => {
                    let val = pop(&mut stack)?;
                    let obj = pop(&mut stack)?;
                    let (cls, name, d) = self.member(in0.a as u16)?;
                    let ty = self.field_type(&cls, &name, &d);
                    let owner = self.owner_expr(obj, &cls);
                    let target = Expr::Field { owner, cls, name, ty, is_static: false };
                    stmts.push(mk_assign(target, val));
                }

                // ---- invokes ----
                Opcode::Invokevirtual | Opcode::Invokespecial | Opcode::Invokeinterface | Opcode::Invokestatic => {
                    self.invoke(&mut stack, &mut stmts, op, in0.a as u16)?;
                }
                Opcode::Invokedynamic => {
                    self.invoke_dynamic(&mut stack, &mut stmts, in0.a as u16)?;
                }

                // ---- objects & arrays ----
                Opcode::New => {
                    let cls = self.pc.class_name(in0.a as u16)
                        .ok_or_else(|| BuildError("new: bad cp".into()))?
                        .to_string();
                    let ty = TypeRef::J(JavaType::Object(cls.clone()));
                    stack.push(Expr::New { cls, ty, args: Vec::new(), raw: true });
                }
                Opcode::Newarray => {
                    let n = pop(&mut stack)?;
                    let elem = match in0.a {
                        4 => JavaType::Boolean,
                        5 => JavaType::Char,
                        6 => JavaType::Float,
                        7 => JavaType::Double,
                        8 => JavaType::Byte,
                        9 => JavaType::Short,
                        10 => JavaType::Int,
                        11 => JavaType::Long,
                        _ => return Err(BuildError(format!("newarray bad atype {}", in0.a))),
                    };
                    stack.push(Expr::NewArray { elem: elem.into(), dims: vec![n], trailing_dims: 0, init: None });
                }
                Opcode::Anewarray => {
                    let n = pop(&mut stack)?;
                    let cls = self.pc.class_name(in0.a as u16)
                        .ok_or_else(|| BuildError("anewarray: bad cp".into()))?
                        .to_string();
                    // Component may itself be an array (`new byte[x][]` has
                    // component `[B`): peel the array levels into
                    // trailing_dims so emission reads `new byte[x][]`.
                    let levels = cls.chars().take_while(|&c| c == '[').count() as u8;
                    let mut elem = if levels > 0 {
                        jcdc_jvm::parse_field_descriptor(&cls).unwrap_or(JavaType::Object(cls))
                    } else {
                        JavaType::Object(cls)
                    };
                    for _ in 0..levels {
                        elem = match elem {
                            JavaType::Array(inner) => *inner,
                            other => other,
                        };
                    }
                    stack.push(Expr::NewArray {
                        elem: elem.into(),
                        dims: vec![n],
                        trailing_dims: levels,
                        init: None,
                    });
                }
                Opcode::Multianewarray => {
                    let dims_n = in0.b as usize;
                    let mut dims = Vec::with_capacity(dims_n);
                    for _ in 0..dims_n {
                        dims.push(pop(&mut stack)?);
                    }
                    dims.reverse();
                    // multianewarray references a CONSTANT_Class (array type)
                    let cls = self
                        .pc
                        .class_name(in0.a as u16)
                        .ok_or_else(|| BuildError("mana class".into()))?;
                    let ty = jcdc_jvm::parse_field_descriptor(&cls)
                        .unwrap_or(JavaType::Object("java/lang/Object".into()));
                    // Represent as NewArray with the unallocated levels as
                    // trailing dims (`new char[2][]`): this lets the
                    // array-initializer folding and emission treat it like
                    // any nested initializer.
                    let levels = cls.chars().take_while(|&c| c == '[').count();
                    let mut elem = ty;
                    for _ in 0..levels {
                        elem = match elem {
                            JavaType::Array(inner) => *inner,
                            other => other,
                        };
                    }
                    let trailing = levels.saturating_sub(dims.len()) as u8;
                    stack.push(Expr::NewArray {
                        elem: elem.into(),
                        dims,
                        trailing_dims: trailing,
                        init: None,
                    });
                }
                Opcode::Arraylength => {
                    let arr = pop(&mut stack)?;
                    stack.push(Expr::Field {
                        owner: Some(Box::new(arr)),
                        cls: String::new(),
                        name: "length".into(),
                        ty: JavaType::Int.into(),
                        is_static: false,
                    });
                }

                // ---- misc ----
                Opcode::Checkcast => {
                    let v = pop(&mut stack)?;
                    let ty = self.cp_type(in0.a as u16)?;
                    // javac reifies the covariant array clone() with an
                    // erased checkcast; in source form clone() carries the
                    // receiver's array type statically. Retype the cast to
                    // the receiver's GENERIC array so nested inference
                    // keeps the element type (`Arrays.asList((Class[])
                    // ptypes.clone())` froze T=Class — "List<Class>
                    // 无法转换为List<? extends Class<?>>", jdk17
                    // MethodType.parameterList).
                    let ty = match (&v, &ty) {
                        (
                            Expr::Method { name, owner: Some(o), .. },
                            TypeRef::J(jcdc_jvm::JavaType::Array(_)),
                        ) if name == "clone" => match o.type_ref() {
                            TypeRef::G(g @ jcdc_jvm::GenericType::Array(_))
                                if TypeRef::G(g.clone()).erased() == ty.erased() =>
                            {
                                TypeRef::G(g)
                            }
                            _ => ty,
                        },
                        _ => ty,
                    };
                    stack.push(Expr::Cast { ty, e: Box::new(v) });
                }
                Opcode::Instanceof => {
                    let v = pop(&mut stack)?;
                    let ty = self.cp_type(in0.a as u16)?;
                    stack.push(Expr::InstanceOf { e: Box::new(v), ty });
                }
                Opcode::Monitorenter => {
                    let v = pop(&mut stack)?;
                    stmts.push(Stmt::MonitorEnter(v));
                }
                Opcode::Monitorexit => {
                    let v = pop(&mut stack)?;
                    stmts.push(Stmt::MonitorExit(v));
                }

                Opcode::Invalid => return Err(BuildError(format!("invalid opcode at pc {}", in0.pc))),
                _ => return Err(BuildError(format!("unhandled opcode {:?} at pc {}", op, in0.pc))),
            }
        }

        // Materialize folded array initializers at use sites.
        for st in stmts.iter_mut() {
            self.materialize_stmt_arrays(st);
        }
        term = self.materialize_term_arrays(term);
        for e in stack.iter_mut() {
            let e2 = std::mem::replace(e, Expr::Const(ConstVal::Null));
            *e = self.materialize_arrays(e2);
        }
        Ok(BlockResult { stmts, out_stack: stack, term })
    }

    /// Replace fresh NewArray expressions that have pending folded stores
    /// with `new T[]{...}` initializers (consumed once). Skips assignment
    /// targets (an array being filled by non-constant stores must stay raw).
    pub fn materialize_arrays(&self, e: Expr) -> Expr {
        match e {
            Expr::NewArray { elem, dims, trailing_dims, init: None } => {
                let key = array_key_of(&elem, &dims, trailing_dims);
                let taken = key.and_then(|k| {
                    let vals = self.arrays.borrow_mut().remove(&k)?;
                    if vals.is_empty() { None } else { Some(vals) }
                });
                match taken {
                    Some(vals) => Expr::NewArray { elem, dims, trailing_dims, init: Some(vals) },
                    None => Expr::NewArray { elem, dims, trailing_dims, init: None },
                }
            }
            Expr::Assign { target, op, value } => Expr::Assign {
                target, // do not materialize inside the target
                op,
                value: Box::new(self.materialize_arrays(*value)),
            },
            Expr::New { cls, ty, args, raw } => Expr::New {
                cls,
                ty,
                args: args.into_iter().map(|a| self.materialize_arrays(a)).collect(),
                raw,
            },
            Expr::Method { owner, cls, name, desc, args, is_static, is_interface, is_special, is_super, is_dynamic, type_args } => {
                Expr::Method {
                    owner: owner.map(|o| Box::new(self.materialize_arrays(*o))),
                    cls,
                    name,
                    desc,
                    args: args.into_iter().map(|a| self.materialize_arrays(a)).collect(),
                    is_static,
                    is_interface,
                    is_special,
                    is_super,
                    is_dynamic,
                    type_args,
                }
            }
            Expr::Field { owner, cls, name, ty, is_static } => Expr::Field {
                owner: owner.map(|o| Box::new(self.materialize_arrays(*o))),
                cls,
                name,
                ty,
                is_static,
            },
            Expr::Bin { op, l, r, ty } => Expr::Bin {
                op,
                l: Box::new(self.materialize_arrays(*l)),
                r: Box::new(self.materialize_arrays(*r)),
                ty,
            },
            Expr::Un { op, e } => Expr::Un { op, e: Box::new(self.materialize_arrays(*e)) },
            Expr::Cast { ty, e } => Expr::Cast { ty, e: Box::new(self.materialize_arrays(*e)) },
            Expr::Cond { c, t, f } => Expr::Cond {
                c: Box::new(self.materialize_arrays(*c)),
                t: Box::new(self.materialize_arrays(*t)),
                f: Box::new(self.materialize_arrays(*f)),
            },
            Expr::ArrayIndex { array, index } => Expr::ArrayIndex {
                array: Box::new(self.materialize_arrays(*array)),
                index: Box::new(self.materialize_arrays(*index)),
            },
            Expr::InstanceOf { e, ty } => Expr::InstanceOf { e: Box::new(self.materialize_arrays(*e)), ty },
            Expr::PreIncDec { e, delta, wide } => {
                Expr::PreIncDec { e: Box::new(self.materialize_arrays(*e)), delta, wide }
            }
            Expr::PostIncDec { e, delta, wide } => {
                Expr::PostIncDec { e: Box::new(self.materialize_arrays(*e)), delta, wide }
            }
            Expr::StringConcat(parts) => Expr::StringConcat(
                parts
                    .into_iter()
                    .map(|p| match p {
                        ConcatPart::Str(e) => ConcatPart::Str(self.materialize_arrays(e)),
                        c => c,
                    })
                    .collect(),
            ),
            Expr::Invokedynamic { name, desc, args, bsm_text, bsm_static_args } => Expr::Invokedynamic {
                name,
                desc,
                args: args.into_iter().map(|a| self.materialize_arrays(a)).collect(),
                bsm_text,
                bsm_static_args,
            },
            other => other,
        }
    }

    fn materialize_stmt_arrays(&self, s: &mut Stmt) {
        match s {
            Stmt::ExprStmt(e) => *e = self.materialize_arrays(std::mem::replace(e, Expr::Const(ConstVal::Null))),
            Stmt::LocalDef { init: Some(e), .. } => {
                *e = self.materialize_arrays(std::mem::replace(e, Expr::Const(ConstVal::Null)))
            }
            Stmt::Return(Some(e)) | Stmt::Throw(e) => {
                *e = self.materialize_arrays(std::mem::replace(e, Expr::Const(ConstVal::Null)))
            }
            _ => {}
        }
    }

    fn materialize_term_arrays(&self, t: Term) -> Term {
        match t {
            Term::Return(Some(e)) => Term::Return(Some(self.materialize_arrays(e))),
            Term::Throw(e) => Term::Throw(self.materialize_arrays(e)),
            Term::Cond { cond } => Term::Cond { cond: self.materialize_arrays(cond) },
            Term::Switch { selector, targets } => Term::Switch { selector: self.materialize_arrays(selector), targets },
            other => other,
        }
    }

    // ------------------------------------------------------------------
    // helpers
    // ------------------------------------------------------------------

    /// If the instructions starting at `at` form `<load L>; iconst_1; iadd;
    /// <store L>` (or iinc L,1), return its length (the post-increment
    /// side-effect of an `x++` expression whose value was dup'd).
    fn postinc_ahead(&self, ins: &[Instruction], at: usize) -> Option<usize> {
        let i0 = ins.get(at)?;
        let i1 = ins.get(at + 1)?;
        let i2 = ins.get(at + 2)?;
        let i3 = ins.get(at + 3)?;
        let load_slot = match i0.op {
            Opcode::Iload => Some(i0.a as u16),
            Opcode::Iload0 => Some(0),
            Opcode::Iload1 => Some(1),
            Opcode::Iload2 => Some(2),
            Opcode::Iload3 => Some(3),
            _ => None,
        };
        if let Some(slot) = load_slot {
            if i1.op == Opcode::Iconst1 && i2.op == Opcode::Iadd {
                let store_slot = match i3.op {
                    Opcode::Istore => Some(i3.a as u16),
                    Opcode::Istore0 => Some(0),
                    Opcode::Istore1 => Some(1),
                    Opcode::Istore2 => Some(2),
                    Opcode::Istore3 => Some(3),
                    _ => None,
                };
                if store_slot == Some(slot) {
                    return Some(4);
                }
            }
        }
        // iinc form: dup; iinc L,1 (value = old)
        if i0.op == Opcode::Iinc && i0.b == 1 {
            return Some(1);
        }
        None
    }

    /// Match `<const K>; iadd; <store>` where the store target equals the
    /// stack top (Local slot or Field). Returns (instruction count, delta).
    fn dup_add_store_ahead(&self, ins: &[Instruction], at: usize, stack: &[Expr]) -> Option<(usize, i64)> {
        let i0 = ins.get(at)?;
        let i1 = ins.get(at + 1)?;
        let i2 = ins.get(at + 2)?;
        let k = match i0.op {
            Opcode::Iconst1 => 1i64,
            Opcode::IconstM1 => -1,
            Opcode::Bipush | Opcode::Sipush => i0.a as i64,
            _ => return None,
        };
        if i1.op != Opcode::Iadd {
            return None;
        }
        match (stack.last()?, i2.op) {
            (Expr::Local { var, .. }, sop) => {
                let top_slot = self.vt.var(*var).slot;
                let store_slot = match sop {
                    Opcode::Istore => i2.a as u16,
                    Opcode::Istore0 => 0,
                    Opcode::Istore1 => 1,
                    Opcode::Istore2 => 2,
                    Opcode::Istore3 => 3,
                    _ => return None,
                };
                if store_slot == top_slot {
                    Some((3, k))
                } else {
                    None
                }
            }
            (Expr::Field { cls, name, is_static, .. }, Opcode::Putstatic | Opcode::Putfield) => {
                let (scls, sname, _) = self.member(i2.a as u16).ok()?;
                let want_static = matches!(i2.op, Opcode::Putstatic);
                if scls == *cls && sname == *name && want_static == *is_static {
                    Some((3, k))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Execute one instruction of a recognized post-increment sequence:
    /// the load is skipped (its value is the expression result already on
    /// the stack), the add is dropped, the store becomes `x++`.
    fn exec_postinc_step(
        &self,
        _stack: &mut Vec<Expr>,
        stmts: &mut Vec<Stmt>,
        in0: &Instruction,
    ) -> BResult<()> {
        match in0.op {
            Opcode::Iload | Opcode::Iload0 | Opcode::Iload1 | Opcode::Iload2 | Opcode::Iload3 => Ok(()),
            Opcode::Iconst1 | Opcode::Iadd => Ok(()),
            Opcode::Istore | Opcode::Istore0 | Opcode::Istore1 | Opcode::Istore2 | Opcode::Istore3 => {
                let slot = match in0.op {
                    Opcode::Istore => in0.a as u16,
                    _ => (in0.op as u8 - Opcode::Istore0 as u8) as u16,
                };
                let v = self.var_at(slot, in0.pc)?;
                stmts.push(Stmt::ExprStmt(Expr::PostIncDec {
                    e: Box::new(self.local_expr(v)),
                    delta: 1,
                    wide: false,
                }));
                Ok(())
            }
            Opcode::Iinc => {
                let v = self.var_at(in0.a as u16, in0.pc)?;
                stmts.push(Stmt::ExprStmt(Expr::PostIncDec {
                    e: Box::new(self.local_expr(v)),
                    delta: in0.b as i64,
                    wide: false,
                }));
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn var_at(&self, slot: u16, at_pc: u16) -> BResult<u32> {
        self.vt
            .at(slot, at_pc)
            .ok_or_else(|| BuildError(format!("no var for slot {} @{}", slot, at_pc)))
    }

    fn local_expr(&self, v: u32) -> Expr {
        let info = self.vt.var(v);
        Expr::Local { var: v, ty: info.ty.clone() }
    }

    fn load(&self, slot: u16, at_pc: u16) -> BResult<Expr> {
        let v = self.var_at(slot, at_pc)?;
        if !self.is_static && slot == 0 && self.vt.var(v).name == "this" {
            return Ok(Expr::This);
        }
        Ok(self.local_expr(v))
    }

    fn member(&self, cp_idx: u16) -> BResult<(String, String, String)> {
        let (c, n, d) = self
            .pc
            .member_ref(cp_idx)
            .ok_or_else(|| BuildError("bad member ref".into()))?;
        Ok((c.to_string(), n.to_string(), d.to_string()))
    }

#[allow(dead_code)]
    fn nat_index(&self, cp_idx: u16) -> BResult<u16> {
        match jcdc_classfile::get_entry(&self.pc.cf.constant_pool, cp_idx) {
            Some(ConstantPoolEntry::Methodref(m)) => Ok(m.name_and_type_index),
            Some(ConstantPoolEntry::InterfaceMethodref(m)) => Ok(m.name_and_type_index),
            Some(ConstantPoolEntry::Fieldref(m)) => Ok(m.name_and_type_index),
            Some(ConstantPoolEntry::Dynamic(d)) => Ok(d.name_and_type_index),
            Some(ConstantPoolEntry::InvokeDynamic(d)) => Ok(d.name_and_type_index),
            _ => Err(BuildError("bad nat".into())),
        }
    }

    /// Resolve a CONSTANT_Class index to a TypeRef (handles array classes).
    fn cp_type(&self, idx: u16) -> BResult<TypeRef> {
        let name = self
            .pc
            .class_name(idx)
            .ok_or_else(|| BuildError("bad class cp".into()))?
            .to_string();
        Ok(TypeRef::J(class_name_to_type(&name)))
    }

    fn ldc(&self, stack: &mut Vec<Expr>, idx: u16) -> BResult<()> {
        let e = jcdc_classfile::get_entry(&self.pc.cf.constant_pool, idx)
            .ok_or_else(|| BuildError("ldc bad idx".into()))?;
        match e {
            ConstantPoolEntry::Integer(i) => stack.push(int_const(i.value)),
            ConstantPoolEntry::Float(f) => stack.push(Expr::Const(ConstVal::Float(f.value))),
            ConstantPoolEntry::String(_) => {
                let v = self.pc.string_value(idx).ok_or_else(|| BuildError("ldc str".into()))?;
                stack.push(Expr::Const(ConstVal::Str(v.to_string())));
            }
            ConstantPoolEntry::Class(_) => {
                let name = self.pc.class_name(idx).ok_or_else(|| BuildError("ldc class".into()))?;
                let ty = class_name_to_type(name);
                stack.push(Expr::Const(ConstVal::ClassLit(TypeRef::J(ty))));
            }
            ConstantPoolEntry::Dynamic(_) => {
                // condy: rare; render as null placeholder (refine later).
                stack.push(Expr::Const(ConstVal::Null));
            }
            _ => return Err(BuildError("ldc unexpected entry".into())),
        }
        Ok(())
    }

    fn ldc2w(&self, stack: &mut Vec<Expr>, idx: u16) -> BResult<()> {
        let e = jcdc_classfile::get_entry(&self.pc.cf.constant_pool, idx)
            .ok_or_else(|| BuildError("ldc2w bad idx".into()))?;
        match e {
            ConstantPoolEntry::Long(l) => stack.push(Expr::Const(ConstVal::Long(l.value))),
            ConstantPoolEntry::Double(d) => stack.push(Expr::Const(ConstVal::Double(d.value))),
            _ => return Err(BuildError("ldc2w unexpected".into())),
        }
        Ok(())
    }

    fn arith(&self, stack: &mut Vec<Expr>, op: BinOp, ty: JavaType) -> BResult<()> {
        let r = pop(stack)?;
        let l = pop(stack)?;
        if let Some(folded) = fold_const_binop(op, &l, &r) {
            stack.push(folded);
            return Ok(());
        }
        stack.push(Expr::Bin { op, l: Box::new(l), r: Box::new(r), ty: Some(TypeRef::J(ty)) });
        Ok(())
    }

    fn neg(&self, stack: &mut Vec<Expr>, _ty: JavaType) -> BResult<()> {
        let v = pop(stack)?;
        if let Expr::Const(c) = &v {
            let folded = match c {
                ConstVal::Int(i) => Some(int_const(-i)),
                ConstVal::Long(l) => Some(Expr::Const(ConstVal::Long(-l))),
                ConstVal::Float(f) => Some(Expr::Const(ConstVal::Float(-f))),
                ConstVal::Double(d) => Some(Expr::Const(ConstVal::Double(-d))),
                _ => None,
            };
            if let Some(f) = folded {
                stack.push(f);
                return Ok(());
            }
        }
        stack.push(Expr::Un { op: UnOp::Neg, e: Box::new(v) });
        Ok(())
    }

    fn convert(&self, stack: &mut Vec<Expr>, to: JavaType) -> BResult<()> {
        let v = pop(stack)?;
        let from = v.type_ref().erased();
        if from == to {
            stack.push(v);
            return Ok(());
        }
        // Fold conversions of constants where exact.
        if let Expr::Const(c) = &v {
            let folded = match (&to, c) {
                (JavaType::Long, ConstVal::Int(i)) => Some(Expr::Const(ConstVal::Long(*i as i64))),
                (JavaType::Float, ConstVal::Int(i)) => Some(Expr::Const(ConstVal::Float(*i as f32))),
                (JavaType::Double, ConstVal::Int(i)) => Some(Expr::Const(ConstVal::Double(*i as f64))),
                (JavaType::Double, ConstVal::Long(l)) => Some(Expr::Const(ConstVal::Double(*l as f64))),
                (JavaType::Float, ConstVal::Long(l)) => Some(Expr::Const(ConstVal::Float(*l as f32))),
                (JavaType::Double, ConstVal::Float(f)) => Some(Expr::Const(ConstVal::Double(*f as f64))),
                _ => None,
            };
            if let Some(f) = folded {
                stack.push(f);
                return Ok(());
            }
        }
        // Keep as explicit cast; the emitter drops widening casts when the
        // context makes them implicit.
        stack.push(Expr::Cast { ty: TypeRef::J(to), e: Box::new(v) });
        Ok(())
    }

    /// lcmp/fcmp*/dcmp*: record a comparison marker consumed by the following
    /// if<cond> instruction.
    fn cmp(&self, stack: &mut Vec<Expr>, ty: JavaType) -> BResult<()> {
        let r = pop(stack)?;
        let l = pop(stack)?;
        let tag = match ty {
            JavaType::Long => "J",
            JavaType::Float => "F",
            _ => "D",
        };
        stack.push(Expr::Invokedynamic {
            name: format!("\u{0}cmp{}", tag),
            desc: MethodDescriptor { args: vec![ty.clone(), ty], ret: JavaType::Int },
            args: vec![l, r],
            bsm_text: String::new(),
            bsm_static_args: Vec::new(),
        });
        Ok(())
    }

    /// A store whose popped value is the clone half of a live `dup` pair:
    /// the surviving original becomes an inline `x = e` Assign expression
    /// embedded in the enclosing expression (jdk17 LambdaForm$Name ctor:
    /// `this(-1, .., arguments = Arrays.copyOf(..))` — hoisting the store
    /// to a statement precedes the ctor delegation: "灵活构造器" error).
    /// Returns None when handled, else the untouched value for `store`.
    fn inline_dup_store(
        &self,
        stack: &mut Vec<Expr>,
        slot: u16,
        at_pc: u16,
        next_pc: u16,
        val: Expr,
    ) -> Option<Expr> {
        if std::env::var("JCDC_NO_DUP_INLINE").is_ok() {
            return Some(val);
        }
        let marked = !stack.is_empty()
            && DUP_MARKS.with(|m| m.borrow_mut().remove(&(stack.len() - 1)));
        if !marked {
            return Some(val);
        }
        let v = match self.vt.at(slot, next_pc).or_else(|| self.vt.at(slot, at_pc)) {
            Some(v) => v,
            None => return Some(val),
        };
        // PARAMETER reassignments only: `this(.., arguments = copyOf(..))`
        // (flexible-ctor shape) is the source pattern this recovers.
        // Inlining LOCAL stores (`(c = x.getClass()) != String.class`)
        // reshapes conditions and corrupted downstream loop folding
        // (census +850: ConcurrentHashMap foreach mangle) — locals keep
        // the statement form.
        if !self.vt.var(v).is_param {
            return Some(val);
        }
        let _survivor = stack.pop();
        dup_marks_clear_at_or_above(stack.len());
        stack.push(Expr::Assign {
            target: Box::new(self.local_expr(v)),
            op: AssignOp::Plain,
            value: Box::new(val),
        });
        None
    }

    fn store(&self, stmts: &mut Vec<Stmt>, slot: u16, at_pc: u16, next_pc: u16, val: Expr) -> BResult<()> {
        if !self.is_static && slot == 0 && matches!(val, Expr::This) {
            return Ok(()); // storing `this` to slot 0: noise
        }
        // The stored variable is the one live right AFTER the store (LVT
        // ranges start at the following pc); fall back to the store pc.
        let v = self
            .vt
            .at(slot, next_pc)
            .or_else(|| self.vt.at(slot, at_pc))
            .ok_or_else(|| BuildError(format!("no var for store slot {}", slot)))?;
        let info = self.vt.var(v).clone();
        let already = self.declared.borrow().contains(&v);
        // Declare here when:
        // - the LVT range starts right at/after this store (source variable), or
        // - this is the first write of a synthetic (no-LVT) variable, or
        // - there is no LVT at all.
        let declare_here = !info.is_param
            && !already
            && (info.range_start == next_pc
                || info.range_start == at_pc
                || info.synthetic_name
                || !self.vt.has_lvt);
        if declare_here {
            self.declared.borrow_mut().push(v);
            stmts.push(Stmt::LocalDef { var: v, init: Some(val), is_final: false, force_type: false });
        } else if !info.is_param {
            self.declared.borrow_mut().push(v);
            stmts.push(mk_assign(self.local_expr(v), val));
        } else {
            stmts.push(mk_assign(self.local_expr(v), val));
        }
        Ok(())
    }

    fn invoke(
        &self,
        stack: &mut Vec<Expr>,
        stmts: &mut Vec<Stmt>,
        op: Opcode,
        cp_idx: u16,
    ) -> BResult<()> {
        let (cls, name, d) = self.member(cp_idx)?;
        let mdesc = parse_method_descriptor(&d).ok_or_else(|| BuildError(format!("bad desc {}", d)))?;
        let is_static = op == Opcode::Invokestatic;
        let is_special = op == Opcode::Invokespecial;
        let is_interface = op == Opcode::Invokeinterface;

        let mut args = Vec::with_capacity(mdesc.args.len());
        for _ in 0..mdesc.args.len() {
            args.push(pop(stack)?);
        }
        args.reverse();

        // Varargs call sites: javac packs the trailing arguments into a
        // fresh array. Spread a folded initializer back out so the
        // recompiled call keeps working generic inference
        // (`Map.ofEntries(e1, e2)` vs `Map.ofEntries(new Entry[]{...})`).
        if method_is_varargs(&cls, &name, &d, self.pool, self.pc) {
            if let Some(Expr::NewArray { init: Some(_), .. }) = args.last() {
                let comp = match mdesc.args.last() {
                    Some(JavaType::Array(c)) => Some((**c).clone()),
                    _ => None,
                };
                if let Some(Expr::NewArray { init: Some(vals), .. }) = args.pop() {
                    // Spread Int constants from a folded byte[]/short[]/
                    // char[] initializer re-cast to the component type:
                    // varargs positions do NOT constant-narrow ("varargs
                    // 不匹配; 从int转换到byte可能会有损失", jdk26
                    // PKCS9Attribute.add(.., 22)).
                    let narrow = matches!(
                        comp,
                        Some(JavaType::Byte) | Some(JavaType::Short) | Some(JavaType::Char)
                    );
                    args.extend(vals.into_iter().map(|v| {
                        if narrow && matches!(v, Expr::Const(ConstVal::Int(_))) {
                            if let Some(c) = &comp {
                                return Expr::Cast { ty: TypeRef::J(c.clone()), e: Box::new(v) };
                            }
                        }
                        v
                    }));
                }
            }
        }

        let owner_raw = if is_static { None } else { Some(pop(stack)?) };

        // Constructor calls.
        if name == "<init>" {
            // javac <= 8 synthesizes access constructors for private inner
            // constructors: `Inner(Outer, Outer$1)` where the trailing
            // marker parameter (an empty synthetic class) always receives
            // null at the call site. Drop the marker arg so the call reads
            // `new Inner(...)` against the real constructor.
            if let Some(JavaType::Object(marker)) = mdesc.args.last() {
                let marker_is_synthetic = self
                    .pool
                    .get(marker)
                    .map(|mpc| {
                        mpc.cf
                            .access_flags
                            .contains(jcdc_classfile::ClassAccessFlags::SYNTHETIC)
                    })
                    .unwrap_or(false)
                    || marker
                        .rsplit('$')
                        .next()
                        .map(|tail| !tail.is_empty() && tail.chars().all(|c| c.is_ascii_digit()))
                        .unwrap_or(false);
                if marker_is_synthetic && matches!(args.last(), Some(Expr::Const(ConstVal::Null))) {
                    args.pop();
                }
            }
            if let Some(Expr::New { raw: true, .. }) = owner_raw {
                let ty = TypeRef::J(JavaType::Object(cls.clone()));
                let folded = Expr::New { cls: cls.clone(), ty, args, raw: false };
                // Standard `new C; dup; ...; invokespecial <init>` pattern:
                // the raw twin pushed by `new` is still on the stack and now
                // denotes the initialized object — replace it instead of
                // pushing a second value.
                let twin_on_top = matches!(
                    stack.last(),
                    Some(Expr::New { raw: true, cls: c2, .. }) if *c2 == cls
                );
                if twin_on_top {
                    stack.pop();
                    dup_marks_clear_at_or_above(stack.len());
                }
                stack.push(folded);
                return Ok(());
            }
            // super(...) / this(...)
            let owner = owner_raw.unwrap_or(Expr::This);
            let is_super = !matches!(owner, Expr::This) || cls != self.pc.internal_name;
            let call = Expr::Method {
                owner: Some(Box::new(owner)),
                cls: cls.clone(),
                name: "<init>".into(),
                desc: mdesc,
                args,
                is_static: false,
                is_interface: false,
                is_special: true,
                is_super: cls != self.pc.internal_name,
                is_dynamic: false,
                type_args: Vec::new(),
            };
            let _ = is_super;
            stmts.push(Stmt::ExprStmt(call));
            return Ok(());
        }

        // Java <= 8 javac compiles `a + b + "c"` into a StringBuilder
        // append chain. Contract `new SB(x).append(a)...toString()` back
        // into a StringConcat (`+`) expression — the original source form,
        // which also avoids recompile-time overload ambiguities (e.g.
        // `append(null)`).
        if !is_static
            && args.is_empty()
            && name == "toString"
            && (cls == "java/lang/StringBuilder" || cls == "java/lang/StringBuffer")
        {
            if let Some(parts) = collect_append_chain(owner_raw.clone()) {
                stack.push(Expr::StringConcat(parts));
                return Ok(());
            }
        }

        // invokespecial instance call on `this` targeting another class:
        // a superclass method call (`super.m()`), not a virtual dispatch.
        let super_call = is_special
            && !is_static
            && matches!(owner_raw, Some(Expr::This))
            && cls != self.pc.internal_name;
        let owner = if super_call {
            None
        } else {
            owner_raw.and_then(|o| self.owner_expr(o, &cls))
        };

        // `String.valueOf(poly)` breaks javac's inference when recompiled
        // (overload resolution on inference variables); rewrite to `"" + x`,
        // which matches the original source form.
        if cls == "java/lang/String" && name == "valueOf" && args.len() == 1 && is_poly_expr(&args[0], self.pool) {
            let concat = Expr::StringConcat(vec![
                ConcatPart::Const(String::new()),
                ConcatPart::Str(args.pop().unwrap()),
            ]);
            stack.push(concat);
            return Ok(());
        }

        let e = Expr::Method {
            owner,
            cls,
            name,
            desc: mdesc.clone(),
            args,
            is_static,
            is_interface,
            is_special,
            is_super: super_call,
            is_dynamic: false,
            type_args: Vec::new(),
        };
        if mdesc.ret == JavaType::Void {
            stmts.push(Stmt::ExprStmt(e));
        } else {
            stack.push(e);
        }
        Ok(())
    }

    /// Decide the printed owner expression for an instance member access.
    fn owner_expr(&self, obj: Expr, cls: &str) -> Option<Box<Expr>> {
        if cls == self.pc.internal_name {
            if matches!(obj, Expr::This) {
                return None; // implicit this
            }
        }
        Some(Box::new(obj))
    }

    fn field_type(&self, cls: &str, name: &str, desc: &str) -> TypeRef {
        let base = jcdc_jvm::parse_field_descriptor(desc).unwrap_or(JavaType::Int);
        // Resolve the generic Signature when the declaring class is available.
        if cls == self.pc.internal_name {
            return field_sig_type(self.pc, name, desc).unwrap_or(TypeRef::J(base));
        }
        let owner = self.pool.get(cls);
        if let Some(fpc) = owner.as_deref() {
            return field_sig_type(fpc, name, desc).unwrap_or(TypeRef::J(base));
        }
        TypeRef::J(base)
    }

    fn invoke_dynamic(&self, stack: &mut Vec<Expr>, stmts: &mut Vec<Stmt>, cp_idx: u16) -> BResult<()> {
        let (name, d, bsm_idx) = match jcdc_classfile::get_entry(&self.pc.cf.constant_pool, cp_idx) {
            Some(ConstantPoolEntry::InvokeDynamic(i)) => {
                let (n, d) = self
                    .pc
                    .name_and_type(i.name_and_type_index)
                    .ok_or_else(|| BuildError("indy nat".into()))?;
                (n.to_string(), d.to_string(), i.bootstrap_method_attr_index)
            }
            _ => return Err(BuildError("indy cp".into())),
        };
        let mdesc = parse_method_descriptor(&d).ok_or_else(|| BuildError("indy desc".into()))?;
        let mut args = Vec::with_capacity(mdesc.args.len());
        for _ in 0..mdesc.args.len() {
            args.push(pop(stack)?);
        }
        args.reverse();

        let bsm = self.bootstrap_method(bsm_idx)?;
        let handle = match jcdc_classfile::get_entry(&self.pc.cf.constant_pool, bsm.bootstrap_method_ref) {
            Some(ConstantPoolEntry::MethodHandle(h)) => (h.reference_kind, h.reference_index),
            _ => return Err(BuildError("bsm handle".into())),
        };
        let bsm_target = self.pc.member_ref(handle.1).map(|(a, b, c)| (a.to_string(), b.to_string(), c.to_string()));

        if let Some((bsm_cls, bsm_name, _)) = &bsm_target {
            if (bsm_name == "metafactory" || bsm_name == "altMetafactory")
                && bsm_cls == "java/lang/invoke/LambdaMetafactory"
                && bsm.bootstrap_arguments.len() >= 3
            {
                let impl_handle_idx = bsm.bootstrap_arguments[1];
                // samMethodType = bootstrap arg 0 (CONSTANT_MethodType)
                let sam_md = match jcdc_classfile::get_entry(
                    &self.pc.cf.constant_pool,
                    bsm.bootstrap_arguments[0],
                ) {
                    Some(ConstantPoolEntry::MethodType(mt)) => self
                        .pc
                        .utf8(mt.descriptor_index)
                        .and_then(|d| parse_method_descriptor(d)),
                    _ => None,
                };
                let sam = sam_md.unwrap_or_else(|| mdesc.clone());
                // instantiatedMethodType = bootstrap arg 2 (CONSTANT_MethodType)
                let inst_md = bsm.bootstrap_arguments.get(2).and_then(|&ia| {
                    match jcdc_classfile::get_entry(&self.pc.cf.constant_pool, ia) {
                        Some(ConstantPoolEntry::MethodType(mt)) => self
                            .pc
                            .utf8(mt.descriptor_index)
                            .and_then(|d| parse_method_descriptor(d)),
                        _ => None,
                    }
                });
                if let Some(le) =
                    self.build_lambda(&name, &sam, args.clone(), impl_handle_idx, inst_md)?
                {
                    let e = Expr::Lambda(Box::new(le));
                    if mdesc.ret == JavaType::Void {
                        stmts.push(Stmt::ExprStmt(e));
                    } else {
                        stack.push(e);
                    }
                    return Ok(());
                }
            }
            if (bsm_name == "makeConcatWithConstants" || bsm_name == "makeConcat")
                && bsm_cls == "java/lang/invoke/StringConcatFactory"
            {
                let recipe = if bsm_name == "makeConcatWithConstants" && !bsm.bootstrap_arguments.is_empty() {
                    self.pc.string_value(bsm.bootstrap_arguments[0]).unwrap_or("").to_string()
                } else {
                    "\u{1}".repeat(args.len())
                };
                // Constant placeholders (\u{2}) take values from bsm args[1..].
                let consts: Vec<String> = bsm.bootstrap_arguments[1..]
                    .iter()
                    .filter_map(|&i| self.pc.string_value(i).map(|s| s.to_string()))
                    .collect();
                let mut parts = parse_concat_recipe(&recipe, args, &consts);
                // Concat args declared boolean at the call site: fold
                // 0/1-valued conditionals so they print as true/false.
                {
                    let mut ai = 0usize;
                    for p in parts.iter_mut() {
                        if let ConcatPart::Str(e) = p {
                            if mdesc.args.get(ai) == Some(&JavaType::Boolean) {
                                booleanize(e);
                            }
                            ai += 1;
                        }
                    }
                }
                let e = Expr::StringConcat(parts);
                if mdesc.ret == JavaType::Void {
                    stmts.push(Stmt::ExprStmt(e));
                } else {
                    stack.push(e);
                }
                return Ok(());
            }
        }

        // Fallback: opaque indy.
        let bsm_static_args: Vec<crate::expr::BsmArg> = bsm
            .bootstrap_arguments
            .iter()
            .map(|&ai| {
                match jcdc_classfile::get_entry(&self.pc.cf.constant_pool, ai) {
                    Some(jcdc_classfile::ConstantPoolEntry::String(_)) => {
                        match self.pc.string_value(ai) {
                            Some(v) => crate::expr::BsmArg::Str(v.to_string()),
                            None => crate::expr::BsmArg::Other,
                        }
                    }
                    Some(jcdc_classfile::ConstantPoolEntry::Class(_)) => {
                        match self.pc.class_name(ai) {
                            Some(n) => crate::expr::BsmArg::Cls(n.to_string()),
                            None => crate::expr::BsmArg::Other,
                        }
                    }
                    _ => crate::expr::BsmArg::Other,
                }
            })
            .collect();
        let e = Expr::Invokedynamic {
            name,
            desc: mdesc.clone(),
            args,
            bsm_text: format!("{:?}", bsm_target),
            bsm_static_args,
        };
        if mdesc.ret == JavaType::Void {
            stmts.push(Stmt::ExprStmt(e));
        } else {
            stack.push(e);
        }
        Ok(())
    }

    fn bootstrap_method(&self, idx: u16) -> BResult<jcdc_classfile::BootstrapMethodEntry> {
        for a in &self.pc.cf.attributes {
            if let ParsedAttribute::BootstrapMethods(bm) =
                parse_specialized_attribute(a, &self.pc.cf.constant_pool)
            {
                if let Some(e) = bm.bootstrap_methods.get(idx as usize) {
                    return Ok(e.clone());
                }
            }
        }
        Err(BuildError("bsm index out of range".into()))
    }

    fn build_lambda(
        &self,
        sam_name: &str,
        sam_desc: &MethodDescriptor,
        dynamic_args: Vec<Expr>,
        impl_handle_idx: u16,
        inst_sam_desc: Option<MethodDescriptor>,
    ) -> BResult<Option<LambdaExpr>> {
        let (kind, ref_index) = match jcdc_classfile::get_entry(&self.pc.cf.constant_pool, impl_handle_idx) {
            Some(ConstantPoolEntry::MethodHandle(h)) => (h.reference_kind, h.reference_index),
            _ => return Err(BuildError("lambda impl handle".into())),
        };
        let (impl_owner, impl_name, impl_desc) = {
            let (a, b, c) = self
                .pc
                .member_ref(ref_index)
                .ok_or_else(|| BuildError("lambda impl ref".into()))?;
            (a.to_string(), b.to_string(), c.to_string())
        };
        let impl_mdesc =
            parse_method_descriptor(&impl_desc).ok_or_else(|| BuildError("lambda impl desc".into()))?;

        let n_sam_params = sam_desc.args.len();
        let same_class = impl_owner == self.pc.internal_name;
        let is_synthetic_lambda = same_class && impl_name.starts_with("lambda$");

        if is_synthetic_lambda && kind == jcdc_classfile::ref_kind::INVOKESTATIC {
            // True lambda: dynamic args = captured values; the impl method's
            // params are [captures..., sam params...].
            let captures = dynamic_args;
            let param_names =
                self.impl_param_names(&impl_name, &impl_desc, captures.len(), n_sam_params);
            return Ok(Some(LambdaExpr {
                kind: LambdaKind::Lambda,
                sam_name: sam_name.to_string(),
                sam_desc: sam_desc.clone(),
                inst_sam_desc: inst_sam_desc.clone(),
                impl_owner,
                impl_name,
                impl_desc: impl_mdesc,
                impl_is_static: true,
                captures,
                param_names,
                ref_receiver: None,
                capture_snaps: Vec::new(),
            }));
        }
        if is_synthetic_lambda
            && kind == jcdc_classfile::ref_kind::INVOKEVIRTUAL
            && matches!(dynamic_args.first(), Some(Expr::This))
        {
            // Lambda capturing `this`: javac makes the impl an instance
            // method; the dynamic args are [this, captures...] and the
            // impl params are [captures..., sam params...] with slots
            // starting at 1.
            let captures = dynamic_args[1..].to_vec();
            let param_names =
                self.impl_param_names_slot1(&impl_name, &impl_desc, captures.len(), n_sam_params);
            return Ok(Some(LambdaExpr {
                kind: LambdaKind::Lambda,
                sam_name: sam_name.to_string(),
                sam_desc: sam_desc.clone(),
                inst_sam_desc: inst_sam_desc.clone(),
                impl_owner,
                impl_name,
                impl_desc: impl_mdesc,
                impl_is_static: false,
                captures,
                param_names,
                ref_receiver: None,
                capture_snaps: Vec::new(),
            }));
        }

        // Method reference forms.
        let receiver = match kind {
            jcdc_classfile::ref_kind::INVOKEVIRTUAL | jcdc_classfile::ref_kind::INVOKEINTERFACE
                if dynamic_args.is_empty() =>
            {
                Some(impl_owner.clone()) // Type::instanceMethod
            }
            _ => None,
        };

        let param_names = (0..n_sam_params).map(|i| format!("x{}", i)).collect();
        Ok(Some(LambdaExpr {
            kind: LambdaKind::MethodRef,
            sam_name: sam_name.to_string(),
            sam_desc: sam_desc.clone(),
            inst_sam_desc: inst_sam_desc.clone(),
            impl_owner: impl_owner.clone(),
            impl_name: impl_name.to_string(),
            impl_desc: impl_mdesc,
            impl_is_static: kind == jcdc_classfile::ref_kind::INVOKESTATIC,
            captures: dynamic_args,
            param_names,
            ref_receiver: receiver,
            capture_snaps: Vec::new(),
        }))
    }

    /// Parameter names of a synthetic lambda impl method: skip the first
    /// `n_captures` params, take names for the next `n` from the LVT.
    fn impl_param_names(&self, name: &str, desc: &str, n_captures: usize, n: usize) -> Vec<String> {
        self.impl_param_names_base(name, desc, n_captures, n, 0)
    }

    /// Instance lambda impl: slot 0 is `this`.
    fn impl_param_names_slot1(&self, name: &str, desc: &str, n_captures: usize, n: usize) -> Vec<String> {
        self.impl_param_names_base(name, desc, n_captures, n, 1)
    }

    fn impl_param_names_base(&self, name: &str, desc: &str, n_captures: usize, n: usize, slot_base: u16) -> Vec<String> {
        let fallback = |i: usize| format!("x{}", i);
        let dbg = std::env::var("JCDC_DBG_LAMBDA").is_ok();
        if dbg {
            eprintln!("IMPLPARAMS {} {} caps={} n={} found={}", name, desc, n_captures, n,
                self.pc.find_own_method(name, desc).is_some());
        }
        if let Some(mi) = self.pc.find_own_method(name, desc) {
            if let Some(code) = code_attribute(self.pc, mi) {
                if let Some(md) = parse_method_descriptor(desc) {
                    // Collect LVT entries: slot -> name at start_pc 0.
                    let mut slot_names: Vec<(u16, String)> = Vec::new();
                    for sub in &code.attributes {
                        if let ParsedAttribute::LocalVariableTable(t) =
                            parse_specialized_attribute(sub, &self.pc.cf.constant_pool)
                        {
                            for e in &t.local_variable_table {
                                if e.start_pc == 0 {
                                    if let Some(nm) = self.pc.utf8(e.name_index) {
                                        slot_names.push((e.index, nm.to_string()));
                                    }
                                }
                            }
                        }
                    }
                    let mut names = Vec::new();
                    let mut slot = slot_base; // instance impls start at slot 1
                    for (i, a) in md.args.iter().enumerate() {
                        if i >= n_captures && names.len() < n {
                            let nm = slot_names
                                .iter()
                                .find(|(s, _)| *s == slot)
                                .map(|(_, nm)| nm.clone())
                                .unwrap_or_else(|| fallback(names.len()));
                            names.push(nm);
                        }
                        slot += a.slot_size() as u16;
                    }
                    if dbg {
                        eprintln!("IMPLPARAMS slots={:?} names={:?}", slot_names, names);
                    }
                    if names.len() == n {
                        return names;
                    }
                }
            }
        }
        (0..n).map(fallback).collect()
    }
}

// ----------------------------------------------------------------------
// free helpers
// ----------------------------------------------------------------------

/// Rewrite 0/1-valued expressions in boolean context to true/false forms:
/// `c ? 1 : 0` → c, `c ? 0 : 1` → !c.
fn booleanize(e: &mut Expr) {
    use crate::expr::BinOp;
    let replacement = match e {
        Expr::Cond { c, t, f } => {
            match (&**t, &**f) {
                (Expr::Const(ConstVal::Int(1)), Expr::Const(ConstVal::Int(0))) => {
                    Some((**c).clone())
                }
                (Expr::Const(ConstVal::Int(0)), Expr::Const(ConstVal::Int(1))) => {
                    Some(Expr::Un { op: UnOp::Not, e: c.clone() })
                }
                _ => None,
            }
        }
        Expr::Bin { op, l, r, .. }
            if matches!(op, BinOp::Eq | BinOp::Ne)
                && matches!(&**r, Expr::Const(ConstVal::Int(0)))
                && l.type_ref().erased() == JavaType::Boolean =>
        {
            let inner = (**l).clone();
            Some(match op {
                BinOp::Eq => Expr::Un { op: UnOp::Not, e: Box::new(inner) },
                _ => inner,
            })
        }
        _ => None,
    };
    if let Some(r) = replacement {
        *e = r;
    }
}

/// If `e` shares structure with expressions used in `stmts` and contains
/// side effects or mutable reads, return a textual-safe deep clone. Since
/// Expr trees are values, cloning is structural; the danger is emitting the
/// SAME read twice where the bytecode had one snapshot. We approximate by
/// rebuilding array reads (`a[i]`) that also appear as assign targets in
/// `stmts` into fresh copies — structurally identical but evaluated later;
/// for those cases we instead force a conservative re-read guard: nothing
/// to do here because trees are already independent clones. Kept as a hook.
#[allow(dead_code)]
fn deep_copy_side_effects(e: &Expr, stmts: &[Stmt]) -> Expr {
    let _ = stmts;
    e.clone()
}

pub fn int_const(i: i32) -> Expr {
    Expr::Const(ConstVal::Int(i))
}

fn pop(stack: &mut Vec<Expr>) -> BResult<Expr> {
    let v = stack.pop().ok_or_else(|| BuildError("stack underflow".into()))?;
    dup_marks_clear_at_or_above(stack.len());
    Ok(v)
}

fn mk_assign(target: Expr, val: Expr) -> Stmt {
    Stmt::ExprStmt(Expr::Assign { target: Box::new(target), op: AssignOp::Plain, value: Box::new(val) })
}

/// Resolve a field's generic type from its Signature attribute, if present.
fn field_sig_type(fpc: &PoolClass, name: &str, desc: &str) -> Option<TypeRef> {
    let fi = fpc.find_own_field(name, Some(desc))?;
    let sig_bytes = fpc.field_attr(&fpc.cf.fields[fi], "Signature")?;
    if sig_bytes.len() < 2 {
        return None;
    }
    let idx = u16::from_be_bytes([sig_bytes[0], sig_bytes[1]]);
    let s = fpc.utf8(idx)?;
    jcdc_jvm::parse_field_signature(s).map(TypeRef::G)
}

/// True if the expression is a poly expression whose type is inference-
/// determined (lambda, indy, or a call to a generic method).
pub fn is_poly_expr(e: &Expr, pool: &ClassPool) -> bool {
    match e {
        Expr::Lambda(_) | Expr::Invokedynamic { .. } => true,
        Expr::Method { cls, name, desc, .. } => {
            if let Some((pc, mi)) = pool.resolve_method(cls, name, &desc.to_string()) {
                let m = &pc.cf.methods[mi];
                m.attributes.iter().any(|a| {
                    pc.utf8(a.attribute_name_index) == Some("Signature") && a.info.len() >= 2
                        && u16::from_be_bytes([a.info[0], a.info[1]]) != 0
                        && pc.utf8(u16::from_be_bytes([a.info[0], a.info[1]]))
                            .map(|s| s.starts_with('<'))
                            .unwrap_or(false)
                })
            } else {
                false
            }
        }
        _ => false,
    }
}

pub fn class_name_to_type(name: &str) -> JavaType {
    if name.starts_with('[') {
        jcdc_jvm::parse_field_descriptor(name).unwrap_or(JavaType::Object(name.to_string()))
    } else {
        JavaType::Object(name.to_string())
    }
}

/// True if dropping this expression from a `pop` would change semantics.
pub fn has_side_effects(e: &Expr) -> bool {
    match e {
        Expr::Const(_) | Expr::Local { .. } | Expr::This | Expr::Raw(_) | Expr::RawT(..) => false,
        Expr::New { .. } | Expr::Method { .. } | Expr::Invokedynamic { .. } | Expr::Lambda(_)
        | Expr::AnonNew { .. } => true,
        Expr::Assign { .. } | Expr::PreIncDec { .. } | Expr::PostIncDec { .. } => true,
        Expr::Field { owner, .. } => {
            // getfield can NPE / trigger clinit; keep to be safe unless owner is this
            owner.is_some()
        }
        Expr::ArrayIndex { .. } => true,
        Expr::Un { e, .. } | Expr::Cast { e, .. } | Expr::InstanceOf { e, .. } => has_side_effects(e),
        Expr::Bin { l, r, .. } => has_side_effects(l) || has_side_effects(r),
        Expr::Cond { c, t, f } => has_side_effects(c) || has_side_effects(t) || has_side_effects(f),
        Expr::NewArray { dims, init, .. } => {
            dims.iter().any(has_side_effects) || init.as_ref().map(|v| v.iter().any(has_side_effects)).unwrap_or(false)
        }
        Expr::NewMultiArray { dims, .. } => dims.iter().any(has_side_effects),
        Expr::StringConcat(parts) => parts.iter().any(|p| match p {
            ConcatPart::Str(e) => has_side_effects(e),
            ConcatPart::Const(_) => false,
        }),
    }
}

/// If the value is a cmp sentinel, unfold into (l, r, op); otherwise compare
/// against zero.
fn unfold_cmp(v: Expr, op_if_int: BinOp) -> (Expr, Expr, BinOp) {
    if let Expr::Invokedynamic { name, args, .. } = &v {
        if name.starts_with("\u{0}cmp") && args.len() == 2 {
            let mut args = match v {
                Expr::Invokedynamic { args, .. } => args,
                _ => unreachable!(),
            };
            let r = args.pop().unwrap();
            let l = args.pop().unwrap();
            return (l, r, op_if_int);
        }
    }
    (v, int_const(0), op_if_int)
}

fn fold_const_binop(op: BinOp, l: &Expr, r: &Expr) -> Option<Expr> {
    use ConstVal::*;
    match (op, l, r) {
        (BinOp::Add, Expr::Const(Int(a)), Expr::Const(Int(b))) => Some(int_const(a.wrapping_add(*b))),
        (BinOp::Sub, Expr::Const(Int(a)), Expr::Const(Int(b))) => Some(int_const(a.wrapping_sub(*b))),
        (BinOp::Mul, Expr::Const(Int(a)), Expr::Const(Int(b))) => Some(int_const(a.wrapping_mul(*b))),
        (BinOp::Div, Expr::Const(Int(a)), Expr::Const(Int(b))) if *b != 0 => Some(int_const(a.wrapping_div(*b))),
        (BinOp::Rem, Expr::Const(Int(a)), Expr::Const(Int(b))) if *b != 0 => Some(int_const(a.wrapping_rem(*b))),
        (BinOp::And, Expr::Const(Int(a)), Expr::Const(Int(b))) => Some(int_const(a & b)),
        (BinOp::Or, Expr::Const(Int(a)), Expr::Const(Int(b))) => Some(int_const(a | b)),
        (BinOp::Xor, Expr::Const(Int(a)), Expr::Const(Int(b))) => Some(int_const(a ^ b)),
        (BinOp::Shl, Expr::Const(Int(a)), Expr::Const(Int(b))) => Some(int_const(a.wrapping_shl(*b as u32))),
        (BinOp::Shr, Expr::Const(Int(a)), Expr::Const(Int(b))) => Some(int_const(a.wrapping_shr(*b as u32))),
        (BinOp::Ushr, Expr::Const(Int(a)), Expr::Const(Int(b))) => {
            Some(int_const(((*a as u32).wrapping_shr(*b as u32)) as i32))
        }
        (BinOp::Add, Expr::Const(Long(a)), Expr::Const(Long(b))) => Some(Expr::Const(Long(a.wrapping_add(*b)))),
        (BinOp::Sub, Expr::Const(Long(a)), Expr::Const(Long(b))) => Some(Expr::Const(Long(a.wrapping_sub(*b)))),
        (BinOp::Mul, Expr::Const(Long(a)), Expr::Const(Long(b))) => Some(Expr::Const(Long(a.wrapping_mul(*b)))),
        (BinOp::Div, Expr::Const(Long(a)), Expr::Const(Long(b))) if *b != 0 => {
            Some(Expr::Const(Long(a.wrapping_div(*b))))
        }
        (BinOp::Rem, Expr::Const(Long(a)), Expr::Const(Long(b))) if *b != 0 => {
            Some(Expr::Const(Long(a.wrapping_rem(*b))))
        }
        (BinOp::Add, Expr::Const(Str(a)), Expr::Const(Str(b))) => {
            Some(Expr::Const(Str(format!("{}{}", a, b))))
        }
        _ => None,
    }
}

/// Translate a StringConcatFactory recipe into parts.
/// `\u{1}` = dynamic arg placeholder, `\u{2}` = constant placeholder (value
/// from `consts`, consumed in order).
pub fn parse_concat_recipe(recipe: &str, args: Vec<Expr>, consts: &[String]) -> Vec<ConcatPart> {
    let mut parts = Vec::new();
    let mut buf = String::new();
    let mut arg_it = args.into_iter();
    let mut const_it = consts.iter();
    for c in recipe.chars() {
        match c {
            '\u{1}' => {
                if !buf.is_empty() {
                    parts.push(ConcatPart::Const(std::mem::take(&mut buf)));
                }
                if let Some(a) = arg_it.next() {
                    parts.push(ConcatPart::Str(a));
                }
            }
            '\u{2}' => {
                if let Some(s) = const_it.next() {
                    buf.push_str(s);
                }
            }
            _ => buf.push(c),
        }
    }
    if !buf.is_empty() {
        parts.push(ConcatPart::Const(buf));
    }
    parts
}


/// Contract a `new StringBuilder[(init)].append(x)...` receiver chain into
/// string-concat parts. Returns None when the receiver is not a pure
/// javac concat chain (e.g. a variable or a capacity constructor).
fn collect_append_chain(owner: Option<Expr>) -> Option<Vec<ConcatPart>> {
    let is_sb = |c: &str| c == "java/lang/StringBuilder" || c == "java/lang/StringBuffer";
    let mut parts: Vec<ConcatPart> = Vec::new();
    let mut cur = owner?;
    loop {
        match cur {
            Expr::Method { owner: ref o, cls: ref c, name: ref n, args: ref a, .. }
                if n == "append" && is_sb(c) && a.len() == 1 && o.is_some() =>
            {
                parts.push(ConcatPart::Str(a[0].clone()));
                cur = *o.clone().unwrap();
            }
            Expr::New { cls: ref c, args: ref a, raw: false, .. } if is_sb(c) => {
                match a.len() {
                    0 => break,
                    1 => {
                        // `new StringBuilder("lit")` seeds the first part;
                        // capacity (int) or char[] forms are not concat
                        // desugaring — bail out.
                        match a[0].type_ref().erased() {
                            JavaType::Object(ref n) if n == "java/lang/String" => {
                                parts.push(ConcatPart::Str(a[0].clone()));
                                break;
                            }
                            _ => return None,
                        }
                    }
                    _ => return None,
                }
            }
            _ => return None,
        }
    }
    parts.reverse();
    if parts.is_empty() {
        return None;
    }
    Some(parts)
}


/// True when the referenced method is declared VARARGS.
fn method_is_varargs(
    cls: &str,
    name: &str,
    desc: &str,
    pool: &jcdc_jvm::ClassPool,
    pc: &jcdc_jvm::PoolClass,
) -> bool {
    use jcdc_classfile::MethodAccessFlags;
    let check = |cpc: &jcdc_jvm::PoolClass| -> bool {
        (0..cpc.cf.methods.len()).any(|i| {
            cpc.method_name(i) == Some(name)
                && cpc.method_desc(i) == Some(desc)
                && cpc.cf.methods[i].access_flags.contains(MethodAccessFlags::VARARGS)
        })
    };
    if cls == pc.internal_name {
        return check(pc);
    }
    match pool.get(cls) {
        Some(cpc) => check(&cpc),
        None => false,
    }
}
