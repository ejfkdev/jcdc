//! Statement tree for decompiled code.

use crate::expr::Expr;

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    /// A plain `{ ... }` block (or statement sequence during construction).
    Block(Vec<Stmt>),
    /// Expression statement (the expression must have side effects).
    ExprStmt(Expr),
    /// Local variable declaration: `[final] T name [= init];`
    LocalDef {
        var: u32,
        init: Option<Expr>,
        is_final: bool,
        /// Force declaration with explicit type even when inferrable.
        force_type: bool,
    },
    Return(Option<Expr>),
    Throw(Expr),
    If {
        cond: Expr,
        then_stmt: Box<Stmt>,
        else_stmt: Option<Box<Stmt>>,
    },
    /// `while (cond) body`; cond may be `true` for infinite loops.
    While {
        cond: Expr,
        body: Box<Stmt>,
    },
    DoWhile {
        body: Box<Stmt>,
        cond: Expr,
    },
    /// Classic `for (init; cond; update) body`.
    For {
        init: Vec<Stmt>,
        cond: Option<Expr>,
        update: Vec<Expr>,
        body: Box<Stmt>,
    },
    /// Enhanced for: `for (T v : iterable) body`.
    ForEach {
        var: u32,
        iterable: Expr,
        /// true if iterating an array (index-based lowering).
        is_array: bool,
        body: Box<Stmt>,
    },
    Switch {
        selector: Expr,
        cases: Vec<CaseGroup>,
        default: Option<Box<Stmt>>,
        /// true if this was a string switch (selector hashed).
        on_string: bool,
    },
    Try {
        body: Box<Stmt>,
        catches: Vec<Catch>,
        finally: Option<Box<Stmt>>,
    },
    /// `try (resources) body` — restored try-with-resources.
    TryWithResources {
        /// Resource declarations (`LocalDef` statements).
        resources: Vec<Stmt>,
        body: Box<Stmt>,
        catches: Vec<Catch>,
        finally: Option<Box<Stmt>>,
    },
    /// `assert cond [: msg];` restored from the $assertionsDisabled idiom.
    Assert {
        cond: Expr,
        msg: Option<Expr>,
    },
    /// `synchronized (lock) body`
    Synchronized {
        lock: Expr,
        body: Box<Stmt>,
    },
    /// A folded value-diamond: this "statement" represents a value left on
    /// the operand stack (consumed by the merge block). Removed after the
    /// merge statements are woven.
    TernaryValue { e: Expr },
    /// Raw monitorenter (before synchronized reconstruction).
    MonitorEnter(Expr),
    /// Raw monitorexit.
    MonitorExit(Expr),
    /// Fallback: label (for unstructured control flow / jsr-ret leftovers).
    Label(u32),
    /// Fallback: goto a label.
    Goto(u32),
    /// Local class declaration rendered inline in a method body.
    /// `header` is e.g. `Local implements Runnable`.
    ClassDecl { name: String, header: String, body: String },
    /// `label: statement`
    Labeled { label: String, body: Box<Stmt> },
    /// `break;` / `break label;`
    Break(Option<String>),
    /// `continue;` / `continue label;`
    Continue(Option<String>),
    /// A raw line we could not decompile (error resilience).
    Comment(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct CaseGroup {
    /// Case labels (empty = fallthrough continuation of previous group).
    pub labels: Vec<i64>,
    /// String case values (when on_string).
    pub string_labels: Vec<String>,
    /// Enum constant names (restored $SwitchMap switch).
    pub enum_labels: Vec<String>,
    /// Verbatim case labels (`null`, type patterns) from typeSwitch
    /// restoration.
    pub raw_labels: Vec<String>,
    pub body: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Catch {
    /// Exception class internal names (multi-catch when >1);
    /// empty = catch-all (`finally` style / Throwable).
    pub exc: Vec<String>,
    /// Variable holding the exception parameter.
    pub var: u32,
    /// Per-occurrence printed name (avoids nested-catch collisions).
    pub var_name: Option<String>,
    pub body: Box<Stmt>,
}

impl Stmt {
    pub fn is_empty_block(&self) -> bool {
        matches!(self, Stmt::Block(b) if b.is_empty())
    }

    /// Wrap in a block if not already one.
    pub fn as_block(self) -> Stmt {
        match self {
            Stmt::Block(_) => self,
            other => Stmt::Block(vec![other]),
        }
    }
}

/// Flatten nested single-statement blocks for cleaner output.
pub fn flatten(s: &mut Stmt) {
    match s {
        Stmt::Block(v) => {
            for x in v.iter_mut() {
                flatten(x);
            }
        }
        Stmt::If { then_stmt, else_stmt, .. } => {
            flatten(then_stmt);
            if let Some(e) = else_stmt {
                flatten(e);
            }
        }
        Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => flatten(body),
        Stmt::For { body, .. } | Stmt::ForEach { body, .. } => flatten(body),
        Stmt::Try { body, catches, finally } => {
            flatten(body);
            for c in catches {
                flatten(&mut c.body);
            }
            if let Some(f) = finally {
                flatten(f);
            }
        }
        Stmt::TryWithResources { body, catches, finally, .. } => {
            flatten(body);
            for c in catches {
                flatten(&mut c.body);
            }
            if let Some(f) = finally {
                flatten(f);
            }
        }
        Stmt::Synchronized { body, .. } => flatten(body),
        Stmt::Switch { cases, default, .. } => {
            for c in cases {
                for s in c.body.iter_mut() {
                    flatten(s);
                }
            }
            if let Some(d) = default {
                flatten(d);
            }
        }
        _ => {}
    }
}
