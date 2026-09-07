//! Expression tree for decompiled code.

use jcdc_jvm::{GenericType, JavaType, MethodDescriptor};

/// A type reference that may carry generics from a Signature attribute.
#[derive(Debug, Clone, PartialEq)]
pub enum TypeRef {
    /// Plain descriptor type.
    J(JavaType),
    /// Generic signature type.
    G(GenericType),
}

impl TypeRef {
    pub fn to_java(&self) -> String {
        match self {
            TypeRef::J(t) => t.to_java(true),
            TypeRef::G(g) => g.to_java(),
        }
    }

    /// Underlying erased Java type (for generics: erased class/primitive).
    pub fn erased(&self) -> JavaType {
        match self {
            TypeRef::J(t) => t.clone(),
            TypeRef::G(g) => generic_to_erased(g),
        }
    }

    pub fn slot_size(&self) -> usize {
        self.erased().slot_size()
    }

    pub fn is_wide(&self) -> bool {
        self.erased().is_wide()
    }

    /// The internal class name if this is a plain object reference.
    pub fn internal_name(&self) -> Option<&str> {
        match self {
            TypeRef::J(JavaType::Object(n)) => Some(n),
            TypeRef::G(GenericType::Class(cs)) if cs.parts.iter().all(|p| p.args.is_empty()) => None, // owned string; caller uses erased
            _ => None,
        }
    }
}

pub fn generic_to_erased(g: &GenericType) -> JavaType {
    match g {
        GenericType::Primitive(c) => match c {
            'V' => JavaType::Void,
            'Z' => JavaType::Boolean,
            'B' => JavaType::Byte,
            'C' => JavaType::Char,
            'S' => JavaType::Short,
            'I' => JavaType::Int,
            'F' => JavaType::Float,
            'J' => JavaType::Long,
            'D' => JavaType::Double,
            _ => JavaType::Void,
        },
        GenericType::Class(cs) => JavaType::Object(cs.internal_name()),
        GenericType::Array(inner) => JavaType::Array(Box::new(generic_to_erased(inner))),
        GenericType::TypeVar(_) => JavaType::Object("java/lang/Object".into()),
        GenericType::Wildcard(_) => JavaType::Object("java/lang/Object".into()),
    }
}

impl From<JavaType> for TypeRef {
    fn from(t: JavaType) -> Self {
        TypeRef::J(t)
    }
}

/// A constant value with its source-level type.
#[derive(Debug, Clone, PartialEq)]
pub enum ConstVal {
    Int(i32),
    Long(i64),
    Float(f32),
    Double(f64),
    Str(String),
    /// `null` literal.
    Null,
    /// Unloaded class constant resolved to a class literal or `X.class`.
    ClassLit(TypeRef),
}

impl ConstVal {
    pub fn type_ref(&self) -> TypeRef {
        match self {
            ConstVal::Int(_) => JavaType::Int.into(),
            ConstVal::Long(_) => JavaType::Long.into(),
            ConstVal::Float(_) => JavaType::Float.into(),
            ConstVal::Double(_) => JavaType::Double.into(),
            ConstVal::Str(_) => JavaType::Object("java/lang/String".into()).into(),
            ConstVal::Null => JavaType::Object("java/lang/Object".into()).into(),
            ConstVal::ClassLit(_) => JavaType::Object("java/lang/Class".into()).into(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Neg,     // -x
    Not,     // !x
    BitNot,  // ~x
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add, Sub, Mul, Div, Rem,
    Shl, Shr, Ushr,
    And, Or, Xor,
    Eq, Ne, Lt, Ge, Gt, Le,
    /// Reference equality on objects (==).
    RefEq, RefNe,
    /// Logical && and || (from short-circuit structuring).
    LogAnd, LogOr,
    /// String concatenation `+`.
    StrCat,
}

impl BinOp {
    /// Java operator precedence (higher binds tighter).
    pub fn precedence(&self) -> u8 {
        match self {
            BinOp::Mul | BinOp::Div | BinOp::Rem => 13,
            BinOp::Add | BinOp::Sub | BinOp::StrCat => 12,
            BinOp::Shl | BinOp::Shr | BinOp::Ushr => 11,
            BinOp::Lt | BinOp::Ge | BinOp::Gt | BinOp::Le => 10,
            BinOp::Eq | BinOp::Ne | BinOp::RefEq | BinOp::RefNe => 9,
            BinOp::And => 8,
            BinOp::Xor => 7,
            BinOp::Or => 6,
            BinOp::LogAnd => 4,
            BinOp::LogOr => 3,
        }
    }

    pub fn symbol(&self) -> &'static str {
        match self {
            BinOp::Add | BinOp::StrCat => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Rem => "%",
            BinOp::Shl => "<<",
            BinOp::Shr => ">>",
            BinOp::Ushr => ">>>",
            BinOp::And => "&",
            BinOp::Or => "|",
            BinOp::Xor => "^",
            BinOp::Eq | BinOp::RefEq => "==",
            BinOp::Ne | BinOp::RefNe => "!=",
            BinOp::Lt => "<",
            BinOp::Ge => ">=",
            BinOp::Gt => ">",
            BinOp::Le => "<=",
            BinOp::LogAnd => "&&",
            BinOp::LogOr => "||",
        }
    }

    /// The reversed comparison operator (for condition inversion).
    pub fn invert(self) -> Option<BinOp> {
        Some(match self {
            BinOp::Eq | BinOp::RefEq => BinOp::Ne,
            BinOp::Ne | BinOp::RefNe => BinOp::Eq,
            BinOp::Lt => BinOp::Ge,
            BinOp::Ge => BinOp::Lt,
            BinOp::Gt => BinOp::Le,
            BinOp::Le => BinOp::Gt,
            BinOp::LogAnd => BinOp::LogOr,
            BinOp::LogOr => BinOp::LogAnd,
            _ => return None,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignOp {
    Plain,
    Add, Sub, Mul, Div, Rem,
    Shl, Shr, Ushr,
    And, Or, Xor,
}

impl AssignOp {
    pub fn symbol(&self) -> &'static str {
        match self {
            AssignOp::Plain => "=",
            AssignOp::Add => "+=",
            AssignOp::Sub => "-=",
            AssignOp::Mul => "*=",
            AssignOp::Div => "/=",
            AssignOp::Rem => "%=",
            AssignOp::Shl => "<<=",
            AssignOp::Shr => ">>=",
            AssignOp::Ushr => ">>>=",
            AssignOp::And => "&=",
            AssignOp::Or => "|=",
            AssignOp::Xor => "^=",
        }
    }
}

/// Lambda kind inferred from invokedynamic + LambdaMetafactory.
#[derive(Debug, Clone, PartialEq)]
pub enum LambdaKind {
    /// `args -> body` referencing an implementation method.
    Lambda,
    /// `Cls::name` static/instance reference.
    MethodRef,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LambdaExpr {
    pub kind: LambdaKind,
    /// Functional interface method name/desc for casting ambiguity if needed.
    pub sam_name: String,
    pub sam_desc: MethodDescriptor,
    /// Implementation method (for Lambda kind: the body is emitted from it,
    /// or referenced by name when it belongs to another class).
    pub impl_owner: String,
    pub impl_name: String,
    pub impl_desc: MethodDescriptor,
    pub impl_is_static: bool,
    /// Captured arguments (evaluated at indy call site), in impl-arg order
    /// after the SAM parameters.
    pub captures: Vec<Expr>,
    /// SAM parameter names (synthesized if absent).
    pub param_names: Vec<String>,
    /// Method-ref receiver class name, for `X::y` form.
    pub ref_receiver: Option<String>,
    /// Snapshot renames for captured outer locals that are NOT
    /// effectively final (the decompiler hoists+reassigns them):
    /// (outer var id, impl-method param var id, snapshot name). The
    /// method pass declares `final T name = outer;` before the lambda's
    /// statement and the printer renames the impl param accordingly.
    pub capture_snaps: Vec<(u32, u32, String)>,
}

/// Resolved static bootstrap-method argument.
#[derive(Debug, Clone, PartialEq)]
pub enum BsmArg {
    Str(String),
    Cls(String),
    Other,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ConcatPart {
    Str(Expr),
    /// Recipe constant segment.
    Const(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Const(ConstVal),
    /// Local variable by VarId, with its declared type (needed for
    /// category-1 vs category-2 stack operations like dup2/pop2).
    Local { var: u32, ty: TypeRef },
    This,
    /// `new T(args)` (constructor call folded with New when possible).
    New {
        cls: String,
        ty: TypeRef,
        args: Vec<Expr>,
        /// true if this is a raw `new` whose `<init>` hasn't been folded yet.
        raw: bool,
    },
    /// Array creation: `new int[n]`, `new int[]{...}`, `new int[a][b][]`.
    NewArray {
        elem: TypeRef,
        /// dimension sizes for the created dimensions
        dims: Vec<Expr>,
        /// trailing empty dimensions count (e.g. `new int[3][]` -> dims=[3], trailing=1)
        trailing_dims: u8,
        /// initializer for `new T[]{...}` form
        init: Option<Vec<Expr>>,
    },
    /// Multi-dimensional array creation `multianewarray`.
    NewMultiArray {
        ty: TypeRef,
        dims: Vec<Expr>,
    },
    Field {
        /// None = `this` (instance field of current class) or static import-style.
        owner: Option<Box<Expr>>,
        /// Declaring class internal name.
        cls: String,
        name: String,
        ty: TypeRef,
        is_static: bool,
    },
    Method {
        owner: Option<Box<Expr>>,
        cls: String,
        name: String,
        desc: MethodDescriptor,
        args: Vec<Expr>,
        is_static: bool,
        is_interface: bool,
        /// invokespecial (super call / constructor / private).
        is_special: bool,
        /// `super.m(...)` form.
        is_super: bool,
        /// invokedynamic without recognized pattern.
        is_dynamic: bool,
        /// Explicit type arguments (`Cls.<E>m(...)`) restored for generic
        /// calls in throw position, where inference would pick the bound.
        type_args: Vec<String>,
    },
    ArrayIndex {
        array: Box<Expr>,
        index: Box<Expr>,
    },
    Cast {
        ty: TypeRef,
        e: Box<Expr>,
    },
    InstanceOf {
        e: Box<Expr>,
        ty: TypeRef,
    },
    Un {
        op: UnOp,
        e: Box<Expr>,
    },
    Bin {
        op: BinOp,
        l: Box<Expr>,
        r: Box<Expr>,
        /// Type context for `+` disambiguation (string vs numeric).
        ty: Option<TypeRef>,
    },
    Cond {
        c: Box<Expr>,
        t: Box<Expr>,
        f: Box<Expr>,
    },
    Assign {
        target: Box<Expr>,
        op: AssignOp,
        value: Box<Expr>,
    },
    /// `++x` / `--x` (delta = +1 / -1)
    PreIncDec {
        e: Box<Expr>,
        delta: i64,
        wide: bool,
    },
    /// `x++` / `x--`
    PostIncDec {
        e: Box<Expr>,
        delta: i64,
        wide: bool,
    },
    Lambda(Box<LambdaExpr>),
    /// String concatenation via StringConcatFactory recipe.
    StringConcat(Vec<ConcatPart>),
    /// Pre-rendered source fragment (used for captured expressions that are
    /// substituted across method contexts).
    Raw(String),
    /// Pre-rendered capture text WITH the captured local's declared type:
    /// comparisons inside local-class bodies need the operand's generic
    /// type to drive witnesses (erased val$ field types cannot).
    RawT(String, TypeRef),
    /// Unrecognized invokedynamic fallback.
    Invokedynamic {
        name: String,
        desc: MethodDescriptor,
        args: Vec<Expr>,
        bsm_text: String,
        /// Resolved static bootstrap arguments (for SwitchBootstraps
        /// typeSwitch restoration).
        bsm_static_args: Vec<BsmArg>,
    },
    /// `new Anon(args) { ...class body... }` — anonymous class instantiation.
    AnonNew {
        /// The anonymous class itself.
        cls: String,
        /// Interface being implemented, or superclass (Object suppressed).
        base: TypeRef,
        args: Vec<Expr>,
        /// Decompiled class body lines (already indented relative).
        body: String,
    },
}

impl Expr {
    /// Best-effort static type of this expression.
    pub fn type_ref(&self) -> TypeRef {
        match self {
            Expr::Const(c) => c.type_ref(),
            Expr::Local { ty, .. } => ty.clone(),
            Expr::This => JavaType::Object("java/lang/Object".into()).into(),
            Expr::New { ty, .. } => ty.clone(),
            Expr::NewArray { elem, .. } => JavaType::Array(Box::new(elem.erased())).into(),
            Expr::NewMultiArray { ty, .. } => ty.clone(),
            Expr::Field { ty, .. } => ty.clone(),
            Expr::Method { desc, .. } => desc.ret.clone().into(),
            Expr::ArrayIndex { array, .. } => match &**array {
                other => match other.type_ref().erased() {
                    JavaType::Array(inner) => (*inner).clone().into(),
                    t => t.into(),
                },
            },
            Expr::Cast { ty, .. } => ty.clone(),
            Expr::InstanceOf { .. } => JavaType::Boolean.into(),
            Expr::Un { op: UnOp::Not, .. } => JavaType::Boolean.into(),
            Expr::Un { e, .. } => e.type_ref(),
            Expr::Bin { op, ty, l, .. } => match op {
                // Comparisons and short-circuit logicals are boolean
                // regardless of operand types — the stored `ty` (when
                // present it mirrors the operands) misled the bool->int
                // assignment rewrite (`int mode = e != null;` stayed
                // unrewrapped: jdk11 SynchronousQueue).
                BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Ge | BinOp::Gt
                | BinOp::Le | BinOp::RefEq | BinOp::RefNe | BinOp::LogAnd
                | BinOp::LogOr => JavaType::Boolean.into(),
                _ => ty.clone().unwrap_or_else(|| l.type_ref()),
            },
            Expr::Cond { t, .. } => t.type_ref(),
            Expr::Assign { value, .. } => value.type_ref(),
            Expr::PreIncDec { e, .. } | Expr::PostIncDec { e, .. } => e.type_ref(),
            Expr::Lambda(_) => JavaType::Object("java/lang/Object".into()).into(),
            Expr::Raw(_) => JavaType::Object("java/lang/Object".into()).into(),
            Expr::RawT(_, ty) => ty.clone(),
            Expr::AnonNew { cls, .. } => JavaType::Object(cls.clone()).into(),
            Expr::StringConcat(_) => JavaType::Object("java/lang/String".into()).into(),
            Expr::Invokedynamic { desc, .. } => desc.ret.clone().into(),
        }
    }

    /// True if emitting this expression as a statement component needs parens
    /// at the given outer precedence context.
    pub fn needs_parens(&self, outer_prec: u8, is_right: bool) -> bool {
        match self {
            Expr::Bin { op, .. } => {
                let p = op.precedence();
                p < outer_prec || (is_right && p == outer_prec)
            }
            Expr::InstanceOf { .. } => outer_prec > 10,
            Expr::Cond { .. } => outer_prec > 2,
            Expr::Assign { .. } | Expr::PreIncDec { .. } | Expr::PostIncDec { .. } => outer_prec > 1,
            Expr::Un { .. } => outer_prec > 14,
            Expr::Cast { .. } => outer_prec > 13,
            _ => false,
        }
    }
}
