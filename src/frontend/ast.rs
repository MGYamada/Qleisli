//! Syntax tree for the provisional `.qli` surface grammar.
//!
//! Every span is a half-open UTF-8 byte range in the original source. The
//! parser deliberately records syntax only; an AST is not a type or resource
//! safety certificate.

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub const fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    pub const fn cover(self, other: Self) -> Self {
        Self::new(self.start, other.end)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ident {
    pub text: String,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Module {
    pub uses: Vec<UseDecl>,
    pub decls: Vec<Decl>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UseDecl {
    /// The final segment is the imported name; preceding segments name its module.
    pub path: Vec<Ident>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FnKind {
    /// A provisional bounded Nat helper; never an ordinary runtime function.
    Static,
    /// A finite mathematical target, never a callable runtime function.
    Meaning,
    /// A total finite classical expression, reusable ordinarily and in basis maps.
    Classical,
    /// An ordinary body-bearing function with no effect assertion.
    Inferred,
    Iso,
    Unitary,
    Observe,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decl {
    pub public: bool,
    pub kind: FnKind,
    pub name: Ident,
    pub static_params: Vec<StaticParam>,
    pub requires: Vec<Requirement>,
    pub params: Vec<Param>,
    pub return_type: Type,
    pub body: FnBody,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Param {
    /// One typed pattern is one argument. Name/wildcard/product patterns retain
    /// immediate tuple arity; their ownership rules depend on the value's type.
    pub pattern: Pattern,
    pub ty: Type,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Type {
    pub kind: TypeKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeKind {
    Unit,
    Bit,
    Bits(Natural),
    Named(Ident),
    Q(Box<Type>),
    Tuple(Vec<Type>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FnBody {
    Natural(Natural),
    Meaning { permutation: bool, function: Ident },
    Basis(BasisExpr),
    Quantum(Block),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    /// True only when source omitted its tail expression; profile checks decide support.
    pub implicit_result: bool,
    pub statements: Vec<Stmt>,
    pub result: Box<Expr>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StmtKind {
    StaticLet { name: Ident, value: Natural },
    Let { pattern: Pattern, value: Expr },
    Expr(Expr),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PatternKind {
    Name(Ident),
    Wildcard,
    Tuple(Vec<Pattern>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprKind {
    ApplyStatic {
        operation: StaticOp,
        input: Box<Expr>,
    },
    ApplyContract {
        implementation: Ident,
        specification: Ident,
        input: Box<Expr>,
    },
    Adjoint {
        operation: StaticOp,
        input: Box<Expr>,
    },
    RepeatStatic {
        count: u16,
        function: Ident,
        input: Box<Expr>,
    },
    QuantumIf {
        control: Box<Expr>,
        target: Box<Expr>,
        zero: Ident,
        one: Ident,
    },
    Controlled {
        operation: StaticOp,
        args: Vec<Expr>,
    },
    StaticIf {
        predicate: Predicate,
        then_branch: Block,
        else_branch: Block,
    },
    StaticFold {
        /// True for explicit quantum-owner threading; false for ordinary carry.
        quantum: bool,
        index: Ident,
        start: Natural,
        end: Natural,
        carry: Pattern,
        initial: Box<Expr>,
        body: Block,
    },
    Name(Ident),
    Bit(bool),
    Unit,
    Tuple(Vec<Expr>),
    Not(Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Xor(Box<Expr>, Box<Expr>),
    Call {
        callee: Ident,
        static_args: Vec<StaticOp>,
        args: Vec<Expr>,
    },
    If {
        condition: Box<Expr>,
        then_branch: Block,
        else_branch: Block,
    },
    CoherentLift {
        binder: Pattern,
        input: Box<Expr>,
        basis: BasisExpr,
    },
    WithComputed {
        source: Box<Expr>,
        function: Ident,
        binder: Ident,
        body: Block,
    },
    CertifiedComputed {
        source: Box<Expr>,
        function: Ident,
        // Keep the expression enum small: the parser bounds nesting, and
        // adding several inline identifiers would inflate every stack frame.
        logical: Box<Ident>,
        data_binder: Box<Ident>,
        ancilla_binder: Box<Ident>,
        body: Block,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Access {
    Apply,
    Adjoint,
    Controlled,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AccessConstraint {
    pub span: Span,
    pub access: Access,
    pub name: Ident,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StaticParam {
    pub name: Ident,
    pub kind: StaticParamKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StaticParamKind {
    Natural,
    Basis,
    Operation { basis: Type, meaning: Option<Ident> },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Requirement {
    Access(AccessConstraint),
    Predicate(Predicate),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StaticOp {
    pub kind: StaticOpKind,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StaticOpKind {
    Name(Ident),
    Type(Type),
    Bind {
        implementation: Ident,
        meaning: Ident,
    },
    Inverse(Box<StaticOp>),
    Then(Box<StaticOp>, Box<StaticOp>),
    Tensor(Box<StaticOp>, Box<StaticOp>),
    Controlled(Box<StaticOp>),
    Repeat(Count, Box<StaticOp>),
    Natural(Natural),
    Specialize {
        name: Ident,
        arguments: Vec<StaticOp>,
    },
    Conjugate(Box<StaticOp>, Box<StaticOp>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BasisExpr {
    pub kind: BasisExprKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BasisExprKind {
    Name(Ident),
    Bit(bool),
    Unit,
    Tuple(Vec<BasisExpr>),
    Call { callee: Ident, args: Vec<BasisExpr> },
    Not(Box<BasisExpr>),
    Xor(Box<BasisExpr>, Box<BasisExpr>),
    And(Box<BasisExpr>, Box<BasisExpr>),
}

/// Symbolic natural syntax, with a bounded tree depth; not a checked size.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Natural {
    pub kind: NatKind,
    pub span: Span,
    pub depth: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NatKind {
    Call {
        callee: Ident,
        arguments: Vec<Natural>,
    },
    Number(i128),
    Name(String),
    Add(Box<Natural>, Box<Natural>),
    Sub(Box<Natural>, Box<Natural>),
    Mul(Box<Natural>, Box<Natural>),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Compare {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Predicate {
    pub left: Natural,
    pub comparison: Compare,
    pub right: Natural,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Count {
    Natural(Natural),
    Power(Natural),
}

/// The direct literal named-function repetition profile. This classification
/// does not grant static-provider access or validate the count or target.
pub(crate) fn named_literal_repetition(operation: &StaticOp) -> Option<(&Ident, i128, Span)> {
    let StaticOpKind::Repeat(Count::Natural(count), target) = &operation.kind else {
        return None;
    };
    let (StaticOpKind::Name(name), NatKind::Number(number)) = (&target.kind, &count.kind) else {
        return None;
    };
    Some((name, *number, count.span))
}
