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
    Basis,
    Iso,
    Unitary,
    Observe,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decl {
    pub public: bool,
    pub kind: FnKind,
    pub name: Ident,
    pub params: Vec<Param>,
    pub return_type: Type,
    pub body: FnBody,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Param {
    pub name: Ident,
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
    CBit,
    Q(Box<Type>),
    Tuple(Box<Type>, Box<Type>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FnBody {
    Basis(BasisExpr),
    Quantum(Block),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
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
    Tuple(Box<Pattern>, Box<Pattern>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprKind {
    Name(Ident),
    Unit,
    Tuple(Box<Expr>, Box<Expr>),
    Call {
        callee: Ident,
        args: Vec<Expr>,
    },
    If {
        condition: Box<Expr>,
        then_branch: Block,
        else_branch: Block,
    },
    CoherentLift {
        binder: Ident,
        input: Box<Expr>,
        basis: BasisExpr,
    },
    WithComputed {
        source: Box<Expr>,
        function: Ident,
        binder: Ident,
        body: Block,
    },
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
    Tuple(Box<BasisExpr>, Box<BasisExpr>),
    Call { callee: Ident, args: Vec<BasisExpr> },
    Not(Box<BasisExpr>),
    Xor(Box<BasisExpr>, Box<BasisExpr>),
    And(Box<BasisExpr>, Box<BasisExpr>),
}
