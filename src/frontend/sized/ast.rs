//! Private source representation; never verification evidence.
use super::Span;

#[derive(Clone, Debug)]
pub(super) struct Natural {
    pub kind: NatKind,
    pub span: Span,
    pub depth: usize,
}
#[derive(Clone, Debug)]
pub(super) enum NatKind {
    Number(i128),
    Name(String),
    Add(Box<Natural>, Box<Natural>),
    Sub(Box<Natural>, Box<Natural>),
    Mul(Box<Natural>, Box<Natural>),
}
#[derive(Clone, Debug)]
pub(super) enum Basis {
    Bit,
    Bits(Natural),
}
#[derive(Clone, Debug)]
pub(super) enum Type {
    Quantum(Basis),
    CBit,
    CBits(Natural),
    Tuple(Vec<Type>),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Effect {
    Unitary,
    Iso,
    Observe,
}
#[derive(Clone, Debug)]
pub(super) enum Parameter {
    Natural(String),
    Operation(String, Basis),
}
#[derive(Clone, Copy, Debug)]
pub(super) enum Compare {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}
#[derive(Clone, Debug)]
pub(super) struct Predicate {
    pub left: Natural,
    pub comparison: Compare,
    pub right: Natural,
}
#[derive(Clone, Debug)]
pub(super) enum Requirement {
    Predicate(Predicate),
    Access(String, String, Span),
}
#[derive(Clone, Debug)]
pub(super) enum Argument {
    Natural(Natural),
    Definition(String, Vec<Argument>, Span),
    Repeat(Count, Box<Argument>, Span),
}
#[derive(Clone, Debug)]
pub(super) enum Count {
    Natural(Natural),
    Power(Natural),
}
#[derive(Clone, Debug)]
pub(super) enum Pattern {
    Name(String, Span),
    Tuple(Vec<Pattern>, Span),
}
#[derive(Clone, Debug)]
pub(super) struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub(super) enum ExprKind {
    Name(String),
    Tuple(Vec<Expr>),
    Call(String, Vec<Argument>, Vec<Expr>),
    Adjoint(Argument, Box<Expr>),
    Controlled(Argument, Vec<Expr>),
    If(Predicate, Block, Block),
    Fold {
        index: String,
        start: Natural,
        end: Natural,
        carry: Pattern,
        initial: Box<Expr>,
        body: Block,
    },
}
#[derive(Clone, Debug)]
pub(super) enum Statement {
    Let(Pattern, Expr),
    Drop(Expr),
}
#[derive(Clone, Debug)]
pub(super) struct Block {
    pub statements: Vec<Statement>,
    pub result: Box<Expr>,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub(super) struct Function {
    pub name: String,
    pub public: bool,
    pub effect: Effect,
    pub parameters: Vec<Parameter>,
    pub arguments: Vec<(String, Type, Span)>,
    pub result: Type,
    pub requires: Vec<Requirement>,
    pub body: Block,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub(super) struct Module {
    pub imports: Vec<(String, Span)>,
    pub function: Function,
}
