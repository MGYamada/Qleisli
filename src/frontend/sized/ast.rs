//! Temporary checked-profile projection of the common source AST; never evidence.
//! No parser or source-token interpretation belongs here.
use super::Span;

pub(super) use crate::frontend::ast::{Compare, Count, NatKind, Natural, Predicate};

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
