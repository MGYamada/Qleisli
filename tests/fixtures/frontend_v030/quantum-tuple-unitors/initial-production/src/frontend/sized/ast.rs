//! Temporary checked-profile projection of the common source AST; never evidence.
//! No parser or source-token interpretation belongs here.
use super::Span;

pub(super) use crate::frontend::ast::Compare;
pub(super) use crate::frontend::ordinary::Boolean;
use crate::frontend::resolve::locals::UseSiteId;
pub(super) use crate::frontend::resolve::locals::{BinderKey, ResolvedUse, Table};
use std::sync::Arc;

/// IDs are absent only in the discarded profile preflight projection.
#[derive(Clone, Debug)]
pub(super) struct BindingName {
    pub name: String,
    pub key: Option<BinderKey>,
    pub shadowed: Option<BinderKey>,
}
impl BindingName {
    pub fn key(&self) -> &BinderKey {
        self.key.as_ref().expect("indexed sized binder")
    }
}
impl std::fmt::Display for BindingName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name.fmt(f)
    }
}
#[derive(Clone, Debug)]
pub(super) struct Reference {
    pub name: String,
    pub site: Option<UseSiteId>,
    pub local: Option<BinderKey>,
}
impl Reference {
    pub fn target(&self, table: &Table) -> ResolvedUse {
        table.usage(self.site.expect("indexed sized use")).target
    }
    pub fn get<'a, T>(
        &self,
        bindings: &'a std::collections::BTreeMap<BinderKey, T>,
    ) -> Option<&'a T> {
        self.local.as_ref().and_then(|key| bindings.get(key))
    }
}
impl std::fmt::Display for Reference {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name.fmt(f)
    }
}
#[derive(Clone, Debug)]
pub(super) struct Natural {
    pub kind: NatKind,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub(super) enum NatKind {
    Number(i128),
    Name(Reference),
    Add(Box<Natural>, Box<Natural>),
    Sub(Box<Natural>, Box<Natural>),
    Mul(Box<Natural>, Box<Natural>),
}
#[derive(Clone, Debug)]
pub(super) struct Predicate {
    pub left: Natural,
    pub comparison: Compare,
    pub right: Natural,
}
#[derive(Clone, Debug)]
pub(super) enum Count {
    Natural(Natural),
    Power(Natural),
}

pub(super) type Type = crate::frontend::types::Type<Natural>;
/// The common exact type tree, projected specifically in the basis stage.
pub(super) type Basis = Type;
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Effect {
    Unitary,
    Iso,
    Observe,
}
#[derive(Clone, Debug)]
pub(super) enum Parameter {
    Natural(BindingName),
    Operation(BindingName, Basis),
}
#[derive(Clone, Debug)]
pub(super) enum Requirement {
    Predicate(Predicate),
    Access(String, Reference, Span),
}
#[derive(Clone, Debug)]
pub(super) enum Argument {
    Natural(Natural),
    Definition(Reference, Vec<Argument>, Span),
    Repeat(Count, Box<Argument>, Span),
}
#[derive(Clone, Debug)]
pub(super) enum Pattern {
    Name(BindingName, Span),
    Wildcard(Span),
    Tuple(Vec<Pattern>, Span),
}
#[derive(Clone, Debug)]
pub(super) struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub(super) enum ExprKind {
    Unit,
    Boolean(Boolean, Vec<Expr>),
    Name(Reference),
    Tuple(Vec<Expr>),
    Call(Reference, Vec<Argument>, Vec<Expr>),
    Adjoint(Argument, Box<Expr>),
    Controlled(Argument, Vec<Expr>),
    If(Predicate, Block, Block),
    Fold {
        index: BindingName,
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
    pub lexical: Option<Arc<Table>>,
    pub name: String,
    pub effect: Effect,
    pub parameters: Vec<Parameter>,
    /// One pattern and whole type per source argument; never flattened binders.
    pub arguments: Vec<(Pattern, Type, Span)>,
    pub result: Type,
    pub requires: Vec<Requirement>,
    pub body: Block,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub(super) struct Module {
    /// Exactly one projection per common declaration, in original source order.
    pub functions: Vec<Function>,
}
