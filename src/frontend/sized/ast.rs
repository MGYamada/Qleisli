//! Temporary checked-profile projection of the common source AST; never evidence.
//! No parser or source-token interpretation belongs here.
use super::Span;

pub(super) use crate::frontend::ast::Compare;
pub(super) use crate::frontend::ordinary::Boolean;
use crate::frontend::pattern::{Node as PatternNode, PatternView};
use crate::frontend::resolve::locals::UseSiteId;
pub(super) use crate::frontend::resolve::locals::{BinderKey, ResolvedUse, Table};
use std::sync::Arc;

/// Original numeric identities, copied only after complete source checking.
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
pub(super) use crate::ir::Effect;
#[derive(Clone, Debug)]
pub(super) enum Argument {
    Natural(Natural),
    Basis(Basis, Span),
    Definition(Reference, Vec<Argument>, Span),
    Repeat(Count, Box<Argument>, Span),
}
#[derive(Clone, Debug)]
pub(super) enum Pattern {
    Name(BindingName, Span),
    Wildcard(Span),
    Tuple(Vec<Pattern>, Span),
}
// A borrowed bridge over the existing projection, not another AST or cache.
impl PatternView for Pattern {
    type Name = BindingName;

    fn node(&self) -> PatternNode<'_, Self> {
        match self {
            Self::Name(name, span) => PatternNode::Name(name, *span),
            Self::Wildcard(span) => PatternNode::Wildcard(*span),
            Self::Tuple(fields, span) => PatternNode::Tuple(fields, *span),
        }
    }

    fn spelling(name: &BindingName) -> &str {
        &name.name
    }
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
    StaticLet(BindingName, Natural),
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
    pub effect: Effect,
    /// Patterns belong only to concrete body lowering. Interface types and
    /// static categories come from the common original-source judgment.
    pub arguments: Vec<(Pattern, Span)>,
    pub body: Block,
    pub span: Span,
}
