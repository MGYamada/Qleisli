//! Shared runtime pattern-binding rules; no value here is acceptance evidence.
//!
//! The borrowed view temporarily bridges the existing sized projection. It
//! neither creates a second pattern tree nor changes lexical binder identities.

use super::ast::{Ident, Pattern, PatternKind, Span};
use super::types::Type;
use std::borrow::Cow;
use std::collections::BTreeSet;

pub(super) enum Node<'a, P: PatternView> {
    Wildcard(Span),
    Name(&'a P::Name, Span),
    Tuple(&'a [P], Span),
}

pub(super) trait PatternView: Sized {
    type Name;
    fn node(&self) -> Node<'_, Self>;
    fn spelling(name: &Self::Name) -> &str;
}

impl PatternView for Pattern {
    type Name = Ident;

    fn node(&self) -> Node<'_, Self> {
        match &self.kind {
            PatternKind::Wildcard => Node::Wildcard(self.span),
            PatternKind::Name(name) => Node::Name(name, name.span),
            PatternKind::Tuple(fields) => Node::Tuple(fields, self.span),
        }
    }

    fn spelling(name: &Self::Name) -> &str {
        &name.text
    }
}

/// Payload storage, located diagnostics and existing accounting stay with the
/// consumer. The shared traversal selects the wildcard/name/shape judgments.
pub(super) trait BindingContext<P: PatternView> {
    type Value;
    type Size: Clone;
    type Error;

    fn linear(&self, value: &Self::Value) -> bool;
    fn pattern_type<'v>(&self, value: &'v Self::Value) -> Cow<'v, Type<Self::Size>>;
    fn consume_fields(&mut self, value: Self::Value) -> Vec<Self::Value>;
    fn bind_name(
        &mut self,
        name: &P::Name,
        span: Span,
        value: Self::Value,
    ) -> Result<(), Self::Error>;
    fn wildcard_error(&self, span: Span) -> Self::Error;
    fn duplicate_error(&self, span: Span) -> Self::Error;
    fn shape_error(
        &self,
        span: Span,
        arity: usize,
        value: &Self::Value,
        actual: &Type<Self::Size>,
    ) -> Self::Error;
}

/// Bind one already typed value in source order using the caller's existing
/// duplicate-name scope. No payload type is rebuilt for a wildcard or name.
pub(super) fn bind<P, C>(
    pattern: &P,
    value: C::Value,
    names: &mut BTreeSet<String>,
    context: &mut C,
) -> Result<(), C::Error>
where
    P: PatternView,
    C: BindingContext<P>,
{
    match pattern.node() {
        Node::Wildcard(span) => {
            if context.linear(&value) {
                return Err(context.wildcard_error(span));
            }
        }
        Node::Name(name, span) => {
            if !names.insert(P::spelling(name).to_owned()) {
                return Err(context.duplicate_error(span));
            }
            context.bind_name(name, span, value)?;
        }
        Node::Tuple(patterns, span) => {
            let actual = context.pattern_type(&value);
            if actual.pattern_fields(patterns.len()).is_none() {
                return Err(context.shape_error(span, patterns.len(), &value, &actual));
            }
            if patterns.is_empty() {
                // The shared shape check established ordinary Unit, never Q
                // or an empty tuple. Earlier expression effects stay intact.
                return Ok(());
            }
            drop(actual);
            let fields = context.consume_fields(value);
            for (pattern, field) in patterns.iter().zip(fields) {
                bind(pattern, field, names, context)?;
            }
        }
    }
    Ok(())
}
