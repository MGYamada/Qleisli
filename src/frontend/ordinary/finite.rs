//! Shared finite-label evaluation of the original ordinary expression tree.
//! Contexts retain type/identity checks and charge before copying or allocation.
//! A computed label or table is untrusted data, never native acceptance evidence.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
use super::Boolean;
use crate::frontend::ast::{BasisExpr, BasisExprKind, Ident, Span};

pub(in crate::frontend) trait Context {
    type Value;
    type Environment;
    type Tuple;
    type Error;
    fn enter(&mut self, span: Span, depth: usize) -> Result<(), Self::Error>;
    fn name(&mut self, name: &Ident, env: &Self::Environment) -> Result<Self::Value, Self::Error>;
    fn unit(&mut self) -> Self::Value;
    fn bit(&mut self, value: bool) -> Self::Value;
    fn tuple(&mut self, fields: usize) -> Self::Tuple;
    fn push(
        &mut self,
        span: Span,
        tuple: &mut Self::Tuple,
        value: Self::Value,
    ) -> Result<(), Self::Error>;
    fn product(&mut self, tuple: Self::Tuple) -> Self::Value;
    fn require_bit(&mut self, span: Span, value: &Self::Value) -> Result<(), Self::Error>;
    fn boolean(
        &mut self,
        operation: Boolean,
        a: Self::Value,
        b: Option<Self::Value>,
    ) -> Self::Value;
    fn call(
        &mut self,
        span: Span,
        callee: &Ident,
        args: &[BasisExpr],
        env: &Self::Environment,
        depth: usize,
    ) -> Result<Self::Value, Self::Error>;
    fn finish(&mut self, span: Span, value: Self::Value) -> Result<Self::Value, Self::Error>;
}

/// Traverse the original AST eagerly in source order. In particular an AND
/// always evaluates its right operand; result shape/width is checked at each
/// product field, before evaluating the next field or shifting its label.
pub(in crate::frontend) fn evaluate<C: Context>(
    context: &mut C,
    expr: &BasisExpr,
    env: &C::Environment,
    depth: usize,
) -> Result<C::Value, C::Error> {
    context.enter(expr.span, depth)?;
    let value = match &expr.kind {
        BasisExprKind::Name(name) => context.name(name, env)?,
        BasisExprKind::Unit => context.unit(),
        BasisExprKind::Bit(value) => context.bit(*value),
        BasisExprKind::Tuple(fields) => {
            let mut tuple = context.tuple(fields.len());
            for field in fields {
                let value = evaluate(context, field, env, depth + 1)?;
                context.push(expr.span, &mut tuple, value)?;
            }
            context.product(tuple)
        }
        BasisExprKind::Not(input) => {
            let input = evaluate(context, input, env, depth + 1)?;
            context.require_bit(expr.span, &input)?;
            context.boolean(Boolean::Not, input, None)
        }
        BasisExprKind::And(a, b) | BasisExprKind::Xor(a, b) => {
            let a = evaluate(context, a, env, depth + 1)?;
            let b = evaluate(context, b, env, depth + 1)?;
            context.require_bit(expr.span, &a)?;
            context.require_bit(expr.span, &b)?;
            context.boolean(
                if matches!(expr.kind, BasisExprKind::And(..)) {
                    Boolean::And
                } else {
                    Boolean::Xor
                },
                a,
                Some(b),
            )
        }
        BasisExprKind::Call { callee, args } => {
            context.call(expr.span, callee, args, env, depth)?
        }
    };
    context.finish(expr.span, value)
}
