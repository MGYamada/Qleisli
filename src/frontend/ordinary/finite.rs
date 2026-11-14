//! Shared finite-label evaluation of the original ordinary expression tree.
//! Contexts retain type/identity checks and charge before copying or allocation.
//! A computed label or table is untrusted data, never native acceptance evidence.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::Boolean;
use crate::frontend::ast::{BasisExpr, BasisExprKind, Ident, Span, VariantValue};
use crate::frontend::types::{
    Kind, Type,
    nominal::{Body, Field, Nominal},
};

#[derive(Clone, Debug)]
pub(in crate::frontend) struct Label {
    pub ty: Type<u32>,
    pub label: u16,
}

pub(in crate::frontend) trait NominalContext: Context<Value = Label> {
    fn enum_label(&mut self, value: &VariantValue) -> Result<(Type<u32>, usize), Self::Error>;
    fn nominal_type(&mut self, name: &Ident) -> Result<Type<u32>, Self::Error>;
    fn record_index(
        &mut self,
        nominal: &Nominal<u32>,
        fields: &[Field<u32>],
        name: &Ident,
    ) -> Result<usize, Self::Error>;
    fn charge(&mut self, span: Span, cells: usize) -> Result<(), Self::Error>;
    fn copy_type(&mut self, span: Span, ty: &Type<u32>) -> Result<Type<u32>, Self::Error>;
    fn width(&mut self, span: Span, ty: &Type<u32>) -> Result<usize, Self::Error>;
    fn same_type(
        &mut self,
        span: Span,
        actual: &Type<u32>,
        expected: &Type<u32>,
    ) -> Result<(), Self::Error>;
    fn invalid_nominal(&self, span: Span) -> Self::Error;
}

pub(in crate::frontend) trait Context {
    type Value;
    type Environment;
    type Tuple;
    type Error;
    fn enter(&mut self, span: Span, depth: usize) -> Result<(), Self::Error>;
    fn nominal_unavailable(&mut self, span: Span) -> Self::Error;
    fn nominal(
        &mut self,
        expression: &BasisExpr,
        _env: &Self::Environment,
        _depth: usize,
    ) -> Result<Self::Value, Self::Error> {
        Err(self.nominal_unavailable(expression.span))
    }
    fn name(&mut self, name: &Ident, env: &Self::Environment) -> Result<Self::Value, Self::Error>;
    fn unit(&mut self) -> Self::Value;
    fn bit(&mut self, value: bool) -> Self::Value;
    fn bit_index(
        &mut self,
        span: Span,
        value: Self::Value,
        index: u32,
    ) -> Result<Self::Value, Self::Error>;
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
        BasisExprKind::Variant(_)
        | BasisExprKind::Record(_)
        | BasisExprKind::Field { .. }
        | BasisExprKind::Match(_) => context.nominal(expr, env, depth)?,
        BasisExprKind::Name(name) => context.name(name, env)?,
        BasisExprKind::Unit => context.unit(),
        BasisExprKind::Bit(value) => context.bit(*value),
        BasisExprKind::BitIndex {
            receiver,
            index,
            index_span,
        } => {
            let word = evaluate(context, receiver, env, depth + 1)?;
            context.bit_index(*index_span, word, *index)?
        }
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

pub(in crate::frontend) fn label_bit_index(value: &Label, index: u32) -> Option<bool> {
    match value.ty.kind {
        Kind::Bits(width) if index < width => Some(value.label.checked_shr(index)? & 1 != 0),
        _ => None,
    }
}

/// Evaluate nominal values and choose the matching declaration ordinal.
pub(in crate::frontend) fn nominal<C: NominalContext>(
    context: &mut C,
    expr: &BasisExpr,
    env: &C::Environment,
    depth: usize,
) -> Result<Label, C::Error> {
    match &expr.kind {
        BasisExprKind::Variant(variant) => {
            let (ty, ordinal) = context.enum_label(variant)?;
            context.width(expr.span, &ty)?;
            Ok(Label {
                ty,
                label: ordinal as u16,
            })
        }
        BasisExprKind::Record(record) => {
            let ty = context.nominal_type(&record.type_name)?;
            context.width(expr.span, &ty)?;
            let Kind::Nominal(nominal) = &ty.kind else {
                return Err(context.invalid_nominal(expr.span));
            };
            let Body::Record(fields) = &nominal.body else {
                return Err(context.invalid_nominal(expr.span));
            };
            context.charge(expr.span, fields.len() + record.fields.len() + 1)?;
            let mut values = vec![None; fields.len()];
            for field in &record.fields {
                let index = context.record_index(nominal, fields, &field.name)?;
                if values[index].is_some() {
                    return Err(context.invalid_nominal(expr.span));
                }
                let value = evaluate(context, &field.value, env, depth + 1)?;
                context.same_type(field.span, &value.ty, &fields[index].ty)?;
                values[index] = Some(value.label);
            }
            let mut label = 0;
            let mut offset = 0;
            for (field, value) in fields.iter().zip(values) {
                let Some(value) = value else {
                    return Err(context.invalid_nominal(expr.span));
                };
                label |= value << offset;
                offset += context.width(expr.span, &field.ty)?;
            }
            Ok(Label { ty, label })
        }
        BasisExprKind::Field { receiver, field } => {
            let value = evaluate(context, receiver, env, depth + 1)?;
            let Kind::Nominal(nominal) = &value.ty.kind else {
                return Err(context.invalid_nominal(expr.span));
            };
            let Body::Record(fields) = &nominal.body else {
                return Err(context.invalid_nominal(expr.span));
            };
            let index = context.record_index(nominal, fields, field)?;
            let mut offset = 0;
            for previous in &fields[..index] {
                offset += context.width(expr.span, &previous.ty)?;
            }
            let ty = &fields[index].ty;
            let width = context.width(expr.span, ty)?;
            Ok(Label {
                ty: context.copy_type(expr.span, ty)?,
                label: (value.label >> offset) & ((1u16 << width) - 1),
            })
        }
        BasisExprKind::Match(selection) => {
            let value = evaluate(context, &selection.scrutinee, env, depth + 1)?;
            // The complete common judgment already checks exhaustiveness,
            // duplicates, and every arm's type. Select by declaration ordinal.
            for arm in &selection.arms {
                let (ty, ordinal) = context.enum_label(&arm.label)?;
                context.same_type(arm.span, &value.ty, &ty)?;
                if usize::from(value.label) == ordinal {
                    return evaluate(context, &arm.body, env, depth + 1);
                }
            }
            Err(context.invalid_nominal(expr.span))
        }
        _ => unreachable!("only ordinary nominal forms dispatch here"),
    }
}
