//! Shared ordinary Boolean checking, eager operand order and untrusted Raw IR.
//! Native acceptance and source-preservation validation remain independent.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

pub(super) mod finite;

use super::ast::{BasisExpr, BasisExprKind, Ident};
use super::types::{Kind, Type};
use crate::ir::{ClassicalId, RawOp};

/// Allocation-free view of an original finite classical expression. Both
/// runtime consumers use ordinary operations while retaining the original
/// Ident addresses required by the one checked lexical occurrence table.
/// Consumers charge their existing traversal/allocation budgets; this view
/// creates no second source tree, truth table, acceptance or evidence.
pub(crate) enum RuntimeExpression<'a> {
    Name(&'a Ident),
    Unit,
    Tuple(&'a [BasisExpr]),
    Call {
        callee: &'a Ident,
        args: &'a [BasisExpr],
    },
    Boolean {
        operation: Boolean,
        inputs: [Option<&'a BasisExpr>; 2],
    },
}

pub(crate) fn runtime_expression(expr: &BasisExpr) -> RuntimeExpression<'_> {
    match &expr.kind {
        BasisExprKind::Name(name) => RuntimeExpression::Name(name),
        BasisExprKind::Unit => RuntimeExpression::Unit,
        BasisExprKind::Tuple(fields) => RuntimeExpression::Tuple(fields),
        BasisExprKind::Call { callee, args } => RuntimeExpression::Call { callee, args },
        BasisExprKind::Bit(value) => RuntimeExpression::Boolean {
            operation: Boolean::Constant(*value),
            inputs: [None, None],
        },
        BasisExprKind::Not(input) => RuntimeExpression::Boolean {
            operation: Boolean::Not,
            inputs: [Some(input), None],
        },
        BasisExprKind::And(left, right) => RuntimeExpression::Boolean {
            operation: Boolean::And,
            inputs: [Some(left), Some(right)],
        },
        BasisExprKind::Xor(left, right) => RuntimeExpression::Boolean {
            operation: Boolean::Xor,
            inputs: [Some(left), Some(right)],
        },
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Boolean {
    Constant(bool),
    Not,
    And,
    Xor,
}

impl Boolean {
    pub(crate) fn arity(self) -> usize {
        match self {
            Self::Constant(_) => 0,
            Self::Not => 1,
            Self::And | Self::Xor => 2,
        }
    }

    pub(crate) fn operator(self) -> &'static str {
        match self {
            Self::Constant(_) => "constant",
            Self::Not => "not",
            Self::And => "and",
            Self::Xor => "xor",
        }
    }

    pub(crate) fn result_type<N>(self) -> Type<N> {
        Type::bit()
    }
}

pub(crate) enum OperandFailure<N> {
    Arity { expected: usize, actual: usize },
    Type(Type<N>),
}

/// Evaluate and check each operand before proceeding to the next one. In
/// particular, an AND operand's value cannot skip evaluation of its sibling.
/// Context adapters own effects, ownership and diagnostics; this judgment owns
/// argument count and exact ordinary Bit typing (never Bits<1> or Q<Bit>).
pub(crate) fn evaluate<C, X, V, N, E>(
    operation: Boolean,
    operands: impl ExactSizeIterator<Item = X>,
    context: &mut C,
    mut evaluate: impl FnMut(&mut C, X) -> Result<V, E>,
    type_of: impl Fn(&V) -> Type<N>,
    mut failure: impl FnMut(&mut C, OperandFailure<N>) -> E,
) -> Result<Vec<V>, E> {
    if operands.len() != operation.arity() {
        return Err(failure(
            context,
            OperandFailure::Arity {
                expected: operation.arity(),
                actual: operands.len(),
            },
        ));
    }
    let mut values = Vec::with_capacity(operation.arity());
    for operand in operands {
        let value = evaluate(context, operand)?;
        let ty = type_of(&value);
        if !matches!(&ty.kind, Kind::Bit) {
            return Err(failure(context, OperandFailure::Type(ty)));
        }
        values.push(value);
    }
    Ok(values)
}

/// Construct one untrusted instruction using the caller's fresh output ID.
/// A malformed operand list is rejected, never truncated or padded.
pub(crate) fn emit(
    operation: Boolean,
    inputs: &[ClassicalId],
    output: ClassicalId,
) -> Option<RawOp> {
    Some(match (operation, inputs) {
        (Boolean::Constant(value), []) => RawOp::ClassicalConst { value, output },
        (Boolean::Not, [input]) => RawOp::ClassicalNot {
            input: *input,
            output,
        },
        (Boolean::And, [left, right]) => RawOp::ClassicalAnd {
            left: *left,
            right: *right,
            output,
        },
        (Boolean::Xor, [left, right]) => RawOp::ClassicalXor {
            left: *left,
            right: *right,
            output,
        },
        _ => return None,
    })
}
