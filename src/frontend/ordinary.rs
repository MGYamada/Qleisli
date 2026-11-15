//! Shared ordinary Boolean checking, eager operand order and untrusted Raw IR.
//! Native acceptance and source-preservation validation remain independent.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

pub(super) mod finite;

use super::ast::{BasisExpr, BasisExprKind, Ident};
use super::types::{Kind, Type};
use crate::interchange::{Error, carrier::Atom};
use crate::ir::{ClassicalId, RawOp};

/// Allocation-free view of an original finite classical expression. Both
/// runtime consumers use ordinary operations while retaining the original
/// Ident addresses required by the one checked lexical occurrence table.
/// Consumers charge their existing traversal/allocation budgets; this view
/// creates no second source tree, truth table, acceptance or evidence.
pub(crate) enum RuntimeExpression<'a> {
    /// Common typing is available; nominal execution needs its typed transport.
    Nominal,
    Name(&'a Ident),
    Unit,
    Tuple(&'a [BasisExpr]),
    BitIndex {
        receiver: &'a BasisExpr,
        index: usize,
    },
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
        BasisExprKind::Variant(_)
        | BasisExprKind::Record(_)
        | BasisExprKind::Field { .. }
        | BasisExprKind::Match(_) => RuntimeExpression::Nominal,
        BasisExprKind::Name(name) => RuntimeExpression::Name(name),
        BasisExprKind::Unit => RuntimeExpression::Unit,
        BasisExprKind::Tuple(fields) => RuntimeExpression::Tuple(fields),
        BasisExprKind::BitIndex {
            receiver, index, ..
        } => RuntimeExpression::BitIndex {
            receiver,
            index: *index as usize,
        },
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

/// Deterministic producer coordinates for one finite type forest.
/// The independent native carrier reader checks the original type and codes.
pub(in crate::frontend) fn proposed_codes(
    parameters: &[Vec<Atom>],
) -> Result<(usize, Vec<usize>), Error> {
    type Layout = (usize, Vec<usize>);
    fn tensor((low_bits, low): Layout, (high_bits, high): Layout) -> Result<Layout, Error> {
        if low_bits + high_bits > 6 || low.len() * high.len() > 64 {
            return Err(limit("ordinary input domain exceeds six bits or 64 rows"));
        }
        let rows = high
            .into_iter()
            .flat_map(|high| low.iter().map(move |low| low + (high << low_bits)))
            .collect();
        Ok((low_bits + high_bits, rows))
    }
    if parameters.len() > 64 || parameters.iter().map(Vec::len).sum::<usize>() > 128 {
        return Err(limit("ordinary parameter forest exceeds capacity"));
    }
    let mut domain = (0, vec![0]);
    for basis in parameters {
        let mut stack: Vec<Layout> = Vec::new();
        for atom in basis.iter().rev() {
            let arity = match atom {
                Atom::Pair => Some(2),
                Atom::Tuple(arity) => Some(*arity as usize),
                Atom::Record(_, fields) => Some(fields.len()),
                _ => None,
            };
            if let Some(arity) = arity {
                if arity > stack.len() {
                    return Err(invalid("incomplete parameter type tree"));
                }
                let mut combined = (0, vec![0]);
                for _ in 0..arity {
                    combined = tensor(combined, stack.pop().unwrap())?;
                }
                stack.push(combined);
            } else {
                let (bits, count) = match atom {
                    Atom::Unit => (0, 1),
                    Atom::Bit => (1, 2),
                    Atom::Bits(width) if *width <= 6 => (*width as usize, 1usize << width),
                    Atom::Enum(_, labels) if !labels.is_empty() && labels.len() <= 64 => (
                        usize::BITS as usize - (labels.len() - 1).leading_zeros() as usize,
                        labels.len(),
                    ),
                    _ => return Err(limit("unsupported ordinary parameter code")),
                };
                stack.push((bits, (0..count).collect()));
            }
        }
        if stack.len() != 1 {
            return Err(invalid("incomplete parameter type forest"));
        }
        domain = tensor(domain, stack.pop().unwrap())?;
    }
    Ok(domain)
}

fn invalid(message: &str) -> Error {
    Error::new("format", message)
}

fn limit(message: &str) -> Error {
    Error::new("limit", message)
}
