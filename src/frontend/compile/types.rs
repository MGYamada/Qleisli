//! Copy an exact checked type into the existing finite representation.
//! Source syntax supplies diagnostic locations only; copying grants no evidence.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FailureKind {
    TreeLimit,
    WorkOverflow,
    BasisWidth,
    NonzeroRegister,
    Parameter,
    QuantumBasis,
    TupleArity,
    TupleLimit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Failure {
    span: Span,
    kind: FailureKind,
}

impl Failure {
    fn at(original: &Type, kind: FailureKind) -> Self {
        Self {
            span: original.span,
            kind,
        }
    }

    fn compile(self, compiler: &Compiler<'_>, module: &str) -> CompileError {
        let (code, message) = match self.kind {
            FailureKind::TreeLimit => (
                ErrorCode::Limit,
                format!("internal value or type exceeds the initial {MAX_TREE_NODES}-node / {MAX_TREE_DEPTH}-level limit"),
            ),
            FailureKind::WorkOverflow => (
                ErrorCode::Limit,
                "finite type copy work accounting overflow".to_owned(),
            ),
            FailureKind::BasisWidth => (
                ErrorCode::Limit,
                "basis type exceeds the initial 12-bit limit".to_owned(),
            ),
            FailureKind::NonzeroRegister => (
                ErrorCode::Unsupported,
                "nonzero register types are outside the finite lowering profile; only Bits<0> is supported".to_owned(),
            ),
            FailureKind::Parameter => (
                ErrorCode::Unsupported,
                "named Basis types are outside the finite lowering profile".to_owned(),
            ),
            FailureKind::QuantumBasis => (
                ErrorCode::TypeMismatch,
                "finite Basis type cannot contain quantum ownership".to_owned(),
            ),
            FailureKind::TupleArity => (
                ErrorCode::TypeMismatch,
                "finite tuple requires at least two fields".to_owned(),
            ),
            FailureKind::TupleLimit => (
                ErrorCode::Limit,
                "finite tuple exceeds 64 fields".to_owned(),
            ),
        };
        compiler.error(module, self.span, code, message)
    }
}

#[derive(Clone, Copy, Debug)]
struct Measured {
    nodes: usize,
    copy_work: usize,
    basis_bits: Option<usize>,
}

fn original_basis(original: &Type) -> &Type {
    match &original.kind {
        TypeKind::Q(basis) => basis,
        _ => original,
    }
}

fn original_field(original: &Type, arity: usize, ordinal: usize) -> &Type {
    match &original.kind {
        TypeKind::Tuple(fields) if fields.len() == arity => fields.get(ordinal).unwrap_or(original),
        _ => original,
    }
}

/// This bounded preflight uses only borrowed nodes and fixed-size stack frames.
/// It creates no temporary Vec, Box or copied type. The total copy charge is
/// exactly the former sum of subtree.tree_size().nodes over every copied node.
fn measure<N: FiniteRegisterSize>(
    original: &Type,
    checked: &crate::frontend::types::Type<N>,
    stage: Stage,
    depth: usize,
    visited: &mut usize,
) -> Result<Measured, Failure> {
    if depth > MAX_TREE_DEPTH || *visited >= MAX_TREE_NODES {
        return Err(Failure::at(original, FailureKind::TreeLimit));
    }
    *visited += 1;
    let result = match &checked.kind {
        Kind::Unit => Measured {
            nodes: 1,
            copy_work: 1,
            basis_bits: Some(0),
        },
        Kind::Bit => Measured {
            nodes: 1,
            copy_work: 1,
            basis_bits: Some(1),
        },
        Kind::Bits(size) => {
            if !size.is_exact_zero() {
                return Err(Failure::at(original, FailureKind::NonzeroRegister));
            }
            Measured {
                nodes: 1,
                copy_work: 1,
                basis_bits: Some(0),
            }
        }
        Kind::Parameter(_) => return Err(Failure::at(original, FailureKind::Parameter)),
        Kind::Q(basis) => {
            if stage == Stage::Basis {
                return Err(Failure::at(original, FailureKind::QuantumBasis));
            }
            let child = measure(
                original_basis(original),
                basis,
                Stage::Basis,
                depth + 1,
                visited,
            )?;
            let nodes = child
                .nodes
                .checked_add(1)
                .ok_or_else(|| Failure::at(original, FailureKind::WorkOverflow))?;
            Measured {
                nodes,
                copy_work: child
                    .copy_work
                    .checked_add(nodes)
                    .ok_or_else(|| Failure::at(original, FailureKind::WorkOverflow))?,
                basis_bits: None,
            }
        }
        Kind::Tuple(fields) => {
            if fields.len() < 2 {
                return Err(Failure::at(original, FailureKind::TupleArity));
            }
            if fields.len() > 64 {
                return Err(Failure::at(original, FailureKind::TupleLimit));
            }
            let mut result = Measured {
                nodes: 1,
                copy_work: 0,
                basis_bits: Some(0),
            };
            for (ordinal, field) in fields.iter().enumerate() {
                let child = measure(
                    original_field(original, fields.len(), ordinal),
                    field,
                    stage,
                    depth + 1,
                    visited,
                )?;
                result.nodes = result
                    .nodes
                    .checked_add(child.nodes)
                    .ok_or_else(|| Failure::at(original, FailureKind::WorkOverflow))?;
                result.copy_work = result
                    .copy_work
                    .checked_add(child.copy_work)
                    .ok_or_else(|| Failure::at(original, FailureKind::WorkOverflow))?;
                result.basis_bits = match (result.basis_bits, child.basis_bits) {
                    (Some(a), Some(b)) => Some(
                        a.checked_add(b)
                            .ok_or_else(|| Failure::at(original, FailureKind::WorkOverflow))?,
                    ),
                    _ => None,
                };
            }
            result.copy_work = result
                .copy_work
                .checked_add(result.nodes)
                .ok_or_else(|| Failure::at(original, FailureKind::WorkOverflow))?;
            result
        }
    };
    if stage == Stage::Basis && result.basis_bits.is_some_and(|bits| bits > MAX_BITS) {
        return Err(Failure::at(original, FailureKind::BasisWidth));
    }
    Ok(result)
}

fn copy_reserved<N: FiniteRegisterSize>(
    original: &Type,
    checked: &crate::frontend::types::Type<N>,
    stage: Stage,
) -> Result<Ty, Failure> {
    match &checked.kind {
        Kind::Unit => Ok(Ty::unit()),
        Kind::Bit => Ok(Ty::bit()),
        Kind::Bits(size) if size.is_exact_zero() => Ok(Ty::empty_bits()),
        Kind::Bits(_) => Err(Failure::at(original, FailureKind::NonzeroRegister)),
        Kind::Parameter(_) => Err(Failure::at(original, FailureKind::Parameter)),
        Kind::Q(_) if stage == Stage::Basis => {
            Err(Failure::at(original, FailureKind::QuantumBasis))
        }
        Kind::Q(basis) => Ok(Ty::quantum(copy_reserved(
            original_basis(original),
            basis,
            Stage::Basis,
        )?)),
        Kind::Tuple(fields) => {
            if fields.len() < 2 {
                return Err(Failure::at(original, FailureKind::TupleArity));
            }
            if fields.len() > 64 {
                return Err(Failure::at(original, FailureKind::TupleLimit));
            }
            let mut copied = Vec::with_capacity(fields.len());
            for (ordinal, field) in fields.iter().enumerate() {
                copied.push(copy_reserved(
                    original_field(original, fields.len(), ordinal),
                    field,
                    stage,
                )?);
            }
            Ok(Ty::tuple(copied))
        }
    }
}

/// The actual conversion path reserves all type-copy work before invoking its
/// copy callback. Keeping this boundary explicit lets tests observe failures
/// before any copied tuple/owner storage is constructed.
fn reserve_and_copy<N: FiniteRegisterSize, E>(
    original: &Type,
    checked: &crate::frontend::types::Type<N>,
    stage: Stage,
    failure: impl Fn(Failure) -> E,
    mut reserve: impl FnMut(Span, usize) -> Result<(), E>,
    copy: impl FnOnce(&crate::frontend::types::Type<N>) -> Result<Ty, Failure>,
) -> Result<Ty, E> {
    let measured = measure(original, checked, stage, 1, &mut 0).map_err(&failure)?;
    reserve(original.span, measured.copy_work)?;
    copy(checked).map_err(failure)
}

/// Preserve the complete closed checked tree. Named source types can expand to
/// any eligible closed tree; source shape selects locations, never constructors.
pub(super) fn finite_type<N: FiniteRegisterSize>(
    compiler: &Compiler<'_>,
    work: &mut usize,
    module: &str,
    original: &Type,
    checked: &crate::frontend::types::Type<N>,
    stage: Stage,
) -> Result<Ty, CompileError> {
    reserve_and_copy(
        original,
        checked,
        stage,
        |failure| failure.compile(compiler, module),
        |span, amount| compiler.charge_at(work, module, span, amount),
        |checked| copy_reserved(original, checked, stage),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    type Closed = crate::frontend::types::Type<u32>;

    fn named(span: Span) -> Type {
        Type {
            kind: TypeKind::Named(Ident {
                text: "A".to_owned(),
                span,
            }),
            span,
        }
    }

    #[test]
    fn complete_copy_reservation_precedes_the_real_copy_callback() {
        let original = named(Span { start: 1, end: 2 });
        let checked = Closed::pair(Closed::unit(), Closed::bit());
        for available in [4, 5] {
            let copied = Cell::new(false);
            let used = Cell::new(0);
            let result = reserve_and_copy(
                &original,
                &checked,
                Stage::Basis,
                |failure| failure,
                |span, amount| {
                    assert_eq!(span, original.span);
                    assert_eq!(amount, 5, "three root nodes and one per leaf");
                    if amount > available {
                        return Err(Failure {
                            span,
                            kind: FailureKind::WorkOverflow,
                        });
                    }
                    used.set(amount);
                    Ok(())
                },
                |checked| {
                    copied.set(true);
                    copy_reserved(&original, checked, Stage::Basis)
                },
            );
            assert_eq!(copied.get(), available == 5);
            assert_eq!(used.get(), if available == 5 { 5 } else { 0 });
            if available == 5 {
                assert_eq!(result.unwrap(), Ty::pair(Ty::unit(), Ty::bit()));
            } else {
                assert_eq!(result.unwrap_err().kind, FailureKind::WorkOverflow);
            }
        }
    }

    #[test]
    fn named_expansion_keeps_quantum_product_and_empty_register_tags() {
        let original = named(Span { start: 3, end: 4 });
        let checked = Closed::pair(Closed::quantum(Closed::bits(0)), Closed::bit());
        let result = reserve_and_copy(
            &original,
            &checked,
            Stage::Runtime,
            |failure| failure,
            |_, amount| {
                assert_eq!(amount, 8);
                Ok(())
            },
            |checked| copy_reserved(&original, checked, Stage::Runtime),
        )
        .unwrap();
        assert_eq!(result, Ty::pair(Ty::quantum(Ty::empty_bits()), Ty::bit()));
        assert_ne!(result, Ty::pair(Ty::quantum(Ty::unit()), Ty::bit()));
    }

    #[test]
    fn locations_follow_only_corresponding_original_children() {
        let root = Span { start: 1, end: 8 };
        let child = Span { start: 6, end: 7 };
        let original = Type {
            kind: TypeKind::Tuple(vec![named(root), named(child)]),
            span: root,
        };
        let checked = Closed::pair(Closed::unit(), Closed::bits(1));
        assert_eq!(
            measure(&original, &checked, Stage::Basis, 1, &mut 0)
                .unwrap_err()
                .span,
            child
        );
        assert_eq!(
            measure(&named(root), &checked, Stage::Basis, 1, &mut 0)
                .unwrap_err()
                .span,
            root
        );
        let mismatched = Type {
            kind: TypeKind::Tuple(vec![named(child)]),
            span: root,
        };
        assert_eq!(
            measure(&mismatched, &checked, Stage::Basis, 1, &mut 0)
                .unwrap_err()
                .span,
            root
        );
    }

    #[test]
    fn malformed_or_open_checked_types_refuse_before_reservation_or_copy() {
        let original = named(Span { start: 0, end: 1 });
        let parameter = Closed::parameter(crate::frontend::types::TypeParameter {
            key: None,
            name: "A".to_owned(),
            span: original.span,
        });
        for (checked, expected) in [
            (Closed::bits(1), FailureKind::NonzeroRegister),
            (parameter, FailureKind::Parameter),
            (Closed::quantum(Closed::bit()), FailureKind::QuantumBasis),
            (Closed::tuple(Vec::new()), FailureKind::TupleArity),
            (Closed::tuple(vec![Closed::unit()]), FailureKind::TupleArity),
        ] {
            let result = reserve_and_copy(
                &original,
                &checked,
                Stage::Basis,
                |failure| failure,
                |_, _| panic!("invalid checked type must not reach reservation"),
                |_| panic!("invalid checked type must not reach type-copy allocation"),
            );
            assert_eq!(result.unwrap_err().kind, expected);
        }
    }
}
