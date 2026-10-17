//! Copy an exact checked type into the existing finite representation.
//! Source syntax supplies diagnostic locations only; copying grants no evidence.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;

#[derive(Clone, Copy)]
enum Location<'a> {
    Source(&'a Type),
    Span(Span),
}
impl<'a> From<&'a Type> for Location<'a> {
    fn from(source: &'a Type) -> Self {
        Self::Source(source)
    }
}
impl Location<'_> {
    fn span(self) -> Span {
        match self {
            Self::Source(source) => source.span,
            Self::Span(span) => span,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FailureKind {
    TreeLimit,
    WorkOverflow,
    BasisWidth,
    RegisterWidth(RegisterWidthError),
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
    fn at<'a>(original: impl Into<Location<'a>>, kind: FailureKind) -> Self {
        Self {
            span: original.into().span(),
            kind,
        }
    }

    fn compile(self, compiler: &Compiler<'_>, module: &str) -> CompileError {
        let (code, message) = match self.kind {
            FailureKind::TreeLimit => (
                ErrorCode::Limit,
                format!(
                    "internal value or type exceeds the initial {MAX_TREE_NODES}-node / {MAX_TREE_DEPTH}-level limit"
                ),
            ),
            FailureKind::WorkOverflow => (
                ErrorCode::Limit,
                "finite type copy work accounting overflow".to_owned(),
            ),
            FailureKind::BasisWidth => (
                ErrorCode::Limit,
                "basis type exceeds the initial 12-bit limit".to_owned(),
            ),
            FailureKind::RegisterWidth(RegisterWidthError::Unresolved) => (
                ErrorCode::Unsupported,
                "finite register size requires an exact closed natural".to_owned(),
            ),
            FailureKind::RegisterWidth(RegisterWidthError::Capacity) => (
                ErrorCode::Limit,
                "finite register size exceeds u32 or is negative".to_owned(),
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

fn original_basis(original: Location<'_>) -> Location<'_> {
    match original {
        Location::Source(Type {
            kind: TypeKind::Q(basis),
            ..
        }) => Location::Source(basis),
        _ => original,
    }
}

fn original_field(original: Location<'_>, arity: usize, ordinal: usize) -> Location<'_> {
    match original {
        Location::Source(Type {
            kind: TypeKind::Tuple(fields),
            ..
        }) if fields.len() == arity => fields.get(ordinal).map_or(original, Location::Source),
        _ => original,
    }
}

/// This bounded preflight uses only borrowed nodes and fixed-size stack frames.
/// It creates no temporary Vec, Box or copied type. The total copy charge is
/// exactly the former sum of subtree.tree_size().nodes over every copied node.
fn measure<'a, N: FiniteRegisterSize>(
    original: impl Into<Location<'a>>,
    checked: &crate::frontend::types::Type<N>,
    stage: Stage,
    depth: usize,
    visited: &mut usize,
) -> Result<Measured, Failure> {
    let original = original.into();
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
            let width = size
                .finite_width()
                .map_err(|error| Failure::at(original, FailureKind::RegisterWidth(error)))?;
            let width = usize::try_from(width)
                .map_err(|_| Failure::at(original, FailureKind::WorkOverflow))?;
            if width > MAX_BITS {
                return Err(Failure::at(original, FailureKind::BasisWidth));
            }
            Measured {
                nodes: 1,
                copy_work: 1,
                basis_bits: Some(width),
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

fn copy_reserved<'a, N: FiniteRegisterSize>(
    original: impl Into<Location<'a>>,
    checked: &crate::frontend::types::Type<N>,
    stage: Stage,
) -> Result<Ty, Failure> {
    let original = original.into();
    match &checked.kind {
        Kind::Unit => Ok(Ty::unit()),
        Kind::Bit => Ok(Ty::bit()),
        Kind::Bits(size) => {
            Ok(Ty::bits(size.finite_width().map_err(|error| {
                Failure::at(original, FailureKind::RegisterWidth(error))
            })?))
        }
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
fn reserve_and_copy<'a, N: FiniteRegisterSize, E>(
    original: impl Into<Location<'a>>,
    checked: &crate::frontend::types::Type<N>,
    stage: Stage,
    failure: impl Fn(Failure) -> E,
    mut reserve: impl FnMut(Span, usize) -> Result<(), E>,
    copy: impl FnOnce(&crate::frontend::types::Type<N>) -> Result<Ty, Failure>,
) -> Result<Ty, E> {
    let original = original.into();
    let measured = measure(original, checked, stage, 1, &mut 0).map_err(&failure)?;
    reserve(original.span(), measured.copy_work)?;
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

/// Inferred checked types have a real expression location but no source type
/// annotation. Use the same preflight and copier without fabricating an AST.
pub(super) fn finite_body_type(
    compiler: &Compiler<'_>,
    work: &mut usize,
    module: &str,
    span: Span,
    checked: &crate::frontend::types::Type<u32>,
) -> Result<Ty, CompileError> {
    reserve_and_copy(
        Location::Span(span),
        checked,
        Stage::Runtime,
        |failure| failure.compile(compiler, module),
        |span, cells| compiler.charge_at(work, module, span, cells),
        |checked| copy_reserved(Location::Span(span), checked, Stage::Runtime),
    )
}

pub(super) fn closed_capacity(
    checked: &crate::frontend::types::Type<u32>,
    span: Span,
    charge: &mut impl FnMut(Span, usize) -> Result<(), SourceError>,
) -> Result<(), SourceError> {
    capacity_at(checked, Stage::Runtime, span, charge)
}

pub(super) fn closed_basis_capacity(
    checked: &crate::frontend::types::Type<u32>,
    span: Span,
    charge: &mut impl FnMut(Span, usize) -> Result<(), SourceError>,
) -> Result<(), SourceError> {
    capacity_at(checked, Stage::Basis, span, charge)
}

fn capacity_at(
    checked: &crate::frontend::types::Type<u32>,
    stage: Stage,
    span: Span,
    charge: &mut impl FnMut(Span, usize) -> Result<(), SourceError>,
) -> Result<(), SourceError> {
    let measured = measure(Location::Span(span), checked, stage, 1, &mut 0).map_err(|failure| {
        let (code, message) = match failure.kind {
            FailureKind::TreeLimit | FailureKind::WorkOverflow => (
                "limit",
                "finite closed type exceeds its tree or work capacity",
            ),
            FailureKind::BasisWidth => ("limit", "basis type exceeds the initial 12-bit limit"),
            FailureKind::RegisterWidth(_) => ("limit", "finite register size is not represented"),
            FailureKind::Parameter => ("static", "finite closed type retains an unbound Basis"),
            _ => (
                "type",
                "finite closed type has an invalid ownership or tuple constructor",
            ),
        };
        SourceError::new(code, failure.span, message)
    })?;
    charge(span, measured.nodes)
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
        let checked = Closed::pair(Closed::unit(), Closed::bits(13));
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
            (Closed::bits(13), FailureKind::BasisWidth),
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

    #[test]
    fn closed_register_transport_keeps_zero_one_and_product_constructor_identity() {
        let original = named(Span { start: 2, end: 3 });
        for checked in [
            Closed::bits(0),
            Closed::bits(1),
            Closed::pair(Closed::bits(0), Closed::bits(1)),
            Closed::pair(Closed::quantum(Closed::bits(1)), Closed::unit()),
        ] {
            let stage = if checked.linear() {
                Stage::Runtime
            } else {
                Stage::Basis
            };
            let copied = reserve_and_copy(
                &original,
                &checked,
                stage,
                |failure| failure,
                |_, _| Ok(()),
                |checked| copy_reserved(&original, checked, stage),
            )
            .unwrap();
            assert_eq!(copied, checked);
        }
        assert_ne!(Closed::bits(0), Closed::unit());
        assert_ne!(Closed::bits(1), Closed::bit());
        assert_ne!(
            Closed::pair(Closed::bits(0), Closed::bits(1)),
            Closed::pair(Closed::bits(1), Closed::bits(0))
        );
    }

    #[test]
    fn symbolic_register_storage_requires_exact_unsigned_width_before_copying() {
        let original = named(Span { start: 8, end: 9 });
        for number in [-1, i128::from(u32::MAX) + 1] {
            let checked = crate::frontend::types::Type::bits(check::Linear::constant(number));
            let result = reserve_and_copy(
                &original,
                &checked,
                Stage::Basis,
                |failure| failure,
                |_, _| panic!("out-of-representation sizes must refuse before reservation"),
                |_| panic!("out-of-representation sizes must refuse before copying"),
            );
            assert_eq!(
                result.unwrap_err().kind,
                FailureKind::RegisterWidth(RegisterWidthError::Capacity)
            );
        }
        let checked = crate::frontend::types::Type::bits(check::Linear::constant(1));
        let copied = reserve_and_copy(
            &original,
            &checked,
            Stage::Basis,
            |failure| failure,
            |_, cost| {
                assert_eq!(cost, 1);
                Ok(())
            },
            |checked| copy_reserved(&original, checked, Stage::Basis),
        )
        .unwrap();
        assert_eq!(copied, Ty::bits(1));

        let module = crate::frontend::parser::parse_module(
            "unitary fn keep[const n: Nat](q: Q<Bits<n>>) -> Q<Bits<n>> { q }",
        )
        .unwrap();
        let checked = check::program_with(
            BTreeMap::from([("main", &module)]),
            SourceLimits::finite(),
            |_, _, _, _, _, _, _| Ok(()),
        )
        .unwrap()
        .0;
        let definition = checked.resolution.qualified("main::keep").unwrap();
        let Kind::Q(symbolic) = &checked.interfaces[&definition].params[0].kind else {
            panic!("original checked quantum register")
        };
        let result = reserve_and_copy(
            &original,
            symbolic.as_ref(),
            Stage::Basis,
            |failure| failure,
            |_, _| panic!("an unresolved original size must refuse before reservation"),
            |_| panic!("an unresolved original size must refuse before copying"),
        );
        assert_eq!(
            result.unwrap_err().kind,
            FailureKind::RegisterWidth(RegisterWidthError::Unresolved)
        );
    }
}
