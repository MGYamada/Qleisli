//! Copy an exact checked type into the existing finite representation.
//! Source syntax supplies diagnostic locations only; copying grants no evidence.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;
use crate::frontend::types::nominal::{Body, Field, Nominal};

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
    Nominal,
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
            FailureKind::Nominal => (
                ErrorCode::Unsupported,
                "nominal source types require typed native transport".to_owned(),
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
    metadata_work: usize,
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
/// the former sum of subtree.tree_size().nodes over every copied node, plus
/// complete nominal metadata. It reserves that work before cloning labels.
fn measure<'a, N: FiniteRegisterSize>(
    original: impl Into<Location<'a>>,
    checked: &crate::frontend::types::Type<N>,
    stage: Stage,
    depth: usize,
    visited: &mut usize,
) -> Result<Measured, Failure> {
    measure_inner(original.into(), checked, stage, depth, visited, false)
}

fn measure_inner<N: FiniteRegisterSize>(
    original: Location<'_>,
    checked: &crate::frontend::types::Type<N>,
    stage: Stage,
    depth: usize,
    visited: &mut usize,
    ordinary: bool,
) -> Result<Measured, Failure> {
    if depth > MAX_TREE_DEPTH || *visited >= MAX_TREE_NODES {
        return Err(Failure::at(original, FailureKind::TreeLimit));
    }
    *visited += 1;
    let result = match &checked.kind {
        Kind::Unit => Measured {
            nodes: 1,
            copy_work: 1,
            metadata_work: 0,
            basis_bits: Some(0),
        },
        Kind::Bit => Measured {
            nodes: 1,
            copy_work: 1,
            metadata_work: 0,
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
                metadata_work: 0,
                basis_bits: Some(width),
            }
        }
        Kind::Parameter(_) => return Err(Failure::at(original, FailureKind::Parameter)),
        Kind::Nominal(nominal) => {
            let metadata_work = nominal.metadata_cells();
            let mut result = Measured {
                nodes: 1,
                copy_work: metadata_work,
                metadata_work,
                // Ordinary nominal storage is never a coherent Basis encoding.
                basis_bits: None,
            };
            for field in nominal.fields() {
                let child = measure_inner(original, field, stage, depth + 1, visited, true)?;
                result.nodes = result
                    .nodes
                    .checked_add(child.nodes)
                    .ok_or_else(|| Failure::at(original, FailureKind::WorkOverflow))?;
                result.copy_work = result
                    .copy_work
                    .checked_add(child.copy_work)
                    .ok_or_else(|| Failure::at(original, FailureKind::WorkOverflow))?;
                result.metadata_work = result
                    .metadata_work
                    .checked_add(child.metadata_work)
                    .ok_or_else(|| Failure::at(original, FailureKind::WorkOverflow))?;
            }
            result.copy_work = result
                .copy_work
                .checked_add(result.nodes)
                .ok_or_else(|| Failure::at(original, FailureKind::WorkOverflow))?;
            result
        }
        Kind::Q(basis) => {
            if stage == Stage::Basis || ordinary {
                return Err(Failure::at(original, FailureKind::QuantumBasis));
            }
            let child = measure_inner(
                original_basis(original),
                basis,
                Stage::Basis,
                depth + 1,
                visited,
                true,
            )?;
            if child.basis_bits.is_none() {
                return Err(Failure::at(original, FailureKind::Nominal));
            }
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
                metadata_work: child.metadata_work,
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
                metadata_work: 0,
                basis_bits: Some(0),
            };
            for (ordinal, field) in fields.iter().enumerate() {
                let child = measure_inner(
                    original_field(original, fields.len(), ordinal),
                    field,
                    stage,
                    depth + 1,
                    visited,
                    ordinary,
                )?;
                result.nodes = result
                    .nodes
                    .checked_add(child.nodes)
                    .ok_or_else(|| Failure::at(original, FailureKind::WorkOverflow))?;
                result.copy_work = result
                    .copy_work
                    .checked_add(child.copy_work)
                    .ok_or_else(|| Failure::at(original, FailureKind::WorkOverflow))?;
                result.metadata_work = result
                    .metadata_work
                    .checked_add(child.metadata_work)
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
        Kind::Nominal(nominal) => match &nominal.body {
            Body::Enum(variants) => Ok(Ty::nominal(Nominal {
                origin: Arc::clone(&nominal.origin),
                body: Body::Enum(variants.clone()),
            })),
            Body::Record(fields) => {
                let mut copied = Vec::with_capacity(fields.len());
                for field in fields {
                    copied.push(Field {
                        name: field.name.clone(),
                        public: field.public,
                        // The borrowed preflight has already refused every Q
                        // below this ordinary record, before any allocation.
                        ty: copy_reserved(original, &field.ty, stage)?,
                    });
                }
                Ok(Ty::nominal(Nominal {
                    origin: Arc::clone(&nominal.origin),
                    body: Body::Record(copied),
                }))
            }
        },
        Kind::Q(_) if stage == Stage::Basis => {
            Err(Failure::at(original, FailureKind::QuantumBasis))
        }
        Kind::Q(basis) => {
            let copied = copy_reserved(original_basis(original), basis, Stage::Basis)?;
            if copied.basis_bits().is_none() {
                return Err(Failure::at(original_basis(original), FailureKind::Nominal));
            }
            Ok(Ty::quantum(copied))
        }
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
    if stage == Stage::Basis && measured.basis_bits.is_none() {
        return Err(SourceError::new(
            "type",
            span,
            "ordinary nominal types have no coherent finite basis encoding",
        ));
    }
    // Keep built-in accounting unchanged; nominal metadata is additional work.
    charge(span, measured.nodes + measured.metadata_work)
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
    fn enumeration(module: &str, labels: &[&str]) -> Closed {
        Closed::nominal(Nominal {
            origin: Arc::new(crate::frontend::types::nominal::Origin {
                module: module.to_owned(),
                name: "Tri".to_owned(),
                source: Arc::from("enum Tri { A, B, C }"),
                span: Span { start: 0, end: 20 },
            }),
            body: Body::Enum(labels.iter().map(|label| (*label).to_owned()).collect()),
        })
    }

    #[test]
    fn enum_copy_reserves_metadata_and_retains_exact_declaration() {
        let original = named(Span { start: 0, end: 3 });
        let checked = enumeration("main", &["A", "B", "C"]);
        let Kind::Nominal(nominal) = &checked.kind else {
            panic!("enum fixture")
        };
        let cost = nominal.metadata_cells() + 1;
        for available in [cost - 1, cost] {
            let copied = Cell::new(false);
            let result = reserve_and_copy(
                &original,
                &checked,
                Stage::Basis,
                |failure| failure,
                |span, amount| {
                    assert_eq!(amount, cost);
                    if amount > available {
                        return Err(Failure {
                            span,
                            kind: FailureKind::WorkOverflow,
                        });
                    }
                    Ok(())
                },
                |checked| {
                    copied.set(true);
                    copy_reserved(&original, checked, Stage::Basis)
                },
            );
            assert_eq!(copied.get(), available == cost);
            if let Ok(value) = result {
                assert_eq!(value, checked);
                assert_ne!(value, enumeration("foreign", &["A", "B", "C"]));
                assert_ne!(value, enumeration("main", &["B", "A", "C"]));
                assert_ne!(value, Closed::bits(2));
                assert_eq!(value.basis_bits(), None);
            } else {
                assert_eq!(available, cost - 1);
            }
        }
    }

    #[test]
    fn enum_runtime_capacity_does_not_open_coherent_types() {
        let original = named(Span { start: 1, end: 2 });
        let checked = enumeration("main", &["A"]);
        let Kind::Nominal(nominal) = &checked.kind else {
            panic!("enum fixture")
        };
        let mut charge = 0;
        closed_capacity(&checked, original.span, &mut |_, cells| {
            charge += cells;
            Ok(())
        })
        .unwrap();
        assert_eq!(charge, nominal.metadata_cells() + 1);
        assert_ne!(checked, Closed::unit());
        assert_ne!(checked, Closed::bits(0));
        assert!(
            closed_basis_capacity(&checked, original.span, &mut |_, _| {
                panic!("nominal coherent basis must refuse before reservation")
            })
            .is_err()
        );
        let record = Closed::nominal(Nominal {
            origin: Arc::clone(&nominal.origin),
            body: Body::Record(Vec::new()),
        });
        for invalid in [Closed::quantum(checked), Closed::quantum(record)] {
            let error = reserve_and_copy(
                &original,
                &invalid,
                Stage::Runtime,
                |failure| failure,
                |_, _| panic!("unsupported types must refuse before reservation"),
                |_| panic!("unsupported types must refuse before copying"),
            )
            .unwrap_err();
            assert_eq!(error.kind, FailureKind::Nominal);
        }
    }

    fn record(fields: Vec<Field<u32>>) -> Closed {
        Closed::nominal(Nominal {
            origin: Arc::new(crate::frontend::types::nominal::Origin {
                module: "main".to_owned(),
                name: "Packet".to_owned(),
                source: Arc::from("struct Packet{}"),
                span: Span::default(),
            }),
            body: Body::Record(fields),
        })
    }

    #[test]
    fn record_copy_preserves_order_privacy_zero_children_and_reserves_before_allocation() {
        let original = named(Span { start: 0, end: 1 });
        let checked = record(vec![
            Field {
                name: "one".into(),
                public: true,
                ty: enumeration("main", &["Only"]),
            },
            Field {
                name: "empty".into(),
                public: false,
                ty: record(Vec::new()),
            },
            Field {
                name: "bits".into(),
                public: true,
                ty: Closed::bits(0),
            },
        ]);
        let Kind::Nominal(nominal) = &checked.kind else {
            panic!("record fixture");
        };
        let metadata = nominal.metadata_cells()
            + nominal
                .fields()
                .map(|field| match &field.kind {
                    Kind::Nominal(child) => child.metadata_cells(),
                    _ => 0,
                })
                .sum::<usize>();
        // Four nodes: three leaf copies plus the four-node root traversal.
        let cost = metadata + 7;
        assert_eq!(
            measure(&original, &checked, Stage::Runtime, MAX_TREE_DEPTH, &mut 0)
                .unwrap_err()
                .kind,
            FailureKind::TreeLimit
        );
        let mut visited = MAX_TREE_NODES - 1;
        assert_eq!(
            measure(&original, &checked, Stage::Runtime, 1, &mut visited)
                .unwrap_err()
                .kind,
            FailureKind::TreeLimit
        );
        for available in [cost - 1, cost] {
            let copied = Cell::new(false);
            let result = reserve_and_copy(
                &original,
                &checked,
                Stage::Runtime,
                |failure| failure,
                |span, amount| {
                    assert_eq!(amount, cost);
                    if amount > available {
                        return Err(Failure {
                            span,
                            kind: FailureKind::WorkOverflow,
                        });
                    }
                    Ok(())
                },
                |checked| {
                    copied.set(true);
                    copy_reserved(&original, checked, Stage::Runtime)
                },
            );
            assert_eq!(copied.get(), available == cost);
            assert_eq!(result.is_ok(), available == cost);
            if let Ok(actual) = result {
                assert_eq!(actual, checked);
                assert_eq!(actual.basis_bits(), None);
                let Kind::Nominal(nominal) = &actual.kind else {
                    panic!("record type");
                };
                let Body::Record(fields) = &nominal.body else {
                    panic!("record declaration");
                };
                assert_eq!(
                    fields
                        .iter()
                        .map(|field| field.name.as_str())
                        .collect::<Vec<_>>(),
                    ["one", "empty", "bits"]
                );
                assert!(!fields[1].public);
            }
        }
        assert!(
            closed_basis_capacity(&checked, original.span, &mut |_, _| {
                panic!("record coherent basis refuses before reservation")
            })
            .is_err()
        );
    }

    #[test]
    fn record_children_cannot_hide_quantum_ownership_even_in_runtime_tuples() {
        let original = named(Span::default());
        let invalid = record(vec![Field {
            name: "hidden".into(),
            public: false,
            ty: Closed::pair(Closed::unit(), Closed::quantum(Closed::unit())),
        }]);
        let error = reserve_and_copy(
            &original,
            &invalid,
            Stage::Runtime,
            |failure| failure,
            |_, _| panic!("ordinary record owner must refuse before reservation"),
            |_| panic!("ordinary record owner must refuse before copying"),
        )
        .unwrap_err();
        assert_eq!(error.kind, FailureKind::QuantumBasis);
    }
}
