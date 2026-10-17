//! Internal selected emitter operations; these supply no source or IR authority.
//! Source primitives enter only through their language-owned typed identity.
//! Historical derived/backend operations remain internal transport constructors.
//! Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
//! Concrete capacity limits and lowering/translation checks remain separate.
use super::ast::Effect;
use super::{Error, Result, Span};
use crate::frontend::types::Type;

#[derive(Clone, Copy)]
pub(super) enum Size {
    Constant(u32),
    Argument(usize, i8),
}
#[derive(Clone, Copy)]
pub(super) enum TypeShape {
    /// Ordinary Unit has no quantum owner, unlike the exact singleton basis.
    Unit,
    QUnit,
    Bit,
    Bits(Size),
    CBit,
    CBits(Size),
    Tuple(&'static [TypeShape]),
}
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Guard {
    None,
    RegisterIndex,
}

#[derive(Clone, Copy)]
pub(super) enum TypeRule {
    Fixed(&'static [TypeShape], TypeShape),
    QuantumEndomorphism,
    Split,
    Join,
}
impl TypeRule {
    pub fn dependent(self) -> bool {
        !matches!(self, Self::Fixed(..))
    }
    pub fn runtime_arity(self) -> usize {
        match self {
            Self::Fixed(inputs, _) => inputs.len(),
            Self::QuantumEndomorphism | Self::Split => 1,
            Self::Join => 2,
        }
    }
}

/// The selected scalar emitter preserves one owner's complete exact basis.
pub(super) fn quantum_endomorphism<N: Clone>(input: &Type<N>, span: Span) -> Result<Type<N>> {
    if input.quantum_basis().is_some_and(Type::is_basis) {
        Ok(input.clone())
    } else {
        Err(Error::new(
            "type",
            span,
            "scalar phase requires one Q<A> owner",
        ))
    }
}

/// The selected concrete emitter's input-dependent exact-tree rule.
/// It authorizes no implicit coherence or physical-state assumption.
pub(super) fn dependent_output<N: Clone>(
    rule: TypeRule,
    inputs: &[&Type<N>],
    span: Span,
) -> Result<Type<N>> {
    if inputs.len() != rule.runtime_arity() {
        return Err(Error::new("type", span, "runtime argument arity mismatch"));
    }
    for input in inputs {
        if input.storage_size(4096, 64).is_none() {
            return Err(Error::new(
                "limit",
                span,
                "primitive type exceeds 4096 cells or depth 64",
            ));
        }
    }
    match rule {
        TypeRule::QuantumEndomorphism => quantum_endomorphism(inputs[0], span),
        TypeRule::Split => {
            let fields = inputs[0]
                .quantum_basis()
                .and_then(Type::tuple_fields)
                .filter(|fields| fields.len() == 2)
                .ok_or_else(|| Error::new("type", span, "split requires Q<(A, B)>"))?;
            Ok(Type::pair(
                Type::quantum(fields[0].clone()),
                Type::quantum(fields[1].clone()),
            ))
        }
        TypeRule::Join => {
            let a = inputs[0]
                .quantum_basis()
                .ok_or_else(|| Error::new("type", span, "join requires two quantum owners"))?;
            let b = inputs[1]
                .quantum_basis()
                .ok_or_else(|| Error::new("type", span, "join requires two quantum owners"))?;
            let x = a.storage_size(4096, 64).expect("bounded input");
            let y = b.storage_size(4096, 64).expect("bounded input");
            if x.nodes + y.nodes + 1 > 4096 || x.depth.max(y.depth) >= 64 {
                return Err(Error::new(
                    "limit",
                    span,
                    "joined basis exceeds 4096 cells or depth 64",
                ));
            }
            Ok(Type::quantum(Type::pair(a.clone(), b.clone())))
        }
        TypeRule::Fixed(..) => unreachable!("fixed primitive has no dependent rule"),
    }
}

pub(super) struct Signature {
    pub natural_arity: usize,
    pub types: TypeRule,
    pub effect: Effect,
    pub guard: Guard,
}
macro_rules! primitives {
    ($($name:ident => ($arity:literal, $types:expr, $effect:ident, $guard:ident)),+ $(,)?) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub(super) enum Primitive { $($name),+ }
        impl Primitive {
            pub const ALL: &'static [Self] = &[$(Self::$name),+];
            pub fn signature(self) -> Signature {
                match self { $(Self::$name => Signature {
                    natural_arity: $arity, types: $types,
                    effect: Effect::$effect, guard: Guard::$guard,
                }),+ }
            }
        }
    };
}
impl Primitive {
    /// Existing selected adapters are explicitly a subset of the source
    /// catalog. An unavailable adapter refuses; it cannot retry by spelling.
    pub fn from_language(id: crate::frontend::resolve::PrimitiveId) -> Option<Self> {
        Self::ALL
            .iter()
            .copied()
            .find(|operation| operation.language_identity() == Some(id))
    }
    pub fn language_identity(self) -> Option<crate::frontend::resolve::PrimitiveId> {
        use crate::frontend::resolve::PrimitiveId as Language;
        Some(match self {
            Self::H => Language::H,
            Self::Phase => Language::Phase,
            Self::PhaseEighth => Language::GlobalPhaseEighth,
            Self::MeasureZ => Language::MeasureZ,
            Self::TakeBit => Language::TakeBit,
            Self::PutBit => Language::PutBit,
            Self::EmptyBits => Language::EmptyBits,
            Self::PrependBit => Language::PrependBit,
            Self::Unit => Language::Unit,
            Self::Finish => Language::Finish,
            Self::Split => Language::Split,
            Self::Join => Language::Join,
            Self::X
            | Self::Z
            | Self::Cnot
            | Self::ControlledPhase
            | Self::Init0
            | Self::Empty
            | Self::ConsumeEmpty => return None,
        })
    }
}

use Size::{Argument as A, Constant as C};
use TypeRule::{Fixed, QuantumEndomorphism};
use TypeShape::{Bit, Bits, CBit, CBits, QUnit, Tuple, Unit};
primitives! {
    H => (0, Fixed(&[Bit], Bit), Unitary, None),
    X => (0, Fixed(&[Bit], Bit), Unitary, None),
    Z => (0, Fixed(&[Bit], Bit), Unitary, None),
    Cnot => (0, Fixed(&[Bit, Bit], Tuple(&[Bit, Bit])), Unitary, None),
    Phase => (2, Fixed(&[Bit], Bit), Unitary, None),
    PhaseEighth => (0, QuantumEndomorphism, Unitary, None),
    ControlledPhase => (2, Fixed(&[Bit, Bit], Tuple(&[Bit, Bit])), Unitary, None),
    Init0 => (0, Fixed(&[], Bit), Isometry, None),
    MeasureZ => (0, Fixed(&[Bit], CBit), Observe, None),
    TakeBit => (2, Fixed(&[Bits(A(0, 0))], Tuple(&[Bit, Bits(A(0, -1))])), Unitary, RegisterIndex),
    PutBit => (2, Fixed(&[Bit, Bits(A(0, -1))], Bits(A(0, 0))), Unitary, RegisterIndex),
    Empty => (0, Fixed(&[], Bits(C(0))), Unitary, None),
    ConsumeEmpty => (0, Fixed(&[Bits(C(0))], Unit), Unitary, None),
    EmptyBits => (0, Fixed(&[], CBits(C(0))), Unitary, None),
    PrependBit => (1, Fixed(&[CBit, CBits(A(0, 0))], CBits(A(0, 1))), Unitary, None),
    Unit => (0, Fixed(&[Unit], QUnit), Unitary, None),
    Finish => (0, Fixed(&[QUnit], Unit), Unitary, None),
    Split => (0, TypeRule::Split, Unitary, None),
    Join => (0, TypeRule::Join, Unitary, None),
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn catalog_has_unique_resolvable_paths_and_well_scoped_sizes() {
        fn shape(t: TypeShape, arity: usize) {
            match t {
                TypeShape::Bits(Size::Argument(index, _))
                | TypeShape::CBits(Size::Argument(index, _)) => assert!(index < arity),
                TypeShape::Tuple(fields) => fields.iter().for_each(|f| shape(*f, arity)),
                TypeShape::Unit
                | TypeShape::QUnit
                | TypeShape::Bit
                | TypeShape::CBit
                | TypeShape::Bits(Size::Constant(_))
                | TypeShape::CBits(Size::Constant(_)) => {}
            }
        }
        let mut paths = std::collections::BTreeSet::new();
        for p in Primitive::ALL {
            let s = p.signature();
            if let Some(id) = p.language_identity() {
                assert!(paths.insert(id));
                assert_eq!(Primitive::from_language(id), Some(*p));
            }
            match s.types {
                TypeRule::Fixed(inputs, output) => {
                    inputs.iter().for_each(|f| shape(*f, s.natural_arity));
                    shape(output, s.natural_arity);
                }
                TypeRule::QuantumEndomorphism | TypeRule::Split | TypeRule::Join => {
                    assert_eq!(s.natural_arity, 0);
                    assert!((1..=2).contains(&s.types.runtime_arity()));
                    assert_eq!(s.effect, Effect::Unitary);
                }
            }
        }
        assert_eq!(
            Primitive::from_language(crate::frontend::resolve::PrimitiveId::Discard),
            None
        );
    }
}
