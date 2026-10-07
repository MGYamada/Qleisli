//! Existing selected concrete emitter signatures; these supply no IR evidence.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
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
    pub path: &'static str,
    pub natural_arity: usize,
    pub types: TypeRule,
    pub effect: Effect,
    pub guard: Guard,
}
macro_rules! primitives {
    ($($name:ident => ($path:literal, $arity:literal, $types:expr, $effect:ident, $guard:ident)),+ $(,)?) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub(super) enum Primitive { $($name),+ }
        impl Primitive {
            pub const ALL: &'static [Self] = &[$(Self::$name),+];
            pub fn lookup(path: &str) -> Option<Self> {
                Self::ALL.iter().copied().find(|p| p.signature().path == path)
            }
            pub fn signature(self) -> Signature {
                match self { $(Self::$name => Signature {
                    path: $path, natural_arity: $arity, types: $types,
                    effect: Effect::$effect, guard: Guard::$guard,
                }),+ }
            }
        }
    };
}
use Size::{Argument as A, Constant as C};
use TypeRule::{Fixed, QuantumEndomorphism};
use TypeShape::{Bit, Bits, CBit, CBits, QUnit, Tuple, Unit};
primitives! {
    H => ("std::quantum::h", 0, Fixed(&[Bit], Bit), Unitary, None),
    X => ("std::quantum::x", 0, Fixed(&[Bit], Bit), Unitary, None),
    Z => ("std::quantum::z", 0, Fixed(&[Bit], Bit), Unitary, None),
    Cnot => ("std::quantum::cnot", 0, Fixed(&[Bit, Bit], Tuple(&[Bit, Bit])), Unitary, None),
    Phase => ("std::quantum::phase", 2, Fixed(&[Bit], Bit), Unitary, None),
    PhaseEighth => ("std::quantum::phase_eighth", 0, QuantumEndomorphism, Unitary, None),
    ControlledPhase => ("std::quantum::controlled_phase", 2, Fixed(&[Bit, Bit], Tuple(&[Bit, Bit])), Unitary, None),
    Init0 => ("std::quantum::init0", 0, Fixed(&[], Bit), Iso, None),
    MeasureZ => ("std::observe::measure_z", 0, Fixed(&[Bit], CBit), Observe, None),
    TakeBit => ("std::registers::take_bit", 2, Fixed(&[Bits(A(0, 0))], Tuple(&[Bit, Bits(A(0, -1))])), Unitary, RegisterIndex),
    PutBit => ("std::registers::put_bit", 2, Fixed(&[Bit, Bits(A(0, -1))], Bits(A(0, 0))), Unitary, RegisterIndex),
    Empty => ("std::registers::empty", 0, Fixed(&[], Bits(C(0))), Unitary, None),
    ConsumeEmpty => ("std::registers::consume_empty", 0, Fixed(&[Bits(C(0))], Unit), Unitary, None),
    EmptyBits => ("std::classical::empty_bits", 0, Fixed(&[], CBits(C(0))), Unitary, None),
    PrependBit => ("std::classical::prepend_bit", 1, Fixed(&[CBit, CBits(A(0, 0))], CBits(A(0, 1))), Unitary, None),
    Unit => ("std::quantum::unit", 0, Fixed(&[Unit], QUnit), Unitary, None),
    Finish => ("std::quantum::finish", 0, Fixed(&[QUnit], Unit), Unitary, None),
    Split => ("std::quantum::split", 0, TypeRule::Split, Unitary, None),
    Join => ("std::quantum::join", 0, TypeRule::Join, Unitary, None),
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
            assert!(paths.insert(s.path));
            assert_eq!(Primitive::lookup(s.path), Some(*p));
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
        assert_eq!(Primitive::lookup("std::quantum::unknown"), None);
    }
}
