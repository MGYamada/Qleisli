//! Shared untrusted source signatures; this catalog supplies no IR evidence.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
//! Concrete capacity limits and lowering/translation checks remain separate.
use super::ast::Effect;

#[derive(Clone, Copy)]
pub(super) enum Size {
    Constant(u32),
    Argument(usize, i8),
}
#[derive(Clone, Copy)]
pub(super) enum TypeShape {
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

pub(super) struct Signature {
    pub path: &'static str,
    pub natural_arity: usize,
    pub inputs: &'static [TypeShape],
    pub output: TypeShape,
    pub effect: Effect,
    pub guard: Guard,
}
macro_rules! primitives {
    ($($name:ident => ($path:literal, $arity:literal, $inputs:expr, $output:expr, $effect:ident, $guard:ident)),+ $(,)?) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub(super) enum Primitive { $($name),+ }
        impl Primitive {
            pub const ALL: &'static [Self] = &[$(Self::$name),+];
            pub fn lookup(path: &str) -> Option<Self> {
                Self::ALL.iter().copied().find(|p| p.signature().path == path)
            }
            pub fn signature(self) -> Signature {
                match self { $(Self::$name => Signature {
                    path: $path, natural_arity: $arity, inputs: $inputs,
                    output: $output, effect: Effect::$effect, guard: Guard::$guard,
                }),+ }
            }
        }
    };
}
use Size::{Argument as A, Constant as C};
use TypeShape::{Bit, Bits, CBit, CBits, Tuple};
primitives! {
    H => ("std::quantum::h", 0, &[Bit], Bit, Unitary, None),
    X => ("std::quantum::x", 0, &[Bit], Bit, Unitary, None),
    Cnot => ("std::quantum::cnot", 0, &[Bit, Bit], Tuple(&[Bit, Bit]), Unitary, None),
    Phase => ("std::quantum::phase", 2, &[Bit], Bit, Unitary, None),
    ControlledPhase => ("std::quantum::controlled_phase", 2, &[Bit, Bit], Tuple(&[Bit, Bit]), Unitary, None),
    Init0 => ("std::quantum::init0", 0, &[], Bit, Iso, None),
    MeasureZ => ("std::observe::measure_z", 0, &[Bit], CBit, Observe, None),
    TakeBit => ("std::registers::take_bit", 2, &[Bits(A(0, 0))], Tuple(&[Bit, Bits(A(0, -1))]), Unitary, RegisterIndex),
    PutBit => ("std::registers::put_bit", 2, &[Bit, Bits(A(0, -1))], Bits(A(0, 0)), Unitary, RegisterIndex),
    Empty => ("std::registers::empty", 0, &[], Bits(C(0)), Unitary, None),
    ConsumeEmpty => ("std::registers::consume_empty", 0, &[Bits(C(0))], Tuple(&[]), Unitary, None),
    EmptyBits => ("std::classical::empty_bits", 0, &[], CBits(C(0)), Unitary, None),
    PrependBit => ("std::classical::prepend_bit", 1, &[CBit, CBits(A(0, 0))], CBits(A(0, 1)), Unitary, None),
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
                TypeShape::Bit
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
            s.inputs.iter().for_each(|f| shape(*f, s.natural_arity));
            shape(s.output, s.natural_arity);
        }
        assert_eq!(Primitive::lookup("std::quantum::unknown"), None);
    }
}
