//! Audited language primitive signatures, separate from ordinary checked stdlib.
//! Metadata grants no native acceptance, source preservation or capabilities.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::ast::FnKind;
pub use super::primitive::PrimitiveId;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Primitive {
    pub id: PrimitiveId,
    pub signature: &'static str,
}
impl Primitive {
    pub fn name(self) -> &'static str {
        self.id.spelling()
    }
    pub fn kind(self) -> FnKind {
        match self.id.effect() {
            crate::ir::Effect::Unitary => FnKind::Unitary,
            crate::ir::Effect::Isometry => FnKind::Isometry,
            crate::ir::Effect::Observe => FnKind::Observe,
        }
    }
    pub fn arity(self) -> usize {
        self.id.runtime_arity()
    }
    pub fn natural_arity(self) -> usize {
        self.id.natural_arity()
    }
}
use PrimitiveId::*;
pub const PRIMITIVES: &[Primitive] = &[
    Primitive {
        id: H,
        signature: "(Q<Bit>) -> Q<Bit>",
    },
    Primitive {
        id: Phase,
        signature: "(Q<Bit>) -> Q<Bit>",
    },
    Primitive {
        id: GlobalPhaseEighth,
        signature: "(Q<A>) -> Q<A>",
    },
    Primitive {
        id: Unit,
        signature: "(Unit) -> Q<Unit>",
    },
    Primitive {
        id: Finish,
        signature: "(Q<Unit>) -> Unit",
    },
    Primitive {
        id: Split,
        signature: "(Q<(A,B)>) -> (Q<A>,Q<B>)",
    },
    Primitive {
        id: Join,
        signature: "(Q<A>,Q<B>) -> Q<(A,B)>",
    },
    Primitive {
        id: MeasureZ,
        signature: "(Q<Bit>) -> Bit",
    },
    Primitive {
        id: Discard,
        signature: "(Q<A>) -> Unit",
    },
    Primitive {
        id: TakeBit,
        signature: "(Q<Bits<n>>) -> (Q<Bit>,Q<Bits<n-1>>)",
    },
    Primitive {
        id: PutBit,
        signature: "(Q<Bit>,Q<Bits<n-1>>) -> Q<Bits<n>>",
    },
    Primitive {
        id: EmptyBits,
        signature: "() -> Bits<0>",
    },
    Primitive {
        id: PrependBit,
        signature: "(Bit,Bits<n>) -> Bits<n+1>",
    },
];

/// Descriptor lookup consumes an already resolved language identity.
/// It is not source name resolution and cannot confer primitive authority.
pub fn primitive(id: PrimitiveId) -> &'static Primitive {
    PRIMITIVES
        .iter()
        .find(|item| item.id == id)
        .expect("complete audited language catalog")
}
