//! Language-owned identities for the audited existing primitive meanings.
//! Names resolve only after lexical binders and ordinary declarations/imports.
//! This catalog grants no native acceptance, inverse/control access or proof.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use crate::ir::Effect;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PrimitiveId {
    H,
    Phase,
    GlobalPhaseEighth,
    Unit,
    Finish,
    Split,
    Join,
    MeasureZ,
    Discard,
    TakeBit,
    PutBit,
    EmptyBits,
    PrependBit,
}

impl PrimitiveId {
    pub const ALL: &'static [Self] = &[
        Self::H,
        Self::Phase,
        Self::GlobalPhaseEighth,
        Self::Unit,
        Self::Finish,
        Self::Split,
        Self::Join,
        Self::MeasureZ,
        Self::Discard,
        Self::TakeBit,
        Self::PutBit,
        Self::EmptyBits,
        Self::PrependBit,
    ];

    pub fn spelling(self) -> &'static str {
        match self {
            Self::H => "h",
            Self::Phase => "phase",
            Self::GlobalPhaseEighth => "global_phase_eighth",
            Self::Unit => "unit",
            Self::Finish => "finish",
            Self::Split => "split",
            Self::Join => "join",
            Self::MeasureZ => "measure_z",
            Self::Discard => "discard",
            Self::TakeBit => "take_bit",
            Self::PutBit => "put_bit",
            Self::EmptyBits => "empty_bits",
            Self::PrependBit => "prepend_bit",
        }
    }

    pub fn lookup_unbound(name: &str) -> Option<Self> {
        Self::ALL.iter().copied().find(|id| id.spelling() == name)
    }

    pub fn effect(self) -> Effect {
        match self {
            Self::MeasureZ | Self::Discard => Effect::Observe,
            _ => Effect::Unitary,
        }
    }

    pub fn natural_arity(self) -> usize {
        match self {
            Self::Phase | Self::TakeBit | Self::PutBit => 2,
            Self::PrependBit => 1,
            _ => 0,
        }
    }

    pub fn runtime_arity(self) -> usize {
        match self {
            Self::EmptyBits => 0,
            Self::Join | Self::PutBit | Self::PrependBit => 2,
            _ => 1,
        }
    }
}

/// Migration guidance is never a compatibility lookup or source authority.
/// Every old source entry has a concrete destination; historical Raw meanings
/// remain separate from source naming and are not changed by this table.
pub(super) fn retired_name_hint(module: &str, name: &str) -> Option<&'static str> {
    match (module, name) {
        ("std::quantum", "h") => Some("; help: call the language primitive `h` without an import"),
        ("std::quantum", "phase") => {
            Some("; help: call the language primitive `phase` without an import")
        }
        ("std::quantum", "phase_eighth") => Some(
            "; help: call `global_phase_eighth` without an import; it applies a global scalar, while `std::gate::t` is the derived relative phase gate",
        ),
        ("std::quantum", "unit") => {
            Some("; help: call the language primitive `unit` without an import")
        }
        ("std::quantum", "finish") => {
            Some("; help: call the language primitive `finish` without an import")
        }
        ("std::quantum", "split") => {
            Some("; help: call the language primitive `split` without an import")
        }
        ("std::quantum", "join") => {
            Some("; help: call the language primitive `join` without an import")
        }
        ("std::quantum", "init0") => {
            Some("; help: import the ordinary checked definition `std::state::init0`")
        }
        ("std::quantum", "x") => Some("; help: import the ordinary checked gate `std::gate::x`"),
        ("std::quantum", "z") => Some("; help: import the ordinary checked gate `std::gate::z`"),
        ("std::quantum", "t") => Some("; help: import the ordinary checked gate `std::gate::t`"),
        ("std::quantum", "s") => Some("; help: import the ordinary checked gate `std::gate::s`"),
        ("std::quantum", "sdg") => {
            Some("; help: import the ordinary checked gate `std::gate::sdg`")
        }
        ("std::quantum", "tdg") => {
            Some("; help: import the ordinary checked gate `std::gate::tdg`")
        }
        ("std::quantum", "id") => Some(
            "; help: import the ordinary checked gate `std::gate::id` and supply its explicit `type(A)` argument",
        ),
        ("std::quantum", "cnot") => {
            Some("; help: import the ordinary checked gate `std::gate::cnot`")
        }
        ("std::quantum", "toffoli") => {
            Some("; help: import the ordinary checked gate `std::gate::toffoli`")
        }
        ("std::quantum", "controlled_phase") => {
            Some("; help: import the ordinary checked gate `std::gate::controlled_phase`")
        }
        ("std::observe", "measure_z") => {
            Some("; help: call the language primitive `measure_z` without an import")
        }
        ("std::observe", "discard") => {
            Some("; help: call the language primitive `discard` without an import")
        }
        ("std::observe", "reset") => {
            Some("; help: import the ordinary checked definition `std::state::reset`")
        }
        ("std::registers", "take_bit") => {
            Some("; help: call the language primitive `take_bit` without an import")
        }
        ("std::registers", "put_bit") => {
            Some("; help: call the language primitive `put_bit` without an import")
        }
        ("std::registers", "empty") => {
            Some("; help: import the ordinary checked definition `std::structure::empty`")
        }
        ("std::registers", "consume_empty") => {
            Some("; help: import the ordinary checked definition `std::structure::consume_empty`")
        }
        ("std::classical", "empty_bits") => {
            Some("; help: call the language primitive `empty_bits` without an import")
        }
        ("std::classical", "prepend_bit") => {
            Some("; help: call the language primitive `prepend_bit` without an import")
        }
        ("std::quantum", _) => Some(
            "; help: std::quantum is retired; use language primitives or ordinary checked stdlib definitions",
        ),
        _ => None,
    }
}
