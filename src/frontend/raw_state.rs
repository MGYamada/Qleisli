//! Shared untrusted Raw emission and current quantum register ownership.
//!
//! Source environments, type/effect judgments, work bounds and diagnostics stay
//! with their adapters. This state issues no accepted handle. Restoring a branch
//! may restore registers and operations, but must never rewind fresh identities.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

use super::ordinary::{self, Boolean};
use super::types::{Kind, Type};
use crate::ir::{CircuitAction, CircuitStep, ClassicalId, RawOp, SingleGate, TokenId, WireId};
use std::collections::BTreeMap;
use std::fmt;

pub(crate) type Slot = u32;

#[derive(Clone, Debug)]
pub(crate) struct Register<N> {
    pub(crate) token: TokenId,
    pub(crate) wires: Vec<WireId>,
    pub(crate) basis: Type<N>,
}
impl<N> Register<N> {
    pub(crate) fn size(&self) -> usize {
        1 + self.wires.len() + self.basis.tree_size().nodes
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum StateError {
    MissingRegister(Slot),
    ExpectedBit(Slot),
    AliasedRegisters,
    BooleanArity { expected: usize, actual: usize },
}
impl fmt::Display for StateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingRegister(slot) => write!(f, "quantum register {slot} is unavailable"),
            Self::ExpectedBit(slot) => {
                write!(f, "quantum register {slot} is not an exact Bit owner")
            }
            Self::AliasedRegisters => f.write_str("gate operands alias one quantum register"),
            Self::BooleanArity { expected, actual } => write!(
                f,
                "Boolean operation requires {expected} operands, found {actual}"
            ),
        }
    }
}
impl std::error::Error for StateError {}

/// One state spans pending arguments and suspended callers. There is deliberately
/// no `Clone` implementation: copying a register snapshot must not copy ID supplies.
pub(crate) struct RawState<N> {
    pub(crate) registers: BTreeMap<Slot, Register<N>>,
    pub(crate) operations: Vec<RawOp>,
    next_token: u32,
    next_wire: u32,
    next_classical: u32,
    next_slot: u32,
}
impl<N> RawState<N> {
    pub(crate) fn new() -> Self {
        Self {
            registers: BTreeMap::new(),
            operations: Vec::new(),
            next_token: 0,
            next_wire: 0,
            next_classical: 0,
            next_slot: 0,
        }
    }
    pub(crate) fn token(&mut self) -> TokenId {
        let id = TokenId(self.next_token);
        self.next_token += 1;
        id
    }
    pub(crate) fn wire(&mut self) -> WireId {
        let id = WireId(self.next_wire);
        self.next_wire += 1;
        id
    }
    pub(crate) fn classical(&mut self) -> ClassicalId {
        let id = ClassicalId(self.next_classical);
        self.next_classical += 1;
        id
    }
    pub(crate) fn slot(&mut self) -> Slot {
        let id = self.next_slot;
        self.next_slot += 1;
        id
    }
    pub(crate) fn register(&mut self, basis: Type<N>, wires: Vec<WireId>) -> Slot {
        let slot = self.slot();
        let token = self.token();
        self.registers.insert(
            slot,
            Register {
                token,
                wires,
                basis,
            },
        );
        slot
    }
    pub(crate) fn init0(&mut self) -> Slot {
        let wire = self.wire();
        let slot = self.register(Type::bit(), vec![wire]);
        self.operations.push(RawOp::Init0 {
            output: self.registers[&slot].token,
            wire,
        });
        slot
    }
    fn bit_token(&self, slot: Slot) -> Result<TokenId, StateError> {
        let register = self
            .registers
            .get(&slot)
            .ok_or(StateError::MissingRegister(slot))?;
        if !matches!(&register.basis.kind, Kind::Bit) || register.wires.len() != 1 {
            return Err(StateError::ExpectedBit(slot));
        }
        Ok(register.token)
    }
    pub(crate) fn gate_bit(&mut self, gate: SingleGate, slot: Slot) -> Result<(), StateError> {
        let input = self.bit_token(slot)?;
        let output = self.token();
        self.operations.push(RawOp::Gate {
            gate,
            input,
            output,
        });
        self.registers
            .get_mut(&slot)
            .ok_or(StateError::MissingRegister(slot))?
            .token = output;
        Ok(())
    }
    pub(crate) fn scalar_eighth(&mut self, slot: Slot) -> Result<(), StateError> {
        let input = self
            .registers
            .get(&slot)
            .ok_or(StateError::MissingRegister(slot))?
            .token;
        let output = self.token();
        // An empty-axis monomial multiplies the entire owner by omega,
        // including an owner with no physical wires. It is not a T gate.
        self.operations.push(RawOp::ApplyUnitary {
            input,
            output,
            steps: vec![CircuitStep {
                controls: vec![],
                action: CircuitAction::Monomial {
                    indices: vec![],
                    permutation: vec![0],
                    phases: vec![1],
                },
            }],
        });
        self.registers
            .get_mut(&slot)
            .ok_or(StateError::MissingRegister(slot))?
            .token = output;
        Ok(())
    }
    pub(crate) fn cnot(&mut self, control: Slot, target: Slot) -> Result<(), StateError> {
        if control == target {
            return Err(StateError::AliasedRegisters);
        }
        let control_in = self.bit_token(control)?;
        let target_in = self.bit_token(target)?;
        let control_out = self.token();
        let target_out = self.token();
        self.operations.push(RawOp::Cnot {
            control: control_in,
            target: target_in,
            control_out,
            target_out,
        });
        self.registers
            .get_mut(&control)
            .ok_or(StateError::MissingRegister(control))?
            .token = control_out;
        self.registers
            .get_mut(&target)
            .ok_or(StateError::MissingRegister(target))?
            .token = target_out;
        Ok(())
    }
    pub(crate) fn measure_z(&mut self, slot: Slot) -> Result<ClassicalId, StateError> {
        self.bit_token(slot)?;
        let register = self
            .registers
            .remove(&slot)
            .ok_or(StateError::MissingRegister(slot))?;
        let output = self.classical();
        self.operations.push(RawOp::MeasureZ {
            input: register.token,
            output,
        });
        Ok(output)
    }
    pub(crate) fn boolean(
        &mut self,
        operation: Boolean,
        inputs: &[ClassicalId],
    ) -> Result<ClassicalId, StateError> {
        let failure = StateError::BooleanArity {
            expected: operation.arity(),
            actual: inputs.len(),
        };
        if inputs.len() != operation.arity() {
            return Err(failure);
        }
        let output = self.classical();
        self.operations
            .push(ordinary::emit(operation, inputs, output).ok_or(failure)?);
        Ok(output)
    }
}
