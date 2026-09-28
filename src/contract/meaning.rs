//! Phase-fixed finite mathematical targets and their concrete implementations.
//!
//! Targets lower canonically to the existing monomial IR. This checked adapter
//! reuses FunctionEvidence; it adds no trusted action or fabricated source fn.
use super::exact::{Budget, Matrix};
use super::function::RetainedIdentity;
use super::{BasisType, Circuit, ContractError, FunctionEvidence, FunctionIdentity};
use crate::ir::*;
use std::sync::Arc;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FiniteMeaning {
    signature: BasisType,
    permutation: Vec<u16>,
    phases: Vec<u8>,
}

impl FiniteMeaning {
    /// A total permutation, with columns/axes in least-significant-leaf order.
    pub fn permutation(signature: BasisType, table: Vec<u16>) -> Result<Self, ContractError> {
        let bits = signature.bits()?;
        if table.len() != 1 << bits {
            return Err(ContractError::Type("meaning table has the wrong dimension"));
        }
        let mut seen = vec![None; table.len()];
        for (input, &output) in table.iter().enumerate() {
            let Some(previous) = seen.get_mut(usize::from(output)) else {
                return Err(ContractError::InvalidCircuit(
                    "permutation output is outside its basis".into(),
                ));
            };
            if let Some(first) = previous.replace(input) {
                return Err(ContractError::InvalidCircuit(format!(
                    "permutation inputs {first} and {input} both map to {output}"
                )));
            }
        }
        Self::new(signature, table, vec![0; 1 << bits])
    }
    /// Diagonal powers of zeta_8, including the scalar phase on Unit.
    pub fn phase(signature: BasisType, phases: Vec<u8>) -> Result<Self, ContractError> {
        let bits = signature.bits()?;
        if phases.len() != 1 << bits {
            return Err(ContractError::Type("meaning table has the wrong dimension"));
        }
        Self::new(signature, (0..1 << bits).collect(), phases)
    }
    fn new(
        signature: BasisType,
        permutation: Vec<u16>,
        phases: Vec<u8>,
    ) -> Result<Self, ContractError> {
        let meaning = Self {
            signature,
            permutation,
            phases,
        };
        meaning.circuit()?;
        Ok(meaning)
    }
    pub fn signature(&self) -> &BasisType {
        &self.signature
    }
    pub fn permutation_table(&self) -> &[u16] {
        &self.permutation
    }
    pub fn phase_table(&self) -> &[u8] {
        &self.phases
    }
    pub fn matrix(&self, budget: &mut Budget) -> Result<Matrix, ContractError> {
        self.circuit()?.matrix(budget)
    }
    fn circuit(&self) -> Result<Circuit, ContractError> {
        Circuit::new(
            self.signature.clone(),
            vec![CircuitStep {
                controls: vec![],
                action: CircuitAction::Monomial {
                    indices: (0..self.signature.bits()?).collect(),
                    permutation: self.permutation.clone(),
                    phases: self.phases.clone(),
                },
            }],
        )
    }
    /// Canonical mathematical-target IR, not a generated `.qli` specification.
    pub fn target_ir(&self) -> Result<RawProgram, ContractError> {
        let bits = self.signature.bits()?;
        Ok(RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: TokenId(0),
                wires: (0..bits as u32).map(WireId).collect(),
                shape: BasisShape { bits: bits as u8 },
            }],
            classical_inputs: vec![],
            operations: vec![RawOp::ApplyUnitary {
                input: TokenId(0),
                output: TokenId(1),
                steps: self.circuit()?.steps().to_vec(),
            }],
            quantum_outputs: vec![TokenId(1)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        })
    }
}

/// Checked binding of a full finite target, exact type tree and raw implementation.
/// Final IR retains the existing sealed receipt, including canonical target IR
/// and source/dependency snapshots. Names or hashes never authorize the binding.
#[derive(Clone, Debug)]
pub struct MeaningEvidence {
    target: FiniteMeaning,
    receipt: Arc<FunctionEvidence>,
}

impl MeaningEvidence {
    pub fn check(
        implementation: RawProgram,
        target: FiniteMeaning,
        identity: FunctionIdentity,
        budget: &mut Budget,
    ) -> Result<Self, ContractError> {
        Self::check_retained(
            implementation,
            target,
            RetainedIdentity::Owned(identity),
            budget,
        )
    }

    pub(crate) fn check_retained(
        implementation: RawProgram,
        target: FiniteMeaning,
        identity: RetainedIdentity,
        budget: &mut Budget,
    ) -> Result<Self, ContractError> {
        let receipt = FunctionEvidence::check_retained_diagnostic(
            target.signature.clone(),
            implementation,
            target.target_ir()?,
            identity,
            budget,
        )
        .map_err(|diagnostic| diagnostic.error)?;
        Ok(Self {
            target,
            receipt: Arc::new(receipt),
        })
    }
    pub fn target(&self) -> &FiniteMeaning {
        &self.target
    }
    /// The existing core receipt binds the entire target, not just its name.
    pub fn receipt(&self) -> Arc<FunctionEvidence> {
        Arc::clone(&self.receipt)
    }
    pub fn check_binding(
        &self,
        implementation: &RawProgram,
        target: &FiniteMeaning,
        identity: &FunctionIdentity,
    ) -> Result<(), ContractError> {
        if target != &self.target {
            return Err(ContractError::EvidenceMismatch);
        }
        self.receipt
            .check_binding(identity, implementation, &target.target_ir()?)
    }
}
