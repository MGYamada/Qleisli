//! Bounded untrusted Meaning expressions shared by concrete source adapters.
//! A reference identity is retained even when its denotation is monomial.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
use super::resolve::DefId;
use crate::contract::{
    BasisType, ContractError, FunctionEvidence, exact::Budget, function::RetainedIdentity,
    meaning::FiniteMeaning,
};
use crate::interchange::{RootInterface, Version, native};
use crate::ir::*;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

#[derive(Clone, Debug)]
pub(super) struct Target {
    signature: BasisType,
    node: Arc<Node>,
    cells: usize,
    depth: usize,
}
#[derive(Debug)]
enum Node {
    Monomial(FiniteMeaning),
    Reference(DefId),
    Compose(Target, Target),
    Tensor(Target, Target),
}
impl Target {
    pub(super) fn monomial(target: FiniteMeaning) -> Self {
        Self {
            signature: target.signature().clone(),
            cells: 1 + target.permutation_table().len() + target.phase_table().len(),
            node: Arc::new(Node::Monomial(target)),
            depth: 1,
        }
    }
    pub(super) fn reference(
        signature: BasisType,
        definition: DefId,
    ) -> Result<Self, ContractError> {
        signature.bits()?;
        Ok(Self {
            signature,
            node: Arc::new(Node::Reference(definition)),
            cells: 1,
            depth: 1,
        })
    }
    pub(super) fn signature(&self) -> &BasisType {
        &self.signature
    }
    pub(super) fn cells(&self) -> usize {
        self.cells
    }
    pub(super) fn finite(&self) -> Result<&FiniteMeaning, ContractError> {
        match self.node.as_ref() {
            Node::Monomial(target) => Ok(target),
            _ => Err(ContractError::Type(
                "FiniteMeaning is monomial-only; a reference-containing target requires native artifact-bound checking",
            )),
        }
    }
    pub(super) fn references(&self) -> BTreeSet<DefId> {
        let mut pending = vec![self];
        let mut references = BTreeSet::new();
        while let Some(target) = pending.pop() {
            match target.node.as_ref() {
                Node::Reference(id) => {
                    references.insert(*id);
                }
                Node::Compose(a, b) | Node::Tensor(a, b) => pending.extend([a, b]),
                Node::Monomial(_) => {}
            }
        }
        references
    }
    pub(super) fn compose(&self, next: &Self) -> Result<Self, ContractError> {
        if self.signature != next.signature {
            return Err(ContractError::Type(
                "Meaning composition requires identical exact basis trees",
            ));
        }
        self.binary(next, false)
    }
    pub(super) fn tensor(&self, right: &Self) -> Result<Self, ContractError> {
        self.binary(right, true)
    }
    /// Build a request retaining every original reference body and dependency.
    /// Native self-equations validate child artifacts; the caller must still
    /// independently compare the actual implementation with this request.
    pub(super) fn materialize(
        &self,
        kernel: &native::Kernel,
        references: &BTreeMap<DefId, RawProgram>,
        identity: &dyn Fn() -> RetainedIdentity,
        budget: &mut Budget,
    ) -> Result<RawProgram, ContractError> {
        self.materialize_inner(kernel, references, identity, budget, &mut 0)
    }
    fn materialize_inner(
        &self,
        kernel: &native::Kernel,
        references: &BTreeMap<DefId, RawProgram>,
        identity: &dyn Fn() -> RetainedIdentity,
        budget: &mut Budget,
        bytes: &mut usize,
    ) -> Result<RawProgram, ContractError> {
        budget.charge(self.cells)?;
        let raw = match self.node.as_ref() {
            Node::Monomial(target) => target.target_ir()?,
            Node::Reference(id) => references
                .get(id)
                .ok_or(ContractError::Type("original reference artifact is absent"))?
                .clone(),
            Node::Compose(left, right) | Node::Tensor(left, right) => {
                let tensor = matches!(self.node.as_ref(), Node::Tensor(..));
                let mut steps = Vec::with_capacity(2);
                for (child, offset) in [
                    (left, 0),
                    (right, if tensor { left.signature.bits()? } else { 0 }),
                ] {
                    let raw =
                        child.materialize_inner(kernel, references, identity, budget, bytes)?;
                    let evidence = FunctionEvidence::check_retained_with_kernel(
                        kernel,
                        child.signature.clone(),
                        raw.clone(),
                        raw,
                        identity(),
                        budget,
                    )
                    .map_err(|e| e.error)?;
                    steps.push(CircuitStep {
                        controls: vec![],
                        action: CircuitAction::Contract {
                            indices: (offset..offset + child.signature.bits()?).collect(),
                            evidence: Arc::new(evidence),
                            adjoint: false,
                        },
                    });
                }
                let bits = self.signature.bits()?;
                RawProgram {
                    quantum_inputs: vec![QuantumPort {
                        token: TokenId(0),
                        wires: (0..bits as u32).map(WireId).collect(),
                        shape: BasisShape { bits: bits as u8 },
                    }],
                    classical_inputs: vec![],
                    operations: vec![RawOp::ApplyUnitary {
                        input: TokenId(0),
                        output: TokenId(1),
                        steps,
                    }],
                    quantum_outputs: vec![TokenId(1)],
                    classical_outputs: vec![],
                    declared_effect: Effect::Unitary,
                }
            }
        };
        let interface = RootInterface {
            input: self.signature.clone(),
            output: self.signature.clone(),
        };
        let proposal = native::Proposal::from_raw(&raw, Some(&interface), Version::V2, None)
            .map_err(|e| ContractError::InvalidCircuit(e.to_string()))?;
        *bytes = bytes.saturating_add(proposal.artifact().len());
        if *bytes > 100_000 {
            return Err(ContractError::Limit(
                "Meaning target exceeds 100000 aggregate artifact bytes",
            ));
        }
        budget.charge(proposal.artifact().len())?;
        Ok(raw)
    }
    fn binary(&self, right: &Self, tensor: bool) -> Result<Self, ContractError> {
        let signature = if tensor {
            BasisType::pair(self.signature.clone(), right.signature.clone())
        } else {
            self.signature.clone()
        };
        signature.bits()?;
        let depth = 1 + self.depth.max(right.depth);
        let cells = self.cells.saturating_add(right.cells).saturating_add(1);
        if depth > 64 || cells > 4096 {
            return Err(ContractError::Limit(
                "Meaning expression exceeds 4096 cells or depth 64",
            ));
        }
        if let (Ok(left), Ok(right)) = (self.finite(), right.finite()) {
            return Ok(Self::monomial(if tensor {
                left.tensor(right)?
            } else {
                left.compose(right)?
            }));
        }
        Ok(Self {
            signature,
            node: Arc::new(if tensor {
                Node::Tensor(self.clone(), right.clone())
            } else {
                Node::Compose(self.clone(), right.clone())
            }),
            cells,
            depth,
        })
    }
}
