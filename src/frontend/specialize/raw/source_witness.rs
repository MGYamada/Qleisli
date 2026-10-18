//! Inert retained original Raw source behind an actually executed checked leaf.
//! Existing native equations and Raw source replay remain mandatory; this is
//! neither hierarchy/source equality nor a new acceptance authority.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::contract::FunctionEvidence;
use crate::ir::{CircuitAction, RawOp};

/// Original proposal and issued native snapshots bound to one actual unitary leaf.
#[derive(Debug)]
pub(in crate::frontend::specialize) struct SourceOperationWitness {
    original: Arc<RawSourceProposal>,
    key: super::super::elaborate::OperationKey,
    boundary: UnitaryBoundary,
    meaning: Arc<crate::contract::exact::Matrix>,
    accepted_original: crate::AcceptedProgram,
    accepted_leaf: crate::AcceptedProgram,
    reference: Option<Arc<FunctionEvidence>>,
    retained_cells: usize,
}

/// Debit shared exact work before source storage or byte comparison.
fn charge(budget: &mut Budget, cells: usize) -> Result<()> {
    budget
        .charge(cells)
        .map_err(|error| Error::new("limit", Span::default(), error.to_string()))
}
/// Count the retained exact basis tree, including zero-width structure.
fn type_cells(ty: &BasisType) -> usize {
    match ty {
        BasisType::Pair(a, b) => 1usize
            .saturating_add(type_cells(a))
            .saturating_add(type_cells(b)),
        BasisType::Tuple(fields) => fields
            .iter()
            .fold(1usize, |n, field| n.saturating_add(type_cells(field))),
        _ => 1,
    }
}
/// Count the copied shell of a shared accepted native program.
fn program_clone_cells(program: &crate::AcceptedProgram) -> usize {
    let interface = program.root_interface().map_or(0, |ports| {
        type_cells(&ports.input).saturating_add(type_cells(&ports.output))
    });
    program
        .output_ports()
        .iter()
        .fold(16usize.saturating_add(interface), |n, port| {
            n.saturating_add(port.wires.len()).saturating_add(3)
        })
}
/// Count the retained original lexical selector and descendant path.
fn site_cells(site: &OperationSite) -> usize {
    match site {
        OperationSite::Binding(_, name) => name.len().saturating_add(2),
        OperationSite::Step(..) => 2,
        OperationSite::Descendant(site, path) => site_cells(site)
            .saturating_add(path.len())
            .saturating_add(2),
    }
}
/// Count source shells and ports whose lifetime this witness extends.
fn cloned_proposal_cells(original: &RawSourceProposal) -> usize {
    original
        .source
        .witness_clone_cells()
        .saturating_add(original.binding.as_ref().map_or(0, site_cells))
        .saturating_add(original.finite_boundary.as_ref().map_or(0, |boundary| {
            type_cells(boundary.signature())
                .saturating_add(boundary.input().wires.len())
                .saturating_add(boundary.output().wires.len())
                .saturating_add(8)
        }))
        .saturating_add(16)
}

impl SourceOperationWitness {
    /// Retain the same checked original proposal within the caller aggregate.
    pub(super) fn from_owned(
        original: RawSourceProposal,
        leaf: &CheckedUnitaryLeaf,
        accepted_original: Option<crate::AcceptedProgram>,
        reference: Option<Arc<FunctionEvidence>>,
        budget: &mut Budget,
        aggregate: &mut usize,
    ) -> Result<Arc<Self>> {
        let operation = original.operation().ok_or_else(|| {
            invalid(
                Span::default(),
                "source witness lacks its original operation site",
            )
        })?;
        let boundary = original.finite_boundary.as_ref().ok_or_else(|| {
            invalid(
                operation.span(),
                "source witness lacks its exact unitary source boundary",
            )
        })?;
        if boundary.signature() != leaf.boundary().signature() {
            return Err(invalid(
                operation.span(),
                "source witness changes its exact original basis tree",
            ));
        }
        let key_cells = operation.expanded_key_cells();
        let boundary_cells = type_cells(leaf.boundary().signature())
            .saturating_add(leaf.boundary().input().wires.len())
            .saturating_add(leaf.boundary().output().wires.len())
            .saturating_add(8);
        // The checked leaf already owns this bounded exact matrix. Share it;
        // retaining a second JSON encoding would artificially reduce its profile.
        let meaning = leaf.shared_meaning();
        let original_clone = accepted_original
            .as_ref()
            .map_or_else(|| program_clone_cells(leaf.program()), |_| 0);
        let cells = cloned_proposal_cells(&original)
            .saturating_add(key_cells)
            .saturating_add(boundary_cells)
            .saturating_add(1)
            .saturating_add(program_clone_cells(leaf.program()))
            .saturating_add(original_clone)
            .saturating_add(32);
        let total = aggregate.checked_add(cells).ok_or_else(|| {
            Error::new(
                "limit",
                operation.span(),
                "source witness retention overflow",
            )
        })?;
        if total > MAX_CELLS {
            return Err(Error::new(
                "limit",
                operation.span(),
                "source witnesses exceed 100000 retained cells",
            ));
        }
        charge(budget, cells)?;
        *aggregate = total;
        let key = operation.key();
        let accepted_original = accepted_original.unwrap_or_else(|| leaf.program().clone());
        if accepted_original.artifact() != original.payload()
            || accepted_original.raw().declared_effect != Effect::Unitary
        {
            return Err(invalid(
                operation.span(),
                "source witness accepted body differs from original Raw bytes or effect",
            ));
        }
        if leaf.payload() != leaf.program().artifact() {
            return Err(invalid(
                operation.span(),
                "checked leaf payload differs from its retained accepted artifact",
            ));
        }
        charge(budget, leaf.meaning().entries().len().saturating_mul(4))?;
        if reference
            .as_ref()
            .is_some_and(|receipt| receipt.meaning() != leaf.meaning())
        {
            return Err(invalid(
                operation.span(),
                "reference witness changes its checked requested matrix",
            ));
        }
        if reference.is_none() && leaf.payload() != original.payload() {
            return Err(invalid(
                operation.span(),
                "source witness substitutes its actual checked provider bytes",
            ));
        }
        let witness = Arc::new(Self {
            key,
            boundary: leaf.boundary().clone(),
            meaning,
            accepted_original,
            accepted_leaf: leaf.program().clone(),
            reference,
            original: Arc::new(original),
            retained_cells: cells,
        });
        witness.validate_reference(budget)?;
        Ok(witness)
    }
    /// Preflight one private clone of the already checked original proposal.
    pub(super) fn from_borrowed(
        check: &SourceMeaningCheck<'_>,
        budget: &mut Budget,
        aggregate: &mut usize,
    ) -> Result<Arc<Self>> {
        let clone_cells = cloned_proposal_cells(check.source);
        // Standalone checks have no collector's original-payload allowance.
        let payload_cells = check.source.payload().len();
        let preflight = aggregate
            .checked_add(clone_cells)
            .and_then(|n| n.checked_add(payload_cells))
            .ok_or_else(|| {
                Error::new(
                    "limit",
                    Span::default(),
                    "source witness clone retention overflow",
                )
            })?;
        if preflight > MAX_CELLS {
            return Err(Error::new(
                "limit",
                Span::default(),
                "source witnesses exceed 100000 retained cells",
            ));
        }
        charge(budget, clone_cells.saturating_add(payload_cells))?;
        *aggregate = aggregate.saturating_add(payload_cells);
        let mut witness = Self::from_owned(
            check.source.clone(),
            check.leaf(),
            None,
            None,
            budget,
            aggregate,
        )?;
        let retained = payload_cells.saturating_add(witness.retained_cells());
        Arc::get_mut(&mut witness)
            .expect("new unshared witness")
            .retained_cells = retained;
        Ok(witness)
    }

    /// Full original operation identity, including requested meanings and effects.
    pub(in crate::frontend::specialize) fn key(&self) -> &super::super::elaborate::OperationKey {
        &self.key
    }
    /// Borrow the operation selected by the exact retained lexical site.
    pub(in crate::frontend::specialize) fn operation(&self) -> &super::super::SourceOperation {
        self.original
            .operation()
            .expect("witness captures original operation")
    }
    /// Borrow the original immutable source collection.
    pub(in crate::frontend::specialize) fn source(&self) -> &ElaboratedProgram {
        self.original.source()
    }
    /// Actual checked leaf ports, retaining the full exact basis tree.
    pub(in crate::frontend::specialize) fn boundary(&self) -> &UnitaryBoundary {
        &self.boundary
    }
    /// Actual executed checked leaf bytes; reference wrappers remain wrappers.
    pub(in crate::frontend::specialize) fn payload(&self) -> &[u8] {
        self.accepted_leaf.artifact()
    }
    /// Same immutable exact requested matrix, including global phase.
    #[cfg(test)]
    pub(in crate::frontend::specialize) fn meaning(&self) -> &crate::contract::exact::Matrix {
        &self.meaning
    }
    /// Storage charged when this immutable witness was retained.
    pub(in crate::frontend::specialize) fn retained_cells(&self) -> usize {
        self.retained_cells
    }
    /// Compare original collection and complete operation ports under shared work.
    pub(in crate::frontend::specialize) fn matches(
        &self,
        source: &ElaboratedProgram,
        operation: &super::super::SourceOperation,
        budget: &mut Budget,
    ) -> Result<bool> {
        charge(
            budget,
            source
                .contracts
                .len()
                .saturating_add(source.instruments.len())
                .saturating_add(source.meaning_artifacts.len())
                .saturating_add(operation.expanded_key_cells())
                .saturating_add(8),
        )?;
        if !self.original.source.same_witness_source(source) || self.key != operation.key() {
            return Ok(false);
        }
        let (expected, expected_effect, _) = super::operation_signature(
            self.operation(),
            self.source().definitions(),
            self.operation().span(),
        )?;
        let (actual, actual_effect, _) =
            super::operation_signature(operation, source.definitions(), operation.span())?;
        let cells = [expected.input, expected.output, actual.input, actual.output]
            .into_iter()
            .try_fold(0usize, |n, ty| {
                ty.storage_size(4096, 64)
                    .map(|size| n.saturating_add(size.nodes))
                    .ok_or_else(|| {
                        invalid(
                            operation.span(),
                            "source witness operation ports exceed type storage",
                        )
                    })
            })?;
        charge(budget, cells)?;
        Ok(expected.input == actual.input
            && expected.output == actual.output
            && expected_effect == actual_effect)
    }
    /// Compare actual immutable leaf bytes and its decoded exact required matrix.
    pub(in crate::frontend::specialize) fn check_leaf_bytes(
        &self,
        payload: &[u8],
        meaning: &[u8],
        budget: &mut Budget,
    ) -> Result<()> {
        charge(
            budget,
            payload
                .len()
                .saturating_add(self.payload().len())
                .saturating_add(meaning.len())
                .saturating_add(self.meaning.entries().len().saturating_mul(4)),
        )?;
        if payload != self.payload() {
            return Err(invalid(
                self.operation().span(),
                "actual leaf changes original checked Raw bytes",
            ));
        }
        let actual = crate::interchange::finite_matrix::decode(meaning, budget)
            .map_err(|error| Error::new(error.code, self.operation().span(), error.to_string()))?;
        if &actual != self.meaning.as_ref() {
            return Err(invalid(
                self.operation().span(),
                "actual leaf changes its exact required matrix",
            ));
        }
        Ok(())
    }
    /// Invoke existing source replay after binding the original immutable collection.
    fn validate_source(
        &self,
        source: &ElaboratedProgram,
        operation: &super::super::SourceOperation,
        budget: &mut Budget,
    ) -> Result<()> {
        if !self.matches(source, operation, budget)? {
            return Err(invalid(
                operation.span(),
                "source witness belongs to another original source operation",
            ));
        }
        self.validate_reference(budget)?;
        self.original
            .replay_with_work(&self.accepted_original, budget)
    }
    /// Bind actual bytes and invoke the existing original Raw source replay.
    pub(in crate::frontend::specialize) fn validate(
        &self,
        source: &ElaboratedProgram,
        operation: &super::super::SourceOperation,
        payload: &[u8],
        meaning: &[u8],
        budget: &mut Budget,
    ) -> Result<()> {
        self.check_leaf_bytes(payload, meaning, budget)?;
        self.validate_source(source, operation, budget)
    }
    /// Keep the original reference receipt and actual wrapper exactly associated.
    fn validate_reference(&self, budget: &mut Budget) -> Result<()> {
        let Some(receipt) = &self.reference else {
            return Ok(());
        };
        let original = self.accepted_original.raw();
        let actual = self.accepted_leaf.raw();
        charge(
            budget,
            self.original
                .payload()
                .len()
                .saturating_add(self.payload().len()),
        )?;
        // Fresh native receipt decoding changes issued proof identities. Bind
        // complete canonical pair/dependency bytes, never host Eq or a hash.
        charge(
            budget,
            receipt
                .snapshot_key()
                .len()
                .saturating_mul(2)
                .saturating_add(self.original.payload().len()),
        )?;
        let original_key = crate::interchange::function_snapshot_key(
            receipt.signature(),
            original,
            receipt.specification(),
            receipt.identity_parts(),
        )
        .map_err(|error| invalid(self.operation().span(), &error.to_string()))?;
        if original_key.as_ref() != receipt.snapshot_key().as_ref()
            || receipt.signature() != self.boundary.signature()
            || actual.quantum_inputs.as_slice() != std::slice::from_ref(self.boundary.input())
            || actual.quantum_outputs.as_slice() != [self.boundary.output().token]
            || !actual.classical_inputs.is_empty()
            || !actual.classical_outputs.is_empty()
            || actual.declared_effect != Effect::Unitary
        {
            return Err(invalid(
                self.operation().span(),
                "reference witness changes original implementation or complete wrapper ports",
            ));
        }
        let [
            RawOp::ApplyUnitary {
                input,
                output,
                steps,
            },
        ] = actual.operations.as_slice()
        else {
            return Err(invalid(
                self.operation().span(),
                "reference witness lacks its actual checked wrapper",
            ));
        };
        let [step] = steps.as_slice() else {
            return Err(invalid(
                self.operation().span(),
                "reference witness changes its checked interval",
            ));
        };
        let CircuitAction::Contract {
            indices,
            evidence,
            adjoint,
        } = &step.action
        else {
            return Err(invalid(
                self.operation().span(),
                "reference witness replaces its original receipt",
            ));
        };
        if *input != self.boundary.input().token
            || *output != self.boundary.output().token
            || !step.controls.is_empty()
            || *adjoint
            || indices
                .iter()
                .copied()
                .ne(0..self.boundary.input().wires.len())
        {
            return Err(invalid(
                self.operation().span(),
                "reference witness changes original direction or axes",
            ));
        }
        charge(
            budget,
            evidence
                .snapshot_key()
                .len()
                .saturating_add(receipt.snapshot_key().len()),
        )?;
        if evidence.snapshot_key().as_ref() != receipt.snapshot_key().as_ref() {
            return Err(invalid(
                self.operation().span(),
                "reference witness changes original request or receipt dependencies",
            ));
        }
        Ok(())
    }
}
