//! Coherent exact-label construction with a fresh native whole-circuit equation.
//!
//! Built-in interfaces use the existing six-bit encoded contract gate; small
//! nominal selector/target functions use the original-source gate on their whole call.
//! The full twelve-bit/64-label route remains pending. Rust sector projections
//! cannot replace independent source, arm, owner or actual-circuit checking.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::contract::exact::{Budget, Exact, Matrix};
use crate::contract::{Circuit, Contract, ContractError, Encoding, MAX_CONTRACT_BITS};

pub(super) mod nominal;
#[cfg(test)]
mod tests;

/// Replace only the synthetic outer positive predicate of an already controlled
/// operation. In particular, the uncontrolled A†/A scaffolding of conjugate_op
/// stays uncontrolled: no Controlled capability for A is invented.
fn lift_arm(
    steps: &mut [CircuitStep],
    selector_bits: usize,
    target_bits: usize,
    label: usize,
    already_controlled: bool,
) -> Result<(), ContractError> {
    let input_bits = target_bits + usize::from(already_controlled);
    let map_axis = |axis: &mut usize| -> Result<(), ContractError> {
        if *axis >= input_bits || (already_controlled && *axis == 0) {
            return Err(ContractError::InvalidCircuit(
                "qmatch arm acts on its synthetic selector or an invalid target axis".into(),
            ));
        }
        *axis = selector_bits + *axis - usize::from(already_controlled);
        Ok(())
    };
    for step in steps {
        let has_outer = if already_controlled {
            let mut outer = step.controls.iter().filter(|control| control.index == 0);
            let present = match outer.next() {
                Some(control) if control.when_one => true,
                Some(_) => {
                    return Err(ContractError::InvalidCircuit(
                        "qmatch controlled arm has a negative outer predicate".into(),
                    ));
                }
                None => false,
            };
            if outer.next().is_some() {
                return Err(ContractError::InvalidCircuit(
                    "qmatch controlled arm duplicates its outer predicate".into(),
                ));
            }
            // Remove before remapping: for a zero-width selector, target axis
            // one becomes zero and must remain an ordinary target control.
            step.controls.retain(|control| control.index != 0);
            present
        } else {
            true
        };
        for control in &mut step.controls {
            map_axis(&mut control.index)?;
        }
        match &mut step.action {
            CircuitAction::Hadamard { target } => map_axis(target)?,
            CircuitAction::Contract { indices, .. } | CircuitAction::Monomial { indices, .. } => {
                for index in indices {
                    map_axis(index)?;
                }
            }
        }
        if has_outer {
            step.controls
                .extend((0..selector_bits).map(|index| BitControl {
                    index,
                    when_one: label & (1 << index) != 0,
                }));
        }
    }
    Ok(())
}

/// Independent canonical block layout: selector axes precede target axes, so
/// row/column (s,y) has integer label s + 2^selector_bits * y. Written arm order
/// never supplies the ordinal, and all coefficients retain their exact phase.
fn block_meaning(sectors: &[Matrix], budget: &mut Budget) -> Result<Matrix, ContractError> {
    let first = sectors
        .first()
        .ok_or(ContractError::Type("empty qmatch table"))?;
    let target = first.rows();
    if sectors
        .iter()
        .any(|matrix| matrix.rows() != target || matrix.cols() != target)
    {
        return Err(ContractError::Type("qmatch arm matrix shape differs"));
    }
    let dimension = sectors.len() * target;
    budget.charge(dimension * dimension)?;
    let mut entries = vec![Exact::zero(); dimension * dimension];
    for (label, sector) in sectors.iter().enumerate() {
        for row in 0..target {
            for column in 0..target {
                entries
                    [(sectors.len() * row + label) * dimension + sectors.len() * column + label] =
                    sector.get(row, column).expect("square arm");
            }
        }
    }
    Matrix::new(dimension, dimension, entries).map_err(Into::into)
}

/// The original complete proposed circuit is submitted to the existing Lean
/// encoded checker. A Rust matrix comparison is not the acceptance decision.
fn check_native(
    kernel: &crate::interchange::native::Kernel,
    circuit: &Circuit,
    expected: Matrix,
    budget: &mut Budget,
) -> Result<(), ContractError> {
    let dimension = expected.rows();
    budget.charge(2 * dimension * dimension)?;
    let mut pending = vec![circuit.basis()];
    while let Some(basis) = pending.pop() {
        budget.charge(6)?;
        match basis {
            crate::contract::BasisType::Pair(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            crate::contract::BasisType::Tuple(fields) => pending.extend(fields),
            _ => {}
        }
    }
    let encoding = Encoding::identity(circuit.basis().clone())?;
    let required = Contract::new(encoding.clone(), encoding, expected, budget)?;
    let checked = kernel.check_encoded(circuit, &required).map_err(|error| {
        if error.code == "limit" {
            ContractError::Limit("native qmatch equation work/profile limit")
        } else if error.code == "contract" {
            ContractError::EquationMismatch
        } else {
            ContractError::InvalidCircuit(error.to_string())
        }
    })?;
    budget.charge(checked.exact_work())?;
    Ok(())
}

impl Lowerer<'_, '_> {
    pub(super) fn quantum_match(
        &mut self,
        module: &str,
        span: Span,
        selection: &QuantumMatch,
        env: &mut Env,
    ) -> Result<Value, CompileError> {
        let selector = self.expr(module, &selection.selector, env)?;
        let selector_slot = self.quantum(module, selection.selector.span, &selector, false)?;
        let target = self.expr(module, &selection.target, env)?;
        let target_slot = self.quantum(module, selection.target.span, &target, false)?;
        let selector_basis = &self.raw.registers[&selector_slot].basis;
        if self.nominal_qmatch.is_some()
            || selector_basis.basis_bits().is_none()
            || self.raw.registers[&target_slot]
                .basis
                .basis_bits()
                .is_none()
        {
            return nominal::emit(
                self,
                module,
                span,
                selection,
                env,
                selector,
                selector_slot,
                target,
                target_slot,
            );
        }
        let selector_bits = match &selector_basis.kind {
            Kind::Unit => 0,
            Kind::Bit => 1,
            Kind::Bits(width) if *width <= 6 => *width as usize,
            _ => return Err(self.error(module, span, ErrorCode::Unsupported,
                "qmatch requires a closed built-in selector here; nominal selectors await typed source/native binding")),
        };
        let count = 1usize << selector_bits;
        if selection.arms.len() != count {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "qmatch must retain every exact ordinal arm",
            ));
        }
        self.compiler
            .charge(module, span, selector_basis.tree_size().nodes + count)?;
        let selector_basis = self.raw.registers[&selector_slot].basis.clone();
        let target_basis = &self.raw.registers[&target_slot].basis;
        let target_bits = target_basis.basis_bits().ok_or_else(|| {
            self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "qmatch target requires an exact finite basis",
            )
        })?;
        if selector_bits + target_bits > MAX_CONTRACT_BITS {
            return Err(self.error(module, span, ErrorCode::Unsupported,
                "qmatch beyond the existing six-bit whole-circuit equation profile awaits the checked kernel restriction/arm-binding extension"));
        }
        self.compiler
            .charge(module, span, target_basis.tree_size().nodes + count)?;
        let target_basis = self.raw.registers[&target_slot].basis.clone();
        let mut expectations = vec![None; count];
        let mut steps = Vec::new();
        for arm in &selection.arms {
            let QuantumLabel::Ordinal(label) = &arm.label else {
                return Err(self.error(
                    module,
                    arm.span,
                    ErrorCode::TypeMismatch,
                    "built-in qmatch requires exact ordinal labels",
                ));
            };
            let label = *label as usize;
            if label >= count || expectations[label].is_some() {
                return Err(self.error(
                    module,
                    arm.span,
                    ErrorCode::TypeMismatch,
                    "qmatch ordinal is duplicated or outside the selector domain",
                ));
            }
            let operation = self.operation_steps(
                module,
                &arm.operation,
                &target_basis,
                env,
                Access::Controlled,
            )?;
            let already_controlled = operation.is_some();
            let mut body = match operation {
                Some(body) => body,
                None => self.static_steps(module, &arm.operation, &target_basis, env)?,
            };
            let expected = self
                .target_meaning(module, &arm.operation, &target_basis)?
                .ok_or_else(|| {
                    self.error(
                        module,
                        arm.span,
                        ErrorCode::Unsupported,
                        "qmatch requires each arm's independently obtained exact meaning",
                    )
                })?;
            self.compiler.charge(
                module,
                span,
                total_size(body.iter().map(super::super::circuit::size))
                    .saturating_add(body.len().saturating_mul(selector_bits + 1)),
            )?;
            lift_arm(
                &mut body,
                selector_bits,
                target_bits,
                label,
                already_controlled,
            )
            .map_err(|error| self.compiler.op_error(module, arm.span, error))?;
            if steps.len().saturating_add(body.len()) > crate::contract::MAX_CONTRACT_STEPS {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::Limit,
                    "qmatch exceeds the existing native contract circuit step bound",
                ));
            }
            steps.extend(body);
            expectations[label] = Some(expected);
        }
        let sectors = expectations
            .into_iter()
            .map(|value| value.expect("complete ordinal table"))
            .collect::<Vec<_>>();
        let expected = block_meaning(&sectors, &mut self.compiler.exact_work)
            .map_err(|error| self.compiler.op_error(module, span, error))?;
        let joined_basis = Ty::pair(selector_basis, target_basis);
        let circuit = Circuit::new(
            super::super::operations::contract_basis(&joined_basis),
            steps,
        )
        .map_err(|error| self.compiler.op_error(module, span, error))?;
        check_native(
            &self.compiler.kernel,
            &circuit,
            expected,
            &mut self.compiler.exact_work,
        )
        .map_err(|error| self.compiler.op_error(module, span, error))?;
        self.compiler.charge(
            module,
            span,
            total_size(circuit.steps().iter().map(super::super::circuit::size)),
        )?;
        let joined =
            self.primitive_call(module, span, PrimitiveId::Join, vec![selector, target])?;
        let slot = self.quantum(module, span, &joined, false)?;
        self.apply_circuit(slot, circuit.steps().to_vec());
        self.primitive_call(module, span, PrimitiveId::Split, vec![joined])
    }
}
