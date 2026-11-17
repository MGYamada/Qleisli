//! Exact-zero presentation for a closed, bounded subset of accepted Raw IR.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::ExecutableProgram;
use crate::AcceptedProgram;
use crate::contract::exact::{Budget, Exact, ExactError};
use crate::contract::{Circuit, ContractError, MAX_CONTRACT_BITS, MAX_CONTRACT_STEPS};
use crate::ir::{BitControl, CircuitAction, CircuitStep, RawOp, RawProgram, TokenId, UnitaryStep};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use self::ExactZeroUnavailable::{Limit, Unsupported};

const MAX_RAW_OPERATIONS: usize = 2_048;
const MAX_EXACT_WORK: usize = 1_000_000;

/// Why the bounded reference calculation could not classify zero outcomes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExactZeroUnavailable {
    Unsupported,
    Limit,
    Arithmetic,
}

impl fmt::Display for ExactZeroUnavailable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Unsupported => "outside the exact-zero terminal profile",
            Self::Limit => "exact-zero calculation exceeds its work or size limit",
            Self::Arithmetic => "exact-zero arithmetic capacity exhausted",
        })
    }
}

impl std::error::Error for ExactZeroUnavailable {}

fn exact_failure(error: ContractError) -> ExactZeroUnavailable {
    match error {
        ContractError::Arithmetic(ExactError::ArithmeticCapacity) => {
            ExactZeroUnavailable::Arithmetic
        }
        ContractError::Limit(_)
        | ContractError::Arithmetic(ExactError::WorkLimit | ExactError::Dimension { .. }) => Limit,
        _ => Unsupported,
    }
}

type Result<T> = std::result::Result<T, ExactZeroUnavailable>;

/// Classify exactly zero outcome words in an already accepted closed program.
///
/// The reference calculation covers a pure Raw prefix on at most six axes
/// followed by a complete terminal Z measurement of those axes. Every measured
/// bit must appear once in the visible result. Bits in the returned words
/// follow the original Raw classical output order.
///
/// This calculation supplies presentation detail. It does not change the
/// floating-point distribution or issue semantic evidence.
pub fn terminal_exact_zeros(
    program: &AcceptedProgram,
) -> std::result::Result<BTreeSet<Vec<bool>>, ExactZeroUnavailable> {
    if program.has_source_parameters() {
        return Err(Unsupported);
    }
    raw_terminal_zeros(program.raw())
}

fn raw_terminal_zeros(raw: &RawProgram) -> Result<BTreeSet<Vec<bool>>> {
    if !raw.quantum_inputs.is_empty()
        || !raw.classical_inputs.is_empty()
        || !raw.quantum_outputs.is_empty()
    {
        return Err(Unsupported);
    }
    if raw.operations.len() > MAX_RAW_OPERATIONS || raw.classical_outputs.len() > MAX_CONTRACT_BITS
    {
        return Err(Limit);
    }
    let readout_start = raw
        .operations
        .iter()
        .position(|op| matches!(op, RawOp::MeasureZ { .. }))
        .unwrap_or(raw.operations.len());
    let (prefix, readout) = raw.operations.split_at(readout_start);
    let mut projected = Prefix::default();
    for operation in prefix {
        projected.append(operation)?;
    }

    // A complete visible readout puts each word in one-to-one correspondence
    // with a basis row. No branch histories enter this calculation.
    let mut measured = BTreeMap::new();
    for operation in readout {
        let RawOp::MeasureZ { input, output } = operation else {
            return Err(Unsupported);
        };
        let axis = projected.take_bit(*input)?;
        if measured.insert(*output, axis).is_some() {
            return Err(Unsupported);
        }
    }
    if !projected.owners.is_empty()
        || measured.len() != projected.axes
        || raw.classical_outputs.len() != projected.axes
    {
        return Err(Unsupported);
    }
    let output_axes = raw
        .classical_outputs
        .iter()
        .map(|id| measured.remove(id).ok_or(Unsupported))
        .collect::<Result<Vec<_>>>()?;

    let circuit =
        Circuit::for_coordinates(projected.axes, projected.steps).map_err(exact_failure)?;
    let amplitudes = circuit
        .vacuum_column(&mut Budget::new(MAX_EXACT_WORK))
        .map_err(exact_failure)?;
    Ok(amplitudes
        .into_iter()
        .enumerate()
        .filter(|&(_, value)| value == Exact::zero())
        .map(|(row, _)| {
            output_axes
                .iter()
                .map(|&axis| super::bit(row, axis))
                .collect()
        })
        .collect())
}

#[derive(Default)]
struct Prefix {
    axes: usize,
    owners: BTreeMap<TokenId, Vec<usize>>,
    steps: Vec<CircuitStep>,
}

impl Prefix {
    fn take(&mut self, id: TokenId) -> Result<Vec<usize>> {
        self.owners.remove(&id).ok_or(Unsupported)
    }

    fn take_bit(&mut self, id: TokenId) -> Result<usize> {
        match self.take(id)?.as_slice() {
            [axis] => Ok(*axis),
            _ => Err(Unsupported),
        }
    }

    fn check_step_count(&self, additional: usize) -> Result<()> {
        if additional > MAX_CONTRACT_STEPS - self.steps.len() {
            return Err(Limit);
        }
        Ok(())
    }

    fn push_step(&mut self, mut step: CircuitStep, axes: &[usize]) -> Result<()> {
        let axis = |local| axes.get(local).copied().ok_or(Unsupported);
        for control in &mut step.controls {
            control.index = axis(control.index)?;
        }
        match &mut step.action {
            CircuitAction::Hadamard { target } => *target = axis(*target)?,
            CircuitAction::Monomial { indices, .. } => {
                for index in indices {
                    *index = axis(*index)?;
                }
            }
            CircuitAction::Contract { .. } => return Err(Unsupported),
        }
        self.steps.push(step);
        Ok(())
    }

    fn push_primitive(&mut self, op: UnitaryStep, axes: &[usize]) -> Result<()> {
        self.check_step_count(1)?;
        self.push_step(op.to_circuit_step(), axes)
    }

    fn lift_basis(
        &mut self,
        input: TokenId,
        output: TokenId,
        output_width: usize,
        table: &[u16],
    ) -> Result<()> {
        let mut axes = self.take(input)?;
        let added = output_width.checked_sub(axes.len()).ok_or(Unsupported)?;
        if added > MAX_CONTRACT_BITS - self.axes {
            return Err(Limit);
        }
        if table.len() != 1 << axes.len() {
            return Err(Unsupported);
        }
        self.check_step_count(1)?;

        // The appended axes are still zero when this operation runs, so only
        // the low input labels occur. Extend the injection to a permutation
        // by assigning the unused images to the unreachable input labels.
        let dimension = 1 << output_width;
        let mut used_images = vec![false; dimension];
        for &image in table {
            let used = used_images.get_mut(usize::from(image)).ok_or(Unsupported)?;
            if std::mem::replace(used, true) {
                return Err(Unsupported);
            }
        }
        let mut permutation = Vec::with_capacity(dimension);
        permutation.extend_from_slice(table);
        permutation.extend(
            used_images
                .iter()
                .enumerate()
                .filter(|&(_, used)| !used)
                .map(|(image, _)| image as u16),
        );

        axes.extend(self.axes..self.axes + added);
        self.axes += added;
        self.steps.push(CircuitStep {
            controls: Vec::new(),
            action: CircuitAction::Monomial {
                indices: axes.clone(),
                permutation,
                phases: vec![0; dimension],
            },
        });
        self.owners.insert(output, axes);
        Ok(())
    }

    fn append(&mut self, operation: &RawOp) -> Result<()> {
        match operation {
            RawOp::Init0 { output, .. } => {
                if self.axes == MAX_CONTRACT_BITS {
                    return Err(Limit);
                }
                // Dense positions are assigned in allocation order. A later
                // fresh zero axis commutes with the preceding disjoint gates.
                self.owners.insert(*output, vec![self.axes]);
                self.axes += 1;
            }
            RawOp::PackUnit { output } => {
                self.owners.insert(*output, Vec::new());
            }
            RawOp::UnpackUnit { input } => {
                if !self.take(*input)?.is_empty() {
                    return Err(Unsupported);
                }
            }
            RawOp::Join {
                left,
                right,
                output,
            } => {
                let mut axes = self.take(*left)?;
                axes.extend(self.take(*right)?);
                self.owners.insert(*output, axes);
            }
            RawOp::Split {
                input,
                left,
                right,
                left_bits,
            } => {
                let mut axes = self.take(*input)?;
                let split = usize::from(*left_bits);
                if split > axes.len() {
                    return Err(Unsupported);
                }
                let right_axes = axes.split_off(split);
                self.owners.insert(*left, axes);
                self.owners.insert(*right, right_axes);
            }
            RawOp::LiftBasis {
                input,
                output,
                output_wires,
                table,
            } => self.lift_basis(*input, *output, output_wires.len(), table)?,
            RawOp::Gate {
                gate,
                input,
                output,
            } => {
                let target = self.take_bit(*input)?;
                self.push_primitive(
                    UnitaryStep::Gate {
                        gate: *gate,
                        target_index: 0,
                    },
                    &[target],
                )?;
                self.owners.insert(*output, vec![target]);
            }
            RawOp::Cnot {
                control,
                target,
                control_out,
                target_out,
            } => {
                let control = self.take_bit(*control)?;
                let target = self.take_bit(*target)?;
                self.push_primitive(
                    UnitaryStep::Cnot {
                        control_index: 0,
                        target_index: 1,
                    },
                    &[control, target],
                )?;
                self.owners.insert(*control_out, vec![control]);
                self.owners.insert(*target_out, vec![target]);
            }
            RawOp::Toffoli {
                control_a,
                control_b,
                target,
                control_a_out,
                control_b_out,
                target_out,
            } => {
                let first = self.take_bit(*control_a)?;
                let second = self.take_bit(*control_b)?;
                let target = self.take_bit(*target)?;
                self.push_primitive(
                    UnitaryStep::Toffoli {
                        control_a_index: 0,
                        control_b_index: 1,
                        target_index: 2,
                    },
                    &[first, second, target],
                )?;
                self.owners.insert(*control_a_out, vec![first]);
                self.owners.insert(*control_b_out, vec![second]);
                self.owners.insert(*target_out, vec![target]);
            }
            RawOp::QuantumIf {
                control,
                target,
                control_out,
                target_out,
                zero_ops,
                one_ops,
            } => {
                self.check_step_count(zero_ops.len().saturating_add(one_ops.len()))?;
                let control = self.take_bit(*control)?;
                let mut axes = self.take(*target)?;
                let target_bits = axes.len();
                axes.push(control);
                for (when_one, arm) in [(false, zero_ops), (true, one_ops)] {
                    for operation in arm {
                        let mut step = operation.to_circuit_step();
                        step.controls.push(BitControl {
                            index: target_bits,
                            when_one,
                        });
                        self.push_step(step, &axes)?;
                    }
                }
                axes.truncate(target_bits);
                self.owners.insert(*control_out, vec![control]);
                self.owners.insert(*target_out, axes);
            }
            RawOp::ApplyUnitary {
                input,
                output,
                steps,
            } => {
                self.check_step_count(steps.len())?;
                let axes = self.take(*input)?;
                let table_limit = 1 << axes.len();
                for step in steps {
                    // Bound nested storage before cloning any accepted step.
                    if step.controls.len() > axes.len() {
                        return Err(Limit);
                    }
                    match &step.action {
                        CircuitAction::Contract { .. } => return Err(Unsupported),
                        CircuitAction::Monomial {
                            indices,
                            permutation,
                            phases,
                        } if indices.len() > axes.len()
                            || permutation.len() > table_limit
                            || phases.len() > table_limit =>
                        {
                            return Err(Limit);
                        }
                        _ => (),
                    }
                    self.push_step(step.clone(), &axes)?;
                }
                self.owners.insert(*output, axes);
            }
            _ => return Err(Unsupported),
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{ClassicalId, Effect, ScalarPhase, SingleGate, WireId};

    fn closed(operations: Vec<RawOp>, classical_outputs: Vec<ClassicalId>) -> RawProgram {
        RawProgram {
            operations,
            classical_outputs,
            quantum_inputs: vec![],
            classical_inputs: vec![],
            quantum_outputs: vec![],
            declared_effect: Effect::Observe,
        }
    }

    #[test]
    fn signed_controls_and_visible_words_track_original_axis_order() {
        let raw = closed(
            vec![
                RawOp::Init0 {
                    output: TokenId(0),
                    wire: WireId(900),
                },
                RawOp::Init0 {
                    output: TokenId(1),
                    wire: WireId(2),
                },
                RawOp::Join {
                    left: TokenId(1),
                    right: TokenId(0),
                    output: TokenId(2),
                },
                RawOp::ApplyUnitary {
                    input: TokenId(2),
                    output: TokenId(3),
                    steps: vec![CircuitStep {
                        controls: vec![BitControl {
                            index: 1,
                            when_one: false,
                        }],
                        action: CircuitAction::Monomial {
                            indices: vec![0],
                            permutation: vec![1, 0],
                            phases: vec![0, 0],
                        },
                    }],
                },
                RawOp::Split {
                    input: TokenId(3),
                    left: TokenId(4),
                    right: TokenId(5),
                    left_bits: 1,
                },
                RawOp::MeasureZ {
                    input: TokenId(5),
                    output: ClassicalId(0),
                },
                RawOp::MeasureZ {
                    input: TokenId(4),
                    output: ClassicalId(1),
                },
            ],
            vec![ClassicalId(1), ClassicalId(0)],
        );
        assert_eq!(
            raw_terminal_zeros(&raw).unwrap(),
            BTreeSet::from([vec![false, false], vec![false, true], vec![true, true]])
        );
    }

    #[test]
    fn zero_width_targets_keep_scalar_phase_in_both_coherent_arms() {
        let raw = closed(
            vec![
                RawOp::Init0 {
                    output: TokenId(0),
                    wire: WireId(1),
                },
                RawOp::Gate {
                    gate: SingleGate::H,
                    input: TokenId(0),
                    output: TokenId(1),
                },
                RawOp::PackUnit { output: TokenId(2) },
                RawOp::QuantumIf {
                    control: TokenId(1),
                    target: TokenId(2),
                    control_out: TokenId(3),
                    target_out: TokenId(4),
                    zero_ops: vec![UnitaryStep::ScalarPhase(ScalarPhase::EighthTurn)],
                    one_ops: vec![
                        UnitaryStep::ScalarPhase(ScalarPhase::EighthTurn),
                        UnitaryStep::ScalarPhase(ScalarPhase::MinusOne),
                    ],
                },
                RawOp::UnpackUnit { input: TokenId(4) },
                RawOp::Gate {
                    gate: SingleGate::H,
                    input: TokenId(3),
                    output: TokenId(5),
                },
                RawOp::MeasureZ {
                    input: TokenId(5),
                    output: ClassicalId(0),
                },
            ],
            vec![ClassicalId(0)],
        );
        assert_eq!(
            raw_terminal_zeros(&raw).unwrap(),
            BTreeSet::from([vec![false]])
        );
    }
}
