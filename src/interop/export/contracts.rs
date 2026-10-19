//! Borrowed expansion of actual checked function circuits for terminal export.
//! This consumes retained implementations; it creates no acceptance evidence.

use super::super::{InteropError, InteropErrorKind, MAX_QUBITS};
use crate::contract::function::{MAX_FUNCTION_DEPTH, MAX_FUNCTION_EXPANDED_STEPS};
use crate::ir::{BitControl, CircuitAction, CircuitStep};

/// One counter for the entire exported program. Flat steps retain their existing
/// gate/Raw limits; nested bodies reserve their checked transitive work up front.
#[derive(Default)]
pub(in crate::interop) struct ExpansionBudget {
    used: usize,
    pub(super) normalizations: super::normalization::State,
}

impl ExpansionBudget {
    pub(in crate::interop) fn for_program(program: &crate::AcceptedProgram) -> Self {
        Self {
            used: 0,
            normalizations: super::normalization::State::for_program(program),
        }
    }

    fn reserve(&mut self, steps: &[CircuitStep]) -> Result<(), InteropError> {
        for step in steps {
            if let CircuitAction::Contract { evidence, .. } = &step.action {
                self.used = self
                    .used
                    .checked_add(evidence.expanded_steps())
                    .ok_or_else(|| {
                        InteropError::limit("function export expansion size overflow")
                    })?;
                if self.used > MAX_FUNCTION_EXPANDED_STEPS {
                    return Err(InteropError::limit(
                        "function export expansion exceeds 1000000 steps",
                    ));
                }
            }
        }
        Ok(())
    }
}

struct Frame<'a> {
    body: &'a [CircuitStep],
    consumed: usize,
    inverse: bool,
    axes: Vec<usize>,
    controls: Vec<BitControl>,
}

pub(super) struct Cursor<'a> {
    frames: Vec<Frame<'a>>,
}

fn invalid(message: &'static str) -> InteropError {
    InteropError::new(InteropErrorKind::InvalidIr, message)
}

fn mapped_axes(indices: &[usize], axes: &[usize]) -> Result<Vec<usize>, InteropError> {
    if indices.len() > MAX_QUBITS {
        return Err(InteropError::limit(
            "function export interface exceeds 12 axes",
        ));
    }
    let mut result = Vec::with_capacity(indices.len());
    for &index in indices {
        let mapped = *axes
            .get(index)
            .ok_or_else(|| invalid("function export axis is out of range"))?;
        if result.contains(&mapped) {
            return Err(invalid("function export axes are not distinct"));
        }
        result.push(mapped);
    }
    Ok(result)
}

fn mapped_controls(step: &CircuitStep, frame: &Frame<'_>) -> Result<Vec<BitControl>, InteropError> {
    let len = step
        .controls
        .len()
        .checked_add(frame.controls.len())
        .filter(|&len| len <= MAX_QUBITS)
        .ok_or_else(|| InteropError::limit("function export controls exceed 12 axes"))?;
    let mut controls = Vec::with_capacity(len);
    for control in &step.controls {
        let index = *frame
            .axes
            .get(control.index)
            .ok_or_else(|| invalid("function export control is out of range"))?;
        controls.push(BitControl {
            index,
            when_one: control.when_one,
        });
    }
    controls.extend_from_slice(&frame.controls);
    for (i, control) in controls.iter().enumerate() {
        if controls[..i]
            .iter()
            .any(|other| other.index == control.index)
        {
            return Err(invalid("function export controls are not distinct"));
        }
    }
    Ok(controls)
}

impl<'a> Cursor<'a> {
    pub(super) fn new(
        steps: &'a [CircuitStep],
        width: usize,
        budget: &mut ExpansionBudget,
    ) -> Result<Self, InteropError> {
        if width > MAX_QUBITS {
            return Err(InteropError::limit(
                "function export interface exceeds 12 axes",
            ));
        }
        // Reject excessive transitive work before copying even the root frame.
        budget.reserve(steps)?;
        Ok(Self {
            frames: vec![Frame {
                body: steps,
                consumed: 0,
                inverse: false,
                axes: (0..width).collect(),
                controls: vec![],
            }],
        })
    }

    pub(super) fn next(&mut self) -> Result<Option<CircuitStep>, InteropError> {
        loop {
            let depth = self.frames.len();
            let Some(frame) = self.frames.last_mut() else {
                return Ok(None);
            };
            if frame.consumed == frame.body.len() {
                self.frames.pop();
                continue;
            }
            let index = if frame.inverse {
                frame.body.len() - frame.consumed - 1
            } else {
                frame.consumed
            };
            let step = &frame.body[index];
            frame.consumed += 1;
            let controls = mapped_controls(step, frame)?;
            if let CircuitAction::Contract {
                indices,
                evidence,
                adjoint,
            } = &step.action
            {
                if depth > MAX_FUNCTION_DEPTH {
                    return Err(InteropError::limit("function export nesting exceeds 32"));
                }
                if indices.len()
                    != evidence
                        .circuit()
                        .basis()
                        .bits()
                        .map_err(|_| invalid("invalid function export interface"))?
                {
                    return Err(invalid("function export interface has the wrong width"));
                }
                let axes = mapped_axes(indices, &frame.axes)?;
                if controls.iter().any(|control| axes.contains(&control.index)) {
                    return Err(invalid("function export control overlaps its interface"));
                }
                let child = Frame {
                    body: evidence.circuit().steps(),
                    consumed: 0,
                    inverse: frame.inverse ^ *adjoint,
                    axes,
                    controls,
                };
                // Each frame owns at most 12 axes and 12 controls. This bound is
                // checked before growing the stack; bodies themselves stay borrowed.
                self.frames.push(child);
                continue;
            }
            let action = match &step.action {
                CircuitAction::Hadamard { target } => CircuitAction::Hadamard {
                    target: *frame
                        .axes
                        .get(*target)
                        .ok_or_else(|| invalid("function export target is out of range"))?,
                },
                CircuitAction::Monomial {
                    indices,
                    permutation,
                    phases,
                } => {
                    // The terminal vocabulary has only zero-, one-, or two-axis
                    // leaves. Refuse larger tables while borrowed, before cloning.
                    if indices.len() > 2 {
                        return Err(InteropError::unsupported(
                            "monomial table outside the terminal gate vocabulary",
                        ));
                    }
                    let dim = 1usize << indices.len();
                    if permutation.len() != dim
                        || phases.len() != dim
                        || phases.iter().any(|&phase| phase >= 8)
                        || permutation.iter().enumerate().any(|(i, &value)| {
                            usize::from(value) >= dim || permutation[..i].contains(&value)
                        })
                    {
                        return Err(invalid("invalid function export monomial table"));
                    }
                    CircuitAction::Monomial {
                        indices: mapped_axes(indices, &frame.axes)?,
                        permutation: permutation.clone(),
                        phases: phases.clone(),
                    }
                }
                CircuitAction::Contract { .. } => unreachable!("handled above"),
            };
            let targets: &[usize] = match &action {
                CircuitAction::Hadamard { target } => std::slice::from_ref(target),
                CircuitAction::Monomial { indices, .. } => indices,
                CircuitAction::Contract { .. } => unreachable!("leaf action"),
            };
            if controls
                .iter()
                .any(|control| targets.contains(&control.index))
            {
                return Err(invalid("function export control overlaps a target"));
            }
            let mut leaf = CircuitStep { controls, action };
            if frame.inverse {
                crate::contract::invert_steps(std::slice::from_mut(&mut leaf));
            }
            return Ok(Some(leaf));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::contract::exact::Budget;
    use crate::contract::{BasisType, DEFAULT_EXACT_WORK, FunctionEvidence, FunctionIdentity};
    use crate::ir::*;

    fn scalar() -> FunctionEvidence {
        let raw = RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: TokenId(0),
                wires: vec![],
                shape: BasisShape { bits: 0 },
            }],
            classical_inputs: vec![],
            operations: vec![RawOp::ApplyUnitary {
                input: TokenId(0),
                output: TokenId(1),
                steps: vec![CircuitStep {
                    controls: vec![],
                    action: CircuitAction::Monomial {
                        indices: vec![],
                        permutation: vec![0],
                        phases: vec![1],
                    },
                }],
            }],
            quantum_outputs: vec![TokenId(1)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        FunctionEvidence::check(
            crate::edition::Edition::E2026,
            BasisType::Unit,
            raw.clone(),
            raw,
            FunctionIdentity {
                implementation: "scalar".into(),
                specification: "scalar".into(),
                sources: vec![],
            },
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .unwrap()
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn expansion_reservation_is_shared_across_raw_operations() {
        let steps = [CircuitStep {
            controls: vec![],
            action: CircuitAction::Contract {
                indices: vec![],
                evidence: scalar().into(),
                adjoint: false,
            },
        }];
        let mut budget = ExpansionBudget {
            used: MAX_FUNCTION_EXPANDED_STEPS - 1,
            ..Default::default()
        };
        let mut cursor = Cursor::new(&steps, 0, &mut budget).unwrap();
        assert!(cursor.next().unwrap().is_some());
        assert!(cursor.next().unwrap().is_none());
        assert!(matches!(
            Cursor::new(&steps, 0, &mut budget),
            Err(InteropError {
                kind: InteropErrorKind::Limit,
                ..
            })
        ));
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn malformed_mapping_of_checked_dependency_returns_an_error() {
        // This is an untrusted step around a real checked dependency, never a
        // forged AcceptedProgram or a replacement for native validity checking.
        let steps = [CircuitStep {
            controls: vec![],
            action: CircuitAction::Contract {
                indices: vec![1],
                evidence: scalar().into(),
                adjoint: false,
            },
        }];
        let mut cursor = Cursor::new(&steps, 0, &mut ExpansionBudget::default()).unwrap();
        assert!(matches!(
            cursor.next(),
            Err(InteropError {
                kind: InteropErrorKind::InvalidIr,
                ..
            })
        ));
    }
}
