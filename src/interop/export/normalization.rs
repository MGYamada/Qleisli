//! Bounded proposals over actual expanded leaves. Rust recognizes a candidate;
//! the existing native function-equation check alone authorizes its replacement.
//! Original accepted source/Raw graphs and their obligations remain untouched.

use std::collections::VecDeque;

use super::contracts::Cursor;
use crate::AcceptedProgram;
use crate::contract::exact::Budget;
use crate::contract::function::RetainedIdentity;
use crate::contract::{BasisType, DEFAULT_EXACT_WORK, FunctionEvidence, FunctionIdentity};
use crate::interchange::native::Kernel;
use crate::interop::{InteropError, InteropErrorKind};
use crate::ir::*;

// Zero, one, or two controls have exactly 1 + 2 + 4 polarity profiles.
const MAX_LOCAL_EQUATIONS: usize = 7;

pub(super) struct State {
    kernel: Option<Kernel>,
    work: Budget,
    equations: Vec<FunctionEvidence>,
}

impl Default for State {
    fn default() -> Self {
        Self {
            kernel: None,
            work: Budget::new(DEFAULT_EXACT_WORK),
            equations: vec![],
        }
    }
}

impl State {
    pub(super) fn for_program(program: &AcceptedProgram) -> Self {
        Self {
            // Bind every new equation to the original accepted subject's own
            // checker/log. Never select an environment-dependent alternative.
            kernel: Some(program.kernel()),
            ..Self::default()
        }
    }

    pub(super) fn next(
        &mut self,
        cursor: &mut Cursor<'_>,
        window: &mut VecDeque<CircuitStep>,
    ) -> Result<Option<CircuitStep>, InteropError> {
        if window.len() > 3 {
            return Err(InteropError::limit(
                "terminal normalization window exceeds three leaves",
            ));
        }
        while window.len() < 3 {
            let Some(step) = cursor.next()? else { break };
            window.push_back(step);
        }
        let Some(replacement) = candidate(window) else {
            return Ok(window.pop_front());
        };
        self.check(window, &replacement)?;
        // No commuting or cross-Raw-operation lookahead. Only these three
        // actual adjacent leaves are consumed; all other steps retain order.
        drop(window.drain(..3));
        Ok(Some(replacement))
    }

    fn check(
        &mut self,
        window: &VecDeque<CircuitStep>,
        replacement: &CircuitStep,
    ) -> Result<(), InteropError> {
        // Charge the complete bounded construction/comparison before copying.
        // This counter is shared across all Raw operations of this export.
        self.work
            .charge(1024)
            .map_err(|_| InteropError::limit("terminal local normalization work exhausted"))?;
        let (signature, original, proposed) = compact(window, replacement)?;
        // These receipt bodies are flat, at most three bits/steps, and contain
        // no nested receipt identities. Compare full structures, never hashes
        // or source names. Reuse is local to this original accepted subject.
        if self.equations.iter().any(|equation| {
            equation.signature() == &signature
                && equation.implementation() == &original
                && equation.specification() == &proposed
        }) {
            return Ok(());
        }
        if self.equations.len() >= MAX_LOCAL_EQUATIONS {
            return Err(InteropError::limit(
                "at most seven terminal local equations",
            ));
        }
        let kernel = self.kernel.as_ref().ok_or_else(|| {
            InteropError::new(
                InteropErrorKind::InvalidIr,
                "terminal normalization has no bound native checker",
            )
        })?;
        let equation = FunctionEvidence::check_retained_with_kernel(
            kernel,
            signature,
            original,
            proposed,
            RetainedIdentity::Owned(FunctionIdentity {
                implementation: "interop::expanded_hzh_window".into(),
                specification: "interop::existing_x_word".into(),
                // These are exact IR-local operands, not fabricated source
                // provenance or a general source/export preservation theorem.
                sources: vec![],
            }),
            &mut self.work,
        )
        .map_err(|failure| {
            if failure.error.is_capacity() {
                InteropError::limit("native terminal local equation exceeds exact work limits")
            } else {
                InteropError::new(
                    InteropErrorKind::InvalidIr,
                    "native terminal local equation was not established",
                )
            }
        })?;
        self.equations.push(equation);
        Ok(())
    }
}

fn candidate(window: &VecDeque<CircuitStep>) -> Option<CircuitStep> {
    let first = window.front()?;
    let middle = window.get(1)?;
    let last = window.get(2)?;
    let CircuitAction::Hadamard { target } = first.action else {
        return None;
    };
    if first.controls.len() > 2
        || first.controls != middle.controls
        || first.controls != last.controls
        || !matches!(last.action, CircuitAction::Hadamard { target: other } if target == other)
    {
        return None;
    }
    let CircuitAction::Monomial {
        indices,
        permutation,
        phases,
    } = &middle.action
    else {
        return None;
    };
    if indices != &[target] || permutation != &[0, 1] || phases != &[0, 4] {
        return None;
    }
    Some(CircuitStep {
        controls: first.controls.clone(),
        action: CircuitAction::Monomial {
            indices: vec![target],
            permutation: vec![1, 0],
            phases: vec![0, 0],
        },
    })
}

// Compaction is a physical coordinate relabeling only. Keep original ordered
// control polarities, use the target as the final local axis, and check every
// exact action coefficient. Source type trees and owner mappings are unchanged.
fn compact(
    window: &VecDeque<CircuitStep>,
    replacement: &CircuitStep,
) -> Result<(BasisType, RawProgram, RawProgram), InteropError> {
    let invalid = || {
        InteropError::new(
            InteropErrorKind::InvalidIr,
            "terminal local equation axis binding mismatch",
        )
    };
    if window.len() != 3 {
        return Err(invalid());
    }
    let CircuitAction::Monomial { indices, .. } = &replacement.action else {
        return Err(invalid());
    };
    if indices.len() != 1 || replacement.controls.len() > 2 {
        return Err(invalid());
    }
    let ordered_axes: Vec<_> = replacement
        .controls
        .iter()
        .map(|control| control.index)
        .chain(indices.iter().copied())
        .collect();
    if ordered_axes
        .iter()
        .enumerate()
        .any(|(index, axis)| ordered_axes[..index].contains(axis))
    {
        return Err(invalid());
    }
    let width = ordered_axes.len();
    let bits = u8::try_from(width).map_err(|_| invalid())?;
    let axis = |original| {
        ordered_axes
            .iter()
            .position(|&physical| physical == original)
            .ok_or_else(invalid)
    };
    let local = |step: &CircuitStep| -> Result<CircuitStep, InteropError> {
        let controls = step
            .controls
            .iter()
            .map(|control| {
                Ok(BitControl {
                    index: axis(control.index)?,
                    when_one: control.when_one,
                })
            })
            .collect::<Result<Vec<_>, InteropError>>()?;
        let action = match &step.action {
            CircuitAction::Hadamard { target } => CircuitAction::Hadamard {
                target: axis(*target)?,
            },
            CircuitAction::Monomial {
                indices,
                permutation,
                phases,
            } => CircuitAction::Monomial {
                indices: indices
                    .iter()
                    .map(|&index| axis(index))
                    .collect::<Result<Vec<_>, _>>()?,
                permutation: permutation.clone(),
                phases: phases.clone(),
            },
            _ => return Err(invalid()),
        };
        Ok(CircuitStep { controls, action })
    };
    let raw = |steps| RawProgram {
        quantum_inputs: vec![QuantumPort {
            token: TokenId(0),
            wires: (0..width).map(|axis| WireId(axis as u32)).collect(),
            shape: BasisShape { bits },
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
    };
    Ok((
        BasisType::Bits(width as u32),
        raw(window
            .iter()
            .take(3)
            .map(local)
            .collect::<Result<Vec<_>, _>>()?),
        raw(vec![local(replacement)?]),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::contract::exact::{Exact, Matrix};
    use crate::contract::{CheckedContract, Circuit, Contract, Encoding};
    use crate::interop::export::ExpansionBudget;
    use crate::interop::profile::{Gate, TerminalCircuit};

    fn hzh(controls: Vec<BitControl>, target: usize) -> Vec<CircuitStep> {
        vec![
            CircuitStep {
                controls: controls.clone(),
                action: CircuitAction::Hadamard { target },
            },
            CircuitStep {
                controls: controls.clone(),
                action: CircuitAction::Monomial {
                    indices: vec![target],
                    permutation: vec![0, 1],
                    phases: vec![0, 4],
                },
            },
            CircuitStep {
                controls,
                action: CircuitAction::Hadamard { target },
            },
        ]
    }

    #[test]
    fn candidate_requires_exact_adjacent_phase_target_and_ordered_controls() {
        let controls = vec![
            BitControl {
                index: 2,
                when_one: false,
            },
            BitControl {
                index: 0,
                when_one: true,
            },
        ];
        let original: VecDeque<_> = hzh(controls, 1).into();
        assert!(candidate(&original).is_some());
        for change in 0..9 {
            let mut changed = original.clone();
            match change {
                0 | 1 => {
                    let CircuitAction::Monomial { phases, .. } = &mut changed[1].action else {
                        unreachable!()
                    };
                    *phases = if change == 0 { vec![4, 0] } else { vec![1, 5] };
                }
                2 => {
                    let CircuitAction::Monomial { permutation, .. } = &mut changed[1].action else {
                        unreachable!()
                    };
                    *permutation = vec![1, 0];
                }
                3 => {
                    let CircuitAction::Monomial { indices, .. } = &mut changed[1].action else {
                        unreachable!()
                    };
                    *indices = vec![3];
                }
                4 => changed[2].action = CircuitAction::Hadamard { target: 3 },
                5 => changed[1].controls.reverse(),
                6 => changed[1].controls[0].when_one = true,
                7 => {
                    let inserted = CircuitStep {
                        controls: changed[0].controls.clone(),
                        action: CircuitAction::Monomial {
                            indices: vec![1],
                            permutation: vec![0, 1],
                            phases: vec![0, 1],
                        },
                    };
                    changed.insert(1, inserted);
                }
                8 => {
                    for step in &mut changed {
                        step.controls.push(BitControl {
                            index: 3,
                            when_one: true,
                        });
                    }
                }
                _ => unreachable!(),
            }
            assert!(candidate(&changed).is_none(), "mutation {change}");
            // A noncandidate stream is returned exactly, without name/type
            // fallback or silently dropping a leaf. Existing emitter policy
            // decides whether that unchanged stream is supported.
            let steps: Vec<_> = changed.into();
            let mut expansion = ExpansionBudget::default();
            let mut cursor = Cursor::new(&steps, 4, &mut expansion).unwrap();
            let mut state = State::default();
            let mut window = VecDeque::with_capacity(3);
            let mut returned = vec![];
            while let Some(step) = state.next(&mut cursor, &mut window).unwrap() {
                returned.push(step);
            }
            assert_eq!(returned, steps);
        }
    }

    #[test]
    fn equation_failure_keeps_the_original_window_and_shared_budget() {
        let steps = hzh(vec![], 0);
        let mut expansion = ExpansionBudget::default();
        let mut cursor = Cursor::new(&steps, 1, &mut expansion).unwrap();
        let mut window = VecDeque::with_capacity(3);
        let mut state = State {
            work: Budget::new(0),
            ..State::default()
        };
        assert_eq!(
            state.next(&mut cursor, &mut window).unwrap_err().kind,
            InteropErrorKind::Limit
        );
        assert_eq!(
            window.iter().collect::<Vec<_>>(),
            steps.iter().collect::<Vec<_>>()
        );
        assert!(state.equations.is_empty());
        state.work = Budget::new(DEFAULT_EXACT_WORK);
        assert_eq!(
            state.next(&mut cursor, &mut window).unwrap_err().kind,
            InteropErrorKind::InvalidIr
        );
        assert!(state.equations.is_empty());
    }

    fn unary(width: usize, steps: Vec<CircuitStep>) -> RawProgram {
        RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: TokenId(0),
                wires: (0..width).map(|i| WireId(i as u32)).collect(),
                shape: BasisShape {
                    bits: u8::try_from(width).unwrap(),
                },
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

    fn expected_x(width: usize, controls: &[BitControl], target: usize) -> Matrix {
        let dimension = 1usize << width;
        Matrix::new(
            dimension,
            dimension,
            (0..dimension * dimension)
                .map(|entry| {
                    let row = entry / dimension;
                    let column = entry % dimension;
                    let active = controls
                        .iter()
                        .all(|c| ((column >> c.index) & 1 != 0) == c.when_one);
                    let image = if active {
                        column ^ (1 << target)
                    } else {
                        column
                    };
                    if row == image {
                        Exact::one()
                    } else {
                        Exact::zero()
                    }
                })
                .collect(),
        )
        .unwrap()
    }

    fn check_emitted(circuit: &TerminalCircuit, meaning: Matrix) {
        let basis = BasisType::Bits(circuit.qubits as u32);
        let mut steps = vec![];
        for op in &circuit.gates {
            let mut step = op.gate.step();
            for c in &mut step.controls {
                c.index = op.wires[c.index];
            }
            match &mut step.action {
                CircuitAction::Hadamard { target } => *target = op.wires[*target],
                CircuitAction::Monomial { indices, .. } => {
                    for axis in indices {
                        *axis = op.wires[*axis];
                    }
                }
                _ => unreachable!(),
            }
            steps.push(step);
        }
        let mut budget = Budget::new(DEFAULT_EXACT_WORK);
        let encoding = Encoding::identity(basis.clone()).unwrap();
        let contract = Contract::new(encoding.clone(), encoding, meaning, &mut budget).unwrap();
        CheckedContract::check(Circuit::new(basis, steps).unwrap(), contract, &mut budget).unwrap();
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn existing_native_equation_refuses_wrong_phase_or_control_subjects() {
        let controls = vec![BitControl {
            index: 0,
            when_one: false,
        }];
        let original: VecDeque<_> = hzh(controls, 1).into();
        let replacement = candidate(&original).unwrap();
        let kernel = Kernel::selected().unwrap();
        for mutation in 0..3 {
            let mut changed = original.clone();
            match mutation {
                0 => {
                    let CircuitAction::Monomial { phases, .. } = &mut changed[1].action else {
                        unreachable!()
                    };
                    *phases = vec![1, 5]; // Conditional scalar phase, not X.
                }
                1 => changed[1].controls[0].when_one = true,
                2 => changed[2].action = CircuitAction::Hadamard { target: 0 },
                _ => unreachable!(),
            }
            assert!(candidate(&changed).is_none());
            let mut state = State {
                kernel: Some(kernel.clone()),
                ..State::default()
            };
            // Exercise the existing native gate on the exact untrusted subject
            // even though the production matcher correctly declines it first.
            assert_eq!(
                state.check(&changed, &replacement).unwrap_err().kind,
                InteropErrorKind::InvalidIr
            );
            assert!(state.equations.is_empty());
        }
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn actual_retained_hzh_and_adjoint_preserve_all_columns_controls_and_reference() {
        let kernel = Kernel::selected().unwrap();
        let original = unary(1, hzh(vec![], 0));
        let evidence = FunctionEvidence::check(
            BasisType::Bits(1),
            original.clone(),
            original,
            FunctionIdentity {
                implementation: "arbitrary_implementation_label".into(),
                specification: "arbitrary_reference_label".into(),
                sources: vec![],
            },
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .unwrap();
        for count in 0..=2 {
            for polarity in 0..1usize << count {
                for adjoint in [false, true] {
                    let controls: Vec<_> = [2, 0][..count]
                        .iter()
                        .enumerate()
                        .map(|(position, &index)| BitControl {
                            index,
                            when_one: polarity & (1 << position) != 0,
                        })
                        .collect();
                    let steps = vec![CircuitStep {
                        controls: controls.clone(),
                        action: CircuitAction::Contract {
                            indices: vec![1],
                            evidence: evidence.clone().into(),
                            adjoint,
                        },
                    }];
                    let accepted = kernel.accept_raw(unary(3, steps.clone())).unwrap();
                    let retained_before = accepted.raw().clone();
                    let mut expansion = ExpansionBudget::for_program(&accepted);
                    let mut circuit = TerminalCircuit {
                        qubits: 3,
                        gates: vec![],
                        measurements: vec![],
                    };
                    crate::interop::export::steps(
                        &mut circuit,
                        &mut vec![],
                        &steps,
                        &[0, 1, 2],
                        &mut expansion,
                    )
                    .unwrap();
                    assert_eq!(
                        accepted.raw(),
                        &retained_before,
                        "original obligations retained"
                    );
                    let main = &circuit.gates[controls.iter().filter(|c| !c.when_one).count()];
                    assert_eq!(main.gate, [Gate::X, Gate::Cx, Gate::Ccx][count]);
                    assert_eq!(
                        main.wires,
                        controls
                            .iter()
                            .map(|c| c.index)
                            .chain([1])
                            .collect::<Vec<_>>()
                    );
                    assert_eq!(circuit.qubits, 3, "no new workspace");
                    check_emitted(&circuit, expected_x(3, &controls, 1));
                    assert_eq!(expansion.normalizations.equations.len(), 1);
                    // Reuse only the same complete bounded equation; charge
                    // again under the shared export budget.
                    let remaining = expansion.normalizations.work.remaining();
                    crate::interop::export::steps(
                        &mut circuit,
                        &mut vec![],
                        &steps,
                        &[0, 1, 2],
                        &mut expansion,
                    )
                    .unwrap();
                    assert_eq!(expansion.normalizations.equations.len(), 1);
                    assert!(expansion.normalizations.work.remaining() < remaining);
                }
            }
        }
    }
}
