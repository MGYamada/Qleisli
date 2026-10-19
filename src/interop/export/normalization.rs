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
use crate::interop::profile::{Gate, GateOp, TerminalCircuit};
use crate::interop::{InteropError, InteropErrorKind, MAX_GATES, MAX_QUBITS};
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

    /// Final target-word pass, after every original push has obeyed the gate
    /// limit. Pure Raw boundaries may separate a word; allocation/observation
    /// boundaries may not. The accepted source and Raw subject are unchanged.
    pub(super) fn terminal(
        &mut self,
        circuit: &mut TerminalCircuit,
        barriers: &[bool; MAX_GATES + 1],
    ) -> Result<(), InteropError> {
        if circuit.gates.len() > MAX_GATES || circuit.qubits > MAX_QUBITS {
            return Err(InteropError::limit(
                "terminal normalization input exceeds target limits",
            ));
        }
        // Account for the full scan and bounded replacement-position storage
        // before inspecting/copying. This uses the same export-wide counter as
        // retained function windows, not another exact-work allowance.
        self.work
            .charge(circuit.gates.len() + 1)
            .map_err(|_| InteropError::limit("terminal local normalization work exhausted"))?;
        if circuit.gates.iter().any(|op| {
            op.wires.len() != op.gate.arity()
                || op.wires.iter().any(|&axis| axis >= circuit.qubits)
                || op
                    .wires
                    .iter()
                    .enumerate()
                    .any(|(index, axis)| op.wires[..index].contains(axis))
        }) {
            return Err(InteropError::new(
                InteropErrorKind::InvalidIr,
                "terminal gate word operand binding mismatch",
            ));
        }
        let mut replacements = Vec::new();
        let mut index = 0;
        while index + 2 < circuit.gates.len() {
            let possible = if barriers[index + 1] || barriers[index + 2] {
                None
            } else {
                terminal_candidate(&circuit.gates[index..index + 3])?
            };
            if let Some((window, replacement)) = possible {
                self.check(&window, &replacement)?;
                replacements.push(index);
                index += 3;
            } else {
                index += 1;
            }
        }
        // Complete every equation check before changing the output word. A
        // failure retains the original target gates and produces no artifact.
        if replacements.is_empty() {
            return Ok(());
        }
        let mut positions = replacements.into_iter().peekable();
        let mut original = std::mem::take(&mut circuit.gates).into_iter().enumerate();
        while let Some((index, mut op)) = original.next() {
            if positions.peek() == Some(&index) {
                positions.next();
                // The matched actual word has the same one physical operand.
                // Its checked replacement is the existing exact X definition.
                op.gate = Gate::X;
                original.next();
                original.next();
            }
            circuit.gates.push(op);
        }
        Ok(())
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

// Read exact semantics from the actual emitted GateOps, including their own
// operand mappings. No source name, caller label, endpoint type or assumed
// producer equation supplies the original checked word.
fn terminal_candidate(
    word: &[GateOp],
) -> Result<Option<(VecDeque<CircuitStep>, CircuitStep)>, InteropError> {
    if word.len() != 3
        || word[0].gate != Gate::H
        || word[1].gate != Gate::Z
        || word[2].gate != Gate::H
        || word[0].wires.len() != 1
        || word[0].wires != word[1].wires
        || word[0].wires != word[2].wires
    {
        return Ok(None);
    }
    let mapped = |op: &GateOp| -> Result<CircuitStep, InteropError> {
        let mut step = op.gate.step();
        let axis = |index: usize| {
            op.wires.get(index).copied().ok_or_else(|| {
                InteropError::new(
                    InteropErrorKind::InvalidIr,
                    "terminal gate word operand binding mismatch",
                )
            })
        };
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
            _ => {
                return Err(InteropError::new(
                    InteropErrorKind::InvalidIr,
                    "terminal gate word has no exact finite action",
                ));
            }
        }
        Ok(step)
    };
    let window = word
        .iter()
        .map(mapped)
        .collect::<Result<VecDeque<_>, _>>()?;
    let proposed = mapped(&GateOp {
        gate: Gate::X,
        wires: word[0].wires.clone(),
    })?;
    if candidate(&window).as_ref() != Some(&proposed) {
        return Ok(None);
    }
    Ok(Some((window, proposed)))
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

    fn terminal_word(word: &[(Gate, &[usize])], width: usize) -> TerminalCircuit {
        TerminalCircuit {
            qubits: width,
            gates: word
                .iter()
                .map(|(gate, wires)| GateOp {
                    gate: *gate,
                    wires: wires.to_vec(),
                })
                .collect(),
            measurements: vec![],
        }
    }

    fn gate_snapshot(circuit: &TerminalCircuit) -> Vec<(Gate, Vec<usize>)> {
        circuit
            .gates
            .iter()
            .map(|op| (op.gate, op.wires.clone()))
            .collect()
    }

    #[test]
    fn final_target_windows_retain_axes_order_and_nonpure_barriers() {
        for middle in [Gate::S, Gate::Sdg, Gate::T, Gate::Tdg, Gate::X] {
            let mut circuit = terminal_word(&[(Gate::H, &[1]), (middle, &[1]), (Gate::H, &[1])], 2);
            let before = gate_snapshot(&circuit);
            let mut state = State::default();
            state
                .terminal(&mut circuit, &[false; MAX_GATES + 1])
                .unwrap();
            assert_eq!(gate_snapshot(&circuit), before, "other exact phase/action");
            assert!(state.equations.is_empty());
        }
        for word in [
            vec![
                (Gate::H, &[0][..]),
                (Gate::Z, &[1][..]),
                (Gate::H, &[0][..]),
            ],
            vec![
                (Gate::H, &[0][..]),
                (Gate::Z, &[0][..]),
                (Gate::T, &[1][..]),
                (Gate::H, &[0][..]),
            ],
            vec![
                (Gate::H, &[0][..]),
                (Gate::Cz, &[1, 0][..]),
                (Gate::H, &[0][..]),
            ],
        ] {
            let mut circuit = terminal_word(&word, 2);
            let before = gate_snapshot(&circuit);
            let mut state = State::default();
            state
                .terminal(&mut circuit, &[false; MAX_GATES + 1])
                .unwrap();
            assert_eq!(
                gate_snapshot(&circuit),
                before,
                "no commuting/control/axis fallback"
            );
            assert!(state.equations.is_empty());
        }
        for position in [1, 2] {
            let mut circuit =
                terminal_word(&[(Gate::H, &[0]), (Gate::Z, &[0]), (Gate::H, &[0])], 1);
            let before = gate_snapshot(&circuit);
            let mut barriers = [false; MAX_GATES + 1];
            barriers[position] = true;
            let mut state = State::default();
            state.terminal(&mut circuit, &barriers).unwrap();
            assert_eq!(
                gate_snapshot(&circuit),
                before,
                "allocation/observation boundary"
            );
            assert!(state.equations.is_empty());
        }
    }

    #[test]
    fn final_target_equation_failure_retains_the_original_gates() {
        let mut circuit = terminal_word(&[(Gate::H, &[1]), (Gate::Z, &[1]), (Gate::H, &[1])], 2);
        let before = gate_snapshot(&circuit);
        let mut state = State {
            work: Budget::new(0),
            ..State::default()
        };
        assert_eq!(
            state
                .terminal(&mut circuit, &[false; MAX_GATES + 1])
                .unwrap_err()
                .kind,
            InteropErrorKind::Limit
        );
        assert_eq!(gate_snapshot(&circuit), before);
        state.work = Budget::new(DEFAULT_EXACT_WORK);
        assert_eq!(
            state
                .terminal(&mut circuit, &[false; MAX_GATES + 1])
                .unwrap_err()
                .kind,
            InteropErrorKind::InvalidIr
        );
        assert_eq!(gate_snapshot(&circuit), before);
        assert!(state.equations.is_empty());
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn final_target_native_equations_share_full_receipts_and_preserve_all_columns() {
        let kernel = Kernel::selected(crate::edition::Edition::E2026).unwrap();
        let accepted = kernel.accept_raw(unary(3, vec![])).unwrap();
        let original = accepted.raw().clone();
        let mut state = State::for_program(&accepted);
        // Retained controlled windows and final unary windows share precisely
        // the same seven full-body profiles, never an eighth cache allowance.
        for count in 1..=2 {
            for polarity in 0..1usize << count {
                let controls = (0..count)
                    .map(|index| BitControl {
                        index,
                        when_one: polarity & (1 << index) != 0,
                    })
                    .collect();
                let window: VecDeque<_> = hzh(controls, 2).into();
                let replacement = candidate(&window).unwrap();
                state.check(&window, &replacement).unwrap();
            }
        }
        assert_eq!(state.equations.len(), 6);
        for target in 0..3 {
            let mut circuit = terminal_word(
                &[
                    (Gate::H, &[target]),
                    (Gate::Z, &[target]),
                    (Gate::H, &[target]),
                ],
                3,
            );
            let before_work = state.work.remaining();
            state
                .terminal(&mut circuit, &[false; MAX_GATES + 1])
                .unwrap();
            assert_eq!(gate_snapshot(&circuit), vec![(Gate::X, vec![target])]);
            assert_eq!(state.equations.len(), 7, "only complete compact body reuse");
            assert!(
                state.work.remaining() < before_work,
                "one shared export allowance"
            );
            check_emitted(&circuit, expected_x(3, &[], target));
        }
        assert_eq!(
            accepted.raw(),
            &original,
            "original source/dependencies untouched"
        );
        let mut multiple = terminal_word(
            &[
                (Gate::H, &[2]),
                (Gate::Z, &[2]),
                (Gate::H, &[2]),
                (Gate::H, &[0]),
                (Gate::Z, &[0]),
                (Gate::H, &[0]),
            ],
            3,
        );
        state
            .terminal(&mut multiple, &[false; MAX_GATES + 1])
            .unwrap();
        assert_eq!(
            gate_snapshot(&multiple),
            vec![(Gate::X, vec![2]), (Gate::X, vec![0])]
        );
        assert_eq!(state.equations.len(), 7);
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
        CheckedContract::check(
            crate::edition::Edition::E2026,
            Circuit::new(basis, steps).unwrap(),
            contract,
            &mut budget,
        )
        .unwrap();
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
        let kernel = Kernel::selected(crate::edition::Edition::E2026).unwrap();
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
        let kernel = Kernel::selected(crate::edition::Edition::E2026).unwrap();
        let original = unary(1, hzh(vec![], 0));
        let evidence = FunctionEvidence::check(
            crate::edition::Edition::E2026,
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
