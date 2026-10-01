//! Exact terminal-target rewrites after verification. These are untrusted
//! adapters, not kernel rules or resource certificates. Conjunction workspace
//! starts in zero, is explicitly uncomputed, and counts toward the target cap.

use super::profile::{self, Gate, GateOp, TerminalCircuit};
use super::{InteropError, MAX_QUBITS};
use crate::ir::{CircuitAction, CircuitStep};

fn phase_word(k: u8) -> &'static [Gate] {
    match k % 8 {
        0 => &[],
        1 => &[Gate::T],
        2 => &[Gate::S],
        3 => &[Gate::S, Gate::T],
        4 => &[Gate::Z],
        5 => &[Gate::Sdg, Gate::Tdg],
        6 => &[Gate::Sdg],
        7 => &[Gate::Tdg],
        _ => unreachable!(),
    }
}

fn phase(circuit: &mut TerminalCircuit, target: usize, k: u8) -> Result<(), InteropError> {
    for &gate in phase_word(k) {
        circuit.push(gate, vec![target])?;
    }
    Ok(())
}

fn workspace(
    circuit: &mut TerminalCircuit,
    scratch: &mut Vec<usize>,
    count: usize,
) -> Result<(), InteropError> {
    while scratch.len() < count {
        if circuit.qubits >= MAX_QUBITS {
            return Err(InteropError::limit(
                "synthesis workspace exceeds the 12-qubit target limit",
            ));
        }
        scratch.push(circuit.qubits);
        circuit.qubits += 1;
    }
    Ok(())
}

/// Multiply the state by omega^k only when all operands are one. For two
/// operands and even k, k*a*b = (k/2)*(a+b-(a xor b)) modulo eight.
/// Otherwise compute their conjunction, phase it, then undo the entire chain.
fn conditional_phase(
    circuit: &mut TerminalCircuit,
    scratch: &mut Vec<usize>,
    operands: &[usize],
    k: u8,
) -> Result<(), InteropError> {
    let k = k % 8;
    if k == 0 {
        return Ok(());
    }
    match operands {
        [] => {
            return Err(InteropError::unsupported(
                "uncontrolled scalar phase is outside the terminal gate vocabulary",
            ));
        }
        &[target] => return phase(circuit, target, k),
        &[a, b] if k % 2 == 0 => {
            if k == 4 {
                return circuit.push(Gate::Cz, vec![a, b]);
            }
            phase(circuit, a, k / 2)?;
            phase(circuit, b, k / 2)?;
            circuit.push(Gate::Cx, vec![a, b])?;
            phase(circuit, b, (8 - k / 2) % 8)?;
            return circuit.push(Gate::Cx, vec![a, b]);
        }
        _ => {}
    }
    workspace(circuit, scratch, operands.len() - 1)?;
    let mut chain = vec![vec![operands[0], operands[1], scratch[0]]];
    for i in 2..operands.len() {
        chain.push(vec![scratch[i - 2], operands[i], scratch[i - 1]]);
    }
    for args in &chain {
        circuit.push(Gate::Ccx, args.clone())?;
    }
    phase(circuit, scratch[operands.len() - 2], k)?;
    for args in chain.into_iter().rev() {
        circuit.push(Gate::Ccx, args)?;
    }
    Ok(())
}

pub(super) fn step(
    circuit: &mut TerminalCircuit,
    scratch: &mut Vec<usize>,
    step: &CircuitStep,
    wires: &[usize],
) -> Result<(), InteropError> {
    let negative: Vec<_> = step
        .controls
        .iter()
        .filter(|c| !c.when_one)
        .map(|c| wires[c.index])
        .collect();
    for &q in &negative {
        circuit.push(Gate::X, vec![q])?;
    }
    let mut positive = step.clone();
    for control in &mut positive.controls {
        control.when_one = true;
    }
    if let Ok((gate, args)) = profile::recognize(&positive, wires) {
        circuit.push(gate, args)?;
    } else {
        let controls: Vec<_> = step.controls.iter().map(|c| wires[c.index]).collect();
        match &step.action {
            CircuitAction::Hadamard { target } if controls.len() == 1 => {
                let target = wires[*target];
                // A = S H T H S† sends Z to H by conjugation. Execute A†,
                // controlled-Z, A; the two scalar phases cancel exactly.
                for gate in [Gate::Sdg, Gate::H, Gate::Tdg, Gate::H, Gate::S] {
                    circuit.push(gate, vec![target])?;
                }
                circuit.push(Gate::Cz, vec![controls[0], target])?;
                for gate in [Gate::Sdg, Gate::H, Gate::T, Gate::H, Gate::S] {
                    circuit.push(gate, vec![target])?;
                }
            }
            CircuitAction::Monomial {
                indices,
                permutation,
                phases,
            } if indices.is_empty() && permutation == &[0] => {
                conditional_phase(circuit, scratch, &controls, phases[0])?;
            }
            CircuitAction::Monomial {
                indices,
                permutation,
                phases,
            } if indices.len() == 1 && permutation == &[0, 1] => {
                conditional_phase(circuit, scratch, &controls, phases[0])?;
                let mut operands = controls;
                operands.push(wires[indices[0]]);
                conditional_phase(circuit, scratch, &operands, (phases[1] + 8 - phases[0]) % 8)?;
            }
            _ => {
                return Err(InteropError::unsupported(
                    "circuit action or controls outside the terminal gate vocabulary",
                ));
            }
        }
    }
    for q in negative.into_iter().rev() {
        circuit.push(Gate::X, vec![q])?;
    }
    Ok(())
}

/// Recover diagonal words before assigning synthesis workspace. In particular
/// the source alias S lowers to two controlled T steps, whose combined even
/// exponent has an ancilla-free realization. Controls and ordered axes must
/// match exactly; no operation is commuted across another step.
pub(super) fn steps(
    circuit: &mut TerminalCircuit,
    scratch: &mut Vec<usize>,
    steps: &[CircuitStep],
    wires: &[usize],
) -> Result<(), InteropError> {
    let mut index = 0;
    while index < steps.len() {
        let mut merged = steps[index].clone();
        index += 1;
        if let CircuitAction::Monomial {
            indices,
            permutation,
            phases,
        } = &mut merged.action
        {
            if permutation
                .iter()
                .enumerate()
                .all(|(i, &j)| i == usize::from(j))
            {
                while let Some(next) = steps.get(index) {
                    let CircuitAction::Monomial {
                        indices: next_indices,
                        permutation: next_perm,
                        phases: next_phases,
                    } = &next.action
                    else {
                        break;
                    };
                    if next.controls != merged.controls
                        || next_indices != indices
                        || next_perm != permutation
                    {
                        break;
                    }
                    for (a, b) in phases.iter_mut().zip(next_phases) {
                        *a = (*a + *b) % 8;
                    }
                    index += 1;
                }
            }
        }
        step(circuit, scratch, &merged, wires)?;
    }
    Ok(())
}

/// Only structural axis permutations, including identity, are admitted here.
/// Checking every row prevents arbitrary reversible truth tables being
/// mistaken for wiring. General LiftBasis synthesis remains a separate gate.
pub(super) fn axis_permutation(
    table: &[u16],
    input: usize,
    output: usize,
) -> Result<Vec<usize>, InteropError> {
    let unsupported = || {
        InteropError::unsupported(
            "only equal-width axis permutations can export LiftBasis; general table synthesis is unavailable",
        )
    };
    if input != output || table.len() != 1usize << input {
        return Err(unsupported());
    }
    let mut axes = vec![];
    for axis in 0..input {
        let image = usize::from(table[1usize << axis]);
        if !image.is_power_of_two() {
            return Err(unsupported());
        }
        let destination = image.trailing_zeros() as usize;
        if destination >= input || axes.contains(&destination) {
            return Err(unsupported());
        }
        axes.push(destination);
    }
    for (x, &y) in table.iter().enumerate() {
        let expected = axes.iter().enumerate().fold(0, |acc, (source, &dest)| {
            acc | (((x >> source) & 1) << dest)
        });
        if usize::from(y) != expected {
            return Err(unsupported());
        }
    }
    let mut inverse = vec![0; input];
    for (source, &dest) in axes.iter().enumerate() {
        inverse[dest] = source;
    }
    Ok(inverse)
}

/// Fold only adjacent diagonal operations on the same physical operand. Never
/// commute across a gate, change a controlled phase, or quotient global phase.
pub(super) fn fold_phases(circuit: &mut TerminalCircuit) {
    fn exponent(gate: Gate) -> Option<u8> {
        Some(match gate {
            Gate::T => 1,
            Gate::S => 2,
            Gate::Z => 4,
            Gate::Sdg => 6,
            Gate::Tdg => 7,
            _ => return None,
        })
    }
    let gates = std::mem::take(&mut circuit.gates);
    let mut gates = gates.into_iter().peekable();
    while let Some(op) = gates.next() {
        let Some(mut k) = exponent(op.gate) else {
            circuit.gates.push(op);
            continue;
        };
        while let Some(next) = gates
            .peek()
            .filter(|next| next.wires == op.wires && exponent(next.gate).is_some())
        {
            k = (k + exponent(next.gate).expect("diagonal")) % 8;
            gates.next();
        }
        for &gate in phase_word(k) {
            circuit.gates.push(GateOp {
                gate,
                wires: op.wires.clone(),
            });
        }
    }
}
