//! Deterministic numerical gates and expansion of already checked contracts.
//! Observation and ensemble construction belong to the calling interpreter.
use super::{Complex, Component, ExecutionBudget, SimulationError, bit, local_label};
use crate::ir::{
    BitControl, CircuitAction, CircuitStep, Control, ProtectedBit, ProtectedRegion, ProtectedUse,
    ScalarPhase, SingleGate, UnitaryStep, WireId,
};

pub(super) fn apply_gate(
    amplitudes: &mut [Complex],
    axis: usize,
    gate: SingleGate,
    enabled: impl Fn(usize) -> bool,
) {
    let mask = 1usize << axis;
    let inv_sqrt_2 = std::f64::consts::FRAC_1_SQRT_2;
    let t_phase = Complex {
        re: inv_sqrt_2,
        im: inv_sqrt_2,
    };
    for zero_index in 0..amplitudes.len() {
        if zero_index & mask != 0 || !enabled(zero_index) {
            continue;
        }
        let one_index = zero_index | mask;
        let zero = amplitudes[zero_index];
        let one = amplitudes[one_index];
        let (new_zero, new_one) = match gate {
            SingleGate::H => (
                (zero + one).scaled(inv_sqrt_2),
                (zero - one).scaled(inv_sqrt_2),
            ),
            SingleGate::X => (one, zero),
            SingleGate::Z => (zero, one.scaled(-1.0)),
            SingleGate::T => (zero, one * t_phase),
        };
        amplitudes[zero_index] = new_zero;
        amplitudes[one_index] = new_one;
    }
}

fn protected_value(
    index: usize,
    protected: ProtectedBit,
    source_axes: &[usize],
    function: &[u16],
) -> bool {
    match protected.region {
        ProtectedRegion::Source => bit(index, source_axes[usize::from(protected.index)]),
        ProtectedRegion::Ancilla => {
            let x = local_label(index, source_axes);
            (function[x] >> protected.index) & 1 != 0
        }
    }
}

fn controls_match(
    index: usize,
    controls: &[Control],
    source_axes: &[usize],
    function: &[u16],
) -> bool {
    controls.iter().all(|control| {
        protected_value(index, control.bit, source_axes, function) == control.when_one
    })
}

pub(super) fn run_protected_use(
    component: &mut Component,
    source_axes: &[usize],
    target_wires: &[WireId],
    function: &[u16],
    operations: &[ProtectedUse],
) -> Result<(), SimulationError> {
    for operation in operations {
        match operation {
            ProtectedUse::ProtectedGate { bit, gate } => {
                let phase = match gate {
                    SingleGate::Z => Complex { re: -1.0, im: 0.0 },
                    SingleGate::T => Complex {
                        re: std::f64::consts::FRAC_1_SQRT_2,
                        im: std::f64::consts::FRAC_1_SQRT_2,
                    },
                    _ => {
                        return Err(SimulationError::InconsistentVerifiedIr(
                            "non-diagonal protected gate",
                        ));
                    }
                };
                for (index, amplitude) in component.amplitudes.iter_mut().enumerate() {
                    if protected_value(index, *bit, source_axes, function) {
                        *amplitude = *amplitude * phase;
                    }
                }
            }
            ProtectedUse::ControlledTargetGate {
                controls,
                target_index,
                gate,
            } => {
                let target = target_wires.get(*target_index).ok_or(
                    SimulationError::InconsistentVerifiedIr("protected target is missing"),
                )?;
                let axis = component.position(*target)?;
                apply_gate(&mut component.amplitudes, axis, *gate, |index| {
                    controls_match(index, controls, source_axes, function)
                });
            }
            ProtectedUse::ControlledPhase { controls, phase } => {
                let factor = match phase {
                    ScalarPhase::MinusOne => Complex { re: -1.0, im: 0.0 },
                    ScalarPhase::EighthTurn => Complex {
                        re: std::f64::consts::FRAC_1_SQRT_2,
                        im: std::f64::consts::FRAC_1_SQRT_2,
                    },
                };
                for (index, amplitude) in component.amplitudes.iter_mut().enumerate() {
                    if controls_match(index, controls, source_axes, function) {
                        *amplitude = *amplitude * factor;
                    }
                }
            }
        }
    }
    Ok(())
}

pub(super) fn run_qif_arm(
    component: &mut Component,
    target_axes: &[usize],
    control_axis: usize,
    when_one: bool,
    steps: &[UnitaryStep],
) {
    let mut axes = target_axes.to_vec();
    axes.push(control_axis);
    for step in steps {
        let mut step = step.to_circuit_step();
        step.controls.push(BitControl {
            index: target_axes.len(),
            when_one,
        });
        // QuantumIf precharges both arms before consuming either owner. This
        // compatibility adapter must neither charge again nor create evidence.
        run_circuit_precharged(component, &axes, &[step]);
    }
}

fn phase_factor(exponent: u8) -> Complex {
    let s = std::f64::consts::FRAC_1_SQRT_2;
    let (re, im) = [
        (1.0, 0.0),
        (s, s),
        (0.0, 1.0),
        (-s, s),
        (-1.0, 0.0),
        (-s, -s),
        (0.0, -1.0),
        (s, -s),
    ][usize::from(exponent)];
    Complex { re, im }
}

pub(super) fn run_circuit(
    component: &mut Component,
    axes: &[usize],
    steps: &[CircuitStep],
    budget: &mut ExecutionBudget,
) -> Result<(), SimulationError> {
    // Charge the transitive cost before cloning or expanding dependencies.
    for step in steps {
        budget.charge(match &step.action {
            CircuitAction::Contract { evidence, .. } => evidence.expanded_steps(),
            _ => 1,
        })?;
    }
    run_circuit_precharged(component, axes, steps);
    Ok(())
}

fn run_circuit_precharged(component: &mut Component, axes: &[usize], steps: &[CircuitStep]) {
    for step in steps {
        let enabled = |index| {
            step.controls
                .iter()
                .all(|c| bit(index, axes[c.index]) == c.when_one)
        };
        match &step.action {
            CircuitAction::Contract {
                indices,
                evidence,
                adjoint,
            } => {
                // Execute the checked extracted circuit, which may contain
                // proved cleanup substitutions. Retain every outer control
                // and remap the function's ordered interface axes.
                let mut body = evidence.circuit().steps().to_vec();
                if *adjoint {
                    crate::contract::invert_steps(&mut body);
                }
                for inner in &mut body {
                    for control in &mut inner.controls {
                        control.index = indices[control.index];
                    }
                    inner.controls.extend(step.controls.iter().cloned());
                    match &mut inner.action {
                        CircuitAction::Hadamard { target } => *target = indices[*target],
                        CircuitAction::Monomial {
                            indices: targets, ..
                        }
                        | CircuitAction::Contract {
                            indices: targets, ..
                        } => {
                            for target in targets {
                                *target = indices[*target];
                            }
                        }
                    }
                }
                run_circuit_precharged(component, axes, &body);
            }
            CircuitAction::Hadamard { target } => {
                apply_gate(
                    &mut component.amplitudes,
                    axes[*target],
                    SingleGate::H,
                    enabled,
                );
            }
            CircuitAction::Monomial {
                indices,
                permutation,
                phases,
            } => {
                // Retain in-place execution for the small gates emitted by
                // compatibility adapters. Canonicalization must not allocate
                // another full state vector for an X, Z, T or scalar phase.
                let gate = match (
                    indices.as_slice(),
                    permutation.as_slice(),
                    phases.as_slice(),
                ) {
                    ([_], [1, 0], [0, 0]) => Some(SingleGate::X),
                    ([_], [0, 1], [0, 4]) => Some(SingleGate::Z),
                    ([_], [0, 1], [0, 1]) => Some(SingleGate::T),
                    _ => None,
                };
                if let Some(gate) = gate {
                    apply_gate(&mut component.amplitudes, axes[indices[0]], gate, enabled);
                    continue;
                }
                if indices.is_empty() {
                    let factor = phase_factor(phases[0]);
                    for (index, amplitude) in component.amplitudes.iter_mut().enumerate() {
                        if enabled(index) {
                            *amplitude = *amplitude * factor;
                        }
                    }
                    continue;
                }
                let targets: Vec<_> = indices.iter().map(|i| axes[*i]).collect();
                let mut amplitudes = vec![Complex::ZERO; component.amplitudes.len()];
                for (index, amplitude) in component.amplitudes.iter().copied().enumerate() {
                    if !enabled(index) {
                        amplitudes[index] += amplitude;
                        continue;
                    }
                    let label = local_label(index, &targets);
                    let mut output = index;
                    for (place, axis) in targets.iter().enumerate() {
                        output = (output & !(1 << axis))
                            | (((usize::from(permutation[label]) >> place) & 1) << axis);
                    }
                    amplitudes[output] += amplitude * phase_factor(phases[label]);
                }
                component.amplitudes = amplitudes;
            }
        }
    }
}
