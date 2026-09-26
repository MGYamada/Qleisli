//! A finite reference interpreter for already verified, closed IR programs.
//!
//! This interpreter is a diagnostic aid, not a proof of the verifier's general
//! soundness. Each component of the ensemble is an *unnormalized* pure state.
//! Separate components with the same visible classical values are added as
//! probabilities, never as amplitudes. This preserves the mixed state caused
//! by a partial measurement, discard, or reset.

use std::collections::BTreeMap;
use std::fmt;

use crate::VerifiedProgram;
use crate::ir::{
    CircuitAction, CircuitStep, ClassicalId, ClassicalPhi, Control, ProtectedBit, ProtectedRegion,
    ProtectedUse, QuantumPhi, RawOp, ScalarPhase, SingleGate, TokenId, UnitaryStep, WireId,
};

/// A practical cap on the number of live state-vector axes in this initial
/// interpreter. Limits chosen by the caller may be smaller.
pub const MAX_SIMULATED_QUBITS: usize = 20;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SimulationLimits {
    pub max_qubits: usize,
    pub max_components: usize,
    /// Total complex amplitudes retained across all ensemble components.
    pub max_amplitude_cells: usize,
}

impl Default for SimulationLimits {
    fn default() -> Self {
        Self {
            max_qubits: 16,
            max_components: 65_536,
            max_amplitude_cells: 1 << 20,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SimulationError {
    NotClosed(&'static str),
    DimensionLimit { required: usize, max: usize },
    ComponentLimit { max: usize },
    AmplitudeLimit { required: usize, max: usize },
    InconsistentVerifiedIr(&'static str),
}

impl fmt::Display for SimulationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotClosed(reason) => write!(f, "a closed program is required: {reason}"),
            Self::DimensionLimit { required, max } => {
                write!(f, "simulation requires {required} qubits; limit is {max}")
            }
            Self::ComponentLimit { max } => {
                write!(f, "simulation exceeds the {max}-component ensemble limit")
            }
            Self::AmplitudeLimit { required, max } => {
                write!(
                    f,
                    "simulation requires {required} amplitude cells; limit is {max}"
                )
            }
            Self::InconsistentVerifiedIr(reason) => {
                write!(f, "verified IR is inconsistent during simulation: {reason}")
            }
        }
    }
}

impl std::error::Error for SimulationError {}

#[derive(Clone, Copy, Debug, Default)]
struct Complex {
    re: f64,
    im: f64,
}

impl Complex {
    const ZERO: Self = Self { re: 0.0, im: 0.0 };
    const ONE: Self = Self { re: 1.0, im: 0.0 };

    fn scaled(self, factor: f64) -> Self {
        Self {
            re: self.re * factor,
            im: self.im * factor,
        }
    }

    fn norm_squared(self) -> f64 {
        self.re * self.re + self.im * self.im
    }
}

impl std::ops::Add for Complex {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self {
            re: self.re + rhs.re,
            im: self.im + rhs.im,
        }
    }
}

impl std::ops::AddAssign for Complex {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl std::ops::Sub for Complex {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Self {
            re: self.re - rhs.re,
            im: self.im - rhs.im,
        }
    }
}

impl std::ops::Mul for Complex {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        Self {
            re: self.re * rhs.re - self.im * rhs.im,
            im: self.re * rhs.im + self.im * rhs.re,
        }
    }
}

#[derive(Clone, Debug)]
struct Component {
    /// Axis 0 is the least significant bit in the state-vector index.
    axes: Vec<WireId>,
    amplitudes: Vec<Complex>,
    tokens: BTreeMap<TokenId, Vec<WireId>>,
    classical: BTreeMap<ClassicalId, bool>,
}

impl Component {
    fn vacuum() -> Self {
        Self {
            axes: Vec::new(),
            amplitudes: vec![Complex::ONE],
            tokens: BTreeMap::new(),
            classical: BTreeMap::new(),
        }
    }

    fn position(&self, wire: WireId) -> Result<usize, SimulationError> {
        self.axes
            .iter()
            .position(|candidate| *candidate == wire)
            .ok_or(SimulationError::InconsistentVerifiedIr(
                "wire axis is missing",
            ))
    }

    fn take(&mut self, token: TokenId) -> Result<Vec<WireId>, SimulationError> {
        self.tokens
            .remove(&token)
            .ok_or(SimulationError::InconsistentVerifiedIr("token is missing"))
    }

    fn classical(&self, id: ClassicalId) -> Result<bool, SimulationError> {
        self.classical
            .get(&id)
            .copied()
            .ok_or(SimulationError::InconsistentVerifiedIr(
                "classical value is missing",
            ))
    }

    fn add_zero_wire(
        &mut self,
        wire: WireId,
        limits: SimulationLimits,
    ) -> Result<(), SimulationError> {
        check_dimension(self.axes.len() + 1, limits)?;
        check_amplitude_cells(self.amplitudes.len() * 2, limits)?;
        self.axes.push(wire);
        self.amplitudes
            .resize(self.amplitudes.len() * 2, Complex::ZERO);
        Ok(())
    }

    /// Project one wire, then remove its axis. The probability weight remains
    /// in the norm of the resulting vector.
    fn project_remove(&self, wire: WireId, outcome: bool) -> Result<Self, SimulationError> {
        let axis = self.position(wire)?;
        let mask = 1usize << axis;
        let mut projected = vec![Complex::ZERO; self.amplitudes.len() / 2];
        for (old_index, amplitude) in self.amplitudes.iter().copied().enumerate() {
            if (old_index & mask != 0) == outcome {
                let low = old_index & (mask - 1);
                let high = old_index >> (axis + 1);
                projected[low | (high << axis)] = amplitude;
            }
        }
        let mut component = Self {
            axes: self.axes.clone(),
            amplitudes: projected,
            tokens: self.tokens.clone(),
            classical: self.classical.clone(),
        };
        component.axes.remove(axis);
        Ok(component)
    }

    fn weight(&self) -> f64 {
        self.amplitudes.iter().map(|z| z.norm_squared()).sum()
    }
}

fn check_dimension(required: usize, limits: SimulationLimits) -> Result<(), SimulationError> {
    let max = limits.max_qubits.min(MAX_SIMULATED_QUBITS);
    if required > max {
        Err(SimulationError::DimensionLimit { required, max })
    } else {
        Ok(())
    }
}

fn check_components(required: usize, limits: SimulationLimits) -> Result<(), SimulationError> {
    if required > limits.max_components {
        Err(SimulationError::ComponentLimit {
            max: limits.max_components,
        })
    } else {
        Ok(())
    }
}

fn check_amplitude_cells(required: usize, limits: SimulationLimits) -> Result<(), SimulationError> {
    if required > limits.max_amplitude_cells {
        Err(SimulationError::AmplitudeLimit {
            required,
            max: limits.max_amplitude_cells,
        })
    } else {
        Ok(())
    }
}

fn bit(index: usize, axis: usize) -> bool {
    (index >> axis) & 1 != 0
}

fn local_label(index: usize, axes: &[usize]) -> usize {
    axes.iter().enumerate().fold(0, |label, (place, axis)| {
        label | (usize::from(bit(index, *axis)) << place)
    })
}

fn apply_gate(
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

fn run_protected_use(
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

fn run_unitary_steps(
    component: &mut Component,
    target_axes: &[usize],
    control_axis: usize,
    when_one: bool,
    steps: &[UnitaryStep],
) {
    for step in steps {
        match step {
            UnitaryStep::Gate { gate, target_index } => {
                apply_gate(
                    &mut component.amplitudes,
                    target_axes[*target_index],
                    *gate,
                    |index| bit(index, control_axis) == when_one,
                );
            }
            UnitaryStep::Cnot {
                control_index,
                target_index,
            } => {
                let inner_control_axis = target_axes[*control_index];
                apply_gate(
                    &mut component.amplitudes,
                    target_axes[*target_index],
                    SingleGate::X,
                    |index| bit(index, control_axis) == when_one && bit(index, inner_control_axis),
                );
            }
            UnitaryStep::Toffoli {
                control_a_index,
                control_b_index,
                target_index,
            } => {
                let first_axis = target_axes[*control_a_index];
                let second_axis = target_axes[*control_b_index];
                apply_gate(
                    &mut component.amplitudes,
                    target_axes[*target_index],
                    SingleGate::X,
                    |index| {
                        bit(index, control_axis) == when_one
                            && bit(index, first_axis)
                            && bit(index, second_axis)
                    },
                );
            }
            UnitaryStep::ScalarPhase(phase) => {
                let factor = match phase {
                    ScalarPhase::MinusOne => Complex { re: -1.0, im: 0.0 },
                    ScalarPhase::EighthTurn => Complex {
                        re: std::f64::consts::FRAC_1_SQRT_2,
                        im: std::f64::consts::FRAC_1_SQRT_2,
                    },
                };
                for (index, amplitude) in component.amplitudes.iter_mut().enumerate() {
                    if bit(index, control_axis) == when_one {
                        *amplitude = *amplitude * factor;
                    }
                }
            }
        }
    }
}

fn run_circuit(component: &mut Component, axes: &[usize], steps: &[CircuitStep]) {
    for step in steps {
        let enabled = |index| {
            step.controls
                .iter()
                .all(|c| bit(index, axes[c.index]) == c.when_one)
        };
        match &step.action {
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
                    ][usize::from(phases[label])];
                    amplitudes[output] += amplitude * Complex { re, im };
                }
                component.amplitudes = amplitudes;
            }
        }
    }
}

fn relabel_branch(
    mut component: Component,
    then_arm: bool,
    quantum_phis: &[QuantumPhi],
    classical_phis: &[ClassicalPhi],
) -> Result<Component, SimulationError> {
    let mut wire_renames = BTreeMap::new();
    let mut outputs = Vec::with_capacity(quantum_phis.len());
    for phi in quantum_phis {
        let old_token = if then_arm {
            phi.then_token
        } else {
            phi.else_token
        };
        let old_wires = component.take(old_token)?;
        if old_wires.len() != phi.output_wires.len() {
            return Err(SimulationError::InconsistentVerifiedIr("phi shape differs"));
        }
        for (old, new) in old_wires.iter().zip(&phi.output_wires) {
            wire_renames.insert(*old, *new);
        }
        outputs.push((phi.output, phi.output_wires.clone()));
    }
    for axis in &mut component.axes {
        if let Some(new) = wire_renames.get(axis) {
            *axis = *new;
        }
    }
    for (token, wires) in outputs {
        component.tokens.insert(token, wires);
    }
    for phi in classical_phis {
        let old = if then_arm { phi.then_id } else { phi.else_id };
        let value = component.classical(old)?;
        component.classical.insert(phi.output, value);
    }
    Ok(component)
}

fn execute_op(
    mut component: Component,
    operation: &RawOp,
    limits: SimulationLimits,
) -> Result<Vec<Component>, SimulationError> {
    match operation {
        RawOp::ApplyUnitary {
            input,
            output,
            steps,
        } => {
            let wires = component.take(*input)?;
            let axes = wires
                .iter()
                .map(|wire| component.position(*wire))
                .collect::<Result<Vec<_>, _>>()?;
            run_circuit(&mut component, &axes, steps);
            component.tokens.insert(*output, wires);
        }
        RawOp::Init0 { output, wire } => {
            component.add_zero_wire(*wire, limits)?;
            component.tokens.insert(*output, vec![*wire]);
        }
        RawOp::Gate {
            gate,
            input,
            output,
        } => {
            let wires = component.take(*input)?;
            let axis = component.position(wires[0])?;
            apply_gate(&mut component.amplitudes, axis, *gate, |_| true);
            component.tokens.insert(*output, wires);
        }
        RawOp::Cnot {
            control,
            target,
            control_out,
            target_out,
        } => {
            let control_wires = component.take(*control)?;
            let target_wires = component.take(*target)?;
            let control_axis = component.position(control_wires[0])?;
            let target_axis = component.position(target_wires[0])?;
            apply_gate(
                &mut component.amplitudes,
                target_axis,
                SingleGate::X,
                |index| bit(index, control_axis),
            );
            component.tokens.insert(*control_out, control_wires);
            component.tokens.insert(*target_out, target_wires);
        }
        RawOp::Toffoli {
            control_a,
            control_b,
            target,
            control_a_out,
            control_b_out,
            target_out,
        } => {
            let first = component.take(*control_a)?;
            let second = component.take(*control_b)?;
            let target_wires = component.take(*target)?;
            let first_axis = component.position(first[0])?;
            let second_axis = component.position(second[0])?;
            let target_axis = component.position(target_wires[0])?;
            apply_gate(
                &mut component.amplitudes,
                target_axis,
                SingleGate::X,
                |index| bit(index, first_axis) && bit(index, second_axis),
            );
            component.tokens.insert(*control_a_out, first);
            component.tokens.insert(*control_b_out, second);
            component.tokens.insert(*target_out, target_wires);
        }
        RawOp::QuantumIf {
            control,
            target,
            control_out,
            target_out,
            zero_ops,
            one_ops,
        } => {
            let control_wires = component.take(*control)?;
            let target_wires = component.take(*target)?;
            let control_axis = component.position(control_wires[0])?;
            let target_axes = target_wires
                .iter()
                .map(|wire| component.position(*wire))
                .collect::<Result<Vec<_>, _>>()?;
            run_unitary_steps(&mut component, &target_axes, control_axis, false, zero_ops);
            run_unitary_steps(&mut component, &target_axes, control_axis, true, one_ops);
            component.tokens.insert(*control_out, control_wires);
            component.tokens.insert(*target_out, target_wires);
        }
        RawOp::Split {
            input,
            left,
            right,
            left_bits,
        } => {
            let wires = component.take(*input)?;
            let split = usize::from(*left_bits);
            component.tokens.insert(*left, wires[..split].to_vec());
            component.tokens.insert(*right, wires[split..].to_vec());
        }
        RawOp::Join {
            left,
            right,
            output,
        } => {
            let mut wires = component.take(*left)?;
            wires.extend(component.take(*right)?);
            component.tokens.insert(*output, wires);
        }
        RawOp::LiftBasis {
            input,
            output,
            output_wires,
            table,
        } => {
            let input_wires = component.take(*input)?;
            let input_axes = input_wires
                .iter()
                .map(|wire| component.position(*wire))
                .collect::<Result<Vec<_>, _>>()?;
            let added = output_wires.len() - input_wires.len();
            check_dimension(component.axes.len() + added, limits)?;
            let old_len = component.amplitudes.len();
            let old_axis_count = component.axes.len();
            check_amplitude_cells(old_len << added, limits)?;
            let mut new_amplitudes = vec![Complex::ZERO; old_len << added];
            let output_axes: Vec<_> = output_wires
                .iter()
                .enumerate()
                .map(|(place, wire)| {
                    if place < input_wires.len() {
                        component.position(*wire)
                    } else {
                        Ok(old_axis_count + place - input_wires.len())
                    }
                })
                .collect::<Result<_, _>>()?;
            for (old_index, amplitude) in component.amplitudes.iter().copied().enumerate() {
                let label = local_label(old_index, &input_axes);
                let mapped = usize::from(table[label]);
                let mut new_index = old_index;
                for (place, axis) in output_axes.iter().copied().enumerate() {
                    let mask = 1usize << axis;
                    if bit(mapped, place) {
                        new_index |= mask;
                    } else {
                        new_index &= !mask;
                    }
                }
                new_amplitudes[new_index] += amplitude;
            }
            component
                .axes
                .extend_from_slice(&output_wires[input_wires.len()..]);
            component.amplitudes = new_amplitudes;
            component.tokens.insert(*output, output_wires.clone());
        }
        RawOp::MeasureZ { input, output } => {
            let wires = component.take(*input)?;
            let mut outcomes = Vec::with_capacity(2);
            for outcome in [false, true] {
                let mut branch = component.project_remove(wires[0], outcome)?;
                if branch.weight() > 0.0 {
                    branch.classical.insert(*output, outcome);
                    outcomes.push(branch);
                }
            }
            return Ok(outcomes);
        }
        RawOp::Reset {
            input,
            output,
            fresh_wire,
        } => {
            let wires = component.take(*input)?;
            let mut branches = Vec::with_capacity(2);
            for outcome in [false, true] {
                let mut branch = component.project_remove(wires[0], outcome)?;
                if branch.weight() > 0.0 {
                    branch.add_zero_wire(*fresh_wire, limits)?;
                    branch.tokens.insert(*output, vec![*fresh_wire]);
                    branches.push(branch);
                }
            }
            return Ok(branches);
        }
        RawOp::Discard { input } => {
            let wires = component.take(*input)?;
            let mut branches = vec![component];
            for wire in wires {
                let mut next = Vec::new();
                for branch in branches {
                    for outcome in [false, true] {
                        let projected = branch.project_remove(wire, outcome)?;
                        if projected.weight() > 0.0 {
                            next.push(projected);
                            check_components(next.len(), limits)?;
                        }
                    }
                }
                branches = next;
            }
            return Ok(branches);
        }
        RawOp::ClassicalNot { input, output } => {
            let value = !component.classical(*input)?;
            component.classical.insert(*output, value);
        }
        RawOp::ClassicalXor {
            left,
            right,
            output,
        } => {
            let value = component.classical(*left)? ^ component.classical(*right)?;
            component.classical.insert(*output, value);
        }
        RawOp::ClassicalBranch {
            condition,
            then_ops,
            else_ops,
            quantum_phis,
            classical_phis,
        } => {
            let then_arm = component.classical(*condition)?;
            let arm = if then_arm { then_ops } else { else_ops };
            let result = execute_ops(vec![component], arm, limits)?;
            return result
                .into_iter()
                .map(|branch| relabel_branch(branch, then_arm, quantum_phis, classical_phis))
                .collect();
        }
        RawOp::ComputeUseUncompute {
            source,
            source_out,
            targets,
            ancilla_wires,
            function,
            use_ops,
        } => {
            check_dimension(component.axes.len() + ancilla_wires.len(), limits)?;
            let source_wires = component.take(*source)?;
            let source_axes = source_wires
                .iter()
                .map(|wire| component.position(*wire))
                .collect::<Result<Vec<_>, _>>()?;
            let mut target_wires = Vec::with_capacity(targets.len());
            for target in targets {
                let wires = component.take(target.input)?;
                target_wires.push(wires[0]);
            }
            run_protected_use(
                &mut component,
                &source_axes,
                &target_wires,
                function,
                use_ops,
            )?;
            component.tokens.insert(*source_out, source_wires);
            for (target, wire) in targets.iter().zip(target_wires) {
                component.tokens.insert(target.output, vec![wire]);
            }
        }
    }
    Ok(vec![component])
}

fn execute_ops(
    mut ensemble: Vec<Component>,
    operations: &[RawOp],
    limits: SimulationLimits,
) -> Result<Vec<Component>, SimulationError> {
    for operation in operations {
        let mut next = Vec::new();
        let mut next_cells = 0usize;
        for component in ensemble {
            for successor in execute_op(component, operation, limits)? {
                next_cells = next_cells.checked_add(successor.amplitudes.len()).ok_or(
                    SimulationError::AmplitudeLimit {
                        required: usize::MAX,
                        max: limits.max_amplitude_cells,
                    },
                )?;
                check_amplitude_cells(next_cells, limits)?;
                next.push(successor);
                check_components(next.len(), limits)?;
            }
        }
        ensemble = next;
    }
    Ok(ensemble)
}

/// Execute a verified program with no quantum or classical inputs and no live
/// quantum outputs. The returned key follows `classical_outputs` order; a
/// component's norm squared contributes to that outcome's probability.
///
/// Register/table bit 0 is the first wire in the register. The global
/// state-vector index likewise uses axis 0 as its least significant bit.
/// Floating-point probabilities can differ slightly from their exact values.
pub fn run_closed(
    program: &VerifiedProgram,
    limits: SimulationLimits,
) -> Result<BTreeMap<Vec<bool>, f64>, SimulationError> {
    let raw = program.raw();
    if !raw.quantum_inputs.is_empty() {
        return Err(SimulationError::NotClosed("quantum inputs are present"));
    }
    if !raw.classical_inputs.is_empty() {
        return Err(SimulationError::NotClosed("classical inputs are present"));
    }
    if !raw.quantum_outputs.is_empty() {
        return Err(SimulationError::NotClosed("quantum outputs are present"));
    }
    check_components(1, limits)?;
    check_amplitude_cells(1, limits)?;
    let ensemble = execute_ops(vec![Component::vacuum()], &raw.operations, limits)?;
    let mut probabilities = BTreeMap::new();
    for component in ensemble {
        if !component.tokens.is_empty() || !component.axes.is_empty() {
            return Err(SimulationError::InconsistentVerifiedIr(
                "live quantum output remains",
            ));
        }
        let outcome = raw
            .classical_outputs
            .iter()
            .map(|id| component.classical(*id))
            .collect::<Result<Vec<_>, _>>()?;
        *probabilities.entry(outcome).or_insert(0.0) += component.weight();
    }
    Ok(probabilities)
}
