//! Single-trajectory reference sampling. This module issues no semantic evidence.

use super::*;
use std::convert::Infallible;

const TOLERANCE: f64 = 1.0 / ((1_u64 << 40) as f64);

/// A fallible source of uniformly distributed 64-bit words.
/// Uniformity is a caller premise; the sampler cannot certify an RNG.
pub trait RandomSource {
    type Error;
    fn next_u64(&mut self) -> Result<u64, Self::Error>;
}

impl<F, E> RandomSource for F
where
    F: FnMut() -> Result<u64, E>,
{
    type Error = E;
    fn next_u64(&mut self) -> Result<u64, E> {
        self()
    }
}

/// The reproducible `splitmix64-v1` reference generator; not cryptographic.
#[derive(Clone, Debug)]
pub struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    pub fn new(seed: u64) -> Self {
        Self { state: seed }
    }
}

impl RandomSource for SplitMix64 {
    type Error = Infallible;

    fn next_u64(&mut self) -> Result<u64, Infallible> {
        self.state = self.state.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        Ok(z ^ (z >> 31))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SampleLimits {
    pub max_qubits: usize,
    pub max_amplitude_cells: usize,
    pub max_execution_steps: usize,
}

impl Default for SampleLimits {
    fn default() -> Self {
        Self {
            max_qubits: 16,
            max_amplitude_cells: 1 << 20,
            max_execution_steps: 1_000_000,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Sample {
    /// The same classical output order as `run_closed`.
    pub bits: Vec<bool>,
    /// Executed IR/circuit steps and copied metadata entries, including hidden observations.
    pub execution_steps: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SampleError<E> {
    NotClosed(&'static str),
    Limit(SimulationError),
    RandomSource(E),
    Numerical(&'static str),
    InconsistentVerifiedIr(&'static str),
}

impl<E: fmt::Display> fmt::Display for SampleError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotClosed(reason) => write!(f, "a closed sample requires {reason}"),
            Self::Limit(error) => error.fmt(f),
            Self::RandomSource(error) => write!(f, "random source failed: {error}"),
            Self::Numerical(reason) => write!(f, "numerical sampling failure: {reason}"),
            Self::InconsistentVerifiedIr(reason) => write!(f, "inconsistent verified IR: {reason}"),
        }
    }
}

impl<E: std::error::Error + 'static> std::error::Error for SampleError<E> {}

impl<E> From<SimulationError> for SampleError<E> {
    fn from(error: SimulationError) -> Self {
        match error {
            SimulationError::NotClosed(reason) => Self::NotClosed(reason),
            SimulationError::InconsistentVerifiedIr(reason) => Self::InconsistentVerifiedIr(reason),
            error => Self::Limit(error),
        }
    }
}

fn normalize<E>(state: &mut Component, executed_steps: usize) -> Result<(), SampleError<E>> {
    if state
        .amplitudes
        .iter()
        .any(|z| !z.re.is_finite() || !z.im.is_finite())
    {
        return Err(SampleError::Numerical("nonfinite amplitude"));
    }
    let norm = state.weight();
    // Account only for work since the previous normalization, including gates
    // nested inside one IR operation. This is a numerical guard, not evidence
    // or a certified forward-error bound. Configured unused work grants nothing.
    let tolerance = TOLERANCE + 16.0 * f64::EPSILON * executed_steps as f64;
    if !norm.is_finite() || norm <= 0.0 || (norm - 1.0).abs() > tolerance {
        return Err(SampleError::Numerical("trajectory norm differs from one"));
    }
    let scale = 1.0 / norm.sqrt();
    for amplitude in &mut state.amplitudes {
        *amplitude = amplitude.scaled(scale);
    }
    Ok(())
}

fn observe<R: RandomSource>(
    mut state: Component,
    wire: WireId,
    random: &mut R,
    budget: &mut ExecutionBudget,
) -> Result<(Component, bool), SampleError<R::Error>> {
    normalize(&mut state, 0)?;
    let axis = state.position(wire)?;
    let p0: f64 = state
        .amplitudes
        .iter()
        .enumerate()
        .filter(|(index, _)| !bit(*index, axis))
        .map(|(_, z)| z.norm_squared())
        .sum();
    if !p0.is_finite() || !(-TOLERANCE..=1.0 + TOLERANCE).contains(&p0) {
        return Err(SampleError::Numerical("invalid observation probability"));
    }
    let projection = state.prepare_projection(wire, budget)?;
    // Deterministic measurements consume a word too, fixing the trace contract.
    let word = random.next_u64().map_err(SampleError::RandomSource)?;
    let u = (word >> 11) as f64 * (1.0 / ((1_u64 << 53) as f64));
    let outcome = u >= p0.clamp(0.0, 1.0);
    let mut state = projection.project(outcome);
    let weight = state.weight();
    if !weight.is_finite() || weight <= 0.0 {
        return Err(SampleError::Numerical(
            "selected branch has zero or invalid norm",
        ));
    }
    for amplitude in &mut state.amplitudes {
        *amplitude = amplitude.scaled(1.0 / weight.sqrt());
    }
    normalize(&mut state, 0)?;
    Ok((state, outcome))
}

fn trajectory<R: RandomSource>(
    mut state: Component,
    operations: &[RawOp],
    random: &mut R,
    limits: SimulationLimits,
    budget: &mut ExecutionBudget,
) -> Result<Component, SampleError<R::Error>> {
    for operation in operations {
        match operation {
            RawOp::MeasureZ { input, output } => {
                budget.charge(1)?;
                let wires = state.take(*input)?;
                let (next, outcome) = observe(state, wires[0], random, budget)?;
                state = next;
                state.classical.insert(*output, outcome);
            }
            RawOp::Reset {
                input,
                output,
                fresh_wire,
            } => {
                // Dispatch and the hidden measurement are both charged.
                budget.charge(2)?;
                let wires = state.take(*input)?;
                state = observe(state, wires[0], random, budget)?.0;
                state.add_zero_wire(*fresh_wire, limits)?;
                state.tokens.insert(*output, vec![*fresh_wire]);
            }
            RawOp::Discard { input } => {
                budget.charge(1)?;
                let mut wires = state.take(*input)?;
                wires.sort();
                for wire in wires {
                    budget.charge(1)?;
                    state = observe(state, wire, random, budget)?.0;
                }
            }
            RawOp::ClassicalBranch {
                condition,
                then_ops,
                else_ops,
                quantum_phis,
                classical_phis,
            } => {
                budget.charge(1)?;
                let then_arm = state.classical(*condition)?;
                state = trajectory(
                    state,
                    if then_arm { then_ops } else { else_ops },
                    random,
                    limits,
                    budget,
                )?;
                state = relabel_branch(state, then_arm, quantum_phis, classical_phis, budget)?;
            }
            _ => {
                // Share only deterministic numerical execution. Observations and
                // branches above never construct an exhaustive ensemble.
                let before = budget.remaining;
                let copies_before = budget.copied_entries;
                let mut next = execute_op(state, operation, limits, budget)?;
                if next.len() != 1 {
                    return Err(SampleError::InconsistentVerifiedIr(
                        "non-observing step branched",
                    ));
                }
                state = next.pop().expect("exactly one successor");
                // Metadata copies cost resources but introduce no numerical
                // error, so they must not relax the trajectory norm alarm.
                let arithmetic_steps =
                    before - budget.remaining - (budget.copied_entries - copies_before);
                normalize(&mut state, arithmetic_steps)?;
            }
        }
    }
    Ok(state)
}

/// Sample a fresh, closed, independently verified program once. No quantum
/// state survives this call. The supplied RNG stream is advanced in execution
/// order, including hidden reset/discard observations. Floating-point reference
/// execution is separate from the exact semantic evidence authorizing the IR.
pub fn sample_closed<R: RandomSource>(
    program: &(impl ExecutableProgram + ?Sized),
    random: &mut R,
    limits: SampleLimits,
) -> Result<Sample, SampleError<R::Error>> {
    let raw = program.execution_view();
    if !raw.quantum_inputs.is_empty()
        || !raw.classical_inputs.is_empty()
        || !raw.quantum_outputs.is_empty()
    {
        return Err(SampleError::NotClosed(
            "no external inputs or quantum outputs",
        ));
    }
    let limits = SimulationLimits {
        max_qubits: limits.max_qubits,
        max_components: 1,
        max_amplitude_cells: limits.max_amplitude_cells,
        max_execution_steps: limits.max_execution_steps,
    };
    check_amplitude_cells(1, limits)?;
    let mut budget = ExecutionBudget {
        copied_entries: 0,
        remaining: limits.max_execution_steps,
        max: limits.max_execution_steps,
    };
    let mut state = trajectory(
        Component::vacuum(),
        &raw.operations,
        random,
        limits,
        &mut budget,
    )?;
    normalize(&mut state, 0)?;
    if !state.tokens.is_empty() || !state.axes.is_empty() {
        return Err(SampleError::InconsistentVerifiedIr(
            "live quantum output remains",
        ));
    }
    Ok(Sample {
        bits: raw
            .classical_outputs
            .iter()
            .map(|id| state.classical(*id))
            .collect::<Result<_, _>>()?,
        execution_steps: (budget.max - budget.remaining) as u64,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_nonfinite_zero_and_excessive_norm_error() {
        for value in [f64::NAN, f64::INFINITY, 0.0, 1.001] {
            let mut state = Component::vacuum();
            state.amplitudes[0].re = value;
            assert!(matches!(
                normalize::<Infallible>(&mut state, 0),
                Err(SampleError::Numerical(_))
            ));
        }
        let mut state = Component::vacuum();
        state.amplitudes[0].re += f64::EPSILON;
        normalize::<Infallible>(&mut state, 0).unwrap();
        assert_eq!(state.weight(), 1.0);
    }

    #[test]
    fn norm_allowance_tracks_executed_work_and_remains_bounded() {
        let mut state = Component::vacuum();
        state.amplitudes[0].re += 2e-12;
        assert!(normalize::<Infallible>(&mut state, 0).is_err());
        normalize::<Infallible>(&mut state, 12_000).unwrap();
        assert_eq!(state.weight(), 1.0);
        for value in [0.0, f64::NAN, f64::INFINITY, 1.001] {
            state.amplitudes[0].re = value;
            assert!(normalize::<Infallible>(&mut state, 1_000_000).is_err());
        }
    }
}
