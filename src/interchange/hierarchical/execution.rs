//! Bounded floating-point interpretation of retained, freshly checked actual IR.
//! This adapter does not issue evidence or use requested meanings as a program.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

use super::super::json;
use super::{
    CheckedInstrument, CheckedRequest, Error, Matrix, Reconstructed, Result, Value, bridge,
};
use crate::sim::RandomSource;
use std::collections::BTreeMap;

/// Explicit execution bounds, independent of the acceptance checker budgets.
#[derive(Clone, Copy, Debug)]
pub struct ExecutionLimits {
    /// Peak aggregate complex cells owned by execution, including work buffers
    /// and all returned branches. The caller's input slice is excluded.
    pub max_amplitudes: usize,
    /// Definition visits and coefficient work; repeats spend work per iteration.
    pub max_steps: usize,
}

/// Quantum basis varies fastest; reference index is the outer dimension.
/// Coefficients are `[real, imaginary]`, without normalization or phase removal.
#[derive(Debug)]
pub struct StateVector {
    pub amplitudes: Vec<[f64; 2]>,
    pub quantum_bits: usize,
    pub reference_dimension: usize,
    pub steps: usize,
}

/// Every measurement outcome, including zero branches, in actual pack order.
/// Within each branch the residual quantum basis varies before the reference.
#[derive(Debug)]
pub struct InstrumentBranches {
    pub branches: Vec<Vec<[f64; 2]>>,
    pub measured_bits: usize,
    pub residual_quantum_bits: usize,
    pub reference_dimension: usize,
    pub steps: usize,
}

/// Bounds for fresh shots, independent of acceptance and transport limits.
#[derive(Clone, Copy, Debug)]
pub struct SamplingLimits {
    /// The requested number of shots must be positive and no greater than this.
    pub max_shots: usize,
    /// Work is shared by all shots, including input/branch normalization.
    /// Amplitudes include the normalized input, retained shot states, execution
    /// work buffers and one complex-cell allowance per temporary real weight.
    pub execution: ExecutionLimits,
}

/// One actual packed outcome and its normalized joint residual/reference state.
#[derive(Debug)]
pub struct InstrumentSample {
    /// Low-bit-first integer in the same actual pack order as `execute`.
    pub outcome: usize,
    /// Numerically normalized Born probability for this complete outcome.
    pub probability: f64,
    pub amplitudes: Vec<[f64; 2]>,
}

#[derive(Debug)]
pub struct InstrumentSamples {
    pub shots: Vec<InstrumentSample>,
    pub measured_bits: usize,
    pub residual_quantum_bits: usize,
    pub reference_dimension: usize,
    /// The supplied input's finite positive squared norm, before normalization.
    pub input_norm_squared: f64,
    pub steps: usize,
}

/// A failed batch returns no partial result; earlier shots may have consumed RNG
/// words. RNG errors retain the caller's original error value.
#[derive(Debug)]
pub enum SamplingError<E> {
    Execution(Error),
    RandomSource(E),
    Numerical(&'static str),
}

impl<E> From<Error> for SamplingError<E> {
    fn from(error: Error) -> Self {
        Self::Execution(error)
    }
}
impl<E: std::fmt::Display> std::fmt::Display for SamplingError<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Execution(error) => error.fmt(f),
            Self::RandomSource(error) => write!(f, "random source failed: {error}"),
            Self::Numerical(reason) => write!(f, "numerical sampling failure: {reason}"),
        }
    }
}
impl<E: std::error::Error + 'static> std::error::Error for SamplingError<E> {}

fn unsupported(message: impl Into<String>) -> Error {
    Error::new("unsupported", message)
}
fn invalid(message: impl Into<String>) -> Error {
    Error::new("execution", message)
}
fn index(v: &Value) -> Result<usize> {
    Ok(bridge::number(v)? as usize)
}
fn width_dimension(width: usize) -> Result<usize> {
    1usize
        .checked_shl(u32::try_from(width).map_err(|_| Error::limit("execution width overflow"))?)
        .ok_or_else(|| Error::limit("execution dimension overflow"))
}
fn product(a: usize, b: usize) -> Result<usize> {
    a.checked_mul(b)
        .ok_or_else(|| Error::limit("execution size/work overflow"))
}
fn wires(side: &Value) -> Result<Vec<usize>> {
    side.field("quantum")?
        .array()?
        .iter()
        .flat_map(|p| match p.field("axes").and_then(Value::array) {
            Ok(a) => a.iter().map(index).collect::<Vec<_>>(),
            Err(e) => vec![Err(e)],
        })
        .collect()
}
fn quantum_only(side: &Value) -> Result<()> {
    if side.field("classical")?.array()?.is_empty() {
        Ok(())
    } else {
        Err(unsupported(
            "reference execution requires quantum-only circuit endpoints",
        ))
    }
}
fn owner_axis(side: &Value, owner: usize) -> Result<usize> {
    let mut offset = 0;
    for p in side.field("quantum")?.array()? {
        let axes = p.field("axes")?.array()?;
        if index(p.field("owner")?)? == owner {
            if axes.len() != 1 {
                return Err(unsupported("phase/measurement target must be one Bit"));
            }
            return Ok(offset);
        }
        offset += axes.len();
    }
    Err(invalid("actual target owner absent from its interface"))
}
fn positions(from: &[usize], to: &[usize]) -> Result<Vec<usize>> {
    to.iter()
        .map(|axis| {
            from.iter()
                .position(|x| x == axis)
                .ok_or_else(|| invalid("actual axis absent from its input interface"))
        })
        .collect()
}
fn permutation(map: Vec<usize>, width: usize) -> Result<Vec<usize>> {
    let mut sorted = map.clone();
    sorted.sort_unstable();
    if sorted != (0..width).collect::<Vec<_>>() {
        return Err(invalid(
            "actual execution map is not a complete permutation",
        ));
    }
    Ok(map)
}
fn finite(values: &[[f64; 2]]) -> Result<()> {
    if values.iter().flatten().all(|x| x.is_finite()) {
        Ok(())
    } else {
        Err(invalid("execution coefficients must remain finite"))
    }
}
fn zeroes(cells: usize) -> Result<Vec<[f64; 2]>> {
    let mut result = Vec::new();
    result
        .try_reserve_exact(cells)
        .map_err(|_| Error::limit("cannot allocate bounded execution amplitudes"))?;
    result.resize(cells, [0.0, 0.0]);
    Ok(result)
}
struct Work {
    limits: ExecutionLimits,
    spent: usize,
}
impl Work {
    fn charge(&mut self, amount: usize) -> Result<()> {
        self.spent = self
            .spent
            .checked_add(amount)
            .filter(|n| *n <= self.limits.max_steps)
            .ok_or_else(|| Error::limit("reference execution work exhausted"))?;
        Ok(())
    }
    fn cells(&self, amount: usize) -> Result<()> {
        if amount > self.limits.max_amplitudes {
            Err(Error::limit("reference execution amplitude limit exceeded"))
        } else {
            Ok(())
        }
    }
}

enum Op<'a> {
    Leaf(&'a Matrix),
    Sequence(Vec<usize>),
    Tensor(usize, usize),
    Repeat(usize, usize),
    Inverse(usize),
    Control(usize, bool),
    Permutation(Vec<usize>),
    Phase(usize, [f64; 2]),
}
struct Node<'a> {
    width: usize,
    op: Op<'a>,
}
struct Program<'a> {
    nodes: Vec<Node<'a>>,
    root: usize,
    inputs: Vec<usize>,
    outputs: Vec<usize>,
}
impl<'a> Program<'a> {
    fn compile(actual: &Value, checked: &'a Reconstructed) -> Result<Self> {
        let definitions = actual.field("definitions")?.array()?;
        let proofs = actual.field("proofs")?.array()?;
        let mut matrices = BTreeMap::new();
        for (proof_index, checked_leaf) in checked.leaves() {
            let proof = proofs
                .get(*proof_index)
                .ok_or_else(|| invalid("missing finite proof"))?;
            let implementation = index(proof.field("implementation")?)?;
            let definition = definitions
                .get(implementation)
                .ok_or_else(|| invalid("missing finite definition"))?;
            // Bind the retained matrix to the actual body, not the proof table's
            // position, requested meaning, or producer-supplied identity flags.
            if definition
                .field("body")?
                .field("program")?
                .text()?
                .as_bytes()
                != checked_leaf.leaf().payload()
                || super::boundary(definition.field("interface")?)?
                    != *checked_leaf.leaf().boundary()
            {
                return Err(invalid(
                    "finite matrix no longer matches its actual definition",
                ));
            }
            matrices.insert(implementation, checked_leaf.leaf().meaning());
        }
        let mut nodes = Vec::with_capacity(definitions.len());
        // The accepted artifact may retain non-root definitions. Rejecting an
        // unsupported one is explicit, and includes every zero-repeat child.
        for (i, definition) in definitions.iter().enumerate() {
            let header = definition.field("interface")?;
            let inputs = header.field("inputs")?;
            let outputs = header.field("outputs")?;
            quantum_only(inputs)?;
            quantum_only(outputs)?;
            let a = wires(inputs)?;
            let b = wires(outputs)?;
            if a.len() != b.len() || definition.field("effect")?.text()? != "unitary" {
                return Err(unsupported(
                    "pure execution requires width-preserving unitary definitions",
                ));
            }
            let body = definition.field("body")?;
            let child = |field| -> Result<usize> {
                let n = index(body.field(field)?)?;
                if n >= definitions.len() {
                    return Err(invalid("actual child index outside definition table"));
                }
                Ok(n)
            };
            let op = match body.field("tag")?.text()? {
                "leaf" => Op::Leaf(*matrices.get(&i).ok_or_else(|| {
                    unsupported("actual finite leaf lacks retained reconstruction")
                })?),
                "sequence" => Op::Sequence(
                    body.field("children")?
                        .array()?
                        .iter()
                        .map(index)
                        .collect::<Result<_>>()?,
                ),
                "tensor" => Op::Tensor(child("left")?, child("right")?),
                "repeat" => Op::Repeat(child("definition")?, index(body.field("count")?)?),
                "inverse" => Op::Inverse(child("definition")?),
                "control" => Op::Control(child("definition")?, body.field("polarity")?.boolean()?),
                "rewire" => Op::Permutation(permutation(
                    body.field("permutation")?
                        .field("axes")?
                        .array()?
                        .iter()
                        .map(index)
                        .collect::<Result<_>>()?,
                    a.len(),
                )?),
                "structural" => Op::Permutation(permutation(positions(&a, &b)?, a.len())?),
                "dyadic_phase" => {
                    let target = owner_axis(inputs, index(body.field("target")?)?)?;
                    let j = index(body.field("j")?)?;
                    let k = index(body.field("k")?)?;
                    let denominator = width_dimension(k)?;
                    let angle =
                        std::f64::consts::TAU * (j % denominator) as f64 / denominator as f64;
                    let (im, re) = angle.sin_cos();
                    Op::Phase(target, [re, im])
                }
                tag => {
                    return Err(unsupported(format!(
                        "reference execution does not support actual {tag} nodes"
                    )));
                }
            };
            nodes.push(Node { width: a.len(), op });
        }
        let root = index(actual.field("entry")?.field("implementation")?)?;
        let header = definitions
            .get(root)
            .ok_or_else(|| invalid("missing actual entry"))?
            .field("interface")?;
        Ok(Self {
            nodes,
            root,
            inputs: wires(header.field("inputs")?)?,
            outputs: wires(header.field("outputs")?)?,
        })
    }

    fn apply(&self, state: &mut Vec<[f64; 2]>, work: &mut Work) -> Result<()> {
        let mut scratch = zeroes(state.len())?;
        let mut stack = Vec::new();
        reserve_tasks(&mut stack, 1, work)?;
        stack.push(Task {
            node: self.root,
            offset: 0,
            mask: 0,
            value: 0,
            inverse: false,
            repetitions: 1,
        });
        while let Some(mut task) = stack.pop() {
            if task.repetitions == 0 {
                continue;
            }
            work.charge(1)?;
            task.repetitions -= 1;
            if task.repetitions != 0 {
                reserve_tasks(&mut stack, 1, work)?;
                stack.push(task);
            }
            task.repetitions = 1;
            let node = self
                .nodes
                .get(task.node)
                .ok_or_else(|| invalid("missing execution node"))?;
            let push = |stack: &mut Vec<Task>, node, offset, inverse| {
                stack.push(Task {
                    node,
                    offset,
                    inverse,
                    ..task
                })
            };
            match &node.op {
                Op::Sequence(children) => {
                    reserve_tasks(&mut stack, children.len(), work)?;
                    if task.inverse {
                        for child in children {
                            push(&mut stack, *child, task.offset, true);
                        }
                    } else {
                        for child in children.iter().rev() {
                            push(&mut stack, *child, task.offset, false);
                        }
                    }
                }
                Op::Tensor(left, right) => {
                    reserve_tasks(&mut stack, 2, work)?;
                    let left_width = self
                        .nodes
                        .get(*left)
                        .ok_or_else(|| invalid("missing tensor child"))?
                        .width;
                    let right_offset = task
                        .offset
                        .checked_add(left_width)
                        .ok_or_else(|| Error::limit("execution offset overflow"))?;
                    push(&mut stack, *right, right_offset, task.inverse);
                    push(&mut stack, *left, task.offset, task.inverse);
                }
                Op::Repeat(child, count) => {
                    if *count != 0 {
                        reserve_tasks(&mut stack, 1, work)?;
                        stack.push(Task {
                            node: *child,
                            repetitions: *count,
                            ..task
                        });
                    }
                }
                Op::Inverse(child) => {
                    reserve_tasks(&mut stack, 1, work)?;
                    push(&mut stack, *child, task.offset, !task.inverse);
                }
                Op::Control(child, polarity) => {
                    reserve_tasks(&mut stack, 1, work)?;
                    let bit = width_dimension(task.offset)?;
                    stack.push(Task {
                        node: *child,
                        offset: task.offset + 1,
                        mask: task.mask | bit,
                        value: if *polarity {
                            task.value | bit
                        } else {
                            task.value
                        },
                        ..task
                    });
                }
                Op::Permutation(map) => {
                    work.charge(state.len())?;
                    let local_mask = (width_dimension(node.width)? - 1) << task.offset;
                    for (i, amplitude) in state.iter().enumerate() {
                        let mut output = i;
                        if task.active(i) {
                            output &= !local_mask;
                            for (to, from) in map.iter().enumerate() {
                                let (to, from) = if task.inverse {
                                    (*from, to)
                                } else {
                                    (to, *from)
                                };
                                output |= ((i >> (task.offset + from)) & 1) << (task.offset + to);
                            }
                        }
                        scratch[output] = *amplitude;
                    }
                    std::mem::swap(state, &mut scratch);
                }
                Op::Phase(target, phase) => {
                    work.charge(state.len())?;
                    let phase = [phase[0], if task.inverse { -phase[1] } else { phase[1] }];
                    for (i, amplitude) in state.iter_mut().enumerate() {
                        if task.active(i) && i & width_dimension(task.offset + target)? != 0 {
                            *amplitude = multiply(*amplitude, phase);
                        }
                    }
                    finite(state)?;
                }
                Op::Leaf(matrix) => {
                    let dimension = width_dimension(node.width)?;
                    if matrix.rows() != dimension || matrix.cols() != dimension {
                        return Err(invalid(
                            "finite matrix dimension disagrees with actual node",
                        ));
                    }
                    work.charge(product(state.len(), dimension)?)?;
                    let mask = (dimension - 1) << task.offset;
                    for (output, result) in scratch.iter_mut().enumerate() {
                        if !task.active(output) {
                            *result = state[output];
                            continue;
                        }
                        let row = (output & mask) >> task.offset;
                        *result = [0.0, 0.0];
                        for col in 0..dimension {
                            let (r, c) = if task.inverse { (col, row) } else { (row, col) };
                            let [a, b, c, d] = matrix.entries()[r * dimension + c]
                                .dyadics()
                                .map(|(n, exponent)| n as f64 / 2_f64.powi(exponent as i32));
                            let re = a + b * std::f64::consts::SQRT_2;
                            let im = c + d * std::f64::consts::SQRT_2;
                            let term = multiply(
                                state[(output & !mask) | (col << task.offset)],
                                [re, if task.inverse { -im } else { im }],
                            );
                            result[0] += term[0];
                            result[1] += term[1];
                        }
                    }
                    finite(&scratch)?;
                    std::mem::swap(state, &mut scratch);
                }
            }
        }
        Ok(())
    }
}
#[derive(Clone, Copy)]
struct Task {
    node: usize,
    offset: usize,
    mask: usize,
    value: usize,
    inverse: bool,
    repetitions: usize,
}
// Each pending task requires at least one later charged node visit. Reserve
// its metadata only when that lower bound fits the remaining work budget.
fn reserve_tasks(stack: &mut Vec<Task>, additional: usize, work: &Work) -> Result<()> {
    if work
        .spent
        .checked_add(stack.len())
        .and_then(|n| n.checked_add(additional))
        .is_none_or(|n| n > work.limits.max_steps)
    {
        return Err(Error::limit(
            "pending execution tasks exceed remaining work",
        ));
    }
    stack
        .try_reserve_exact(additional)
        .map_err(|_| Error::limit("cannot allocate bounded execution tasks"))
}
impl Task {
    fn active(&self, basis: usize) -> bool {
        basis & self.mask == self.value
    }
}
fn multiply(a: [f64; 2], b: [f64; 2]) -> [f64; 2] {
    [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]]
}
fn input_check(input: &[[f64; 2]], width: usize, reference: usize, work: &Work) -> Result<()> {
    if reference == 0 {
        return Err(invalid("reference dimension must be positive"));
    }
    let cells = product(width_dimension(width)?, reference)?;
    if input.len() != cells {
        return Err(invalid("input coefficients have the wrong dimension"));
    }
    work.cells(product(cells, 2)?)?;
    finite(input)
}

fn instrument_input_side(actual: &Value) -> Result<&Value> {
    let preparation = actual.field("preparation")?;
    match preparation.field("initializations")?.array()?.first() {
        Some(first) => first.field("interface")?.field("inputs"),
        None => preparation.field("outputs"),
    }
}

fn norm_squared(values: &[[f64; 2]]) -> std::result::Result<f64, &'static str> {
    let mut sum = 0.0;
    for [re, im] in values {
        if !re.is_finite() || !im.is_finite() {
            return Err("nonfinite amplitude");
        }
        sum += re * re + im * im;
    }
    if sum.is_finite() {
        Ok(sum)
    } else {
        Err("squared norm is not representable as finite f64")
    }
}

fn norm_tolerance(steps: usize) -> f64 {
    // A numerical alarm, not a certified forward-error bound. Unused configured
    // work grants no tolerance; even enormous executed work cannot mask 1e-3.
    (1.0 / (1_u64 << 40) as f64 + 16.0 * f64::EPSILON * steps as f64)
        .min(1.0 / (1_u64 << 20) as f64)
}

fn branch_weights<E>(
    branches: &[Vec<[f64; 2]>],
    steps: usize,
) -> std::result::Result<(Vec<f64>, f64), SamplingError<E>> {
    let mut weights = Vec::new();
    weights
        .try_reserve_exact(branches.len())
        .map_err(|_| Error::limit("cannot allocate bounded branch weights"))?;
    let mut total = 0.0;
    for branch in branches {
        let weight = norm_squared(branch).map_err(SamplingError::Numerical)?;
        weights.push(weight);
        total += weight;
    }
    if !total.is_finite() || total <= 0.0 || (total - 1.0).abs() > norm_tolerance(steps) {
        return Err(SamplingError::Numerical(
            "complete branch norm differs from one",
        ));
    }
    Ok((weights, total))
}

fn choose_branch(weights: &[f64], total: f64, word: u64) -> usize {
    let unit = (word >> 11) as f64 * (1.0 / (1_u64 << 53) as f64);
    // Rounding the product must not select an empty interval after the last
    // positive branch. `total` is positive/finite and weights are nonnegative.
    let target = (unit * total).min(f64::from_bits(total.to_bits() - 1));
    let mut cumulative = 0.0;
    for (index, weight) in weights.iter().enumerate() {
        cumulative += weight;
        if target < cumulative {
            return index;
        }
    }
    // The caller computed total in this same order; no valid weight list can
    // reach here. Keep the failure explicit rather than inventing an outcome.
    weights.len()
}

impl CheckedRequest {
    /// Apply the retained actual circuit to finite unnormalized coefficients.
    /// No requested meaning is executed, and no execution result is evidence.
    pub fn execute(
        &self,
        input: &[[f64; 2]],
        reference_dimension: usize,
        limits: ExecutionLimits,
    ) -> Result<StateVector> {
        let actual = json::parse(self.reconstruction().payload())?;
        let program = Program::compile(&actual, self.reconstruction())?;
        let mut work = Work { limits, spent: 0 };
        input_check(input, program.inputs.len(), reference_dimension, &work)?;
        let mut amplitudes = zeroes(input.len())?;
        amplitudes.copy_from_slice(input);
        program.apply(&mut amplitudes, &mut work)?;
        Ok(StateVector {
            amplitudes,
            quantum_bits: program.outputs.len(),
            reference_dimension,
            steps: work.spent,
        })
    }
}

impl CheckedInstrument {
    /// Prepare actual fresh zero axes and retain all ordered measurement
    /// branches, including residual/reference coherence and global phase.
    pub fn execute(
        &self,
        input: &[[f64; 2]],
        reference_dimension: usize,
        limits: ExecutionLimits,
    ) -> Result<InstrumentBranches> {
        let actual = json::parse(self.reconstruction().payload())?;
        let program = Program::compile(actual.field("circuit")?, self.reconstruction())?;
        let preparation = actual.field("preparation")?;
        let initializations = preparation.field("initializations")?.array()?;
        let input_side = instrument_input_side(&actual)?;
        quantum_only(input_side)?;
        let input_axes = wires(input_side)?;
        let mut work = Work { limits, spent: 0 };
        input_check(input, input_axes.len(), reference_dimension, &work)?;
        let dimensions = width_dimension(program.inputs.len())?;
        let cells = product(dimensions, reference_dimension)?;
        work.cells(product(cells, 2)?)?;
        let input_positions = positions(&program.inputs, &input_axes)?;
        let mut fresh = Vec::new();
        for init in initializations {
            work.charge(1)?;
            let body = init.field("body")?;
            if body.field("tag")?.text()? != "init0" {
                return Err(unsupported("initialization must be actual init0"));
            }
            let side = init.field("interface")?.field("outputs")?;
            let axes = wires(side)?;
            fresh.push(axes[owner_axis(side, index(body.field("output")?)?)?]);
        }
        let mut expected_axes = input_axes.clone();
        expected_axes.extend(fresh);
        expected_axes.sort_unstable();
        let mut prepared_axes = program.inputs.clone();
        prepared_axes.sort_unstable();
        if expected_axes != prepared_axes {
            return Err(invalid(
                "actual preparation does not cover the circuit inputs",
            ));
        }
        work.charge(cells)?;
        let mut state = zeroes(cells)?;
        let input_dimension = width_dimension(input_axes.len())?;
        for (i, coefficient) in input.iter().enumerate() {
            let basis = i % input_dimension;
            let prepared = input_positions
                .iter()
                .enumerate()
                .fold(0, |out, (j, position)| {
                    out | (((basis >> j) & 1) << position)
                });
            state[(i / input_dimension) * dimensions + prepared] = *coefficient;
        }
        program.apply(&mut state, &mut work)?;
        let readout = actual.field("readout")?;
        let mut measured = BTreeMap::new();
        for measurement in readout.field("measurements")?.array()? {
            work.charge(1)?;
            let body = measurement.field("body")?;
            if body.field("tag")?.text()? != "observe_z" {
                return Err(unsupported("readout must be actual observe_z"));
            }
            let before = measurement.field("interface")?.field("inputs")?;
            let axes = wires(before)?;
            let axis = axes[owner_axis(before, index(body.field("input")?)?)?];
            measured.insert(index(body.field("output")?)?, axis);
        }
        let pack = readout.field("pack")?.array()?;
        let measured_axes = pack
            .iter()
            .map(|value| {
                measured
                    .get(&index(value)?)
                    .copied()
                    .ok_or_else(|| invalid("actual pack references an unmeasured value"))
            })
            .collect::<Result<Vec<_>>>()?;
        if pack.len() != measured.len() {
            return Err(unsupported("readout must retain every measured result"));
        }
        let residual_axes = wires(readout.field("outputs")?)?;
        let outcome_positions = positions(&program.outputs, &measured_axes)?;
        let residual_positions = positions(&program.outputs, &residual_axes)?;
        let outcome_count = width_dimension(pack.len())?;
        let residual_dimension = width_dimension(residual_axes.len())?;
        let branch_cells = product(residual_dimension, reference_dimension)?;
        if product(outcome_count, branch_cells)? != cells {
            return Err(invalid("readout axes do not partition the output state"));
        }
        work.charge(cells)?;
        let mut branches = Vec::new();
        branches
            .try_reserve_exact(outcome_count)
            .map_err(|_| Error::limit("cannot allocate readout branches"))?;
        for _ in 0..outcome_count {
            branches.push(zeroes(branch_cells)?);
        }
        for (i, coefficient) in state.into_iter().enumerate() {
            let select = |positions: &[usize]| {
                positions
                    .iter()
                    .enumerate()
                    .fold(0, |out, (j, position)| out | (((i >> position) & 1) << j))
            };
            let outcome = select(&outcome_positions);
            let residual = select(&residual_positions);
            branches[outcome][(i / dimensions) * residual_dimension + residual] = coefficient;
        }
        Ok(InstrumentBranches {
            branches,
            measured_bits: pack.len(),
            residual_quantum_bits: residual_axes.len(),
            reference_dimension,
            steps: work.spent,
        })
    }

    /// Explicitly normalize a finite positive-norm input, then execute each shot
    /// afresh from that same joint input/reference state. No collapsed state or
    /// cached branch execution is reused. The original norm is returned.
    ///
    /// On success, one RNG word is consumed per outcome (even deterministic
    /// outcomes); its high 53 bits select from the full actual branch weights.
    /// Uniform independent words are a caller premise. Complete output norm
    /// error must be at most min(2^-20, 2^-40 + 16*epsilon*executed_steps), after
    /// which probabilities and the selected conditional state are normalized.
    /// This numerical guard is not evidence or a certified error bound.
    ///
    /// `steps` includes fresh execution for every shot, norm scans, normalization
    /// and a full-outcome selection allowance. Zero/nonfinite/unrepresentable
    /// input norms, invalid output norms and exhausted limits are errors.
    pub fn sample_normalized_shots<R: RandomSource>(
        &self,
        input: &[[f64; 2]],
        reference_dimension: usize,
        shots: usize,
        random: &mut R,
        limits: SamplingLimits,
    ) -> std::result::Result<InstrumentSamples, SamplingError<R::Error>> {
        if shots == 0 {
            return Err(invalid("shot count must be positive").into());
        }
        if shots > limits.max_shots {
            return Err(Error::limit("sampling shot limit exceeded").into());
        }
        let actual = json::parse(self.reconstruction().payload())?;
        let input_side = instrument_input_side(&actual)?;
        quantum_only(input_side)?;
        let input_width = wires(input_side)?.len();
        let readout = actual.field("readout")?;
        let output_width = wires(readout.field("outputs")?)?.len();
        let measured_bits = readout.field("pack")?.array()?.len();
        let branch_cells = product(width_dimension(output_width)?, reference_dimension)?;
        let mut work = Work {
            limits: limits.execution,
            spent: 0,
        };
        input_check(input, input_width, reference_dimension, &work)?;
        let output_cells = product(shots, branch_cells)?;
        work.cells(
            input
                .len()
                .checked_add(output_cells)
                .ok_or_else(|| Error::limit("sampling retained output size overflow"))?,
        )?;
        work.charge(product(input.len(), 2)?)?;
        let input_norm = norm_squared(input).map_err(SamplingError::Numerical)?;
        if input_norm <= 0.0 {
            return Err(SamplingError::Numerical("input norm must be positive"));
        }
        let mut normalized = zeroes(input.len())?;
        let scale = input_norm.sqrt();
        for (to, from) in normalized.iter_mut().zip(input) {
            *to = [from[0] / scale, from[1] / scale];
        }
        let mut results = Vec::new();
        results
            .try_reserve_exact(shots)
            .map_err(|_| Error::limit("cannot allocate bounded shot results"))?;
        for shot in 0..shots {
            let retained = input
                .len()
                .checked_add(product(shot, branch_cells)?)
                .ok_or_else(|| Error::limit("sampling retained state overflow"))?;
            let available = ExecutionLimits {
                max_amplitudes: limits.execution.max_amplitudes - retained,
                max_steps: limits.execution.max_steps - work.spent,
            };
            let mut result = self.execute(&normalized, reference_dimension, available)?;
            work.charge(result.steps)?;
            if result.measured_bits != measured_bits || result.residual_quantum_bits != output_width
            {
                return Err(invalid("actual shot output shape changed").into());
            }
            let cells = product(result.branches.len(), branch_cells)?;
            work.cells(
                retained
                    .checked_add(cells)
                    .and_then(|n| n.checked_add(result.branches.len()))
                    .ok_or_else(|| Error::limit("sampling branch workspace overflow"))?,
            )?;
            work.charge(cells)?;
            work.charge(result.branches.len())?;
            // Charge before drawing; the selected branch is then normalized and
            // its norm independently scanned without additional allocation.
            work.charge(product(branch_cells, 2)?)?;
            let (weights, total) = branch_weights(&result.branches, result.steps)?;
            let word = random.next_u64().map_err(SamplingError::RandomSource)?;
            let outcome = choose_branch(&weights, total, word);
            let weight = weights.get(outcome).copied().filter(|w| *w > 0.0).ok_or(
                SamplingError::Numerical("selected branch has zero or invalid norm"),
            )?;
            let mut amplitudes = result.branches.swap_remove(outcome);
            let scale = weight.sqrt();
            for value in &mut amplitudes {
                value[0] /= scale;
                value[1] /= scale;
            }
            let norm = norm_squared(&amplitudes).map_err(SamplingError::Numerical)?;
            if (norm - 1.0).abs() > norm_tolerance(branch_cells) {
                return Err(SamplingError::Numerical(
                    "conditional branch norm differs from one",
                ));
            }
            results.push(InstrumentSample {
                outcome,
                probability: weight / total,
                amplitudes,
            });
        }
        Ok(InstrumentSamples {
            shots: results,
            measured_bits,
            residual_quantum_bits: output_width,
            reference_dimension,
            input_norm_squared: input_norm,
            steps: work.spent,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::contract::exact::Exact;

    fn limits() -> ExecutionLimits {
        ExecutionLimits {
            max_amplitudes: 1024,
            max_steps: 100_000,
        }
    }
    fn run(nodes: Vec<Node<'_>>, input: &[[f64; 2]]) -> (Vec<[f64; 2]>, usize) {
        let root = nodes.len() - 1;
        let width = nodes[root].width;
        let program = Program {
            nodes,
            root,
            inputs: (0..width).collect(),
            outputs: (0..width).collect(),
        };
        let mut work = Work {
            limits: limits(),
            spent: 0,
        };
        let mut state = input.to_vec();
        program.apply(&mut state, &mut work).unwrap();
        (state, work.spent)
    }
    fn near(actual: &[[f64; 2]], expected: &[[f64; 2]]) {
        assert_eq!(actual.len(), expected.len());
        for (a, b) in actual.iter().flatten().zip(expected.iter().flatten()) {
            assert!((a - b).abs() < 1e-12, "{actual:?} != {expected:?}");
        }
    }
    fn h() -> Matrix {
        let r = Exact::inv_sqrt2();
        Matrix::new(2, 2, vec![r, r, r, r.neg().unwrap()]).unwrap()
    }

    #[test]
    fn sampling_uses_full_branch_weights_and_never_selects_zero_branches() {
        let branches = vec![
            vec![[0.0, 0.0]],
            vec![[0.0, 0.6]],
            vec![[0.8, 0.0]],
            vec![[0.0, 0.0]],
        ];
        let (weights, total) = branch_weights::<()>(&branches, 0).unwrap();
        assert_eq!(choose_branch(&weights, total, 0), 1);
        assert_eq!(choose_branch(&weights, total, u64::MAX), 2);
        assert_eq!(choose_branch(&[0.0, 1.0, 0.0], 1.0, u64::MAX), 1);
        // A single full-outcome draw keeps both real and imaginary mass; there
        // is no phase removal or norm computed from only a marginal system.
        assert!((weights[1] - 0.36).abs() < 1e-15);
    }

    #[test]
    fn sampling_norm_guard_rejects_zero_nonfinite_and_excessive_drift() {
        for value in [0.0, f64::NAN, f64::INFINITY, 1.001] {
            assert!(branch_weights::<()>(&[vec![[value, 0.0]]], usize::MAX).is_err());
        }
        let small_drift = vec![vec![[1.0 + 2e-12, 0.0]]];
        assert!(branch_weights::<()>(&small_drift, 0).is_err());
        assert!(branch_weights::<()>(&small_drift, 12_000).is_ok());
        assert_eq!(norm_tolerance(usize::MAX), 1.0 / (1_u64 << 20) as f64);
    }

    #[test]
    fn sequence_adjoint_retains_complex_phase_and_reference() {
        let h = h();
        // U = S H. U† = H S†; unequal reference coefficients retain phase.
        let nodes = vec![
            Node {
                width: 1,
                op: Op::Leaf(&h),
            },
            Node {
                width: 1,
                op: Op::Phase(0, [0.0, 1.0]),
            },
            Node {
                width: 1,
                op: Op::Sequence(vec![0, 1]),
            },
            Node {
                width: 1,
                op: Op::Inverse(2),
            },
        ];
        let (actual, _) = run(nodes, &[[0.0, 0.0], [1.0, 0.0], [0.0, 2.0], [0.0, 0.0]]);
        let r = std::f64::consts::FRAC_1_SQRT_2;
        near(
            &actual,
            &[[0.0, -r], [0.0, r], [0.0, 2.0 * r], [0.0, 2.0 * r]],
        );
    }

    #[test]
    fn tensor_places_left_axes_first_and_control_keeps_global_phase() {
        let negative = Matrix::new(
            2,
            2,
            vec![
                Exact::integer(-1),
                Exact::zero(),
                Exact::zero(),
                Exact::integer(-1),
            ],
        )
        .unwrap();
        let h = h();
        let (actual, _) = run(
            vec![
                Node {
                    width: 1,
                    op: Op::Leaf(&h),
                },
                Node {
                    width: 1,
                    op: Op::Leaf(&negative),
                },
                Node {
                    width: 2,
                    op: Op::Control(1, true),
                },
                Node {
                    width: 3,
                    op: Op::Tensor(0, 2),
                },
            ],
            &[
                [0.0, 0.0],
                [0.0, 0.0],
                [1.0, 0.0],
                [0.0, 0.0],
                [0.0, 0.0],
                [0.0, 0.0],
                [0.0, 0.0],
                [0.0, 0.0],
            ],
        );
        let r = -std::f64::consts::FRAC_1_SQRT_2;
        near(
            &actual,
            &[
                [0.0, 0.0],
                [0.0, 0.0],
                [r, 0.0],
                [r, 0.0],
                [0.0, 0.0],
                [0.0, 0.0],
                [0.0, 0.0],
                [0.0, 0.0],
            ],
        );
    }

    #[test]
    fn negative_control_retains_a_zero_qubit_leaf_scalar() {
        let scalar = Matrix::new(1, 1, vec![Exact::integer(-1)]).unwrap();
        let (actual, _) = run(
            vec![
                Node {
                    width: 0,
                    op: Op::Leaf(&scalar),
                },
                Node {
                    width: 1,
                    op: Op::Control(0, false),
                },
            ],
            &[[2.0, 3.0], [4.0, 5.0]],
        );
        assert_eq!(actual, [[-2.0, -3.0], [4.0, 5.0]]);
    }

    #[test]
    fn permutation_direction_inverse_and_zero_width() {
        let input: Vec<_> = (0..8).map(|i| [i as f64, -(i as f64)]).collect();
        let (forward, _) = run(
            vec![Node {
                width: 3,
                op: Op::Permutation(vec![2, 0, 1]),
            }],
            &input,
        );
        for (i, value) in input.iter().enumerate() {
            assert_eq!(
                forward[((i >> 2) & 1) | ((i & 1) << 1) | (((i >> 1) & 1) << 2)],
                *value
            );
        }
        let (back, _) = run(
            vec![
                Node {
                    width: 3,
                    op: Op::Permutation(vec![2, 0, 1]),
                },
                Node {
                    width: 3,
                    op: Op::Inverse(0),
                },
            ],
            &forward,
        );
        assert_eq!(back, input);
        let (empty, _) = run(
            vec![Node {
                width: 0,
                op: Op::Permutation(vec![]),
            }],
            &[[2.0, -3.0]],
        );
        assert_eq!(empty, [[2.0, -3.0]]);
    }

    #[test]
    fn repeats_spend_actual_work_even_under_inactive_control() {
        for count in [0, 1, 4, 17] {
            let nodes = vec![
                Node {
                    width: 1,
                    op: Op::Phase(0, [0.0, 1.0]),
                },
                Node {
                    width: 1,
                    op: Op::Repeat(0, count),
                },
                Node {
                    width: 2,
                    op: Op::Control(1, true),
                },
            ];
            let (actual, steps) = run(nodes, &[[1.0, 0.0], [0.0, 0.0], [0.0, 0.0], [0.0, 0.0]]);
            assert_eq!(actual[0], [1.0, 0.0]);
            assert_eq!(steps, 2 + count * 5);
        }
        let p = Program {
            nodes: vec![
                Node {
                    width: 1,
                    op: Op::Phase(0, [0.0, 1.0]),
                },
                Node {
                    width: 1,
                    op: Op::Repeat(0, usize::MAX),
                },
            ],
            root: 1,
            inputs: vec![0],
            outputs: vec![0],
        };
        let mut work = Work {
            limits: ExecutionLimits {
                max_steps: 10,
                ..limits()
            },
            spent: 0,
        };
        assert_eq!(
            p.apply(&mut vec![[0.0, 0.0]; 2], &mut work)
                .unwrap_err()
                .code,
            "limit"
        );
    }

    #[test]
    fn pending_metadata_is_bounded_before_wide_sequence_enqueue() {
        let program = Program {
            nodes: vec![
                Node {
                    width: 0,
                    op: Op::Permutation(vec![]),
                },
                Node {
                    width: 0,
                    op: Op::Sequence(vec![0; 10_000]),
                },
            ],
            root: 1,
            inputs: vec![],
            outputs: vec![],
        };
        let mut work = Work {
            limits: ExecutionLimits {
                max_steps: 2,
                ..limits()
            },
            spent: 0,
        };
        assert_eq!(
            program
                .apply(&mut vec![[1.0, 0.0]], &mut work)
                .unwrap_err()
                .code,
            "limit"
        );
        assert_eq!(work.spent, 1);
        let mut tasks = Vec::new();
        assert_eq!(
            reserve_tasks(&mut tasks, usize::MAX, &work)
                .unwrap_err()
                .code,
            "limit"
        );
        assert_eq!(tasks.capacity(), 0);
    }

    #[test]
    fn capability_scan_rejects_unsupported_zero_repeat_children_and_classical_inputs() {
        // Capability-only fixtures, not values returned by a native check.
        // No fake report can enter the public execution API outside this module.
        let report = Reconstructed {
            native_exact_work: 0,
            payload: std::sync::Arc::from([]),
            leaves: vec![],
            structural_work: 0,
            exact_work: 0,
        };
        let side = r#"{"quantum":[{"owner":0,"basis":[{"tag":"bit"}],"axes":[9]}],"classical":[]}"#;
        let header = format!(r#"{{"inputs":{side},"outputs":{side}}}"#);
        let input = format!(
            r#"{{"definitions":[{{"interface":{header},"effect":"unitary","body":{{"tag":"computed"}}}},{{"interface":{header},"effect":"unitary","body":{{"tag":"repeat","count":0,"definition":0}}}}],"proofs":[],"entry":{{"implementation":1}}}}"#
        );
        let actual = json::parse(input.as_bytes()).unwrap();
        assert!(matches!(Program::compile(&actual, &report), Err(e) if e.code == "unsupported"));
        let input = input.replace(
            r#""classical":[]"#,
            r#""classical":[{"value":20,"basis":[{"tag":"bit"}]}]"#,
        );
        let actual = json::parse(input.as_bytes()).unwrap();
        assert!(matches!(Program::compile(&actual, &report), Err(e) if e.code == "unsupported"));
    }

    #[test]
    fn explicit_limits_dimensions_and_numeric_overflow() {
        let work = Work {
            limits: limits(),
            spent: 0,
        };
        assert_eq!(
            input_check(&[[1.0, 0.0]], 0, 0, &work).unwrap_err().code,
            "execution"
        );
        assert_eq!(
            input_check(&[[1.0, 0.0]], 1, 1, &work).unwrap_err().code,
            "execution"
        );
        for x in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            assert_eq!(
                input_check(&[[x, 0.0]], 0, 1, &work).unwrap_err().code,
                "execution"
            );
        }
        assert_eq!(
            input_check(&[[1.0, 0.0]], usize::MAX, 1, &work)
                .unwrap_err()
                .code,
            "limit"
        );
        assert_eq!(
            input_check(&[[1.0, 0.0]], 1, usize::MAX, &work)
                .unwrap_err()
                .code,
            "limit"
        );
        let work = Work {
            limits: ExecutionLimits {
                max_amplitudes: 3,
                ..limits()
            },
            spent: 0,
        };
        assert_eq!(
            input_check(&[[1.0, 0.0]; 2], 1, 1, &work).unwrap_err().code,
            "limit"
        );
        let h = h();
        let p = Program {
            nodes: vec![Node {
                width: 1,
                op: Op::Leaf(&h),
            }],
            root: 0,
            inputs: vec![0],
            outputs: vec![0],
        };
        let mut work = Work {
            limits: limits(),
            spent: 0,
        };
        assert_eq!(
            p.apply(&mut vec![[f64::MAX, 0.0]; 2], &mut work)
                .unwrap_err()
                .code,
            "execution"
        );
    }
}
