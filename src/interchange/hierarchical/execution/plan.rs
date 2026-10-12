//! Owned exact execution plans; construction is untrusted materialization.
//! Numerical execution reads these same immutable nodes, without recompiling JSON.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;

/// A retained result may explicitly lack execution support. Such a failure
/// cannot change the native inspection decision or become a different plan.
#[derive(Debug)]
pub(in crate::interchange::hierarchical) struct Plan {
    inner: Executable,
}

#[derive(Debug)]
enum Executable {
    Pure(Program),
    Instrument(InstrumentPlan),
}

#[derive(Debug)]
pub(super) struct InstrumentPlan {
    pub(super) program: Program,
    pub(super) input_axes: Vec<usize>,
    pub(super) fresh_axes: Vec<usize>,
    pub(super) input_positions: Vec<usize>,
    pub(super) measurements: Vec<(usize, usize)>,
    pub(super) pack: Vec<usize>,
    pub(super) outcome_positions: Vec<usize>,
    pub(super) residual_axes: Vec<usize>,
    pub(super) residual_positions: Vec<usize>,
}

impl Plan {
    pub(in crate::interchange::hierarchical) fn retained(checked: &Reconstructed) -> Result<Self> {
        let actual = json::parse(checked.payload())?;
        let instrument = actual.field("format")?.text()? == "qleisli.instrument-ir";
        Self::compile(&actual, instrument, |circuit| {
            retained_matrices(circuit, checked)
        })
    }

    pub(in crate::interchange::hierarchical) fn native(checked: &NativeChecked) -> Result<Self> {
        let actual = json::parse(checked.payload())?;
        Self::compile(&actual, checked.instrument, |circuit| {
            native_matrices(circuit, checked)
        })
    }

    fn compile(
        actual: &Value,
        instrument: bool,
        matrices: impl FnOnce(&Value) -> Result<BTreeMap<usize, Matrix>>,
    ) -> Result<Self> {
        let circuit = if instrument {
            actual.field("circuit")?
        } else {
            actual
        };
        let program = Program::compile(circuit, matrices(circuit)?)?;
        let inner = if instrument {
            Executable::Instrument(InstrumentPlan::compile(actual, program)?)
        } else {
            Executable::Pure(program)
        };
        Ok(Self { inner })
    }

    pub(super) fn pure(&self) -> Result<&Program> {
        match &self.inner {
            Executable::Pure(program) => Ok(program),
            Executable::Instrument(_) => Err(unsupported(
                "instrument report requires instrument execution",
            )),
        }
    }

    pub(super) fn instrument(&self) -> Result<&InstrumentPlan> {
        match &self.inner {
            Executable::Instrument(plan) => Ok(plan),
            Executable::Pure(_) => Err(unsupported("pure report has no checked instrument")),
        }
    }
}

impl InstrumentPlan {
    fn compile(actual: &Value, program: Program) -> Result<Self> {
        let preparation = actual.field("preparation")?;
        let initializations = preparation.field("initializations")?.array()?;
        let input_side = instrument_input_side(actual)?;
        quantum_only(input_side)?;
        let input_axes = wires(input_side)?;
        let input_positions = positions(&program.inputs, &input_axes)?;
        let mut fresh_axes = Vec::new();
        for init in initializations {
            let body = init.field("body")?;
            if body.field("tag")?.text()? != "init0" {
                return Err(unsupported("initialization must be actual init0"));
            }
            let side = init.field("interface")?.field("outputs")?;
            let axes = wires(side)?;
            fresh_axes.push(axes[owner_axis(side, index(body.field("output")?)?)?]);
        }
        let mut expected_axes = input_axes.clone();
        expected_axes.extend(&fresh_axes);
        expected_axes.sort_unstable();
        let mut prepared_axes = program.inputs.clone();
        prepared_axes.sort_unstable();
        if expected_axes != prepared_axes {
            return Err(invalid(
                "actual preparation does not cover the circuit inputs",
            ));
        }

        let readout = actual.field("readout")?;
        let mut measurements = Vec::new();
        let mut measured = BTreeMap::new();
        for measurement in readout.field("measurements")?.array()? {
            let body = measurement.field("body")?;
            if body.field("tag")?.text()? != "observe_z" {
                return Err(unsupported("readout must be actual observe_z"));
            }
            let before = measurement.field("interface")?.field("inputs")?;
            let axes = wires(before)?;
            let axis = axes[owner_axis(before, index(body.field("input")?)?)?];
            let value = index(body.field("output")?)?;
            measurements.push((value, axis));
            measured.insert(value, axis);
        }
        let pack = readout
            .field("pack")?
            .array()?
            .iter()
            .map(index)
            .collect::<Result<Vec<_>>>()?;
        let measured_axes = pack
            .iter()
            .map(|value| {
                measured
                    .get(value)
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
        if product(outcome_count, residual_dimension)? != width_dimension(program.inputs.len())? {
            return Err(invalid("readout axes do not partition the output state"));
        }
        Ok(Self {
            program,
            input_axes,
            fresh_axes,
            input_positions,
            measurements,
            pack,
            outcome_positions,
            residual_axes,
            residual_positions,
        })
    }
}

#[derive(Debug)]
pub(super) enum Op {
    Leaf(Matrix),
    Sequence(Vec<usize>),
    Tensor(usize, usize),
    Repeat(usize, usize),
    Inverse(usize),
    Control(usize, bool),
    Permutation(Vec<usize>),
    Phase { target: usize, j: usize, k: usize },
}
#[derive(Debug)]
pub(super) struct Node {
    pub(super) width: usize,
    pub(super) op: Op,
}
#[derive(Debug)]
pub(super) struct Program {
    pub(super) nodes: Vec<Node>,
    pub(super) root: usize,
    pub(super) inputs: Vec<usize>,
    pub(super) outputs: Vec<usize>,
}
impl Program {
    pub(super) fn compile(actual: &Value, mut matrices: BTreeMap<usize, Matrix>) -> Result<Self> {
        let definitions = actual.field("definitions")?.array()?;
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
                "leaf" => Op::Leaf(matrices.remove(&i).ok_or_else(|| {
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
                    width_dimension(k)?;
                    Op::Phase { target, j, k }
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
}

#[cfg(test)]
mod tests;
