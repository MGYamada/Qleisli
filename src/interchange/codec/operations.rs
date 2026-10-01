//! Explicit field maps for raw operations and circuit actions.
use super::{Codec, Decoder, Encoder, Error, Result, Value};
use crate::ir::{CircuitAction, ProtectedUse, RawOp, UnitaryStep};

impl Codec for RawOp {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        c.charge(1)?;
        match self {
            Self::CertifiedCompute {
                source,
                source_out,
                ancilla_wires,
                function,
                use_steps,
                logical_steps,
            } => Ok(Value::object([
                ("tag", Value::String("certified_compute".into())),
                ("source", source.write(c)?),
                ("source_out", source_out.write(c)?),
                ("ancilla_wires", ancilla_wires.write(c)?),
                ("function", function.write(c)?),
                ("use_steps", use_steps.write(c)?),
                ("logical_steps", logical_steps.write(c)?),
            ])),
            Self::ApplyUnitary {
                input,
                output,
                steps,
            } => Ok(Value::object([
                ("tag", Value::String("apply_unitary".into())),
                ("input", input.write(c)?),
                ("output", output.write(c)?),
                ("steps", steps.write(c)?),
            ])),
            Self::Init0 { output, wire } => Ok(Value::object([
                ("tag", Value::String("init0".into())),
                ("output", output.write(c)?),
                ("wire", wire.write(c)?),
            ])),
            Self::Gate {
                gate,
                input,
                output,
            } => Ok(Value::object([
                ("tag", Value::String("gate".into())),
                ("gate", gate.write(c)?),
                ("input", input.write(c)?),
                ("output", output.write(c)?),
            ])),
            Self::Cnot {
                control,
                target,
                control_out,
                target_out,
            } => Ok(Value::object([
                ("tag", Value::String("cnot".into())),
                ("control", control.write(c)?),
                ("target", target.write(c)?),
                ("control_out", control_out.write(c)?),
                ("target_out", target_out.write(c)?),
            ])),
            Self::Toffoli {
                control_a,
                control_b,
                target,
                control_a_out,
                control_b_out,
                target_out,
            } => Ok(Value::object([
                ("tag", Value::String("toffoli".into())),
                ("control_a", control_a.write(c)?),
                ("control_b", control_b.write(c)?),
                ("target", target.write(c)?),
                ("control_a_out", control_a_out.write(c)?),
                ("control_b_out", control_b_out.write(c)?),
                ("target_out", target_out.write(c)?),
            ])),
            Self::QuantumIf {
                control,
                target,
                control_out,
                target_out,
                zero_ops,
                one_ops,
            } => Ok(Value::object([
                ("tag", Value::String("quantum_if".into())),
                ("control", control.write(c)?),
                ("target", target.write(c)?),
                ("control_out", control_out.write(c)?),
                ("target_out", target_out.write(c)?),
                ("zero_ops", zero_ops.write(c)?),
                ("one_ops", one_ops.write(c)?),
            ])),
            Self::Split {
                input,
                left,
                right,
                left_bits,
            } => Ok(Value::object([
                ("tag", Value::String("split".into())),
                ("input", input.write(c)?),
                ("left", left.write(c)?),
                ("right", right.write(c)?),
                ("left_bits", left_bits.write(c)?),
            ])),
            Self::Join {
                left,
                right,
                output,
            } => Ok(Value::object([
                ("tag", Value::String("join".into())),
                ("left", left.write(c)?),
                ("right", right.write(c)?),
                ("output", output.write(c)?),
            ])),
            Self::LiftBasis {
                input,
                output,
                output_wires,
                table,
            } => Ok(Value::object([
                ("tag", Value::String("lift_basis".into())),
                ("input", input.write(c)?),
                ("output", output.write(c)?),
                ("output_wires", output_wires.write(c)?),
                ("table", table.write(c)?),
            ])),
            Self::MeasureZ { input, output } => Ok(Value::object([
                ("tag", Value::String("measure_z".into())),
                ("input", input.write(c)?),
                ("output", output.write(c)?),
            ])),
            Self::Reset {
                input,
                output,
                fresh_wire,
            } => Ok(Value::object([
                ("tag", Value::String("reset".into())),
                ("input", input.write(c)?),
                ("output", output.write(c)?),
                ("fresh_wire", fresh_wire.write(c)?),
            ])),
            Self::Discard { input } => Ok(Value::object([
                ("tag", Value::String("discard".into())),
                ("input", input.write(c)?),
            ])),
            Self::ClassicalConst { value, output } => Ok(Value::object([
                ("tag", Value::String("classical_const".into())),
                ("value", value.write(c)?),
                ("output", output.write(c)?),
            ])),
            Self::ClassicalNot { input, output } => Ok(Value::object([
                ("tag", Value::String("classical_not".into())),
                ("input", input.write(c)?),
                ("output", output.write(c)?),
            ])),
            Self::ClassicalXor {
                left,
                right,
                output,
            } => Ok(Value::object([
                ("tag", Value::String("classical_xor".into())),
                ("left", left.write(c)?),
                ("right", right.write(c)?),
                ("output", output.write(c)?),
            ])),
            Self::ClassicalAnd {
                left,
                right,
                output,
            } => Ok(Value::object([
                ("tag", Value::String("classical_and".into())),
                ("left", left.write(c)?),
                ("right", right.write(c)?),
                ("output", output.write(c)?),
            ])),
            Self::ClassicalBranch {
                condition,
                then_ops,
                else_ops,
                quantum_phis,
                classical_phis,
            } => Ok(Value::object([
                ("tag", Value::String("classical_branch".into())),
                ("condition", condition.write(c)?),
                ("then_ops", then_ops.write(c)?),
                ("else_ops", else_ops.write(c)?),
                ("quantum_phis", quantum_phis.write(c)?),
                ("classical_phis", classical_phis.write(c)?),
            ])),
            Self::ComputeUseUncompute {
                source,
                source_out,
                targets,
                ancilla_wires,
                function,
                use_ops,
            } => Ok(Value::object([
                ("tag", Value::String("compute_use_uncompute".into())),
                ("source", source.write(c)?),
                ("source_out", source_out.write(c)?),
                ("targets", targets.write(c)?),
                ("ancilla_wires", ancilla_wires.write(c)?),
                ("function", function.write(c)?),
                ("use_ops", use_ops.write(c)?),
            ])),
        }
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        match v.field("tag")?.text()? {
            "certified_compute" => {
                v.fields(&[
                    "tag",
                    "source",
                    "source_out",
                    "ancilla_wires",
                    "function",
                    "use_steps",
                    "logical_steps",
                ])?;
                Ok(Self::CertifiedCompute {
                    source: Codec::read(v.field("source")?, c)?,
                    source_out: Codec::read(v.field("source_out")?, c)?,
                    ancilla_wires: Codec::read(v.field("ancilla_wires")?, c)?,
                    function: Codec::read(v.field("function")?, c)?,
                    use_steps: Codec::read(v.field("use_steps")?, c)?,
                    logical_steps: Codec::read(v.field("logical_steps")?, c)?,
                })
            }
            "apply_unitary" => {
                v.fields(&["tag", "input", "output", "steps"])?;
                Ok(Self::ApplyUnitary {
                    input: Codec::read(v.field("input")?, c)?,
                    output: Codec::read(v.field("output")?, c)?,
                    steps: Codec::read(v.field("steps")?, c)?,
                })
            }
            "init0" => {
                v.fields(&["tag", "output", "wire"])?;
                Ok(Self::Init0 {
                    output: Codec::read(v.field("output")?, c)?,
                    wire: Codec::read(v.field("wire")?, c)?,
                })
            }
            "gate" => {
                v.fields(&["tag", "gate", "input", "output"])?;
                Ok(Self::Gate {
                    gate: Codec::read(v.field("gate")?, c)?,
                    input: Codec::read(v.field("input")?, c)?,
                    output: Codec::read(v.field("output")?, c)?,
                })
            }
            "cnot" => {
                v.fields(&["tag", "control", "target", "control_out", "target_out"])?;
                Ok(Self::Cnot {
                    control: Codec::read(v.field("control")?, c)?,
                    target: Codec::read(v.field("target")?, c)?,
                    control_out: Codec::read(v.field("control_out")?, c)?,
                    target_out: Codec::read(v.field("target_out")?, c)?,
                })
            }
            "toffoli" => {
                v.fields(&[
                    "tag",
                    "control_a",
                    "control_b",
                    "target",
                    "control_a_out",
                    "control_b_out",
                    "target_out",
                ])?;
                Ok(Self::Toffoli {
                    control_a: Codec::read(v.field("control_a")?, c)?,
                    control_b: Codec::read(v.field("control_b")?, c)?,
                    target: Codec::read(v.field("target")?, c)?,
                    control_a_out: Codec::read(v.field("control_a_out")?, c)?,
                    control_b_out: Codec::read(v.field("control_b_out")?, c)?,
                    target_out: Codec::read(v.field("target_out")?, c)?,
                })
            }
            "quantum_if" => {
                v.fields(&[
                    "tag",
                    "control",
                    "target",
                    "control_out",
                    "target_out",
                    "zero_ops",
                    "one_ops",
                ])?;
                Ok(Self::QuantumIf {
                    control: Codec::read(v.field("control")?, c)?,
                    target: Codec::read(v.field("target")?, c)?,
                    control_out: Codec::read(v.field("control_out")?, c)?,
                    target_out: Codec::read(v.field("target_out")?, c)?,
                    zero_ops: Codec::read(v.field("zero_ops")?, c)?,
                    one_ops: Codec::read(v.field("one_ops")?, c)?,
                })
            }
            "split" => {
                v.fields(&["tag", "input", "left", "right", "left_bits"])?;
                Ok(Self::Split {
                    input: Codec::read(v.field("input")?, c)?,
                    left: Codec::read(v.field("left")?, c)?,
                    right: Codec::read(v.field("right")?, c)?,
                    left_bits: Codec::read(v.field("left_bits")?, c)?,
                })
            }
            "join" => {
                v.fields(&["tag", "left", "right", "output"])?;
                Ok(Self::Join {
                    left: Codec::read(v.field("left")?, c)?,
                    right: Codec::read(v.field("right")?, c)?,
                    output: Codec::read(v.field("output")?, c)?,
                })
            }
            "lift_basis" => {
                v.fields(&["tag", "input", "output", "output_wires", "table"])?;
                Ok(Self::LiftBasis {
                    input: Codec::read(v.field("input")?, c)?,
                    output: Codec::read(v.field("output")?, c)?,
                    output_wires: Codec::read(v.field("output_wires")?, c)?,
                    table: Codec::read(v.field("table")?, c)?,
                })
            }
            "measure_z" => {
                v.fields(&["tag", "input", "output"])?;
                Ok(Self::MeasureZ {
                    input: Codec::read(v.field("input")?, c)?,
                    output: Codec::read(v.field("output")?, c)?,
                })
            }
            "reset" => {
                v.fields(&["tag", "input", "output", "fresh_wire"])?;
                Ok(Self::Reset {
                    input: Codec::read(v.field("input")?, c)?,
                    output: Codec::read(v.field("output")?, c)?,
                    fresh_wire: Codec::read(v.field("fresh_wire")?, c)?,
                })
            }
            "discard" => {
                v.fields(&["tag", "input"])?;
                Ok(Self::Discard {
                    input: Codec::read(v.field("input")?, c)?,
                })
            }
            "classical_const" => {
                v.fields(&["tag", "value", "output"])?;
                Ok(Self::ClassicalConst {
                    value: Codec::read(v.field("value")?, c)?,
                    output: Codec::read(v.field("output")?, c)?,
                })
            }
            "classical_not" => {
                v.fields(&["tag", "input", "output"])?;
                Ok(Self::ClassicalNot {
                    input: Codec::read(v.field("input")?, c)?,
                    output: Codec::read(v.field("output")?, c)?,
                })
            }
            "classical_xor" => {
                v.fields(&["tag", "left", "right", "output"])?;
                Ok(Self::ClassicalXor {
                    left: Codec::read(v.field("left")?, c)?,
                    right: Codec::read(v.field("right")?, c)?,
                    output: Codec::read(v.field("output")?, c)?,
                })
            }
            "classical_and" => {
                v.fields(&["tag", "left", "right", "output"])?;
                Ok(Self::ClassicalAnd {
                    left: Codec::read(v.field("left")?, c)?,
                    right: Codec::read(v.field("right")?, c)?,
                    output: Codec::read(v.field("output")?, c)?,
                })
            }
            "classical_branch" => {
                v.fields(&[
                    "tag",
                    "condition",
                    "then_ops",
                    "else_ops",
                    "quantum_phis",
                    "classical_phis",
                ])?;
                Ok(Self::ClassicalBranch {
                    condition: Codec::read(v.field("condition")?, c)?,
                    then_ops: Codec::read(v.field("then_ops")?, c)?,
                    else_ops: Codec::read(v.field("else_ops")?, c)?,
                    quantum_phis: Codec::read(v.field("quantum_phis")?, c)?,
                    classical_phis: Codec::read(v.field("classical_phis")?, c)?,
                })
            }
            "compute_use_uncompute" => {
                v.fields(&[
                    "tag",
                    "source",
                    "source_out",
                    "targets",
                    "ancilla_wires",
                    "function",
                    "use_ops",
                ])?;
                Ok(Self::ComputeUseUncompute {
                    source: Codec::read(v.field("source")?, c)?,
                    source_out: Codec::read(v.field("source_out")?, c)?,
                    targets: Codec::read(v.field("targets")?, c)?,
                    ancilla_wires: Codec::read(v.field("ancilla_wires")?, c)?,
                    function: Codec::read(v.field("function")?, c)?,
                    use_ops: Codec::read(v.field("use_ops")?, c)?,
                })
            }
            _ => Err(Error::format("unknown node tag")),
        }
    }
}
impl Codec for CircuitAction {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        c.charge(1)?;
        match self {
            Self::Contract {
                indices,
                evidence,
                adjoint,
            } => Ok(Value::object([
                ("tag", Value::String("contract".into())),
                ("indices", indices.write(c)?),
                ("evidence", evidence.write(c)?),
                ("adjoint", adjoint.write(c)?),
            ])),
            Self::Hadamard { target } => Ok(Value::object([
                ("tag", Value::String("hadamard".into())),
                ("target", target.write(c)?),
            ])),
            Self::Monomial {
                indices,
                permutation,
                phases,
            } => Ok(Value::object([
                ("tag", Value::String("monomial".into())),
                ("indices", indices.write(c)?),
                ("permutation", permutation.write(c)?),
                ("phases", phases.write(c)?),
            ])),
        }
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        match v.field("tag")?.text()? {
            "contract" => {
                v.fields(&["tag", "indices", "evidence", "adjoint"])?;
                Ok(Self::Contract {
                    indices: Codec::read(v.field("indices")?, c)?,
                    evidence: Codec::read(v.field("evidence")?, c)?,
                    adjoint: Codec::read(v.field("adjoint")?, c)?,
                })
            }
            "hadamard" => {
                v.fields(&["tag", "target"])?;
                Ok(Self::Hadamard {
                    target: Codec::read(v.field("target")?, c)?,
                })
            }
            "monomial" => {
                v.fields(&["tag", "indices", "permutation", "phases"])?;
                Ok(Self::Monomial {
                    indices: Codec::read(v.field("indices")?, c)?,
                    permutation: Codec::read(v.field("permutation")?, c)?,
                    phases: Codec::read(v.field("phases")?, c)?,
                })
            }
            _ => Err(Error::format("unknown node tag")),
        }
    }
}
impl Codec for ProtectedUse {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        c.charge(1)?;
        match self {
            Self::ProtectedGate { bit, gate } => Ok(Value::object([
                ("tag", Value::String("protected_gate".into())),
                ("bit", bit.write(c)?),
                ("gate", gate.write(c)?),
            ])),
            Self::ControlledTargetGate {
                controls,
                target_index,
                gate,
            } => Ok(Value::object([
                ("tag", Value::String("controlled_target_gate".into())),
                ("controls", controls.write(c)?),
                ("target_index", target_index.write(c)?),
                ("gate", gate.write(c)?),
            ])),
            Self::ControlledPhase { controls, phase } => Ok(Value::object([
                ("tag", Value::String("controlled_phase".into())),
                ("controls", controls.write(c)?),
                ("phase", phase.write(c)?),
            ])),
        }
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        match v.field("tag")?.text()? {
            "protected_gate" => {
                v.fields(&["tag", "bit", "gate"])?;
                Ok(Self::ProtectedGate {
                    bit: Codec::read(v.field("bit")?, c)?,
                    gate: Codec::read(v.field("gate")?, c)?,
                })
            }
            "controlled_target_gate" => {
                v.fields(&["tag", "controls", "target_index", "gate"])?;
                Ok(Self::ControlledTargetGate {
                    controls: Codec::read(v.field("controls")?, c)?,
                    target_index: Codec::read(v.field("target_index")?, c)?,
                    gate: Codec::read(v.field("gate")?, c)?,
                })
            }
            "controlled_phase" => {
                v.fields(&["tag", "controls", "phase"])?;
                Ok(Self::ControlledPhase {
                    controls: Codec::read(v.field("controls")?, c)?,
                    phase: Codec::read(v.field("phase")?, c)?,
                })
            }
            _ => Err(Error::format("unknown node tag")),
        }
    }
}
impl Codec for UnitaryStep {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        c.charge(1)?;
        match self {
            Self::Gate { gate, target_index } => Ok(Value::object([
                ("tag", Value::String("gate".into())),
                ("gate", gate.write(c)?),
                ("target_index", target_index.write(c)?),
            ])),
            Self::Cnot {
                control_index,
                target_index,
            } => Ok(Value::object([
                ("tag", Value::String("cnot".into())),
                ("control_index", control_index.write(c)?),
                ("target_index", target_index.write(c)?),
            ])),
            Self::Toffoli {
                control_a_index,
                control_b_index,
                target_index,
            } => Ok(Value::object([
                ("tag", Value::String("toffoli".into())),
                ("control_a_index", control_a_index.write(c)?),
                ("control_b_index", control_b_index.write(c)?),
                ("target_index", target_index.write(c)?),
            ])),
            Self::ScalarPhase(phase) => Ok(Value::object([
                ("tag", Value::String("scalar_phase".into())),
                ("phase", phase.write(c)?),
            ])),
        }
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        match v.field("tag")?.text()? {
            "gate" => {
                v.fields(&["tag", "gate", "target_index"])?;
                Ok(Self::Gate {
                    gate: Codec::read(v.field("gate")?, c)?,
                    target_index: Codec::read(v.field("target_index")?, c)?,
                })
            }
            "cnot" => {
                v.fields(&["tag", "control_index", "target_index"])?;
                Ok(Self::Cnot {
                    control_index: Codec::read(v.field("control_index")?, c)?,
                    target_index: Codec::read(v.field("target_index")?, c)?,
                })
            }
            "toffoli" => {
                v.fields(&["tag", "control_a_index", "control_b_index", "target_index"])?;
                Ok(Self::Toffoli {
                    control_a_index: Codec::read(v.field("control_a_index")?, c)?,
                    control_b_index: Codec::read(v.field("control_b_index")?, c)?,
                    target_index: Codec::read(v.field("target_index")?, c)?,
                })
            }
            "scalar_phase" => {
                v.fields(&["tag", "phase"])?;
                Ok(Self::ScalarPhase(Codec::read(v.field("phase")?, c)?))
            }
            _ => Err(Error::format("unknown node tag")),
        }
    }
}
