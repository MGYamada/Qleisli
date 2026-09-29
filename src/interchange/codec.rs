//! Explicit versioned wire fields, independent of Rust struct evolution.
use super::json::Value;
use super::{Decoder, Encoder, Error, Result};
use crate::contract::{BasisType, FunctionEvidence};
use crate::ir::*;
use std::sync::Arc;

pub(super) trait Codec: Sized {
    fn write(&self, context: &mut Encoder) -> Result<Value>;
    fn read(value: &Value, context: &Decoder<'_>) -> Result<Self>;
}
impl<T: Codec> Codec for Vec<T> {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        c.charge(self.len())?;
        Ok(Value::Array(
            self.iter().map(|x| x.write(c)).collect::<Result<_>>()?,
        ))
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        v.array()?.iter().map(|x| T::read(x, c)).collect()
    }
}
impl Codec for bool {
    fn write(&self, _: &mut Encoder) -> Result<Value> {
        Ok(Value::Bool(*self))
    }
    fn read(v: &Value, _: &Decoder<'_>) -> Result<Self> {
        v.boolean()
    }
}
impl Codec for u8 {
    fn write(&self, _: &mut Encoder) -> Result<Value> {
        let n = u32::from(*self);
        Ok(Value::Number(u64::from(n)))
    }
    fn read(v: &Value, _: &Decoder<'_>) -> Result<Self> {
        let n =
            u32::try_from(v.number()?).map_err(|_| Error::format("integer exceeds wire u32"))?;
        u8::try_from(n).map_err(|_| Error::format("integer outside field range"))
    }
}
impl Codec for u16 {
    fn write(&self, _: &mut Encoder) -> Result<Value> {
        let n = u32::from(*self);
        Ok(Value::Number(u64::from(n)))
    }
    fn read(v: &Value, _: &Decoder<'_>) -> Result<Self> {
        let n =
            u32::try_from(v.number()?).map_err(|_| Error::format("integer exceeds wire u32"))?;
        u16::try_from(n).map_err(|_| Error::format("integer outside field range"))
    }
}
impl Codec for u32 {
    fn write(&self, _: &mut Encoder) -> Result<Value> {
        let n = *self;
        Ok(Value::Number(u64::from(n)))
    }
    fn read(v: &Value, _: &Decoder<'_>) -> Result<Self> {
        let n =
            u32::try_from(v.number()?).map_err(|_| Error::format("integer exceeds wire u32"))?;
        Ok(n)
    }
}
impl Codec for usize {
    fn write(&self, _: &mut Encoder) -> Result<Value> {
        let n = u32::try_from(*self).map_err(|_| Error::format("integer exceeds wire u32"))?;
        Ok(Value::Number(u64::from(n)))
    }
    fn read(v: &Value, _: &Decoder<'_>) -> Result<Self> {
        let n =
            u32::try_from(v.number()?).map_err(|_| Error::format("integer exceeds wire u32"))?;
        usize::try_from(n).map_err(|_| Error::format("integer outside field range"))
    }
}
impl Codec for TokenId {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        self.0.write(c)
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        Ok(Self(u32::read(v, c)?))
    }
}
impl Codec for WireId {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        self.0.write(c)
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        Ok(Self(u32::read(v, c)?))
    }
}
impl Codec for ClassicalId {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        self.0.write(c)
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        Ok(Self(u32::read(v, c)?))
    }
}
impl Codec for Effect {
    fn write(&self, _: &mut Encoder) -> Result<Value> {
        Ok(Value::String(
            match self {
                Self::Unitary => "unitary",
                Self::Iso => "iso",
                Self::Observe => "observe",
            }
            .into(),
        ))
    }
    fn read(v: &Value, _: &Decoder<'_>) -> Result<Self> {
        match v.text()? {
            "unitary" => Ok(Self::Unitary),
            "iso" => Ok(Self::Iso),
            "observe" => Ok(Self::Observe),
            _ => Err(Error::format("unknown enum spelling")),
        }
    }
}
impl Codec for SingleGate {
    fn write(&self, _: &mut Encoder) -> Result<Value> {
        Ok(Value::String(
            match self {
                Self::H => "h",
                Self::X => "x",
                Self::Z => "z",
                Self::T => "t",
            }
            .into(),
        ))
    }
    fn read(v: &Value, _: &Decoder<'_>) -> Result<Self> {
        match v.text()? {
            "h" => Ok(Self::H),
            "x" => Ok(Self::X),
            "z" => Ok(Self::Z),
            "t" => Ok(Self::T),
            _ => Err(Error::format("unknown enum spelling")),
        }
    }
}
impl Codec for ScalarPhase {
    fn write(&self, _: &mut Encoder) -> Result<Value> {
        Ok(Value::String(
            match self {
                Self::MinusOne => "minus_one",
                Self::EighthTurn => "eighth_turn",
            }
            .into(),
        ))
    }
    fn read(v: &Value, _: &Decoder<'_>) -> Result<Self> {
        match v.text()? {
            "minus_one" => Ok(Self::MinusOne),
            "eighth_turn" => Ok(Self::EighthTurn),
            _ => Err(Error::format("unknown enum spelling")),
        }
    }
}
impl Codec for ProtectedRegion {
    fn write(&self, _: &mut Encoder) -> Result<Value> {
        Ok(Value::String(
            match self {
                Self::Source => "source",
                Self::Ancilla => "ancilla",
            }
            .into(),
        ))
    }
    fn read(v: &Value, _: &Decoder<'_>) -> Result<Self> {
        match v.text()? {
            "source" => Ok(Self::Source),
            "ancilla" => Ok(Self::Ancilla),
            _ => Err(Error::format("unknown enum spelling")),
        }
    }
}
impl Codec for BasisShape {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        c.charge(1)?;
        Ok(Value::object([("bits", self.bits.write(c)?)]))
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        v.fields(&["bits"])?;
        Ok(Self {
            bits: Codec::read(v.field("bits")?, c)?,
        })
    }
}
impl Codec for QuantumPort {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        c.charge(1)?;
        Ok(Value::object([
            ("token", self.token.write(c)?),
            ("wires", self.wires.write(c)?),
            ("shape", self.shape.write(c)?),
        ]))
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        v.fields(&["token", "wires", "shape"])?;
        Ok(Self {
            token: Codec::read(v.field("token")?, c)?,
            wires: Codec::read(v.field("wires")?, c)?,
            shape: Codec::read(v.field("shape")?, c)?,
        })
    }
}
impl Codec for RawProgram {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        c.charge(1)?;
        Ok(Value::object([
            ("quantum_inputs", self.quantum_inputs.write(c)?),
            ("classical_inputs", self.classical_inputs.write(c)?),
            ("operations", self.operations.write(c)?),
            ("quantum_outputs", self.quantum_outputs.write(c)?),
            ("classical_outputs", self.classical_outputs.write(c)?),
            ("declared_effect", self.declared_effect.write(c)?),
        ]))
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        v.fields(&[
            "quantum_inputs",
            "classical_inputs",
            "operations",
            "quantum_outputs",
            "classical_outputs",
            "declared_effect",
        ])?;
        Ok(Self {
            quantum_inputs: Codec::read(v.field("quantum_inputs")?, c)?,
            classical_inputs: Codec::read(v.field("classical_inputs")?, c)?,
            operations: Codec::read(v.field("operations")?, c)?,
            quantum_outputs: Codec::read(v.field("quantum_outputs")?, c)?,
            classical_outputs: Codec::read(v.field("classical_outputs")?, c)?,
            declared_effect: Codec::read(v.field("declared_effect")?, c)?,
        })
    }
}
impl Codec for BitControl {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        c.charge(1)?;
        Ok(Value::object([
            ("index", self.index.write(c)?),
            ("when_one", self.when_one.write(c)?),
        ]))
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        v.fields(&["index", "when_one"])?;
        Ok(Self {
            index: Codec::read(v.field("index")?, c)?,
            when_one: Codec::read(v.field("when_one")?, c)?,
        })
    }
}
impl Codec for CircuitStep {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        c.charge(1)?;
        Ok(Value::object([
            ("controls", self.controls.write(c)?),
            ("action", self.action.write(c)?),
        ]))
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        v.fields(&["controls", "action"])?;
        Ok(Self {
            controls: Codec::read(v.field("controls")?, c)?,
            action: Codec::read(v.field("action")?, c)?,
        })
    }
}
impl Codec for ProtectedBit {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        c.charge(1)?;
        Ok(Value::object([
            ("region", self.region.write(c)?),
            ("index", self.index.write(c)?),
        ]))
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        v.fields(&["region", "index"])?;
        Ok(Self {
            region: Codec::read(v.field("region")?, c)?,
            index: Codec::read(v.field("index")?, c)?,
        })
    }
}
impl Codec for Control {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        c.charge(1)?;
        Ok(Value::object([
            ("bit", self.bit.write(c)?),
            ("when_one", self.when_one.write(c)?),
        ]))
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        v.fields(&["bit", "when_one"])?;
        Ok(Self {
            bit: Codec::read(v.field("bit")?, c)?,
            when_one: Codec::read(v.field("when_one")?, c)?,
        })
    }
}
impl Codec for TargetTransition {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        c.charge(1)?;
        Ok(Value::object([
            ("input", self.input.write(c)?),
            ("output", self.output.write(c)?),
        ]))
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        v.fields(&["input", "output"])?;
        Ok(Self {
            input: Codec::read(v.field("input")?, c)?,
            output: Codec::read(v.field("output")?, c)?,
        })
    }
}
impl Codec for QuantumPhi {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        c.charge(1)?;
        Ok(Value::object([
            ("then_token", self.then_token.write(c)?),
            ("else_token", self.else_token.write(c)?),
            ("output", self.output.write(c)?),
            ("output_wires", self.output_wires.write(c)?),
        ]))
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        v.fields(&["then_token", "else_token", "output", "output_wires"])?;
        Ok(Self {
            then_token: Codec::read(v.field("then_token")?, c)?,
            else_token: Codec::read(v.field("else_token")?, c)?,
            output: Codec::read(v.field("output")?, c)?,
            output_wires: Codec::read(v.field("output_wires")?, c)?,
        })
    }
}
impl Codec for ClassicalPhi {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        c.charge(1)?;
        Ok(Value::object([
            ("then_id", self.then_id.write(c)?),
            ("else_id", self.else_id.write(c)?),
            ("output", self.output.write(c)?),
        ]))
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        v.fields(&["then_id", "else_id", "output"])?;
        Ok(Self {
            then_id: Codec::read(v.field("then_id")?, c)?,
            else_id: Codec::read(v.field("else_id")?, c)?,
            output: Codec::read(v.field("output")?, c)?,
        })
    }
}
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

impl Codec for BasisType {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        c.charge(1)?;
        Ok(match self {
            Self::Unit => Value::object([("tag", Value::String("unit".into()))]),
            Self::Bit => Value::object([("tag", Value::String("bit".into()))]),
            Self::Pair(a, b) => Value::object([
                ("tag", Value::String("pair".into())),
                ("left", a.write(c)?),
                ("right", b.write(c)?),
            ]),
            Self::Tuple(fields) => {
                if fields.len() < 3 {
                    return Err(Error::format("tuple type requires at least three fields"));
                }
                Value::object([
                    ("tag", Value::String("tuple".into())),
                    ("fields", fields.write(c)?),
                ])
            }
        })
    }
    fn read(v: &Value, _c: &Decoder<'_>) -> Result<Self> {
        match v.field("tag")?.text()? {
            "unit" => {
                v.fields(&["tag"])?;
                Ok(Self::Unit)
            }
            "bit" => {
                v.fields(&["tag"])?;
                Ok(Self::Bit)
            }
            "pair" => {
                v.fields(&["tag", "left", "right"])?;
                Ok(Self::pair(
                    Self::read(v.field("left")?, _c)?,
                    Self::read(v.field("right")?, _c)?,
                ))
            }
            "tuple" => {
                v.fields(&["tag", "fields"])?;
                let fields = Vec::<Self>::read(v.field("fields")?, _c)?;
                if fields.len() < 3 {
                    return Err(Error::format("tuple type requires at least three fields"));
                }
                Ok(Self::Tuple(fields))
            }
            _ => Err(Error::format("unknown basis type")),
        }
    }
}
impl Codec for Arc<FunctionEvidence> {
    fn write(&self, c: &mut Encoder) -> Result<Value> {
        Ok(Value::Number(c.evidence(self)? as u64))
    }
    fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
        let i = usize::read(v, c)?;
        c.evidence
            .get(i)
            .and_then(Option::as_ref)
            .cloned()
            .ok_or_else(|| Error::format("unchecked or invalid evidence reference"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::contract::exact::Budget;
    use crate::contract::meaning::{FiniteMeaning, MeaningEvidence};
    use crate::contract::{DEFAULT_EXACT_WORK, FunctionIdentity};
    use crate::interchange::Version;

    #[test]
    fn every_frozen_raw_operation_and_action_preserves_its_fields() {
        let target = FiniteMeaning::permutation(BasisType::Bit, vec![1, 0]).unwrap();
        let receipt = MeaningEvidence::check(
            target.target_ir().unwrap(),
            target,
            FunctionIdentity {
                implementation: "x".into(),
                specification: "flip".into(),
                sources: vec![],
            },
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .unwrap()
        .receipt();
        let steps = vec![
            CircuitStep {
                controls: vec![BitControl {
                    index: 2,
                    when_one: false,
                }],
                action: CircuitAction::Contract {
                    indices: vec![0],
                    evidence: receipt.clone(),
                    adjoint: true,
                },
            },
            CircuitStep {
                controls: vec![],
                action: CircuitAction::Hadamard { target: 1 },
            },
            CircuitStep {
                controls: vec![BitControl {
                    index: 0,
                    when_one: true,
                }],
                action: CircuitAction::Monomial {
                    indices: vec![1],
                    permutation: vec![1, 0],
                    phases: vec![3, 7],
                },
            },
        ];
        let t = TokenId;
        let w = WireId;
        let c = ClassicalId;
        let unitary = vec![
            UnitaryStep::Gate {
                gate: SingleGate::Z,
                target_index: 2,
            },
            UnitaryStep::Cnot {
                control_index: 1,
                target_index: 0,
            },
            UnitaryStep::Toffoli {
                control_a_index: 1,
                control_b_index: 2,
                target_index: 0,
            },
            UnitaryStep::ScalarPhase(ScalarPhase::EighthTurn),
        ];
        let protected = vec![
            ProtectedUse::ProtectedGate {
                bit: ProtectedBit {
                    region: ProtectedRegion::Source,
                    index: 1,
                },
                gate: SingleGate::T,
            },
            ProtectedUse::ControlledTargetGate {
                controls: vec![Control {
                    bit: ProtectedBit {
                        region: ProtectedRegion::Ancilla,
                        index: 0,
                    },
                    when_one: false,
                }],
                target_index: 2,
                gate: SingleGate::H,
            },
            ProtectedUse::ControlledPhase {
                controls: vec![Control {
                    bit: ProtectedBit {
                        region: ProtectedRegion::Source,
                        index: 2,
                    },
                    when_one: true,
                }],
                phase: ScalarPhase::MinusOne,
            },
        ];
        // Distinct asymmetric fields catch accidental swaps as well as omission.
        // These are wire-codec fixtures; semantic validity is checked separately.
        let variants = vec![
            (
                "certified_compute",
                RawOp::CertifiedCompute {
                    source: t(2),
                    source_out: t(3),
                    ancilla_wires: vec![w(19)],
                    function: vec![0, 1],
                    use_steps: steps.clone(),
                    logical_steps: steps.clone(),
                },
            ),
            (
                "apply_unitary",
                RawOp::ApplyUnitary {
                    input: t(3),
                    output: t(9),
                    steps,
                },
            ),
            (
                "init0",
                RawOp::Init0 {
                    output: t(25),
                    wire: w(300),
                },
            ),
            (
                "gate",
                RawOp::Gate {
                    gate: SingleGate::X,
                    input: t(25),
                    output: t(29),
                },
            ),
            (
                "cnot",
                RawOp::Cnot {
                    control: t(1),
                    target: t(2),
                    control_out: t(3),
                    target_out: t(4),
                },
            ),
            (
                "toffoli",
                RawOp::Toffoli {
                    control_a: t(1),
                    control_b: t(2),
                    target: t(3),
                    control_a_out: t(4),
                    control_b_out: t(5),
                    target_out: t(6),
                },
            ),
            (
                "quantum_if",
                RawOp::QuantumIf {
                    control: t(1),
                    target: t(2),
                    control_out: t(3),
                    target_out: t(4),
                    zero_ops: unitary.clone(),
                    one_ops: unitary.into_iter().rev().collect(),
                },
            ),
            (
                "split",
                RawOp::Split {
                    input: t(1),
                    left: t(2),
                    right: t(3),
                    left_bits: 2,
                },
            ),
            (
                "join",
                RawOp::Join {
                    left: t(2),
                    right: t(3),
                    output: t(4),
                },
            ),
            (
                "lift_basis",
                RawOp::LiftBasis {
                    input: t(1),
                    output: t(2),
                    output_wires: vec![w(4), w(7)],
                    table: vec![0, 3],
                },
            ),
            (
                "measure_z",
                RawOp::MeasureZ {
                    input: t(4),
                    output: c(9),
                },
            ),
            (
                "reset",
                RawOp::Reset {
                    input: t(8),
                    output: t(9),
                    fresh_wire: w(11),
                },
            ),
            ("discard", RawOp::Discard { input: t(9) }),
            (
                "classical_const",
                RawOp::ClassicalConst {
                    value: true,
                    output: c(7),
                },
            ),
            (
                "classical_not",
                RawOp::ClassicalNot {
                    input: c(7),
                    output: c(8),
                },
            ),
            (
                "classical_xor",
                RawOp::ClassicalXor {
                    left: c(7),
                    right: c(9),
                    output: c(10),
                },
            ),
            (
                "classical_and",
                RawOp::ClassicalAnd {
                    left: c(9),
                    right: c(10),
                    output: c(11),
                },
            ),
            (
                "classical_branch",
                RawOp::ClassicalBranch {
                    condition: c(2),
                    then_ops: vec![RawOp::ClassicalConst {
                        value: false,
                        output: c(12),
                    }],
                    else_ops: vec![RawOp::Discard { input: t(5) }],
                    quantum_phis: vec![QuantumPhi {
                        then_token: t(2),
                        else_token: t(3),
                        output: t(4),
                        output_wires: vec![w(12), w(15)],
                    }],
                    classical_phis: vec![ClassicalPhi {
                        then_id: c(12),
                        else_id: c(5),
                        output: c(20),
                    }],
                },
            ),
            (
                "compute_use_uncompute",
                RawOp::ComputeUseUncompute {
                    source: t(1),
                    source_out: t(2),
                    targets: vec![TargetTransition {
                        input: t(3),
                        output: t(4),
                    }],
                    ancilla_wires: vec![w(7)],
                    function: vec![1, 0],
                    use_ops: protected,
                },
            ),
        ];
        for version in [Version::V1, Version::V2] {
            let mut encoder = Encoder::new(version);
            let evidence = [Some(receipt.clone())];
            let decoder = Decoder {
                evidence: &evidence,
            };
            for (tag, raw) in &variants {
                let value = raw.write(&mut encoder).unwrap();
                assert_eq!(value.field("tag").unwrap().text().unwrap(), *tag);
                assert_eq!(RawOp::read(&value, &decoder).unwrap(), *raw, "{tag}");
            }
        }
    }
}
