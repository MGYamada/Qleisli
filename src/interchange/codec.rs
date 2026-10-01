//! Explicit versioned wire fields, independent of Rust struct evolution.
use super::json::Value;
use super::{Decoder, Encoder, Error, Result};
use crate::ir::*;

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
mod evidence;
mod operations;
mod scalars;

// Explicit wire keys and field evaluation order are specified together. This
// removes duplicate read/write lists without deriving a format from Rust names.
macro_rules! record_codec {
    ($ty:ty { $($field:ident => $key:literal),+ $(,)? }) => {
        impl Codec for $ty {
            fn write(&self, c: &mut Encoder) -> Result<Value> {
                c.charge(1)?;
                Ok(Value::object([$(($key, self.$field.write(c)?)),+]))
            }
            fn read(v: &Value, c: &Decoder<'_>) -> Result<Self> {
                v.fields(&[$($key),+])?;
                Ok(Self { $($field: Codec::read(v.field($key)?, c)?),+ })
            }
        }
    };
}

record_codec!(BasisShape { bits => "bits" });
record_codec!(QuantumPort { token => "token", wires => "wires", shape => "shape" });
record_codec!(RawProgram {
    quantum_inputs => "quantum_inputs",
    classical_inputs => "classical_inputs",
    operations => "operations",
    quantum_outputs => "quantum_outputs",
    classical_outputs => "classical_outputs",
    declared_effect => "declared_effect",
});
record_codec!(BitControl { index => "index", when_one => "when_one" });
record_codec!(CircuitStep { controls => "controls", action => "action" });
record_codec!(ProtectedBit { region => "region", index => "index" });
record_codec!(Control { bit => "bit", when_one => "when_one" });
record_codec!(TargetTransition { input => "input", output => "output" });
record_codec!(QuantumPhi {
    then_token => "then_token",
    else_token => "else_token",
    output => "output",
    output_wires => "output_wires",
});
record_codec!(ClassicalPhi {
    then_id => "then_id",
    else_id => "else_id",
    output => "output",
});

#[cfg(test)]
mod tests {
    use super::*;
    use crate::contract::exact::Budget;
    use crate::contract::meaning::{FiniteMeaning, MeaningEvidence};
    use crate::contract::{BasisType, DEFAULT_EXACT_WORK, FunctionIdentity};
    use crate::interchange::Version;

    #[test]
    fn wire_integer_bounds_retain_field_range_and_u32_error_precedence() {
        let decoder = Decoder { evidence: &[] };
        assert_eq!(u8::read(&Value::Number(255), &decoder).unwrap(), 255);
        assert_eq!(u16::read(&Value::Number(65535), &decoder).unwrap(), 65535);
        assert_eq!(
            usize::read(&Value::Number(u64::from(u32::MAX)), &decoder).unwrap(),
            u32::MAX as usize
        );
        for error in [
            u8::read(&Value::Number(256), &decoder).unwrap_err(),
            u16::read(&Value::Number(65536), &decoder).unwrap_err(),
        ] {
            assert_eq!(error.code, "format");
            assert_eq!(error.message, "integer outside field range");
        }
        let overflow = Value::Number(u64::from(u32::MAX) + 1);
        for error in [
            u8::read(&overflow, &decoder).unwrap_err(),
            u16::read(&overflow, &decoder).unwrap_err(),
            u32::read(&overflow, &decoder).unwrap_err(),
            usize::read(&overflow, &decoder).unwrap_err(),
        ] {
            assert_eq!(error.code, "format");
            assert_eq!(error.message, "integer exceeds wire u32");
        }
    }

    #[test]
    fn record_wire_fields_and_work_are_stable_and_unknown_fields_are_rejected() {
        let mut encoder = Encoder::new(Version::V2);
        let decoder = Decoder { evidence: &[] };
        let port = QuantumPort {
            token: TokenId(7),
            wires: vec![WireId(19), WireId(3)],
            shape: BasisShape { bits: 2 },
        };
        let before = encoder.remaining;
        let encoded = port.write(&mut encoder).unwrap();
        // One port, two vector entries, one shape; IDs have no node charge.
        assert_eq!(before - encoder.remaining, 4);
        assert_eq!(
            super::super::json::encode(&encoded).unwrap(),
            b"{\"shape\":{\"bits\":2},\"token\":7,\"wires\":[19,3]}\n"
        );
        let Value::Object(mut fields) = encoded else {
            panic!("port must be a wire object")
        };
        fields.insert("extra".into(), Value::Null);
        assert!(QuantumPort::read(&Value::Object(fields.clone()), &decoder).is_err());
        fields.remove("extra");
        fields.remove("token");
        assert!(QuantumPort::read(&Value::Object(fields), &decoder).is_err());
    }

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
