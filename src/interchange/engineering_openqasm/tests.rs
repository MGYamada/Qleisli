// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::super::engineering_pure::DyadicBound;
use super::*;
use crate::contract::{FunctionIdentity, InstrumentSignature};
use crate::ir::{
    BasisShape, ClassicalId, Effect, QuantumPort, RawOp, RawProgram, SingleGate, TokenId, WireId,
};

fn text(gates: &str) -> Vec<u8> {
    format!("OPENQASM 3.0;\ninclude \"stdgates.inc\";\nqubit[1] q;\nbit[1] c;\nreset q;\n{gates}c[0] = measure q[0];\n").into_bytes()
}

fn request(epsilon: DyadicBound, majorants: Vec<DyadicBound>) -> EngineeringOpenQasmRequest {
    let signature = InstrumentSignature::new(BasisType::Unit, vec![InstrumentResult::Bit]).unwrap();
    EngineeringOpenQasmRequest::new(
        EngineeringInstrumentRequest::new(
            signature.clone(),
            signature,
            FunctionIdentity {
                implementation: "literal-target".into(),
                specification: "original-ideal".into(),
                sources: vec![],
            },
            epsilon,
            majorants,
        )
        .unwrap(),
    )
    .unwrap()
}

fn nonzero_request() -> EngineeringOpenQasmRequest {
    request(
        DyadicBound::new(1, 0).unwrap(),
        vec![DyadicBound::new(1, 1).unwrap(); 2],
    )
}

#[test]
fn canonical_target_is_literal_closed_unit_data_with_exact_ordered_gate_expansions() {
    let bytes =
        text("h q[0];\nx q[0];\ny q[0];\nz q[0];\ns q[0];\nsdg q[0];\nt q[0];\ntdg q[0];\n");
    let decoded = target::Decoded::new(&bytes).unwrap();
    assert_eq!(decoded.original(), bytes);
    assert_eq!(
        decoded.gate_word().collect::<Vec<_>>(),
        ["h", "x", "y", "z", "s", "sdg", "t", "tdg"]
    );
    let graph = decoded.graph();
    assert!(graph.interface.is_none());
    assert_eq!(graph.effect, Effect::Observe);
    assert!(graph.outputs.is_empty());
    let raw = graph.root;
    assert_eq!(
        raw.quantum_inputs,
        [QuantumPort {
            token: TokenId(0),
            wires: vec![],
            shape: BasisShape::UNIT
        }]
    );
    assert!(raw.quantum_outputs.is_empty());
    assert_eq!(raw.classical_outputs, [ClassicalId(0)]);
    assert_eq!(raw.operations[0], RawOp::UnpackUnit { input: TokenId(0) });
    assert_eq!(
        raw.operations[1],
        RawOp::Init0 {
            output: TokenId(1),
            wire: WireId(0)
        }
    );
    assert_eq!(
        raw.operations.last(),
        Some(&RawOp::MeasureZ {
            input: TokenId(9),
            output: ClassicalId(0)
        })
    );
    for (index, permutation, phases) in [
        (4, vec![1, 0], vec![2, 6]),
        (6, vec![0, 1], vec![0, 2]),
        (7, vec![0, 1], vec![0, 6]),
        (9, vec![0, 1], vec![0, 7]),
    ] {
        let RawOp::ApplyUnitary {
            input,
            output,
            steps,
        } = &raw.operations[index]
        else {
            panic!("expected literal monomial for gate at {index}")
        };
        assert_eq!(input.0 + 1, output.0);
        assert_eq!(steps.len(), 1);
        assert!(steps[0].controls.is_empty());
        assert_eq!(
            steps[0].action,
            crate::ir::CircuitAction::Monomial {
                indices: vec![0],
                permutation,
                phases
            }
        );
    }
    for bad in [
        text("h q[1];\n"),
        text("rx(0.1) q[0];\n"),
        text("c[0] = measure q[0];\nh q[0];\n"),
        text("// comment\n"),
        text(&"h q[0];\n".repeat(9)),
        text("").strip_suffix(b"\n").unwrap().to_vec(),
        text("").into_iter().chain(*b"\n").collect(),
        text("").into_iter().chain([128]).collect(),
        text("")
            .into_iter()
            .map(|b| if b == b'\n' { b'\r' } else { b })
            .collect(),
        String::from_utf8(text(""))
            .unwrap()
            .replace("stdgates.inc", "other.inc")
            .into_bytes(),
        vec![b' '; 1025],
        vec![],
    ] {
        assert!(target::Decoded::new(&bad).is_err(), "{bad:?}");
    }
}

#[test]
fn closed_request_retains_identity_bounds_and_rejects_full_type_or_profile_substitution() {
    let original = nonzero_request();
    let bytes = encode_request(&original, b"{\"untouched\":\"ideal\\nbytes\"}\n").unwrap();
    let (decoded, ideal) = decode_request(&bytes).unwrap();
    assert_eq!(decoded, original);
    assert_eq!(ideal, "{\"untouched\":\"ideal\\nbytes\"}\n");
    let base = json::parse(&bytes).unwrap();
    let Value::Object(fields) = &base else {
        unreachable!()
    };
    for field in fields.keys() {
        let mut missing = base.clone();
        let Value::Object(fields) = &mut missing else {
            unreachable!()
        };
        fields.remove(field);
        assert!(
            decode_request(&json::encode(&missing).unwrap()).is_err(),
            "{field}"
        );
    }
    for (field, _, _) in PROFILES {
        let mut changed = base.clone();
        let Value::Object(fields) = &mut changed else {
            unreachable!()
        };
        fields.insert(
            field.into(),
            Value::String("engineering-instrument-bound".into()),
        );
        assert!(
            decode_request(&json::encode(&changed).unwrap()).is_err(),
            "{field}"
        );
    }
    let wrong = InstrumentSignature::new(BasisType::Bits(0), vec![InstrumentResult::Bit]).unwrap();
    let contract = original.contract();
    assert!(
        EngineeringOpenQasmRequest::new(
            EngineeringInstrumentRequest::new(
                wrong.clone(),
                wrong,
                contract.identity().clone(),
                contract.epsilon(),
                contract.majorants().to_vec()
            )
            .unwrap()
        )
        .is_err()
    );
    let wrong = InstrumentSignature::new(BasisType::Unit, vec![InstrumentResult::Bits(1)]).unwrap();
    assert!(
        EngineeringOpenQasmRequest::new(
            EngineeringInstrumentRequest::new(
                wrong.clone(),
                wrong,
                contract.identity().clone(),
                contract.epsilon(),
                contract.majorants().to_vec()
            )
            .unwrap()
        )
        .is_err()
    );
    let mut extra = base;
    let Value::Object(fields) = &mut extra else {
        unreachable!()
    };
    fields.insert("accepted".into(), Value::Bool(true));
    assert!(decode_request(&json::encode(&extra).unwrap()).is_err());
    assert!(decode_request(&[]).is_err());
    assert!(decode_request(&vec![b' '; MAX_FILE_BYTES + 1]).is_err());
}

fn ideal(kernel: &Kernel, gate: SingleGate) -> AcceptedProgram {
    kernel
        .verify(&RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: TokenId(0),
                wires: vec![],
                shape: BasisShape::UNIT,
            }],
            classical_inputs: vec![],
            operations: vec![
                RawOp::UnpackUnit { input: TokenId(0) },
                RawOp::Init0 {
                    output: TokenId(1),
                    wire: WireId(0),
                },
                RawOp::Gate {
                    gate,
                    input: TokenId(1),
                    output: TokenId(2),
                },
                RawOp::MeasureZ {
                    input: TokenId(2),
                    output: ClassicalId(0),
                },
            ],
            quantum_outputs: vec![],
            classical_outputs: vec![ClassicalId(0)],
            declared_effect: Effect::Observe,
        })
        .unwrap()
        .into_program()
}

fn exported(kernel: &Kernel, hadamard: bool) -> Vec<u8> {
    let mut operations = vec![RawOp::Init0 {
        output: TokenId(1),
        wire: WireId(0),
    }];
    if hadamard {
        operations.push(RawOp::Gate {
            gate: SingleGate::H,
            input: TokenId(1),
            output: TokenId(2),
        });
    }
    operations.push(RawOp::MeasureZ {
        input: TokenId(if hadamard { 2 } else { 1 }),
        output: ClassicalId(0),
    });
    let closed = kernel
        .verify(&RawProgram {
            quantum_inputs: vec![],
            classical_inputs: vec![],
            operations,
            quantum_outputs: vec![],
            classical_outputs: vec![ClassicalId(0)],
            declared_effect: Effect::Observe,
        })
        .unwrap()
        .into_program();
    crate::interop::export_openqasm3(&closed)
        .unwrap()
        .into_bytes()
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn native_checks_actual_backend_target_bytes_against_an_original_ideal_and_zero_stays_engineering()
{
    let kernel = Kernel::selected(crate::edition::Edition::E2026).unwrap();
    let actual = exported(&kernel, false);
    assert_eq!(actual, text(""));
    let ideal = ideal(&kernel, SingleGate::H);
    let request = nonzero_request();
    let report = check_with_kernel(&kernel, &actual, &ideal, &request).unwrap();
    assert_eq!(report.target_bytes(), actual);
    assert_eq!(report.ideal_artifact(), ideal.artifact());
    assert_eq!(report.request(), &request);
    assert_eq!(report.claim_kind(), CLAIM_KIND);
    assert_eq!(report.metric(), METRIC);
    assert_eq!(report.checker_profile(), CHECKER_PROFILE);
    assert_eq!(report.target_profile(), TARGET_PROFILE);
    assert_eq!(report.composition(), COMPOSITION);
    assert_eq!(report.error_category(), ERROR_CATEGORY);
    assert!(report.gate_word().collect::<Vec<_>>().is_empty());
    assert!(report.exact_work() > 0);
    let original = [b"\n ".as_slice(), report.request_bytes(), b" \n".as_slice()].concat();
    let replay = check_serialized_with_kernel(&kernel, &actual, &original).unwrap();
    assert_eq!(replay.request_bytes(), original);
    assert_eq!(replay.target_bytes(), actual);
    assert_eq!(replay.ideal_artifact(), ideal.artifact());
    let zero = self::request(
        DyadicBound::new(0, 0).unwrap(),
        vec![DyadicBound::new(0, 0).unwrap(); 2],
    );
    let h_target = exported(&kernel, true);
    let zero_report = check_with_kernel(&kernel, &h_target, &ideal, &zero).unwrap();
    assert_eq!(zero_report.claim_kind(), CLAIM_KIND);
    assert_eq!(zero_report.gate_word().collect::<Vec<_>>(), ["h"]);
    assert_eq!(
        zero_report.request().contract().epsilon(),
        DyadicBound::new(0, 0).unwrap()
    );
    assert!(check_with_kernel(&kernel, &actual, &ideal, &zero).is_err());
    let subject = Subject::prepare(&kernel, &actual, &ideal, &request).unwrap();
    let changed_target = Subject::prepare(&kernel, &h_target, &ideal, &request).unwrap();
    assert_eq!(
        subject
            .bind(Decision {
                context: report.context,
                subject: changed_target,
                exact_work: report.exact_work()
            })
            .unwrap_err()
            .code,
        "kernel"
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn altered_original_ideal_tight_bound_or_cell_witness_refuses_without_fallback() {
    let kernel = Kernel::selected(crate::edition::Edition::E2026).unwrap();
    let actual = exported(&kernel, false);
    let ideal = ideal(&kernel, SingleGate::H);
    for changed in [
        request(
            DyadicBound::new(1, 1).unwrap(),
            vec![DyadicBound::new(1, 1).unwrap(); 2],
        ),
        request(
            DyadicBound::new(1, 0).unwrap(),
            vec![DyadicBound::new(1, 2).unwrap(); 2],
        ),
        request(
            DyadicBound::new(1, 0).unwrap(),
            vec![DyadicBound::new(1, 1).unwrap()],
        ),
        request(
            DyadicBound::new(1, 0).unwrap(),
            vec![DyadicBound::new(1, 1).unwrap(); 3],
        ),
    ] {
        assert!(check_with_kernel(&kernel, &actual, &ideal, &changed).is_err());
    }
    let wrong_ideal = self::ideal(&kernel, SingleGate::X);
    assert!(check_with_kernel(&kernel, &actual, &wrong_ideal, &nonzero_request()).is_err());
}

fn view_value(bytes: &[u8]) -> crate::interchange::execution_view::Value {
    use crate::interchange::execution_view::Value as View;
    fn read(bytes: &[u8], offset: &mut usize) -> View {
        let tag = bytes[*offset];
        *offset += 1;
        if tag <= 2 {
            return match tag {
                0 => View::Null,
                1 => View::Bool(false),
                _ => View::Bool(true),
            };
        }
        if tag == 3 {
            let value = u64::from_le_bytes(bytes[*offset..*offset + 8].try_into().unwrap());
            *offset += 8;
            return View::Natural(value);
        }
        let count = u32::from_le_bytes(bytes[*offset..*offset + 4].try_into().unwrap()) as usize;
        *offset += 4;
        if tag == 4 {
            let value = std::str::from_utf8(&bytes[*offset..*offset + count])
                .unwrap()
                .to_owned();
            *offset += count;
            View::Text(value)
        } else {
            assert_eq!(tag, 5);
            View::Array((0..count).map(|_| read(bytes, offset)).collect())
        }
    }
    assert_eq!(&bytes[..4], b"QDV1");
    let mut offset = 4;
    let value = read(bytes, &mut offset);
    assert_eq!(offset, bytes.len());
    value
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn native_binds_literal_target_gate_word_typed_context_and_both_original_graphs() {
    use crate::interchange::execution_view::{self, Value as View};
    let kernel = Kernel::selected(crate::edition::Edition::E2026).unwrap();
    let actual = exported(&kernel, false);
    let ideal = ideal(&kernel, SingleGate::H);
    let request = nonzero_request();
    let subject = Subject::prepare(&kernel, &actual, &ideal, &request).unwrap();
    let packet = subject.packet().unwrap();
    runtime::check(
        &subject.checker,
        packet.clone(),
        crate::edition::Edition::E2026,
    )
    .unwrap();
    let original_len = u32::from_le_bytes(packet[12..16].try_into().unwrap()) as usize;
    let graph_len = u32::from_le_bytes(packet[16..20].try_into().unwrap()) as usize;
    let graph_start = 28 + original_len;
    let original = &packet[28..graph_start];
    let description = view_value(&packet[graph_start..graph_start + graph_len]);
    for (slot, count) in [(1, 15), (4, 9), (5, 9)] {
        for field in 0..count {
            let mut mutation = description.clone();
            let View::Array(root) = &mut mutation else {
                unreachable!()
            };
            let View::Array(fields) = &mut root[slot] else {
                unreachable!()
            };
            assert_eq!(fields.len(), count);
            // Generated target and original ideal deliberately have no root
            // interface. Mutating an existing Null to Null would test nothing.
            fields[field] = if matches!(fields[field], View::Null) {
                View::Bool(true)
            } else {
                View::Null
            };
            let graph = execution_view::encode(&mutation).unwrap();
            let (packet, _) = super::super::native_packet::encode(
                crate::edition::Edition::E2026,
                original,
                Some(super::super::native_packet::View {
                    graph: &graph,
                    caller: None,
                }),
            )
            .unwrap();
            assert_eq!(
                runtime::check(&subject.checker, packet, crate::edition::Edition::E2026)
                    .unwrap_err()
                    .code,
                "decoded_view",
                "slot {slot} field {field}"
            );
        }
    }
    for slot in [2, 3] {
        let mut mutation = description.clone();
        let View::Array(root) = &mut mutation else {
            unreachable!()
        };
        root[slot] = View::Null;
        let graph = execution_view::encode(&mutation).unwrap();
        let (packet, _) = super::super::native_packet::encode(
            crate::edition::Edition::E2026,
            original,
            Some(super::super::native_packet::View {
                graph: &graph,
                caller: None,
            }),
        )
        .unwrap();
        assert_eq!(
            runtime::check(&subject.checker, packet, crate::edition::Edition::E2026)
                .unwrap_err()
                .code,
            "decoded_view"
        );
    }
    let (inspection, _) =
        super::super::native_packet::encode(crate::edition::Edition::E2026, original, None)
            .unwrap();
    assert!(runtime::check(&subject.checker, inspection, crate::edition::Edition::E2026).is_err());
    let graph = &packet[graph_start..graph_start + graph_len];
    let (caller, _) = super::super::native_packet::encode(
        crate::edition::Edition::E2026,
        original,
        Some(super::super::native_packet::View {
            graph,
            caller: Some((graph, &[])),
        }),
    )
    .unwrap();
    assert!(runtime::check(&subject.checker, caller, crate::edition::Edition::E2026).is_err());
    assert!(
        runtime::check(
            &subject.checker,
            original.to_vec(),
            crate::edition::Edition::E2026
        )
        .is_err()
    );
}
