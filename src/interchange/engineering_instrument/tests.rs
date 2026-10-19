// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::ir::{
    BasisShape, ClassicalId, Effect, QuantumPort, RawOp, RawProgram, SingleGate, TokenId, WireId,
};

fn port(token: u32, wires: &[u32]) -> QuantumPort {
    QuantumPort {
        token: TokenId(token),
        wires: wires.iter().copied().map(WireId).collect(),
        shape: BasisShape {
            bits: wires.len() as u8,
        },
    }
}

fn identity() -> FunctionIdentity {
    FunctionIdentity {
        implementation: "actual".into(),
        specification: "ideal".into(),
        sources: vec![],
    }
}

fn unit_signature() -> InstrumentSignature {
    InstrumentSignature::new(BasisType::Unit, vec![InstrumentResult::Bit]).unwrap()
}

fn unit_request() -> EngineeringInstrumentRequest {
    EngineeringInstrumentRequest::new(
        unit_signature(),
        unit_signature(),
        identity(),
        DyadicBound::new(1, 1).unwrap(),
        vec![DyadicBound::new(1, 2).unwrap(); 2],
    )
    .unwrap()
}

#[test]
fn signatures_keep_full_trees_zero_width_owners_and_validate_prefix_capacity() {
    let signature = InstrumentSignature::new(
        BasisType::Unit,
        vec![
            InstrumentResult::Pair,
            InstrumentResult::Unit,
            InstrumentResult::Quantum(BasisType::Unit),
        ],
    )
    .unwrap();
    assert_eq!(signature.input(), &BasisType::Unit);
    assert_eq!(signature.result().len(), 3);
    let same_width =
        InstrumentSignature::new(BasisType::Bits(0), signature.result().to_vec()).unwrap();
    assert_ne!(signature, same_width);
    assert!(
        EngineeringInstrumentRequest::new(
            signature,
            same_width,
            identity(),
            DyadicBound::new(0, 0).unwrap(),
            vec![]
        )
        .is_err()
    );
    for result in [
        vec![],
        vec![InstrumentResult::Pair, InstrumentResult::Bit],
        vec![InstrumentResult::Bit, InstrumentResult::Unit],
        vec![InstrumentResult::Tuple(usize::MAX)],
        vec![InstrumentResult::Unit; 4097],
        vec![InstrumentResult::Quantum(BasisType::Bits(7))],
    ] {
        assert!(InstrumentSignature::new(BasisType::Unit, result).is_err());
    }
    assert!(InstrumentSignature::new(BasisType::Bits(7), vec![InstrumentResult::Unit]).is_err());
    let mut result = vec![];
    for _ in 0..65 {
        result.extend([InstrumentResult::Pair, InstrumentResult::Unit]);
    }
    result.push(InstrumentResult::Unit);
    assert!(InstrumentSignature::new(BasisType::Unit, result).is_err());
}

#[test]
fn request_retains_exact_identity_and_witnesses_without_acceptance() {
    let original = unit_request();
    let expected = "{\"unaltered\":\"original\\nbytes\"}\n";
    let bytes = encode_request(&original, expected.as_bytes()).unwrap();
    let (decoded, artifact) = decode_request(&bytes).unwrap();
    assert_eq!(decoded, original);
    assert_eq!(artifact, expected);
    assert_eq!(decoded.epsilon(), DyadicBound::new(1, 1).unwrap());
    assert_eq!(decoded.majorants(), [DyadicBound::new(1, 2).unwrap(); 2]);
    for invalid in [
        FunctionIdentity {
            implementation: "".into(),
            ..identity()
        },
        FunctionIdentity {
            specification: "i".repeat(4097),
            ..identity()
        },
        FunctionIdentity {
            sources: vec![("a".into(), "".into()), ("a".into(), "".into())],
            ..identity()
        },
        FunctionIdentity {
            sources: (0..129).map(|i| (format!("{i}"), String::new())).collect(),
            ..identity()
        },
        FunctionIdentity {
            sources: vec![("a".into(), "a".repeat(1_048_577))],
            ..identity()
        },
    ] {
        assert!(
            EngineeringInstrumentRequest::new(
                unit_signature(),
                unit_signature(),
                invalid,
                DyadicBound::new(1, 1).unwrap(),
                vec![]
            )
            .is_err()
        );
    }
    assert!(
        EngineeringInstrumentRequest::new(
            unit_signature(),
            unit_signature(),
            identity(),
            DyadicBound::new(1, 1).unwrap(),
            vec![DyadicBound::new(0, 0).unwrap(); DEFAULT_EXACT_WORK / 256 + 1]
        )
        .is_err()
    );
}

fn set(value: &mut Value, name: &str, replacement: Value) {
    let Value::Object(fields) = value else {
        panic!("test object expected")
    };
    fields.insert(name.into(), replacement);
}

#[test]
fn strict_request_rejects_unknown_missing_open_and_cross_kind_data() {
    let bytes = encode_request(&unit_request(), b"{}").unwrap();
    let base = json::parse(&bytes).unwrap();
    for field in [
        "format",
        "version",
        "claim_kind",
        "metric",
        "checker_profile",
        "target_profile",
        "composition",
        "error_category",
        "actual_signature",
        "expected_signature",
        "identity",
        "epsilon",
        "majorants",
        "expected_artifact",
    ] {
        let mut missing = base.clone();
        let Value::Object(fields) = &mut missing else {
            unreachable!()
        };
        fields.remove(field);
        assert!(
            decode_request(&json::encode(&missing).unwrap()).is_err(),
            "missing {field}"
        );
    }
    for field in [
        "format",
        "claim_kind",
        "metric",
        "checker_profile",
        "target_profile",
        "composition",
        "error_category",
    ] {
        let mut changed = base.clone();
        set(&mut changed, field, Value::String("exact".into()));
        assert!(
            decode_request(&json::encode(&changed).unwrap()).is_err(),
            "changed {field}"
        );
    }
    for numerator in [
        "-1",
        "-0",
        "+1",
        "01",
        "1.0",
        "1e2",
        "",
        "170141183460469231731687303715884105728",
    ] {
        let mut changed = base.clone();
        set(
            &mut changed,
            "epsilon",
            Value::object([
                ("numerator", Value::String(numerator.into())),
                ("denominator_bits", Value::Number(0)),
            ]),
        );
        assert!(
            decode_request(&json::encode(&changed).unwrap()).is_err(),
            "numerator {numerator}"
        );
    }
    for invalid in [
        Value::object([
            ("numerator", Value::String("2".into())),
            ("denominator_bits", Value::Number(1)),
        ]),
        Value::object([
            ("numerator", Value::String("0".into())),
            ("denominator_bits", Value::Number(1)),
        ]),
        Value::object([
            ("numerator", Value::String("1".into())),
            ("denominator_bits", Value::Number(127)),
        ]),
        Value::String("open-budget".into()),
    ] {
        for field in ["epsilon", "majorants"] {
            let mut changed = base.clone();
            set(
                &mut changed,
                field,
                if field == "majorants" {
                    Value::Array(vec![invalid.clone()])
                } else {
                    invalid.clone()
                },
            );
            assert!(decode_request(&json::encode(&changed).unwrap()).is_err());
        }
    }
    let mut unknown = base.clone();
    set(&mut unknown, "accepted", Value::Bool(true));
    assert!(decode_request(&json::encode(&unknown).unwrap()).is_err());
    assert!(decode_request(b"{\"accepted\":true}").is_err());
    assert!(decode_request(&vec![b' '; MAX_FILE_BYTES + 1]).is_err());
    let mut mismatch = base;
    let Value::Object(fields) = &mut mismatch else {
        unreachable!()
    };
    let Value::Object(signature) = fields.get_mut("actual_signature").unwrap() else {
        unreachable!()
    };
    signature.insert(
        "input".into(),
        Value::object([
            ("tag", Value::String("bits".into())),
            ("width", Value::Number(0)),
        ]),
    );
    assert!(decode_request(&json::encode(&mismatch).unwrap()).is_err());
}

fn unit_bodies() -> (RawProgram, RawProgram) {
    let mut actual = RawProgram {
        quantum_inputs: vec![port(0, &[])],
        classical_inputs: vec![],
        operations: vec![
            RawOp::UnpackUnit { input: TokenId(0) },
            RawOp::Init0 {
                output: TokenId(1),
                wire: WireId(1),
            },
            RawOp::Gate {
                gate: SingleGate::H,
                input: TokenId(1),
                output: TokenId(2),
            },
            RawOp::MeasureZ {
                input: TokenId(2),
                output: ClassicalId(0),
            },
            RawOp::Init0 {
                output: TokenId(3),
                wire: WireId(2),
            },
            RawOp::Gate {
                gate: SingleGate::H,
                input: TokenId(3),
                output: TokenId(4),
            },
            RawOp::MeasureZ {
                input: TokenId(4),
                output: ClassicalId(1),
            },
            RawOp::ClassicalAnd {
                left: ClassicalId(0),
                right: ClassicalId(1),
                output: ClassicalId(2),
            },
        ],
        quantum_outputs: vec![],
        classical_outputs: vec![ClassicalId(2)],
        declared_effect: Effect::Observe,
    };
    let ideal = RawProgram {
        operations: vec![
            RawOp::UnpackUnit { input: TokenId(0) },
            RawOp::Init0 {
                output: TokenId(1),
                wire: WireId(1),
            },
            RawOp::MeasureZ {
                input: TokenId(1),
                output: ClassicalId(2),
            },
        ],
        ..actual.clone()
    };
    actual.declared_effect = Effect::Observe;
    (actual, ideal)
}

fn pair(
    kernel: &Kernel,
) -> (
    AcceptedProgram,
    AcceptedProgram,
    EngineeringInstrumentRequest,
) {
    let (actual, ideal) = unit_bodies();
    (
        kernel.verify(&actual).unwrap().into_program(),
        kernel.verify(&ideal).unwrap().into_program(),
        unit_request(),
    )
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn native_nonzero_and_zero_reports_keep_original_bytes_and_engineering_status() {
    let kernel = Kernel::selected(crate::edition::Edition::E2026).unwrap();
    let (actual, ideal, request) = pair(&kernel);
    let report = check_with_kernel(&kernel, &actual, &ideal, &request).unwrap();
    assert_eq!(report.actual_artifact(), actual.artifact());
    assert_eq!(report.ideal_artifact(), ideal.artifact());
    assert_eq!(report.request(), &request);
    assert!(report.exact_work() > 0);
    assert_eq!(report.claim_kind(), CLAIM_KIND);
    assert_eq!(report.metric(), METRIC);
    assert_eq!(report.composition(), COMPOSITION);
    assert_eq!(report.error_category(), ERROR_CATEGORY);
    assert_eq!(report.checker_profile(), CHECKER_PROFILE);
    assert_eq!(report.target_profile(), TARGET_PROFILE);
    assert!(report.instrument_bound_verified());
    let bytes = [b"\n".as_slice(), report.request_bytes(), b" \n".as_slice()].concat();
    let fresh = check_serialized_with_kernel(&kernel, actual.artifact(), &bytes).unwrap();
    assert_eq!(fresh.request_bytes(), bytes);
    assert_eq!(fresh.request(), &request);
    let zero = EngineeringInstrumentRequest::new(
        unit_signature(),
        unit_signature(),
        identity(),
        DyadicBound::new(0, 0).unwrap(),
        // Zero-weight hidden histories retain their public labels too.
        vec![DyadicBound::new(0, 0).unwrap(); 2],
    )
    .unwrap();
    let zero = check_with_kernel(&kernel, &ideal, &ideal, &zero).unwrap();
    assert_eq!(zero.claim_kind(), CLAIM_KIND);
    assert_eq!(zero.request().epsilon(), DyadicBound::new(0, 0).unwrap());
    let first = Subject::prepare(&kernel, &actual, &ideal, &request).unwrap();
    let other = Subject::prepare(&kernel, &actual, &ideal, &request).unwrap();
    assert_eq!(
        first
            .bind(Decision {
                context: report.context,
                subject: other,
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
fn native_refuses_tight_incomplete_reordered_witnesses_and_hidden_observation_labels() {
    let kernel = Kernel::selected(crate::edition::Edition::E2026).unwrap();
    let (actual, ideal, original) = pair(&kernel);
    for (epsilon, majorants) in [
        (DyadicBound::new(1, 2).unwrap(), original.majorants.clone()),
        (original.epsilon, vec![]),
        (original.epsilon, vec![DyadicBound::new(1, 2).unwrap()]),
        (original.epsilon, vec![DyadicBound::new(1, 2).unwrap(); 3]),
        (
            original.epsilon,
            vec![
                DyadicBound::new(1, 2).unwrap(),
                DyadicBound::new(0, 0).unwrap(),
            ],
        ),
        (
            DyadicBound::new(0, 0).unwrap(),
            vec![DyadicBound::new(0, 0).unwrap(); 2],
        ),
    ] {
        let changed = EngineeringInstrumentRequest {
            epsilon,
            majorants,
            ..original.clone()
        };
        assert!(check_with_kernel(&kernel, &actual, &ideal, &changed).is_err());
    }
    let mut bad_identity = original.clone();
    bad_identity.identity.sources = vec![("".into(), "source".into())];
    assert!(check_with_kernel(&kernel, &actual, &ideal, &bad_identity).is_err());
    let mut capacity = original.clone();
    capacity.epsilon = DyadicBound::new(i128::MAX, 0).unwrap();
    capacity.majorants = vec![DyadicBound::new(i128::MAX, 0).unwrap(); 2];
    assert!(check_with_kernel(&kernel, &actual, &ideal, &capacity).is_err());
    let mut wrong_owner = original.clone();
    let signature = InstrumentSignature::new(
        BasisType::Unit,
        vec![
            InstrumentResult::Pair,
            InstrumentResult::Bit,
            InstrumentResult::Quantum(BasisType::Unit),
        ],
    )
    .unwrap();
    wrong_owner.actual_signature = signature.clone();
    wrong_owner.expected_signature = signature;
    assert!(check_with_kernel(&kernel, &actual, &ideal, &wrong_owner).is_err());
    let (raw, _) = unit_bodies();
    let mut changed_output = raw.clone();
    changed_output.classical_outputs = vec![ClassicalId(0)];
    let changed_output = kernel.verify(&changed_output).unwrap().into_program();
    assert!(check_with_kernel(&kernel, &changed_output, &ideal, &original).is_err());
    for effect in [Effect::Unitary, Effect::Isometry] {
        let mut hidden = raw.clone();
        hidden.declared_effect = effect;
        assert!(kernel.verify(&hidden).is_err());
    }
    let mut lost_owner = raw.clone();
    lost_owner.operations.remove(0);
    assert!(kernel.verify(&lost_owner).is_err());
    let mut lost_output = raw;
    lost_output.classical_outputs = vec![ClassicalId(999)];
    assert!(kernel.verify(&lost_output).is_err());
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn original_dependency_meanings_are_reconstructed_instead_of_reusing_summaries() {
    use crate::contract::FunctionEvidence;
    use crate::ir::{CircuitAction, CircuitStep};
    let kernel = Kernel::selected(crate::edition::Edition::E2026).unwrap();
    let dependency = |gate| {
        let raw = RawProgram {
            quantum_inputs: vec![port(0, &[0])],
            classical_inputs: vec![],
            operations: vec![RawOp::Gate {
                gate,
                input: TokenId(0),
                output: TokenId(1),
            }],
            quantum_outputs: vec![TokenId(1)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        Arc::new(
            FunctionEvidence::check_retained_with_kernel(
                &kernel,
                BasisType::Bit,
                raw.clone(),
                raw,
                RetainedIdentity::Owned(identity()),
                &mut Budget::new(DEFAULT_EXACT_WORK),
            )
            .unwrap(),
        )
    };
    let make_actual = |evidence| {
        let (mut raw, _) = unit_bodies();
        raw.operations[2] = RawOp::ApplyUnitary {
            input: TokenId(1),
            output: TokenId(2),
            steps: vec![CircuitStep {
                controls: vec![],
                action: CircuitAction::Contract {
                    indices: vec![0],
                    evidence,
                    adjoint: false,
                },
            }],
        };
        kernel.verify(&raw).unwrap().into_program()
    };
    let actual = make_actual(dependency(SingleGate::H));
    let changed = make_actual(dependency(SingleGate::X));
    let (_, ideal, request) = pair(&kernel);
    check_with_kernel(&kernel, &actual, &ideal, &request).unwrap();
    assert!(check_with_kernel(&kernel, &changed, &ideal, &request).is_err());
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn residual_coherences_and_reference_correlations_are_not_probability_only_bounds() {
    let kernel = Kernel::selected(crate::edition::Edition::E2026).unwrap();
    let (mut actual, mut ideal) = unit_bodies();
    for raw in [&mut actual, &mut ideal] {
        raw.quantum_inputs = vec![port(0, &[0])];
        raw.operations.remove(0);
        raw.quantum_outputs = vec![TokenId(0)];
    }
    let actual = kernel.verify(&actual).unwrap().into_program();
    let ideal = kernel.verify(&ideal).unwrap().into_program();
    let signature = InstrumentSignature::new(
        BasisType::Bit,
        vec![
            InstrumentResult::Pair,
            InstrumentResult::Bit,
            InstrumentResult::Quantum(BasisType::Bit),
        ],
    )
    .unwrap();
    let mut majorants = vec![];
    for _ in 0..2 {
        for row in 0..2 {
            for col in 0..2 {
                for other_row in 0..2 {
                    for other_col in 0..2 {
                        majorants.push(
                            DyadicBound::new(
                                if row == col && other_row == other_col {
                                    1
                                } else {
                                    0
                                },
                                if row == col && other_row == other_col {
                                    2
                                } else {
                                    0
                                },
                            )
                            .unwrap(),
                        );
                    }
                }
            }
        }
    }
    let request = EngineeringInstrumentRequest::new(
        signature.clone(),
        signature.clone(),
        identity(),
        DyadicBound::new(2, 0).unwrap(),
        majorants,
    )
    .unwrap();
    check_with_kernel(&kernel, &actual, &ideal, &request).unwrap();
    let mut tight = request.clone();
    tight.epsilon = DyadicBound::new(1, 0).unwrap();
    assert!(check_with_kernel(&kernel, &actual, &ideal, &tight).is_err());
    let mut reordered = request.clone();
    reordered.majorants.swap(0, 1);
    assert!(check_with_kernel(&kernel, &actual, &ideal, &reordered).is_err());
    let constant = RawProgram {
        quantum_inputs: vec![port(0, &[0])],
        classical_inputs: vec![],
        operations: vec![
            RawOp::Init0 {
                output: TokenId(2),
                wire: WireId(2),
            },
            RawOp::MeasureZ {
                input: TokenId(2),
                output: ClassicalId(0),
            },
        ],
        quantum_outputs: vec![TokenId(0)],
        classical_outputs: vec![ClassicalId(0)],
        declared_effect: Effect::Observe,
    };
    let reset = RawProgram {
        operations: [
            vec![RawOp::Reset {
                input: TokenId(0),
                output: TokenId(1),
                fresh_wire: WireId(1),
            }],
            constant.operations.clone(),
        ]
        .concat(),
        quantum_outputs: vec![TokenId(1)],
        ..constant.clone()
    };
    let reset = kernel.verify(&reset).unwrap().into_program();
    let constant = kernel.verify(&constant).unwrap().into_program();
    let zero = EngineeringInstrumentRequest::new(
        signature.clone(),
        signature,
        identity(),
        DyadicBound::new(0, 0).unwrap(),
        vec![DyadicBound::new(0, 0).unwrap(); 32],
    )
    .unwrap();
    check_with_kernel(&kernel, &constant, &constant, &zero).unwrap();
    assert!(check_with_kernel(&kernel, &reset, &constant, &zero).is_err());
}

/// Decode only the test's already bounded view vocabulary, without production authority.
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
            let n = u64::from_le_bytes(bytes[*offset..*offset + 8].try_into().unwrap());
            *offset += 8;
            return View::Natural(n);
        }
        let n = u32::from_le_bytes(bytes[*offset..*offset + 4].try_into().unwrap()) as usize;
        *offset += 4;
        if tag == 4 {
            let s = std::str::from_utf8(&bytes[*offset..*offset + n])
                .unwrap()
                .to_owned();
            *offset += n;
            View::Text(s)
        } else {
            assert_eq!(tag, 5);
            View::Array((0..n).map(|_| read(bytes, offset)).collect())
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
fn every_view_context_and_original_graph_field_requires_fresh_native_agreement() {
    use crate::interchange::execution_view::{self, Value as View};
    let kernel = Kernel::selected(crate::edition::Edition::E2026).unwrap();
    let (actual, ideal, request) = pair(&kernel);
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
    for (slot, count) in [(1, 15), (2, 9), (3, 9)] {
        for field in 0..count {
            let mut mutation = description.clone();
            let View::Array(root) = &mut mutation else {
                unreachable!()
            };
            let View::Array(fields) = &mut root[slot] else {
                unreachable!()
            };
            assert_eq!(fields.len(), count);
            fields[field] = if matches!(fields[field], View::Null) {
                View::Natural(1234)
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
                "slot{slot}field{field}"
            );
        }
    }
    let mut stale = description;
    let View::Array(fields) = &mut stale else {
        unreachable!()
    };
    fields[2] = fields[3].clone();
    let stale = execution_view::encode(&stale).unwrap();
    let (stale, _) = super::super::native_packet::encode(
        crate::edition::Edition::E2026,
        original,
        Some(super::super::native_packet::View {
            graph: &stale,
            caller: None,
        }),
    )
    .unwrap();
    assert_eq!(
        runtime::check(&subject.checker, stale, crate::edition::Edition::E2026)
            .unwrap_err()
            .code,
        "decoded_view"
    );
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
