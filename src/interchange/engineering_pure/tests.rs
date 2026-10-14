// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::contract::exact::Exact;
use crate::ir::{BasisShape, TokenId, WireId};

fn port(token: u32, wires: &[u32]) -> QuantumPort {
    QuantumPort {
        token: TokenId(token),
        wires: wires.iter().copied().map(WireId).collect(),
        shape: BasisShape {
            bits: wires.len() as u8,
        },
    }
}

fn request() -> EngineeringPureRequest {
    EngineeringPureRequest::new(
        PureBoundary::new(BasisType::Bit, BasisType::Bit, port(0, &[0]), port(1, &[0])).unwrap(),
        Matrix::new(
            2,
            2,
            vec![Exact::one(), Exact::zero(), Exact::zero(), Exact::phase(1)],
        )
        .unwrap(),
        PureBoundary::new(BasisType::Bit, BasisType::Bit, port(4, &[0]), port(4, &[0])).unwrap(),
        Matrix::identity(2).unwrap(),
        DyadicBound::new(7, 3).unwrap(),
    )
    .unwrap()
}

#[test]
fn epsilon_is_finite_nonnegative_and_canonical_without_promotion() {
    for (numerator, exponent) in [(0, 0), (7, 3), (1, 126), (i128::MAX, 0)] {
        let bound = DyadicBound::new(numerator, exponent).unwrap();
        assert_eq!(bound.numerator(), numerator);
        assert_eq!(bound.denominator_bits(), exponent);
    }
    for (numerator, exponent) in [(-1, 0), (0, 1), (2, 1), (1, 127), (0, u32::MAX)] {
        assert!(DyadicBound::new(numerator, exponent).is_err());
    }
}

#[test]
fn request_decoding_retains_full_types_independent_ports_and_exact_matrices() {
    let original = request();
    let artifact = "{\"untouched\":\"escaped\\nvalue\"}\n";
    let bytes = encode_request(&original, artifact.as_bytes()).unwrap();
    let (decoded, expected) = decode_request(&bytes).unwrap();
    assert_eq!(decoded, original);
    assert_eq!(expected.as_bytes(), artifact.as_bytes());
    assert_ne!(decoded.actual_meaning(), decoded.ideal_meaning());
    assert_ne!(
        decoded.actual_boundary().input(),
        decoded.ideal_boundary().input()
    );

    let actual = original.actual_boundary.clone();
    let different_tree = PureBoundary::new(
        BasisType::Bits(1),
        BasisType::Bit,
        port(4, &[0]),
        port(4, &[0]),
    )
    .unwrap();
    assert!(
        EngineeringPureRequest::new(
            actual,
            original.actual_meaning.clone(),
            different_tree,
            original.ideal_meaning.clone(),
            original.epsilon,
        )
        .is_err()
    );
    let mismatched_shape = Matrix::identity(1).unwrap();
    assert!(
        EngineeringPureRequest::new(
            original.actual_boundary.clone(),
            mismatched_shape,
            original.ideal_boundary.clone(),
            original.ideal_meaning.clone(),
            original.epsilon,
        )
        .is_err()
    );
}

#[test]
fn request_decoder_rejects_missing_unknown_and_cross_kind_contexts() {
    let bytes = encode_request(&request(), b"{}").unwrap();
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
        "domain",
        "codomain",
        "actual",
        "ideal",
        "epsilon",
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
        let Value::Object(fields) = &mut changed else {
            unreachable!()
        };
        fields.insert(field.into(), Value::String("exact".into()));
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
        let Value::Object(fields) = &mut changed else {
            unreachable!()
        };
        let Value::Object(epsilon) = fields.get_mut("epsilon").unwrap() else {
            unreachable!()
        };
        epsilon.insert("numerator".into(), Value::String(numerator.into()));
        assert!(
            decode_request(&json::encode(&changed).unwrap()).is_err(),
            "numerator {numerator}"
        );
    }
    let mut unknown = base;
    let Value::Object(fields) = &mut unknown else {
        unreachable!()
    };
    fields.insert("accepted".into(), Value::Bool(true));
    assert!(decode_request(&json::encode(&unknown).unwrap()).is_err());
    assert!(decode_request(b"{\"accepted\":true}").is_err());
    assert!(decode_request(&vec![b' '; MAX_FILE_BYTES + 1]).is_err());
}

fn pair(kernel: &Kernel) -> (AcceptedProgram, AcceptedProgram, EngineeringPureRequest) {
    use crate::ir::{Effect, RawOp, RawProgram, SingleGate};
    let request = request();
    let actual = RawProgram {
        quantum_inputs: vec![request.actual_boundary.input().clone()],
        classical_inputs: vec![],
        operations: vec![RawOp::Gate {
            gate: SingleGate::T,
            input: TokenId(0),
            output: TokenId(1),
        }],
        quantum_outputs: vec![TokenId(1)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    let ideal = RawProgram {
        quantum_inputs: vec![request.ideal_boundary.input().clone()],
        classical_inputs: vec![],
        operations: vec![],
        quantum_outputs: vec![TokenId(4)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    let interface = super::super::RootInterface {
        input: BasisType::Bit,
        output: BasisType::Bit,
    };
    (
        kernel
            .check_raw(&actual, Some(&interface), Version::V2, None)
            .unwrap()
            .into_program(),
        kernel
            .check_raw(&ideal, Some(&interface), Version::V2, None)
            .unwrap()
            .into_program(),
        request,
    )
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn native_bound_retains_original_bodies_and_zero_stays_engineering() {
    let kernel = Kernel::selected().unwrap();
    let (actual, ideal, request) = pair(&kernel);
    let report = check_with_kernel(&kernel, &actual, &ideal, &request).unwrap();
    assert_eq!(report.actual_artifact(), actual.artifact());
    assert_eq!(report.ideal_artifact(), ideal.artifact());
    assert_eq!(report.request(), &request);
    assert_eq!(report.claim_kind(), "engineering");
    assert_eq!(report.metric(), METRIC);
    assert_eq!(report.target_profile(), TARGET_PROFILE);
    assert_eq!(report.composition(), COMPOSITION);
    assert_eq!(report.error_category(), ERROR_CATEGORY);
    assert!(report.exact_work() > 0);

    let mut original_bytes = vec![b'\n'];
    original_bytes.extend_from_slice(report.request_bytes());
    original_bytes.extend_from_slice(b" \n");
    let replay = check_serialized_with_kernel(&kernel, actual.artifact(), &original_bytes).unwrap();
    assert_eq!(replay.request_bytes(), original_bytes);
    assert_eq!(replay.actual_artifact(), actual.artifact());
    assert_eq!(replay.ideal_artifact(), ideal.artifact());
    assert_eq!(replay.request(), &request);

    let identical = EngineeringPureRequest::new(
        request.ideal_boundary.clone(),
        request.ideal_meaning.clone(),
        request.ideal_boundary.clone(),
        request.ideal_meaning.clone(),
        DyadicBound::new(0, 0).unwrap(),
    )
    .unwrap();
    let zero = check_with_kernel(&kernel, &ideal, &ideal, &identical).unwrap();
    assert_eq!(zero.claim_kind(), "engineering");
    assert_eq!(zero.request().epsilon(), DyadicBound::new(0, 0).unwrap());

    let one = Subject::prepare(&kernel, &actual, &ideal, &request).unwrap();
    let other = Subject::prepare(&kernel, &actual, &ideal, &request).unwrap();
    assert_eq!(
        one.bind(Decision {
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
fn native_refuses_tight_bounds_stale_meanings_phase_and_owner_substitution() {
    let kernel = Kernel::selected().unwrap();
    let (actual, ideal, original) = pair(&kernel);
    let mut changed = original.clone();
    changed.epsilon = DyadicBound::new(1, 1).unwrap();
    assert!(check_with_kernel(&kernel, &actual, &ideal, &changed).is_err());
    changed.epsilon = DyadicBound::new(10, 0).unwrap();
    changed.actual_meaning = original.ideal_meaning.clone();
    assert!(check_with_kernel(&kernel, &actual, &ideal, &changed).is_err());
    changed = original.clone();
    changed.epsilon = DyadicBound::new(10, 0).unwrap();
    changed.ideal_meaning = original.actual_meaning.clone();
    assert!(check_with_kernel(&kernel, &actual, &ideal, &changed).is_err());
    changed = original.clone();
    changed.actual_meaning = Matrix::new(
        2,
        2,
        vec![Exact::one(), Exact::zero(), Exact::zero(), Exact::phase(-1)],
    )
    .unwrap();
    assert!(check_with_kernel(&kernel, &actual, &ideal, &changed).is_err());
    changed = original.clone();
    changed.actual_boundary =
        PureBoundary::new(BasisType::Bit, BasisType::Bit, port(0, &[1]), port(1, &[1])).unwrap();
    assert!(check_with_kernel(&kernel, &actual, &ideal, &changed).is_err());
    changed = original.clone();
    changed.actual_boundary = PureBoundary::new(
        BasisType::Bits(1),
        BasisType::Bits(1),
        port(0, &[0]),
        port(1, &[0]),
    )
    .unwrap();
    changed.ideal_boundary = PureBoundary::new(
        BasisType::Bits(1),
        BasisType::Bits(1),
        port(4, &[0]),
        port(4, &[0]),
    )
    .unwrap();
    assert!(check_with_kernel(&kernel, &actual, &ideal, &changed).is_err());
}

/// Test-only decoder for the already bounded QDV1 value vocabulary. It never
/// constructs a production request, graph or receipt.
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
fn every_typed_context_and_both_original_graph_fields_are_compared_by_lean() {
    use crate::interchange::execution_view::{self, Value as View};
    let kernel = Kernel::selected().unwrap();
    let (actual, ideal, request) = pair(&kernel);
    let subject = Subject::prepare(&kernel, &actual, &ideal, &request).unwrap();
    let packet = subject.packet().unwrap();
    runtime::check(&subject.checker, packet.clone()).unwrap();
    let original_len = u32::from_le_bytes(packet[8..12].try_into().unwrap()) as usize;
    let graph_len = u32::from_le_bytes(packet[12..16].try_into().unwrap()) as usize;
    let graph_start = 24 + original_len;
    let original = &packet[24..graph_start];
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
            fields[field] = View::Null;
            let graph = execution_view::encode(&mutation).unwrap();
            let (packet, _) = crate::interchange::native_packet::encode(
                original,
                Some(crate::interchange::native_packet::View {
                    graph: &graph,
                    caller: None,
                }),
            )
            .unwrap();
            assert_eq!(
                runtime::check(&subject.checker, packet).unwrap_err().code,
                "decoded_view",
                "slot {slot} field {field}"
            );
        }
    }
    // Engineering cannot authorize inspection or caller-alias scopes.
    let (inspection, _) = crate::interchange::native_packet::encode(original, None).unwrap();
    assert!(runtime::check(&subject.checker, inspection).is_err());
    let graph = &packet[graph_start..graph_start + graph_len];
    let (caller, _) = crate::interchange::native_packet::encode(
        original,
        Some(crate::interchange::native_packet::View {
            graph,
            caller: Some((graph, &[])),
        }),
    )
    .unwrap();
    assert!(runtime::check(&subject.checker, caller).is_err());
    assert!(runtime::check(&subject.checker, original.to_vec()).is_err());
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn hidden_observation_reset_and_discard_cannot_receive_pure_engineering_labels() {
    use crate::ir::{ClassicalId, Effect, RawOp, RawProgram};
    let kernel = Kernel::selected().unwrap();
    let ideal_raw = RawProgram {
        quantum_inputs: vec![port(4, &[])],
        classical_inputs: vec![],
        operations: vec![],
        quantum_outputs: vec![TokenId(4)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    let ideal = kernel.verify(&ideal_raw).unwrap().into_program();
    for hidden in [
        vec![RawOp::MeasureZ {
            input: TokenId(1),
            output: ClassicalId(0),
        }],
        vec![
            RawOp::Reset {
                input: TokenId(1),
                output: TokenId(3),
                fresh_wire: WireId(1),
            },
            RawOp::Discard { input: TokenId(3) },
        ],
        vec![RawOp::Discard { input: TokenId(1) }],
    ] {
        let mut operations = vec![
            RawOp::UnpackUnit { input: TokenId(0) },
            RawOp::Init0 {
                output: TokenId(1),
                wire: WireId(0),
            },
        ];
        operations.extend(hidden);
        operations.push(RawOp::PackUnit { output: TokenId(2) });
        let mut raw = RawProgram {
            quantum_inputs: vec![port(0, &[])],
            classical_inputs: vec![],
            operations,
            quantum_outputs: vec![TokenId(2)],
            classical_outputs: vec![],
            declared_effect: Effect::Observe,
        };
        let actual = kernel.verify(&raw).unwrap().into_program();
        assert!(actual.raw().classical_outputs.is_empty());
        let request = EngineeringPureRequest::new(
            PureBoundary::new(BasisType::Unit, BasisType::Unit, port(0, &[]), port(2, &[]))
                .unwrap(),
            Matrix::identity(1).unwrap(),
            PureBoundary::new(BasisType::Unit, BasisType::Unit, port(4, &[]), port(4, &[]))
                .unwrap(),
            Matrix::identity(1).unwrap(),
            DyadicBound::new(10, 0).unwrap(),
        )
        .unwrap();
        assert!(check_with_kernel(&kernel, &actual, &ideal, &request).is_err());
        let request_bytes = encode_request(&request, ideal.artifact()).unwrap();
        let graph = crate::interchange::execution_view::finite::engineering_pure::complete(
            &request, &ideal, &actual,
        )
        .unwrap();
        for label in [Effect::Unitary, Effect::Isometry] {
            raw.declared_effect = label;
            let artifact =
                crate::interchange::native::Proposal::from_raw(&raw, None, Version::V2, None)
                    .unwrap();
            // Submit the falsely labelled original bytes directly as well as
            // through the public serialized API. The independent pure/effect
            // gate must reject before any decoded-view agreement could help.
            let mut original = b"QLV1".to_vec();
            original.extend_from_slice(&(artifact.artifact().len() as u32).to_le_bytes());
            original.extend_from_slice(&(request_bytes.len() as u32).to_le_bytes());
            original.extend_from_slice(artifact.artifact());
            original.extend_from_slice(&request_bytes);
            let (packet, _) = crate::interchange::native_packet::encode(
                &original,
                Some(crate::interchange::native_packet::View {
                    graph: &graph,
                    caller: None,
                }),
            )
            .unwrap();
            let failure = runtime::check(kernel.checker_path(), packet).unwrap_err();
            assert_ne!(failure.code, "decoded_view");
            assert!(
                check_serialized_with_kernel(&kernel, artifact.artifact(), &request_bytes).is_err()
            );
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn rectangular_original_preparations_are_compared_at_their_distinct_ports() {
    use crate::ir::{Effect, RawOp, RawProgram, SingleGate};
    let kernel = Kernel::selected().unwrap();
    let actual_boundary =
        PureBoundary::new(BasisType::Unit, BasisType::Bit, port(0, &[]), port(2, &[7])).unwrap();
    let ideal_boundary =
        PureBoundary::new(BasisType::Unit, BasisType::Bit, port(4, &[]), port(5, &[9])).unwrap();
    let actual_raw = RawProgram {
        quantum_inputs: vec![actual_boundary.input().clone()],
        classical_inputs: vec![],
        operations: vec![
            RawOp::UnpackUnit { input: TokenId(0) },
            RawOp::Init0 {
                output: TokenId(1),
                wire: WireId(7),
            },
            RawOp::Gate {
                gate: SingleGate::H,
                input: TokenId(1),
                output: TokenId(2),
            },
        ],
        quantum_outputs: vec![TokenId(2)],
        classical_outputs: vec![],
        declared_effect: Effect::Isometry,
    };
    let ideal_raw = RawProgram {
        quantum_inputs: vec![ideal_boundary.input().clone()],
        classical_inputs: vec![],
        operations: vec![
            RawOp::UnpackUnit { input: TokenId(4) },
            RawOp::Init0 {
                output: TokenId(5),
                wire: WireId(9),
            },
        ],
        quantum_outputs: vec![TokenId(5)],
        classical_outputs: vec![],
        declared_effect: Effect::Isometry,
    };
    let interface = crate::interchange::RootInterface {
        input: BasisType::Unit,
        output: BasisType::Bit,
    };
    let actual = kernel
        .check_raw(&actual_raw, Some(&interface), Version::V2, None)
        .unwrap()
        .into_program();
    let ideal = kernel
        .check_raw(&ideal_raw, Some(&interface), Version::V2, None)
        .unwrap()
        .into_program();
    let request = EngineeringPureRequest::new(
        actual_boundary,
        Matrix::new(2, 1, vec![Exact::inv_sqrt2(); 2]).unwrap(),
        ideal_boundary,
        Matrix::new(2, 1, vec![Exact::one(), Exact::zero()]).unwrap(),
        DyadicBound::new(7, 3).unwrap(),
    )
    .unwrap();
    let report = check_with_kernel(&kernel, &actual, &ideal, &request).unwrap();
    assert_eq!(report.request().actual_meaning().rows(), 2);
    assert_eq!(report.request().actual_meaning().cols(), 1);
    let mut changed = request;
    changed.epsilon = DyadicBound::new(1, 1).unwrap();
    assert!(check_with_kernel(&kernel, &actual, &ideal, &changed).is_err());
}
