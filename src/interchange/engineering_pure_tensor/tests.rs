// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::contract::exact::Exact;
use crate::ir::{BasisShape, Effect, RawOp, RawProgram, SingleGate, TokenId, WireId};

fn port(token: u32, wires: &[u32]) -> QuantumPort {
    QuantumPort {
        token: TokenId(token),
        wires: wires.iter().copied().map(WireId).collect(),
        shape: BasisShape {
            bits: wires.len() as u8,
        },
    }
}

fn pair_type() -> BasisType {
    BasisType::Pair(Box::new(BasisType::Bit), Box::new(BasisType::Bit))
}

fn single_request(t: bool, epsilon: DyadicBound) -> EngineeringPureRequest {
    EngineeringPureRequest::new(
        PureBoundary::new(
            BasisType::Bit,
            BasisType::Bit,
            port(0, &[0]),
            port(u32::from(t), &[0]),
        )
        .unwrap(),
        Matrix::new(
            2,
            2,
            vec![
                Exact::one(),
                Exact::zero(),
                Exact::zero(),
                if t { Exact::phase(1) } else { Exact::one() },
            ],
        )
        .unwrap(),
        PureBoundary::new(BasisType::Bit, BasisType::Bit, port(0, &[0]), port(0, &[0])).unwrap(),
        Matrix::identity(2).unwrap(),
        epsilon,
    )
    .unwrap()
}

fn request() -> EngineeringPureTensorRequest {
    let left = single_request(false, DyadicBound::new(0, 0).unwrap());
    let right = single_request(true, DyadicBound::new(7, 3).unwrap());
    let actual = left
        .actual_meaning()
        .tensor(right.actual_meaning(), &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    let parent = EngineeringPureRequest::new(
        PureBoundary::new(pair_type(), pair_type(), port(0, &[0, 1]), port(4, &[0, 1])).unwrap(),
        actual,
        PureBoundary::new(pair_type(), pair_type(), port(0, &[0, 1]), port(0, &[0, 1])).unwrap(),
        Matrix::identity(4).unwrap(),
        right.epsilon(),
    )
    .unwrap();
    EngineeringPureTensorRequest::new(parent, left, right).unwrap()
}

#[test]
fn typed_request_retains_component_budgets_and_rejects_equal_width_parent_tree_substitution() {
    let request = request();
    let artifacts = [b"{}".as_slice(); 6];
    let bytes = encode_request(&request, artifacts).unwrap();
    let (decoded, embedded) = decode_request(&bytes).unwrap();
    assert_eq!(decoded, request);
    assert_eq!(embedded, ["{}"; 5]);
    assert_ne!(request.left().epsilon(), request.right().epsilon());
    assert_eq!(request.parent().epsilon(), request.right().epsilon());
    for (domain, codomain) in [
        (BasisType::Bits(2), pair_type()),
        (pair_type(), BasisType::Bits(2)),
    ] {
        let parent = EngineeringPureRequest::new(
            PureBoundary::new(
                domain.clone(),
                codomain.clone(),
                port(0, &[0, 1]),
                port(4, &[0, 1]),
            )
            .unwrap(),
            request.parent().actual_meaning().clone(),
            PureBoundary::new(domain, codomain, port(0, &[0, 1]), port(0, &[0, 1])).unwrap(),
            request.parent().ideal_meaning().clone(),
            request.parent().epsilon(),
        )
        .unwrap();
        assert!(
            EngineeringPureTensorRequest::new(
                parent,
                request.left().clone(),
                request.right().clone()
            )
            .is_err()
        );
    }
}

#[test]
fn strict_tensor_request_rejects_missing_extra_cross_kind_and_open_budget_data() {
    let bytes = encode_request(&request(), [b"{}".as_slice(); 6]).unwrap();
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
        let mut wrong = base.clone();
        let Value::Object(fields) = &mut wrong else {
            unreachable!()
        };
        fields.insert(field.into(), Value::String("single-component-v1".into()));
        assert!(
            decode_request(&json::encode(&wrong).unwrap()).is_err(),
            "{field}"
        );
    }
    for side in ["left", "right"] {
        let Value::Object(component) = base.field(side).unwrap() else {
            unreachable!()
        };
        for field in component.keys() {
            let mut missing = base.clone();
            let Value::Object(fields) = &mut missing else {
                unreachable!()
            };
            let Value::Object(fields) = fields.get_mut(side).unwrap() else {
                unreachable!()
            };
            fields.remove(field);
            assert!(
                decode_request(&json::encode(&missing).unwrap()).is_err(),
                "{side}.{field}"
            );
        }
    }
    for location in [None, Some("left"), Some("right")] {
        for numerator in [
            "-1",
            "01",
            "1.0",
            "1e2",
            "n",
            "170141183460469231731687303715884105728",
        ] {
            let mut changed = base.clone();
            let Value::Object(fields) = &mut changed else {
                unreachable!()
            };
            let fields = if let Some(side) = location {
                let Value::Object(fields) = fields.get_mut(side).unwrap() else {
                    unreachable!()
                };
                fields
            } else {
                fields
            };
            let Value::Object(epsilon) = fields.get_mut("epsilon").unwrap() else {
                unreachable!()
            };
            epsilon.insert("numerator".into(), Value::String(numerator.into()));
            assert!(
                decode_request(&json::encode(&changed).unwrap()).is_err(),
                "{location:?}.{numerator}"
            );
        }
    }
    let mut extra = base;
    let Value::Object(fields) = &mut extra else {
        unreachable!()
    };
    fields.insert("accepted".into(), Value::Bool(true));
    assert!(decode_request(&json::encode(&extra).unwrap()).is_err());
    assert!(decode_request(&vec![b' '; MAX_FILE_BYTES + 1]).is_err());
}

fn programs(kernel: &Kernel) -> [AcceptedProgram; 6] {
    let single = |t: bool| RawProgram {
        quantum_inputs: vec![port(0, &[0])],
        classical_inputs: vec![],
        operations: if t {
            vec![RawOp::Gate {
                gate: SingleGate::T,
                input: TokenId(0),
                output: TokenId(1),
            }]
        } else {
            vec![]
        },
        quantum_outputs: vec![TokenId(u32::from(t))],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    let parent_actual = RawProgram {
        quantum_inputs: vec![port(0, &[0, 1])],
        classical_inputs: vec![],
        operations: vec![
            RawOp::Split {
                input: TokenId(0),
                left: TokenId(1),
                right: TokenId(2),
                left_bits: 1,
            },
            RawOp::Gate {
                gate: SingleGate::T,
                input: TokenId(2),
                output: TokenId(3),
            },
            RawOp::Join {
                left: TokenId(1),
                right: TokenId(3),
                output: TokenId(4),
            },
        ],
        quantum_outputs: vec![TokenId(4)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    let parent_ideal = RawProgram {
        quantum_inputs: vec![port(0, &[0, 1])],
        classical_inputs: vec![],
        operations: vec![],
        quantum_outputs: vec![TokenId(0)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    [
        parent_actual,
        parent_ideal,
        single(false),
        single(false),
        single(true),
        single(false),
    ]
    .into_iter()
    .enumerate()
    .map(|(index, raw)| {
        let basis = if index < 2 {
            pair_type()
        } else {
            BasisType::Bit
        };
        kernel
            .check_raw(
                &raw,
                Some(&super::super::RootInterface {
                    input: basis.clone(),
                    output: basis,
                }),
                Version::V2,
                None,
            )
            .unwrap()
            .into_program()
    })
    .collect::<Vec<_>>()
    .try_into()
    .unwrap()
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn native_tensor_composes_component_bounds_without_parent_frobenius() {
    let kernel = Kernel::selected().unwrap();
    let programs = programs(&kernel);
    let request = request();
    assert!(
        super::super::engineering_pure::check_with_kernel(
            &kernel,
            &programs[0],
            &programs[1],
            request.parent()
        )
        .is_err()
    );
    let report = check_with_kernel(&kernel, programs.each_ref(), &request).unwrap();
    assert_eq!(report.request(), &request);
    assert_eq!(
        report.artifacts(),
        programs.each_ref().map(AcceptedProgram::artifact)
    );
    assert_eq!(report.claim_kind(), CLAIM_KIND);
    assert_eq!(report.metric(), METRIC);
    assert_eq!(report.checker_profile(), CHECKER_PROFILE);
    assert_eq!(report.target_profile(), TARGET_PROFILE);
    assert_eq!(report.composition(), COMPOSITION);
    assert_eq!(report.error_category(), ERROR_CATEGORY);
    assert!(report.exact_work() > 0);
    let original_bytes = [b"\n ".as_slice(), report.request_bytes(), b" \n".as_slice()].concat();
    let replay =
        check_serialized_with_kernel(&kernel, programs[0].artifact(), &original_bytes).unwrap();
    assert_eq!(replay.request_bytes(), original_bytes);
    assert_eq!(replay.artifacts(), report.artifacts());
    let subject = Subject::prepare(&kernel, programs.each_ref(), &request).unwrap();
    let other = Subject::prepare(&kernel, programs.each_ref(), &request).unwrap();
    assert_eq!(
        subject
            .bind(Decision {
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
fn changed_parent_component_total_budget_or_original_invalidates_the_claim() {
    let kernel = Kernel::selected().unwrap();
    let programs = programs(&kernel);
    let request = request();
    for epsilon in [
        DyadicBound::new(0, 0).unwrap(),
        DyadicBound::new(1, 0).unwrap(),
    ] {
        let parent = request.parent();
        let changed = EngineeringPureTensorRequest::new(
            EngineeringPureRequest::new(
                parent.actual_boundary().clone(),
                parent.actual_meaning().clone(),
                parent.ideal_boundary().clone(),
                parent.ideal_meaning().clone(),
                epsilon,
            )
            .unwrap(),
            request.left().clone(),
            request.right().clone(),
        )
        .unwrap();
        assert!(check_with_kernel(&kernel, programs.each_ref(), &changed).is_err());
    }
    let right = request.right();
    let changed = EngineeringPureTensorRequest::new(
        request.parent().clone(),
        request.left().clone(),
        EngineeringPureRequest::new(
            right.actual_boundary().clone(),
            right.actual_meaning().clone(),
            right.ideal_boundary().clone(),
            right.ideal_meaning().clone(),
            DyadicBound::new(1, 1).unwrap(),
        )
        .unwrap(),
    )
    .unwrap();
    assert!(check_with_kernel(&kernel, programs.each_ref(), &changed).is_err());
    let mut refs = programs.each_ref();
    refs[4] = &programs[5];
    assert!(check_with_kernel(&kernel, refs, &request).is_err());
    let parent = request.parent();
    let swapped = request
        .right()
        .actual_meaning()
        .tensor(
            request.left().actual_meaning(),
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .unwrap();
    let wrong_axis = EngineeringPureTensorRequest::new(
        EngineeringPureRequest::new(
            parent.actual_boundary().clone(),
            swapped,
            parent.ideal_boundary().clone(),
            parent.ideal_meaning().clone(),
            parent.epsilon(),
        )
        .unwrap(),
        request.left().clone(),
        request.right().clone(),
    )
    .unwrap();
    assert!(check_with_kernel(&kernel, programs.each_ref(), &wrong_axis).is_err());
    let zero_parent = EngineeringPureRequest::new(
        parent.ideal_boundary().clone(),
        parent.ideal_meaning().clone(),
        parent.ideal_boundary().clone(),
        parent.ideal_meaning().clone(),
        DyadicBound::new(0, 0).unwrap(),
    )
    .unwrap();
    let zero_component = single_request(false, DyadicBound::new(0, 0).unwrap());
    let zero_request =
        EngineeringPureTensorRequest::new(zero_parent, zero_component.clone(), zero_component)
            .unwrap();
    let zero = check_with_kernel(
        &kernel,
        [
            &programs[1],
            &programs[1],
            &programs[2],
            &programs[3],
            &programs[5],
            &programs[5],
        ],
        &zero_request,
    )
    .unwrap();
    assert_eq!(zero.claim_kind(), CLAIM_KIND);
    assert_eq!(
        zero.request().parent().epsilon(),
        DyadicBound::new(0, 0).unwrap()
    );
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
fn lean_compares_every_typed_tensor_context_and_all_six_original_graphs() {
    use crate::interchange::execution_view::{self, Value as View};
    let kernel = Kernel::selected().unwrap();
    let programs = programs(&kernel);
    let request = request();
    let subject = Subject::prepare(&kernel, programs.each_ref(), &request).unwrap();
    let packet = subject.packet().unwrap();
    runtime::check(&subject.checker, packet.clone()).unwrap();
    let original_len = u32::from_le_bytes(packet[8..12].try_into().unwrap()) as usize;
    let graph_len = u32::from_le_bytes(packet[12..16].try_into().unwrap()) as usize;
    let graph_start = 24 + original_len;
    let original = &packet[24..graph_start];
    let description = view_value(&packet[graph_start..graph_start + graph_len]);
    for (slot, count) in [(1, 17), (2, 9), (3, 9), (4, 9), (5, 9), (6, 9), (7, 9)] {
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
            let (packet, _) = super::super::native_packet::encode(
                original,
                Some(super::super::native_packet::View {
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
    let (inspection, _) = super::super::native_packet::encode(original, None).unwrap();
    assert!(runtime::check(&subject.checker, inspection).is_err());
    let graph = &packet[graph_start..graph_start + graph_len];
    let (caller, _) = super::super::native_packet::encode(
        original,
        Some(super::super::native_packet::View {
            graph,
            caller: Some((graph, &[])),
        }),
    )
    .unwrap();
    assert!(runtime::check(&subject.checker, caller).is_err());
    assert!(runtime::check(&subject.checker, original.to_vec()).is_err());
}
