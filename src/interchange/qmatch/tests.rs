//! Strict data failures, original identities and complete interface retention.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::interchange::carrier::{Origin, Owner};
use crate::ir::{BasisShape, Effect, QuantumPort, TokenId};
use std::sync::Arc;

fn owner(token: u32) -> Owner {
    Owner {
        port: QuantumPort {
            token: TokenId(token),
            wires: vec![],
            shape: BasisShape { bits: 0 },
        },
        basis: vec![Atom::Unit],
    }
}

fn request() -> Request {
    let interface = Interface {
        inputs: vec![owner(10), owner(11)],
        outputs: vec![owner(14), owner(15)],
        public_effect: Effect::Unitary,
    };
    Request {
        source: SourceSite {
            module: "same".into(),
            function: "choose".into(),
        },
        positions: vec![Position {
            offset: 137,
            start: 0,
            count: 3,
        }],
        sites: vec![Site {
            attached: interface.clone(),
            required: interface,
            position: Position {
                offset: 137,
                start: 0,
                count: 3,
            },
            arms: vec![Arm {
                evidence: 0,
                controlled: 2,
            }],
        }],
    }
}

fn changed(mut change: impl FnMut(&mut std::collections::BTreeMap<String, Value>)) -> Vec<u8> {
    let Value::Object(mut value) = json::parse(&request().encode().unwrap()).unwrap() else {
        unreachable!()
    };
    change(&mut value);
    json::encode(&Value::Object(value)).unwrap()
}

#[test]
fn complete_nominal_trees_effects_and_zero_width_positions_survive_transport() {
    let mut request = request();
    request.sites[0].attached.inputs[0].basis = vec![Atom::Enum(
        Arc::new(Origin {
            module: "labels".into(),
            declaration: "Tri".into(),
            source: "pub enum Tri { A,B,C }".into(),
        }),
        vec!["A".into(), "B".into(), "C".into()],
    )];
    request.sites[0].required.outputs[1].basis = vec![Atom::Tuple(2), Atom::Unit, Atom::Bits(0)];
    request.sites[0].required.public_effect = Effect::Observe;
    // Deliberately inconsistent proposed data remains data: only Lean can
    // accept semantic interfaces or prevent public-effect sharpening.
    let decoded = Request::decode(&request.encode().unwrap()).unwrap();
    assert_eq!(decoded, request);
    assert_ne!(
        decoded.sites[0].attached.inputs[0],
        decoded.sites[0].attached.inputs[1]
    );
    assert_eq!(decoded.sites[0].required.public_effect, Effect::Observe);
}

#[test]
fn proposed_success_labels_logical_matrices_roots_and_implementations_refuse() {
    for field in ["accepted", "label", "logical", "roots", "implementation"] {
        let bytes = changed(|value| {
            value.insert(field.into(), Value::Bool(true));
        });
        assert!(Request::decode(&bytes).is_err(), "unexpected field {field}");
    }
}

#[test]
fn profile_format_version_and_required_fields_are_exact() {
    for (key, value) in [
        ("format", text("qleisli.carrier-request")),
        ("profile", text("finite-carrier-pure-v1")),
        ("profile", text("finite-source-qmatch-named-v1")),
        ("profile", text("finite-source-qmatch-named-v2")),
        ("profile", text("finite-source-qmatch-named-v3")),
        ("version", n(1)),
        ("version", n(2)),
        ("version", n(3)),
    ] {
        let bytes = changed(|fields| {
            fields.insert(key.into(), value.clone());
        });
        assert!(Request::decode(&bytes).is_err());
    }
    for required in ["source", "positions"] {
        assert!(
            Request::decode(&changed(|fields| {
                fields.remove(required);
            }))
            .is_err()
        );
    }
}

#[test]
fn all_event_positions_retain_postorder_without_inventing_arm_requests() {
    let mut proposed = request();
    proposed.positions = (0..130)
        .map(|index| Position {
            offset: 300 - index,
            start: index,
            count: 1,
        })
        .collect();
    let decoded = Request::decode(&proposed.encode().unwrap()).unwrap();
    assert_eq!(decoded.positions, proposed.positions);
    assert_eq!(decoded.sites, proposed.sites);
    assert_eq!(decoded.sites.len(), 1);
    // Coverage is a native source judgment, including the empty proposal.
    proposed.positions.clear();
    assert!(
        Request::decode(&proposed.encode().unwrap())
            .unwrap()
            .positions
            .is_empty()
    );
}

#[test]
fn every_context_position_field_is_unsigned_u32_and_has_no_extra_authority() {
    let mut proposed = request();
    proposed.positions[0] = Position {
        offset: u32::MAX,
        start: u32::MAX,
        count: u32::MAX,
    };
    assert_eq!(
        Request::decode(&proposed.encode().unwrap()).unwrap(),
        proposed
    );
    for field in ["offset", "start", "count"] {
        for invalid in [Value::Number(u64::from(u32::MAX) + 1), text("-1")] {
            let bytes = changed(|fields| {
                fields.insert(
                    "positions".into(),
                    Value::Array(vec![Value::object([
                        ("offset", n(1)),
                        ("start", n(0)),
                        ("count", n(1)),
                        (field, invalid.clone()),
                    ])]),
                );
            });
            assert!(Request::decode(&bytes).is_err(), "position {field}");
        }
        let bytes = changed(|fields| {
            let mut position = std::collections::BTreeMap::from([
                ("offset".into(), n(1)),
                ("start".into(), n(0)),
                ("count".into(), n(1)),
            ]);
            position.remove(field);
            fields.insert(
                "positions".into(),
                Value::Array(vec![Value::Object(position)]),
            );
        });
        assert!(Request::decode(&bytes).is_err(), "missing position {field}");
    }
    for field in ["kind", "owners", "effect", "accepted", "roots"] {
        let bytes = changed(|fields| {
            fields.insert(
                "positions".into(),
                Value::Array(vec![Value::object([
                    ("offset", n(1)),
                    ("start", n(0)),
                    ("count", n(1)),
                    (field, Value::Bool(true)),
                ])]),
            );
        });
        assert!(
            Request::decode(&bytes).is_err(),
            "position authority {field}"
        );
    }
}

#[test]
fn event_positions_share_the_existing_request_allocation_budget() {
    let count = json::MAX_BYTES / 128 - 1;
    let mut proposed = request();
    proposed.positions = vec![proposed.positions[0].clone(); count];
    let error = proposed.encode().unwrap_err();
    assert_eq!(error.code, "limit");
    assert!(error.message.contains("allocation capacity"));

    // This valid JSON fits the wire budget. Its positions plus the retained
    // interfaces exceed the same allocation budget used by the encoder.
    let template = String::from_utf8(changed(|fields| {
        fields.insert("positions".into(), Value::Null);
    }))
    .unwrap();
    let mut positions = String::from("[");
    positions.push_str(&"{\"offset\":1,\"start\":0,\"count\":1},".repeat(count - 1));
    positions.push_str("{\"offset\":1,\"start\":0,\"count\":1}]");
    let wire = template.replace("\"positions\":null", &format!("\"positions\":{positions}"));
    assert!(wire.len() < json::MAX_BYTES);
    let error = Request::decode(wire.as_bytes()).unwrap_err();
    assert_eq!(error.code, "limit");
    assert!(error.message.contains("allocation capacity"));
}

#[test]
fn actual_retained_view_binds_all_positions_even_when_selection_requests_match() {
    use crate::interchange::execution_view::finite::{self, Graph};
    use crate::ir::RawProgram;
    let raw = Arc::new(RawProgram {
        quantum_inputs: vec![],
        classical_inputs: vec![],
        operations: vec![],
        quantum_outputs: vec![],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    });
    let graph = crate::interchange::DecodedGraph {
        programs: vec![Arc::clone(&raw)],
        evidence: vec![],
        root: 0,
        interface: None,
        sources: vec![],
    };
    let view = |request: &Request| {
        finite::qmatch::complete(
            Graph {
                graph: &graph,
                root: &raw,
                interface: None,
                effect: Effect::Unitary,
                outputs: &[],
            },
            request,
        )
        .unwrap()
    };
    let mut original = request();
    original.positions.insert(
        0,
        Position {
            offset: 201,
            start: 0,
            count: 1,
        },
    );
    let expected = view(&original);
    for variant in 0..6 {
        let mut changed = original.clone();
        match variant {
            0 => changed.positions[0].offset += 1,
            1 => changed.positions[0].start += 1,
            2 => changed.positions[0].count += 1,
            3 => changed.positions.swap(0, 1),
            4 => {
                changed.positions.pop();
            }
            _ => changed.positions.push(changed.positions[0].clone()),
        }
        assert_eq!(changed.sites, original.sites);
        assert_ne!(
            view(&changed),
            expected,
            "context position variant {variant}"
        );
    }
}

#[test]
fn nested_source_and_arm_fields_cannot_supply_other_authority() {
    let mut value = json::parse(&request().encode().unwrap()).unwrap();
    let Value::Object(fields) = &mut value else {
        unreachable!()
    };
    let Value::Object(source) = fields.get_mut("source").unwrap() else {
        unreachable!()
    };
    source.insert("checked".into(), Value::Bool(true));
    assert!(Request::decode(&json::encode(&value).unwrap()).is_err());
    let bytes = changed(|fields| {
        let Value::Array(sites) = fields.get_mut("sites").unwrap() else {
            unreachable!()
        };
        let Value::Object(site) = &mut sites[0] else {
            unreachable!()
        };
        site.insert(
            "arms".into(),
            Value::Array(vec![Value::object([
                ("evidence", n(0)),
                ("controlled", n(2)),
                ("implementation", n(1)),
            ])]),
        );
    });
    assert!(Request::decode(&bytes).is_err());
}

#[test]
fn indices_are_unsigned_u32_and_arm_count_is_bounded() {
    let overflow = Value::Number(u64::from(u32::MAX) + 1);
    let bytes = changed(|fields| {
        let Value::Array(sites) = fields.get_mut("sites").unwrap() else {
            unreachable!()
        };
        let Value::Object(site) = &mut sites[0] else {
            unreachable!()
        };
        site.insert(
            "arms".into(),
            Value::Array(vec![Value::object([
                ("evidence", overflow.clone()),
                ("controlled", n(2)),
            ])]),
        );
    });
    assert!(Request::decode(&bytes).is_err());
    for count in [0, 65] {
        let mut request = request();
        request.sites[0].arms = vec![
            Arm {
                evidence: 0,
                controlled: 2
            };
            count
        ];
        assert!(request.encode().is_err());
    }
}

#[test]
fn bounded_names_and_interfaces_refuse_before_encoder_copies() {
    let mut value = request();
    value.source.function = "x".repeat(4097);
    assert!(value.encode().is_err());
    value.source.function = "choose".into();
    value.sites[0].attached.inputs = vec![owner(10); 129];
    assert!(value.encode().is_err());
}

#[test]
fn shared_dto_faults_agree_with_the_independent_lean_reader() {
    let fixture = json::parse(include_bytes!(
        "../../../tests/fixtures/qmatch_v030/transport-cases.json"
    ))
    .unwrap();
    for case in fixture.field("cases").unwrap().array().unwrap() {
        let name = case.field("name").unwrap().text().unwrap();
        let bytes = case.field("text").unwrap().text().unwrap().as_bytes();
        let expected = case.field("accepted").unwrap().boolean().unwrap();
        assert_eq!(Request::decode(bytes).is_ok(), expected, "DTO case {name}");
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn physical_arm_proposals_require_full_nominal_code_and_actual_control() {
    use crate::contract::function::{FunctionIdentity, RetainedIdentity};
    use crate::ir::{BitControl, CircuitAction, CircuitStep, RawOp, RawProgram, WireId};
    let source = "pub enum Tri{A,B,C} pub enum Other{A,B,C}
        pub unitary fn idle(q:Q<Tri>)->Q<Tri>{q}
        pub unitary fn phase(q:Q<Tri>)->Q<Tri>{global_phase_eighth(q)}
        pub unitary fn choose(s:Q<Bit>,q:Q<Tri>)->(Q<Bit>,Q<Tri>){
            qmatch(s,q){0=>idle,1=>phase}}";
    let port = |token, wires: Vec<u32>| QuantumPort {
        token: TokenId(token),
        shape: BasisShape {
            bits: wires.len() as u8,
        },
        wires: wires.into_iter().map(WireId).collect(),
    };
    let phase = |power, control: bool| CircuitStep {
        controls: if control {
            vec![BitControl {
                index: 0,
                when_one: true,
            }]
        } else {
            vec![]
        },
        action: CircuitAction::Monomial {
            indices: vec![],
            permutation: vec![0],
            phases: vec![power],
        },
    };
    let body = |steps: Vec<CircuitStep>| RawProgram {
        quantum_inputs: vec![port(0, vec![0]), port(1, vec![1, 2])],
        classical_inputs: vec![],
        operations: vec![
            RawOp::Join {
                left: TokenId(0),
                right: TokenId(1),
                output: TokenId(2),
            },
            RawOp::ApplyUnitary {
                input: TokenId(2),
                output: TokenId(3),
                steps,
            },
            RawOp::Split {
                input: TokenId(3),
                left: TokenId(4),
                right: TokenId(5),
                left_bits: 1,
            },
        ],
        quantum_outputs: vec![TokenId(4), TokenId(5)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    let subjects = || {
        ["idle", "phase"]
            .into_iter()
            .enumerate()
            .map(|(ordinal, name)| {
                let raw = RawProgram {
                    quantum_inputs: vec![port(0, vec![0, 1])],
                    classical_inputs: vec![],
                    operations: vec![RawOp::ApplyUnitary {
                        input: TokenId(0),
                        output: TokenId(1),
                        steps: if ordinal == 0 {
                            vec![]
                        } else {
                            vec![phase(1, false)]
                        },
                    }],
                    quantum_outputs: vec![TokenId(1)],
                    classical_outputs: vec![],
                    declared_effect: Effect::Unitary,
                };
                ArmSubject {
                    body: ArmBody::Physical {
                        bits: 2,
                        raw,
                        identity: Box::new(RetainedIdentity::Owned(FunctionIdentity {
                            implementation: format!("main::{name}"),
                            specification: format!("main::{name}"),
                            sources: vec![("main".into(), source.into())],
                        })),
                    },
                    controlled: body(if ordinal == 0 {
                        vec![]
                    } else {
                        vec![phase(1, true)]
                    }),
                }
            })
            .collect::<Vec<_>>()
    };
    let target = vec![Atom::Enum(
        Arc::new(Origin {
            module: "main".into(),
            declaration: "Tri".into(),
            source: source.into(),
        }),
        vec!["A".into(), "B".into(), "C".into()],
    )];
    let interface = Interface {
        inputs: vec![
            Owner {
                port: port(0, vec![0]),
                basis: vec![Atom::Bit],
            },
            Owner {
                port: port(1, vec![1, 2]),
                basis: target.clone(),
            },
        ],
        outputs: vec![
            Owner {
                port: port(4, vec![0]),
                basis: vec![Atom::Bit],
            },
            Owner {
                port: port(5, vec![1, 2]),
                basis: target,
            },
        ],
        public_effect: Effect::Unitary,
    };
    let site = SourceSite {
        module: "main".into(),
        function: "choose".into(),
    };
    let kernel =
        crate::interchange::native::Kernel::selected(crate::edition::Edition::E2026).unwrap();
    let check = |raw: &RawProgram, interface: Interface, arms: &[ArmSubject]| {
        let position = Position {
            offset: source.find("qmatch").unwrap() as u32,
            start: 0,
            count: raw.operations.len() as u32,
        };
        let (artifact, request) = proposal(
            raw,
            site.clone(),
            std::slice::from_ref(&position),
            &[SelectionSubject {
                interface: &interface,
                arms,
                position: position.clone(),
            }],
            &[("main".into(), source.into())],
        )
        .unwrap();
        kernel.check_qmatch_source(&artifact, &request)
    };
    let actual = body(vec![phase(1, true)]);
    assert_eq!(
        check(&actual, interface.clone(), &subjects())
            .unwrap()
            .native()
            .mode(),
        "--qmatch-source-check"
    );
    assert!(check(&body(vec![phase(7, true)]), interface.clone(), &subjects()).is_err());
    let mut wrong = subjects();
    wrong[1].controlled = body(vec![phase(7, true)]);
    assert!(check(&actual, interface.clone(), &wrong).is_err());
    let mut leaking = subjects();
    let ArmBody::Physical { raw, .. } = &mut leaking[1].body else {
        unreachable!()
    };
    let RawOp::ApplyUnitary { steps, .. } = &mut raw.operations[0] else {
        unreachable!()
    };
    *steps = vec![CircuitStep {
        controls: vec![],
        action: CircuitAction::Monomial {
            indices: vec![0, 1],
            permutation: vec![3, 1, 2, 0],
            phases: vec![0; 4],
        },
    }];
    assert!(check(&actual, interface.clone(), &leaking).is_err());

    // The two correct intervals have the same total phase as the wrong
    // intervals below. Every source occurrence must bind its own actual body.
    let sequence_source = source.replace(
        "qmatch(s,q){0=>idle,1=>phase}",
        "let(s,q)=qmatch(s,q){0=>idle,1=>phase}; qmatch(s,q){0=>idle,1=>phase}",
    );
    let mut sequence_arms = subjects();
    for arm in &mut sequence_arms {
        let ArmBody::Physical { identity, .. } = &mut arm.body else {
            unreachable!()
        };
        let RetainedIdentity::Owned(identity) = identity.as_mut() else {
            unreachable!()
        };
        identity.sources[0].1 = sequence_source.clone();
    }
    let mut first = interface.clone();
    for owner in first.inputs.iter_mut().chain(&mut first.outputs) {
        if let Atom::Enum(origin, _) = &mut owner.basis[0] {
            Arc::make_mut(origin).source = sequence_source.clone();
        }
    }
    let mut second = first.clone();
    second.inputs = first.outputs.clone();
    second.outputs[0].port.token = TokenId(8);
    second.outputs[1].port.token = TokenId(9);
    let mut sequence = actual.clone();
    sequence.operations.extend([
        RawOp::Join {
            left: TokenId(4),
            right: TokenId(5),
            output: TokenId(6),
        },
        RawOp::ApplyUnitary {
            input: TokenId(6),
            output: TokenId(7),
            steps: vec![phase(1, true)],
        },
        RawOp::Split {
            input: TokenId(7),
            left: TokenId(8),
            right: TokenId(9),
            left_bits: 1,
        },
    ]);
    sequence.quantum_outputs = vec![TokenId(8), TokenId(9)];
    let positions = sequence_source
        .match_indices("qmatch")
        .enumerate()
        .map(|(index, (offset, _))| Position {
            offset: offset as u32,
            start: 3 * index as u32,
            count: 3,
        })
        .collect::<Vec<_>>();
    let propose = |raw: &RawProgram| {
        proposal(
            raw,
            site.clone(),
            &positions,
            &[
                SelectionSubject {
                    interface: &first,
                    position: positions[0].clone(),
                    arms: &sequence_arms,
                },
                SelectionSubject {
                    interface: &second,
                    position: positions[1].clone(),
                    arms: &sequence_arms,
                },
            ],
            &[("main".into(), sequence_source.clone())],
        )
        .unwrap()
    };
    let (artifact, requested) = propose(&sequence);
    kernel.check_qmatch_source(&artifact, &requested).unwrap();
    let mut wrong_intervals = sequence.clone();
    for (index, power) in [(1, 2), (4, 0)] {
        let RawOp::ApplyUnitary { steps, .. } = &mut wrong_intervals.operations[index] else {
            unreachable!()
        };
        *steps = vec![phase(power, true)];
    }
    let (wrong_artifact, wrong_request) = propose(&wrong_intervals);
    assert!(
        kernel
            .check_qmatch_source(&wrong_artifact, &wrong_request)
            .is_err()
    );
    let original = Request::decode(&requested).unwrap();
    for variant in 0..6 {
        let mut changed = original.clone();
        match variant {
            0 => {
                changed.sites.pop();
            }
            1 => changed.sites.swap(0, 1),
            2 => changed.sites.push(changed.sites[0].clone()),
            3 => changed.sites[1].position.start = 0,
            4 => changed.sites[1].position.start = 4,
            _ => changed.sites[0].position.count = 2,
        }
        assert!(
            kernel
                .check_qmatch_source(&artifact, &changed.encode().unwrap())
                .is_err(),
            "sequence variant {variant}"
        );
    }
    let mut wrong_type = interface;
    for owner in [&mut wrong_type.inputs[1], &mut wrong_type.outputs[1]] {
        let Atom::Enum(origin, _) = &mut owner.basis[0] else {
            unreachable!()
        };
        Arc::make_mut(origin).declaration = "Other".into();
    }
    assert!(check(&actual, wrong_type, &subjects()).is_err());
}
