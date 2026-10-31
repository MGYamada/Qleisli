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
        attached: interface.clone(),
        required: interface,
        source: SourceSite {
            module: "same".into(),
            function: "choose".into(),
            offset: 137,
        },
        arms: vec![Arm {
            evidence: 0,
            controlled: 2,
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
    request.attached.inputs[0].basis = vec![Atom::Enum(
        Arc::new(Origin {
            module: "labels".into(),
            declaration: "Tri".into(),
            source: "pub enum Tri { A,B,C }".into(),
        }),
        vec!["A".into(), "B".into(), "C".into()],
    )];
    request.required.outputs[1].basis = vec![Atom::Tuple(2), Atom::Unit, Atom::Bits(0)];
    request.required.public_effect = Effect::Observe;
    // Deliberately inconsistent proposed data remains data: only Lean can
    // accept semantic interfaces or prevent public-effect sharpening.
    let decoded = Request::decode(&request.encode().unwrap()).unwrap();
    assert_eq!(decoded, request);
    assert_ne!(decoded.attached.inputs[0], decoded.attached.inputs[1]);
    assert_eq!(decoded.required.public_effect, Effect::Observe);
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
        ("version", n(2)),
    ] {
        let bytes = changed(|fields| {
            fields.insert(key.into(), value.clone());
        });
        assert!(Request::decode(&bytes).is_err());
    }
    assert!(
        Request::decode(&changed(|fields| {
            fields.remove("source");
        }))
        .is_err()
    );
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
        fields.insert(
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
        fields.insert(
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
        request.arms = vec![
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
    value.attached.inputs = vec![owner(10); 129];
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
        offset: source.find("qmatch").unwrap() as u32,
    };
    let kernel =
        crate::interchange::native::Kernel::selected(crate::edition::Edition::E2026).unwrap();
    let check = |raw: &RawProgram, interface: Interface, arms: &[ArmSubject]| {
        let (artifact, request) = proposal(
            raw,
            interface,
            site.clone(),
            arms,
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
    let mut wrong_type = interface;
    for owner in [&mut wrong_type.inputs[1], &mut wrong_type.outputs[1]] {
        let Atom::Enum(origin, _) = &mut owner.basis[0] else {
            unreachable!()
        };
        Arc::make_mut(origin).declaration = "Other".into();
    }
    assert!(check(&actual, wrong_type, &subjects()).is_err());
}
