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
