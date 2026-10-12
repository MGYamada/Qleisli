// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::contract::{DEFAULT_EXACT_WORK, exact::Budget};
use crate::interchange::{Decoder, codec::Codec, execution_view, json};

fn vectors() -> json::Value {
    json::parse(include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/verification_v030/execution-view-binding/contract-walker-vectors.json"
    )))
    .unwrap()
}

fn basis(value: &json::Value) -> BasisType {
    BasisType::read(value, &Decoder { evidence: &[] }).unwrap()
}

fn prefix(value: &json::Value) -> BasisType {
    fn next(atoms: &mut std::slice::Iter<'_, json::Value>) -> BasisType {
        match atoms.next().unwrap().text().unwrap() {
            "unit" => BasisType::Unit,
            "bit" => BasisType::Bit,
            "pair" => BasisType::pair(next(atoms), next(atoms)),
            text if text.starts_with("bits:") => BasisType::Bits(text[5..].parse().unwrap()),
            text => BasisType::Tuple(
                (0..text[6..].parse::<usize>().unwrap())
                    .map(|_| next(atoms))
                    .collect(),
            ),
        }
    }
    let mut atoms = value.array().unwrap().iter();
    let result = next(&mut atoms);
    assert!(atoms.next().is_none());
    result
}

fn matrix(value: &json::Value) -> Matrix {
    crate::interchange::finite_matrix::decode(
        &json::encode(value).unwrap(),
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap()
}

fn encoding(value: &json::Value) -> Encoding {
    Encoding::new(
        prefix(value.field("logical").unwrap()),
        prefix(value.field("physical").unwrap()),
        matrix(value.field("map").unwrap()),
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap()
}

fn port(value: &json::Value) -> QuantumPort {
    QuantumPort::read(value, &Decoder { evidence: &[] }).unwrap()
}

fn signature(value: &json::Value) -> Signature {
    fn result(value: &json::Value, output: &mut Vec<ResultAtom>) {
        match value.field("tag").unwrap().text().unwrap() {
            "unit" => output.push(ResultAtom::Unit),
            "bit" => output.push(ResultAtom::Bit),
            "bits" => output.push(ResultAtom::Bits(
                value.field("width").unwrap().number().unwrap() as u32,
            )),
            "quantum" => output.push(ResultAtom::Quantum(basis(value.field("basis").unwrap()))),
            "pair" => {
                output.push(ResultAtom::Pair);
                result(value.field("left").unwrap(), output);
                result(value.field("right").unwrap(), output);
            }
            "tuple" => {
                let fields = value.field("fields").unwrap().array().unwrap();
                output.push(ResultAtom::Tuple(fields.len()));
                for field in fields {
                    result(field, output);
                }
            }
            _ => panic!("unknown result type"),
        }
    }
    let mut atoms = vec![];
    result(value.field("result").unwrap(), &mut atoms);
    let signature = Signature {
        input: basis(value.field("input").unwrap()),
        result: atoms,
    };
    signature
        .validate(&mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    signature
}

fn axes(value: &json::Value) -> Vec<usize> {
    value
        .array()
        .unwrap()
        .iter()
        .map(|n| n.number().unwrap() as usize)
        .collect()
}

fn describe(value: &json::Value) -> Vec<u8> {
    match value.field("kind").unwrap().text().unwrap() {
        "encoded" => {
            let value = value.field("contract").unwrap();
            let contract = Contract::new(
                encoding(value.field("input").unwrap()),
                encoding(value.field("output").unwrap()),
                matrix(value.field("logical").unwrap()),
                &mut Budget::new(DEFAULT_EXACT_WORK),
            )
            .unwrap();
            request(Request::Encoded(&contract)).unwrap()
        }
        "leaf" => {
            let boundary = UnitaryBoundary::new(
                basis(value.field("signature").unwrap()),
                port(value.field("input").unwrap()),
                port(value.field("output").unwrap()),
            )
            .unwrap();
            request(Request::Leaf(
                &boundary,
                &matrix(value.field("matrix").unwrap()),
            ))
            .unwrap()
        }
        "pure-leaf" => {
            let boundary = PureBoundary::new(
                basis(value.field("domain").unwrap()),
                basis(value.field("codomain").unwrap()),
                port(value.field("input").unwrap()),
                port(value.field("output").unwrap()),
            )
            .unwrap();
            request(Request::PureLeaf(
                &boundary,
                &matrix(value.field("matrix").unwrap()),
            ))
            .unwrap()
        }
        "control" => request(Request::Control(
            &basis(value.field("signature").unwrap()),
            &axes(value.field("axes").unwrap()),
        ))
        .unwrap(),
        "control-owners" => {
            let signatures: Vec<_> = value
                .field("signatures")
                .unwrap()
                .array()
                .unwrap()
                .iter()
                .map(basis)
                .collect();
            request(Request::ControlOwners(
                &signatures,
                &axes(value.field("axes").unwrap()),
            ))
            .unwrap()
        }
        "instrument" => {
            let id = value.field("identity").unwrap();
            let sources: Vec<_> = id
                .field("sources")
                .unwrap()
                .array()
                .unwrap()
                .iter()
                .map(|s| {
                    (
                        s.field("path").unwrap().text().unwrap().into(),
                        s.field("text").unwrap().text().unwrap().into(),
                    )
                })
                .collect();
            request(Request::Instrument {
                actual: &signature(value.field("actual_signature").unwrap()),
                expected: &signature(value.field("expected_signature").unwrap()),
                identity: (
                    id.field("implementation").unwrap().text().unwrap(),
                    id.field("specification").unwrap().text().unwrap(),
                    &sources,
                ),
            })
            .unwrap()
        }
        _ => panic!("unknown request kind"),
    }
}

fn caller(value: &json::Value, dependencies: &[Arc<FunctionEvidence>]) -> Circuit {
    let evidence: Vec<_> = dependencies.iter().cloned().map(Some).collect();
    let steps = Vec::<CircuitStep>::read(
        value.field("steps").unwrap(),
        &Decoder {
            evidence: &evidence,
        },
    )
    .unwrap();
    Circuit::new(prefix(value.field("basis").unwrap()), steps).unwrap()
}

fn expected(row: &json::Value) -> Vec<u8> {
    execution_view::encode(&execution_view::tests::vector_value(
        row.field("view").unwrap(),
    ))
    .unwrap()
}

#[test]
fn six_typed_obligation_kinds_and_actual_caller_circuit_match_shared_vectors() {
    for row in vectors().array().unwrap() {
        if row.field("dependency").is_ok() {
            continue;
        }
        let actual = if row.field("kind").unwrap().text().unwrap() == "request" {
            describe(row.field("request").unwrap())
        } else {
            circuit(&caller(row.field("circuit").unwrap(), &[]), &[]).unwrap()
        };
        assert_eq!(
            actual,
            expected(row),
            "{}",
            row.field("name").unwrap().text().unwrap()
        );
    }
}

fn at<'a>(value: &'a mut json::Value, path: &[&str]) -> &'a mut json::Value {
    let Some((first, rest)) = path.split_first() else {
        return value;
    };
    let next = match value {
        json::Value::Object(fields) => fields.get_mut(*first).unwrap(),
        json::Value::Array(fields) => &mut fields[first.parse::<usize>().unwrap()],
        _ => panic!("invalid mutation path"),
    };
    at(next, rest)
}

#[test]
fn typed_obligation_changes_preserve_neither_encoding_phase_ports_types_nor_identity() {
    use json::Value::{Array, Number, String as Text};
    let mutations: Vec<(usize, Vec<&str>, json::Value)> = vec![
        (
            0,
            vec!["contract", "input", "map", "entries", "0", "0", "numerator"],
            Text("-1".into()),
        ),
        (
            0,
            vec!["contract", "output", "physical"],
            Array(vec![Text("bit".into())]),
        ),
        (
            0,
            vec!["contract", "logical", "entries", "0", "0", "numerator"],
            Text("-1".into()),
        ),
        (1, vec!["input", "token"], Number(99)),
        (1, vec!["output", "token"], Number(99)),
        (
            1,
            vec!["matrix", "entries", "0", "0", "numerator"],
            Text("1".into()),
        ),
        (
            2,
            vec!["domain"],
            json::parse(br#"{"tag":"bits","width":0}"#).unwrap(),
        ),
        (2, vec!["output", "wires", "0"], Number(3)),
        (
            2,
            vec!["matrix", "entries", "1", "1", "numerator"],
            Text("-1".into()),
        ),
        (3, vec!["axes", "0"], Number(0)),
        (
            3,
            vec!["signature"],
            json::parse(br#"{"tag":"bits","width":2}"#).unwrap(),
        ),
        (
            5,
            vec!["signatures", "0"],
            json::parse(br#"{"tag":"bits","width":0}"#).unwrap(),
        ),
        (5, vec!["axes"], Array(vec![Number(0), Number(1)])),
        (
            6,
            vec!["actual_signature", "result", "fields", "0", "basis"],
            json::parse(br#"{"tag":"bits","width":0}"#).unwrap(),
        ),
        (
            6,
            vec!["expected_signature", "result", "fields", "2", "width"],
            Number(1),
        ),
        (
            6,
            vec!["identity", "sources", "0", "path"],
            Text("é.qli".into()),
        ),
        (
            6,
            vec!["identity", "sources", "1", "text"],
            Text("different source".into()),
        ),
        (
            6,
            vec!["identity", "implementation"],
            Text("different implementation".into()),
        ),
    ];
    let rows = vectors();
    for (index, path, replacement) in mutations {
        let original = rows.array().unwrap()[index].field("request").unwrap();
        let mut changed = original.clone();
        *at(&mut changed, &path) = replacement;
        assert_ne!(
            describe(&changed),
            describe(original),
            "{}: {path:?}",
            rows.array().unwrap()[index]
                .field("name")
                .unwrap()
                .text()
                .unwrap()
        );
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn caller_circuit_reads_actual_dependency_reference_and_literal_steps() {
    use crate::contract::{
        FunctionIdentity,
        meaning::{FiniteMeaning, MeaningEvidence},
    };
    let meaning = FiniteMeaning::permutation(BasisType::Bit, vec![1, 0]).unwrap();
    let receipt = MeaningEvidence::check(
        meaning.target_ir().unwrap(),
        meaning,
        FunctionIdentity {
            implementation: "x-dependency".into(),
            specification: "flip".into(),
            sources: vec![],
        },
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap()
    .receipt();
    let rows = vectors();
    let row = &rows.array().unwrap()[8];
    let value = row.field("circuit").unwrap();
    let actual = caller(value, std::slice::from_ref(&receipt));
    let bytes = circuit(&actual, std::slice::from_ref(&receipt)).unwrap();
    assert_eq!(bytes, expected(row));
    assert!(circuit(&actual, &[]).is_err());
    assert!(circuit(&actual, &[receipt.clone(), receipt.clone()]).is_err());
    for (path, replacement) in [
        (
            vec!["steps", "0", "action", "adjoint"],
            json::Value::Bool(false),
        ),
        (
            vec!["steps", "0", "action", "indices", "0"],
            json::Value::Number(0),
        ),
        (
            vec!["steps", "0", "controls", "0", "when_one"],
            json::Value::Bool(true),
        ),
    ] {
        let mut changed = value.clone();
        *at(&mut changed, &path) = replacement;
        // Construction describes an untrusted proposal, including overlap;
        // semantic access checking remains the independent native gate's duty.
        assert_ne!(
            circuit(
                &caller(&changed, std::slice::from_ref(&receipt)),
                std::slice::from_ref(&receipt)
            )
            .unwrap(),
            bytes
        );
    }
}
