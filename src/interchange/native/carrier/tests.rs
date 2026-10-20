//! Small native requests and deliberate stale-view/source/body faults.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::contract::exact::{Exact, Matrix};
use crate::edition::Edition;
use crate::interchange::carrier::{Atom, Interface, Origin, Owner};
use crate::interchange::json::{self, Value};
use crate::ir::*;

const SOURCE: &str = "// enum Tri { Decoy }\npub enum Tri { A, B, C }\npub enum Four { A, B, C, D }\npub enum One { Only }\npub struct Empty {}\npub struct Wrapped { flags: (Unit, Bits<0>), tag: labels::Tri }";

fn n(value: u32) -> Value {
    Value::Number(u64::from(value))
}

fn replace(value: &mut Value, key: &str, replacement: Value) {
    let Value::Object(fields) = value else {
        panic!("fixture object")
    };
    *fields.get_mut(key).unwrap() = replacement;
}

fn root(value: &mut Value) -> &mut Value {
    let Value::Object(fields) = value else {
        panic!("fixture artifact")
    };
    let Value::Array(programs) = fields.get_mut("programs").unwrap() else {
        panic!("fixture programs")
    };
    &mut programs[1]
}

fn op(tag: &str, fields: impl IntoIterator<Item = (&'static str, Value)>) -> Value {
    Value::object(std::iter::once(("tag", text(tag))).chain(fields))
}
fn text(value: &str) -> Value {
    Value::String(value.into())
}
fn array(values: impl IntoIterator<Item = u32>) -> Value {
    Value::Array(values.into_iter().map(n).collect())
}

fn port(token: u32) -> QuantumPort {
    QuantumPort {
        token: TokenId(token),
        wires: vec![WireId(7), WireId(19)],
        shape: BasisShape { bits: 2 },
    }
}
fn nominal(name: &str, members: &[&str]) -> Atom {
    Atom::Enum(
        Arc::new(Origin {
            module: "labels".into(),
            declaration: name.into(),
            source: SOURCE.into(),
        }),
        members.iter().map(|s| (*s).into()).collect(),
    )
}
fn request() -> Request {
    let interface = Interface {
        inputs: vec![Owner {
            port: port(0),
            basis: vec![nominal("Tri", &["A", "B", "C"])],
        }],
        outputs: vec![Owner {
            port: port(1),
            basis: vec![nominal("Tri", &["A", "B", "C"])],
        }],
        public_effect: Effect::Unitary,
    };
    let logical = Matrix::new(
        3,
        3,
        (0..9)
            .map(|i| {
                if i / 3 == (i % 3 + 1) % 3 {
                    Exact::one()
                } else {
                    Exact::zero()
                }
            })
            .collect(),
    )
    .unwrap();
    Request {
        attached: interface.clone(),
        required: interface,
        logical,
    }
}

fn body(action: Value) -> Value {
    Value::object([
        (
            "quantum_inputs",
            Value::Array(vec![Value::object([
                ("token", n(0)),
                ("wires", array([7, 19])),
                ("shape", Value::object([("bits", n(2))])),
            ])]),
        ),
        ("classical_inputs", Value::Array(vec![])),
        (
            "operations",
            Value::Array(vec![Value::object([
                ("tag", text("apply_unitary")),
                ("input", n(0)),
                ("output", n(1)),
                (
                    "steps",
                    Value::Array(vec![Value::object([
                        ("controls", Value::Array(vec![])),
                        ("action", action),
                    ])]),
                ),
            ])]),
        ),
        ("quantum_outputs", array([1])),
        ("classical_outputs", Value::Array(vec![])),
        ("declared_effect", text("unitary")),
    ])
}

fn artifact(permutation: [u32; 4], phases: [u32; 4], indices: [u32; 2]) -> Vec<u8> {
    // Source rows are bound to reachable original function evidence; the new
    // carrier path never bypasses the existing sourcesUsed/dependency checks.
    let implementation = body(Value::object([
        ("tag", text("monomial")),
        ("indices", array(indices)),
        ("permutation", array(permutation)),
        ("phases", array(phases)),
    ]));
    let root = body(Value::object([
        ("tag", text("contract")),
        ("indices", array([0, 1])),
        ("evidence", n(0)),
        ("adjoint", Value::Bool(false)),
    ]));
    json::encode(&Value::object([
        ("format", text("qleisli.finite-ir")),
        ("version", n(2)),
        ("profile", text("finite-meaning-v1")),
        (
            "sources",
            Value::Array(vec![Value::object([
                ("path", text("labels")),
                ("text", text(SOURCE)),
            ])]),
        ),
        ("programs", Value::Array(vec![implementation, root])),
        (
            "evidence",
            Value::Array(vec![Value::object([
                ("tag", text("circuit")),
                (
                    "signature",
                    Value::object([("tag", text("bits")), ("width", n(2))]),
                ),
                ("implementation", n(0)),
                ("specification", n(0)),
                (
                    "identity",
                    Value::object([
                        ("implementation", text("labels::body")),
                        ("specification", text("labels::body")),
                        ("sources", array([0])),
                    ]),
                ),
            ])]),
        ),
        ("root", n(1)),
        ("root_interface", Value::Null),
    ]))
    .unwrap()
}

fn observe(
    kernel: &Kernel,
    label: &str,
    artifact: &[u8],
    request: &Request,
) -> Result<CarrierChecked> {
    let bytes = request.encode().unwrap();
    eprintln!(
        "carrier case {label}\nartifact {}\nrequest {}",
        String::from_utf8_lossy(artifact),
        String::from_utf8_lossy(&bytes)
    );
    let result = kernel.check_carrier(artifact, &bytes);
    eprintln!(
        "outcome {}",
        match &result {
            Ok(_) => "accepted",
            Err(error) => error.code,
        }
    );
    result
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn original_carrier_body_source_and_logical_phase_are_bound() {
    let selected = Kernel::selected(Edition::E2026).unwrap();
    let (kernel, log) = selected.recording();
    let good = artifact([1, 2, 0, 3], [0; 4], [0, 1]);
    let requested = request();
    let checked = observe(&kernel, "three-cycle", &good, &requested).unwrap();
    assert_eq!(checked.artifact(), good);
    assert_eq!(checked.request(), &requested);
    assert_eq!(checked.request_bytes(), requested.encode().unwrap());
    assert_eq!(checked.native().mode(), "--carrier-pure-check");
    assert!(log.summary().complete());
    let mut public_iso = requested.clone();
    public_iso.attached.public_effect = Effect::Isometry;
    public_iso.required.public_effect = Effect::Isometry;
    let retained = observe(&kernel, "square-public-isometry", &good, &public_iso).unwrap();
    assert_eq!(retained.request().required.public_effect, Effect::Isometry);
    let mut record = requested.clone();
    let wrapper = Atom::Record(
        Arc::new(Origin {
            module: "labels".into(),
            declaration: "Wrapped".into(),
            source: SOURCE.into(),
        }),
        vec!["flags".into(), "tag".into()],
    );
    for owner in record
        .attached
        .inputs
        .iter_mut()
        .chain(&mut record.attached.outputs)
    {
        let mut tree = vec![wrapper.clone(), Atom::Pair, Atom::Unit, Atom::Bits(0)];
        tree.append(&mut owner.basis);
        owner.basis = tree;
    }
    record.required = record.attached.clone();
    observe(&kernel, "nested-record-original-source", &good, &record).unwrap();
    for (label, broken) in [
        ("leaks-code", artifact([1, 2, 3, 0], [0; 4], [0, 1])),
        ("wrong-phase", artifact([1, 2, 0, 3], [0, 0, 1, 0], [0, 1])),
        ("wrong-axes", artifact([1, 2, 0, 3], [0; 4], [1, 0])),
        ("wrong-dependency", artifact([0, 1, 2, 3], [0; 4], [0, 1])),
    ] {
        assert!(observe(&kernel, label, &broken, &requested).is_err());
    }
    let mut wrong = requested.clone();
    wrong.attached.inputs[0].basis = vec![nominal("Tri", &["A", "C", "B"])];
    wrong.required = wrong.attached.clone();
    assert!(observe(&kernel, "wrong-original-members", &good, &wrong).is_err());
    let mut wrong = requested.clone();
    let mut origin = match &wrong.attached.inputs[0].basis[0] {
        Atom::Enum(origin, _) => (**origin).clone(),
        _ => unreachable!(),
    };
    origin.source.push(' ');
    wrong.attached.inputs[0].basis = vec![Atom::Enum(
        Arc::new(origin),
        vec!["A".into(), "B".into(), "C".into()],
    )];
    wrong.required = wrong.attached.clone();
    assert!(observe(&kernel, "stale-original-bytes", &good, &wrong).is_err());
    let mut wrong = requested.clone();
    wrong.required.inputs[0].basis = vec![Atom::Bits(2)];
    assert!(
        observe(
            &kernel,
            "equal-width-different-required-type",
            &good,
            &wrong
        )
        .is_err()
    );
    let mut wrong = requested.clone();
    wrong.attached.public_effect = Effect::Observe;
    wrong.required.public_effect = Effect::Observe;
    assert!(observe(&kernel, "false-pure-public-effect", &good, &wrong).is_err());
    let identity = artifact([0, 1, 2, 3], [0; 4], [0, 1]);
    let mut rectangular = requested.clone();
    rectangular.attached.outputs[0].basis = vec![nominal("Four", &["A", "B", "C", "D"])];
    rectangular.attached.public_effect = Effect::Isometry;
    rectangular.required = rectangular.attached.clone();
    rectangular.logical = Matrix::new(
        4,
        3,
        (0..12)
            .map(|i| {
                if i / 3 == i % 3 {
                    Exact::one()
                } else {
                    Exact::zero()
                }
            })
            .collect(),
    )
    .unwrap();
    observe(&kernel, "three-to-four-isometry", &identity, &rectangular).unwrap();
    rectangular.attached.public_effect = Effect::Unitary;
    rectangular.required.public_effect = Effect::Unitary;
    assert!(
        observe(
            &kernel,
            "false-three-to-four-unitary",
            &identity,
            &rectangular
        )
        .is_err()
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn stale_carrier_view_and_wrong_invocation_scope_never_authorize_a_handle() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    let artifact = artifact([1, 2, 0, 3], [0; 4], [0, 1]);
    let request = request();
    let bytes = request.encode().unwrap();
    let subject = kernel.subject(&artifact, Some(&bytes)).unwrap();
    let prepared = Prepared::new(Arc::clone(&subject)).unwrap();
    for mutation in 0..5 {
        let mut stale = request.clone();
        match mutation {
            0 => stale.logical = Matrix::identity(3).unwrap(),
            1 => stale.required.inputs[0].basis = vec![nominal("Four", &["A", "B", "C", "D"])],
            2 => stale.attached.public_effect = Effect::Isometry,
            3 => stale.attached.outputs[0].port.wires.reverse(),
            _ => stale.required.outputs.push(Owner {
                port: QuantumPort {
                    token: TokenId(9),
                    wires: vec![],
                    shape: BasisShape { bits: 0 },
                },
                basis: vec![Atom::Unit],
            }),
        }
        let view = carrier::complete(prepared.graph(), &stale).unwrap();
        eprintln!("stale carrier view {mutation}: {view:?}");
        let result = Kernel::submit_subject(
            Arc::clone(&subject),
            "--carrier-pure-check",
            Some(View {
                graph: &view,
                caller: None,
            }),
        );
        assert_eq!(result.unwrap_err().code, "decoded_view");
    }
    assert!(Kernel::inspect_subject(Arc::clone(&subject), "--carrier-pure-check").is_err());
    let view = carrier::complete(prepared.graph(), &request).unwrap();
    assert!(
        Kernel::submit_subject(
            subject,
            "--carrier-pure-check",
            Some(View {
                graph: &view,
                caller: Some((&view, &[]))
            })
        )
        .is_err()
    );
    for version in [2, 0] {
        let mut unknown = json::parse(&bytes).unwrap();
        replace(&mut unknown, "version", n(version));
        let unknown = json::encode(&unknown).unwrap();
        let subject = kernel.subject(&artifact, Some(&unknown)).unwrap();
        assert!(
            Kernel::submit_subject(
                subject,
                "--carrier-pure-check",
                Some(View {
                    graph: &view,
                    caller: None
                })
            )
            .is_err()
        );
    }
    let subject = kernel.subject(&artifact, None).unwrap();
    assert!(
        Kernel::submit_subject(
            subject,
            "--carrier-pure-check",
            Some(View {
                graph: &view,
                caller: None
            })
        )
        .is_err()
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn hidden_observation_never_obtains_a_pure_carrier_label() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    let good = artifact([1, 2, 0, 3], [0; 4], [0, 1]);
    for label in ["observe", "unitary", "iso"] {
        let mut observing = json::parse(&good).unwrap();
        let body = root(&mut observing);
        let mut operations = body.field("operations").unwrap().array().unwrap().to_vec();
        operations.extend([
            op("discard", [("input", n(1))]),
            op("init0", [("output", n(2)), ("wire", n(23))]),
            op("init0", [("output", n(3)), ("wire", n(29))]),
            op("join", [("left", n(2)), ("right", n(3)), ("output", n(4))]),
        ]);
        replace(body, "operations", Value::Array(operations));
        replace(body, "quantum_outputs", array([4]));
        replace(body, "declared_effect", text(label));
        let mut wrong = request();
        wrong.attached.outputs[0].port = QuantumPort {
            token: TokenId(4),
            wires: vec![WireId(23), WireId(29)],
            shape: BasisShape { bits: 2 },
        };
        wrong.required = wrong.attached.clone();
        let error =
            observe(&kernel, label, &json::encode(&observing).unwrap(), &wrong).unwrap_err();
        assert_ne!(error.code, "format");
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn nominal_zero_width_owners_and_their_scalar_phase_are_retained() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    let original = artifact([1, 2, 0, 3], [0; 4], [0, 1]);
    let mut value = json::parse(&original).unwrap();
    let body = root(&mut value);
    let mut inputs = body
        .field("quantum_inputs")
        .unwrap()
        .array()
        .unwrap()
        .to_vec();
    inputs.insert(
        0,
        Value::object([
            ("token", n(8)),
            ("wires", array([])),
            ("shape", Value::object([("bits", n(0))])),
        ]),
    );
    replace(body, "quantum_inputs", Value::Array(inputs));
    let mut operations = body.field("operations").unwrap().array().unwrap().to_vec();
    operations.insert(
        0,
        op(
            "apply_unitary",
            [
                ("input", n(8)),
                ("output", n(9)),
                (
                    "steps",
                    Value::Array(vec![Value::object([
                        ("controls", Value::Array(vec![])),
                        (
                            "action",
                            Value::object([
                                ("tag", text("monomial")),
                                ("indices", array([])),
                                ("permutation", array([0])),
                                ("phases", array([4])),
                            ]),
                        ),
                    ])]),
                ),
            ],
        ),
    );
    replace(body, "operations", Value::Array(operations));
    replace(body, "quantum_outputs", array([9, 1]));
    let bytes = json::encode(&value).unwrap();
    for zero in [
        nominal("One", &["Only"]),
        Atom::Record(
            Arc::new(Origin {
                module: "labels".into(),
                declaration: "Empty".into(),
                source: SOURCE.into(),
            }),
            vec![],
        ),
    ] {
        let mut requested = request();
        let input = Owner {
            port: QuantumPort {
                token: TokenId(8),
                wires: vec![],
                shape: BasisShape { bits: 0 },
            },
            basis: vec![zero],
        };
        let mut output = input.clone();
        output.port.token = TokenId(9);
        requested.attached.inputs.insert(0, input);
        requested.attached.outputs.insert(0, output);
        requested.required = requested.attached.clone();
        requested.logical = Matrix::new(
            3,
            3,
            (0..9)
                .map(|i| {
                    if i / 3 == (i % 3 + 1) % 3 {
                        Exact::new([-1, 0, 0, 0], 0).unwrap()
                    } else {
                        Exact::zero()
                    }
                })
                .collect(),
        )
        .unwrap();
        observe(&kernel, "zero-owner-phase", &bytes, &requested).unwrap();
        let mut wrong_phase = requested.clone();
        wrong_phase.logical = request().logical;
        assert!(observe(&kernel, "zero-owner-phase-erased", &bytes, &wrong_phase).is_err());
        requested.attached.inputs.remove(0);
        requested.attached.outputs.remove(0);
        requested.required = requested.attached.clone();
        assert!(observe(&kernel, "dropped-zero-owner", &bytes, &requested).is_err());
    }
}
