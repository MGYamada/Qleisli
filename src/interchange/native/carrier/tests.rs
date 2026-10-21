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
        "outcome {label} {}",
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

// This binds type declarations to a raw body, not the source function's meaning.
fn import_artifact(rows: &[(&str, &str)]) -> Vec<u8> {
    source_artifact([1, 2, 0, 3], rows)
}

fn source_artifact(permutation: [u32; 4], rows: &[(&str, &str)]) -> Vec<u8> {
    let mut value = json::parse(&artifact(permutation, [0; 4], [0, 1])).unwrap();
    replace(
        &mut value,
        "sources",
        Value::Array(
            rows.iter()
                .map(|(path, source)| Value::object([("path", text(path)), ("text", text(source))]))
                .collect(),
        ),
    );
    let Value::Object(fields) = &mut value else {
        panic!("fixture artifact")
    };
    let Value::Array(evidence) = fields.get_mut("evidence").unwrap() else {
        panic!("fixture evidence")
    };
    let Value::Object(entry) = &mut evidence[0] else {
        panic!("fixture entry")
    };
    replace(
        entry.get_mut("identity").unwrap(),
        "sources",
        array((0..rows.len()).map(|i| u32::try_from(i).unwrap())),
    );
    json::encode(&value).unwrap()
}

fn import_request(main: &str, leaf: &str) -> Request {
    let mut requested = request();
    let basis = vec![
        Atom::Record(
            Arc::new(Origin {
                module: "main".into(),
                declaration: "Box".into(),
                source: main.into(),
            }),
            vec!["tag".into()],
        ),
        Atom::Enum(
            Arc::new(Origin {
                module: "labels".into(),
                declaration: "Tri".into(),
                source: leaf.into(),
            }),
            vec!["A".into(), "B".into(), "C".into()],
        ),
    ];
    for owner in requested
        .attached
        .inputs
        .iter_mut()
        .chain(&mut requested.attached.outputs)
    {
        owner.basis = basis.clone();
    }
    requested.required = requested.attached.clone();
    requested
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn imports_keep_original_type_identity_visibility_and_category() {
    let selected = Kernel::selected(Edition::E2026).unwrap();
    let (kernel, log) = selected.recording();
    let leaf = "pub enum Tri { A, B, C }";
    let bridge = "pub use {labels::{Tri,},};";
    let main = "use bridge::{Tri}; pub struct Box { tag: Tri }";
    let rows = [("main", main), ("bridge", bridge), ("labels", leaf)];
    let good = import_artifact(&rows);
    let requested = import_request(main, leaf);
    let handle = observe(&kernel, "public-type-reexport", &good, &requested).unwrap();
    assert_eq!(handle.artifact(), good);
    assert_eq!(handle.request(), &requested);
    assert_eq!(handle.request_bytes(), requested.encode().unwrap());
    let qualified = "pub struct Box { tag: bridge::Tri }";
    let qualified_body =
        import_artifact(&[("labels", leaf), ("bridge", bridge), ("main", qualified)]);
    observe(
        &kernel,
        "qualified-type-reexport",
        &qualified_body,
        &import_request(qualified, leaf),
    )
    .unwrap();
    let ordinary = "use labels::Tri; pub struct Box { tag: Tri }";
    let ordinary_body = import_artifact(&[("labels", leaf), ("main", ordinary)]);
    observe(
        &kernel,
        "private-local-type-import",
        &ordinary_body,
        &import_request(ordinary, leaf),
    )
    .unwrap();
    for (label, actual_bridge, actual_leaf, include_bridge) in [
        ("private-facade", "use labels::Tri;", leaf, true),
        ("private-original", bridge, "enum Tri { A, B, C }", true),
        (
            "wrong-original-category",
            bridge,
            "pub classical fn Tri(x: Bit) -> Bit { x }",
            true,
        ),
        ("duplicate-import", "pub use labels::{Tri,Tri};", leaf, true),
        (
            "unanchored-type-export-cycle",
            "pub use labels::Tri;",
            "pub use bridge::Tri;",
            true,
        ),
        ("missing-alias-source", bridge, leaf, false),
    ] {
        let mut actual_rows = vec![("main", main), ("labels", actual_leaf)];
        if include_bridge {
            actual_rows.push(("bridge", actual_bridge));
        }
        let body = import_artifact(&actual_rows);
        let requested = import_request(main, actual_leaf);
        // With no renaming, a valid chain cannot exceed the source count.
        // This cycle exhausts that fuel before revisiting its active pair.
        let expected = if label == "unanchored-type-export-cycle" {
            "limit"
        } else {
            "contract"
        };
        assert_eq!(
            observe(&kernel, label, &body, &requested).unwrap_err().code,
            expected,
            "{label}"
        );
    }
    let changed_bridge = "pub use other::Tri;";
    let substituted = import_artifact(&[
        ("main", main),
        ("bridge", changed_bridge),
        ("labels", leaf),
        ("other", leaf),
    ]);
    assert_eq!(
        observe(
            &kernel,
            "same-width-other-canonical-type",
            &substituted,
            &requested
        )
        .unwrap_err()
        .code,
        "contract"
    );
    let mut facade_origin = requested.clone();
    for owner in facade_origin
        .attached
        .inputs
        .iter_mut()
        .chain(&mut facade_origin.attached.outputs)
    {
        owner.basis[1] = Atom::Enum(
            Arc::new(Origin {
                module: "bridge".into(),
                declaration: "Tri".into(),
                source: bridge.into(),
            }),
            vec!["A".into(), "B".into(), "C".into()],
        );
    }
    facade_origin.required = facade_origin.attached.clone();
    assert_eq!(
        observe(
            &kernel,
            "facade-is-not-a-type-declaration",
            &good,
            &facade_origin
        )
        .unwrap_err()
        .code,
        "contract"
    );
    assert!(log.summary().complete());
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn original_field_numerals_obey_the_common_source_grammar() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    for (label, width, accepted) in [
        ("canonical-field-numeral", "2", true),
        ("leading-zero-field-numeral", "02", false),
    ] {
        let source = format!("pub struct Word {{ bits: Bits<{width}> }}");
        let mut body = json::parse(&artifact([0, 1, 2, 3], [0; 4], [0, 1])).unwrap();
        replace(
            &mut body,
            "sources",
            Value::Array(vec![Value::object([
                ("path", text("labels")),
                ("text", text(&source)),
            ])]),
        );
        let body = json::encode(&body).unwrap();
        let mut requested = request();
        let basis = vec![
            Atom::Record(
                Arc::new(Origin {
                    module: "labels".into(),
                    declaration: "Word".into(),
                    source,
                }),
                vec!["bits".into()],
            ),
            Atom::Bits(2),
        ];
        for owner in requested
            .attached
            .inputs
            .iter_mut()
            .chain(&mut requested.attached.outputs)
        {
            owner.basis = basis.clone();
        }
        requested.required = requested.attached.clone();
        requested.logical = Matrix::identity(4).unwrap();
        let result = observe(&kernel, label, &body, &requested);
        if accepted {
            assert_eq!(result.unwrap().request(), &requested);
        } else {
            assert_eq!(result.unwrap_err().code, "contract");
        }
    }
}

fn field_request(source: &str) -> Request {
    let mut requested = request();
    let basis = vec![
        Atom::Record(
            Arc::new(Origin {
                module: "labels".into(),
                declaration: "Word".into(),
                source: source.into(),
            }),
            vec!["bits".into()],
        ),
        Atom::Bits(2),
    ];
    for owner in requested
        .attached
        .inputs
        .iter_mut()
        .chain(&mut requested.attached.outputs)
    {
        owner.basis = basis.clone();
    }
    requested.required = requested.attached.clone();
    requested.logical = Matrix::identity(4).unwrap();
    requested
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn original_field_naturals_check_actual_generic_helpers() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    // Each positive and every guard/overflow counterexample has the same
    // two-bit intended final width. Width mismatch cannot mask a missing rule.
    for (label, header, expression, accepted) in [
        ("field-nat-literal", "", "2", true),
        ("field-nat-precedence", "", "1+1*1", true),
        ("field-nat-left-association", "", "5-2-1", true),
        (
            "field-nat-wide-u32-intermediate",
            "",
            "4294967296+1-4294967295",
            true,
        ),
        ("field-nat-negative-intermediate", "", "0-1+3", false),
        (
            "field-nat-i128-intermediate-overflow",
            "",
            "170141183460469231731687303715884105727+1-170141183460469231731687303715884105727+1",
            false,
        ),
        (
            "field-nat-guarded-helper",
            "static fn dec[const k:Nat]() -> Nat requires k >= 1 {k-1}",
            "dec[3]()",
            true,
        ),
        (
            "field-nat-false-callee-premise",
            "static fn dec[const k:Nat]() -> Nat requires k >= 1 {k-1}",
            "dec[0]()+3",
            false,
        ),
        (
            "field-nat-generic-not-repaired",
            "static fn dec[const k:Nat]() -> Nat {k-1}",
            "dec[3]()",
            false,
        ),
        (
            "field-nat-nonlinear-not-repaired",
            "static fn square[const k:Nat]() -> Nat {k*k}",
            "square[1]()+1",
            false,
        ),
        (
            "field-nat-unused-private-helper",
            "static fn unused[const k:Nat]() -> Nat {k-1}",
            "2",
            false,
        ),
        (
            "field-nat-multiple-positional-arguments",
            "static fn sum[const a:Nat,const b:Nat]() -> Nat {a+b}",
            "sum[1,1]()",
            true,
        ),
        (
            "field-nat-original-ordinal-order",
            "static fn diff[const z:Nat,const a:Nat]() -> Nat requires z >= a {z-a}",
            "diff[3,1]()",
            true,
        ),
        (
            "field-nat-simultaneous-original-binders",
            "static fn sum[const n:Nat,const p:Nat]() -> Nat {n+p} static fn forward[const p:Nat]() -> Nat {sum[p+1,0]()}",
            "forward[1]()",
            true,
        ),
        (
            "field-nat-runtime-category",
            "fn runtime() -> Bit {0}",
            "runtime()+2",
            false,
        ),
    ] {
        let source = format!("{header} pub struct Word {{ bits: Bits<{expression}> }}");
        let body = source_artifact([0, 1, 2, 3], &[("labels", &source)]);
        let requested = field_request(&source);
        let result = observe(&kernel, label, &body, &requested);
        if accepted {
            assert_eq!(result.unwrap().request(), &requested, "{label}");
        } else {
            // Checked intermediate overflow retains the existing capacity
            // diagnostic; generic contract failures retain their own code.
            let expected = if label == "field-nat-i128-intermediate-overflow" {
                "limit"
            } else {
                "contract"
            };
            assert_eq!(result.unwrap_err().code, expected, "{label}");
        }
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn original_field_helper_imports_keep_source_visibility() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    for (label, bridge, accepted) in [
        ("field-helper-public-reexport", "pub use helper::dec;", true),
        ("field-helper-private-facade", "use helper::dec;", false),
    ] {
        let source = "pub struct Word { bits: Bits<bridge::dec[3]()> }";
        let helper = "pub static fn dec[const k:Nat]() -> Nat requires k >= 1 {k-1}";
        let body = source_artifact(
            [0, 1, 2, 3],
            &[("labels", source), ("bridge", bridge), ("helper", helper)],
        );
        let requested = field_request(source);
        let result = observe(&kernel, label, &body, &requested);
        if accepted {
            assert_eq!(result.unwrap().request(), &requested, "{label}");
        } else {
            assert_eq!(result.unwrap_err().code, "contract", "{label}");
        }
    }
}
