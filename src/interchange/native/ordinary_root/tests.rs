//! Actual native calls, complete measurement histories and stale typed views.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::edition::Edition;
use crate::interchange::carrier::{Atom, Origin};
use crate::interchange::ordinary_root::{Request, Selection, Storage};
use crate::ir::*;

const SOURCE: &str = "pub enum Tri { Zero, One, Other }\npub struct Result { pub choice: Tri, pub flag: Bit }\npub observe fn main() -> Result { let bit = measure_z(h(init0())); Result { choice: if bit { Tri::One } else { Tri::Zero }, flag: bit } }";

fn origin(name: &str) -> Arc<Origin> {
    Arc::new(Origin {
        module: "main".into(),
        declaration: name.into(),
        source: SOURCE.into(),
    })
}

fn request() -> Request {
    Request {
        selection: Selection::Project,
        module: "main".into(),
        declaration: "main".into(),
        basis: vec![
            Atom::Record(origin("Result"), vec!["choice".into(), "flag".into()]),
            Atom::Enum(
                origin("Tri"),
                vec!["Zero".into(), "One".into(), "Other".into()],
            ),
            Atom::Bit,
        ],
        storage: Storage::Record(
            origin("Result"),
            vec![
                (
                    "choice".into(),
                    Storage::Enum(origin("Tri"), vec![ClassicalId(4), ClassicalId(1)]),
                ),
                ("flag".into(), Storage::Bit(ClassicalId(0))),
            ],
        ),
        public_effect: Effect::Observe,
    }
}

fn measured(high: bool) -> RawProgram {
    RawProgram {
        quantum_inputs: vec![],
        classical_inputs: vec![],
        quantum_outputs: vec![],
        classical_outputs: vec![ClassicalId(4), ClassicalId(1), ClassicalId(0)],
        declared_effect: Effect::Observe,
        operations: vec![
            RawOp::Init0 {
                output: TokenId(0),
                wire: WireId(0),
            },
            RawOp::Gate {
                gate: SingleGate::H,
                input: TokenId(0),
                output: TokenId(1),
            },
            RawOp::MeasureZ {
                input: TokenId(1),
                output: ClassicalId(0),
            },
            RawOp::ClassicalConst {
                value: high,
                output: ClassicalId(1),
            },
            RawOp::ClassicalBranch {
                condition: ClassicalId(0),
                then_ops: vec![RawOp::ClassicalConst {
                    value: true,
                    output: ClassicalId(2),
                }],
                else_ops: vec![RawOp::ClassicalConst {
                    value: false,
                    output: ClassicalId(3),
                }],
                quantum_phis: vec![],
                classical_phis: vec![ClassicalPhi {
                    then_id: ClassicalId(2),
                    else_id: ClassicalId(3),
                    output: ClassicalId(4),
                }],
            },
        ],
    }
}

fn proposal(raw: &RawProgram) -> Proposal {
    Proposal::from_raw_with_sources(
        raw,
        None,
        Version::V2,
        None,
        &[("main".into(), SOURCE.into())],
    )
    .unwrap()
}

// Bypass only Rust's request reader in the test: the actual native decoder
// must reject too, using a complete graph/view rather than an inspection error.
fn reject_request_both_readers(kernel: &Kernel, artifact: &[u8], original: &Request, wrong: &[u8]) {
    assert!(kernel.check_ordinary_root(artifact, wrong).is_err());
    let subject = kernel.subject(artifact, Some(wrong)).unwrap();
    let mut budget = crate::contract::exact::Budget::new(crate::contract::DEFAULT_EXACT_WORK);
    let decoded = Arc::new(
        crate::interchange::decode_subject_with_types(&subject, &mut budget, None, Some(original))
            .unwrap(),
    );
    let (derived_effect, output_ports) = view::metadata(&decoded.programs[decoded.root]).unwrap();
    let prepared = Prepared {
        subject: Arc::clone(&subject),
        decoded,
        derived_effect,
        output_ports,
    };
    let graph = ordinary_root::complete(prepared.graph(), original).unwrap();
    assert!(
        Kernel::submit_subject(
            subject,
            "--ordinary-root-check",
            Some(View {
                graph: &graph,
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
fn actual_typed_result_graph_and_all_histories_reach_native_acceptance() {
    let (kernel, log) = Kernel::selected(Edition::E2026).unwrap().recording();
    let requested = request();
    let bytes = requested.encode().unwrap();
    assert_eq!(Request::decode(&bytes).unwrap(), requested);
    let proposed = proposal(&measured(false));
    let checked = kernel
        .check_ordinary_root(proposed.artifact(), &bytes)
        .unwrap();
    let program = checked.into_program();
    assert_eq!(program.ordinary_result(), Some(&requested));
    assert_eq!(program.clone().ordinary_result(), Some(&requested));
    assert_eq!(program.native.mode(), "--ordinary-root-check");
    assert!(kernel.check_program(&program).is_err());
    assert!(log.summary().complete());
    // Original untyped checking must not erase the source/type request.
    assert!(kernel.check(proposed.artifact(), None).is_err());
    let invalid = proposal(&measured(true));
    assert!(
        kernel
            .check_ordinary_root(invalid.artifact(), &bytes)
            .is_err()
    );
    let mut false_pure = request();
    false_pure.public_effect = Effect::Unitary;
    assert!(
        kernel
            .check_ordinary_root(proposed.artifact(), &false_pure.encode().unwrap())
            .is_err()
    );
    let mut swapped = request();
    let Storage::Record(_, fields) = &mut swapped.storage else {
        unreachable!()
    };
    fields[0].1 = Storage::Enum(origin("Tri"), vec![ClassicalId(1), ClassicalId(4)]);
    assert!(
        kernel
            .check_ordinary_root(proposed.artifact(), &swapped.encode().unwrap())
            .is_err()
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn stale_actual_metadata_and_wrong_scope_refuse_without_fallback() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    let proposed = proposal(&measured(false));
    let request = request();
    let bytes = request.encode().unwrap();
    let subject = kernel.subject(proposed.artifact(), Some(&bytes)).unwrap();
    let mut budget = crate::contract::exact::Budget::new(crate::contract::DEFAULT_EXACT_WORK);
    let decoded = Arc::new(
        crate::interchange::decode_subject_with_types(&subject, &mut budget, None, Some(&request))
            .unwrap(),
    );
    let (derived_effect, output_ports) = view::metadata(&decoded.programs[decoded.root]).unwrap();
    let prepared = Prepared {
        subject: Arc::clone(&subject),
        decoded,
        derived_effect,
        output_ports,
    };
    for mutation in 0..5 {
        let mut stale = request.clone();
        match mutation {
            0 => stale.public_effect = Effect::Isometry,
            1 => stale.declaration = "other".into(),
            2 => stale.selection = Selection::Exported,
            3 => stale.basis[0] = Atom::Unit,
            _ => stale.storage = Storage::Tuple(vec![]),
        }
        let graph = ordinary_root::complete(prepared.graph(), &stale).unwrap();
        assert!(
            Kernel::submit_subject(
                Arc::clone(&subject),
                "--ordinary-root-check",
                Some(View {
                    graph: &graph,
                    caller: None
                })
            )
            .is_err()
        );
    }
    assert!(Kernel::inspect_subject(subject, "--ordinary-root-check").is_err());
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn strict_request_and_original_output_structure_cannot_be_erased() {
    use crate::interchange::json::{self, Value};
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    let request = request();
    let bytes = request.encode().unwrap();
    let proposed = proposal(&measured(false));
    for (key, replacement) in [
        ("version", Value::Number(0)),
        ("profile", Value::String("finite-carrier-pure-v1".into())),
        ("selection", Value::String("inspection".into())),
    ] {
        let Value::Object(mut fields) = json::parse(&bytes).unwrap() else {
            unreachable!()
        };
        fields.insert(key.into(), replacement);
        let wrong = json::encode(&Value::Object(fields)).unwrap();
        reject_request_both_readers(&kernel, proposed.artifact(), &request, &wrong);
    }
    let Value::Object(mut fields) = json::parse(&bytes).unwrap() else {
        unreachable!()
    };
    fields.insert("trusted_receipt".into(), Value::String("accepted".into()));
    reject_request_both_readers(
        &kernel,
        proposed.artifact(),
        &request,
        &json::encode(&Value::Object(fields)).unwrap(),
    );
    assert!(kernel.check(proposed.artifact(), Some(&bytes)).is_err());

    // Make the flattened output map agree with the changed storage. The
    // independent declared field order must still reject the request.
    let mut reordered = request.clone();
    let Storage::Record(_, fields) = &mut reordered.storage else {
        unreachable!()
    };
    fields.swap(0, 1);
    let mut raw = measured(false);
    raw.classical_outputs = vec![ClassicalId(0), ClassicalId(4), ClassicalId(1)];
    assert!(
        kernel
            .check_ordinary_root(proposal(&raw).artifact(), &reordered.encode().unwrap())
            .is_err()
    );
    raw = measured(false);
    raw.declared_effect = Effect::Unitary;
    assert!(
        kernel
            .check_ordinary_root(proposal(&raw).artifact(), &bytes)
            .is_err()
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn empty_record_cannot_be_replaced_by_an_equal_width_unit_or_tuple() {
    let source = "pub struct Empty {} pub observe fn main()->Empty{Empty {}}";
    let original = Arc::new(Origin {
        module: "main".into(),
        declaration: "Empty".into(),
        source: source.into(),
    });
    let mut request = Request {
        selection: Selection::Project,
        module: "main".into(),
        declaration: "main".into(),
        basis: vec![Atom::Record(Arc::clone(&original), vec![])],
        storage: Storage::Record(original, vec![]),
        public_effect: Effect::Observe,
    };
    let raw = RawProgram {
        quantum_inputs: vec![],
        classical_inputs: vec![],
        operations: vec![],
        quantum_outputs: vec![],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    let proposed = Proposal::from_raw_with_sources(
        &raw,
        None,
        Version::V2,
        None,
        &[("main".into(), source.into())],
    )
    .unwrap();
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    assert!(
        kernel
            .check_ordinary_root(proposed.artifact(), &request.encode().unwrap())
            .is_ok()
    );
    for stored in [Storage::Unit, Storage::Bits(vec![]), Storage::Tuple(vec![])] {
        request.storage = stored;
        assert!(
            kernel
                .check_ordinary_root(proposed.artifact(), &request.encode().unwrap())
                .is_err()
        );
    }
}
