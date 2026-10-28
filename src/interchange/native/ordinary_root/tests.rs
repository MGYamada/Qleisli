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
        parameters: vec![],
        input_storage: vec![],
        input_rows: vec![vec![]],
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
    for mutation in 0..8 {
        let mut stale = request.clone();
        match mutation {
            0 => stale.public_effect = Effect::Isometry,
            1 => stale.declaration = "other".into(),
            2 => stale.selection = Selection::Exported,
            3 => stale.basis[0] = Atom::Unit,
            4 => stale.storage = Storage::Tuple(vec![]),
            5 => stale.parameters = vec![vec![Atom::Unit]],
            6 => stale.input_storage = vec![Storage::Unit],
            _ => stale.input_rows = vec![],
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
fn internal_declaration_selection_keeps_original_visibility_and_entry_category() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    for (name, public, allowed) in [
        ("helper", false, Selection::Internal),
        ("helper", true, Selection::Exported),
        ("main", false, Selection::Project),
    ] {
        let source = format!(
            "enum E {{A}} {}fn {name}()->E{{E::A}}",
            if public { "pub " } else { "" }
        );
        let origin = Arc::new(Origin {
            module: "main".into(),
            declaration: "E".into(),
            source: source.clone(),
        });
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
            crate::interchange::Version::V2,
            None,
            &[("main".into(), source)],
        )
        .unwrap();
        for selection in [Selection::Project, Selection::Exported, Selection::Internal] {
            let request = Request {
                selection,
                module: "main".into(),
                declaration: name.into(),
                parameters: vec![],
                input_storage: vec![],
                input_rows: vec![vec![]],
                basis: vec![Atom::Enum(Arc::clone(&origin), vec!["A".into()])],
                storage: Storage::Enum(Arc::clone(&origin), vec![]),
                public_effect: Effect::Unitary,
            };
            let actual =
                kernel.check_ordinary_root(proposed.artifact(), &request.encode().unwrap());
            assert_eq!(actual.is_ok(), selection == allowed, "{name} {selection:?}");
            if let Ok(accepted) = actual {
                assert_eq!(accepted.program().ordinary_result().unwrap(), &request);
            }
        }
    }
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
        ("version", Value::Number(1)),
        ("profile", Value::String("finite-ordinary-root-v1".into())),
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

fn ordinary_input() -> (Request, RawProgram, Proposal) {
    let source = "enum Tri { A,B,C } pub fn identity(value:Tri)->Tri{value}";
    let origin = Arc::new(Origin {
        module: "main".into(),
        declaration: "Tri".into(),
        source: source.into(),
    });
    let basis = vec![Atom::Enum(
        Arc::clone(&origin),
        vec!["A".into(), "B".into(), "C".into()],
    )];
    let storage = Storage::Enum(origin, vec![ClassicalId(0), ClassicalId(1)]);
    let request = Request {
        selection: Selection::Exported,
        module: "main".into(),
        declaration: "identity".into(),
        parameters: vec![basis.clone()],
        input_storage: vec![storage.clone()],
        input_rows: vec![vec![false, false], vec![true, false], vec![false, true]],
        basis,
        storage,
        public_effect: Effect::Unitary,
    };
    let raw = RawProgram {
        quantum_inputs: vec![],
        classical_inputs: vec![ClassicalId(0), ClassicalId(1)],
        operations: vec![],
        quantum_outputs: vec![],
        classical_outputs: vec![ClassicalId(0), ClassicalId(1)],
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
    (request, raw, proposed)
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn complete_ordinary_inputs_are_retained_and_last_input_is_actually_checked() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    let (request, mut raw, proposed) = ordinary_input();
    let checked = kernel
        .check_ordinary_root(proposed.artifact(), &request.encode().unwrap())
        .unwrap();
    assert_eq!(checked.program().ordinary_result(), Some(&request));
    assert!(matches!(
        crate::sim::run_closed(checked.program(), Default::default()),
        Err(crate::sim::SimulationError::NotClosed(_))
    ));
    // A and B remain valid; only the final canonical input C yields padding 3.
    raw.operations.push(RawOp::ClassicalXor {
        left: ClassicalId(0),
        right: ClassicalId(1),
        output: ClassicalId(2),
    });
    raw.classical_outputs[0] = ClassicalId(2);
    let mut wrong = request.clone();
    let Storage::Enum(_, ids) = &mut wrong.storage else {
        unreachable!()
    };
    ids[0] = ClassicalId(2);
    let proposed = Proposal::from_raw_with_sources(
        &raw,
        None,
        Version::V2,
        None,
        &[(
            "main".into(),
            request.parameters[0]
                .iter()
                .find_map(|atom| match atom {
                    Atom::Enum(origin, _) => Some(origin.source.clone()),
                    _ => None,
                })
                .unwrap(),
        )],
    )
    .unwrap();
    assert!(
        kernel
            .check_ordinary_root(proposed.artifact(), &wrong.encode().unwrap())
            .is_err()
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn ordinary_input_subsets_permutations_padding_and_same_width_erasure_refuse() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    let (original, _, proposed) = ordinary_input();
    for mutation in 0..10 {
        let mut wrong = original.clone();
        match mutation {
            0 => {
                wrong.input_rows.pop();
            }
            1 => wrong.input_rows.swap(0, 2),
            2 => wrong.input_rows[2] = wrong.input_rows[0].clone(),
            3 => wrong.input_rows.push(vec![true, true]),
            4 => wrong.input_rows[0].pop().map(|_| ()).unwrap(),
            5 => wrong.parameters[0] = vec![Atom::Bits(2)],
            6 => wrong.input_storage[0] = Storage::Bits(vec![ClassicalId(0), ClassicalId(1)]),
            7 => {
                let Storage::Enum(_, ids) = &mut wrong.input_storage[0] else {
                    unreachable!()
                };
                ids.swap(0, 1);
            }
            8 => wrong.input_storage.push(Storage::Unit),
            _ => wrong.parameters.push(vec![Atom::Unit]),
        }
        assert!(
            kernel
                .check_ordinary_root(proposed.artifact(), &wrong.encode().unwrap())
                .is_err(),
            "mutation {mutation} was accepted"
        );
    }
    // A complete v1-shaped packet cannot bypass either actual decoder.
    use crate::interchange::json::{self, Value};
    let Value::Object(mut fields) = json::parse(&original.encode().unwrap()).unwrap() else {
        unreachable!()
    };
    for field in ["parameters", "input_storage", "input_rows"] {
        fields.remove(field);
    }
    fields.insert("version".into(), Value::Number(1));
    fields.insert(
        "profile".into(),
        Value::String("finite-ordinary-root-v1".into()),
    );
    reject_request_both_readers(
        &kernel,
        proposed.artifact(),
        &original,
        &json::encode(&Value::Object(fields)).unwrap(),
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
        parameters: vec![],
        input_storage: vec![],
        input_rows: vec![vec![]],
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

fn imported_input() -> (Request, RawProgram, Vec<(String, String)>) {
    let (mut request, raw, _) = ordinary_input();
    let source = "pub enum Tri { A,B,C } pub enum Other { A,B,C }";
    let origin = Arc::new(Origin {
        module: "labels".into(),
        declaration: "Tri".into(),
        source: source.into(),
    });
    request.basis = vec![Atom::Enum(
        Arc::clone(&origin),
        vec!["A".into(), "B".into(), "C".into()],
    )];
    request.parameters = vec![request.basis.clone()];
    request.storage = Storage::Enum(origin, vec![ClassicalId(0), ClassicalId(1)]);
    request.input_storage = vec![request.storage.clone()];
    (
        request,
        raw,
        vec![
            (
                "main".into(),
                "use facade::Tri; pub fn identity(value:Tri)->Tri{value}".into(),
            ),
            ("facade".into(), "pub use labels::Tri;".into()),
            ("labels".into(), source.into()),
        ],
    )
}

fn proposed_imports(raw: &RawProgram, sources: &[(String, String)]) -> Proposal {
    Proposal::from_raw_with_sources(raw, None, Version::V2, None, sources).unwrap()
}

fn prepared_imports(kernel: &Kernel, artifact: &[u8], request: &Request) -> Prepared {
    let subject = kernel
        .subject(artifact, Some(&request.encode().unwrap()))
        .unwrap();
    let mut budget = crate::contract::exact::Budget::new(crate::contract::DEFAULT_EXACT_WORK);
    let decoded = Arc::new(
        crate::interchange::decode_subject_with_types(&subject, &mut budget, None, Some(request))
            .expect("bounded proposed rows must reach the native coverage gate"),
    );
    let (derived_effect, output_ports) = view::metadata(&decoded.programs[decoded.root]).unwrap();
    Prepared {
        subject,
        decoded,
        derived_effect,
        output_ports,
    }
}

fn reject_imports_with_native_view(kernel: &Kernel, artifact: &[u8], request: &Request) {
    let prepared = prepared_imports(kernel, artifact, request);
    let graph = ordinary_root::complete(prepared.graph(), request).unwrap();
    let error = Kernel::submit_subject(
        prepared.subject,
        "--ordinary-root-check",
        Some(View {
            graph: &graph,
            caller: None,
        }),
    )
    .unwrap_err();
    assert_eq!(error.message, runtime::REJECTION_MESSAGE);
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn imported_parameter_domain_and_exact_original_rows_are_retained() {
    let (kernel, log) = Kernel::selected(Edition::E2026).unwrap().recording();
    let (request, raw, sources) = imported_input();
    let proposed = proposed_imports(&raw, &sources);
    let bytes = request.encode().unwrap();
    let checked = kernel
        .check_ordinary_root(proposed.artifact(), &bytes)
        .unwrap();
    let program = checked.program();
    assert_eq!(checked.artifact(), proposed.artifact());
    assert_eq!(checked.request(), Some(bytes.as_slice()));
    assert_eq!(program.ordinary_result(), Some(&request));
    assert_eq!(program.decoded.sources, sources);
    assert_eq!(
        program.raw().classical_inputs,
        vec![ClassicalId(0), ClassicalId(1)]
    );
    assert_eq!(
        program.raw().classical_outputs,
        program.raw().classical_inputs
    );
    assert_eq!(
        request.input_rows,
        vec![vec![false, false], vec![true, false], vec![false, true]]
    );
    assert!(
        matches!(&request.input_storage[0], Storage::Enum(origin, ids)
        if origin.module == "labels" && origin.declaration == "Tri"
            && ids == &program.raw().classical_inputs)
    );
    assert_eq!(request.storage, request.input_storage[0]);
    assert_eq!(program.native.mode(), "--ordinary-root-check");
    assert!(matches!(
        crate::sim::run_closed(program, Default::default()),
        Err(crate::sim::SimulationError::NotClosed(_))
    ));
    assert_eq!(log.summary().decisions(), 1);
    assert!(log.summary().complete());
    assert!(kernel.check(proposed.artifact(), None).is_err());
    assert_eq!(
        Kernel::new("/missing-explicit-ordinary-import-kernel", Edition::E2026)
            .check_ordinary_root(proposed.artifact(), &bytes)
            .unwrap_err()
            .code,
        "io"
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn native_import_coverage_rejects_missing_private_changed_and_unrelated_rows() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    let (request, raw, sources) = imported_input();
    for mutation in 0..7 {
        let mut wrong = sources.clone();
        match mutation {
            0 => {
                wrong.remove(1);
            }
            1 => wrong[1].1 = "pub use missing::Tri;".into(),
            2 => wrong[1].1 = "use labels::Tri;".into(),
            3 => wrong.push(("unrelated".into(), "pub enum Spare { A }".into())),
            // Preparing every valid Nat helper does not justify its source row.
            4 => wrong.push(("unrelated".into(), "static fn unused()->Nat{2}".into())),
            5 => {
                wrong[1].1 = "pub use bridge::Tri;".into();
                wrong.push(("bridge".into(), "pub use facade::Tri;".into()));
            }
            _ => wrong[1].1 = "pub struct Tri {}".into(),
        }
        let proposed = proposed_imports(&raw, &wrong);
        reject_imports_with_native_view(&kernel, proposed.artifact(), &request);
    }

    // Same code width, labels and SSA map cannot replace the canonical type.
    let mut wrong = request.clone();
    let Atom::Enum(original, labels) = &request.basis[0] else {
        unreachable!()
    };
    let other = Arc::new(Origin {
        declaration: "Other".into(),
        ..original.as_ref().clone()
    });
    wrong.basis = vec![Atom::Enum(Arc::clone(&other), labels.clone())];
    wrong.parameters = vec![wrong.basis.clone()];
    wrong.storage = Storage::Enum(other, vec![ClassicalId(0), ClassicalId(1)]);
    wrong.input_storage = vec![wrong.storage.clone()];
    let proposed = proposed_imports(&raw, &sources);
    reject_imports_with_native_view(&kernel, proposed.artifact(), &wrong);
    let mut subset = request.clone();
    subset.input_rows.pop();
    reject_imports_with_native_view(&kernel, proposed.artifact(), &subset);
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn imported_intermediate_source_bytes_are_bound_to_the_actual_qdv_view() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    let (request, raw, sources) = imported_input();
    let proposed = proposed_imports(&raw, &sources);
    kernel
        .check_ordinary_root(proposed.artifact(), &request.encode().unwrap())
        .unwrap();
    let mut prepared = prepared_imports(&kernel, proposed.artifact(), &request);
    let retained = Arc::get_mut(&mut prepared.decoded).unwrap();
    assert_eq!(retained.sources[1].0, "facade");
    retained.sources[1]
        .1
        .push_str("\n// different retained original bytes\n");
    let graph = ordinary_root::complete(prepared.graph(), &request).unwrap();
    // The unchanged artifact is valid; only the retained source bytes differ.
    let error = Kernel::submit_subject(
        prepared.subject,
        "--ordinary-root-check",
        Some(View {
            graph: &graph,
            caller: None,
        }),
    )
    .unwrap_err();
    assert_eq!(error.code, "decoded_view");
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn zero_width_reexported_parameter_and_result_cannot_erase_the_record() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    let source = "pub struct Empty {}";
    let origin = Arc::new(Origin {
        module: "labels".into(),
        declaration: "Empty".into(),
        source: source.into(),
    });
    let basis = vec![Atom::Record(Arc::clone(&origin), vec![])];
    let storage = Storage::Record(origin, vec![]);
    let request = Request {
        selection: Selection::Exported,
        module: "main".into(),
        declaration: "identity".into(),
        parameters: vec![basis.clone()],
        input_storage: vec![storage.clone()],
        input_rows: vec![vec![]],
        basis,
        storage,
        public_effect: Effect::Unitary,
    };
    let raw = RawProgram {
        quantum_inputs: vec![],
        classical_inputs: vec![],
        operations: vec![],
        quantum_outputs: vec![],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    let sources = vec![
        (
            "main".into(),
            "use facade::Empty; pub fn identity(value:Empty)->Empty{value}".into(),
        ),
        ("facade".into(), "pub use labels::Empty;".into()),
        ("labels".into(), source.into()),
    ];
    let proposed = proposed_imports(&raw, &sources);
    let checked = kernel
        .check_ordinary_root(proposed.artifact(), &request.encode().unwrap())
        .unwrap();
    assert_eq!(checked.program().ordinary_result(), Some(&request));
    assert_eq!(checked.program().decoded.sources, sources);
    for input in [true, false] {
        let mut wrong = request.clone();
        if input {
            wrong.input_storage[0] = Storage::Unit;
        } else {
            wrong.storage = Storage::Unit;
        }
        reject_imports_with_native_view(&kernel, proposed.artifact(), &wrong);
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn zero_width_typed_parameters_require_an_invocation_in_closed_runtime_apis() {
    use crate::sim::{SampleLimits, SimulationLimits, SplitMix64, run_closed, sample_closed};
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    for ty in ["Unit", "Bits<0>", "Empty", "(Unit,Empty)"] {
        let source = format!("pub struct Empty {{}} pub fn choose(value:{ty})->{ty} {{value}}");
        let origin = Arc::new(Origin {
            module: "main".into(),
            declaration: "Empty".into(),
            source: source.clone(),
        });
        let (basis, storage) = match ty {
            "Unit" => (vec![Atom::Unit], Storage::Unit),
            "Bits<0>" => (vec![Atom::Bits(0)], Storage::Bits(vec![])),
            "Empty" => (
                vec![Atom::Record(Arc::clone(&origin), vec![])],
                Storage::Record(Arc::clone(&origin), vec![]),
            ),
            _ => (
                vec![
                    Atom::Pair,
                    Atom::Unit,
                    Atom::Record(Arc::clone(&origin), vec![]),
                ],
                Storage::Pair(
                    Box::new(Storage::Unit),
                    Box::new(Storage::Record(Arc::clone(&origin), vec![])),
                ),
            ),
        };
        let raw = RawProgram {
            quantum_inputs: vec![],
            classical_inputs: vec![],
            operations: vec![],
            quantum_outputs: vec![],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        let request = Request {
            selection: Selection::Exported,
            module: "main".into(),
            declaration: "choose".into(),
            parameters: vec![basis.clone()],
            input_storage: vec![storage.clone()],
            input_rows: vec![vec![]],
            basis,
            storage,
            public_effect: Effect::Unitary,
        };
        let proposal = crate::interchange::native::Proposal::from_raw_with_sources(
            &raw,
            None,
            crate::interchange::Version::V2,
            None,
            &[("main".into(), source)],
        )
        .unwrap();
        let checked = kernel
            .check_ordinary_root(proposal.artifact(), &request.encode().unwrap())
            .unwrap();
        let program = checked.into_program();
        assert_eq!(program.ordinary_result().unwrap().parameters.len(), 1);
        assert!(program.raw().classical_inputs.is_empty());
        assert!(
            run_closed(&program, SimulationLimits::default()).is_err(),
            "{ty} still needs its one logical argument"
        );
        assert!(
            sample_closed(
                &program.clone(),
                &mut SplitMix64::new(0),
                SampleLimits::default()
            )
            .is_err(),
            "{ty} sampling erased the logical argument"
        );
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn typed_unit_result_without_parameters_remains_a_closed_runtime_program() {
    let source = "pub fn choose()->Unit {()}";
    let raw = RawProgram {
        quantum_inputs: vec![],
        classical_inputs: vec![],
        operations: vec![],
        quantum_outputs: vec![],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    let request = Request {
        selection: Selection::Exported,
        module: "main".into(),
        declaration: "choose".into(),
        parameters: vec![],
        input_storage: vec![],
        input_rows: vec![vec![]],
        basis: vec![Atom::Unit],
        storage: Storage::Unit,
        public_effect: Effect::Unitary,
    };
    let proposal = crate::interchange::native::Proposal::from_raw_with_sources(
        &raw,
        None,
        crate::interchange::Version::V2,
        None,
        &[("main".into(), source.into())],
    )
    .unwrap();
    let program = Kernel::selected(Edition::E2026)
        .unwrap()
        .check_ordinary_root(proposal.artifact(), &request.encode().unwrap())
        .unwrap()
        .into_program();
    assert_eq!(
        crate::sim::run_closed(&program, crate::sim::SimulationLimits::default()).unwrap(),
        std::collections::BTreeMap::from([(vec![], 1.0)])
    );
    assert!(
        crate::sim::sample_closed(
            &program,
            &mut crate::sim::SplitMix64::new(0),
            crate::sim::SampleLimits::default()
        )
        .unwrap()
        .bits
        .is_empty()
    );
}
