//! Small original-graph/native boundary checks. No source lowering is inferred.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::edition::Edition;
use crate::interchange::carrier::{Atom as Basis, Origin, Owner};
use crate::interchange::ordinary_root::{Selection, Storage as Ordinary};
use crate::interchange::runtime_root::{Atom, Request, Storage};
use crate::ir::*;

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn runtime_invalid_result_on_zero_probability_history_is_still_rejected() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    let source = "pub enum Tri{A,B,C} pub observe fn keep(q:Q<Tri>)->(Q<Tri>,Tri){let b=measure_z(init0());(q,if b{Tri::B}else{Tri::A})}";
    let mut requested = request(source);
    requested.parameters = vec![qtype(&basis(source))];
    requested.input_storage = vec![vec![Storage::Quantum(owner(source))]];
    requested.input_rows = vec![vec![]];
    requested.result = [
        vec![Atom::Finite(Basis::Pair)],
        qtype(&basis(source)),
        basis(source).into_iter().map(Atom::Finite).collect(),
    ]
    .concat();
    let Basis::Enum(origin, _) = basis(source).pop().unwrap() else {
        unreachable!()
    };
    let mut body = raw(source);
    body.classical_inputs.clear();
    body.operations = vec![
        RawOp::Init0 {
            output: TokenId(1),
            wire: WireId(2),
        },
        RawOp::MeasureZ {
            input: TokenId(1),
            output: ClassicalId(0),
        },
        RawOp::ClassicalConst {
            value: false,
            output: ClassicalId(1),
        },
    ];
    body.declared_effect = Effect::Observe;
    requested.public_effect = Effect::Observe;
    for invalid in [false, true] {
        let ids = vec![ClassicalId(0), ClassicalId(if invalid { 0 } else { 1 })];
        body.classical_outputs = ids.clone();
        requested.storage = vec![
            Storage::Tuple(2),
            Storage::Quantum(owner(source)),
            Storage::Ordinary(basis(source), Ordinary::Enum(Arc::clone(&origin), ids)),
        ];
        assert_eq!(accept(&kernel, source, &body, &requested).is_err(), invalid);
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn runtime_physical_unitary_cannot_leak_a_nominal_code_into_padding() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    let mut body = raw(SOURCE);
    body.operations = vec![RawOp::ApplyUnitary {
        input: TokenId(0),
        output: TokenId(1),
        steps: vec![CircuitStep {
            controls: vec![],
            action: CircuitAction::Monomial {
                indices: vec![0, 1],
                permutation: vec![0, 1, 3, 2],
                phases: vec![0; 4],
            },
        }],
    }];
    body.quantum_outputs = vec![TokenId(1)];
    kernel.verify(&body).unwrap();
    let mut requested = request(SOURCE);
    if let Storage::Quantum(owner) = &mut requested.storage[2] {
        owner.port.token = TokenId(1);
    }
    assert!(accept(&kernel, SOURCE, &body, &requested).is_err());
}

const SOURCE: &str =
    "pub enum Tri{A,B,C} pub unitary fn keep(flag:Bit,q:Q<Tri>)->(Bit,Q<Tri>){(flag,q)}";

fn basis(source: &str) -> Vec<Basis> {
    vec![Basis::Enum(
        Arc::new(Origin {
            module: "main".into(),
            declaration: "Tri".into(),
            source: source.into(),
        }),
        vec!["A".into(), "B".into(), "C".into()],
    )]
}
fn owner(source: &str) -> Owner {
    Owner {
        port: QuantumPort {
            token: TokenId(0),
            wires: vec![WireId(0), WireId(1)],
            shape: BasisShape { bits: 2 },
        },
        basis: basis(source),
    }
}
fn qtype(basis: &[Basis]) -> Vec<Atom> {
    std::iter::once(Atom::Quantum)
        .chain(basis.iter().cloned().map(Atom::Finite))
        .collect()
}
fn request(source: &str) -> Request {
    let quantum = qtype(&basis(source));
    Request {
        selection: Selection::Exported,
        module: "main".into(),
        declaration: "keep".into(),
        parameters: vec![vec![Atom::Finite(Basis::Bit)], quantum.clone()],
        input_storage: vec![
            vec![Storage::Ordinary(
                vec![Basis::Bit],
                Ordinary::Bit(ClassicalId(0)),
            )],
            vec![Storage::Quantum(owner(source))],
        ],
        input_rows: vec![vec![false], vec![true]],
        result: [
            vec![Atom::Finite(Basis::Pair), Atom::Finite(Basis::Bit)],
            quantum,
        ]
        .concat(),
        storage: vec![
            Storage::Tuple(2),
            Storage::Ordinary(vec![Basis::Bit], Ordinary::Bit(ClassicalId(0))),
            Storage::Quantum(owner(source)),
        ],
        public_effect: Effect::Unitary,
    }
}
fn raw(source: &str) -> RawProgram {
    RawProgram {
        quantum_inputs: vec![owner(source).port],
        classical_inputs: vec![ClassicalId(0)],
        operations: vec![],
        quantum_outputs: vec![TokenId(0)],
        classical_outputs: vec![ClassicalId(0)],
        declared_effect: Effect::Unitary,
    }
}
fn proposal(raw: &RawProgram, source: &str) -> Proposal {
    Proposal::from_raw_with_sources(
        raw,
        None,
        Version::V2,
        None,
        &[("main".into(), source.into())],
    )
    .unwrap()
}
fn accept(kernel: &Kernel, source: &str, body: &RawProgram, request: &Request) -> Result<Checked> {
    kernel.check_runtime_root(proposal(body, source).artifact(), &request.encode()?)
}

#[test]
fn runtime_request_is_versioned_bounded_metadata_without_an_acceptance_handle() {
    let request = request(SOURCE);
    let bytes = request.encode().unwrap();
    assert_eq!(Request::decode(&bytes).unwrap(), request);
    for (from, to) in [
        ("finite-runtime-root-v1", "finite-ordinary-root-v2"),
        ("\"version\":1", "\"version\":2"),
        ("\"quantum\"", "\"unknown\""),
    ] {
        let changed = String::from_utf8(bytes.clone()).unwrap().replace(from, to);
        assert_ne!(changed.as_bytes(), bytes);
        assert!(Request::decode(changed.as_bytes()).is_err());
    }
    let mut huge = request.clone();
    huge.input_storage = vec![vec![Storage::Tuple(2); 385]];
    assert!(huge.encode().is_err());
    let mut deep = Ordinary::Unit;
    for _ in 0..33 {
        deep = Ordinary::Tuple(vec![deep]);
    }
    let mut huge = request.clone();
    huge.storage = vec![Storage::Ordinary(vec![Basis::Unit], deep)];
    assert!(huge.encode().is_err());
    let mut huge = request;
    huge.input_storage = vec![vec![
        Storage::Ordinary(vec![Basis::Unit], Ordinary::Unit);
        129
    ]];
    assert!(huge.encode().is_err());
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn runtime_full_request_is_retained_by_execution_clone_and_fresh_recheck() {
    let (kernel, log) = Kernel::selected(Edition::E2026).unwrap().recording();
    let request = request(SOURCE);
    let checked = accept(&kernel, SOURCE, &raw(SOURCE), &request).unwrap();
    let program = checked.into_program();
    assert_eq!(program.runtime_result(), Some(&request));
    assert_eq!(program.clone().runtime_result(), Some(&request));
    let rechecked = kernel.check_program(&program).unwrap().into_program();
    assert_eq!(rechecked.runtime_result(), Some(&request));
    assert!(Arc::ptr_eq(&program.decoded, &rechecked.decoded));
    assert!(Arc::ptr_eq(
        program.runtime_result.as_ref().unwrap(),
        rechecked.runtime_result.as_ref().unwrap()
    ));
    assert_eq!(program.native.mode(), "--runtime-root-check");
    assert!(program.portable_artifact().is_err());
    assert!(log.summary().complete());
    assert_eq!(log.summary().decisions(), 2);
    assert!(kernel.check(program.artifact(), None).is_err());
    assert!(kernel.check(program.artifact(), program.request()).is_err());
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn runtime_stale_retained_type_storage_and_graph_cannot_borrow_original_bytes() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    let original = accept(&kernel, SOURCE, &raw(SOURCE), &request(SOURCE))
        .unwrap()
        .into_program();
    for variant in 0..6 {
        let mut changed = original.clone();
        let retained = Arc::make_mut(changed.runtime_result.as_mut().unwrap());
        match variant {
            0 => retained.parameters.reverse(),
            1 => {
                retained.storage.pop();
            }
            2 => retained.public_effect = Effect::Observe,
            3 => {
                if let Storage::Quantum(owner) = &mut retained.storage[2] {
                    owner.port.wires.reverse();
                }
            }
            4 => retained.input_rows.reverse(),
            _ => retained.selection = Selection::Internal,
        }
        assert!(
            kernel.check_program(&changed).is_err(),
            "stale metadata variant {variant}"
        );
    }
    let mut changed = original.clone();
    changed.derived_effect = Effect::Observe;
    assert!(kernel.check_program(&changed).is_err());
    let mut changed = original;
    changed.output_ports[0].wires.reverse();
    assert!(kernel.check_program(&changed).is_err());
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn runtime_actual_boundary_rejects_type_axis_domain_and_raw_owner_substitution() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    let original = request(SOURCE);
    for variant in 0..7 {
        let mut changed = original.clone();
        match variant {
            0 => changed.input_rows = vec![vec![false]],
            1 => changed.input_rows.reverse(),
            2 => changed.parameters.reverse(),
            3 => changed.result = qtype(&basis(SOURCE)),
            4 => {
                if let Storage::Quantum(owner) = &mut changed.input_storage[1][0] {
                    owner.basis = vec![Basis::Bits(2)];
                }
            }
            5 => {
                if let Storage::Quantum(owner) = &mut changed.storage[2] {
                    owner.port.wires.reverse();
                }
            }
            _ => {
                changed.storage = vec![Storage::Ordinary(
                    vec![Basis::Bit],
                    Ordinary::Bit(ClassicalId(0)),
                )]
            }
        }
        assert!(
            accept(&kernel, SOURCE, &raw(SOURCE), &changed).is_err(),
            "request variant {variant}"
        );
    }
    let mut body = raw(SOURCE);
    body.quantum_outputs.clear();
    assert!(accept(&kernel, SOURCE, &body, &original).is_err());
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn runtime_public_observe_is_not_sharpened_and_hidden_observation_is_not_unitary() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    let observing = SOURCE.replace("pub unitary", "pub observe");
    let mut requested = request(&observing);
    requested.public_effect = Effect::Observe;
    accept(&kernel, &observing, &raw(&observing), &requested).unwrap();
    requested.public_effect = Effect::Unitary;
    assert!(accept(&kernel, &observing, &raw(&observing), &requested).is_err());
    let mut body = raw(SOURCE);
    body.operations = vec![
        RawOp::Init0 {
            output: TokenId(1),
            wire: WireId(2),
        },
        RawOp::MeasureZ {
            input: TokenId(1),
            output: ClassicalId(1),
        },
    ];
    body.declared_effect = Effect::Observe;
    assert!(accept(&kernel, SOURCE, &body, &request(SOURCE)).is_err());
    let mut body = raw(&observing);
    body.operations = vec![
        RawOp::Init0 {
            output: TokenId(1),
            wire: WireId(2),
        },
        RawOp::MeasureZ {
            input: TokenId(1),
            output: ClassicalId(1),
        },
    ];
    body.declared_effect = Effect::Observe;
    requested.public_effect = Effect::Observe;
    accept(&kernel, &observing, &body, &requested).unwrap();
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn runtime_quantum_interface_requires_an_explicit_public_effect_even_without_operations() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    for header in ["pub fn", "pub classical fn"] {
        let source = SOURCE.replace("pub unitary fn", header);
        let body = raw(&source);
        assert!(body.operations.is_empty());
        assert!(accept(&kernel, &source, &body, &request(&source)).is_err());
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn runtime_zero_width_source_parameter_still_prevents_closed_execution() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    let source = "pub fn keep(empty:Unit)->Unit{empty}";
    let mut request = request(SOURCE);
    request.parameters = vec![vec![Atom::Finite(Basis::Unit)]];
    request.input_storage = vec![vec![Storage::Ordinary(vec![Basis::Unit], Ordinary::Unit)]];
    request.input_rows = vec![vec![]];
    request.result = vec![Atom::Finite(Basis::Unit)];
    request.storage = vec![Storage::Ordinary(vec![Basis::Unit], Ordinary::Unit)];
    let body = RawProgram {
        quantum_inputs: vec![],
        classical_inputs: vec![],
        operations: vec![],
        quantum_outputs: vec![],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    let program = accept(&kernel, source, &body, &request)
        .unwrap()
        .into_program();
    assert!(matches!(
        crate::sim::run_closed(&program, crate::sim::SimulationLimits::default()),
        Err(crate::sim::SimulationError::NotClosed(_))
    ));
    assert!(
        crate::sim::sample_closed(
            &program,
            &mut crate::sim::SplitMix64::new(0),
            crate::sim::SampleLimits::default()
        )
        .is_err()
    );
    let erased = Request {
        parameters: vec![],
        input_storage: vec![],
        ..request
    };
    assert!(accept(&kernel, source, &body, &erased).is_err());
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn runtime_singleton_quantum_owner_survives_despite_zero_physical_width() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    let source = "pub enum One{Only} pub unitary fn keep(q:Q<One>)->Q<One>{q}";
    let basis = vec![Basis::Enum(
        Arc::new(Origin {
            module: "main".into(),
            declaration: "One".into(),
            source: source.into(),
        }),
        vec!["Only".into()],
    )];
    let owner = Owner {
        port: QuantumPort {
            token: TokenId(0),
            wires: vec![],
            shape: BasisShape { bits: 0 },
        },
        basis,
    };
    let mut request = request(SOURCE);
    request.parameters = vec![qtype(&owner.basis)];
    request.input_storage = vec![vec![Storage::Quantum(owner.clone())]];
    request.input_rows = vec![vec![]];
    request.result = qtype(&owner.basis);
    request.storage = vec![Storage::Quantum(owner.clone())];
    let mut body = raw(SOURCE);
    body.quantum_inputs = vec![owner.port];
    body.classical_inputs.clear();
    body.classical_outputs.clear();
    let program = accept(&kernel, source, &body, &request)
        .unwrap()
        .into_program();
    assert_eq!(program.runtime_result().unwrap().input_storage.len(), 1);
    assert_eq!(program.output_ports().len(), 1);
    assert_eq!(program.output_ports()[0].shape.bits, 0);
    request.storage.clear();
    assert!(accept(&kernel, source, &body, &request).is_err());
}

// Deliberately bypass the host request parser. Lean must independently refuse
// malformed original requests even when the supplied retained view is valid.
#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn runtime_original_request_decoder_and_scope_cannot_be_bypassed_by_a_valid_view() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    let request = request(SOURCE);
    let proposed = proposal(&raw(SOURCE), SOURCE);
    let bytes = request.encode().unwrap();
    let original = accept(&kernel, SOURCE, &raw(SOURCE), &request)
        .unwrap()
        .into_program();
    let graph = runtime_root::complete(original.execution_view_graph(), &request).unwrap();
    for changed in [
        String::from_utf8(bytes.clone())
            .unwrap()
            .replace("\"version\":1", "\"version\":2"),
        String::from_utf8(bytes.clone())
            .unwrap()
            .replace("\"tag\":\"quantum\"", "\"tag\":\"quantum\",\"ignored\":0"),
    ] {
        assert_ne!(changed.as_bytes(), bytes);
        let subject = kernel
            .subject(proposed.artifact(), Some(changed.as_bytes()))
            .unwrap();
        assert!(
            Kernel::submit_subject(
                subject,
                "--runtime-root-check",
                Some(View {
                    graph: &graph,
                    caller: None
                })
            )
            .is_err()
        );
    }
    let subject = kernel.subject(proposed.artifact(), Some(&bytes)).unwrap();
    assert!(Kernel::inspect_subject(Arc::clone(&subject), "--runtime-root-check").is_err());
    assert!(
        Kernel::submit_subject(
            subject,
            "--runtime-root-check",
            Some(View {
                graph: &graph,
                caller: Some((&graph, &[]))
            })
        )
        .is_err()
    );
    assert!(
        Kernel::new("/nonexistent-qleisli-runtime-kernel", Edition::E2026)
            .check_runtime_root(proposed.artifact(), &bytes)
            .is_err()
    );
}
