//! Full runtime interfaces reach fresh native checking from original source.
//! These small regressions do not prove source or numerical preservation.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
mod common;
use common::SourceRoot;
use qleisli::edition::Edition;
use qleisli::frontend::compile::{ParsedProgram, compile_project};
use qleisli::interchange::carrier::Atom as Basis;
use qleisli::interchange::native::Kernel;
use qleisli::interchange::runtime_root::{Atom, Storage};
use qleisli::sim::{SimulationLimits, run_closed};
use std::collections::BTreeMap;

fn kernel() -> Kernel {
    Kernel::new(
        std::env::var_os("QLEISLI_KERNEL").expect("explicit native test gate"),
        Edition::E2026,
    )
}

fn selected(source: &str) -> qleisli::frontend::compile::SelectedRuntimeProgram {
    ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([("main".into(), source.into())]),
    )
    .unwrap()
    .instantiate_runtime_with_types(
        "main::keep",
        Default::default(),
        Default::default(),
        Default::default(),
    )
    .unwrap()
    .compile_runtime_with_kernel(&kernel())
    .unwrap()
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_static_bases_and_naturals_keep_the_original_generic_interface() {
    let source = "pub enum Tri{A,B,C} pub unitary fn keep[const A:Basis,const n:Nat](q:Q<A>,word:Bits<n>)->(Q<A>,Bits<n>) requires n>=1 {(q,word)}";
    let parsed = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([("main".into(), source.into())]),
    )
    .unwrap();
    let instance = parsed
        .instantiate_runtime_with_types(
            "main::keep",
            BTreeMap::from([("A".into(), parsed.basis_binding("main::Tri").unwrap())]),
            BTreeMap::from([("n".into(), 1)]),
            Default::default(),
        )
        .unwrap();
    let selected = instance.compile_runtime_with_kernel(&kernel()).unwrap();
    let request = selected.program().runtime_result().unwrap();
    assert_eq!(request.static_naturals, vec![("n".into(), 1)]);
    assert_eq!(request.static_bases[0].0, "A");
    assert!(
        matches!(&request.static_bases[0].1[0], Basis::Enum(origin, _)
        if origin.source == source)
    );
    assert_eq!(request.parameters[1], vec![Atom::Finite(Basis::Bits(1))]);
    assert_eq!(request.input_rows, vec![vec![false], vec![true]]);
    assert_eq!(
        kernel()
            .check_program(selected.program())
            .unwrap()
            .program()
            .runtime_result(),
        Some(request)
    );
    assert!(run_closed(selected.program(), SimulationLimits::default()).is_err());
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_unused_static_nominal_actuals_retain_their_source_in_closed_execution() {
    let parsed = ParsedProgram::parse(Edition::E2026, BTreeMap::from([
        ("main".into(), "pub observe fn keep[const Unused:Basis,const n:Nat]()->Bit requires n>=1 {measure_z(init0())}".into()),
        ("types".into(), "pub enum Tri{A,B,C}".into()),
    ])).unwrap();
    let instance = parsed
        .instantiate_runtime_with_types(
            "main::keep",
            BTreeMap::from([("Unused".into(), parsed.basis_binding("types::Tri").unwrap())]),
            BTreeMap::from([("n".into(), 2)]),
            Default::default(),
        )
        .unwrap();
    let selected = instance.compile_runtime_with_kernel(&kernel()).unwrap();
    let request = selected.program().runtime_result().unwrap();
    assert!(
        matches!(&request.static_bases[0].1[0], Basis::Enum(origin, _)
        if origin.module == "types" && origin.source == "pub enum Tri{A,B,C}")
    );
    assert_eq!(request.static_naturals, vec![("n".into(), 2)]);
    assert_eq!(request.public_effect, qleisli::ir::Effect::Observe);
    assert_eq!(
        run_closed(selected.program(), SimulationLimits::default()).unwrap(),
        BTreeMap::from([(vec![false], 1.0)])
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_generic_dependencies_preserve_nominal_owners_and_distinct_formals() {
    let source = "pub enum Tri{A,B,C} pub struct Empty{} pub struct Item{tag:Tri,bit:Bit}
        pub unitary fn relay[const X:Basis,const m:Nat](q:Q<X>,word:Bits<m>)->(Q<X>,Bits<m>) requires m>=1 {(q,word)}
        pub unitary fn keep[const n:Nat,const A:Basis](q:Q<A>,word:Bits<n>)->(Q<A>,Bits<n>) requires n>=1 {relay[A,n](q,word)}";
    let parsed = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([("main".into(), source.into())]),
    )
    .unwrap();
    for name in ["main::Tri", "main::Empty", "main::Item"] {
        let instance = parsed
            .instantiate_runtime_with_types(
                "main::keep",
                BTreeMap::from([("A".into(), parsed.basis_binding(name).unwrap())]),
                BTreeMap::from([("n".into(), 1)]),
                Default::default(),
            )
            .unwrap();
        let selected = instance.compile_runtime_with_kernel(&kernel()).unwrap();
        let request = selected.program().runtime_result().unwrap();
        assert_eq!(request.static_naturals, vec![("n".into(), 1)]);
        assert_eq!(request.static_bases[0].0, "A");
        assert_eq!(request.parameters[1], vec![Atom::Finite(Basis::Bits(1))]);
        assert_eq!(request.input_storage[0][0], request.storage[1]);
        assert_eq!(request.public_effect, qleisli::ir::Effect::Unitary);
        assert_eq!(
            kernel()
                .check_program(selected.program())
                .unwrap()
                .program()
                .runtime_result(),
            Some(request)
        );
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn ordinary_generic_forwarding_does_not_grant_nominal_control() {
    for action in ["controlled(relay[A])(c,q)", "(c,adjoint(relay[A])(q))"] {
        let parsed = ParsedProgram::parse(
            Edition::E2026,
            BTreeMap::from([(
                "main".into(),
                format!(
                    "pub enum Tri{{A,B,C}}
        pub unitary fn relay[const X:Basis](q:Q<X>)->Q<X>{{q}}
        pub unitary fn keep[const A:Basis](c:Q<Bit>,q:Q<A>)->(Q<Bit>,Q<A>){{{action}}}"
                ),
            )]),
        )
        .unwrap();
        let instance = parsed
            .instantiate_runtime_with_types(
                "main::keep",
                BTreeMap::from([("A".into(), parsed.basis_binding("main::Tri").unwrap())]),
                Default::default(),
                Default::default(),
            )
            .unwrap();
        let error = instance.compile_runtime_with_kernel(&kernel()).unwrap_err();
        assert!(error.message.contains("nominal"), "{error:?}");
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn generic_runtime_actuals_keep_original_nominal_names_and_nested_type_arguments() {
    let declarations = "pub enum Tri{A,B,C}
        pub unitary fn relay[const X:Basis](q:Q<X>)->Q<X>{q}";
    for body in [
        "pub unitary fn keep(q:Q<Tri>)->Q<Tri>{relay[type(Tri)](q)}",
        "pub unitary fn keep(q:Q<(Tri,Bits<0>)>)->Q<(Tri,Bits<0>)>{relay[type((Tri,Bits<0>))](q)}",
    ] {
        let source = format!("{declarations}{body}");
        compile_project(&SourceRoot::new(&format!("{source} fn main()->Unit{{()}}")).0).unwrap();
        let checked = selected(&source);
        let request = checked.program().runtime_result().unwrap();
        assert_eq!(request.input_storage[0], request.storage);
        assert_eq!(request.parameters[0], request.result);
        assert_eq!(request.public_effect, qleisli::ir::Effect::Unitary);
    }
    let source = format!("{declarations}
        pub unitary fn keep[const A:Basis,const n:Nat](q:Q<(A,Bits<n>)>)->Q<(A,Bits<n>)>{{relay[type((A,Bits<n>))](q)}}");
    let parsed =
        ParsedProgram::parse(Edition::E2026, BTreeMap::from([("main".into(), source)])).unwrap();
    let instance = parsed
        .instantiate_runtime_with_types(
            "main::keep",
            BTreeMap::from([("A".into(), parsed.basis_binding("main::Tri").unwrap())]),
            BTreeMap::from([("n".into(), 0)]),
            Default::default(),
        )
        .unwrap();
    let checked = instance.compile_runtime_with_kernel(&kernel()).unwrap();
    let request = checked.program().runtime_result().unwrap();
    assert_eq!(request.input_storage[0], request.storage);
    assert_eq!(request.parameters[0], request.result);
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn imported_generic_runtime_call_executes_with_unused_nominal_actuals() {
    let parsed = ParsedProgram::parse(Edition::E2026, BTreeMap::from([
        ("main".into(), "use helper::relay; pub observe fn keep[const A:Basis,const n:Nat]()->Bit requires n>=1 {measure_z(relay[A,n](init0()))}".into()),
        ("helper".into(), "pub unitary fn relay[const Unused:Basis,const m:Nat](q:Q<Bit>)->Q<Bit> requires m>=1 {q}".into()),
        ("types".into(), "pub enum Tri{A,B,C}".into()),
    ])).unwrap();
    let instance = parsed
        .instantiate_runtime_with_types(
            "main::keep",
            BTreeMap::from([("A".into(), parsed.basis_binding("types::Tri").unwrap())]),
            BTreeMap::from([("n".into(), 1)]),
            Default::default(),
        )
        .unwrap();
    let checked = instance.compile_runtime_with_kernel(&kernel()).unwrap();
    assert!(checked.program().runtime_result().is_some());
    assert_eq!(
        run_closed(checked.program(), SimulationLimits::default()).unwrap(),
        BTreeMap::from([(vec![false], 1.0)])
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn ordinary_generic_calls_check_unused_nominal_actuals_and_closed_partial_widths() {
    let source = "pub enum Tri{A,B,C}
        unitary fn relay[const Unused:Basis]()->Unit{()}
        unitary fn main()->Unit{relay[type(Tri)]()}";
    let program = compile_project(&SourceRoot::new(source).0).unwrap();
    assert_eq!(
        run_closed(&program, SimulationLimits::default()).unwrap(),
        BTreeMap::from([(vec![], 1.0)])
    );
    let source = "unitary fn relay[const Unused:Basis](q:Q<Unit>)->Q<Unit>{q}
        unitary fn unused[const A:Basis](q:Q<Unit>)->Q<Unit>{relay[type((A,Bits<13>))](q)}
        pub unitary fn keep()->Unit{()}";
    let parsed = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([("main".into(), source.into())]),
    )
    .unwrap();
    let instance = parsed
        .instantiate_runtime_with_types(
            "main::keep",
            Default::default(),
            Default::default(),
            Default::default(),
        )
        .unwrap();
    let error = instance.compile_runtime_with_kernel(&kernel()).unwrap_err();
    assert!(error.message.contains("12-bit"), "{error:?}");
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn generic_nominal_calls_preserve_the_callees_public_observe_effect() {
    let helper = "pub observe fn opaque[const A:Basis](q:Q<A>)->Q<A>{q}";
    for effect in ["unitary", "isometry", "observe"] {
        let source = format!(
            "use helper::opaque; pub enum Tri{{A,B,C}}
            pub {effect} fn keep[const B:Basis](q:Q<B>)->Q<B>{{opaque[B](q)}}"
        );
        let parsed = ParsedProgram::parse(
            Edition::E2026,
            BTreeMap::from([("main".into(), source), ("helper".into(), helper.into())]),
        );
        if effect != "observe" {
            let error = parsed.unwrap_err();
            assert!(error.message().contains("effect"), "{error:?}");
            continue;
        }
        let parsed = parsed.unwrap();
        let instance = parsed
            .instantiate_runtime_with_types(
                "main::keep",
                BTreeMap::from([("B".into(), parsed.basis_binding("main::Tri").unwrap())]),
                Default::default(),
                Default::default(),
            )
            .unwrap();
        let checked = instance.compile_runtime_with_kernel(&kernel()).unwrap();
        assert_eq!(
            checked.program().runtime_result().unwrap().public_effect,
            qleisli::ir::Effect::Observe
        );
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn source_keeps_mixed_inputs_nominal_quantum_types_and_original_input_order() {
    let source = "pub enum Tri {A,B,C} pub unitary fn keep(flag:Bit,q:Q<Tri>)->(Bit,Q<Tri>){(flag,q)} fn main()->Unit{()}";
    // Project checking also visits the original public helper, with no fake entry.
    compile_project(&SourceRoot::new(source).0).unwrap();
    let selected = selected(source);
    let request = selected.program().runtime_result().unwrap();
    assert_eq!(selected.runtime_parameters(), 2);
    assert_eq!(request.parameters[0], vec![Atom::Finite(Basis::Bit)]);
    assert_eq!(request.parameters[1][0], Atom::Quantum);
    assert!(
        matches!(&request.parameters[1][1], Atom::Finite(Basis::Enum(origin, labels))
        if origin.source == source && origin.module == "main" && labels == &["A","B","C"])
    );
    assert_eq!(request.result[0], Atom::Finite(Basis::Pair));
    assert_eq!(request.input_rows, vec![vec![false], vec![true]]);
    let Storage::Quantum(input) = &request.input_storage[1][0] else {
        panic!("owner")
    };
    let Storage::Quantum(output) = &request.storage[2] else {
        panic!("returned owner")
    };
    assert_eq!(input, output);
    assert!(run_closed(selected.program(), SimulationLimits::default()).is_err());
    assert_eq!(
        kernel()
            .check_program(selected.program())
            .unwrap()
            .program()
            .runtime_result(),
        Some(request)
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn source_keeps_zero_width_quantum_owner_and_ordinary_parameter_distinct() {
    let selected = selected(
        "pub enum One{Only} pub unitary fn keep(empty:Unit,q:Q<One>)->(Q<One>,Unit){(q,empty)}",
    );
    let request = selected.program().runtime_result().unwrap();
    assert_eq!(selected.runtime_parameters(), 2);
    assert_eq!(request.parameters[0], vec![Atom::Finite(Basis::Unit)]);
    assert_eq!(selected.program().raw().quantum_inputs.len(), 1);
    assert_eq!(selected.program().raw().quantum_inputs[0].shape.bits, 0);
    assert!(matches!(request.input_storage[1][0], Storage::Quantum(_)));
    assert!(run_closed(selected.program(), SimulationLimits::default()).is_err());
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn quantum_record_and_nested_runtime_tuples_keep_distinct_shapes() {
    let selected = selected(
        "pub enum Tri{A,B,C} pub struct Packet{pub tag:Tri,pub bit:Bit} pub unitary fn keep(q:Q<Packet>,v:Tri)->((Q<Packet>,Unit),Tri){((q,()),v)}",
    );
    let request = selected.program().runtime_result().unwrap();
    assert!(
        matches!(&request.parameters[0][1], Atom::Finite(Basis::Record(origin, fields))
        if origin.declaration == "Packet" && fields == &["tag","bit"])
    );
    assert_eq!(
        request.input_rows,
        vec![vec![false, false], vec![true, false], vec![false, true]]
    );
    assert_eq!(
        request.result[..3],
        [
            Atom::Finite(Basis::Pair),
            Atom::Finite(Basis::Pair),
            Atom::Quantum
        ]
    );
    assert_eq!(request.storage[..2], [Storage::Tuple(2), Storage::Tuple(2)]);
    let Storage::Quantum(input) = &request.input_storage[0][0] else {
        panic!("record owner")
    };
    let Storage::Quantum(output) = &request.storage[2] else {
        panic!("nested record owner")
    };
    assert_eq!(input, output);
    assert_eq!(input.port.shape.bits, 3);
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn source_hidden_observation_keeps_its_public_effect() {
    let source = "pub enum Tri{A,B,C} pub observe fn keep(q:Q<Tri>)->Q<Tri>{let hidden=measure_z(init0()); q} fn main()->Unit{()}";
    compile_project(&SourceRoot::new(source).0).unwrap();
    let selected = selected(source);
    assert_eq!(
        selected.program().runtime_result().unwrap().public_effect,
        qleisli::ir::Effect::Observe
    );
    assert_eq!(
        selected.program().raw().declared_effect,
        qleisli::ir::Effect::Observe
    );
    for body in ["discard(q)", "let hidden=measure_z(init0()); q"] {
        let result = if body == "discard(q)" {
            "Unit"
        } else {
            "Q<Tri>"
        };
        let dishonest = format!(
            "pub enum Tri{{A,B,C}} pub unitary fn keep(q:Q<Tri>)->{result}{{{body}}} fn main()->Unit{{()}}"
        );
        assert!(compile_project(&SourceRoot::new(&dishonest).0).is_err());
        assert!(
            ParsedProgram::parse(Edition::E2026, BTreeMap::from([("main".into(), dishonest)]))
                .is_err()
        );
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn nominal_quantum_products_split_join_without_erasing_basis_or_axis_order() {
    let selected = selected(
        "pub enum Tri{A,B,C} pub unitary fn keep(q:Q<(Tri,Bit)>)->Q<(Bit,Tri)>{let (a,b)=split(q);join(b,a)}",
    );
    let request = selected.program().runtime_result().unwrap();
    let Storage::Quantum(input) = &request.input_storage[0][0] else {
        panic!("owner")
    };
    let Storage::Quantum(output) = &request.storage[0] else {
        panic!("owner")
    };
    assert_eq!(
        input.port.wires,
        vec![
            qleisli::ir::WireId(0),
            qleisli::ir::WireId(1),
            qleisli::ir::WireId(2)
        ]
    );
    assert_eq!(
        output.port.wires,
        vec![
            qleisli::ir::WireId(2),
            qleisli::ir::WireId(0),
            qleisli::ir::WireId(1)
        ]
    );
    assert!(matches!(input.basis[1], Basis::Enum(..)));
    assert!(matches!(output.basis[2], Basis::Enum(..)));
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_ordinary_result_can_observe_small_quantum_temporaries() {
    let selected = selected(
        "pub enum Tri{A,B,C} pub observe fn keep()->Tri{let b=measure_z(h(init0()));if b{Tri::B}else{Tri::A}}",
    );
    assert!(selected.program().ordinary_result().is_some());
    let actual = run_closed(selected.program(), SimulationLimits::default()).unwrap();
    assert_eq!(actual.len(), 2);
    assert!((actual[&vec![false, false]] - 0.5).abs() < 1e-12);
    assert!((actual[&vec![true, false]] - 0.5).abs() < 1e-12);
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn quantum_nominal_imports_keep_original_declared_code_and_require_native_checking() {
    let leaf = "pub enum Tri{A,B,C}";
    let program = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([
            (
                "main".into(),
                "use facade::Tri; pub unitary fn keep(q:Q<Tri>)->Q<Tri>{global_phase_eighth(q)}"
                    .into(),
            ),
            ("facade".into(), "pub use leaf::Tri;".into()),
            ("leaf".into(), leaf.into()),
        ]),
    )
    .unwrap();
    let instance = program
        .instantiate_runtime_with_types(
            "main::keep",
            Default::default(),
            Default::default(),
            Default::default(),
        )
        .unwrap();
    let checked = instance.compile_runtime_with_kernel(&kernel()).unwrap();
    let request = checked.program().runtime_result().unwrap();
    assert!(
        matches!(&request.parameters[0][1], Atom::Finite(Basis::Enum(origin,_))
        if origin.module == "leaf" && origin.source == leaf)
    );
    assert!(!checked.program().raw().operations.is_empty());
    let missing = Kernel::new("/nonexistent/qleisli-runtime-source-test", Edition::E2026);
    assert!(instance.compile_runtime_with_kernel(&missing).is_err());
    assert!(checked.program().portable_artifact().is_err());
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn runtime_cli_reports_actual_scope_and_refuses_open_execution_and_untyped_export() {
    use std::process::Command;
    let root = SourceRoot::new("pub enum Tri{A,B,C} pub unitary fn keep(q:Q<Tri>)->Q<Tri>{q}");
    let invoke = |action: &str| {
        Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .args([
                action,
                "--entry=main::keep",
                "--ir-profile=raw",
                "--format=json",
            ])
            .arg(format!(
                "--module=main={}",
                root.0.join("main.qli").display()
            ))
            .output()
            .unwrap()
    };
    let checked = invoke("check");
    assert!(
        checked.status.success(),
        "{}",
        String::from_utf8_lossy(&checked.stdout)
    );
    let text = String::from_utf8(checked.stdout).unwrap();
    assert!(text.contains("\"scope\":\"finite-runtime-root-v2\""));
    assert!(text.contains("\"runtime_result_checked\":true"));
    assert!(text.contains("\"ordinary_result_checked\":false"));
    assert!(text.contains("\"source_preservation_verified\":false"));
    let run = invoke("run");
    assert!(!run.status.success());
    assert!(
        String::from_utf8(run.stdout)
            .unwrap()
            .contains("zero runtime parameters")
    );
    let output = root.0.join("unportable.qirf");
    let emitted = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .args([
            "emit-proposal",
            "--entry=main::keep",
            "--ir-profile=raw",
            "--format=json",
        ])
        .arg(format!(
            "--module=main={}",
            root.0.join("main.qli").display()
        ))
        .arg(format!("--output={}", output.display()))
        .output()
        .unwrap();
    assert!(!emitted.status.success());
    assert!(!output.exists());
    assert!(
        String::from_utf8(emitted.stdout)
            .unwrap()
            .contains("complete typed request transport")
    );
}
