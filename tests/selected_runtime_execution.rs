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
    selected_at(source, "main::keep")
}

fn selected_at(source: &str, entry: &str) -> qleisli::frontend::compile::SelectedRuntimeProgram {
    ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([("main".into(), source.into())]),
    )
    .unwrap()
    .instantiate_runtime_with_types(
        entry,
        Default::default(),
        Default::default(),
        Default::default(),
    )
    .unwrap()
    .compile_runtime_with_kernel(&kernel())
    .unwrap_or_else(|error| panic!("{error:?}\nOriginal test source:\n{source}"))
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_qmatch_context_checks_original_phase_parameters_and_aliases() {
    use qleisli::contract::exact::{Budget, Exact, Matrix};
    use qleisli::contract::{BasisType, Circuit};
    for parameters in [
        "let target=phase[1,3](h(target));",
        "static let numerator=1;static let denominator=3;let target=phase[numerator,denominator](h(target));",
    ] {
        let source = format!(
            "#![no_implicit_prelude]\n
            pub enum Selector{{Zero,One}}
            unitary fn idle(q:Q<Bit>)->Q<Bit>{{q}}
            unitary fn marked(q:Q<Bit>)->Q<Bit>{{phase[1,3](q)}}
            pub unitary fn select(selector:Q<Selector>,target:Q<Bit>)->(Q<Selector>,Q<Bit>){{
                {parameters}
                let(selector,target)=qmatch(selector,target){{Selector::Zero=>idle,Selector::One=>marked}};
                (selector,phase[7,3](target))}}"
        );
        let accepted = selected_at(&source, "main::select");
        let raw = accepted.program().raw();
        assert_eq!(raw.operations.len(), 6);
        for (index, exponent) in [(1, 1), (5, 7)] {
            let qleisli::ir::RawOp::ApplyUnitary { steps, .. } = &raw.operations[index] else {
                panic!("original phase must retain its own Raw interval");
            };
            let actual = Circuit::new(BasisType::Bit, steps.clone())
                .unwrap()
                .matrix(&mut Budget::new(10_000))
                .unwrap();
            let expected = Matrix::new(
                2,
                2,
                vec![
                    Exact::one(),
                    Exact::zero(),
                    Exact::zero(),
                    Exact::phase(exponent),
                ],
            )
            .unwrap();
            assert_eq!(actual, expected);
        }
        kernel().check_program(accepted.program()).unwrap();
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_nominal_qmatch_binds_the_actual_complete_call() {
    let source = "pub enum Tri { A, B, C }
        pub unitary fn idle(q:Q<Unit>)->Q<Unit>{q}
        pub unitary fn phase(q:Q<Unit>)->Q<Unit>{global_phase_eighth(q)}
        pub unitary fn keep(s:Q<Tri>,q:Q<Unit>)->(Q<Tri>,Q<Unit>){
            qmatch(s,q){Tri::C=>phase,Tri::A=>idle,Tri::B=>phase}}";
    let selected = selected(source);
    let request = selected.program().runtime_result().unwrap();
    assert!(
        matches!(request.parameters[0].get(1), Some(Atom::Finite(Basis::Enum(_, labels))) if labels == &["A", "B", "C"])
    );
    assert_eq!(request.public_effect, qleisli::ir::Effect::Unitary);
    kernel().check_program(selected.program()).unwrap();
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_qmatch_checks_nominal_basis_rows_and_rejects_padding_leaks() {
    use qleisli::ir::RawOp;

    let source =
        include_str!("fixtures/authoring_sessions/nominal-basis-rows-v030/attempt-01/main.qli");
    let selected = selected(source);
    let program = selected.program();
    assert!(program.qmatch_source_checked());
    assert!(matches!(
        program.raw().operations.first(),
        Some(RawOp::LiftBasis { table, .. }) if table == &[1, 2, 0, 3]
    ));
    let artifact = std::str::from_utf8(program.artifact()).unwrap();
    let original = r#""table":[1,2,0,3],"tag":"lift_basis""#;
    assert_eq!(artifact.matches(original).count(), 1);
    for table in ["[2,0,1,3]", "[1,2,3,0]"] {
        let changed = format!(r#""table":{table},"tag":"lift_basis""#);
        let artifact = artifact.replacen(original, &changed, 1);
        let error = kernel()
            .check_qmatch_source_v5(artifact.as_bytes(), program.request().unwrap())
            .unwrap_err();
        assert_eq!(error.code, "contract", "{error}");
        assert!(
            error.message.contains("Lean native checker rejected"),
            "{error}"
        );
    }

    let standalone = source.replace(
        "qmatch(s, q) { Tri::C => phase, Tri::B => idle, Tri::A => idle }",
        "(s, q)",
    );
    let selected = self::selected(&standalone);
    assert_eq!(
        selected.program().source_body_scope(),
        Some("finite-source-basis-context-v5")
    );
    assert!(!selected.program().qmatch_source_checked());
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn standalone_basis_checks_the_original_nominal_output_and_scope() {
    use qleisli::ir::RawOp;

    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/authoring_sessions/standalone-nominal-basis-v030/attempt-01/output");
    let selected = ParsedProgram::load(BTreeMap::from([("main".into(), root.join("main.qli"))]))
        .unwrap()
        .instantiate_runtime_with_types(
            "main::prepare",
            Default::default(),
            Default::default(),
            Default::default(),
        )
        .unwrap()
        .compile_runtime_with_kernel(&kernel())
        .unwrap();
    let program = selected.program();
    let request = program.request().unwrap();
    assert_eq!(
        program.source_body_scope(),
        Some("finite-source-basis-context-v5")
    );
    assert!(!program.qmatch_source_checked());
    assert!(
        program
            .raw()
            .operations
            .iter()
            .any(|op| matches!(op, RawOp::LiftBasis { table, .. } if table == &[2]))
    );
    kernel().check_program(program).unwrap();

    let artifact = std::str::from_utf8(program.artifact()).unwrap();
    let table = r#""table":[2],"tag":"lift_basis""#;
    assert_eq!(artifact.matches(table).count(), 1);
    let forged = artifact.replacen(table, r#""table":[3],"tag":"lift_basis""#, 1);
    let error = kernel()
        .check_qmatch_source_v5(forged.as_bytes(), request)
        .unwrap_err();
    assert_eq!(error.code, "contract", "{error}");
    assert!(
        error.message.contains("Lean native checker rejected"),
        "{error}"
    );

    let encoded = std::str::from_utf8(request).unwrap();
    let wrong_scope = encoded.replace(
        "finite-source-basis-context-v5",
        "finite-source-qmatch-context-v5",
    );
    let error = kernel()
        .check_qmatch_source_v5(program.artifact(), wrong_scope.as_bytes())
        .unwrap_err();
    assert_eq!(error.code, "format", "{error}");
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn protected_nominal_predicate_checks_the_original_body_and_literal_table() {
    use qleisli::ir::RawOp;
    let source = "#![no_implicit_prelude]
        pub enum Tri { A, B, C }
        classical fn is_b(tag:Tri)->Bit{match tag{Tri::A=>0,Tri::B=>1,Tri::C=>0}}
        unitary fn mark(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}
        pub unitary fn keep(q:Q<Tri>, spectator:Q<Unit>)->(Q<Tri>,Q<Unit>){
            (with_computed(q,is_b){|flag|mark(flag)},spectator)}";
    let selected = selected(source);
    let program = selected.program();
    assert_eq!(
        program.source_body_scope(),
        Some("finite-source-basis-context-v5")
    );
    assert!(matches!(
        program.raw().operations.as_slice(),
        [RawOp::ComputeUseUncompute { function, targets, ancilla_wires, .. }]
            if function == &[0, 1, 0, 0] && targets.is_empty() && ancilla_wires.len() == 1
    ));
    kernel().check_program(program).unwrap();
    let artifact = std::str::from_utf8(program.artifact()).unwrap();
    let request = program.request().unwrap();
    for (original, forged) in [
        (r#""function":[0,1,0,0]"#, r#""function":[0,0,1,0]"#),
        (r#""function":[0,1,0,0]"#, r#""function":[0,1,0,1]"#),
        ("Tri::B=>1", "Tri::B=>0"),
        ("phase[1,1](q)", "phase[1,2](q)"),
    ] {
        assert_eq!(artifact.matches(original).count(), 1, "{original}");
        let changed = artifact.replacen(original, forged, 1);
        let error = kernel()
            .check_qmatch_source_v5(changed.as_bytes(), request)
            .unwrap_err();
        assert_eq!(error.code, "contract", "{error}");
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn nominal_predicate_leaves_padding_between_product_rows() {
    use qleisli::ir::RawOp;
    let source = "#![no_implicit_prelude]
        pub enum Tri { A, B, C }
        classical fn choose((tag,b):(Tri,Bit))->Bit{match tag{Tri::A=>b,Tri::B=>1,Tri::C=>0}}
        pub unitary fn keep(q:Q<(Tri,Bit)>)->Q<(Tri,Bit)>{
            with_computed(q,choose){|flag|phase[1,1](flag)}}";
    let selected = selected(source);
    assert!(matches!(
        selected.program().raw().operations.as_slice(),
        [RawOp::ComputeUseUncompute { function, .. }]
            if function == &[0, 1, 0, 0, 1, 1, 0, 0]
    ));
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn project_checks_a_nominal_predicate_with_its_original_callee() {
    let source = "#![no_implicit_prelude]
        pub enum Tri { A, B, C }
        classical fn is_b(tag:Tri)->Bit{match tag{Tri::A=>0,Tri::B=>1,Tri::C=>0}}
        unitary fn mark(q:Q<Tri>)->Q<Tri>{with_computed(q,is_b){|flag|phase[1,1](flag)}}
        observe fn main()->Unit{discard(mark(basis unit(()) as _{Tri::B}))}";
    let program = compile_project(&SourceRoot::new(source).0).unwrap();
    assert_eq!(
        program.source_body_scope(),
        Some("finite-source-basis-context-v5")
    );
    assert_eq!(
        run_closed(&program, SimulationLimits::default()).unwrap(),
        BTreeMap::from([(vec![], 1.0)])
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn certified_nominal_predicate_binds_both_original_actions() {
    use qleisli::ir::RawOp;
    let source = "#![no_implicit_prelude]
        pub enum Tri { A, B, C }
        classical fn is_b(tag:Tri)->Bit{match tag{Tri::A=>0,Tri::B=>1,Tri::C=>0}}
        unitary fn logical(q:Q<Tri>)->Q<Tri>{global_phase_eighth(q)}
        pub unitary fn keep(q:Q<Tri>)->Q<Tri>{
            with_computed(q,is_b,logical){|data,flag|(global_phase_eighth(data),flag)}}";
    let selected = selected(source);
    let program = selected.program();
    assert_eq!(
        program.source_body_scope(),
        Some("finite-source-basis-context-v5")
    );
    assert!(matches!(
        program.raw().operations.as_slice(),
        [RawOp::CertifiedCompute { function, use_steps, logical_steps, .. }]
            if function == &[0, 1, 0, 0] && use_steps == logical_steps
    ));
    kernel().check_program(program).unwrap();
    let artifact = std::str::from_utf8(program.artifact()).unwrap();
    let request = program.request().unwrap();
    let phases = r#""phases":[1]"#;
    assert_eq!(artifact.matches(phases).count(), 2);
    let forged = artifact.replace(phases, r#""phases":[2]"#);
    assert_eq!(
        kernel()
            .check_qmatch_source_v5(forged.as_bytes(), request)
            .unwrap_err()
            .code,
        "contract"
    );

    let closed =
        format!("{source} fn main()->Unit{{discard(keep(basis unit(()) as _{{Tri::B}}))}}");
    let project = compile_project(&SourceRoot::new(&closed).0).unwrap();
    assert_eq!(
        project.source_body_scope(),
        Some("finite-source-basis-context-v5")
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_arm_compares_the_original_nominal_meaning_to_the_applied_operator() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/authoring_sessions/nominal-meaning-arm-v030/attempt-01/main.qli");
    let source = ParsedProgram::load(BTreeMap::from([("main".into(), path)])).unwrap();
    let finite = source.finite_meaning_target("main::Flip").unwrap();
    assert_eq!(finite.permutation_table(), [1, 0]);
    let selected = source
        .instantiate_runtime_with_types(
            "main::select",
            Default::default(),
            Default::default(),
            Default::default(),
        )
        .unwrap()
        .compile_runtime_with_kernel(&kernel())
        .unwrap();
    let program = selected.program();
    assert!(program.qmatch_source_checked());
    kernel().check_program(program).unwrap();

    let artifact = std::str::from_utf8(program.artifact()).unwrap();
    let original = "Flag::Flip => not bit";
    assert_eq!(artifact.matches(original).count(), 1);
    let stale = artifact.replacen(original, "Flag::Flip => bit", 1);
    let error = kernel()
        .check_qmatch_source_v5(stale.as_bytes(), program.request().unwrap())
        .unwrap_err();
    assert_eq!(error.code, "contract", "{error}");
    assert!(
        error.message.contains("Lean native checker rejected"),
        "{error}"
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn standalone_nominal_meaning_checks_the_actual_call_interval_and_scope() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join(
            "tests/fixtures/authoring_sessions/standalone-nominal-meaning-v030/attempt-01/selected",
        )
        .join("main.qli");
    let source = ParsedProgram::load(BTreeMap::from([("main".into(), path)])).unwrap();
    let selected = source
        .instantiate_runtime_with_types(
            "main::undo",
            Default::default(),
            Default::default(),
            Default::default(),
        )
        .unwrap()
        .compile_runtime_with_kernel(&kernel())
        .unwrap();
    let program = selected.program();
    assert_eq!(
        program.source_body_scope(),
        Some("finite-source-meaning-context-v5")
    );
    assert!(!program.qmatch_source_checked());
    kernel().check_program(program).unwrap();

    let request = program.request().unwrap();
    let artifact = std::str::from_utf8(program.artifact()).unwrap();
    for (before, after) in [
        ("Label::Mark => b", "Label::Mark => 0"),
        (r#""adjoint":true"#, r#""adjoint":false"#),
    ] {
        assert_eq!(artifact.matches(before).count(), 1);
        let stale = artifact.replacen(before, after, 1);
        let error = kernel()
            .check_qmatch_source_v5(stale.as_bytes(), request)
            .unwrap_err();
        assert_eq!(error.code, "contract", "{error}");
        assert!(
            error.message.contains("Lean native checker rejected"),
            "{error}"
        );
    }

    let wrong_scope = std::str::from_utf8(request).unwrap().replace(
        "finite-source-meaning-context-v5",
        "finite-source-basis-context-v5",
    );
    let error = kernel()
        .check_qmatch_source_v5(program.artifact(), wrong_scope.as_bytes())
        .unwrap_err();
    assert_eq!(error.code, "format", "{error}");
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn rectangular_nominal_meaning_checks_the_written_supplier_and_return_code() {
    let source = r#"#![no_implicit_prelude]
        pub enum Mode { A, B, C }
        isometry fn specification(q: Q<Unit>) -> Q<Mode> { basis q as _ { Mode::B } }
        isometry fn implementation(q: Q<Unit>) -> Q<Mode> { basis q as _ { Mode::B } }
        meaning Prepare: Unit -> Mode = reference(specification);
        isometry fn invoke[const U: Op<Unit -> Mode>](q: Q<Unit>) -> Q<Mode>
            requires Applicable(U) { U(q) }
        pub isometry fn prepare(q: Q<Unit>) -> Q<Mode> {
            invoke[checked_op(implementation, Prepare)](q)
        }"#;
    let selected = selected_at(source, "main::prepare");
    let program = selected.program();
    assert_eq!(
        program.source_body_scope(),
        Some("finite-source-meaning-context-v5")
    );
    let artifact = std::str::from_utf8(program.artifact()).unwrap();
    assert!(artifact.contains(r#""root":0"#));
    let programs = artifact.find(r#""programs":[{"#).unwrap();
    let first_table = r#""table":[1]"#;
    let offset = programs + artifact[programs..].find(first_table).unwrap();
    for code in [0, 3] {
        let mut mutated = artifact.to_owned();
        mutated.replace_range(
            offset..offset + first_table.len(),
            &format!(r#""table":[{code}]"#),
        );
        let error = kernel()
            .check_qmatch_source_v5(mutated.as_bytes(), program.request().unwrap())
            .unwrap_err();
        assert_eq!(error.code, "contract", "{error}");
    }

    let unused = source.replace("{ U(q) }", "{ basis q as _ { Mode::A } }");
    let selected = selected_at(&unused, "main::prepare");
    assert_eq!(
        selected.program().source_body_scope(),
        Some("finite-source-meaning-context-v5")
    );
    let mismatched = unused.replace(
        "implementation(q: Q<Unit>) -> Q<Mode> { basis q as _ { Mode::B } }",
        "implementation(q: Q<Unit>) -> Q<Mode> { basis q as _ { Mode::C } }",
    );
    assert_ne!(unused, mismatched);
    let parsed = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([("main".into(), mismatched)]),
    )
    .unwrap();
    let error = parsed
        .instantiate_runtime_with_types(
            "main::prepare",
            Default::default(),
            Default::default(),
            Default::default(),
        )
        .unwrap()
        .compile_runtime_with_kernel(&kernel())
        .unwrap_err();
    assert_eq!(error.code, "contract", "{error:?}");
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn declared_rectangular_nominal_meaning_checks_used_and_unused_supplies() {
    let source = "#![no_implicit_prelude]
pub enum M{A,B,C}
isometry fn r(q:Q<Unit>)->Q<M>{basis q as _{M::B}}
isometry fn a(q:Q<Unit>)->Q<M>{basis q as _{M::B}}
meaning P:Unit->M=reference(r);
isometry fn f[const U:Op<Unit->M,P>](q:Q<Unit>)->Q<M> requires Applicable(U){U(q)}
pub isometry fn g(q:Q<Unit>)->Q<M>{f[a](q)}";
    let unused = source.replace("{U(q)}", "{basis q as _{M::A}}");
    let written = source.replace("f[a]", "f[checked_op(a,P)]");
    for original in [source, unused.as_str(), written.as_str()] {
        let selected = selected_at(original, "main::g");
        assert_eq!(
            selected.program().source_body_scope(),
            Some("finite-source-meaning-context-v5")
        );
    }
    let closed = source.replace(
        "pub isometry fn g(q:Q<Unit>)->Q<M>{f[a](q)}",
        "pub observe fn main()->Unit{discard(f[a](unit(())));()}",
    );
    let project = SourceRoot::new(&closed);
    let checked = compile_project(&project.0).unwrap();
    assert_eq!(
        checked.source_body_scope(),
        Some("finite-source-meaning-context-v5")
    );

    let wrong = unused.replace(
        "fn a(q:Q<Unit>)->Q<M>{basis q as _{M::B}}",
        "fn a(q:Q<Unit>)->Q<M>{basis q as _{M::C}}",
    );
    assert_ne!(unused, wrong);
    let parsed =
        ParsedProgram::parse(Edition::E2026, BTreeMap::from([("main".into(), wrong)])).unwrap();
    let error = parsed
        .instantiate_runtime_with_types(
            "main::g",
            Default::default(),
            Default::default(),
            Default::default(),
        )
        .unwrap()
        .compile_runtime_with_kernel(&kernel())
        .unwrap_err();
    assert_eq!(error.code, "contract", "{error:?}");
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn nominal_meaning_checks_the_original_cycle_and_inverse_on_three_labels() {
    let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/authoring_sessions/nominal-meaning-ports-v030/attempt-01/selected");
    let selected = ParsedProgram::load(BTreeMap::from([(
        "main".into(),
        directory.join("main.qli"),
    )]))
    .unwrap()
    .instantiate_runtime_with_types(
        "main::undo",
        Default::default(),
        Default::default(),
        Default::default(),
    )
    .unwrap()
    .compile_runtime_with_kernel(&kernel())
    .unwrap();
    let program = selected.program();
    let request = program.request().unwrap();
    assert_eq!(
        program.source_body_scope(),
        Some("finite-source-meaning-context-v5")
    );
    kernel().check_program(program).unwrap();
    let artifact = std::str::from_utf8(program.artifact()).unwrap();
    let inverse = r#""permutation":[2,0,1,3]"#;
    let phases = r#""phases":[0,0,0,0]"#;
    for (before, after) in [
        (inverse, r#""permutation":[1,2,0,3]"#),
        (inverse, r#""permutation":[3,0,1,2]"#),
        (phases, r#""phases":[0,4,0,0]"#),
    ] {
        assert_eq!(artifact.matches(before).count(), 1);
        let forged = artifact.replacen(before, after, 1);
        let error = kernel()
            .check_qmatch_source_v5(forged.as_bytes(), request)
            .unwrap_err();
        assert_eq!(error.code, "contract", "{error}");
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn project_executes_the_checked_nominal_meaning_interval() {
    let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/authoring_sessions/nominal-meaning-ports-v030/attempt-01/project");
    let program = compile_project(&directory).unwrap();
    assert_eq!(
        program.source_body_scope(),
        Some("finite-source-meaning-context-v5")
    );
    assert_eq!(
        run_closed(&program, SimulationLimits::default()).unwrap(),
        BTreeMap::from([(vec![], 1.0)])
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn composed_meaning_keeps_the_nominal_intermediate_reference() {
    let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(
        "tests/fixtures/authoring_sessions/nominal-meaning-composition-v030/attempt-03/selected",
    );
    let source = ParsedProgram::load(BTreeMap::from([(
        "main".into(),
        directory.join("main.qli"),
    )]))
    .unwrap();
    let old_target = source.finite_meaning_target("main::Flip").unwrap_err();
    assert!(
        old_target
            .message()
            .contains("original typed runtime transport"),
        "{old_target}"
    );
    let selected = source
        .instantiate_runtime_with_types(
            "main::undo",
            Default::default(),
            Default::default(),
            Default::default(),
        )
        .unwrap()
        .compile_runtime_with_kernel(&kernel())
        .unwrap();
    let program = selected.program();
    assert_eq!(
        program.source_body_scope(),
        Some("finite-source-meaning-context-v5")
    );
    let artifact = std::str::from_utf8(program.artifact()).unwrap();
    let applied = r#""permutation":[1,0]"#;
    assert_eq!(artifact.matches(applied).count(), 1);
    let forged = artifact.replacen(applied, r#""permutation":[0,1]"#, 1);
    let error = kernel()
        .check_qmatch_source_v5(forged.as_bytes(), program.request().unwrap())
        .unwrap_err();
    assert_eq!(error.code, "contract", "{error}");

    let project = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(
        "tests/fixtures/authoring_sessions/nominal-meaning-composition-v030/attempt-03/project",
    );
    let program = compile_project(&project).unwrap();
    assert_eq!(
        program.source_body_scope(),
        Some("finite-source-meaning-context-v5")
    );
    assert_eq!(
        run_closed(&program, SimulationLimits::default()).unwrap(),
        BTreeMap::from([(vec![true], 1.0)])
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn tensor_meaning_checks_the_phase_on_the_original_nominal_product_axis() {
    let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(
        "tests/fixtures/authoring_sessions/nominal-meaning-composition-v030/attempt-03/tensor",
    );
    let selected = ParsedProgram::load(BTreeMap::from([(
        "main".into(),
        directory.join("main.qli"),
    )]))
    .unwrap()
    .instantiate_runtime_with_types(
        "main::undo",
        Default::default(),
        Default::default(),
        Default::default(),
    )
    .unwrap()
    .compile_runtime_with_kernel(&kernel())
    .unwrap();
    let program = selected.program();
    assert_eq!(
        program.source_body_scope(),
        Some("finite-source-meaning-context-v5")
    );
    let artifact = std::str::from_utf8(program.artifact()).unwrap();
    let axis = r#""indices":[2]"#;
    assert!(artifact.contains(axis));
    let forged = artifact.replacen(axis, r#""indices":[0]"#, 1);
    let error = kernel()
        .check_qmatch_source_v5(forged.as_bytes(), program.request().unwrap())
        .unwrap_err();
    assert_eq!(error.code, "contract", "{error}");
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_nominal_basis_lift_uses_logical_dimensions() {
    use qleisli::ir::{Effect, RawOp};

    let source = r#"#![no_implicit_prelude]
pub enum Tri { A, B, C }
unitary fn idle(q: Q<Bit>) -> Q<Bit> { q }
pub isometry fn keep(s: Q<Unit>, q: Q<Bit>, r: Q<Tri>) -> (Q<Unit>, Q<Bit>, Q<(Bit, Bit)>) {
    let r = basis r as tag { match tag { Tri::B => (1,0), Tri::A => (0,0), Tri::C => (0,1) } };
    let (s,q) = qmatch(s,q) { 0 => idle };
    (s,q,r)
}
"#;
    let accepted = selected(source);
    let program = accepted.program();
    assert!(program.qmatch_source_checked());
    assert_eq!(
        program.runtime_result().unwrap().public_effect,
        Effect::Isometry
    );
    assert!(matches!(
        program.raw().operations.first(),
        Some(RawOp::LiftBasis { table, .. }) if table == &[0, 1, 2, 3]
    ));
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_qmatch_binds_nominal_sources_used_only_in_the_body() {
    let entry = include_str!(
        "fixtures/authoring_sessions/nominal-body-provenance-v030/attempt-01/main.qli"
    );
    let labels = include_str!(
        "fixtures/authoring_sessions/nominal-body-provenance-v030/attempt-01/labels.qli"
    );
    let selected = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([
            ("main".into(), entry.into()),
            ("labels".into(), labels.into()),
        ]),
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
    .unwrap();
    let program = selected.program();
    kernel().check_program(program).unwrap();

    // The physical circuit and all public port types remain unchanged. The
    // original body may no longer construct or project this private field.
    let artifact = std::str::from_utf8(program.artifact()).unwrap();
    assert_eq!(artifact.matches("pub bit: Bit").count(), 1);
    let private = artifact.replacen("pub bit: Bit", "bit: Bit", 1);
    let error = kernel()
        .check_qmatch_source_v5(private.as_bytes(), program.request().unwrap())
        .unwrap_err();
    assert!(
        error.message.contains("Lean native checker rejected"),
        "{error}"
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_mixed_runtime_binds_foreign_nominal_body_dependencies() {
    let main = "#![no_implicit_prelude] use labels::Packet;
        pub unitary fn keep(q:Q<Bit>)->(Q<Bit>,Bit){
            let packet=Packet{bit:1}; (q,packet.bit)
        }";
    let labels = "pub struct Packet{pub bit:Bit}";
    let selected = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([
            ("main".into(), main.into()),
            ("labels".into(), labels.into()),
        ]),
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
    .unwrap();
    let program = selected.program();
    assert!(program.runtime_result().is_some());
    assert!(!program.qmatch_source_checked());
    kernel().check_program(program).unwrap();

    let artifact = std::str::from_utf8(program.artifact()).unwrap();
    assert_eq!(artifact.matches("pub bit:Bit").count(), 1);
    let private = artifact.replacen("pub bit:Bit", "bit:Bit", 1);
    let error = kernel()
        .check_runtime_root(private.as_bytes(), program.request().unwrap())
        .unwrap_err();
    assert!(
        error.message.contains("Lean native checker rejected"),
        "{error}"
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_nominal_qmatch_checks_every_original_selection_in_order() {
    // The unchanged first authoring attempt: repeated H/Z sectors cancel as a
    // whole, so checking only the final identity would miss incorrect intervals.
    let source = "pub enum Tag { A, B, C, D }\nunitary fn idle(q: Q<Bit>) -> Q<Bit> { q }\nunitary fn turn(q: Q<Bit>) -> Q<Bit> { h(q) }\nunitary fn sign(q: Q<Bit>) -> Q<Bit> { phase[1,1](q) }\npub unitary fn route(s:Q<Tag>, q:Q<Bit>) -> (Q<Tag>,Q<Bit>) { let (s,q)=qmatch(s,q) { Tag::D=>sign, Tag::B=>turn, Tag::A=>idle, Tag::C=>sign }; qmatch(s,q) { Tag::D=>sign, Tag::B=>turn, Tag::A=>idle, Tag::C=>sign } }\n";
    let parsed = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([("main".into(), source.into())]),
    )
    .unwrap();
    let instance = parsed
        .instantiate_runtime_with_types(
            "main::route",
            Default::default(),
            Default::default(),
            Default::default(),
        )
        .unwrap();
    let accepted = instance.compile_runtime_with_kernel(&kernel()).unwrap();
    let raw = accepted.program().raw();
    assert_eq!(raw.operations.len(), 6);
    assert_eq!(raw.quantum_inputs.len(), 2);
    assert_eq!(raw.quantum_outputs.len(), 2);
    kernel().check_program(accepted.program()).unwrap();

    for effect in ["unitary", "isometry", "observe"] {
        let source = format!(
            "pub enum Tag{{A,B}}
            unitary fn idle(q:Q<Bit>)->Q<Bit>{{q}}
            unitary fn sign(q:Q<Bit>)->Q<Bit>{{phase[1,1](q)}}
            pub {effect} fn keep(q:Q<Bit>,u:Q<Unit>,s:Q<Tag>)->(Q<Unit>,Q<Tag>,Q<Bit>){{
                let pair=(s,q); let (s,q)=pair;
                let (s,q)=qmatch(s,q){{Tag::B=>sign,Tag::A=>idle}};
                let next=qmatch(s,q){{Tag::A=>idle,Tag::B=>sign}};
                let (s,q)=next; (u,s,q)}}"
        );
        let accepted = selected(&source);
        let raw = accepted.program().raw();
        assert_eq!(raw.operations.len(), 6);
        assert_eq!(raw.quantum_outputs[0], raw.quantum_inputs[1].token);
        assert!(raw.quantum_inputs[1].wires.is_empty());
        kernel().check_program(accepted.program()).unwrap();
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_nominal_qmatch_retains_branch_phis_after_input_or_measurement() {
    use qleisli::ir::{Effect, RawOp};

    let source = r#"pub enum Tag { A, B }
unitary fn keep(q: Q<Bit>) -> Q<Bit> { q }
unitary fn turn(q: Q<Bit>) -> Q<Bit> { h(phase[1,3](h(q))) }
unitary fn choose(s: Q<Tag>, q: Q<Bit>) -> (Q<Tag>, Q<Bit>) {
    qmatch(s,q) { Tag::B => turn, Tag::A => keep }
}
pub unitary fn route(s: Q<Tag>, q: Q<Bit>, b: Bit) -> (Q<Tag>, Q<Bit>, Bit) {
    let (s,q,c) = if b {
        let (s,q) = choose(s,q);
        (s,q,1)
    } else {
        (s,q,0)
    };
    (s,q,c)
}
"#;
    let observed = source
        .replace("pub unitary fn route", "pub observe fn route")
        .replace("b: Bit)", "a: Q<Bit>)")
        .replace(
            "    let (s,q,c) = if b",
            "    let b = measure_z(a);\n    let (s,q,c) = if b",
        );
    let prepared = observed
        .replace(", a: Q<Bit>", "")
        .replace("measure_z(a)", "measure_z(h(init0()))");
    let explicit_basis = prepared.replace(
        "    let b = measure_z(h(init0()));",
        "    let a = basis unit(()) as _ { 0 };\n    let b = measure_z(h(a));",
    );
    for (source, expected_effect) in [
        (source, Effect::Unitary),
        (&observed, Effect::Observe),
        (&prepared, Effect::Observe),
        (&explicit_basis, Effect::Observe),
    ] {
        let accepted = selected_at(source, "main::route");
        assert!(accepted.program().qmatch_source_checked());
        let raw = accepted.program().raw();
        assert_eq!(raw.declared_effect, expected_effect);
        let Some(RawOp::ClassicalBranch {
            quantum_phis,
            classical_phis,
            ..
        }) = raw
            .operations
            .iter()
            .find(|op| matches!(op, RawOp::ClassicalBranch { .. }))
        else {
            panic!("the original ordinary branch must be retained");
        };
        assert_eq!(
            raw.quantum_outputs,
            quantum_phis
                .iter()
                .map(|phi| phi.output)
                .collect::<Vec<_>>()
        );
        assert_eq!(classical_phis.len(), 1);
        assert_eq!(raw.classical_outputs, [classical_phis[0].output]);
        kernel().check_program(accepted.program()).unwrap();
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_qmatch_retains_extra_zero_width_owners_and_original_result_order() {
    for reverse in [false, true] {
        for (effect, expected) in [
            ("unitary", qleisli::ir::Effect::Unitary),
            ("isometry", qleisli::ir::Effect::Isometry),
            ("observe", qleisli::ir::Effect::Observe),
        ] {
            let (params, result, value) = if reverse {
                (
                    "q:Q<Unit>,s:Q<Tri>,z:Q<Unit>",
                    "(Q<Unit>,Q<Tri>,Q<Unit>)",
                    "(q,s,z)",
                )
            } else {
                (
                    "s:Q<Tri>,q:Q<Unit>,z:Q<Unit>",
                    "(Q<Tri>,Q<Unit>,Q<Unit>)",
                    "(s,q,z)",
                )
            };
            let source = format!(
                "pub enum Tri{{A,B,C}}
                pub unitary fn idle(q:Q<Unit>)->Q<Unit>{{q}}
                pub unitary fn phase(q:Q<Unit>)->Q<Unit>{{global_phase_eighth(q)}}
                pub {effect} fn keep({params})->{result}{{
                    let(s,q)=qmatch(s,q){{Tri::A=>idle,Tri::B=>phase,Tri::C=>idle}};
                    {value}}}"
            );
            let accepted = selected(&source);
            let raw = accepted.program().raw();
            assert_eq!(raw.quantum_inputs.len(), 3);
            assert_eq!(raw.quantum_outputs.len(), 3);
            let last = raw.quantum_inputs[2].token;
            assert!(raw.quantum_inputs[2].wires.is_empty());
            assert_eq!(raw.quantum_outputs[2], last);
            assert_eq!(
                accepted.program().runtime_result().unwrap().public_effect,
                expected
            );
            kernel().check_program(accepted.program()).unwrap();
        }
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_qmatch_checks_wide_interfaces_in_separate_sectors() {
    let variants = (0..16)
        .map(|ordinal| format!("L{ordinal}"))
        .collect::<Vec<_>>()
        .join(", ");
    for (selector, declaration) in [
        ("Bits<4>", String::new()),
        ("Selector", format!("pub enum Selector {{ {variants} }}")),
    ] {
        let arms = (0..16)
            .rev()
            .map(|ordinal| {
                let label = if selector == "Selector" {
                    format!("Selector::L{ordinal}")
                } else {
                    ordinal.to_string()
                };
                format!("{label} => global_phase_eighth")
            })
            .collect::<Vec<_>>()
            .join(", ");
        let source = format!(
            "#![no_implicit_prelude]
            {declaration}
            pub unitary fn route(s: Q<{selector}>, q: Q<Bits<3>>) -> (Q<{selector}>, Q<Bits<3>>) {{
                qmatch(s, q) {{ {arms} }}
            }}"
        );
        let selected = selected_at(&source, "main::route");
        let program = selected.program();
        assert!(program.qmatch_source_checked());
        let widths = program
            .raw()
            .quantum_inputs
            .iter()
            .map(|port| port.shape.bits)
            .collect::<Vec<_>>();
        assert_eq!(widths, [4, 3]);
        kernel().check_program(program).unwrap();
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_qif_and_qmatch_retain_their_original_selection_order() {
    let source = r#"#![no_implicit_prelude]
pub enum Selector { A, B }
unitary fn mark(q: Q<Bit>) -> Q<Bit> { phase[1,3](q) }
pub unitary fn route(s: Q<Selector>, c: Q<Bit>, q: Q<Bit>) -> (Q<Selector>,Q<Bit>,Q<Bit>) {
    let (c,q) = qif(c,q) { 0 => h, 1 => mark };
    let (s,q) = qmatch(s,q) { Selector::B => h, Selector::A => mark };
    (s,c,q)
}
"#;
    let selected = selected_at(source, "main::route");
    let program = selected.program();
    assert!(program.qmatch_source_checked());
    let mut request =
        qleisli::interchange::qmatch::v5::Request::decode(program.request().unwrap()).unwrap();
    let [qif, qmatch] = request.context.sites.as_slice() else {
        panic!("both original selection sites must be retained");
    };
    assert_eq!(
        qif.position.offset as usize,
        source.find("qif(c,q)").unwrap()
    );
    assert_eq!(
        qmatch.position.offset as usize,
        source.find("qmatch(s,q)").unwrap()
    );
    assert!(qif.position.start + qif.position.count <= qmatch.position.start);
    kernel().check_program(program).unwrap();

    request.context.sites[0].arms.swap(0, 1);
    let error = kernel()
        .check_qmatch_source_v5(program.artifact(), &request.encode().unwrap())
        .unwrap_err();
    assert_eq!(error.code, "contract", "{error}");
    assert!(
        error.message.contains("Lean native checker rejected"),
        "{error}"
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_qmatch_keeps_controlled_permutations_after_evidence_preparation() {
    let source = "unitary fn flip(q:Q<Bit>)->Q<Bit>{h(phase[1,1](h(q)))}
        unitary fn idle(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{q}
        unitary fn exchange(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{let(a,b)=split(q);join(b,a)}
        unitary fn increment(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{
            let(a,b)=split(q);let(a,b)=controlled(flip)(a,b);let a=flip(a);join(a,b)}
        unitary fn decrement(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{
            let(a,b)=split(q);let a=flip(a);let(a,b)=controlled(flip)(a,b);join(a,b)}
        pub unitary fn route(s:Q<Bits<2>>,q:Q<(Bit,Bit)>)->(Q<Bits<2>>,Q<(Bit,Bit)>){
            qmatch(s,q){3=>decrement,0=>idle,2=>increment,1=>exchange}}";
    let parsed = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([("main".into(), source.into())]),
    )
    .unwrap();
    let instance = parsed
        .instantiate_runtime_with_types(
            "main::route",
            Default::default(),
            Default::default(),
            Default::default(),
        )
        .unwrap();
    let accepted = instance.compile_runtime_with_kernel(&kernel()).unwrap();
    assert_eq!(accepted.program().raw().quantum_inputs.len(), 2);
    assert_eq!(accepted.program().raw().quantum_outputs.len(), 2);
    kernel().check_program(accepted.program()).unwrap();
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_qmatch_applies_distinct_phased_arms_on_reversed_noncontiguous_axes() {
    use qleisli::contract::exact::{Budget, Exact};
    use qleisli::contract::{BasisType, Circuit};
    use qleisli::ir::{RawOp, WireId};

    let source = "#![no_implicit_prelude]
        unitary fn zero_arm(q:Q<Bit>)->Q<Bit>{phase[3,2](q)}
        unitary fn one_arm(q:Q<Bit>)->Q<Bit>{h(phase[1,1](h(phase[1,2](q))))}
        pub unitary fn route(t:Q<Bit>,r:Q<Bit>,u:Q<Unit>,s:Q<Bit>)->(Q<Bit>,Q<Bit>,Q<Unit>,Q<Bit>){
            let(s,t)=qmatch(s,t){0=>zero_arm,1=>one_arm}; (t,r,u,s)}";
    let accepted = selected_at(source, "main::route");
    let raw = accepted.program().raw();
    let [target, spectator, unit, selector] = raw.quantum_inputs.as_slice() else {
        panic!("original input owners");
    };
    assert_eq!(target.wires, [WireId(0)]);
    assert_eq!(spectator.wires, [WireId(1)]);
    assert!(unit.wires.is_empty());
    assert_eq!(selector.wires, [WireId(2)]);
    let [
        RawOp::Join {
            left,
            right,
            output: joined,
        },
        RawOp::ApplyUnitary {
            input,
            output,
            steps,
        },
        RawOp::Split {
            input: split,
            left: s,
            right: t,
            left_bits: 1,
        },
    ] = raw.operations.as_slice()
    else {
        panic!("expected the original selection interval");
    };
    assert_eq!(
        (*left, *right, input, output),
        (selector.token, target.token, joined, split)
    );
    assert_eq!(raw.quantum_outputs, [*t, spectator.token, unit.token, *s]);
    let local = Circuit::new(BasisType::Bits(2), steps.clone())
        .unwrap()
        .matrix(&mut Budget::new(100_000))
        .unwrap();
    let packed = |n: usize| (n >> 2) + 2 * (n & 1);
    for col in 0..8 {
        let (dest, phase) = if col < 4 {
            (col, 6 * (col & 1))
        } else {
            (col ^ 1, 2 * (col & 1))
        };
        for row in 0..8 {
            let actual = if (row ^ col) & 2 == 0 {
                local.get(packed(row), packed(col)).unwrap()
            } else {
                Exact::zero()
            };
            let expected = if row == dest {
                Exact::phase(phase as i32)
            } else {
                Exact::zero()
            };
            assert_eq!(actual, expected, "column {col}, row {row}");
        }
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_qmatch_binds_three_phased_arms_and_keeps_padding_dark() {
    use qleisli::contract::exact::{Budget, Exact};
    use qleisli::contract::{BasisType, Circuit};
    use qleisli::ir::RawOp;

    let source = r#"#![no_implicit_prelude]
pub enum Tri { First, Middle, Last }
unitary fn idle(q:Q<Bit>)->Q<Bit>{q}
unitary fn turn(q:Q<Bit>)->Q<Bit>{phase[3,2](q)}
unitary fn flip(q:Q<Bit>)->Q<Bit>{h(phase[1,1](h(q)))}
pub unitary fn keep(s:Q<Tri>,q:Q<Bit>)->(Q<Tri>,Q<Bit>){
    qmatch(s,q){Tri::Last=>flip,Tri::First=>idle,Tri::Middle=>turn}}
"#;
    let accepted = selected(source);
    let raw = accepted.program().raw();
    let [
        RawOp::Join {
            left,
            right,
            output: joined,
        },
        RawOp::ApplyUnitary {
            input,
            output,
            steps,
        },
        RawOp::Split {
            input: split,
            left: selector,
            right: target,
            left_bits: 2,
        },
    ] = raw.operations.as_slice()
    else {
        panic!("expected the complete two-wire selector and Bit target interval")
    };
    assert_eq!(
        (*left, *right),
        (raw.quantum_inputs[0].token, raw.quantum_inputs[1].token)
    );
    assert_eq!((input, output), (joined, split));
    assert_eq!(raw.quantum_outputs, [*selector, *target]);
    let matrix = Circuit::new(BasisType::Bits(3), steps.clone())
        .unwrap()
        .matrix(&mut Budget::new(100_000))
        .unwrap();

    // Tri occupies the two low wires. Only its three legal inputs have a
    // source meaning. Check every output, including the unused fourth label.
    for bit in 0..2 {
        for label in 0..3 {
            let col = label + 4 * bit;
            let dest = if label == 2 { col ^ 4 } else { col };
            let phase = if label == 1 && bit == 1 { 6 } else { 0 };
            for row in 0..8 {
                let expected = if row == dest {
                    Exact::phase(phase)
                } else {
                    Exact::zero()
                };
                assert_eq!(
                    matrix.get(row, col),
                    Some(expected),
                    "row {row}, column {col}"
                );
            }
        }
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_qmatch_preserves_nominal_targets_and_original_phases() {
    for (declaration, target, bits) in [
        ("pub enum Tri { A,B,C }", "Tri", 2),
        (
            "pub enum Tri { A,B,C } pub struct Record { payload: Tri, flag: Bit }",
            "Record",
            3,
        ),
        ("pub struct Empty {}", "Empty", 0),
    ] {
        for (selector, selector_declaration, labels) in [
            (
                "Select",
                "pub enum Select { Left,Right }",
                "Select::Right=>phase,Select::Left=>idle",
            ),
            ("Bit", "", "1=>phase,0=>idle"),
            ("Unit", "", "0=>phase"),
        ] {
            let source = format!(
                "{declaration} {selector_declaration}
                pub unitary fn idle(q:Q<{target}>)->Q<{target}>{{q}}
                pub unitary fn phase(q:Q<{target}>)->Q<{target}>{{global_phase_eighth(q)}}
                pub unitary fn keep(s:Q<{selector}>,q:Q<{target}>)->(Q<{selector}>,Q<{target}>){{
                    qmatch(s,q){{{labels}}}}}"
            );
            let accepted = selected(&source);
            let raw = accepted.program().raw();
            assert_eq!(raw.quantum_inputs.len(), 2);
            assert_eq!(raw.quantum_inputs[1].wires.len(), bits);
            assert_eq!(raw.quantum_outputs.len(), 2);
            let request = accepted.program().runtime_result().unwrap();
            assert!(matches!(
                request.parameters[1].get(1),
                Some(Atom::Finite(Basis::Enum(_, _) | Basis::Record(_, _)))
            ));
            kernel().check_program(accepted.program()).unwrap();
        }
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_qmatch_nominal_target_keeps_two_empty_owner_identities() {
    let accepted = selected(
        "pub enum One{Only} pub struct Empty{}
        pub unitary fn phase(q:Q<Empty>)->Q<Empty>{global_phase_eighth(q)}
        pub unitary fn keep(s:Q<One>,q:Q<Empty>)->(Q<One>,Q<Empty>){
            let pair=(s,q); let (tag,value)=pair;
            qmatch(tag,value){One::Only=>phase}}",
    );
    assert_eq!(accepted.program().raw().quantum_inputs.len(), 2);
    assert_eq!(accepted.program().raw().quantum_outputs.len(), 2);
    assert!(
        accepted
            .program()
            .raw()
            .quantum_inputs
            .iter()
            .all(|port| port.wires.is_empty())
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_nominal_target_arms_keep_original_imports_and_public_effects() {
    for effect in ["unitary", "observe", "isometry"] {
        let sources = BTreeMap::from([
            (
                "main".into(),
                "use facade::Tri; use facade::arm;
                pub unitary fn keep(s:Q<Bit>,q:Q<Tri>)->(Q<Bit>,Q<Tri>){
                    qmatch(s,q){0=>arm,1=>arm}}"
                    .into(),
            ),
            (
                "facade".into(),
                "pub use types::Tri; pub use implementation::arm;".into(),
            ),
            ("types".into(), "pub enum Tri{A,B,C}".into()),
            (
                "implementation".into(),
                format!(
                    "use types::Tri;
                pub {effect} fn arm(q:Q<Tri>)->Q<Tri>{{global_phase_eighth(q)}}"
                ),
            ),
        ]);
        let result = ParsedProgram::parse(Edition::E2026, sources)
            .and_then(|parsed| {
                parsed.instantiate_runtime_with_types(
                    "main::keep",
                    Default::default(),
                    Default::default(),
                    Default::default(),
                )
            })
            .map_err(|error| error.to_string())
            .and_then(|instance| {
                instance
                    .compile_runtime_with_kernel(&kernel())
                    .map_err(|error| error.message)
            });
        assert_eq!(result.is_ok(), effect == "unitary", "{effect}: {result:?}");
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_nominal_qmatch_keeps_structural_moves_and_suspended_callers() {
    let declarations = "pub enum Tri { A,B,C }
        pub unitary fn idle(q:Q<Bit>)->Q<Bit>{q}
        pub unitary fn phase(q:Q<Bit>)->Q<Bit>{global_phase_eighth(q)}
        pub unitary fn route(s:Q<Tri>,q:Q<Bit>)->(Q<Tri>,Q<Bit>){
            let pair=(s,q); let (tag,value)=pair;
            let result=qmatch(tag,value){Tri::C=>phase,Tri::A=>idle,Tri::B=>phase};
            let (tag,value)=result; (tag,value)}";
    let source = format!(
        "{declarations}
        pub unitary fn keep(s:Q<Tri>,q:Q<Bit>,r:Q<Bit>)->(Q<Bit>,Q<Tri>,Q<Bit>){{
            let r=h(r); let (s,q)=route(s,q); (r,s,q)}}"
    );
    let accepted = selected(&source);
    let raw = accepted.program().raw();
    assert_eq!(raw.quantum_inputs.len(), 3);
    assert_eq!(raw.quantum_outputs.len(), 3);
    kernel().check_program(accepted.program()).unwrap();
    let empty = selected(
        "pub enum One{Only}
        pub unitary fn phase(q:Q<Unit>)->Q<Unit>{global_phase_eighth(q)}
        pub unitary fn keep(s:Q<One>,q:Q<Unit>)->(Q<One>,Q<Unit>){
            let result=qmatch(s,q){One::Only=>phase}; result}",
    );
    assert_eq!(empty.program().raw().quantum_inputs.len(), 2);
    assert!(
        empty
            .program()
            .raw()
            .quantum_inputs
            .iter()
            .all(|port| port.wires.is_empty())
    );
    assert_eq!(empty.program().raw().quantum_outputs.len(), 2);
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_nominal_qmatch_retains_named_basis_preparation_and_hidden_observation() {
    use qleisli::ir::{Effect, RawOp};

    let source =
            "pub enum Tri{A,B,C}
            pub unitary fn idle(q:Q<Unit>)->Q<Unit>{q}
            pub observe fn keep(s:Q<Tri>,q:Q<Unit>)->(Q<Tri>,Q<Unit>){
                let hidden=measure_z(init0()); qmatch(s,q){Tri::A=>idle,Tri::B=>idle,Tri::C=>idle}}"
        ;
    let accepted = selected(source);
    let program = accepted.program();
    assert!(program.qmatch_source_checked());
    assert_eq!(
        program.runtime_result().unwrap().public_effect,
        Effect::Observe
    );
    let raw = program.raw();
    assert_eq!(raw.declared_effect, Effect::Observe);
    assert!(raw.classical_outputs.is_empty());
    assert!(matches!(
        raw.operations.as_slice(),
        [
            RawOp::PackUnit { output: unit },
            RawOp::LiftBasis { input, output, table, .. },
            RawOp::MeasureZ { input: measured, .. },
            rest @ ..
        ] if unit == input && output == measured && table == &[0] && !rest.is_empty()
    ));
    kernel().check_program(program).unwrap();
    // Preparing |1> is also a valid Raw isometry. The same original source
    // still prepares |0>, even when the measurement result stays hidden.
    let artifact = std::str::from_utf8(program.artifact()).unwrap();
    let original = r#""table":[0],"tag":"lift_basis""#;
    let changed = r#""table":[1],"tag":"lift_basis""#;
    assert_eq!(artifact.matches(original).count(), 1);
    let altered = artifact.replacen(original, changed, 1);
    let error = kernel()
        .check_qmatch_source_v5(altered.as_bytes(), program.request().unwrap())
        .unwrap_err();
    assert_eq!(error.code, "contract", "{error}");
    assert!(
        error.message.contains("Lean native checker rejected"),
        "{error}"
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_qmatch_context_retains_the_exact_prefix_phase() {
    use qleisli::contract::exact::{Budget, Exact, Matrix};
    use qleisli::contract::{BasisType, Circuit};
    let accepted = selected(
        "pub enum Tri{A,B,C}
        pub unitary fn idle(q:Q<Unit>)->Q<Unit>{q}
        pub unitary fn keep(s:Q<Tri>,q:Q<Unit>)->(Q<Tri>,Q<Unit>){
            let s=global_phase_eighth(s);
            qmatch(s,q){Tri::A=>idle,Tri::B=>idle,Tri::C=>idle}}",
    );
    let raw = accepted.program().raw();
    assert_eq!(raw.operations.len(), 4);
    let qleisli::ir::RawOp::ApplyUnitary { input, steps, .. } = &raw.operations[0] else {
        panic!("the original scalar action must precede the selection");
    };
    assert_eq!(*input, raw.quantum_inputs[0].token);
    let actual = Circuit::new(BasisType::Bits(2), steps.clone())
        .unwrap()
        .matrix(&mut Budget::new(10_000))
        .unwrap();
    let expected = Matrix::new(
        4,
        4,
        (0..16)
            .map(|index| {
                if index / 4 == index % 4 {
                    Exact::phase(1)
                } else {
                    Exact::zero()
                }
            })
            .collect(),
    )
    .unwrap();
    assert_eq!(actual, expected);
    kernel().check_program(accepted.program()).unwrap();
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_qmatch_context_preserves_grouped_postorder_calls_and_zero_width_owners() {
    let accepted = selected(
        "pub enum Tag{A,B}
        unitary fn idle(q:Q<Bit>)->Q<Bit>{q}
        pub unitary fn keep(s:Q<Tag>,q:Q<Bit>,z:Q<Unit>)->(Q<Unit>,Q<Tag>,Q<Bit>){
            let q=((/* λ */ h((h(q)))));
            let (s,q)=((/* μ */ qmatch(s,q){Tag::A=>idle,Tag::B=>idle}));
            let q=(h(h(q))); (z,s,q)}",
    );
    let raw = accepted.program().raw();
    assert_eq!(raw.operations.len(), 7);
    assert!(raw.quantum_inputs[2].wires.is_empty());
    assert_eq!(raw.quantum_outputs[0], raw.quantum_inputs[2].token);
    kernel().check_program(accepted.program()).unwrap();
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_qmatch_context_checks_builtin_pairs_with_a_nominal_spectator() {
    let source = "pub enum Tag{A,B}
        unitary fn idle(q:Q<Bit>)->Q<Bit>{q}
        unitary fn turn(q:Q<Bit>)->Q<Bit>{h(q)}
        pub unitary fn keep(s:Q<Bit>,q:Q<Bit>,z:Q<Tag>)->(Q<Tag>,Q<Bit>,Q<Bit>){
            let(s,q)=qmatch(s,q){0=>idle,1=>turn}; (z,s,q)}";
    let accepted = selected(source);
    let raw = accepted.program().raw();
    assert_eq!(raw.quantum_outputs[0], raw.quantum_inputs[2].token);
    kernel().check_program(accepted.program()).unwrap();

    // The original v5 request carries primitive arm bodies alongside the
    // same typed spectator and selected ports.
    let primitives = source.replace("0=>idle,1=>turn", "0=>h,1=>h");
    let accepted = selected(&primitives);
    assert!(accepted.program().qmatch_source_checked());
    let raw = accepted.program().raw();
    assert_eq!(raw.quantum_outputs[0], raw.quantum_inputs[2].token);
    kernel().check_program(accepted.program()).unwrap();
    let root = SourceRoot::new(&primitives);
    let cli = std::process::Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .args([
            "check",
            "--entry=main::keep",
            "--ir-profile=raw",
            "--format=json",
        ])
        .arg(format!(
            "--module=main={}",
            root.0.join("main.qli").display()
        ))
        .output()
        .unwrap();
    let output = String::from_utf8(cli.stdout).unwrap();
    assert!(cli.status.success(), "{output}");
    assert!(
        output.contains("\"scope\":\"finite-source-qmatch-context-v5\""),
        "{output}"
    );
    assert!(output.contains("\"source_steps_checked\":true"));
    assert!(output.contains("\"source_preservation_verified\":false"));
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_builtin_qmatch_keeps_the_runtime_root_for_register_primitives() {
    let accepted = selected(
        "pub unitary fn keep(s:Q<Bit>,q:Q<Bits<1>>)->(Q<Bit>,Q<Bits<1>>){
            let (b,r)=take_bit[1,0](q);
            let (s,b)=qmatch(s,b){0=>h,1=>h};
            (s,put_bit[1,0](b,r))
        }",
    );
    assert!(!accepted.program().qmatch_source_checked());
    kernel().check_program(accepted.program()).unwrap();
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_builtin_qmatch_keeps_the_runtime_root_for_exclusive_access() {
    for source in [
        "pub unitary fn keep(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){
            h(excl q);
            qmatch(s,q){0=>h,1=>h}
        }",
        "unitary fn apply(q:Q<Bit>)->Q<Bit>{h(excl q);q}
        pub unitary fn keep(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){
            qmatch(s,apply(q)){0=>h,1=>h}
        }",
    ] {
        let accepted = selected(source);
        assert!(!accepted.program().qmatch_source_checked());
        kernel().check_program(accepted.program()).unwrap();
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_builtin_qmatch_keeps_the_runtime_root_for_function_contracts() {
    let accepted = selected(
        "unitary fn implementation(q:Q<Bit>)->Q<Bit>{h(q)}
        unitary fn specification(q:Q<Bit>)->Q<Bit>{h(q)}
        pub unitary fn keep(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){
            let q=apply_contract(implementation,specification,q);
            qmatch(s,q){0=>h,1=>h}
        }",
    );
    assert!(!accepted.program().qmatch_source_checked());
    kernel().check_program(accepted.program()).unwrap();
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_nominal_qmatch_binds_compound_static_child_intervals() {
    let accepted = selected(
        "pub enum Flag { A, B }
        pub unitary fn keep(s:Q<Flag>,q:Q<Bit>)->(Q<Flag>,Q<Bit>){
            let q=if static 1==1 {let q=phase[1,3](q);h(q)} else {q};
            qmatch(s,q){Flag::A=>h,Flag::B=>global_phase_eighth}
        }",
    );
    assert!(accepted.program().qmatch_source_checked());
    let request =
        qleisli::interchange::qmatch::v5::Request::decode(accepted.program().request().unwrap())
            .unwrap();
    let [interval] = request.context.static_intervals.as_slice() else {
        panic!("expected the selected original compound interval");
    };
    assert_eq!(interval.parent, request.context.positions[0]);
    assert_eq!(
        interval
            .children
            .iter()
            .map(|child| (child.start, child.count))
            .collect::<Vec<_>>(),
        [(0, 1), (1, 1)]
    );
    kernel().check_program(accepted.program()).unwrap();
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_builtin_qmatch_keeps_the_runtime_root_for_static_continuations() {
    let source = "pub unitary fn keep[const n:Nat](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){
        let q=if static n==0 {if static n==0 {h(q)} else {q}} else {q};
        qmatch(s,q){0=>h,1=>h}
    }";
    let parsed = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([("main".into(), source.into())]),
    )
    .unwrap();
    for n in [0, 1] {
        let kernel = kernel();
        let instance = parsed
            .instantiate_runtime_with_types(
                "main::keep",
                Default::default(),
                BTreeMap::from([("n".into(), n)]),
                Default::default(),
            )
            .unwrap();
        let accepted = instance.compile_runtime_with_kernel(&kernel).unwrap();
        assert_eq!(accepted.program().qmatch_source_checked(), n == 1);
        kernel.check_program(accepted.program()).unwrap();
    }
    for source in [
        "use std::state::init0;
        pub isometry fn keep(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>,Q<Bit>){
            let fresh=if static 0==0 {init0()} else {init0()};
            let (s,q)=qmatch(s,q){0=>h,1=>h};
            (s,q,fresh)
        }",
        "pub unitary fn keep(s:Q<Bit>,q:Q<Bit>,b:Bit)->(Q<Bit>,Q<Bit>){
            let q=if static 0==0 {if b {h(q)} else {q}} else {q};
            qmatch(s,q){0=>h,1=>h}
        }",
    ] {
        let accepted = selected(source);
        assert!(!accepted.program().qmatch_source_checked());
        kernel().check_program(accepted.program()).unwrap();
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_nominal_qmatch_uses_original_imports_and_public_arm_effects() {
    for effect in ["unitary", "observe", "isometry"] {
        let main = "use facade::Tri; use facade::arm;
            pub unitary fn keep(s:Q<Tri>,q:Q<Unit>)->(Q<Tri>,Q<Unit>){
                qmatch(s,q){Tri::C=>arm,Tri::A=>arm,Tri::B=>arm}}";
        let sources = BTreeMap::from([
            ("main".into(), main.into()),
            (
                "facade".into(),
                "pub use types::Tri; pub use implementation::arm;".into(),
            ),
            ("types".into(), "pub enum Tri{A,B,C}".into()),
            (
                "implementation".into(),
                format!("pub {effect} fn arm(q:Q<Unit>)->Q<Unit>{{q}}"),
            ),
        ]);
        let result = ParsedProgram::parse(Edition::E2026, sources)
            .and_then(|parsed| {
                parsed.instantiate_runtime_with_types(
                    "main::keep",
                    Default::default(),
                    Default::default(),
                    Default::default(),
                )
            })
            .map_err(|error| error.to_string())
            .and_then(|instance| {
                instance
                    .compile_runtime_with_kernel(&kernel())
                    .map_err(|error| error.message)
            });
        assert_eq!(result.is_ok(), effect == "unitary", "{effect}: {result:?}");
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_qmatch_uses_the_common_original_source_and_named_arm_evidence() {
    let source = "pub unitary fn idle(q:Q<Unit>)->Q<Unit>{q}
        pub unitary fn phase(q:Q<Unit>)->Q<Unit>{global_phase_eighth(q)}
        pub unitary fn keep(s:Q<Bit>,q:Q<Unit>)->(Q<Bit>,Q<Unit>){
            qmatch(s,q){1=>phase,0=>idle}}";
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
    let kernel = kernel();
    let selected = instance.compile_runtime_with_kernel(&kernel).unwrap();
    assert!(selected.program().qmatch_source_checked());
    let request = selected.program().runtime_result().unwrap();
    assert_eq!(
        request.parameters,
        vec![
            vec![Atom::Quantum, Atom::Finite(Basis::Bit)],
            vec![Atom::Quantum, Atom::Finite(Basis::Unit)]
        ]
    );
    assert_eq!(request.public_effect, qleisli::ir::Effect::Unitary);
    assert_eq!(
        kernel
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
fn selected_qmatch_keeps_public_arm_effects_and_checks_inactive_arms() {
    let root = "use helper::arm;
        pub unitary fn keep(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){
            qmatch(s,q){0=>h,1=>arm}}";
    for effect in ["observe", "isometry"] {
        let error = ParsedProgram::parse(
            Edition::E2026,
            BTreeMap::from([
                ("main".into(), root.into()),
                (
                    "helper".into(),
                    format!("pub {effect} fn arm(q:Q<Bit>)->Q<Bit>{{q}}"),
                ),
            ]),
        )
        .unwrap_err();
        assert!(
            error.to_string().contains("Unitary") || error.to_string().contains("unitary"),
            "{error}"
        );
    }
    let source = "pub unitary fn idle(q:Q<Bit>)->Q<Bit>{q}
        pub unitary fn keep[const n:Nat](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){
            if static n==0 {(s,q)} else {qmatch(s,q){0=>idle,1=>idle}}}";
    let parsed = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([("main".into(), source.into())]),
    )
    .unwrap();
    assert!(
        parsed
            .requires_typed_runtime_transport("main::keep")
            .unwrap()
    );
    for n in [0, 1] {
        let instance = parsed
            .instantiate_runtime_with_types(
                "main::keep",
                Default::default(),
                BTreeMap::from([("n".into(), n)]),
                Default::default(),
            )
            .unwrap();
        instance.compile_runtime_with_kernel(&kernel()).unwrap();
    }
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
