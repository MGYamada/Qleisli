//! Selected nominal source executes through the existing typed native gate.
//! Exact request assertions and small runtime regressions are not preservation proofs.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
mod common;
use common::SourceRoot;
use qleisli::edition::Edition;
use qleisli::frontend::compile::{Instantiation, ParsedProgram};
use qleisli::interchange::native::Kernel;
use qleisli::sim::{SimulationLimits, run_closed};
use std::collections::BTreeMap;
use std::process::Command;

fn kernel() -> std::path::PathBuf {
    std::env::var_os("QLEISLI_KERNEL")
        .expect("explicit native test gate")
        .into()
}

fn instance(modules: &[(&str, &str)]) -> Instantiation {
    ParsedProgram::parse(
        Edition::E2026,
        modules
            .iter()
            .map(|(name, source)| (name.to_string(), source.to_string()))
            .collect(),
    )
    .unwrap()
    .instantiate_ordinary_with_types(
        "main::choose",
        Default::default(),
        Default::default(),
        Default::default(),
    )
    .unwrap()
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_ordinary_uses_actual_public_nominal_types_and_classical_bodies() {
    for (source, expected) in [
        (
            "pub enum Tri {A,B,C} pub classical fn choose()->Bit {match Tri::C {Tri::A=>0,Tri::B=>0,Tri::C=>1}}",
            vec![true],
        ),
        (
            "pub enum Tri {A,B,C} pub fn choose()->Tri {Tri::C}",
            vec![false, true],
        ),
        (
            "pub struct Empty {} pub fn choose()->Empty {Empty{}}",
            vec![],
        ),
        (
            "pub enum Tri {A,B,C} pub struct Empty {} pub struct Packet {pub flag:Bit,pub tag:Tri,pub empty:Empty} pub fn choose()->Packet {Packet{empty:Empty{},tag:Tri::C,flag:1}}",
            vec![true, false, true],
        ),
        (
            "pub enum Tri {A,B,C} classical fn flag()->Bit {match Tri::C {Tri::A=>0,Tri::B=>0,Tri::C=>1}} pub fn choose()->Bit {flag()}",
            vec![true],
        ),
        (
            "pub enum Tri {A,B,C} unitary fn unused(q:Q<Tri>)->Q<Tri>{q} pub fn choose()->Bit{1}",
            vec![true],
        ),
    ] {
        let original = instance(&[("main", source)]);
        let selected = original
            .compile_ordinary_with_kernel(&Kernel::new(kernel(), Edition::E2026))
            .unwrap();
        assert_eq!(selected.source().entry(), "main::choose");
        assert_eq!(selected.runtime_parameters(), 0);
        let request = selected
            .program()
            .ordinary_result()
            .expect("fresh native typed request");
        assert_eq!(request.declaration, "choose");
        assert!(request.parameters.is_empty());
        assert_eq!(request.input_rows, vec![Vec::<bool>::new()]);
        assert_eq!(
            run_closed(selected.program(), SimulationLimits::default()).unwrap(),
            BTreeMap::from([(expected, 1.0)])
        );
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_ordinary_keeps_import_paths_and_every_nominal_input_row() {
    let classical = instance(&[("main","pub enum Tri{A,B,C} pub classical fn choose(value:Tri)->Tri {match value{Tri::A=>Tri::B,Tri::B=>Tri::C,Tri::C=>Tri::A}}")])
        .compile_ordinary_with_kernel(&Kernel::new(kernel(),Edition::E2026)).unwrap();
    assert_eq!(
        classical.program().ordinary_result().unwrap().input_rows,
        vec![vec![false, false], vec![true, false], vec![false, true]]
    );
    assert!(run_closed(classical.program(), SimulationLimits::default()).is_err());
    let selected = instance(&[
        ("main","use alias::Tri; pub fn choose(value:Tri)->Tri {match value {Tri::A=>Tri::B,Tri::B=>Tri::C,Tri::C=>Tri::A}}"),
        ("alias","pub use leaf::Tri;"),
        ("leaf","pub enum Tri {A,B,C}"),
    ]).compile_ordinary_with_kernel(&Kernel::new(kernel(), Edition::E2026)).unwrap();
    assert_eq!(selected.runtime_parameters(), 1);
    assert_eq!(
        selected.program().ordinary_result().unwrap().input_rows,
        vec![vec![false, false], vec![true, false], vec![false, true]]
    );
    assert!(run_closed(selected.program(), SimulationLimits::default()).is_err());
    for ty in ["Empty", "Unit", "Bits<0>", "(Unit,Empty)"] {
        let source = format!("pub struct Empty {{}} pub fn choose(value:{ty})->{ty} {{value}}");
        let empty = instance(&[("main", &source)])
            .compile_ordinary_with_kernel(&Kernel::new(kernel(), Edition::E2026))
            .unwrap();
        assert_eq!(empty.runtime_parameters(), 1);
        assert_eq!(
            empty.program().ordinary_result().unwrap().parameters.len(),
            1
        );
        assert!(run_closed(empty.program(), SimulationLimits::default()).is_err());
        assert!(
            qleisli::sim::sample_closed(
                empty.program(),
                &mut qleisli::sim::SplitMix64::new(0),
                qleisli::sim::SampleLimits::default()
            )
            .is_err()
        );
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_ordinary_refuses_quantum_and_generic_routes_without_fallback() {
    let program = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([(
            "main".into(),
            "pub enum Tri{A,B,C} pub fn choose[const A:Basis](v:A)->A{v}".into(),
        )]),
    )
    .unwrap();
    let original = program
        .instantiate_ordinary_with_types(
            "main::choose",
            BTreeMap::from([("A".into(), program.basis_binding("main::Tri").unwrap())]),
            Default::default(),
            Default::default(),
        )
        .unwrap();
    let kernel = Kernel::new(kernel(), Edition::E2026);
    assert!(
        original
            .compile_ordinary_with_kernel(&kernel)
            .unwrap_err()
            .message
            .contains("static-binder")
    );
    let original = instance(&[(
        "main",
        "pub enum Tri {A,B,C} pub observe fn choose()->Tri {let b=measure_z(init0()); if b {Tri::A}else{Tri::C}}",
    )]);
    assert!(original.compile_ordinary_with_kernel(&kernel).is_err());
    let absent = Kernel::new("/nonexistent/qleisli-native-selected-test", Edition::E2026);
    assert!(
        instance(&[("main", "pub enum Tri {A,B,C} pub fn choose()->Tri{Tri::C}")])
            .compile_ordinary_with_kernel(&absent)
            .is_err()
    );
}

fn cli(root: &SourceRoot, action: &str) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
    command
        .arg(action)
        .arg("--entry=main::choose")
        .arg("--format=json")
        .arg("--ir-profile=raw")
        .arg(format!(
            "--module=main={}",
            root.0.join("main.qli").display()
        ));
    if action != "emit-proposal" {
        command.arg(format!("--lean-kernel={}", kernel().display()));
    }
    command
}

#[test]
fn selected_ordinary_preparation_preserves_visibility_bindings_and_unused_checks() {
    for source in [
        "pub enum Tri{A,B,C} fn broken()->Bit{()} pub fn choose()->Tri{Tri::C}",
        "pub enum Tri{A,B,C} pub unitary fn choose()->Tri{let b=measure_z(init0()); if b{Tri::A}else{Tri::C}}",
        "pub enum Tri{A,B,C} fn unused(v:Tri)->Bit{match v{Tri::A=>0}} pub fn choose()->Tri{Tri::C}",
    ] {
        assert!(
            ParsedProgram::parse(
                Edition::E2026,
                BTreeMap::from([("main".into(), source.into())])
            )
            .is_err()
        );
    }
    let private = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([(
            "main".into(),
            "pub enum Tri{A,B,C} fn choose()->Tri{Tri::C}".into(),
        )]),
    )
    .unwrap();
    assert!(
        private
            .instantiate_ordinary_with_types(
                "main::choose",
                Default::default(),
                Default::default(),
                Default::default()
            )
            .is_err()
    );
    let public = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([(
            "main".into(),
            "pub enum Tri{A,B,C} pub fn choose()->Tri{Tri::C}".into(),
        )]),
    )
    .unwrap();
    assert!(
        public
            .instantiate_ordinary_with_types(
                "main::choose",
                BTreeMap::from([("unused".into(), public.basis_binding("main::Tri").unwrap())]),
                Default::default(),
                Default::default()
            )
            .is_err()
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_ordinary_preserves_word_and_call_depth_capacity() {
    let wide = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([(
            "main".into(),
            "pub enum Tri{A,B,C} pub fn choose(value:Bits<9>)->Bit{0}".into(),
        )]),
    )
    .unwrap();
    let error = wide
        .instantiate_ordinary_with_types(
            "main::choose",
            Default::default(),
            Default::default(),
            Default::default(),
        )
        .unwrap_err();
    assert_eq!(error.code(), "limit");
    let mut source = "pub enum Tri{A,B,C} pub fn choose()->Bit{f0()}\n".to_string();
    for i in 0..18 {
        source.push_str(&format!("fn f{i}()->Bit{{f{}()}}\n", i + 1));
    }
    source.push_str("fn f18()->Bit{1}\n");
    let deep = instance(&[("main", &source)]);
    assert_eq!(
        deep.compile_ordinary_with_kernel(&Kernel::new(kernel(), Edition::E2026))
            .unwrap_err()
            .code,
        "limit"
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_ordinary_cli_reports_actual_typed_scope_and_preserves_export_refusal() {
    let root = SourceRoot::new("pub enum Tri {A,B,C} pub fn choose()->Tri{Tri::C}");
    for action in ["check", "run"] {
        let result = cli(&root, action).output().unwrap();
        assert!(result.status.success(), "{result:?}");
        let text = String::from_utf8(result.stdout).unwrap();
        for fragment in [
            "\"scope\":\"finite-ordinary-root-v2\"",
            "\"ordinary_result_checked\":true",
            "\"source_meaning_verified\":false",
            "\"native_check_scope\":\"selected-specialization\"",
        ] {
            assert!(text.contains(fragment), "{text}");
        }
    }
    let output = root.0.join("proposal.qirf");
    let result = cli(&root, "emit-proposal")
        .arg(format!("--output={}", output.display()))
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert!(!output.exists());
    assert!(
        String::from_utf8(result.stdout)
            .unwrap()
            .contains("complete typed request transport")
    );
    let root = SourceRoot::new("pub struct Empty {} pub fn choose(value:Empty)->Empty{value}");
    assert!(cli(&root, "check").output().unwrap().status.success());
    let result = cli(&root, "run").output().unwrap();
    assert!(!result.status.success());
    assert!(
        String::from_utf8(result.stdout)
            .unwrap()
            .contains("zero runtime parameters")
    );
}
