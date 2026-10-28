//! Closed ordinary nominal source execution, with fresh native typed results.
//! Numerical correlations are regressions, not source-preservation proofs.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
mod common;
use common::SourceRoot;
use qleisli::frontend::compile::{check_project, compile_project};
use qleisli::interchange::ordinary_root::Storage;
use qleisli::sim::{SimulationLimits, run_closed};

const FIRST: &str = r#"
enum Tri { Zero, One, Other }
struct Empty {}
struct Result { choice: Tri, flag: Bit, empty: Empty }

pub observe fn main() -> Result {
    let q = basis unit(()) as _ { 0 };
    let bit = measure_z(h(q));
    let tag = if bit { Tri::One } else { Tri::Zero };
    let flag = match tag { Tri::Zero => 0, Tri::One => 1, Tri::Other => 0 };
    Result { empty: Empty {}, flag: flag, choice: tag }
}
"#;

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn called_and_unused_private_nominal_helpers_are_checked_without_exporting_them() {
    for (source, expected) in [
        (
            "enum E { A } fn helper()->E{E::A} observe fn main()->E{helper()}",
            vec![],
        ),
        (
            "enum E { A } fn helper()->E{E::A} observe fn main()->Bit{0}",
            vec![false],
        ),
        (
            "struct Empty {} fn helper()->Empty{Empty{}} observe fn main()->Empty{helper()}",
            vec![],
        ),
    ] {
        let root = SourceRoot::new(source);
        check_project(&root.0).unwrap();
        let program = compile_project(&root.0).unwrap();
        let actual = run_closed(&program, SimulationLimits::default()).unwrap();
        assert_eq!(actual, std::collections::BTreeMap::from([(expected, 1.0)]));
        let parsed = qleisli::frontend::compile::ParsedProgram::parse(
            qleisli::edition::Edition::E2026,
            std::collections::BTreeMap::from([("main".into(), source.into())]),
        )
        .unwrap();
        assert_eq!(
            parsed
                .instantiate("main::helper", Default::default(), Default::default())
                .unwrap_err()
                .code(),
            "visibility",
            "internal checking must not export the private source declaration"
        );
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn actual_source_record_enum_and_match_keep_correlated_result_storage() {
    let root = SourceRoot::new(FIRST);
    check_project(&root.0).unwrap();
    let program = compile_project(&root.0).unwrap();
    let request = program
        .ordinary_result()
        .expect("actual typed result retained");
    let Storage::Record(origin, fields) = &request.storage else {
        panic!("record lost")
    };
    assert_eq!(origin.source, FIRST);
    assert_eq!(
        fields
            .iter()
            .map(|(name, _)| name.as_str())
            .collect::<Vec<_>>(),
        ["choice", "flag", "empty"]
    );
    assert!(matches!(&fields[0].1, Storage::Enum(_, ids) if ids.len() == 2));
    assert!(matches!(&fields[2].1, Storage::Record(_, fields) if fields.is_empty()));
    let distribution = run_closed(&program, SimulationLimits::default()).unwrap();
    let expected = [
        (vec![false, false, false], 0.5),
        (vec![true, false, true], 0.5),
    ];
    assert_eq!(distribution.len(), expected.len());
    for (bits, weight) in expected {
        assert!((distribution[&bits] - weight).abs() < 1e-12);
    }
    assert!((distribution.values().sum::<f64>() - 1.0).abs() < 1e-12);
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn zero_width_nominal_result_and_public_observe_bound_survive_execution() {
    let root = SourceRoot::new("struct Empty {} pub observe fn main() -> Empty { Empty {} }");
    let program = compile_project(&root.0).unwrap();
    let request = program.ordinary_result().unwrap();
    assert_eq!(request.public_effect, qleisli::ir::Effect::Observe);
    assert!(matches!(&request.storage, Storage::Record(_, fields) if fields.is_empty()));
    let distribution = run_closed(&program, SimulationLimits::default()).unwrap();
    assert_eq!(distribution.len(), 1);
    assert_eq!(distribution[&Vec::<bool>::new()], 1.0);
    assert!(program.portable_artifact().is_err());
    assert!(
        qleisli::interchange::export(&program, None, qleisli::interchange::Version::V2).is_err()
    );
    assert!(qleisli::interop::export_openqasm3(&program).is_err());
    assert!(qleisli::interop::export_qir_base(&program).is_err());
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn hidden_observation_and_unconnected_quantum_nominal_interfaces_refuse() {
    let root = SourceRoot::new(&FIRST.replace("pub observe fn", "pub unitary fn"));
    assert_eq!(
        compile_project(&root.0).unwrap_err().code,
        qleisli::frontend::compile::ErrorCode::Effect
    );
    let root = SourceRoot::new(
        "enum Tri { A,B,C } pub unitary fn f(q:Q<Tri>)->Q<Tri>{q} observe fn main()->Bit{0}",
    );
    let error = compile_project(&root.0).unwrap_err();
    assert_eq!(
        error.code,
        qleisli::frontend::compile::ErrorCode::Unsupported
    );
    assert!(error.message.contains("quantum nominal"));
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn checked_cli_reports_actual_result_scope_and_refuses_incomplete_export_before_writing() {
    use std::process::Command;
    let root = SourceRoot::new("struct Empty {} pub observe fn main() -> Empty { Empty {} }");
    let checked = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .args(["check", root.0.to_str().unwrap(), "--format=json"])
        .output()
        .unwrap();
    assert!(
        checked.status.success(),
        "{}",
        String::from_utf8_lossy(&checked.stdout)
    );
    let text = String::from_utf8(checked.stdout).unwrap();
    assert!(text.contains("\"ordinary_result_checked\":true"));
    assert!(text.contains("\"source_preservation_verified\":false"));
    let output = root.0.join("unportable.qirf");
    let emitted = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .args(["emit-ir", root.0.to_str().unwrap(), "--format=json"])
        .arg(format!("--output={}", output.display()))
        .output()
        .unwrap();
    assert!(!emitted.status.success());
    assert!(!output.exists());
    assert!(
        String::from_utf8(emitted.stdout)
            .unwrap()
            .contains("typed artifact/request transport")
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn foreign_nominal_outputs_are_bound_and_uncovered_intermediates_never_fall_back_to_raw() {
    let labels = "pub enum Tri { A,B,C }";
    let root = SourceRoot::new("use labels::Tri; pub observe fn main()->Tri{Tri::C}");
    root.write("labels.qli", labels);
    let program = compile_project(&root.0).unwrap();
    let request = program.ordinary_result().unwrap();
    assert!(
        matches!(&request.storage,Storage::Enum(origin,_) if origin.module=="labels" && origin.source==labels)
    );
    let distribution = run_closed(&program, SimulationLimits::default()).unwrap();
    assert_eq!(distribution.len(), 1);
    assert_eq!(distribution[&vec![false, true]], 1.0);
    let root = SourceRoot::new(
        "use labels::Tri; pub observe fn main()->Bit{let t=Tri::C;match t{Tri::A=>0,Tri::B=>0,Tri::C=>1}}",
    );
    root.write("labels.qli", labels);
    let error = compile_project(&root.0).unwrap_err();
    assert_eq!(
        error.code,
        qleisli::frontend::compile::ErrorCode::Unsupported
    );
    assert!(
        error
            .message
            .contains("intermediate nominal source modules")
    );
    let root = SourceRoot::new(
        "enum Tri{A,B,C} pub observe fn main()->Bit{let t=Tri::C;match t{Tri::A=>0,Tri::B=>0,Tri::C=>1}}",
    );
    let program = compile_project(&root.0).unwrap();
    assert!(
        program.ordinary_result().is_some(),
        "same-source intermediates use the typed gate"
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn general_ordinary_parameters_use_all_input_native_checks_and_actual_closed_callers() {
    type Expected = &'static [(&'static [bool], f64)];
    type Case = (&'static str, &'static str, Expected);
    let cases: &[Case] = &[
        (
            "enum-function",
            r###"enum Tri { A, B, C }
pub observe fn cycle(value: Tri) -> Tri {
    match value { Tri::A => Tri::B, Tri::B => Tri::C, Tri::C => Tri::A }
}
pub observe fn main() -> Tri { cycle(Tri::C) }
"###,
            &[(&[false, false], 1.0)],
        ),
        (
            "measured-enum-call",
            r###"enum Tri { A, B, C }
pub observe fn cycle(value: Tri) -> Tri {
    match value { Tri::A => Tri::B, Tri::B => Tri::C, Tri::C => Tri::A }
}
pub observe fn main() -> Tri {
    let q = basis unit(()) as _ { 0 };
    let bit = measure_z(h(q));
    let value = if bit { Tri::B } else { Tri::A };
    cycle(value)
}
"###,
            &[(&[true, false], 0.5), (&[false, true], 0.5)],
        ),
        (
            "record-function",
            r###"enum Tri { A, B, C }
struct Empty {}
struct Row { tag: Tri, flag: Bit, empty: Empty }
pub observe fn flip(row: Row) -> Row {
    Row { empty: row.empty, flag: not row.flag, tag: row.tag }
}
pub observe fn main() -> Row {
    flip(Row { empty: Empty {}, flag: 0, tag: Tri::C })
}
"###,
            &[(&[false, true, true], 1.0)],
        ),
        (
            "zero-width-arguments",
            r###"enum Tri { A, B, C }
struct Empty {}
pub fn select(empty: Empty, tag: Tri, unit_value: Unit, word: Bits<0>) -> Tri { tag }
pub observe fn main() -> Tri { select(Empty {}, Tri::C, (), empty_bits()) }
"###,
            &[(&[false, true], 1.0)],
        ),
        (
            "tuple-parameter",
            r###"enum Tri { A, B, C }
pub fn flag((tag, bit): (Tri, Bit)) -> Bit {
    match tag { Tri::A => bit, Tri::B => not bit, Tri::C => bit }
}
pub observe fn main() -> Bit { flag((Tri::B, 0)) }
"###,
            &[(&[true], 1.0)],
        ),
        (
            "private-parameter-helper",
            r###"enum Tri { A, B, C }
fn helper(value: Tri) -> Tri { value }
pub observe fn main() -> Tri { helper(Tri::C) }
"###,
            &[(&[false, true], 1.0)],
        ),
    ];
    for (name, source, expected) in cases {
        let root = SourceRoot::new(source);
        check_project(&root.0).unwrap_or_else(|error| panic!("{name}: {error}"));
        let program = compile_project(&root.0).unwrap_or_else(|error| panic!("{name}: {error}"));
        let actual = run_closed(&program, SimulationLimits::default()).unwrap();
        assert_eq!(actual.len(), expected.len(), "{name}: {actual:?}");
        for (bits, weight) in *expected {
            assert!(
                (actual.get(*bits).unwrap_or(&-1.0) - weight).abs() < 1e-12,
                "{name}: {bits:?} {actual:?}"
            );
        }
        assert!(
            program.ordinary_result().is_some(),
            "{name}: typed caller disappeared"
        );
    }
}
