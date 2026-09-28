//! Diagnostic text assists repair; schemas, locations and rejection stay intact.
mod common;
use common::SourceRoot;
use qleisli_core::frontend::compile::{check_project_diagnostic, compile_project};
use qleisli_core::sim::{SimulationLimits, run_closed};
use std::{fs, path::Path, process::Command};

fn fixture(name: &str) -> String {
    fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/repair_diagnostics")
            .join(format!("{name}.qli")),
    )
    .unwrap()
}

#[test]
fn concrete_mismatches_show_expected_and_actual_exact_types() {
    for (name, expected, actual) in [
        ("ordinary_return", "(Q<Bit>,Unit)", "Q<Bit>"),
        ("basis_return", "(Bit,(Bit,Bit))", "((Bit,Bit),Bit)"),
        ("basis_argument", "(Unit,Bit)", "Bit"),
        ("static_argument", "Op<Bit>", "Op<(Bit,Bit)>"),
        ("static_composition", "Op<Bit>", "Op<(Bit,Bit)>"),
        ("static_input", "Q<Bit>", "Q<(Bit,Bit)>"),
        ("branch_result", "CBit", "Unit"),
        ("primitive", "Q<Bit>", "CBit"),
        ("zero_width", "Q<Bit>", "Q<Unit>"),
        ("condition", "CBit", "Q<Bit>"),
        ("boolean", "CBit", "Q<Unit>"),
        ("predicate", "Bit -> Bit", "Unit -> Bit"),
        ("certified_predicate", "Bit -> Bit", "Unit -> Bit"),
    ] {
        let root = SourceRoot::new(&fixture(name));
        let error = check_project_diagnostic(&root.0).unwrap_err();
        assert_eq!(error.code, "type_mismatch", "{name}: {error:?}");
        assert!(
            error.message.contains(&format!("expected `{expected}`")),
            "{name}: {error:?}"
        );
        assert!(
            error.message.contains(&format!("found `{actual}`")),
            "{name}: {error:?}"
        );
        assert!(error.primary.is_some(), "{name}: {error:?}");
    }
}

#[test]
fn argument_types_reach_text_and_json_without_moving_the_callers_span() {
    let source = "// 日本語\r\nuse std::transforms::qft3;\r\nunitary fn bad(q:Q<(Bit,(Bit,Bit))>) -> Q<(Bit,(Bit,Bit))> { qft3(q) }";
    let root = SourceRoot::new(source);
    let error = check_project_diagnostic(&root.0).unwrap_err();
    let location = error.primary.unwrap();
    let argument = source.rfind("(q)").unwrap() + 1;
    assert_eq!(
        (location.span.start, location.span.end),
        (argument, argument + 1)
    );
    assert_eq!(location.line, 3);
    assert_eq!(
        location.column,
        source[..argument]
            .rsplit('\n')
            .next()
            .unwrap()
            .chars()
            .count()
            + 1
    );
    for json in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
        command.arg("check").arg(&root.0);
        if json {
            command.arg("--format=json");
        }
        let output = command.output().unwrap();
        assert_eq!(output.status.code(), Some(1));
        let text = String::from_utf8(if json { output.stdout } else { output.stderr }).unwrap();
        assert!(
            text.contains("expected `Q<((Bit,Bit),Bit)>`, found `Q<(Bit,(Bit,Bit))>`"),
            "{text}"
        );
        if json {
            assert!(text.contains("\"code\":\"type_mismatch\""), "{text}");
            assert!(text.contains("\"related\":[]"), "{text}");
        }
    }
}

#[test]
fn cleanup_hint_has_a_working_repair_but_cannot_authorize_a_false_contract() {
    let original = include_str!("fixtures/qli_authoring/rejected/auxiliary_hh.qli");
    let root = SourceRoot::new(original);
    let error = check_project_diagnostic(&root.0).unwrap_err();
    assert_eq!(error.code, "unsupported");
    assert!(
        error
            .message
            .contains("with_computed(source, predicate, logical) { |data, ancilla| ... }")
    );
    assert!(error.message.contains("return both owners"));
    assert!(error.message.contains("does not bypass cleanup checking"));
    let location = error.primary.unwrap();
    assert!(original[location.span.start..location.span.end].contains("h(h(flag))"));
    for json in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
        command.arg("check").arg(&root.0);
        if json {
            command.arg("--format=json");
        }
        let output = command.output().unwrap();
        assert_eq!(output.status.code(), Some(1));
        let text = String::from_utf8(if json { output.stdout } else { output.stderr }).unwrap();
        assert!(text.contains("return both owners"), "{text}");
    }
    root.write(
        "main.qli",
        include_str!("fixtures/qli_authoring/accepted/auxiliary_hh.qli"),
    );
    let program = compile_project(&root.0).unwrap();
    let result = run_closed(&program, SimulationLimits::default()).unwrap();
    assert!((result.get(&vec![false]).unwrap() - 1.0).abs() < 1e-12);
    root.write("main.qli", &fixture("false_cleanup"));
    let error = check_project_diagnostic(&root.0).unwrap_err();
    assert_eq!(error.code, "invalid_ir");
    assert!(error.message.contains("U E_in = E_out u"), "{error:?}");
}
