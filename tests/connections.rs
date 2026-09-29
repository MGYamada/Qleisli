//! Host transport regressions; Python/QIR-reader cases have a separate runner.
use std::io::Write;
use std::process::{Command, Output, Stdio};

fn call(args: &[&str], input: &[u8]) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .arg("interop")
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(input).unwrap();
    child.wait_with_output().unwrap()
}

#[test]
fn terminal_import_execution_export_and_seeded_fresh_shots() {
    let source = include_bytes!("fixtures/interop/bell.qasm");
    for action in ["check", "run", "emit-ir", "emit-qasm", "emit-qir"] {
        let result = call(&[action, "-", "--input=qasm"], source);
        assert!(result.status.success(), "{:?}", result);
        let text = String::from_utf8(result.stdout).unwrap();
        assert!(text.contains("\"outcome\":\"ok\""));
        assert!(text.contains("\"diagnostics\":[]"));
    }
    let args = ["sample", "-", "--input=qasm", "--shots=20", "--seed=0"];
    let first = call(&args, source);
    let second = call(&args, source);
    assert!(first.status.success());
    assert_eq!(first.stdout, second.stdout);
    let text = String::from_utf8(first.stdout).unwrap();
    assert!(text.contains("[true, true]"));
    assert!(text.contains("[false, false]"));
}

#[test]
fn malformed_or_unsupported_input_has_no_partial_result() {
    for (format, input) in [
        ("--input=qirf", &b"{}"[..]),
        ("--input=qasm", &b"OPENQASM 3.0; qubit q;"[..]),
        ("--input=qasm", &b"\xff"[..]),
    ] {
        let result = call(&["emit-qir", "-", format], input);
        assert_eq!(result.status.code(), Some(1));
        let text = String::from_utf8(result.stdout).unwrap();
        assert!(text.contains("\"outcome\":\"error\""));
        assert!(text.contains("\"result\":null"));
    }
}

#[test]
fn malformed_options_are_usage_errors_before_reading_input() {
    for args in [
        vec!["check", "-", "--input=qir"],
        vec!["sample", "-", "--input=qasm", "--shots=01", "--seed=0"],
        vec!["sample", "-", "--input=qasm", "--shots=1"],
        vec!["run", "-", "--input=qasm", "--seed=0"],
        vec!["check", "-", "--input=qli"],
        vec!["check", "-", "--input=qasm", "--input=qasm"],
    ] {
        let result = call(&args, b"");
        assert_eq!(result.status.code(), Some(2), "{args:?}");
    }
}
