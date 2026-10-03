//! Host transport regressions; Python/QIR-reader cases have a separate runner.
mod common;
use common::SourceRoot;
use std::io::Write;
use std::process::{Command, Output, Stdio};

fn call(args: &[&str], input: &[u8]) -> Output {
    let reads_stdin = args.get(1) == Some(&"-");
    let mut child = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .arg("interop")
        .args(args)
        .stdin(if reads_stdin {
            Stdio::piped()
        } else {
            Stdio::null()
        })
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    if let Some(mut stdin) = child.stdin.take() {
        match stdin.write_all(input) {
            Ok(()) => {}
            // Invalid options or a bounded read can close stdin before the writer.
            Err(error) if error.kind() == std::io::ErrorKind::BrokenPipe => {}
            Err(error) => panic!("child stdin write failed: {error}"),
        }
    }
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

#[test]
fn file_inputs_and_early_usage_rejection_do_not_require_stdin_reads() {
    let root = SourceRoot::new("");
    let file = root.0.join("bell.qasm");
    std::fs::write(&file, include_bytes!("fixtures/interop/bell.qasm")).unwrap();
    // This exceeds the pipe buffer: file invocations must ignore this input,
    // while an invalid stdin invocation may close its pipe before it is sent.
    let unused_input = vec![b'x'; 1 << 20];
    let file_result = call(
        &["check", file.to_str().unwrap(), "--input=qasm"],
        &unused_input,
    );
    assert!(file_result.status.success(), "{file_result:?}");
    let rejected = call(&["check", "-", "--input=qir"], &unused_input);
    assert_eq!(rejected.status.code(), Some(2), "{rejected:?}");
}

#[test]
fn qasm_byte_spans_keep_unicode_crlf_coordinates_and_input_identity() {
    let source = "// λ🦀\r\nOPENQASM 3.0; include \"stdgates.inc\"; qubit q; bit c; reset q; mystery q; c = measure q;";
    let root = SourceRoot::new("");
    let file = root.0.join("bad.qasm");
    std::fs::write(&file, source).unwrap();
    let start = source.find("mystery").unwrap();
    for (path, label) in [(file.to_str().unwrap(), "bad.qasm"), ("-", "-")] {
        let result = call(&["check", path, "--input=qasm"], source.as_bytes());
        assert_eq!(result.status.code(), Some(1), "{result:?}");
        let text = String::from_utf8(result.stdout).unwrap();
        assert!(text.contains("\"code\":\"unsupported\""), "{text}");
        assert!(text.contains(&format!("\"primary\":{{\"path\":\"{label}\",\"start\":{start},\"end\":{},\"line\":2,\"column\":64}}", start + 7)), "{text}");
    }
    for (args, input) in [
        (vec!["check", "-", "--input=qasm"], &b"\xff"[..]),
        (
            vec!["check", "missing-issue-56.qasm", "--input=qasm"],
            &b""[..],
        ),
        (vec!["check", "-", "--input=qir"], &b""[..]),
    ] {
        let result = call(&args, input);
        assert!(!result.status.success());
        let text = String::from_utf8(result.stdout).unwrap();
        assert!(text.contains("\"primary\":null,\"related\":[]"), "{text}");
    }
}

#[test]
fn malformed_artifact_pointer_matches_the_verify_ir_envelope() {
    use qleisli::ir::{Effect, RawProgram};
    let verified = common::accept(RawProgram {
        quantum_inputs: vec![],
        classical_inputs: vec![],
        operations: vec![],
        quantum_outputs: vec![],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    })
    .unwrap();
    let bytes =
        qleisli::interchange::export(&verified, None, qleisli::interchange::Version::V2).unwrap();
    let text = String::from_utf8(bytes).unwrap();
    assert!(text.contains("\"root\":0"), "{text}");
    let malformed = text.replace("\"root\":0", "\"root\":null");
    let root = SourceRoot::new("");
    let file = root.0.join("bad.qirf");
    std::fs::write(&file, malformed).unwrap();
    let direct = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .args(["verify-ir", file.to_str().unwrap(), "--format=json"])
        .output()
        .unwrap();
    let interop = call(&["check", file.to_str().unwrap(), "--input=qirf"], b"");
    assert_eq!(direct.status.code(), Some(1));
    assert_eq!(interop.status.code(), Some(1));
    let expected = String::from_utf8(direct.stdout)
        .unwrap()
        .replace("\"command\":\"verify-ir\"", "\"command\":\"interop check\"");
    assert!(expected.contains("\"code\":\"invalid_ir\""), "{expected}");
    assert_eq!(String::from_utf8(interop.stdout).unwrap(), expected);
}
