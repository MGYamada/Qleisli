mod common;

use common::SourceRoot;
use std::process::{Command, Output};

fn cli(args: &[&std::ffi::OsStr]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .args(args)
        .output()
        .unwrap()
}

#[test]
fn truncated_static_arguments_emit_one_located_json_parse_error() {
    for source in [
        "unitary fn f(q: Q<Bit>) -> Q<Bit> { g[",
        "unitary fn f(q: Q<Bit>) -> Q<Bit> { g[repeat_op(0,",
    ] {
        let root = SourceRoot::new(source);
        let end = source.len();
        let column = end + 1;
        for command in ["check", "run"] {
            let output = cli(&[
                command.as_ref(),
                root.0.as_os_str(),
                "--format=json".as_ref(),
            ]);
            assert_eq!(output.status.code(), Some(1), "{output:?}");
            assert!(output.stderr.is_empty(), "{output:?}");
            assert_eq!(
                String::from_utf8(output.stdout).unwrap(),
                format!(
                    "{{\"format\":\"qleisli.result\",\"version\":1,\"command\":\"{command}\",\"outcome\":\"error\",\"diagnostics\":[{{\"code\":\"parse\",\"severity\":\"error\",\"message\":\"parse error: expected a static operation description\",\"primary\":{{\"path\":\"main.qli\",\"start\":{end},\"end\":{end},\"line\":1,\"column\":{column}}},\"related\":[]}}],\"result\":null}}\n"
                )
            );
        }
    }
}

#[test]
fn json_check_and_run_have_golden_envelopes_in_every_flag_position() {
    let root = SourceRoot::new("observe fn main() -> CBit { true }");
    for (command, result) in [
        ("check", "{\"verified\":true}"),
        (
            "run",
            "{\"distribution\":[{\"bits\":[true],\"probability\":1}]}",
        ),
    ] {
        for flag_index in 0..3 {
            let mut args = vec![command.as_ref(), root.0.as_os_str()];
            args.insert(flag_index, "--format=json".as_ref());
            let output = cli(&args);
            assert_eq!(output.status.code(), Some(0), "{output:?}");
            assert!(output.stderr.is_empty(), "{output:?}");
            assert_eq!(
                String::from_utf8(output.stdout).unwrap(),
                format!(
                    "{{\"format\":\"qleisli.result\",\"version\":1,\"command\":\"{command}\",\"outcome\":\"ok\",\"diagnostics\":[],\"result\":{result}}}\n"
                )
            );
        }
    }
}

#[test]
fn json_usage_is_atomic_and_keeps_the_usage_exit_code() {
    for args in [
        vec!["check", "--format=json"],
        vec!["check", ".", "--format=json", "--format=json"],
        vec!["check", ".", "--unknown", "--format=json"],
        vec!["check", ".", "--format", "--format=json"],
        vec!["check", ".", "--format=xml", "--format=json"],
        vec!["check", "--unknown", "--format=json"],
    ] {
        let args: Vec<_> = args.iter().map(std::ffi::OsStr::new).collect();
        let output = cli(&args);
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stderr.is_empty());
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            concat!(
                "{\"format\":\"qleisli.result\",\"version\":1,\"command\":\"check\",\"outcome\":\"error\",",
                "\"diagnostics\":[{\"code\":\"usage\",\"severity\":\"error\",",
                "\"message\":\"usage: qleisli <check|run> <source-root> [--format=json]\",",
                "\"primary\":null,\"related\":[]}],\"result\":null}\n"
            )
        );
    }
}

#[test]
fn json_runtime_limit_does_not_emit_a_partial_distribution() {
    let mut source = String::from(
        "use std::quantum::init0; use std::observe::discard; observe fn main() -> Unit {",
    );
    for i in 0..17 {
        source.push_str(&format!("let q{i} = init0();"));
    }
    for i in 0..17 {
        source.push_str(&format!("discard(q{i});"));
    }
    source.push_str("() }");
    let root = SourceRoot::new(&source);
    let output = cli(&["run".as_ref(), root.0.as_os_str(), "--format=json".as_ref()]);
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stderr.is_empty());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        concat!(
            "{\"format\":\"qleisli.result\",\"version\":1,\"command\":\"run\",\"outcome\":\"error\",",
            "\"diagnostics\":[{\"code\":\"limit\",\"severity\":\"error\",",
            "\"message\":\"simulation requires 17 qubits; limit is 16\",",
            "\"primary\":null,\"related\":[]}],\"result\":null}\n"
        )
    );
}

#[test]
fn json_type_failure_is_located_in_the_original_source() {
    let root = SourceRoot::new("observe fn main() -> CBit { () }");
    let output = cli(&[
        "check".as_ref(),
        "--format=json".as_ref(),
        root.0.as_os_str(),
    ]);
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stderr.is_empty());
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains("\"code\":\"type_mismatch\""), "{output}");
    assert!(output.contains("\"path\":\"main.qli\""), "{output}");
    assert!(!output.contains(&root.0.display().to_string()), "{output}");
}
