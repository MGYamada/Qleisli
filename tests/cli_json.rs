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
fn native_transport_failures_use_the_closed_v1_project_code() {
    let root = SourceRoot::new("observe fn main()->Bit{1}");
    let artifact = root.0.join("valid.qirf");
    let emitted = cli(&[
        "emit-ir".as_ref(),
        root.0.as_os_str(),
        format!("--output={}", artifact.display()).as_ref(),
    ]);
    assert!(emitted.status.success(), "{emitted:?}");
    for command in ["check", "run", "sample", "emit-ir", "verify-ir"] {
        let mut process = Command::new(env!("CARGO_BIN_EXE_qleisli"));
        process
            .arg(command)
            .arg(if command == "verify-ir" {
                &artifact
            } else {
                &root.0
            })
            .arg("--format=json")
            .arg(format!("--lean-kernel={}", root.0.join("absent").display()));
        if command == "sample" {
            process.args(["--shots=1", "--seed=1"]);
        }
        if command == "emit-ir" {
            process.arg(format!(
                "--output={}",
                root.0.join("blocked.qirf").display()
            ));
        }
        let output = process.output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        let text = String::from_utf8(output.stdout).unwrap();
        assert!(text.contains("\"code\":\"project\""), "{command}: {text}");
        assert!(!text.contains("\"code\":\"io\"") && !text.contains("\"code\":\"kernel\""));
    }
}

#[test]
fn function_equation_mismatch_has_the_same_contract_code_in_text_and_json() {
    let root = SourceRoot::new(include_str!(
        "fixtures/frontend_v030/ordinary-type-cutover/current/review_v029/contract_mismatch/main.qli"
    ));
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
            text.contains(if json {
                "\"code\":\"contract\""
            } else {
                ": contract:"
            }),
            "{text}"
        );
        assert!(text.contains("function semantic contract"), "{text}");
    }
}

#[test]
fn truncated_static_arguments_emit_one_located_json_parse_error() {
    for source in [
        "unitary fn f(q: Q<Bit>) -> Q<Bit> { g[",
        "unitary fn f(q: Q<Bit>) -> Q<Bit> { g[power(",
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
fn retired_operation_diagnostics_preserve_utf8_crlf_spans_without_native_setup() {
    for (body, token, replacement) in [
        ("adjoint(U,q)", "adjoint", "inverse(U)(q)"),
        ("g[repeat_op(2,U)](q)", "repeat_op", "power(U, k)"),
        ("repeat_static(2,U,q)", "repeat_static", "power(U, k)(q)"),
    ] {
        let source = format!("// 位相\r\nunitary fn f(q:Q<Bit>)->Q<Bit>{{{body}}}");
        let root = SourceRoot::new(&source);
        let kernel = root.0.join("absent");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            // If parsing accidentally probes/spawns the checker, record it.
            root.write(
                "absent",
                "#!/bin/sh\nprintf called > \"$0.called\"\nexit 91\n",
            );
            std::fs::set_permissions(&kernel, std::fs::Permissions::from_mode(0o700)).unwrap();
        }
        let start = source.find(token).unwrap();
        let end = start + token.len();
        let column = source[source.find('\n').unwrap() + 1..start]
            .chars()
            .count()
            + 1;
        for command in ["check", "run"] {
            for json in [false, true] {
                let mut process = Command::new(env!("CARGO_BIN_EXE_qleisli"));
                process
                    .arg(command)
                    .arg(&root.0)
                    .arg(format!("--lean-kernel={}", kernel.display()));
                if json {
                    process.arg("--format=json");
                }
                let output = process.output().unwrap();
                assert_eq!(output.status.code(), Some(1));
                let text =
                    String::from_utf8(if json { output.stdout } else { output.stderr }).unwrap();
                assert!(
                    text.contains("is retired") && text.contains(replacement),
                    "{text}"
                );
                if json {
                    assert!(text.contains("\"code\":\"parse\""), "{text}");
                    assert!(
                        text.contains(&format!(
                            "\"start\":{start},\"end\":{end},\"line\":2,\"column\":{column}"
                        )),
                        "{text}"
                    );
                } else {
                    assert!(
                        text.contains(&format!("main.qli:2:{column}: parse:")),
                        "{text}"
                    );
                }
            }
        }
        assert!(!kernel.with_file_name("absent.called").exists());
    }
}

#[test]
fn json_check_and_run_have_golden_envelopes_in_every_flag_position() {
    let root = SourceRoot::new("observe fn main() -> Bit { 1 }");
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
fn json_command_identity_is_independent_of_leading_options() {
    let root = SourceRoot::new("observe fn main() -> Bit { 1 }");
    for (command, flags, status) in [
        ("check", vec!["--source-bytes=1048576"], 0),
        ("run", vec!["--legacy-source-limits"], 0),
        ("sample", vec!["--shots=2", "--seed=0"], 0),
        ("check", vec!["--project-bytes=1"], 1),
    ] {
        let trailing = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .arg(command)
            .arg(&root.0)
            .args(&flags)
            .arg("--format=json")
            .output()
            .unwrap();
        let leading = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .args(&flags)
            .arg(command)
            .arg(&root.0)
            .arg("--format=json")
            .output()
            .unwrap();
        assert_eq!(trailing.status.code(), Some(status), "{trailing:?}");
        assert_eq!(leading.status.code(), Some(status), "{leading:?}");
        assert!(trailing.stderr.is_empty() && leading.stderr.is_empty());
        assert!(
            String::from_utf8_lossy(&trailing.stdout)
                .contains(&format!("\"command\":\"{command}\"")),
            "{trailing:?}"
        );
        assert_eq!(leading.stdout, trailing.stdout);
    }
}

#[test]
fn json_usage_is_atomic_and_keeps_the_usage_exit_code() {
    // Preserve the historical golden; only the retired command leaves current help.
    let historical = include_str!("fixtures/frontend_v030/basis-polymorphism/current-usage.txt");
    let retired = "  qleisli sized <check|run|sample|emit-proposal> --entry=MODULE::FUNCTION [sized-options]\n";
    assert_eq!(historical.matches(retired).count(), 1);
    let usage = historical
        .replace(retired, "")
        .trim_end()
        .replace('\n', "\\u000a");
    for args in [
        vec!["check", "--format=json"],
        vec!["check", ".", "--format=json", "--format=json"],
        vec!["check", ".", "--unknown", "--format=json"],
        vec!["check", ".", "--format", "--format=json"],
        vec!["check", ".", "--format=xml", "--format=json"],
        vec!["check", "--unknown", "--format=json"],
        vec!["--source-bytes=0", "check", ".", "--format=json"],
        vec!["--unknown", "check", ".", "--format=json"],
        vec!["--format=json", "--shots=01", "check", "."],
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
                "\"message\":\"USAGE\",",
                "\"primary\":null,\"related\":[]}],\"result\":null}\n"
            ).replace("USAGE", &usage)
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
    let root = SourceRoot::new("observe fn main() -> Bit { () }");
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
