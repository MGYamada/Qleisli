//! Error-only native-process fault injection. The fake process always rejects;
//! it cannot return evidence, checked IR, or an execution handle.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
mod common;

use common::SourceRoot;
#[cfg(unix)]
use qleisli::frontend::compile::ParsedProgram;
#[cfg(unix)]
use std::collections::BTreeMap;
use std::process::Command;

fn cli(root: &SourceRoot) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
    command.args(["check", "--entry=main::f"]).arg(format!(
        "--module=main={}",
        root.0.join("main.qli").display()
    ));
    command
}

#[test]
fn sized_cli_reports_unsupported_lowering_before_starting_a_kernel() {
    for (source, reason) in [
        (
            "use std::quantum::init0; pub isometry fn f(q:Q<Bit>)->(Q<Bit>,Q<Bit>,Bit){(q,init0(),0)}",
            "at most one ordinary Bits<0> result",
        ),
        (
            "pub unitary fn f(q: Q<Bit>, c: Bit) -> (Q<Bit>,Bit) { (q,c) }",
            "classical entry",
        ),
    ] {
        let root = SourceRoot::new(source);
        let output = cli(&root)
            .arg("--ir-profile=hierarchy")
            .arg(format!(
                "--kernel={}",
                root.0.join("absent-kernel").display()
            ))
            .output()
            .unwrap();
        let message = String::from_utf8(output.stderr).unwrap();
        assert_eq!(output.status.code(), Some(1));
        assert!(output.stdout.is_empty());
        assert!(message.contains("unsupported"), "{message}");
        assert!(message.contains("lowering"), "{message}");
        assert!(message.contains(reason), "{message}");
        assert!(!message.contains("cannot start Lean"), "{message}");
    }
    // The original preparation example is now eligible. Its missing checker
    // must still reject instead of bypassing the native acceptance boundary.
    let root = SourceRoot::new(
        "use std::quantum::init0; pub isometry fn f(q:Q<Bit>)->(Q<Bit>,Q<Bit>){(q,init0())}",
    );
    let output = cli(&root)
        .arg("--ir-profile=hierarchy")
        .arg(format!(
            "--kernel={}",
            root.0.join("absent-kernel").display()
        ))
        .output()
        .unwrap();
    let message = String::from_utf8(output.stderr).unwrap();
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert!(message.starts_with("io:"), "{message}");
    assert!(
        message.contains("cannot start Lean native checker"),
        "{message}"
    );
    assert!(message.contains("sized isometry profile"), "{message}");
}

#[cfg(unix)]
fn rejecting_process(root: &SourceRoot, code: &str) -> std::path::PathBuf {
    use std::os::unix::fs::PermissionsExt;
    assert!(matches!(
        code,
        "limit" | "contract" | "invalid_ir" | "format"
    ));
    let mode_file = root.0.join("invoked-mode");
    let mode_file = mode_file.to_str().unwrap().replace('\'', "'\\''");
    root.write(
        "rejecting-kernel",
        &format!(
            "#!/bin/sh\nprintf '%s\\n' \"$1\" > '{mode_file}'\n/bin/cat > /dev/null\ncase \"$1\" in\n  --hierarchy-request-pending) header='qleisli.hierarchy-request-pending 3' ;;\n  --instrument-pending) header='qleisli.instrument-pending 3' ;;\n  --qpe-instrument-pending) header='qleisli.qpe-instrument-pending 3' ;;\n  *) exit 99 ;;\nesac\nprintf '%s\\n' \"$header\" error {code}\nexit 1\n"
        ),
    );
    let path = root.0.join("rejecting-kernel");
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700)).unwrap();
    path
}

#[cfg(unix)]
fn assert_rejection(
    output: std::process::Output,
    code: &str,
    mode: &str,
    profile: &str,
    scope: &str,
) {
    assert_eq!(output.status.code(), Some(1));
    assert!(
        output.stdout.is_empty(),
        "a native rejection must produce no checked result"
    );
    let message = String::from_utf8(output.stderr).unwrap();
    assert!(message.starts_with(&format!("{code}:")), "{message}");
    assert!(message.contains(mode), "{message}");
    assert!(
        message.contains(&format!("sized {profile} profile, {scope} contract")),
        "{message}"
    );
    if code == "limit" {
        assert!(
            message.contains("aggregate structural-work allowance is 2000000"),
            "{message}"
        );
        assert!(
            message.contains("required work is unavailable in the native failure reply"),
            "{message}"
        );
    } else {
        assert!(!message.contains("structural-work allowance"), "{message}");
    }
}

#[test]
#[cfg(unix)]
fn native_failure_diagnostics_preserve_codes_profile_and_producer_or_caller_scope() {
    for (source, profile, mode, argument) in [
        (
            "use std::quantum::h; pub unitary fn f(q: Q<Bit>) -> Q<Bit> { h(q) }",
            "unitary",
            "composition-request checking",
            "--hierarchy-request-pending",
        ),
        (
            "use std::observe::measure_z; use std::classical::empty_bits; use std::classical::prepend_bit; pub observe fn f(q: Q<Bit>) -> Bits<1> { prepend_bit[0](measure_z(q),empty_bits()) }",
            "instrument",
            "composition-instrument checking",
            "--instrument-pending",
        ),
    ] {
        for code in ["limit", "contract", "invalid_ir", "format"] {
            let root = SourceRoot::new(source);
            let fake = rejecting_process(&root, code);
            let proposal = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())]))
                .unwrap()
                .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
                .unwrap()
                .elaborate()
                .unwrap()
                .lower()
                .unwrap();
            std::fs::write(
                root.0.join("caller-request.json"),
                proposal.comparison_request(),
            )
            .unwrap();
            for caller in [false, true] {
                let mut command = cli(&root);
                command.arg(format!("--kernel={}", fake.display()));
                if caller {
                    command.arg(format!(
                        "--request={}",
                        root.0.join("caller-request.json").display()
                    ));
                }
                assert_rejection(
                    command.output().unwrap(),
                    code,
                    mode,
                    profile,
                    if caller {
                        "caller-composition"
                    } else {
                        "producer-consistency"
                    },
                );
                assert_eq!(
                    std::fs::read_to_string(root.0.join("invoked-mode"))
                        .unwrap()
                        .trim(),
                    argument
                );
            }
        }
    }
}
