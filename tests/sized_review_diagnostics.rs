//! Error-only native-process fault injection. The fake process always rejects;
//! it cannot return evidence, checked IR, or an execution handle.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
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
            "use std::state::init0; pub isometry fn f(q:Q<Bit>)->(Q<Bit>,Q<Bit>,Bit){(q,init0(),0)}",
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
        "use std::state::init0; pub isometry fn f(q:Q<Bit>)->(Q<Bit>,Q<Bit>){(q,init0())}",
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
    let mode_file = mode_file.to_str().unwrap();
    root.write(
        "rejecting-kernel",
        &format!(
            r#"#!/usr/bin/env python3
import hashlib
from pathlib import Path
import struct
import sys
data = sys.stdin.buffer.read()
_, version_size, mode_size = struct.unpack_from("<3I", data, 4)
start = 16 + version_size
mode = data[start:start + mode_size].decode("ascii")
Path({mode_file:?}).write_text(mode + "\n")
if mode not in ("--hierarchy-request-pending", "--instrument-pending", "--qpe-instrument-pending"):
    sys.exit(99)
print("qleisli.native-result 4")
print(hashlib.sha256(data).hexdigest())
print("error")
print("{code}")
sys.exit(1)
"#
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
            " pub unitary fn f(q: Q<Bit>) -> Q<Bit> { h(q) }",
            "unitary",
            "composition-request checking",
            "--hierarchy-request-pending",
        ),
        (
            "   pub observe fn f(q: Q<Bit>) -> Bits<1> { prepend_bit[0](measure_z(q),empty_bits()) }",
            "instrument",
            "composition-instrument checking",
            "--instrument-pending",
        ),
    ] {
        for code in ["limit", "contract", "invalid_ir", "format"] {
            let root = SourceRoot::new(source);
            let fake = rejecting_process(&root, code);
            let proposal = ParsedProgram::parse(
                qleisli::edition::Edition::E2026,
                BTreeMap::from([("main".into(), source.into())]),
            )
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
