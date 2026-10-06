//! Bounded CLI checks of atomic Bits interfaces and false Meaning annotations.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use std::process::Command;
mod common;
fn command() -> Command {
    Command::new(env!("CARGO_BIN_EXE_qleisli"))
}

#[test]
fn shared_basis_nat_provider_checks_zero_and_one_bit_registers() {
    let original = include_str!(
        "fixtures/authoring_sessions/meaning-enforcement-v030/bits-attempt-01/spaced.qli"
    );
    for (source, expected_success) in [
        (original.to_owned(), true),
        (original.replace("{phase_eighth(q)}", "{q}"), false),
    ] {
        let files = common::SourceRoot::new(&source);
        for entry in ["zero", "one"] {
            let output = command()
                .args(["check", "--format=json"])
                .arg(format!("--entry=main::{entry}"))
                .arg(format!(
                    "--module=main={}",
                    files.0.join("main.qli").display()
                ))
                .output()
                .unwrap();
            let stdout = String::from_utf8(output.stdout).unwrap();
            assert_eq!(output.status.success(), expected_success, "{stdout}");
            if expected_success {
                assert!(stdout.contains("\"status\":\"checked\""), "{stdout}");
            } else {
                // A well-typed identity provider lies about the scalar phase;
                // it must fail the freshly checked equation, not a type limit.
                assert!(!stdout.contains("\"code\":\"unsupported\""), "{stdout}");
                assert!(stdout.contains("\"code\":\"contract\""), "{stdout}");
                assert!(stdout.contains("must satisfy original Meaning"), "{stdout}");
            }
        }
    }
}
