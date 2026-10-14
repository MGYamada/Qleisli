//! Engineering CLI reports retain their actual bytes and separate claim kind.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use std::process::Command;

fn run(arguments: &[&str]) {
    let output = Command::new("python3")
        .args(["-B", "scripts/test_engineering_pure_cli.py"])
        .args(arguments)
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("Python 3.11+ is required for repository checks");
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn first_native_engineering_client_and_real_diagnostics_are_retained() {
    run(&["--baseline-only"]);
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn engineering_cli_checks_original_artifacts_and_reports_only_the_declared_bound() {
    run(&["--cli", env!("CARGO_BIN_EXE_qleisli")]);
}
