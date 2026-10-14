//! Canonical actual target-byte comparisons retain explicit engineering scope.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use std::process::Command;

fn run(arguments: &[&str]) {
    let output = Command::new("python3")
        .args(["-B", "scripts/test_engineering_openqasm_cli.py"])
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
fn first_target_sources_and_actual_export_diagnostics_are_retained() {
    run(&["--baseline-only"]);
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn openqasm_cli_checks_literal_target_and_original_ideal_with_honest_scope() {
    run(&["--cli", env!("CARGO_BIN_EXE_qleisli")]);
}
