//! Tensor CLI results retain originals and distinguish composition from a
//! whole-parent Frobenius check, without promoting engineering evidence.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use std::process::Command;

fn run(arguments: &[&str]) {
    let output = Command::new("python3")
        .args(["-B", "scripts/test_engineering_pure_tensor_cli.py"])
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
fn original_tensor_sources_and_real_authoring_diagnostics_are_retained() {
    run(&["--baseline-only"]);
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn tensor_cli_checks_six_originals_and_reports_additive_component_scope() {
    run(&["--cli", env!("CARGO_BIN_EXE_qleisli")]);
}
