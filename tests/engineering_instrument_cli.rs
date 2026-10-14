//! Complete instrument reports retain original bytes and scoped engineering claims.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use std::process::Command;

#[test]
fn original_instrument_api_cli_sources_and_actual_failures_remain_intact() {
    let output = Command::new("python3")
        .args([
            "-B",
            "scripts/test_engineering_instrument_cli.py",
            "--baseline-only",
        ])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("Python 3.11+ is required for repository validation");
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn instrument_cli_checks_residual_reference_maps_and_reports_only_declared_bounds() {
    let output = Command::new("python3")
        .args([
            "-B",
            "scripts/test_engineering_instrument_cli.py",
            "--cli",
            env!("CARGO_BIN_EXE_qleisli"),
        ])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("Python 3.11+ is required for repository validation");
    assert!(
        output.status.success(),
        "instrument engineering CLI failed:\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
