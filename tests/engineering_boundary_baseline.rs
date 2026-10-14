//! First evidence is immutable history, separate from current acceptance.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use std::process::Command;

#[test]
fn first_instrument_and_exact_pi8_observations_remain_intact() {
    let output = Command::new("python3")
        .args(["-B", "scripts/test_engineering_boundary_baseline.py"])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("Python 3.11+ is required for repository validation");
    assert!(
        output.status.success(),
        "engineering boundary history check failed:\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn selected_pi8_profile_retains_exact_integers_and_explicit_refusals() {
    let output = Command::new("python3")
        .args([
            "-B",
            "scripts/test_engineering_boundary_baseline.py",
            "--pi8-live",
            "--cli",
            env!("CARGO_BIN_EXE_qleisli"),
        ])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("Python 3.11+ is required for repository validation");
    assert!(
        output.status.success(),
        "exact pi/8 selected profile failed:\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
