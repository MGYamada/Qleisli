//! Preserve first observations separately from approximation implementation.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use std::process::Command;

#[test]
fn first_exact_approx_sources_and_observations_remain_intact() {
    let output = Command::new("python3")
        .args(["-B", "scripts/test_exact_approx_baseline.py"])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("Python 3.11+ is required for repository validation");
    assert!(
        output.status.success(),
        "exact/approximate history check failed:\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
