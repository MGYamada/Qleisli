//! OpenQASM gate reports for ordered composition and phase-sensitive comparisons.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn openqasm_gate_cli_checks_ordered_and_controlled_resource_bounds() {
    let output = std::process::Command::new("python3")
        .args([
            "-B",
            "scripts/test_engineering_openqasm_gate_cli.py",
            env!("CARGO_BIN_EXE_qleisli"),
        ])
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
