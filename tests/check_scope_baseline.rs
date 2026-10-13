//! Preserve the first #363 observations separately from current CLI behavior.

use std::process::Command;

#[test]
fn first_scope_observations_keep_actual_refusals_and_request_free_decisions() {
    let output = Command::new("python3")
        .args(["-B", "scripts/test_native_check_scope_baseline.py"])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("Python 3.11+ is required for the repository validation scripts");
    assert!(
        output.status.success(),
        "baseline integrity check failed:\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
