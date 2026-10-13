//! Original #47 observations remain separate from current behavior.

use std::process::Command;

#[test]
fn first_requires_sources_and_real_diagnostics_remain_intact() {
    let output = Command::new("python3")
        .args(["-B", "scripts/test_unified_requires_baseline.py"])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("Python 3.11+ is required for repository validation");
    assert!(
        output.status.success(),
        "requires history check failed:\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
