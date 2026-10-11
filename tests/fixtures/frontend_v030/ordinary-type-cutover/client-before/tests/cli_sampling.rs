mod common;
use common::SourceRoot;
use std::process::Command;

#[test]
fn seeded_samples_have_atomic_human_and_json_outputs() {
    let root = SourceRoot::new(
        "use std::quantum::init0; use std::observe::measure_z; observe fn main() -> CBit { measure_z(init0()) }",
    );
    for json in [false, true] {
        let mut c = Command::new(env!("CARGO_BIN_EXE_qleisli"));
        c.arg("sample")
            .arg("--seed=18446744073709551615")
            .arg(&root.0)
            .arg("--shots=2");
        if json {
            c.arg("--format=json");
        }
        let output = c.output().unwrap();
        assert!(output.status.success(), "{output:?}");
        assert!(output.stderr.is_empty());
        let s = String::from_utf8(output.stdout).unwrap();
        if json {
            assert!(s.contains("\"seed\":\"18446744073709551615\""), "{s}");
            // Init0, MeasureZ and the projection's axis metadata copy each cost one step.
            assert!(s.contains("\"shots\":[{\"bits\":[false],\"execution_steps\":3},{\"bits\":[false],\"execution_steps\":3}],\"execution_steps\":6"),"{s}");
        } else {
            assert_eq!(s, "0\n0\n");
        }
    }
}

#[test]
fn invalid_flags_and_failed_sampling_never_emit_shots() {
    let root = SourceRoot::new("observe fn main() -> CBit { true }");
    for args in [
        vec!["--shots=0", "--seed=0"],
        vec!["--shots=01", "--seed=0"],
        vec!["--shots=1", "--seed=-1"],
        vec!["--shots=1"],
        vec!["--shots=1", "--seed=0", "--seed=1"],
        vec![
            "--shots=1",
            "--seed=0",
            "--legacy-source-limits",
            "--source-bytes=1",
        ],
    ] {
        let o = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .arg("sample")
            .arg(&root.0)
            .args(args)
            .arg("--format=json")
            .output()
            .unwrap();
        assert_eq!(o.status.code(), Some(2), "{o:?}");
        let s = String::from_utf8(o.stdout).unwrap();
        assert!(s.contains("\"result\":null"));
        assert!(!s.contains("\"shots\":"));
    }
    let o = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .arg("sample")
        .arg(&root.0)
        .args(["--shots=1", "--seed=0", "--source-bytes=1", "--format=json"])
        .output()
        .unwrap();
    assert_eq!(o.status.code(), Some(1));
    let s = String::from_utf8(o.stdout).unwrap();
    assert!(s.contains("\"code\":\"limit\""));
    assert!(s.contains("\"primary\":{\"path\":\"main.qli\""));
    assert!(s.contains("\"result\":null"));
}

#[test]
fn cli_new_default_has_an_explicit_legacy_escape() {
    let root = SourceRoot::new(&format!(
        "observe fn main() -> CBit {{ false }}\n//{}",
        "x".repeat(1 << 20)
    ));
    for legacy in [false, true] {
        let mut c = Command::new(env!("CARGO_BIN_EXE_qleisli"));
        c.arg("check").arg(&root.0).arg("--format=json");
        if legacy {
            c.arg("--legacy-source-limits");
        }
        let output = c.output().unwrap();
        assert_eq!(output.status.success(), legacy, "{output:?}");
    }
}
