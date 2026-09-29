mod common;

use common::SourceRoot;
use std::process::Command;

#[test]
fn doc_reports_truncated_static_arguments_without_panicking() {
    let root = SourceRoot::new("unitary fn f(q: Q<Bit>) -> Q<Bit> { g[");
    let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .arg("doc")
        .arg(root.0.join("main.qli"))
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(
        stderr.contains("expected a static operation description"),
        "{stderr}"
    );
    assert!(!stderr.contains("panicked"), "{stderr}");
}

#[test]
fn check_and_run_accept_source_roots_with_spaces_and_unicode() {
    let root = SourceRoot::new("observe fn main() -> CBit { true }");
    let source_root = root.0.join("source root 日本語");
    std::fs::create_dir(&source_root).unwrap();
    std::fs::rename(root.0.join("main.qli"), source_root.join("main.qli")).unwrap();
    for command in ["check", "run"] {
        let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .arg(command)
            .arg(&source_root)
            .output()
            .unwrap();
        assert!(output.status.success(), "{output:?}");
        let stdout = String::from_utf8(output.stdout).unwrap();
        if command == "check" {
            assert!(stdout.contains(&source_root.display().to_string()));
        } else {
            assert_eq!(stdout, "1: 1.000000000000e0\n");
        }
    }
}

#[cfg(unix)]
#[test]
fn non_utf8_source_root_reports_an_io_error_without_panicking() {
    use std::ffi::OsStr;
    use std::os::unix::ffi::OsStrExt;

    let root = SourceRoot::new("");
    let missing = root.0.join(OsStr::from_bytes(b"missing-\xff"));
    for command in ["check", "run"] {
        let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .arg(command)
            .arg(&missing)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(stderr.contains("missing-"), "{stderr}");
        assert!(!stderr.contains("panicked"), "{stderr}");
    }
}

#[cfg(unix)]
#[test]
fn non_utf8_command_reports_usage_without_panicking() {
    use std::ffi::OsStr;
    use std::os::unix::ffi::OsStrExt;

    let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .arg(OsStr::from_bytes(b"check\xff"))
        .arg(".")
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2), "{output:?}");
    assert_eq!(
        String::from_utf8(output.stderr).unwrap(),
        include_str!("fixtures/review_v020/usage.txt")
    );
}

#[test]
fn doc_reads_one_file_and_does_not_claim_type_checking() {
    let root = SourceRoot::new(
        "//! Example module.\n/// A source-only claim.\npub unitary fn invalid() -> Q<Bit> { missing() }",
    );
    let path = root.0.join("documentation 日本語.qli");
    std::fs::rename(root.0.join("main.qli"), &path).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .arg("doc")
        .arg(&path)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty());
    let markdown = String::from_utf8(output.stdout).unwrap();
    assert!(markdown.contains("Example module."));
    assert!(markdown.contains("invalid (public)"));
    assert!(markdown.contains("no type, ownership or contract verification"));
    let check = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .arg("check")
        .arg(&root.0)
        .output()
        .unwrap();
    assert_eq!(check.status.code(), Some(1));
}

#[test]
fn doc_reports_io_and_comment_errors_without_partial_output() {
    let root = SourceRoot::new("/// orphan");
    for path in [
        root.0.join("main.qli"),
        root.0.join("missing.qli"),
        root.0.clone(),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .arg("doc")
            .arg(path)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(output.stdout.is_empty());
        assert!(!output.stderr.is_empty());
    }
    let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .arg("doc")
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
}

// Linux filesystems permit non-UTF-8 directory names; macOS may reject them.
#[cfg(target_os = "linux")]
#[test]
fn check_and_run_accept_existing_non_utf8_source_roots() {
    use std::ffi::OsStr;
    use std::os::unix::ffi::OsStrExt;

    let root = SourceRoot::new("observe fn main() -> CBit { false }");
    let source_root = root.0.join(OsStr::from_bytes(b"source-\xff"));
    std::fs::create_dir(&source_root).unwrap();
    std::fs::rename(root.0.join("main.qli"), source_root.join("main.qli")).unwrap();
    for command in ["check", "run"] {
        let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .arg(command)
            .arg(&source_root)
            .output()
            .unwrap();
        assert!(output.status.success(), "{output:?}");
        let stdout = String::from_utf8(output.stdout).unwrap();
        if command == "check" {
            assert!(stdout.contains(&source_root.display().to_string()));
        } else {
            assert_eq!(stdout, "0: 1.000000000000e0\n");
        }
    }
}
