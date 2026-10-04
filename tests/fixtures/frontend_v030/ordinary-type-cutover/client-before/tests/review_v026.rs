//! Regressions for the published 0.2.5 bug reports. Acceptance and public types
//! remain unchanged; these tests check diagnostics and host configuration.
mod common;
use common::SourceRoot;
use qleisli::frontend::compile::check_project_diagnostic;
use qleisli::frontend::project::{manifest_warnings, qrate_source_root};
use std::{fs, process::Command};

const IMPORTS: &str = "use std::quantum::{init0,cnot,h}; use std::observe::measure_z;\n";

#[test]
fn tuple_diagnostics_do_not_blame_returned_or_destructured_bindings() {
    for body in [
        "unitary fn both(a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){let result=cnot(a,b);result}\nobserve fn main()->CBit{let a=init0();let b=init0();measure_z(h(both(a,b)))}",
        "observe fn main()->CBit{let a=init0();let b=init0();let p=cnot(a,b);let (a,b)=p;measure_z(h((a,b)))}",
        "observe fn main()->CBit{let a=init0();let b=init0();let p=if true{let inner=cnot(a,b);inner}else{cnot(a,b)};let (a,b)=p;measure_z(h((a,b)))}",
    ] {
        let source = format!("{IMPORTS}{body}");
        let root = SourceRoot::new(&source);
        let failure = check_project_diagnostic(&root.0).unwrap_err();
        assert_eq!(failure.code, "type_mismatch");
        assert_eq!(
            failure.primary.as_ref().unwrap().span.start,
            source.rfind("measure_z(h(").unwrap() + "measure_z(".len()
        );
        assert!(!failure.message.contains("at this binding"), "{failure:?}");
        assert!(!failure.message.contains("binding `result`"));
        assert!(!failure.message.contains("binding `p`"));
    }
}

#[test]
fn tuple_binding_messages_have_no_host_path() {
    let root = SourceRoot::new(&format!(
        "{IMPORTS}observe fn main()->CBit{{let a=init0();let b=init0();let p=cnot(a,b);measure_z(p)}}"
    ));
    let failure = check_project_diagnostic(&root.0).unwrap_err();
    assert!(failure.message.contains("binding `p`"));
    assert!(
        !failure.message.contains(&root.0.display().to_string()),
        "{failure:?}"
    );
    let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .arg("check")
        .arg(&root.0)
        .arg("--format=json")
        .output()
        .unwrap();
    let text = String::from_utf8(output.stdout).unwrap();
    assert_eq!(output.status.code(), Some(1));
    assert!(
        !text.contains(&root.0.canonicalize().unwrap().display().to_string()),
        "{text}"
    );
    assert!(text.contains("\"path\":\"main.qli\""));
}

#[test]
fn malformed_optional_manifest_tables_warn_without_rejecting_source() {
    let root = SourceRoot::new("observe fn main()->Unit{()}");
    for (key, value) in [("source", "'src'"), ("tests", "1"), ("docs", "[]")] {
        root.write(
            "Qargo.toml",
            &format!("schema-version=2\n{key}={value}\n[qrate]\nedition='2026'\n"),
        );
        let warnings = manifest_warnings(&root.0).unwrap();
        assert_eq!(warnings.len(), 1, "{key}: {warnings:?}");
        assert_eq!(warnings[0].code, "project");
        assert!(warnings[0].message.contains(key));
        for json in [false, true] {
            let mut cli = Command::new(env!("CARGO_BIN_EXE_qleisli"));
            cli.arg("check").arg(&root.0);
            if json {
                cli.arg("--format=json");
            }
            let output = cli.output().unwrap();
            assert!(output.status.success());
            let text = String::from_utf8(if json { output.stdout } else { output.stderr }).unwrap();
            assert_eq!(
                text.matches(if json {
                    "\"severity\":\"warning\""
                } else {
                    "warning:"
                })
                .count(),
                1,
                "{text}"
            );
        }
    }
}

#[test]
fn qrate_current_directory_spelling_is_consistent() {
    let root = SourceRoot::new("");
    fs::create_dir(root.0.join("src")).unwrap();
    for relative in ["./src", "src/./", "src"] {
        root.write(
            "Qargo.toml",
            &format!("schema-version=2\n[qrate]\nedition='2026'\n[source]\nroot='{relative}'\n"),
        );
        assert_eq!(
            qrate_source_root(&root.0).unwrap(),
            root.0.canonicalize().unwrap().join("src")
        );
    }
    for (relative, message) in [
        ("../x", "parent traversal"),
        ("/abs", "relative"),
        ("", "nonempty"),
        (".", "nonempty"),
    ] {
        root.write(
            "Qargo.toml",
            &format!("schema-version=2\n[qrate]\nedition='2026'\n[source]\nroot='{relative}'\n"),
        );
        assert!(
            qrate_source_root(&root.0)
                .unwrap_err()
                .message
                .contains(message),
            "{relative}"
        );
    }
}

#[test]
fn doc_usage_only_advertises_accepted_options() {
    let root = SourceRoot::new("observe fn main()->Unit{()}");
    let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .arg("doc")
        .arg(root.0.join("main.qli"))
        .arg("--qrate")
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    let usage = String::from_utf8(output.stderr).unwrap();
    let line = usage
        .lines()
        .find(|line| line.contains("qleisli doc"))
        .unwrap();
    assert!(!line.contains("[source-options]"), "{line}");
    assert!(line.contains("--source-bytes=N"), "{line}");
    for options in [
        vec!["--source-bytes=1024", "--project-bytes=2048"],
        vec!["--legacy-source-limits"],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .arg("doc")
            .arg(root.0.join("main.qli"))
            .args(options)
            .output()
            .unwrap();
        assert!(output.status.success());
    }
}
