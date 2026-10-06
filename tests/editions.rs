mod common;

use common::SourceRoot;
use qleisli::frontend::{
    CURRENT_EDITION,
    compile::{check_project, check_project_with_policy, compile_project},
    project::{Project, SourcePolicy, read_source_file},
    sized::ParsedProgram,
};
use std::{collections::BTreeMap, fs, process::Command};

const SOURCE: &str = "observe fn main() -> Bit { 1 }";

#[test]
fn empty_files_and_directory_entries_consume_bounded_discovery_capacity() {
    let root = SourceRoot::new("");
    for i in 0..65 {
        root.write(&format!("empty{i}.qli"), "");
    }
    let error = Project::load_with_policy(
        &root.0,
        SourcePolicy::Bounded {
            source_bytes: 1024,
            project_bytes: 3 * 1024,
        },
    )
    .unwrap_err();
    assert_eq!(error.code, "limit");
    assert!(error.message.contains("directory-entry limit"), "{error:?}");
    Project::load_with_policy(&root.0, SourcePolicy::default()).unwrap();
}

#[test]
fn edition_only_manifest_covers_ordinary_sources_and_embedded_stdlib() {
    assert_eq!(CURRENT_EDITION, "2026");
    let root = SourceRoot::new(SOURCE);
    check_project(&root.0).unwrap();
    compile_project(&root.0).unwrap();
    let project = Project::load(&root.0).unwrap();
    assert!(project.module("std::transform").is_some());
    assert!(project.module("std::transforms").is_none());
    assert!(project.module("std::routines").is_none());
    let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .args(["run", root.0.to_str().unwrap(), "--format=json"])
        .output()
        .unwrap();
    assert!(output.status.success(), "{:?}", output);
    assert!(
        String::from_utf8(output.stdout)
            .unwrap()
            .contains("\"bits\":[true]")
    );
}

#[test]
fn full_qrate_manifest_and_toml_string_forms_select_the_same_edition() {
    let root = SourceRoot::new(SOURCE);
    for edition in ["\"2026\"", "'2026'", "\"20\\u00326\""] {
        root.write("Qargo.toml", &format!(
            "schema-version = 2\n[qrate]\nname = 'example'\nversion = '0.1.0'\nedition = {edition} # explicit\n[source]\nroot = 'src'\n[tests]\nroot = 'tests'\n[docs]\nroot = 'docs'\n"
        ));
        check_project(&root.0).unwrap();
    }
}

#[test]
fn missing_manifest_has_no_default_and_all_filesystem_loaders_check_it() {
    let root = SourceRoot::new(SOURCE);
    fs::remove_file(root.0.join("Qargo.toml")).unwrap();
    assert!(
        check_project(&root.0)
            .unwrap_err()
            .message
            .contains("missing Qargo.toml")
    );
    assert!(read_source_file(&root.0.join("main.qli"), SourcePolicy::Legacy).is_err());
    assert!(
        ParsedProgram::load(BTreeMap::from([("main".into(), root.0.join("main.qli"))])).is_err()
    );
    let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .args(["check", root.0.to_str().unwrap(), "--format=json"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    assert!(
        String::from_utf8(output.stdout)
            .unwrap()
            .contains("missing Qargo.toml")
    );
}

#[test]
fn malformed_numeric_missing_and_unsupported_editions_are_rejected_before_source() {
    let root = SourceRoot::new("@");
    for (manifest, expected) in [
        (
            "schema-version = 1\n[qrate]\nedition = '2026'",
            "schema-version = 2",
        ),
        ("[qrate]\nedition = '2026'", "schema-version = 2"),
        ("schema-version = 2\n[qrate]", "explicit string"),
        (
            "schema-version = 2\n[qrate]\nedition = 2026",
            "explicit string",
        ),
        (
            "schema-version = 2\n[qrate]\nedition = true",
            "explicit string",
        ),
        (
            "schema-version = 2\n[qrate]\nedition = ['2026']",
            "explicit string",
        ),
        (
            "schema-version = 2\n[qrate]\nedition = '2027'",
            "unsupported Qleisli edition",
        ),
        (
            "schema-version = 2\n[qrate]\nedition = '2026'\nedition = '2026'",
            "invalid Qargo.toml",
        ),
        ("schema-version = 2\nedition = '2026'", "explicit string"),
    ] {
        root.write("Qargo.toml", manifest);
        let diagnostic = check_project_with_policy(&root.0, SourcePolicy::default()).unwrap_err();
        assert_eq!(diagnostic.code, "project");
        assert!(
            diagnostic.message.contains(expected),
            "{}",
            diagnostic.message
        );
        assert!(diagnostic.primary.unwrap().path.ends_with("Qargo.toml"));
    }
}

#[test]
fn closest_manifest_wins_without_changing_import_roots_or_skipping_invalid_files() {
    let root = SourceRoot::new("");
    fs::create_dir(root.0.join("src")).unwrap();
    root.write("src/main.qli", SOURCE);
    // Parent manifest selects edition; the caller still selects the module root.
    compile_project(&root.0.join("src")).unwrap();
    root.write(
        "src/Qargo.toml",
        "schema-version = 2\n[qrate]\nedition = '2027'",
    );
    assert!(
        check_project(&root.0)
            .unwrap_err()
            .message
            .contains("unsupported Qleisli edition")
    );
    assert!(read_source_file(&root.0.join("src/main.qli"), SourcePolicy::Legacy).is_err());
    root.write("src/Qargo.toml", include_str!("Qargo.toml"));
    root.write("Qargo.toml", "invalid");
    compile_project(&root.0.join("src")).unwrap();
}

#[test]
fn qlt_drafts_require_an_edition_without_claiming_execution_support() {
    let root = SourceRoot::new(SOURCE);
    fs::create_dir(root.0.join("drafts")).unwrap();
    root.write("drafts/example.qlt", "QLT remains a draft");
    check_project(&root.0).unwrap();
    root.write(
        "drafts/Qargo.toml",
        "schema-version = 2\n[qrate]\nedition = '2030'",
    );
    assert!(
        check_project(&root.0)
            .unwrap_err()
            .message
            .contains("unsupported Qleisli edition")
    );
}

#[test]
fn sized_and_documentation_files_use_their_enclosing_manifest() {
    let root = SourceRoot::new("pub unitary fn id(q: Q<Bit>) -> Q<Bit> { q }");
    let files = BTreeMap::from([("main".into(), root.0.join("main.qli"))]);
    ParsedProgram::load(files.clone()).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .arg("doc")
        .arg(root.0.join("main.qli"))
        .output()
        .unwrap();
    assert!(output.status.success());
    root.write(
        "Qargo.toml",
        "schema-version = 2\n[qrate]\nedition = '2027'",
    );
    assert!(ParsedProgram::load(files).is_err());
    let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .arg("doc")
        .arg(root.0.join("main.qli"))
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
}

#[test]
fn manifest_bytes_are_bounded_and_decoded_independently_of_source_policy() {
    let root = SourceRoot::new(SOURCE);
    root.write(
        "Qargo.toml",
        &format!("{}#{}", include_str!("Qargo.toml"), "x".repeat(65_536)),
    );
    assert!(
        check_project(&root.0)
            .unwrap_err()
            .message
            .contains("65536-byte manifest limit")
    );
    fs::write(root.0.join("Qargo.toml"), [0xff]).unwrap();
    assert!(
        check_project(&root.0)
            .unwrap_err()
            .message
            .contains("not valid UTF-8")
    );
    root.write("Qargo.toml", include_str!("Qargo.toml"));
    check_project(&root.0).unwrap();
}

#[cfg(unix)]
#[test]
fn manifest_symlinks_and_non_files_cannot_fall_back_to_an_ancestor() {
    use std::os::unix::fs::symlink;
    let root = SourceRoot::new(SOURCE);
    fs::create_dir(root.0.join("src")).unwrap();
    root.write("src/main.qli", SOURCE);
    symlink(root.0.join("Qargo.toml"), root.0.join("src/Qargo.toml")).unwrap();
    let error = compile_project(&root.0.join("src")).unwrap_err();
    assert!(
        error
            .message
            .contains("Qargo.toml must be a regular, non-symlink file"),
        "{error:?}"
    );
    fs::remove_file(root.0.join("src/Qargo.toml")).unwrap();
    symlink(root.0.join("missing.toml"), root.0.join("src/Qargo.toml")).unwrap();
    let error = compile_project(&root.0.join("src")).unwrap_err();
    assert!(
        error
            .message
            .contains("Qargo.toml must be a regular, non-symlink file"),
        "{error:?}"
    );
    fs::remove_file(root.0.join("src/Qargo.toml")).unwrap();
}

#[test]
fn non_file_manifest_is_rejected_before_platform_open() {
    let root = SourceRoot::new(SOURCE);
    fs::create_dir(root.0.join("src")).unwrap();
    root.write("src/main.qli", SOURCE);
    fs::create_dir(root.0.join("src/Qargo.toml")).unwrap();
    let error = compile_project(&root.0.join("src")).unwrap_err();
    assert!(
        error
            .message
            .contains("Qargo.toml must be a regular, non-symlink file"),
        "{error:?}"
    );
}
