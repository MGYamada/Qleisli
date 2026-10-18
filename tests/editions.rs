mod common;

use common::SourceRoot;
use qleisli::frontend::{
    compile::ParsedProgram,
    compile::{check_project, check_project_with_policy, compile_project},
    project::{ModuleOrigin, Project, SourcePolicy, bundled_std, read_source_file},
};
use std::{collections::BTreeMap, fs, process::Command};

const SOURCE: &str = "observe fn main() -> Bit { 1 }";

#[test]
fn qrate_selection_retains_its_exact_manifest_without_reselecting_later_edits() {
    use qleisli::edition::Edition;
    use qleisli::frontend::project::QrateSource;
    let root = SourceRoot::new("");
    let original =
        "# selected bytes\nschema-version=2\n[qrate]\nedition='2026'\n[source]\nroot='src'\n";
    root.write("Qargo.toml", original);
    fs::create_dir(root.0.join("src")).unwrap();
    root.write("src/main.qli", SOURCE);
    let selected = QrateSource::select(&root.0).unwrap();
    assert_eq!(selected.manifest().source(), original);
    assert_eq!(selected.manifest().edition(), Edition::E2026);
    root.write(
        "Qargo.toml",
        "schema-version=2\n[qrate]\nedition='2027'\n[source]\nroot='other'\n",
    );
    let loaded = selected.load_with_policy(SourcePolicy::default()).unwrap();
    assert_eq!(loaded.edition(), Edition::E2026);
    let manifest = loaded.module_manifest("main").unwrap();
    assert_eq!(manifest.source(), original);
    assert_eq!(manifest.path(), selected.manifest().path());
    assert_eq!(loaded.module("main").unwrap().source, SOURCE);
    assert!(QrateSource::select(&root.0).is_err());
}

#[test]
fn nested_sources_keep_their_own_original_manifest_association() {
    use qleisli::edition::Edition;
    let root = SourceRoot::new(SOURCE);
    let nested = "# independent nested bytes\nschema-version=2\n[qrate]\nedition='2026'\n";
    fs::create_dir(root.0.join("nested")).unwrap();
    root.write("nested/Qargo.toml", nested);
    root.write(
        "nested/leaf.qli",
        "pub unitary fn leaf(q:Q<Bit>)->Q<Bit>{q}",
    );
    root.write("nested/test.qlt", "");
    let loaded = Project::load_with_policy(&root.0, SourcePolicy::default()).unwrap();
    assert_eq!(loaded.edition(), Edition::E2026);
    assert_eq!(
        loaded.module_manifest("nested::leaf").unwrap().source(),
        nested
    );
    assert_ne!(
        loaded.module_manifest("main").unwrap().path(),
        loaded.module_manifest("nested::leaf").unwrap().path()
    );
    root.write(
        "nested/Qargo.toml",
        "schema-version=2\n[qrate]\nedition='2027'\n",
    );
    assert_eq!(
        loaded.module_manifest("nested::leaf").unwrap().source(),
        nested
    );
    assert!(Project::load_with_policy(&root.0, SourcePolicy::default()).is_err());
}

#[test]
fn explicit_in_memory_project_has_no_fabricated_file_manifest() {
    use qleisli::edition::Edition;
    let root = SourceRoot::new(SOURCE);
    let loaded = Project::load_with_policy(&root.0, SourcePolicy::default()).unwrap();
    let project = Project::from_modules(loaded.root, loaded.modules, Edition::E2026);
    assert_eq!(project.edition(), Edition::E2026);
    assert!(project.module_manifest("main").is_none());
    assert!(project.module_manifest("std::gate").is_none());
}

#[test]
fn retained_manifest_bytes_share_the_existing_aggregate_capacity_once() {
    let root = SourceRoot::new(SOURCE);
    let nested = "# retained configuration\nschema-version=2\n[qrate]\nedition='2026'\n";
    fs::create_dir(root.0.join("nested")).unwrap();
    root.write("nested/Qargo.toml", nested);
    let leaf = "pub unitary fn leaf(q:Q<Bit>)->Q<Bit>{q}";
    for number in 0..4 {
        root.write(&format!("nested/leaf{number}.qli"), leaf);
    }
    let bytes = fs::read(root.0.join("Qargo.toml")).unwrap().len()
        + nested.len()
        + SOURCE.len()
        + 4 * leaf.len()
        + bundled_std()
            .unwrap()
            .modules()
            .map(|(_, text)| text.len())
            .sum::<usize>();
    let policy = |project_bytes| SourcePolicy::Bounded {
        source_bytes: 1 << 20,
        project_bytes,
    };
    Project::load_with_policy(&root.0, policy(bytes as u64)).unwrap();
    let failure = Project::load_with_policy(&root.0, policy(bytes as u64 - 1)).unwrap_err();
    assert_eq!(failure.code, "limit");
    Project::load_with_policy(&root.0, SourcePolicy::Legacy).unwrap();
}

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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn edition_only_manifest_covers_ordinary_sources_and_embedded_stdlib() {
    assert_eq!(qleisli::edition::Edition::E2026.as_str(), "2026");
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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

#[test]
fn bundled_std_descriptor_binds_manifest_and_complete_loaded_source_inventory() {
    let bundle = bundled_std().unwrap();
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let manifest = fs::read_to_string(repository.join("stdlib/Qargo.toml")).unwrap();
    assert_eq!(bundle.manifest().as_bytes(), manifest.as_bytes());
    let manifest: toml::Table = manifest.parse().unwrap();
    let qrate = manifest["qrate"].as_table().unwrap();
    assert_eq!(bundle.name(), qrate["name"].as_str().unwrap());
    assert_eq!(bundle.version(), qrate["version"].as_str().unwrap());
    assert_eq!(bundle.edition(), qrate["edition"].as_str().unwrap());
    assert_eq!(bundle.product_version(), env!("CARGO_PKG_VERSION"));
    assert_eq!(bundle.version(), bundle.product_version());
    assert_eq!(bundle.edition(), qleisli::edition::Edition::E2026.as_str());

    let mut expected = BTreeMap::new();
    for entry in fs::read_dir(repository.join("stdlib/src")).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().is_some_and(|extension| extension == "qli") {
            assert!(entry.file_type().unwrap().is_file());
            let name = format!("std::{}", path.file_stem().unwrap().to_str().unwrap());
            assert!(
                expected
                    .insert(name, fs::read_to_string(path).unwrap())
                    .is_none()
            );
        }
    }
    assert!(!expected.is_empty());
    let mut actual = BTreeMap::new();
    let modules = bundle.modules();
    let count = modules.len();
    for (name, source) in modules {
        assert!(actual.insert(name.to_owned(), source.to_owned()).is_none());
    }
    assert_eq!(count, expected.len());
    assert_eq!(actual, expected);

    let source = SourceRoot::new("");
    let loaded = Project::load(&source.0).unwrap();
    let loaded: BTreeMap<_, _> = loaded
        .modules
        .values()
        .filter(|module| module.origin == ModuleOrigin::Bundled)
        .map(|module| (module.name.clone(), module.source.clone()))
        .collect();
    assert_eq!(actual, loaded);
}

#[test]
fn bundled_std_descriptor_keeps_external_manifest_checks_fresh() {
    let bundle = bundled_std().unwrap();
    let root = SourceRoot::new(SOURCE);
    let original = fs::read_to_string(root.0.join("Qargo.toml")).unwrap();
    Project::load(&root.0).unwrap();
    for _ in 0..2 {
        root.write(
            "Qargo.toml",
            "schema-version = 2\n[qrate]\nedition = \"2027\"\n",
        );
        bundled_std().unwrap();
        let rejected = Project::load(&root.0).unwrap_err();
        assert!(rejected.message.contains("unsupported Qleisli edition"));
        assert_eq!(
            rejected.path,
            root.0.canonicalize().unwrap().join("Qargo.toml")
        );
        root.write("Qargo.toml", &original);
        Project::load(&root.0).unwrap();
    }
    assert_eq!(bundle.manifest(), bundled_std().unwrap().manifest());
}
