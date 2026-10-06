//! Compatible repairs from the 0.2.4 review; independent target probes live in
//! scripts/test_review_v024.py. No source/IR validity rule is relaxed here.
mod common;
use common::SourceRoot;
use qleisli::frontend::compile::{check_project, check_project_diagnostic, compile_project};
use qleisli::frontend::project::{Project, manifest_warnings, qrate_source_root};
use qleisli::interop::{export_openqasm3, export_qir_base};
use std::{fs, process::Command};

#[test]
fn misplaced_public_import_has_a_checked_repair() {
    let source = "use std::routines::qft2; unitary fn run(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{qft2(q)}";
    let root = SourceRoot::new(source);
    let failure = check_project_diagnostic(&root.0).unwrap_err();
    assert!(
        failure.message.contains("use std::transforms::qft2;"),
        "{failure:?}"
    );
    root.write("main.qli", &source.replace("routines", "transforms"));
    check_project(&root.0).unwrap();
    root.write("main.qli", "use std::quantum::measure_z;");
    assert!(
        check_project_diagnostic(&root.0)
            .unwrap_err()
            .message
            .contains("use std::observe::measure_z;")
    );
    root.write("main.qli", "use std::transforms::private_helper;");
    assert!(
        !check_project_diagnostic(&root.0)
            .unwrap_err()
            .message
            .contains("public alternatives")
    );
}

#[test]
fn nested_register_pattern_names_the_actual_type_and_repairs() {
    let source = "use std::quantum::split; use std::quantum::join;
        unitary fn run(q:Q<((Bit,Bit),Bit)>)->Q<((Bit,Bit),Bit)>{ let ((a,b),c)=split(q); join(join(a,b),c) }";
    let root = SourceRoot::new(source);
    let failure = check_project_diagnostic(&root.0).unwrap_err();
    assert!(
        failure.message.contains("found `Q<(Bit,Bit)>`"),
        "{failure:?}"
    );
    assert!(
        failure
            .message
            .contains("split any nested register separately")
    );
    root.write(
        "main.qli",
        &source.replace(
            "let ((a,b),c)=split(q);",
            "let (ab,c)=split(q); let (a,b)=split(ab);",
        ),
    );
    check_project(&root.0).unwrap();
    for basis in ["Bit", "Bits<1>", "Unit", "(Bit,Bit,Bit)"] {
        let invalid = format!("unitary fn run(q:Q<{basis}>)->Q<{basis}>{{let(a,b)=q;q}}");
        root.write("main.qli", &invalid);
        let failure = check_project_diagnostic(&root.0).unwrap_err();
        assert_eq!(failure.code, "type_mismatch", "{failure:?}");
        assert!(failure.message.contains(&format!("found `Q<{basis}>`")));
        assert!(!failure.message.contains("call `split`"), "{failure:?}");
    }
}

#[test]
fn tuple_misuse_locates_its_binding_without_rejecting_valid_named_tuples() {
    let source = "use std::quantum::{init0,cnot}; use std::observe::measure_z;
        observe fn main()->(Bit,Bit){let a=init0();let b=init0();let b=cnot(a,b); (measure_z(b),measure_z(a))}";
    let root = SourceRoot::new(source);
    let failure = check_project_diagnostic(&root.0).unwrap_err();
    let start = source.find("let b=cnot").unwrap() + 4;
    assert_eq!(failure.primary.unwrap().span.start, start);
    assert!(
        failure.message.contains("found `(Q<Bit>,Q<Bit>)`"),
        "{}",
        failure.message
    );
    assert!(failure.message.contains("let (a, b) = cnot(a, b);"));
    root.write(
        "main.qli",
        &source.replace("let b=cnot(a,b);", "let (a,b)=cnot(a,b);"),
    );
    check_project(&root.0).unwrap();
    root.write("main.qli","use std::quantum::cnot; unitary fn run(a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){let result=cnot(a,b);result}");
    check_project(&root.0).unwrap();
}

const QRATE: &str = "schema-version=2\n[qrate]\nname='demo'\nversion='0.1.0'\nedition='2026'\n[source]\nroot='src'\n[tests]\nroot='tests'\n[docs]\nroot='docs'\n";

#[test]
fn declared_source_selection_excludes_build_outputs_and_preserves_legacy_loading() {
    let root = SourceRoot::new("this is an unrelated scratch source");
    root.write("Qargo.toml", QRATE);
    fs::create_dir(root.0.join("src")).unwrap();
    fs::write(root.0.join("src/main.qli"), "observe fn main()->Unit{()}").unwrap();
    fs::create_dir(root.0.join("target")).unwrap();
    fs::write(root.0.join("target/junk.qli"), "not a program").unwrap();
    #[cfg(unix)]
    std::os::unix::fs::symlink("missing", root.0.join("unrelated-link")).unwrap();
    assert!(Project::load(&root.0).is_err());
    let selected = qrate_source_root(&root.0).unwrap();
    assert_eq!(selected, root.0.canonicalize().unwrap().join("src"));
    assert!(Project::load(&selected).unwrap().module("main").is_some());
    for command in ["check", "run"] {
        for json in [false, true] {
            let mut cli = Command::new(env!("CARGO_BIN_EXE_qleisli"));
            cli.args([command]).arg(&root.0).arg("--qrate");
            if json {
                cli.arg("--format=json");
            }
            let output = cli.output().unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
    }
    // A malformed selected source still rejects, whether imported or not.
    fs::write(root.0.join("src/junk.qli"), "not a program").unwrap();
    assert!(Project::load(&selected).is_err());
}

#[test]
fn selected_roots_reject_escape_build_directory_and_source_symlinks() {
    let root = SourceRoot::new("observe fn main()->Unit{()}");
    fs::create_dir(root.0.join("src")).unwrap();
    for relative in [
        "../escape",
        "/tmp",
        "target",
        "TARGET",
        "Target",
        "src/TaRgEt",
        "",
    ] {
        root.write(
            "Qargo.toml",
            &QRATE.replace("root='src'", &format!("root='{relative}'")),
        );
        let error = qrate_source_root(&root.0).unwrap_err();
        if relative
            .split('/')
            .any(|part| part.eq_ignore_ascii_case("target"))
        {
            assert!(
                error.message.contains("target build directory"),
                "{relative}: {error:?}"
            );
        }
    }
    #[cfg(unix)]
    {
        fs::create_dir(root.0.join("real")).unwrap();
        fs::remove_dir(root.0.join("src")).unwrap();
        std::os::unix::fs::symlink("real", root.0.join("src")).unwrap();
        root.write("Qargo.toml", QRATE);
        assert!(qrate_source_root(&root.0).is_err());
    }
}

#[test]
fn unknown_manifest_metadata_warns_in_text_and_json_without_changing_acceptance() {
    let root = SourceRoot::new("observe fn main()->Unit{()}");
    assert!(manifest_warnings(&root.0).unwrap().is_empty());
    root.write(
        "Qargo.toml",
        "schema-version=2\n[qrate]\nedition='2026'\nunknown_key=1\n",
    );
    check_project(&root.0).unwrap();
    let warnings = manifest_warnings(&root.0).unwrap();
    assert_eq!(warnings.len(), 1);
    assert_eq!(warnings[0].code, "project");
    assert!(warnings[0].message.contains("qrate.unknown_key"));
    for json in [false, true] {
        let mut cli = Command::new(env!("CARGO_BIN_EXE_qleisli"));
        cli.arg("check").arg(&root.0);
        if json {
            cli.arg("--format=json");
        }
        let output = cli.output().unwrap();
        assert!(output.status.success());
        let text = String::from_utf8(if json { output.stdout } else { output.stderr }).unwrap();
        assert!(text.contains("qrate.unknown_key"));
        assert!(text.contains(if json {
            "\"severity\":\"warning\""
        } else {
            "warning:"
        }));
        if json {
            assert!(text.contains("\"outcome\":\"ok\""));
        }
    }
    root.write("Qargo.toml", QRATE);
    assert!(manifest_warnings(&root.0).unwrap().is_empty());
    fs::create_dir(root.0.join("src")).unwrap();
    fs::write(root.0.join("src/main.qli"), "observe fn main()->Unit{()}").unwrap();
    root.write("Qargo.toml", &format!("{QRATE}\nunknown_key=1\n"));
    let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .arg("check")
        .arg(&root.0)
        .args(["--qrate", "--format=json"])
        .output()
        .unwrap();
    assert!(output.status.success());
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("\"code\":\"project\""), "{text}");
    assert!(
        text.contains("\"primary\":{\"path\":\"../Qargo.toml\""),
        "{text}"
    );
    assert!(!text.contains(&root.0.display().to_string()), "{text}");
}

#[test]
fn phase_aliases_export_as_short_exact_target_words() {
    for (name, target) in [("s", "s"), ("sdg", "sdg"), ("tdg", "tdg")] {
        let root = SourceRoot::new(&format!(
            "use std::quantum::{{init0,h,{name}}}; use std::observe::measure_z; observe fn main()->Bit{{measure_z(h({name}(h(init0()))))}}"
        ));
        let program = compile_project(&root.0).unwrap();
        let qasm = export_openqasm3(&program).unwrap();
        assert_eq!(
            qasm.lines()
                .filter(|line| line.starts_with(&format!("{target} q[")))
                .count(),
            1,
            "{qasm}"
        );
        assert_eq!(
            qasm.lines().filter(|line| line.starts_with("t q[")).count(),
            0,
            "{qasm}"
        );
        assert!(export_qir_base(&program).is_ok());
    }
}

#[test]
fn user_compositions_have_a_source_level_contract_check_before_qlt() {
    let source = "use std::quantum::h;
        unitary fn provider(q:Q<Bit>)->Q<Bit>{h(h(q))}
        unitary fn expected(q:Q<Bit>)->Q<Bit>{q}
        unitary fn client(q:Q<Bit>)->Q<Bit>{apply_contract(provider,expected,q)}";
    let root = SourceRoot::new(source);
    check_project(&root.0).unwrap();
    root.write("main.qli", &source.replace("h(h(q))", "h(q)"));
    let error = check_project_diagnostic(&root.0).unwrap_err();
    assert_eq!(error.code, "contract", "{error:?}");
    root.write(
        "main.qli",
        &source
            .replace(
                "use std::quantum::h;",
                "use std::quantum::{h,phase_eighth};",
            )
            .replace("h(h(q))", "phase_eighth(q)"),
    );
    assert_eq!(
        check_project_diagnostic(&root.0).unwrap_err().code,
        "contract"
    );
}
