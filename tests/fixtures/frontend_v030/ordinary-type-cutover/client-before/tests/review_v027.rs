//! Regression cases for GitHub issues #211, #212 and #214.
mod common;

use common::SourceRoot;
use qleisli::frontend::compile::{ErrorCode, check_project};
use qleisli::frontend::project::manifest_warnings;
use std::{fs, path::Path, process::Command};

#[test]
fn unused_manifest_warnings_are_host_independent_and_located() {
    for relative in [None, Some("src"), Some("src/nested")] {
        let mut outputs = Vec::new();
        for _ in 0..2 {
            let root = SourceRoot::new("observe fn main()->Unit{()}");
            let selection = relative.map_or(String::new(), |r| format!("[source]\nroot='{r}'\n"));
            root.write(
                "Qargo.toml",
                &format!("schema-version=2\nunused=true\n[qrate]\nedition='2026'\n{selection}"),
            );
            if let Some(relative) = relative {
                fs::create_dir_all(root.0.join(relative)).unwrap();
                fs::rename(
                    root.0.join("main.qli"),
                    root.0.join(relative).join("main.qli"),
                )
                .unwrap();
            }
            let warning = manifest_warnings(&root.0).unwrap().remove(0);
            assert!(
                !warning.message.contains(&root.0.display().to_string()),
                "{warning:?}"
            );
            assert_eq!(
                warning.primary.unwrap().path,
                root.0.canonicalize().unwrap().join("Qargo.toml")
            );
            for json in [false, true] {
                let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
                command.arg("check").arg(&root.0);
                if relative.is_some() {
                    command.arg("--qrate");
                }
                if json {
                    command.arg("--format=json");
                }
                let output = command.output().unwrap();
                assert!(output.status.success(), "{output:?}");
                let text =
                    String::from_utf8(if json { output.stdout } else { output.stderr }).unwrap();
                assert!(!text.contains(&root.0.display().to_string()), "{text}");
                if json {
                    assert!(text.contains("\"severity\":\"warning\""), "{text}");
                    assert!(!text.contains("\"primary\":null"), "{text}");
                    let label = relative.map_or("Qargo.toml".to_string(), |r| {
                        format!(
                            "{}Qargo.toml",
                            "../".repeat(Path::new(r).components().count())
                        )
                    });
                    assert!(text.contains(&format!("\"path\":\"{label}\"")), "{text}");
                }
                outputs.push(text);
            }
        }
        assert_eq!(outputs[..2], outputs[2..]);
    }
}

fn emit(root: &SourceRoot, destination: &Path) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .args(["sized", "emit-proposal", "--entry=main::f"])
        .arg(format!(
            "--module=main={}",
            root.0.join("main.qli").display()
        ))
        .arg(format!("--output={}", destination.display()))
        .output()
        .unwrap()
}

#[test]
fn sized_proposal_never_overwrites_an_existing_file_or_source() {
    let source = "pub unitary fn f(q: Q<Bit>) -> Q<Bit> { q }";
    let root = SourceRoot::new(source);
    root.write("existing.json", "retain this artifact");
    for (name, expected) in [
        ("existing.json", "retain this artifact"),
        ("main.qli", source),
    ] {
        let path = root.0.join(name);
        let output = emit(&root, &path);
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(output.stdout.is_empty());
        assert_eq!(fs::read_to_string(path).unwrap(), expected);
    }
    assert_eq!(emit(&root, &root.0).status.code(), Some(1));
    let fresh = root.0.join("fresh.json");
    assert!(emit(&root, &fresh).status.success());
    assert!(
        fs::read_to_string(fresh)
            .unwrap()
            .contains("qleisli.hierarchical-ir")
    );
    assert!(
        fs::read_dir(&root.0).unwrap().all(|p| !p
            .unwrap()
            .file_name()
            .to_string_lossy()
            .ends_with(".tmp"))
    );
}

#[cfg(unix)]
#[test]
fn sized_proposal_never_follows_destination_symlinks() {
    let root = SourceRoot::new("pub unitary fn f(q: Q<Bit>) -> Q<Bit> { q }");
    root.write("target.json", "retain target");
    for target in ["target.json", "missing.json"] {
        let link = root.0.join(format!("link-{target}"));
        std::os::unix::fs::symlink(root.0.join(target), &link).unwrap();
        let output = emit(&root, &link);
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(
            fs::symlink_metadata(&link)
                .unwrap()
                .file_type()
                .is_symlink()
        );
    }
    assert_eq!(
        fs::read_to_string(root.0.join("target.json")).unwrap(),
        "retain target"
    );
    assert!(!root.0.join("missing.json").exists());
}

#[test]
fn local_only_call_names_reach_the_lowerers_diagnostics() {
    for (source, message) in [
        (
            "unitary fn bad(q:Q<Bit>)->Q<Bit>{let f=q;f(f)}",
            "a local value is not callable",
        ),
        (
            "unitary fn bad(f:Q<Bit>)->Q<Bit>{f(f)}",
            "a local value is not callable",
        ),
        (
            "unitary fn bad(q:Q<Bit>)->Q<Bit>{let f=true;f(q)}",
            "a local value is not callable",
        ),
        (
            "unitary fn bad(q:Q<Bit>)->Q<Bit>{let (f,u)=(q,());f(f)}",
            "a local value is not callable",
        ),
        (
            "unitary fn bad(q:Q<Bit>)->Q<Bit>{let f=q;let q=f;f(q)}",
            "a local value is not callable",
        ),
        (
            "unitary fn bad(q:Q<Bit>)->Q<Bit>{let f=q;adjoint(f,f)}",
            "static operation requires a function name, not a local value",
        ),
        (
            "unitary fn bad(q:Q<Bit>)->Q<Bit>{let f=q;repeat_static(0,f,f)}",
            "static operation requires a function name, not a local value",
        ),
        (
            "unitary fn bad(q:Q<Bit>)->Q<Bit>{if true{let f=q;f(f)}else{q}}",
            "a local value is not callable",
        ),
        (
            "unitary fn bad(q:Q<Bit>)->Q<Bit>{let f=true;apply_contract(f,f,q)}",
            "apply_contract requires function names, not local values",
        ),
        (
            "unitary fn bad(q:Q<Bit>)->Q<Bit>{let f=true;with_computed(q,f){|a|a}}",
            "with_computed requires a basis function name",
        ),
        (
            "unitary fn bad(q:Q<Bit>)->Q<Bit>{with_computed(q,p){|f|f(f)}} basis fn p(b:Bit)->Bit{b}",
            "a local value is not callable",
        ),
    ] {
        let root = SourceRoot::new(source);
        let error = check_project(&root.0).unwrap_err();
        assert_eq!(error.code, ErrorCode::TypeMismatch, "{source}\n{error}");
        assert_eq!(error.message, message, "{source}\n{error}");
        assert_eq!(&source[error.span.start..error.span.end], "f");
    }
}

#[test]
fn dependency_scopes_do_not_hide_unknown_names_or_recursive_initializers() {
    for (source, expected) in [
        (
            "unitary fn bad(q:Q<Bit>)->Q<Bit>{if true{let f=true;()}else{()};f(q)}",
            ErrorCode::UnknownName,
        ),
        (
            "unitary fn bad(q:Q<Bit>)->Q<Bit>{f(q);let f=q;f}",
            ErrorCode::UnknownName,
        ),
        (
            "unitary fn f(q:Q<Bit>)->Q<Bit>{let f=f(q);f}",
            ErrorCode::RecursiveCall,
        ),
        (
            "unitary fn unused(q:Q<Bit>)->Q<Bit>{missing(q)}",
            ErrorCode::UnknownName,
        ),
    ] {
        let root = SourceRoot::new(source);
        assert_eq!(
            check_project(&root.0).unwrap_err().code,
            expected,
            "{source}"
        );
    }
}

#[test]
fn basis_and_coherent_lift_bindings_are_not_global_dependencies() {
    for source in [
        "basis fn bad(f:Bit)->Bit{f(f)}",
        "unitary fn bad(q:Q<Bit>)->Q<Bit>{do f <- q; pure f(f)}",
    ] {
        let root = SourceRoot::new(source);
        let error = check_project(&root.0).unwrap_err();
        assert_eq!(error.code, ErrorCode::TypeMismatch, "{source}\n{error}");
        assert_eq!(error.message, "a basis value is not callable");
    }
}

#[test]
fn local_static_argument_reports_its_type_at_the_original_argument() {
    let source = "unitary fn apply[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){U(q)}
unitary fn bad(q:Q<Bit>)->Q<Bit>{apply[q](q)}";
    let root = SourceRoot::new(source);
    let error = check_project(&root.0).unwrap_err();
    assert_eq!(error.code, ErrorCode::TypeMismatch);
    assert_eq!(
        error.message,
        "a local or spent runtime value cannot be a static operation"
    );
    assert_eq!(
        error.span.start,
        source.rfind("apply[q]").unwrap() + "apply[".len()
    );
}
