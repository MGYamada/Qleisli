//! Reproductions for the GitHub bug triage, using only bounded examples.
mod common;
use common::SourceRoot;
use qleisli::frontend::compile::compile_project;
use qleisli::interop::{InteropErrorKind, export_openqasm3, export_qir_base};
use std::{fs, process::Command};

#[test]
fn tuple_diagnostic_has_a_structured_binding_and_no_host_path() {
    let root = SourceRoot::new(
        "use std::quantum::{init0,cnot}; use std::observe::measure_z; observe fn main()->Bit { let pair=cnot(init0(),init0()); measure_z(pair) }",
    );
    let result = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .arg("check")
        .arg(&root.0)
        .arg("--format=json")
        .output()
        .unwrap();
    assert!(!result.status.success());
    let text = String::from_utf8(result.stdout).unwrap();
    assert!(text.contains("binding `pair`"), "{text}");
    assert!(
        text.contains("\"primary\":{\"path\":\"main.qli\""),
        "{text}"
    );
    assert!(!text.contains(root.0.to_str().unwrap()), "{text}");
}

#[test]
fn byte_limits_identify_the_file_without_embedding_a_host_path() {
    let root = SourceRoot::new("");
    fs::create_dir(root.0.join("sub")).unwrap();
    root.write("sub/m.qli", "observe fn main()->Unit{()}");
    for limit in ["--source-bytes=10", "--project-bytes=10"] {
        let result = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .arg("check")
            .arg(&root.0)
            .args([limit, "--format=json"])
            .output()
            .unwrap();
        assert!(!result.status.success());
        let text = String::from_utf8(result.stdout).unwrap();
        assert!(text.contains("\"code\":\"limit\""), "{text}");
        assert!(
            text.contains(
                "\"primary\":{\"path\":\"sub/m.qli\",\"start\":0,\"end\":0,\"line\":1,\"column\":1}"
            ),
            "{text}"
        );
        assert!(!text.contains(root.0.to_str().unwrap()), "{text}");
    }
}

#[cfg(unix)]
#[test]
fn unreadable_source_identifies_the_failing_file_in_both_transports() {
    use std::os::unix::fs::PermissionsExt;
    let root = SourceRoot::new("");
    fs::create_dir(root.0.join("sub")).unwrap();
    root.write("sub/m.qli", "unitary fn f()->Unit{()}");
    let path = root.0.join("sub/m.qli");
    fs::set_permissions(&path, fs::Permissions::from_mode(0o0)).unwrap();
    // A privileged test process can read mode 000; permission assertions need
    // the ordinary-user context used by the macOS and Linux CI jobs.
    let denied = fs::File::open(&path).is_err();
    let outputs: Vec<_> = [false, true]
        .into_iter()
        .map(|json| {
            let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
            command.arg("check").arg(&root.0);
            if json {
                command.arg("--format=json");
            }
            (json, command.output().unwrap())
        })
        .collect();
    fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();
    if !denied {
        return;
    }
    for (json, result) in outputs {
        assert!(!result.status.success());
        let text = String::from_utf8(if json { result.stdout } else { result.stderr }).unwrap();
        assert!(text.contains("sub/m.qli"), "{text}");
        if json {
            assert!(!text.contains(root.0.to_str().unwrap()), "{text}");
        }
    }
}

#[test]
fn interop_file_io_uses_the_closed_project_code() {
    let root = SourceRoot::new("");
    for path in [root.0.join("missing.qasm"), root.0.clone()] {
        let result = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .args(["interop", "check"])
            .arg(path)
            .arg("--input=qasm")
            .output()
            .unwrap();
        assert!(!result.status.success());
        let text = String::from_utf8(result.stdout).unwrap();
        assert!(text.contains("\"code\":\"project\""), "{text}");
        assert!(!text.contains("\"code\":\"io\""), "{text}");
    }
}

#[test]
fn terminal_export_keeps_allocations_before_observation() {
    for observe in ["let a=measure_z(q);", "discard(q); let a=0;"] {
        let root = SourceRoot::new(&format!(
            "use std::quantum::{{init0,h}}; use std::observe::{{measure_z,discard}}; observe fn main()->(Bit,Bit) {{let q=h(init0()); {observe} let b=measure_z(init0()); (a,b)}}"
        ));
        let program = compile_project(&root.0).unwrap();
        for error in [
            export_openqasm3(&program).unwrap_err(),
            export_qir_base(&program).unwrap_err(),
        ] {
            assert_eq!(error.kind, InteropErrorKind::Unsupported);
            assert!(error.to_string().contains("after terminal observation"));
        }
        root.write("main.qli", "use std::quantum::init0; use std::observe::measure_z; observe fn main()->(Bit,Bit){let q=init0();let r=init0();(measure_z(q),measure_z(r))}");
        let program = compile_project(&root.0).unwrap();
        assert!(export_openqasm3(&program).is_ok());
        assert!(export_qir_base(&program).is_ok());
    }
}

#[cfg(unix)]
#[test]
fn selected_qrate_rejects_root_and_ancestor_replacement_before_loading() {
    use qleisli::frontend::project::{QrateSource, SourcePolicy};
    use std::os::unix::fs::symlink;
    for replace_ancestor in [false, true] {
        let root = SourceRoot::new("");
        root.write(
            "Qargo.toml",
            "schema-version=2\n[qrate]\nedition='2026'\n[source]\nroot='./parent/src'\n",
        );
        fs::create_dir_all(root.0.join("parent/src")).unwrap();
        root.write("parent/src/main.qli", "observe fn main()->Bit{0}");
        let selected = QrateSource::select(&root.0).unwrap();
        selected.check_with_policy(Default::default()).unwrap();
        let outside = SourceRoot::new("observe fn main()->Bit{1}");
        fs::create_dir(outside.0.join("src")).unwrap();
        outside.write("src/main.qli", "observe fn main()->Bit{1}");
        let replaced = root.0.join(if replace_ancestor {
            "parent"
        } else {
            "parent/src"
        });
        let saved = root.0.join("saved");
        fs::rename(&replaced, &saved).unwrap();
        symlink(&outside.0, &replaced).unwrap();
        assert!(selected.load_with_policy(SourcePolicy::Legacy).is_err());
        assert!(selected.check_with_policy(Default::default()).is_err());
        assert!(selected.compile_with_policy(Default::default()).is_err());
        fs::remove_file(&replaced).unwrap();
        // A different ordinary directory must not silently replace the handle.
        fs::create_dir_all(replaced.join("src")).unwrap();
        assert!(selected.load_with_policy(SourcePolicy::Legacy).is_err());
    }
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn source_loading_needs_search_but_not_read_permission_on_ancestors() {
    use qleisli::frontend::project::Project;
    use std::os::unix::fs::PermissionsExt;
    let root = SourceRoot::new("");
    fs::create_dir(root.0.join("project")).unwrap();
    root.write(
        "project/Qargo.toml",
        "schema-version=2\n[qrate]\nedition='2026'\n",
    );
    root.write("project/main.qli", "observe fn main()->Unit{()}");
    fs::set_permissions(&root.0, fs::Permissions::from_mode(0o100)).unwrap();
    #[cfg(target_os = "macos")]
    let legacy_denied = rustix::system::uname()
        .release()
        .to_str()
        .unwrap()
        .split('.')
        .next()
        .unwrap()
        .parse::<u32>()
        .unwrap()
        < 20
        && fs::File::open(&root.0).is_err();
    #[cfg(not(target_os = "macos"))]
    let legacy_denied = false;
    let result = Project::load(&root.0.join("project"));
    fs::set_permissions(&root.0, fs::Permissions::from_mode(0o700)).unwrap();
    assert_eq!(result.is_err(), legacy_denied, "{result:?}");
}
