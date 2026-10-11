//! Additive CLI checks, including independently executed small source programs.
use std::{path::PathBuf, process::Command};
mod common;
fn command() -> Command {
    Command::new(env!("CARGO_BIN_EXE_qleisli"))
}

#[test]
fn historical_const_manifest_classification_does_not_admit_filesystem_source() {
    let project = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/authoring_sessions/const-parameters-v030/attempt-01/natural");
    let output = command()
        .arg("check")
        .arg(project)
        .args(["--format=json", "--lean-kernel=missing"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("\"code\":\"project\""), "{text}");
    assert!(text.contains("requires schema-version = 2"), "{text}");
}

fn modules() -> (Vec<String>, common::SourceRoot) {
    // Keep the existing bounded Fourier regression and all prior migrations.
    let source = common::current_source_text("corpus/sized/qualtran_qft/fourier.qli");
    let old = "fourier[static n: Nat]";
    assert_eq!(source.matches(old).count(), 1);
    let fourier = common::SourceRoot::new(&source.replacen(old, "fourier[const n: Nat]", 1));
    let modules = [
        ("measurement", "corpus/sized/measured_qpe/measurement.qli"),
        (
            "initialization",
            "corpus/sized/measured_qpe/initialization.qli",
        ),
        ("readout", "corpus/sized/measured_qpe/readout.qli"),
        ("estimation", "corpus/sized/qualtran_qpe/estimation.qli"),
        ("preparation", "corpus/sized/qualtran_qpe/preparation.qli"),
        ("fourier", "corpus/sized/qualtran_qft/fourier.qli"),
        ("evolution", "corpus/sized/qualtran_qpe/evolution.qli"),
    ]
    .into_iter()
    .map(|(name, path)| {
        let selected = if name == "fourier" {
            fourier.0.join("main.qli")
        } else {
            common::current_namespace_fixture(&PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(path))
        };
        format!("--module={name}={}", selected.display())
    })
    .collect();
    (modules, fourier)
}
#[test]
fn sized_cli_rejects_ambiguous_or_incomplete_bindings_before_loading() {
    for args in [
        vec!["check", "--entry=foo::f"],
        vec![
            "check",
            "--entry=foo::f",
            "--module=foo=x",
            "--kernel=x",
            "--kernel=y",
        ],
        vec![
            "run",
            "--entry=foo::f",
            "--module=foo=x",
            "--kernel=x",
            "--request=a",
            "--qpe-provider=b",
        ],
        vec![
            "sample",
            "--entry=foo::f",
            "--module=foo=x",
            "--kernel=x",
            "--shots=01",
            "--seed=0",
        ],
        vec![
            "check",
            "--entry=foo::f",
            "--module=foo=x",
            "--kernel=x",
            "--operation-nat=U.n=1",
        ],
    ] {
        let output = command().args(args).output().unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
    }
}

#[test]
fn sized_check_rejects_execution_basis_before_loading() {
    for basis in ["0", "1", "999"] {
        let output = command()
            .args([
                "check",
                "--entry=foo::f",
                "--module=foo=missing.qli",
                "--kernel=missing",
            ])
            .arg(format!("--basis={basis}"))
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2), "{output:?}");
        assert!(output.stdout.is_empty());
        assert!(String::from_utf8_lossy(&output.stderr).starts_with("usage:"));
    }
}

#[test]
fn sized_execution_basis_still_checks_input_width() {
    let files = common::SourceRoot::new("pub unitary fn f(q: Q<Bit>) -> Q<Bit> { q }");
    for action in ["run", "sample"] {
        let mut cmd = command();
        cmd.args([action, "--entry=main::f", "--basis=2", "--kernel=missing"])
            .arg(format!(
                "--module=main={}",
                files.0.join("main.qli").display()
            ));
        if action == "sample" {
            cmd.args(["--shots=1", "--seed=0"]);
        }
        let output = cmd.output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(output.stdout.is_empty());
        assert!(
            String::from_utf8_lossy(&output.stderr)
                .contains("input basis is outside the entry's quantum type")
        );
    }
}

#[test]
fn sized_cli_cannot_select_private_entries_or_providers() {
    let files = common::SourceRoot::new("unitary fn f(q: Q<Bit>) -> Q<Bit> { q }");
    let args = ["emit-proposal", "--entry=main::f"];
    let run = |provider: bool| {
        let mut cmd = command();
        cmd.args(args)
            .arg(format!(
                "--module=main={}",
                files.0.join("main.qli").display()
            ))
            .arg(format!(
                "--output={}",
                files.0.join("proposal.json").display()
            ));
        if provider {
            cmd.arg(format!(
                "--module=dep={}",
                files.0.join("dep.qli").display()
            ))
            .arg("--operation=U=dep::g");
        }
        cmd.output().unwrap()
    };
    let private_entry = run(false);
    assert_eq!(private_entry.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&private_entry.stderr).contains("visibility"));
    assert!(!files.0.join("proposal.json").exists());

    files.write(
        "main.qli",
        "pub unitary fn f[const U: Op<Bit>](q: Q<Bit>) -> Q<Bit> requires Applicable(U) { U(q) }",
    );
    files.write("dep.qli", "unitary fn g(q: Q<Bit>) -> Q<Bit> { q }");
    let private_provider = run(true);
    assert_eq!(private_provider.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&private_provider.stderr).contains("dependency dep::g is private")
    );
    assert!(!files.0.join("proposal.json").exists());
    files.write("dep.qli", "pub unitary fn g(q: Q<Bit>) -> Q<Bit> { q }");
    let public_provider = run(true);
    assert!(public_provider.status.success(), "{public_provider:?}");
    assert!(files.0.join("proposal.json").is_file());
}
#[test]
fn sized_cli_emits_only_an_untrusted_proposal_without_a_kernel() {
    let (modules, _fourier) = modules();
    let file = std::env::temp_dir().join(format!("qleisli-sized-cli-{}.json", std::process::id()));
    let output = command()
        .args(["emit-proposal", "--entry=fourier::fourier", "--nat=n=1"])
        .args(&modules)
        .arg(format!("--output={}", file.display()))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("untrusted-proposal"));
    let bytes = std::fs::read(&file).unwrap();
    assert!(String::from_utf8_lossy(&bytes).contains("qleisli.hierarchical-ir"));
    std::fs::remove_file(file).unwrap();
}
#[test]
#[ignore = "requires freshly built Lean kernel; CI runs explicitly"]
fn sized_cli_native_source_check_run_and_fresh_sampling() {
    let kernel = PathBuf::from(std::env::var_os("QLEISLI_HIERARCHY_KERNEL").expect("kernel path"));
    let const_client = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/authoring_sessions/const-parameters-v030/closed-public/main.qli");
    for action in ["check", "run"] {
        let output = command()
            .args([action, "--entry=study::main", "--format=json"])
            .arg(format!("--module=study={}", const_client.display()))
            .arg(format!("--kernel={}", kernel.display()))
            .output()
            .unwrap();
        assert!(output.status.success(), "{output:?}");
        assert!(output.stderr.is_empty(), "{output:?}");
        let text = String::from_utf8(output.stdout).unwrap();
        assert!(text.contains("\"scope\":\"native-validity\""), "{text}");
        assert!(text.contains("\"source_meaning_verified\":false"), "{text}");
        if action == "run" {
            assert!(
                text.contains("\"distribution\":[{\"bits\":[false],\"probability\":1}]"),
                "const identity must return the independent zero expectation: {text}"
            );
        }
    }
    let (modules, _fourier) = modules();
    let args = [
        "--entry=measurement::qpe",
        "--nat=n=1",
        "--nat=m=1",
        "--operation=U=evolution::evolve",
        "--operation-nat=U.n=1",
        "--operation-nat=U.j=1",
        "--operation-nat=U.d=1",
    ];
    for action in ["check", "run", "sample"] {
        let mut cmd = command();
        cmd.args([action])
            .args(args)
            .args(&modules)
            .arg(format!("--kernel={}", kernel.display()));
        if action == "sample" {
            cmd.args(["--shots=8", "--seed=42"]);
        }
        if action != "check" {
            cmd.arg("--basis=1");
        }
        let output = cmd.output().unwrap();
        assert!(
            output.status.success(),
            "{action}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let text = String::from_utf8(output.stdout).unwrap();
        assert!(
            text.contains("\"scope\":\"producer-consistency\""),
            "{text}"
        );
        assert!(text.contains("\"source_meaning_verified\":false"), "{text}");
        assert!(
            text.contains("\"execution_authority\":\"checked-produced-ir\""),
            "{text}"
        );
        match action {
            "check" => assert!(text.contains("\"checked\"")),
            "run" => {
                assert!(text.contains("\"measured_bits\":1"));
                assert!(text.contains("\"branches\":"));
            }
            "sample" => assert!(
                text.contains("\"outcomes\":[1, 1, 1, 1, 1, 1, 1, 1]"),
                "{text}"
            ),
            _ => unreachable!(),
        }
    }
}

#[test]
#[ignore = "requires freshly built Lean kernel; CI runs explicitly"]
fn sized_cli_separates_producer_consistency_from_independent_requests() {
    use qleisli::frontend::compile::ParsedProgram;
    use std::collections::BTreeMap;
    let kernel = PathBuf::from(std::env::var_os("QLEISLI_HIERARCHY_KERNEL").expect("kernel path"));
    let h = "use std::quantum::h; pub unitary fn f(q: Q<Bit>) -> Q<Bit> { h(q) }";
    let x = "use std::quantum::x; pub unitary fn f(q: Q<Bit>) -> Q<Bit> { x(q) }";
    let h_proposal = ParsedProgram::parse(BTreeMap::from([("main".into(), h.into())]))
        .unwrap()
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower()
        .unwrap();
    let files = common::SourceRoot::new(h);
    std::fs::write(
        files.0.join("h.request.json"),
        h_proposal.comparison_request(),
    )
    .unwrap();
    for (source, caller, success) in [
        (h, false, true),
        (h, true, true),
        (x, false, true),
        (x, true, false),
    ] {
        files.write("main.qli", source);
        for action in ["check", "run"] {
            let mut cmd = command();
            cmd.args([action, "--entry=main::f"])
                .arg(format!(
                    "--module=main={}",
                    files.0.join("main.qli").display()
                ))
                .arg(format!("--kernel={}", kernel.display()));
            if caller {
                cmd.arg(format!(
                    "--request={}",
                    files.0.join("h.request.json").display()
                ));
            }
            let output = cmd.output().unwrap();
            assert_eq!(
                output.status.success(),
                success,
                "{action}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            if success {
                let text = String::from_utf8(output.stdout).unwrap();
                let scope = if caller {
                    "caller-composition"
                } else {
                    "producer-consistency"
                };
                let authority = if caller {
                    "checked-ir-against-caller-request"
                } else {
                    "checked-produced-ir"
                };
                assert!(text.contains(&format!("\"scope\":\"{scope}\"")), "{text}");
                assert!(
                    text.contains(&format!("\"execution_authority\":\"{authority}\"")),
                    "{text}"
                );
                assert!(text.contains("\"source_meaning_verified\":false"), "{text}");
            } else {
                assert!(output.stdout.is_empty());
            }
        }
    }
}
