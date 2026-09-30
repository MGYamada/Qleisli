//! Additive CLI checks, including independently executed small source programs.
use std::{path::PathBuf, process::Command};
mod common;
fn command() -> Command {
    Command::new(env!("CARGO_BIN_EXE_qleisli"))
}
fn modules() -> Vec<String> {
    [
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
    .map(|(name, path)| format!("--module={name}={}/{path}", env!("CARGO_MANIFEST_DIR")))
    .collect()
}
#[test]
fn sized_cli_rejects_ambiguous_or_incomplete_bindings_before_loading() {
    for args in [
        vec!["sized"],
        vec![
            "sized",
            "check",
            "--entry=foo::f",
            "--module=foo=x",
            "--kernel=x",
            "--kernel=y",
        ],
        vec![
            "sized",
            "run",
            "--entry=foo::f",
            "--module=foo=x",
            "--kernel=x",
            "--request=a",
            "--qpe-provider=b",
        ],
        vec![
            "sized",
            "sample",
            "--entry=foo::f",
            "--module=foo=x",
            "--kernel=x",
            "--shots=01",
            "--seed=0",
        ],
        vec![
            "sized",
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
fn sized_cli_emits_only_an_untrusted_proposal_without_a_kernel() {
    let file = std::env::temp_dir().join(format!("qleisli-sized-cli-{}.json", std::process::id()));
    let output = command()
        .args([
            "sized",
            "emit-proposal",
            "--entry=fourier::fourier",
            "--nat=n=1",
        ])
        .args(modules())
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
    let args = [
        "--entry=measurement::qpe",
        "--nat=n=1",
        "--nat=m=1",
        "--operation=U=evolution::evolve",
        "--operation-nat=U.n=1",
        "--operation-nat=U.j=1",
        "--operation-nat=U.d=1",
        "--basis=1",
    ];
    for action in ["check", "run", "sample"] {
        let mut cmd = command();
        cmd.args(["sized", action])
            .args(args)
            .args(modules())
            .arg(format!("--kernel={}", kernel.display()));
        if action == "sample" {
            cmd.args(["--shots=8", "--seed=42"]);
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
    use qleisli::frontend::sized::ParsedProgram;
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
            cmd.args(["sized", action, "--entry=main::f"])
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
