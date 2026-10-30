//! CLI success describes the exact native scope without claiming source proof.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
mod common;

use common::SourceRoot;
use qleisli::contract::BasisType;
use qleisli::interchange::{RootInterface, Version, native::Kernel};
use qleisli::ir::{BasisShape, Effect, QuantumPort, RawProgram, TokenId, WireId};
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

fn cli(command: &str, path: &Path, json: bool) -> Output {
    let mut process = Command::new(env!("CARGO_BIN_EXE_qleisli"));
    process.arg(command).arg(path);
    if command == "verify-ir" {
        process.arg("--edition=2026");
    }
    if json {
        process.arg("--format=json");
    }
    process.output().unwrap()
}

fn success(output: Output) -> String {
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    String::from_utf8(output.stdout).unwrap()
}

// Counts describe every completed native invocation, including the ordinary
// bundled contracts. They do not confer an independent request on the entry.
fn native_counts(text: &str) -> (usize, usize) {
    assert!(
        !text.contains("native decision metadata truncated"),
        "{text}"
    );
    let lines: Vec<_> = text
        .lines()
        .filter_map(|line| line.strip_prefix("native decisions: "))
        .collect();
    assert_eq!(lines.len(), 1, "{text}");
    let (decisions, requests) = lines[0].split_once("; native requests checked: ").unwrap();
    for count in [decisions, requests] {
        assert!(
            !count.is_empty() && count.bytes().all(|byte| byte.is_ascii_digit()),
            "{text}"
        );
    }
    let counts = (decisions.parse().unwrap(), requests.parse().unwrap());
    assert!(counts.1 <= counts.0, "{text}");
    counts
}

fn assert_json_native_counts(json: &str, (decisions, requests): (usize, usize)) {
    assert!(
        json.contains(&format!(
            "\"native_decisions\":{{\"count\":{decisions},\"requests_checked\":{requests},\"complete\":true}}"
        )),
        "{json}"
    );
}

fn checker() -> PathBuf {
    std::fs::canonicalize(std::env::var_os("QLEISLI_KERNEL").unwrap()).unwrap()
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn requestless_entry_and_mainless_library_have_explicit_success_scopes() {
    let mut bundled_requests = None;
    for (source, entry) in [
        ("observe fn main() -> Bit { 0 }", true),
        ("pub classical fn identity(x: Bit) -> Bit { x }", false),
    ] {
        let root = SourceRoot::new(source);
        let text = success(cli("check", &root.0, false));
        assert!(text.starts_with("checked source:"), "{text}");
        assert!(
            text.contains(&format!("checker: {}\n", checker().display())),
            "{text}"
        );
        assert!(text.contains("checker identity: unpinned"), "{text}");
        let counts = native_counts(&text);
        assert!(counts.1 > 0, "bundled ordinary contracts: {text}");
        if let Some(expected) = bundled_requests {
            assert_eq!(counts.1, expected, "{text}");
        } else {
            bundled_requests = Some(counts.1);
        }
        assert!(text.contains("source preservation: not proved"), "{text}");
        assert!(!text.contains("verified"), "{text}");
        assert!(
            text.contains(if entry {
                "entry request checked: false"
            } else {
                "entry: absent; entry request checked: not applicable"
            }),
            "{text}"
        );
        let json = success(cli("check", &root.0, true));
        assert_json_native_counts(&json, counts);
        assert!(
            json.contains(if entry {
                "\"entry\":{\"present\":true,\"request_checked\":false,\"ordinary_result_checked\":false,\"runtime_result_checked\":false}"
            } else {
                "\"entry\":{\"present\":false,\"request_checked\":null,\"ordinary_result_checked\":false,\"runtime_result_checked\":false}"
            }),
            "{json}"
        );
        assert!(
            json.contains("\"source_preservation_verified\":false"),
            "{json}"
        );
        assert!(!json.contains("\"verified\":true"), "{json}");
        let qrate_root = SourceRoot::new("");
        qrate_root.write(
            "Qargo.toml",
            "schema-version = 2\n[qrate]\nedition = \"2026\"\n[source]\nroot = \"src\"\n",
        );
        std::fs::create_dir(qrate_root.0.join("src")).unwrap();
        qrate_root.write("src/main.qli", source);
        let qrate = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .arg("check")
            .arg(&qrate_root.0)
            .args(["--qrate", "--format=json"])
            .output()
            .unwrap();
        assert_eq!(success(qrate), json);
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn partial_meaning_requests_do_not_become_an_entry_request() {
    let ordinary = SourceRoot::new("observe fn main() -> Bit { 0 }");
    let baseline = native_counts(&success(cli("check", &ordinary.0, false)));
    assert!(baseline.1 > 0);
    let root = SourceRoot::new(
        "unitary fn identity(q:Q<Bit>)->Q<Bit>{q}
         meaning I:Bit=reference(identity);
         observe fn main()->Bit{0}",
    );
    let text = success(cli("check", &root.0, false));
    assert!(text.contains("entry request checked: false"), "{text}");
    let counts = native_counts(&text);
    assert!(
        counts.1 > baseline.1,
        "reference Meaning adds a request: {text}"
    );
    let json = success(cli("check", &root.0, true));
    assert!(
        json.contains("\"entry\":{\"present\":true,\"request_checked\":false,\"ordinary_result_checked\":false,\"runtime_result_checked\":false}"),
        "{json}"
    );
    assert_json_native_counts(&json, counts);
    assert!(
        json.contains("\"source_preservation_verified\":false"),
        "{json}"
    );
}

fn identity_artifact(root: &SourceRoot) -> PathBuf {
    let program = Kernel::selected(qleisli::edition::Edition::E2026)
        .unwrap()
        .accept_raw(RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: TokenId(0),
                wires: vec![WireId(0)],
                shape: BasisShape { bits: 1 },
            }],
            classical_inputs: vec![],
            operations: vec![],
            quantum_outputs: vec![TokenId(0)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        })
        .unwrap();
    let artifact = qleisli::interchange::export(
        &program,
        Some(&RootInterface {
            input: BasisType::Bit,
            output: BasisType::Bit,
        }),
        Version::V2,
    )
    .unwrap();
    let path = root.0.join("identity.qirf");
    std::fs::write(&path, artifact).unwrap();
    path
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn artifact_success_distinguishes_absent_matching_and_wrong_requests() {
    let root = SourceRoot::new("observe fn main()->Bit{0}");
    let artifact = identity_artifact(&root);
    for edition in [None, Some("latest"), Some("2027")] {
        let mut process = Command::new(env!("CARGO_BIN_EXE_qleisli"));
        process.arg("verify-ir").arg(&artifact);
        if let Some(edition) = edition {
            process.arg(format!("--edition={edition}"));
        }
        let output = process.output().unwrap();
        assert!(!output.status.success(), "{output:?}");
        assert!(String::from_utf8_lossy(&output.stderr).contains("edition"));
    }
    for json in [false, true] {
        let text = success(cli("verify-ir", &artifact, json));
        assert!(
            text.contains(if json {
                "\"request_checked\":false"
            } else {
                "artifact root request checked: false"
            }),
            "{text}"
        );
        assert!(
            !text.contains("\"verified\":true") && !text.contains("verified IR"),
            "{text}"
        );
        for (table, accepted) in [("[0,1]", true), ("[1,0]", false)] {
            root.write("request.json", &format!(r#"{{"format":"qleisli.request","version":1,"signature":{{"tag":"bit"}},"meaning":{{"tag":"permutation","table":{table}}},"source_snapshot":null}}"#));
            let mut process = Command::new(env!("CARGO_BIN_EXE_qleisli"));
            process
                .arg("verify-ir")
                .arg(&artifact)
                .arg("--edition=2026")
                .arg(format!(
                    "--against={}",
                    root.0.join("request.json").display()
                ));
            if json {
                process.arg("--format=json");
            }
            let output = process.output().unwrap();
            assert_eq!(output.status.success(), accepted, "{output:?}");
            if accepted {
                let text = success(output);
                assert!(
                    text.contains(if json {
                        "\"request_checked\":true"
                    } else {
                        "artifact root request checked: true"
                    }),
                    "{text}"
                );
                assert!(
                    text.contains(if json {
                        "\"source_preservation_verified\":false"
                    } else {
                        "source preservation: not proved"
                    }),
                    "{text}"
                );
            } else {
                let text =
                    String::from_utf8(if json { output.stdout } else { output.stderr }).unwrap();
                assert!(text.contains("contract"), "{text}");
            }
        }
    }
    let emitted = root.0.join("emitted.qirf");
    let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .arg("emit-ir")
        .arg(&root.0)
        .arg(format!("--output={}", emitted.display()))
        .arg("--format=json")
        .output()
        .unwrap();
    let json = success(output);
    assert!(json.contains("\"request_checked\":false"), "{json}");
    assert!(json.contains("\"checker_identity\":\"unpinned\""), "{json}");
    assert!(
        json.contains("\"source_preservation_verified\":false"),
        "{json}"
    );
    assert!(emitted.is_file());
}

#[cfg(unix)]
fn forwarding_checker(root: &SourceRoot, name: &std::ffi::OsStr) -> PathBuf {
    use std::os::unix::fs::PermissionsExt;
    let path = root.0.join(name);
    std::fs::write(
        &path,
        "#!/bin/sh\nexec \"$QLEISLI_TEST_FORWARD_KERNEL\" \"$@\"\n",
    )
    .unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700)).unwrap();
    path
}

#[cfg(unix)]
#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn json_names_the_canonical_invoked_checker_and_escapes_its_path() {
    use std::io::Write as _;
    let root = SourceRoot::new("observe fn main()->Bit{0}");
    let kernels = SourceRoot::new("");
    let wrapper = forwarding_checker(&kernels, "checker-\"\\\n日本語".as_ref());
    let alias = kernels.0.join("checker-alias");
    std::os::unix::fs::symlink(&wrapper, &alias).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .arg("check")
        .arg(&root.0)
        .arg(format!("--lean-kernel={}", alias.display()))
        .arg("--format=json")
        .env("QLEISLI_TEST_FORWARD_KERNEL", checker())
        .output()
        .unwrap();
    let json = success(output);
    let canonical = std::fs::canonicalize(&wrapper).unwrap();
    let mut child = Command::new("python3").args(["-B", "-c", "import json,sys; r=json.load(sys.stdin)['result']; assert r['checker_paths'] == [sys.argv[1]]; assert r['checker_identity'] == 'unpinned'; assert r['native_decisions']['complete']; assert r['source_preservation_verified'] is False"])
        .arg(&canonical).stdin(Stdio::piped()).spawn().unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(json.as_bytes())
        .unwrap();
    assert!(child.wait().unwrap().success());
    assert!(!json.contains("checker-alias"), "{json}");
    let text = success(
        Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .arg("check")
            .arg(&root.0)
            .arg(format!("--lean-kernel={}", alias.display()))
            .env("QLEISLI_TEST_FORWARD_KERNEL", checker())
            .output()
            .unwrap(),
    );
    assert!(
        text.contains(&format!("checker: {canonical:?}\n")),
        "{text}"
    );
    assert!(!text.contains("\\\n日本語"), "{text}");
}

// macOS filesystems reject invalid UTF-8 filenames before checker invocation;
// the renderer's exact OS-byte refusal is unit-tested on every Unix target.
#[cfg(target_os = "linux")]
#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn non_utf8_checker_refuses_json_before_artifact_creation() {
    use std::os::unix::ffi::OsStrExt;
    let root = SourceRoot::new("observe fn main()->Bit{0}");
    let kernels = SourceRoot::new("");
    let wrapper = forwarding_checker(&kernels, std::ffi::OsStr::from_bytes(b"checker-\xff"));
    let emitted = root.0.join("emitted.qirf");
    for command in ["check", "emit-ir"] {
        let mut process = Command::new(env!("CARGO_BIN_EXE_qleisli"));
        process
            .arg(command)
            .arg(&root.0)
            .arg("--format=json")
            // The environment selection retains OS bytes; CLI flag values
            // deliberately keep their existing UTF-8 grammar.
            .env("QLEISLI_KERNEL", &wrapper)
            .env("QLEISLI_TEST_FORWARD_KERNEL", checker());
        if command == "emit-ir" {
            process.arg(format!("--output={}", emitted.display()));
        }
        let output = process.output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        let json = String::from_utf8(output.stdout).unwrap();
        assert!(
            json.contains("canonical checker path is not valid UTF-8"),
            "{json}"
        );
        assert!(!emitted.exists());
    }
}
