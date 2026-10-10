//! Selected-source routing, bounded execution, and independent request separation.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
mod common;

use common::SourceRoot;
#[cfg(unix)]
use qleisli::frontend::compile::ParsedProgram;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn fixture(category: &str, name: &str) -> PathBuf {
    common::current_namespace_fixture(
        &Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/authoring_sessions/mixed-boolean-v030")
            .join(category)
            .join(name)
            .join("main.qli"),
    )
}

fn kernel() -> PathBuf {
    std::fs::canonicalize(
        std::env::var_os("QLEISLI_KERNEL")
            .or_else(|| std::env::var_os("QLEISLI_HIERARCHY_KERNEL"))
            .expect("select the separately built, audited native kernel"),
    )
    .unwrap()
}

fn selected(action: &str, path: &Path, entry: &str) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
    // Leading formatting must dispatch to the same selected-source plan.
    command
        .args(["--format=json", action])
        .arg(format!("--entry={entry}"))
        .arg(format!("--module=main={}", path.display()));
    command
}

fn result(output: Output, action: &str, success: bool) -> String {
    assert_eq!(output.status.success(), success, "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(
        text.starts_with("{\"format\":\"qleisli.result\",\"version\":1,"),
        "{text}"
    );
    assert!(
        text.contains(&format!("\"command\":\"{action}\"")),
        "{text}"
    );
    assert!(
        text.contains(if success {
            "\"outcome\":\"ok\""
        } else {
            "\"outcome\":\"error\""
        }),
        "{text}"
    );
    if success {
        assert!(text.contains("\"diagnostics\":[]"), "{text}");
    } else {
        assert!(text.contains("\"result\":null"), "{text}");
    }
    text
}

fn scope(text: &str, entry: &str, target: &str) {
    for expected in [
        format!("\"entry\":\"{entry}\""),
        format!("\"ir_profile\":\"{target}\""),
        "\"source_check_scope\":\"all-supplied-module-declarations\"".into(),
        "\"native_check_scope\":\"selected-specialization\"".into(),
        "\"source_meaning_verified\":false".into(),
    ] {
        assert!(text.contains(&expected), "missing {expected}: {text}");
    }
    if target == "raw" {
        for expected in [
            "\"scope\":\"native-validity\"",
            "\"request_origin\":\"none\"",
            "\"source_steps_checked\":true",
        ] {
            assert!(text.contains(expected), "{text}");
        }
        assert!(!text.contains("producer-consistency"), "{text}");
    } else {
        assert!(!text.contains("\"source_steps_checked\":true"), "{text}");
    }
}

#[test]
fn selected_explicit_raw_checks_a_retained_zero_width_quantum_owner() {
    for relative in [
        "tests/fixtures/authoring_sessions/quantum-unit-v030/attempt-01/id/main.qli",
        "tests/fixtures/frontend_v030/quantum-unit-source/current/scalar-unit.qli",
        "tests/fixtures/frontend_v030/quantum-unit-source/current/scalar-bit.qli",
    ] {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(relative);
        let output = selected("check", &path, "main::f")
            .arg("--ir-profile=raw")
            .arg(format!("--lean-kernel={}", kernel().display()))
            .output()
            .unwrap();
        let text = result(output, "check", true);
        scope(&text, "main::f", "raw");
    }
}

fn distribution(text: &str, expected: &[(&[bool], f64)]) {
    // Parse only the documented compact distribution rows. The numerical oracle
    // below is independent of both lowering paths and of the CLI serializer.
    let body = text.split_once("\"distribution\":[").expect(text).1;
    let mut actual = BTreeMap::new();
    for row in body.split("{\"bits\":[").skip(1) {
        let (bits, rest) = row.split_once("],\"probability\":").expect(text);
        let bits: Vec<bool> = if bits.is_empty() {
            vec![]
        } else {
            bits.split(',')
                .map(|bit| match bit {
                    "false" => false,
                    "true" => true,
                    _ => panic!("invalid distribution bit: {text}"),
                })
                .collect()
        };
        let probability = rest.split_once('}').expect(text).0.parse::<f64>().unwrap();
        assert!(
            actual.insert(bits, probability).is_none(),
            "duplicate outcome: {text}"
        );
    }
    assert_eq!(actual.len(), expected.len(), "{text}");
    for &(bits, probability) in expected {
        let observed = actual.get(bits).expect(text);
        assert!((observed - probability).abs() < 1e-12, "{bits:?}: {text}");
    }
}

#[test]
fn selected_mixed_sources_keep_independent_distributions_and_scope() {
    let hth_zero = (2.0 + 2.0_f64.sqrt()) / 4.0;
    let hth_one = (2.0 - 2.0_f64.sqrt()) / 4.0;
    type Expected<'a> = &'a [(&'a [bool], f64)];
    let cases: &[(&str, Expected<'_>)] = &[
        ("eager-zero", &[(&[false], 1.0)]),
        ("bell-xor", &[(&[false, false], 0.5), (&[true, false], 0.5)]),
        (
            "pending-argument",
            &[(&[false, true], 0.5), (&[true, false], 0.5)],
        ),
        ("repeated-helper", &[(&[true, true], 1.0)]),
        ("unit-effect", &[(&[true], 1.0)]),
        ("static-fold", &[(&[false], 1.0)]),
        ("exact-phase", &[(&[false], hth_zero), (&[true], hth_one)]),
    ];
    for &(name, expected) in cases {
        for action in ["check", "run"] {
            let output = selected(action, &fixture("attempt-01", name), "main::main")
                .arg(format!("--lean-kernel={}", kernel().display()))
                .output()
                .unwrap();
            let text = result(output, action, true);
            scope(&text, "main::main", "raw");
            if action == "run" {
                distribution(&text, expected);
            }
        }
    }
}

#[test]
fn selected_static_fold_and_fresh_sampling_use_the_requested_instance() {
    for n in 0..=2 {
        let output = selected("run", &fixture("attempt-01", "static-fold"), "main::f")
            .arg(format!("--nat=n={n}"))
            .arg(format!("--lean-kernel={}", kernel().display()))
            .output()
            .unwrap();
        let text = result(output, "run", true);
        scope(&text, "main::f", "raw");
        distribution(&text, &[(&[n == 1], 1.0)]);
    }
    for (name, allowed) in [
        ("repeated-helper", vec!["true,true"]),
        ("pending-argument", vec!["false,true", "true,false"]),
    ] {
        let mut observed = Vec::new();
        for _ in 0..2 {
            let output = selected("sample", &fixture("attempt-01", name), "main::main")
                .args(["--shots=16", "--seed=37", "--ir-profile=raw"])
                .arg(format!("--lean-kernel={}", kernel().display()))
                .output()
                .unwrap();
            let text = result(output, "sample", true);
            scope(&text, "main::main", "raw");
            assert!(text.contains("\"rng\":\"splitmix64-v1\""), "{text}");
            let bits: Vec<_> = text
                .split("\"bits\":[")
                .skip(1)
                .map(|part| part.split_once(']').expect(&text).0)
                .collect();
            assert_eq!(bits.len(), 16, "{text}");
            assert!(bits.iter().all(|bits| allowed.contains(bits)), "{text}");
            observed.push(text);
        }
        assert_eq!(observed[0], observed[1], "seed replay: {name}");
    }
}

#[cfg(unix)]
struct LoggedKernel {
    files: SourceRoot,
}

#[cfg(unix)]
impl LoggedKernel {
    fn new() -> Self {
        use std::os::unix::fs::PermissionsExt;
        let files = SourceRoot::new("");
        files.write("native", "#!/bin/sh\nprintf '%s\\n' \"$1\" >> \"$QLEISLI_SELECTED_CALL_LOG\"\nif [ -n \"$QLEISLI_SELECTED_REAL_KERNEL\" ]; then exec \"$QLEISLI_SELECTED_REAL_KERNEL\" \"$@\"; fi\nexit 97\n");
        std::fs::set_permissions(
            files.0.join("native"),
            std::fs::Permissions::from_mode(0o700),
        )
        .unwrap();
        Self { files }
    }

    fn attach(&self, command: &mut Command, forward: bool) {
        let path = self.files.0.join("native");
        command
            .arg(format!("--lean-kernel={}", path.display()))
            .env("QLEISLI_KERNEL", &path)
            .env("QLEISLI_HIERARCHY_KERNEL", &path)
            .env("QLEISLI_SELECTED_CALL_LOG", self.files.0.join("calls"));
        if forward {
            command.env("QLEISLI_SELECTED_REAL_KERNEL", kernel());
        } else {
            command.env_remove("QLEISLI_SELECTED_REAL_KERNEL");
        }
    }

    fn calls(&self) -> Vec<String> {
        match std::fs::read_to_string(self.files.0.join("calls")) {
            Ok(text) => text.lines().map(str::to_owned).collect(),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => vec![],
            Err(error) => panic!("cannot read native calls: {error}"),
        }
    }
}

#[test]
#[cfg(unix)]
fn selected_raw_preflight_rejects_open_arguments_and_unsupported_work_before_native() {
    let unit = Path::new(env!("CARGO_MANIFEST_DIR")).join(
        "tests/fixtures/authoring_sessions/selected-source-cli-v030/attempt-01/unit-parameter/main.qli",
    );
    let bit = SourceRoot::new("pub unitary fn f(b: Bit) -> Bit { b }");
    let quantum = SourceRoot::new("pub unitary fn f(q: Q<Bit>) -> Q<Bit> { q }");
    // Q<Unit> is supported by Raw checking but is still an open runtime
    // argument; its zero wire count does not turn it into a closed entry.
    let quantum_unit = SourceRoot::new("pub unitary fn f(q: Q<Unit>) -> Q<Unit> { q }");
    let returned_quantum =
        SourceRoot::new("use std::quantum::init0; pub iso fn f() -> Q<Bit> { init0() }");
    let paths = [
        unit,
        bit.0.join("main.qli"),
        quantum.0.join("main.qli"),
        quantum_unit.0.join("main.qli"),
        returned_quantum.0.join("main.qli"),
    ];
    for path in &paths {
        for action in ["run", "sample"] {
            let log = LoggedKernel::new();
            let mut command = selected(action, path, "main::f");
            command.arg("--ir-profile=raw");
            if action == "sample" {
                command.args(["--shots=1", "--seed=0"]);
            }
            log.attach(&mut command, false);
            let text = result(command.output().unwrap(), action, false);
            assert!(text.contains("\"code\":\"unsupported\""), "{text}");
            assert!(log.calls().is_empty(), "{path:?}: {:?}", log.calls());
        }
    }
    {
        let name = "fine-phase";
        let log = LoggedKernel::new();
        let mut command = selected("check", &fixture("counterexamples", name), "main::main");
        command.arg("--ir-profile=raw");
        log.attach(&mut command, false);
        let text = result(command.output().unwrap(), "check", false);
        assert!(text.contains("\"code\":\"unsupported\""), "{text}");
        assert!(
            text.contains("\"primary\":{") && text.contains("main.qli"),
            "{text}"
        );
        assert!(log.calls().is_empty(), "{name}: {:?}", log.calls());
    }
    // Closed providers and ordinary empty Bits now preserve their source call
    // graphs. Both historical counterexample sources remain unchanged.
    for (name, expected) in [("provider", &[true][..]), ("packed-bits", &[][..])] {
        for action in ["check", "run"] {
            let log = LoggedKernel::new();
            let mut command = selected(action, &fixture("counterexamples", name), "main::main");
            command.arg("--ir-profile=raw");
            log.attach(&mut command, true);
            let text = result(command.output().unwrap(), action, true);
            scope(&text, "main::main", "raw");
            assert!(!log.calls().is_empty());
            if action == "run" {
                distribution(&text, &[(expected, 1.0)]);
            }
        }
    }
}

#[test]
#[cfg(unix)]
fn selected_basis_and_request_conflicts_reject_before_native_or_request_reads() {
    for action in ["run", "sample"] {
        let log = LoggedKernel::new();
        let mut command = selected(action, &fixture("attempt-01", "eager-zero"), "main::main");
        command.arg("--basis=0");
        if action == "sample" {
            command.args(["--shots=1", "--seed=0"]);
        }
        log.attach(&mut command, false);
        let text = result(command.output().unwrap(), action, false);
        assert!(text.contains("basis"), "{text}");
        assert!(log.calls().is_empty());
    }
    for option in [
        "--request=absent-request.json",
        "--qpe-provider=absent-provider.json",
    ] {
        let log = LoggedKernel::new();
        let mut command = selected("check", &fixture("attempt-01", "exact-phase"), "main::f");
        command.args(["--ir-profile=raw", option]);
        log.attach(&mut command, false);
        let text = result(command.output().unwrap(), "check", false);
        assert!(text.contains("\"code\":\"usage\""), "{text}");
        assert!(log.calls().is_empty());
    }
}

#[test]
#[cfg(unix)]
fn selected_module_checking_and_binding_errors_cannot_start_native() {
    for (unused, code) in [
        ("unitary fn unused() -> Bit { () }", "type"),
        (
            "unitary fn unused(q: Q<Bit>) -> (Q<Bit>,Q<Bit>) { (q,q) }",
            "ownership",
        ),
    ] {
        let source = format!("pub unitary fn f() -> Bit {{ 1 }}\n{unused}\n");
        let files = SourceRoot::new(&source);
        let log = LoggedKernel::new();
        let mut command = selected("check", &files.0.join("main.qli"), "main::f");
        log.attach(&mut command, false);
        let text = result(command.output().unwrap(), "check", false);
        assert!(text.contains(&format!("\"code\":\"{code}\"")), "{text}");
        assert!(
            text.contains("\"primary\":{\"module\":\"main\"") && text.contains("main.qli"),
            "{text}"
        );
        assert!(log.calls().is_empty(), "unused declaration: {text}");
    }
    let files = SourceRoot::new("pub unitary fn f() -> Bit { 1 }");
    for (case, code) in [
        ("project-and-modules", "usage"),
        ("kernel-alias", "usage"),
        ("unknown-natural", "static"),
        ("malformed-natural", "usage"),
    ] {
        let log = LoggedKernel::new();
        let mut command = selected("check", &files.0.join("main.qli"), "main::f");
        match case {
            "project-and-modules" => {
                command.arg(&files.0);
            }
            "kernel-alias" => {
                command.arg("--kernel=another-kernel");
            }
            "unknown-natural" => {
                command.arg("--nat=bad=1");
            }
            "malformed-natural" => {
                command.arg("--nat=n=bad");
            }
            _ => unreachable!(),
        }
        // Also supplies --lean-kernel, so the alias case really is a duplicate.
        log.attach(&mut command, false);
        let text = result(command.output().unwrap(), "check", false);
        assert!(
            text.contains(&format!("\"code\":\"{code}\"")),
            "{case}: {text}"
        );
        assert!(log.calls().is_empty(), "{case}: {text}");
    }
}

#[test]
fn selected_open_signature_checks_and_proposals_do_not_claim_closed_execution() {
    let files =
        SourceRoot::new("pub unitary fn f(b: Bit, q: Q<Bit>) -> (Bit,Q<Bit>) { (not b,q) }");
    let output = selected("check", &files.0.join("main.qli"), "main::f")
        .arg(format!("--lean-kernel={}", kernel().display()))
        .output()
        .unwrap();
    let text = result(output, "check", true);
    scope(&text, "main::f", "raw");
    let path = files.0.join("untrusted.qirf");
    let output = selected("emit-proposal", &files.0.join("main.qli"), "main::f")
        .arg(format!("--output={}", path.display()))
        .env("QLEISLI_KERNEL", files.0.join("absent-kernel"))
        .env("QLEISLI_HIERARCHY_KERNEL", files.0.join("absent-kernel"))
        .output()
        .unwrap();
    let text = result(output, "emit-proposal", true);
    assert!(text.contains("\"status\":\"untrusted-proposal\""), "{text}");
    assert!(!text.contains("\"source_steps_checked\":true"), "{text}");
    assert!(!text.contains("\"scope\":\"native-validity\""), "{text}");
    assert!(path.is_file());
}

#[test]
#[cfg(unix)]
fn selected_caller_h_request_rejects_x_once_without_a_raw_retry() {
    let h = "use std::quantum::h; pub unitary fn f(q: Q<Bit>) -> Q<Bit> { h(q) }";
    let x = "use std::quantum::x; pub unitary fn f(q: Q<Bit>) -> Q<Bit> { x(q) }";
    // Choose the H request before creating either CLI candidate. Producer
    // consistency for X must not replace this caller-selected equation.
    let h_request = ParsedProgram::parse(BTreeMap::from([("main".into(), h.into())]))
        .unwrap()
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower()
        .unwrap()
        .comparison_request()
        .to_vec();
    let files = SourceRoot::new(h);
    std::fs::write(files.0.join("h.request.json"), h_request).unwrap();
    for (source, supplied, success) in [(h, true, true), (x, false, true), (x, true, false)] {
        files.write("main.qli", source);
        let log = LoggedKernel::new();
        let mut command = selected("check", &files.0.join("main.qli"), "main::f");
        if supplied {
            command.arg(format!(
                "--request={}",
                files.0.join("h.request.json").display()
            ));
        }
        log.attach(&mut command, true);
        let text = result(command.output().unwrap(), "check", success);
        assert_eq!(log.calls(), ["--hierarchy-request-pending"], "{text}");
        if success {
            scope(&text, "main::f", "hierarchy");
            let expected = if supplied {
                "caller-composition"
            } else {
                "producer-consistency"
            };
            assert!(
                text.contains(&format!("\"scope\":\"{expected}\"")),
                "{text}"
            );
        } else {
            assert!(text.contains("\"code\":\"contract\""), "{text}");
            assert!(text.contains("native checker rejected"), "{text}");
        }
    }
}

fn amplitudes(text: &str, expected: &[[f64; 2]]) {
    let rows = text
        .split_once("\"amplitudes\":[")
        .expect(text)
        .1
        .split_once("]]")
        .expect(text)
        .0;
    let actual: Vec<f64> = rows
        .split(['[', ']', ','])
        .map(str::trim)
        .filter(|part| !part.is_empty())
        .map(|part| part.parse().expect(text))
        .collect();
    let expected: Vec<_> = expected.iter().flatten().copied().collect();
    assert_eq!(actual.len(), expected.len(), "{text}");
    for (a, e) in actual.iter().zip(expected) {
        assert!((a - e).abs() < 1e-12, "{text}");
    }
}

#[test]
fn selected_auto_keeps_hierarchy_fine_phase_and_zero_width_bits_axes() {
    let angle = std::f64::consts::PI / 8.0;
    let files = SourceRoot::new(
        "pub unitary fn f(q: Q<Bits<0>>, a: Q<Bit>) -> (Q<Bit>,Q<Bits<0>>) { (a,q) }",
    );
    for (path, expected) in [
        (
            fixture("counterexamples", "fine-phase"),
            [[0.0, 0.0], [angle.cos(), angle.sin()]],
        ),
        (files.0.join("main.qli"), [[0.0, 0.0], [1.0, 0.0]]),
    ] {
        let output = selected("run", &path, "main::f")
            .arg("--basis=1")
            .arg(format!("--lean-kernel={}", kernel().display()))
            .output()
            .unwrap();
        let text = result(output, "run", true);
        scope(&text, "main::f", "hierarchy");
        assert!(
            text.contains("\"scope\":\"producer-consistency\""),
            "{text}"
        );
        assert!(text.contains("\"quantum_bits\":1"), "{text}");
        amplitudes(&text, &expected);
    }
}

#[test]
#[cfg(unix)]
fn selected_tiny_qpe_keeps_the_fixed_provider_request_after_candidate_changes() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let module_paths = [
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
    ];
    // An explicitly authored closed provider: take the low bit, multiply |1>
    // by omega = exp(i*pi/4), preserve the empty rest owner, then put it back.
    // Existing composition requests also fix the identity/body/rename shell and
    // literal interface labels. Labels 115..119 were inspected in the original
    // n=1,m=1 proposal; the requested phase and equations below are fixed here,
    // never read from either candidate's proposed meanings or generated request.
    let port = |owner: u32, basis: &str, axes: &str| {
        format!("{{\"owner\":{owner},\"basis\":[{basis}],\"axes\":{axes}}}")
    };
    let side = |ports: &[&str]| format!("{{\"quantum\":[{}],\"classical\":[]}}", ports.join(","));
    let input = port(115, r#"{"tag":"bits","width":1}"#, "[0]");
    let bit = port(116, r#"{"tag":"bit"}"#, "[0]");
    let rest = port(117, r#"{"tag":"bits","width":0}"#, "[]");
    let phased = port(118, r#"{"tag":"bit"}"#, "[0]");
    let output = port(119, r#"{"tag":"bits","width":1}"#, "[0]");
    let a = side(&[&input]);
    let b = side(&[&bit]);
    let c = side(&[&rest]);
    let d = side(&[&phased]);
    let e = side(&[&output]);
    let bc = side(&[&bit, &rest]);
    let dc = side(&[&phased, &rest]);
    let header = |before: &str, after: &str| format!("{{\"inputs\":{before},\"outputs\":{after}}}");
    let meaning = |before: &str, after: &str, body: &str| {
        format!(
            "{{\"interface\":{},\"body\":{body}}}",
            header(before, after)
        )
    };
    let rename = r#"{"tag":"rewire","permutation":{"owners":[0],"axes":[0],"classical":[]}}"#;
    let meanings = [
        meaning(
            &a,
            &bc,
            r#"{"tag":"structural","operation":{"tag":"take_bit","width":1,"position":0}}"#,
        ),
        meaning(&b, &b, r#"{"tag":"phase","j":1,"k":3}"#),
        meaning(&b, &d, rename),
        meaning(&b, &d, r#"{"tag":"sequence","children":[1,2]}"#),
        meaning(
            &c,
            &c,
            r#"{"tag":"rewire","permutation":{"owners":[0],"axes":[],"classical":[]}}"#,
        ),
        meaning(&bc, &dc, r#"{"tag":"tensor","left":3,"right":4}"#),
        meaning(
            &dc,
            &e,
            r#"{"tag":"structural","operation":{"tag":"put_bit","width":1,"position":0}}"#,
        ),
        meaning(&a, &e, r#"{"tag":"sequence","children":[0,5,6]}"#),
        meaning(&a, &a, rename),
        meaning(&e, &a, rename),
        meaning(&a, &a, r#"{"tag":"sequence","children":[8,7,9]}"#),
    ];
    let provider = format!(
        "{{\"format\":\"qleisli.hierarchy-request\",\"version\":1,\"profile\":\"qpe-dyadic8-v1\",\"kind\":\"equation\",\"effect\":\"unitary\",\"interface\":{},\"meanings\":[{}],\"entry\":10}}",
        header(&a, &a),
        meanings.join(",")
    );
    // This bounded regression retains its historical Fourier implementation.
    // Translate only its retired parameter header for the current parser.
    let fourier_text = common::current_source_text("corpus/sized/qualtran_qft/fourier.qli");
    let old_header = "fourier[static n: Nat]";
    assert_eq!(fourier_text.matches(old_header).count(), 1);
    let fourier = SourceRoot::new(&fourier_text.replacen(old_header, "fourier[const n: Nat]", 1));
    let files = SourceRoot::new("");
    let requested = files.0.join("fixed-provider.request.json");
    std::fs::write(&requested, provider).unwrap();
    for (action, j, success) in [("check", 1, true), ("run", 1, true), ("check", 2, false)] {
        let log = LoggedKernel::new();
        let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
        command
            .args([
                "--format=json",
                action,
                "--entry=measurement::qpe",
                "--nat=n=1",
                "--nat=m=1",
                "--operation=U=evolution::evolve",
                "--operation-nat=U.n=1",
                "--operation-nat=U.d=3",
            ])
            .arg(format!("--operation-nat=U.j={j}"))
            .arg(format!("--qpe-provider={}", requested.display()));
        if action == "run" {
            command.arg("--basis=1");
        }
        for (name, path) in module_paths {
            let current = if name == "fourier" {
                fourier.0.join("main.qli")
            } else {
                common::current_namespace_fixture(&root.join(path))
            };
            command.arg(format!("--module={name}={}", current.display()));
        }
        log.attach(&mut command, true);
        let text = result(command.output().unwrap(), action, success);
        assert_eq!(log.calls(), ["--qpe-instrument-pending"], "{text}");
        if success {
            scope(&text, "measurement::qpe", "hierarchy");
            assert!(text.contains("\"scope\":\"named-qpe\""), "{text}");
            assert!(
                text.contains("\"request_origin\":\"caller-provider\""),
                "{text}"
            );
            if action == "run" {
                // From H-control(diag(1,omega))-H on phase |0>, target |1>:
                // each residual target-|1> amplitude is (1 +/- omega)/2.
                // Compare the full complex branches without phase alignment.
                let rows = text
                    .split_once("\"branches\":")
                    .expect(&text)
                    .1
                    .split_once(",\"verification\"")
                    .expect(&text)
                    .0;
                let observed: Vec<f64> = rows
                    .split(['[', ']', ','])
                    .map(str::trim)
                    .filter(|value| !value.is_empty())
                    .map(|value| value.parse().expect(&text))
                    .collect();
                let t = std::f64::consts::FRAC_1_SQRT_2;
                let expected = [
                    0.0,
                    0.0,
                    (1.0 + t) / 2.0,
                    t / 2.0,
                    0.0,
                    0.0,
                    (1.0 - t) / 2.0,
                    -t / 2.0,
                ];
                assert_eq!(observed.len(), expected.len(), "{text}");
                for (actual, expected) in observed.iter().zip(expected) {
                    assert!((actual - expected).abs() < 1e-12, "{text}");
                }
            }
        } else {
            assert!(text.contains("\"code\":\"contract\""), "{text}");
            assert!(text.contains("native checker rejected"), "{text}");
        }
    }
}

#[test]
#[cfg(unix)]
fn retired_sized_prefix_reports_migration_without_source_or_native_work() {
    let logger = LoggedKernel::new();
    let files = SourceRoot::new("not valid source syntax");
    let output_path = files.0.join("must-not-be-emitted.json");
    for action in ["check", "run", "sample", "emit-proposal"] {
        for format_position in [None, Some(0), Some(2)] {
            let mut args = vec!["sized".to_string(), action.to_string()];
            if let Some(position) = format_position {
                args.insert(position, "--format=json".into());
            }
            args.extend([
                "--entry=main::main".into(),
                format!("--module=main={}", files.0.join("main.qli").display()),
                format!("--output={}", output_path.display()),
            ]);
            let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
            command.args(args);
            logger.attach(&mut command, false);
            let output = command.output().unwrap();
            assert_eq!(output.status.code(), Some(2), "{output:?}");
            let message = if format_position.is_some() {
                let text = result(output, "sized", false);
                assert!(text.contains("\"code\":\"usage\""), "{text}");
                text
            } else {
                assert!(output.stdout.is_empty(), "{output:?}");
                String::from_utf8(output.stderr).unwrap()
            };
            assert!(message.contains("sized command was removed"), "{message}");
            assert!(message.contains("--entry=MODULE::FUNCTION"), "{message}");
            assert!(message.contains("qleisli help ecosystem"), "{message}");
            assert!(logger.calls().is_empty());
            assert!(!output_path.exists());
        }
    }
    let help = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .arg("--help")
        .output()
        .unwrap();
    assert!(help.status.success());
    assert!(!String::from_utf8_lossy(&help.stdout).contains("qleisli sized"));
}

#[test]
fn control_access_recovery_keeps_text_json_categories_and_original_spans() {
    for call in ["h(&q)", "h(&mut q)", "h(&ctrl q)", "h(ctrl q)"] {
        let source = format!(
            "// π\r\nuse std::quantum::h;pub unitary fn main(q:Q<Bit>)->Q<Bit>{{{call};q}}"
        );
        let files = SourceRoot::new(&source);
        for json in [false, true] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
            command
                .args(["check", "--entry=main::main", "--ir-profile=raw"])
                .arg(format!(
                    "--module=main={}",
                    files.0.join("main.qli").display()
                ))
                .arg(format!("--lean-kernel={}", kernel().display()));
            if json {
                command.arg("--format=json");
            }
            let output = command.output().unwrap();
            assert!(!output.status.success(), "{output:?}");
            let text = if json {
                result(output, "check", false)
            } else {
                assert!(output.stdout.is_empty(), "{output:?}");
                String::from_utf8(output.stderr).unwrap()
            };
            let (code, start, end) = if call.contains('&') {
                assert!(text.contains("for quantum access"), "{text}");
                assert!(
                    text.contains("do not mechanically replace & with ctrl"),
                    "{text}"
                );
                let at = source.rfind('&').unwrap();
                ("parse", at, at + 1)
            } else {
                assert!(text.contains("not read-only access"), "{text}");
                assert!(text.contains("phase kickback is permitted"), "{text}");
                assert!(
                    text.contains("use excl for arbitrary coherent access"),
                    "{text}"
                );
                let at = source.rfind(call).unwrap();
                ("contract", at, at + call.len())
            };
            assert!(!text.contains("https://github.com"), "{text}");
            if json {
                assert!(text.contains(&format!("\"code\":\"{code}\"")), "{text}");
                assert!(
                    text.contains(&format!("\"start\":{start},\"end\":{end}")),
                    "{text}"
                );
            }
        }
    }
}

#[test]
fn selected_static_places_choose_raw_before_native_acceptance() {
    for call in [
        "x(excl q[1]);",
        "z(ctrl q[1]);",
        "phase_eighth(ctrl q[0..0]);",
    ] {
        let files = SourceRoot::new(&format!(
            "use std::quantum::{{x,z,phase_eighth}};pub unitary fn main(q:Q<Bits<3>>)->Q<Bits<3>>{{{call}q}}"
        ));
        for explicit in [false, true] {
            let mut command = selected("check", &files.0.join("main.qli"), "main::main");
            command.arg(format!("--lean-kernel={}", kernel().display()));
            if explicit {
                command.arg("--ir-profile=raw");
            }
            let text = result(command.output().unwrap(), "check", true);
            scope(&text, "main::main", "raw");
        }
        let mut command = selected("check", &files.0.join("main.qli"), "main::main");
        command.args([
            "--ir-profile=hierarchy",
            "--lean-kernel=/missing/place-checker",
        ]);
        let text = result(command.output().unwrap(), "check", false);
        assert!(
            text.contains(if call.starts_with("x(") {
                "static place partitions"
            } else {
                "ctrl source access requires independently bound basis-sector evidence"
            }),
            "{text}"
        );
        assert!(text.contains("\"code\":\"unsupported\""), "{text}");
    }
}

#[test]
fn selected_raw_control_checks_without_weakening_emission() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/authoring_sessions/quantum-access-v030/attempt-04");
    for name in ["entangled", "kickback", "overlap"] {
        let source = path.join(name).join("main.qli");
        let mut command = selected("check", &source, "main::main");
        command
            .arg("--ir-profile=raw")
            .arg(format!("--lean-kernel={}", kernel().display()));
        let text = result(command.output().unwrap(), "check", name != "overlap");
        if name != "overlap" {
            scope(&text, "main::main", "raw");
        } else {
            assert!(text.contains("ownership"), "{text}");
        }
    }
    // Emitting a proposal is explicitly checker-free. It cannot hide the
    // original control obligation or acquire acceptance from another action.
    let output = std::env::temp_dir().join(format!(
        "qleisli-control-emission-{}.json",
        std::process::id()
    ));
    let mut command = selected(
        "emit-proposal",
        &path.join("entangled/main.qli"),
        "main::main",
    );
    command
        .arg("--ir-profile=raw")
        .arg(format!("--output={}", output.display()))
        .env_remove("QLEISLI_KERNEL");
    let text = result(command.output().unwrap(), "emit-proposal", false);
    assert!(text.contains("unsupported"), "{text}");
    assert!(!output.exists());
}
