//! Bounded public-source preparation checks and independent amplitude expectations.
//! Native IR acceptance and these observations are not a source-preservation theorem.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
mod common;

use common::SourceRoot;
use qleisli::frontend::compile::ParsedProgram;
use qleisli::ir::Effect;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/authoring_sessions/isometry-preparation-v030/attempt-01")
        .join(name)
        .join("main.qli")
}

fn kernel() -> PathBuf {
    std::fs::canonicalize(
        std::env::var_os("QLEISLI_KERNEL")
            .or_else(|| std::env::var_os("QLEISLI_HIERARCHY_KERNEL"))
            .expect("select the separately built, audited native kernel"),
    )
    .unwrap()
}

fn selected(action: &str, name: &str, json: bool) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
    if json {
        command.arg("--format=json");
    }
    command
        .arg(action)
        .arg("--entry=main::entry")
        .arg(format!("--module=main={}", fixture(name).display()));
    command
}

fn result(output: Output, action: &str, json: bool, success: bool) -> String {
    assert_eq!(output.status.success(), success, "{output:?}");
    if success || json {
        assert!(output.stderr.is_empty(), "{output:?}");
        let text = String::from_utf8(output.stdout).unwrap();
        if json {
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
            assert!(
                text.contains(if success {
                    "\"diagnostics\":[]"
                } else {
                    "\"result\":null"
                }),
                "{text}"
            );
        }
        text
    } else {
        assert!(output.stdout.is_empty(), "{output:?}");
        String::from_utf8(output.stderr).unwrap()
    }
}

fn hierarchy_scope(text: &str) {
    for expected in [
        "\"entry\":\"main::entry\"",
        "\"ir_profile\":\"hierarchy\"",
        "\"source_check_scope\":\"all-supplied-module-declarations\"",
        "\"native_check_scope\":\"selected-specialization\"",
        "\"scope\":\"producer-consistency\"",
        "\"request_origin\":\"producer\"",
        "\"source_meaning_verified\":false",
        "\"execution_authority\":\"checked-produced-ir\"",
    ] {
        assert!(text.contains(expected), "missing {expected}: {text}");
    }
    assert!(!text.contains("\"source_steps_checked\":true"), "{text}");
}

fn amplitudes(text: &str, expected: &[[f64; 2]]) {
    // Read documented complex output rows, without taking any expected value
    // from the producer's comparison request or another execution profile.
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
fn isometry_cli_check_preserves_inferred_effect_and_actual_verification_scope() {
    for name in [
        "closed-zero",
        "unit-zero",
        "unit-phase",
        "fresh-unit-phase",
        "caller-frame",
        "helper-phase",
        "retained-unit",
        "empty-classical",
    ] {
        let source = std::fs::read_to_string(fixture(name)).unwrap();
        let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), source)])).unwrap();
        assert_eq!(
            parsed.function_effect("main::entry").unwrap().inferred(),
            Effect::Iso,
            "{name}"
        );
        for json in [false, true] {
            let output = selected("check", name, json)
                .arg(format!("--lean-kernel={}", kernel().display()))
                .output()
                .unwrap();
            let text = result(output, "check", json, true);
            hierarchy_scope(&text);
            assert!(text.contains("\"profile\":\"sized-isometry\""), "{text}");
            assert!(!text.contains("sized-instrument"), "{text}");
        }
    }
    let source = std::fs::read_to_string(fixture("pure-control")).unwrap();
    let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), source)])).unwrap();
    assert_eq!(
        parsed.function_effect("main::entry").unwrap().inferred(),
        Effect::Unitary
    );
    for json in [false, true] {
        let output = selected("check", "pure-control", json)
            .arg(format!("--lean-kernel={}", kernel().display()))
            .output()
            .unwrap();
        let text = result(output, "check", json, true);
        hierarchy_scope(&text);
        assert!(text.contains("\"profile\":\"sized-unitary\""), "{text}");
    }
}

#[test]
fn isometry_cli_run_retains_preparation_phase_and_zero_width_owner() {
    let omega = [std::f64::consts::FRAC_1_SQRT_2; 2];
    for (name, coefficient) in [
        ("closed-zero", [1.0, 0.0]),
        ("unit-zero", [1.0, 0.0]),
        ("retained-unit", [1.0, 0.0]),
        ("empty-classical", [1.0, 0.0]),
        ("unit-phase", omega),
        ("fresh-unit-phase", omega),
    ] {
        for json in [false, true] {
            let output = selected("run", name, json)
                .arg("--basis=0")
                .arg(format!("--lean-kernel={}", kernel().display()))
                .output()
                .unwrap();
            let text = result(output, "run", json, true);
            hierarchy_scope(&text);
            assert!(text.contains("\"quantum_bits\":1"), "{text}");
            amplitudes(&text, &[coefficient, [0.0, 0.0]]);
            assert!(!text.contains("\"measured_bits\""), "{text}");
            assert!(!text.contains("\"distribution\""), "{text}");
        }
    }
}

#[test]
fn isometry_cli_run_keeps_the_retained_frame_axis_and_exact_scalar_phase() {
    let omega = [std::f64::consts::FRAC_1_SQRT_2; 2];
    for basis in 0..=1 {
        for (name, row, coefficient) in [
            ("helper-phase", basis, omega),
            ("caller-frame", 3 * basis, [1.0, 0.0]),
        ] {
            let mut expected = [[0.0, 0.0]; 4];
            // The retained input occupies the low axis. Fresh |0> occupies
            // the high axis, flipped by CNOT only for input |1>.
            expected[row] = coefficient;
            let output = selected("run", name, true)
                .arg(format!("--basis={basis}"))
                .arg(format!("--lean-kernel={}", kernel().display()))
                .output()
                .unwrap();
            let text = result(output, "run", true, true);
            hierarchy_scope(&text);
            assert!(text.contains("\"quantum_bits\":2"), "{text}");
            amplitudes(&text, &expected);
        }
    }
}

#[test]
fn isometry_cli_sampling_requires_actual_observation() {
    // Even an asserted Observe upper bound does not grant an observation API
    // to the inferred Iso entry, or produce sampled classical outcomes.
    let files = SourceRoot::new("");
    let absent = files.0.join("absent-kernel");
    for name in ["unit-zero", "unit-phase", "empty-classical"] {
        for json in [false, true] {
            let output = selected("sample", name, json)
                .args(["--shots=4", "--seed=37"])
                // Unsupported sampling is rejected before native invocation.
                .arg(format!("--lean-kernel={}", absent.display()))
                .output()
                .unwrap();
            let text = result(output, "sample", json, false);
            assert!(
                text.contains("sampling require an observing entry"),
                "{text}"
            );
            if json {
                assert!(text.contains("\"code\":\"unsupported\""), "{text}");
            }
            assert!(!text.contains("github.com"), "{text}");
            assert!(!text.contains("\"outcomes\""), "{text}");
        }
    }
}

#[test]
fn isometry_cli_explicit_raw_retains_its_actual_support_boundary() {
    for json in [false, true] {
        let output = selected("check", "unit-zero", json)
            .arg("--ir-profile=raw")
            .arg(format!("--lean-kernel={}", kernel().display()))
            .output()
            .unwrap();
        let text = result(output, "check", json, true);
        assert!(text.contains("\"ir_profile\":\"raw\""), "{text}");
        assert!(text.contains("\"source_steps_checked\":true"), "{text}");
        assert!(!text.contains("github.com"), "{text}");
        let output = selected("check", "closed-zero", json)
            .arg("--ir-profile=raw")
            .arg(format!("--lean-kernel={}", kernel().display()))
            .output()
            .unwrap();
        let text = result(output, "check", json, true);
        for expected in [
            "\"ir_profile\":\"raw\"",
            "\"scope\":\"native-validity\"",
            "\"request_origin\":\"none\"",
            "\"source_steps_checked\":true",
            "\"source_meaning_verified\":false",
        ] {
            assert!(text.contains(expected), "{text}");
        }
        assert!(!text.contains("sized-isometry"), "{text}");
        assert!(!text.contains("producer-consistency"), "{text}");
    }
}

#[test]
fn isometry_cli_missing_native_checker_never_falls_back() {
    let files = SourceRoot::new("");
    let absent = files.0.join("absent-kernel");
    for action in ["check", "run"] {
        for json in [false, true] {
            let output = selected(action, "unit-phase", json)
                .arg(format!("--lean-kernel={}", absent.display()))
                .env("QLEISLI_KERNEL", &absent)
                .env("QLEISLI_HIERARCHY_KERNEL", &absent)
                .output()
                .unwrap();
            let text = result(output, action, json, false);
            assert!(text.contains("native checker"), "{text}");
            assert!(text.contains("sized isometry profile"), "{text}");
            if json {
                assert!(text.contains("\"code\":\"io\""), "{text}");
            }
            assert!(!text.contains("\"status\":\"checked\""), "{text}");
            assert!(!text.contains("\"amplitudes\""), "{text}");
        }
    }
}

#[cfg(unix)]
#[test]
fn isometry_cli_incompatible_native_version_never_falls_back() {
    use std::os::unix::fs::PermissionsExt;
    let files = SourceRoot::new("");
    let wrapper = files.0.join("wrong-version-kernel");
    // Invoke the actual selected checker with an incompatible product version;
    // do not fabricate a successful receipt or reinterpret the source effect.
    std::fs::write(
        &wrapper,
        "#!/bin/sh\nexec \"$QLEISLI_TEST_KERNEL\" \"$1\" 0.0.0\n",
    )
    .unwrap();
    std::fs::set_permissions(&wrapper, std::fs::Permissions::from_mode(0o700)).unwrap();
    for action in ["check", "run"] {
        for json in [false, true] {
            let output = selected(action, "unit-phase", json)
                .arg(format!("--lean-kernel={}", wrapper.display()))
                .env("QLEISLI_TEST_KERNEL", kernel())
                .output()
                .unwrap();
            let text = result(output, action, json, false);
            assert!(text.contains("version"), "{text}");
            assert!(text.contains("sized isometry profile"), "{text}");
            assert!(!text.contains("\"status\":\"checked\""), "{text}");
            assert!(!text.contains("\"amplitudes\""), "{text}");
            assert!(!text.contains("github.com"), "{text}");
        }
    }
}
