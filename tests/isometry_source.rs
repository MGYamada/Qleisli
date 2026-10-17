//! Bounded public-source preparation checks and independent amplitude expectations.
//! Native IR acceptance and these observations are not a source-preservation theorem.
//! Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
mod common;

use common::SourceRoot;
use qleisli::frontend::compile::ParsedProgram;
use qleisli::ir::Effect;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn fixture(name: &str) -> PathBuf {
    common::current_namespace_fixture(
        &Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/authoring_sessions/isometry-preparation-v030/attempt-01")
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn adopted_isometry_spelling_reaches_both_consumers_and_native_raw() {
    use qleisli::frontend::compile::{check_project, compile_project};
    let canonical = common::current_source_text(
        "tests/fixtures/authoring_sessions/isometry-vocabulary-v030/attempt-01/preparation.qli",
    );
    let canonical = canonical.as_str();
    let mut bodies = Vec::new();
    // An assertion does not seed inference or change the emitted isometry.
    for (text, diagnostic, asserted) in [
        (canonical.to_owned(), "main", Some(Effect::Isometry)),
        (
            canonical.replace("pub isometry fn main()", "fn inferred()")
                + "pub isometry fn main()->Q<Bit>{inferred()}",
            "inferred",
            None,
        ),
    ] {
        let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), text.clone())])).unwrap();
        let fact = parsed
            .function_effect(&format!("main::{diagnostic}"))
            .unwrap();
        assert_eq!(fact.inferred(), Effect::Isometry);
        assert_eq!(fact.asserted(), asserted);
        assert_eq!(
            parsed.public_function_effect("main::main"),
            Some(Effect::Isometry)
        );
        let raw = parsed
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap()
            .lower_raw()
            .unwrap();
        let checker = qleisli::interchange::native::Kernel::new(kernel());
        let accepted = checker.accept(raw.proposal()).unwrap();
        raw.validate_source_steps(&accepted).unwrap();
        assert_eq!(accepted.raw().declared_effect, Effect::Isometry);
        assert!(accepted.raw().quantum_inputs.is_empty());
        assert_eq!(accepted.raw().quantum_outputs.len(), 1);
        assert!(matches!(
            accepted.raw().operations.as_slice(),
            [qleisli::ir::RawOp::PackUnit { .. }, qleisli::ir::RawOp::LiftBasis { output_wires, table, .. }]
                if output_wires.len() == 1 && table == &[0]
        ));
        for version in [
            qleisli::interchange::Version::V1,
            qleisli::interchange::Version::V2,
        ] {
            let bytes = qleisli::interchange::export(&accepted, None, version).unwrap();
            // Existing versioned transport retains its original spelling.
            assert!(String::from_utf8_lossy(&bytes).contains("\"declared_effect\":\"iso\""));
            checker.check(&bytes, None).unwrap();
        }
        bodies.push(accepted.raw().clone());
        // The finite entry contract is a closed classical result. Keep that
        // explicit adapter separate from the original quantum-result source.
        let adapter = format!(
            "{} pub observe fn main()->Bit{{measure_z(produce())}}",
            text.replace("fn main()", "fn produce()")
        );
        let root = SourceRoot::new(&adapter);
        check_project(&root.0).unwrap();
        let observed = compile_project(&root.0).unwrap();
        let distribution =
            qleisli::sim::run_closed(&observed, qleisli::sim::SimulationLimits::default()).unwrap();
        assert_eq!(distribution[&vec![false]], 1.0);
    }
    assert_eq!(bodies[0], bodies[1]);
}

#[test]
fn retired_iso_reports_one_exact_migration_span_before_native_checking() {
    use qleisli::frontend::compile::check_project_with_kernel;
    use qleisli::frontend::project::SourcePolicy;
    use qleisli::interchange::native::Kernel;
    let source = "// λ\r\niso fn f() -> Unit { () }";
    let error = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
    assert_eq!(error.code(), "parse");
    assert_eq!(&source[error.span().start..error.span().end], "iso");
    assert!(error.message().contains("was renamed to `isometry`"));
    let root = SourceRoot::new(source);
    let missing = Kernel::new(root.0.join("absent-kernel"));
    let diagnostic =
        check_project_with_kernel(&root.0, SourcePolicy::default(), &missing).unwrap_err();
    assert_eq!(diagnostic.code, "parse");
    let location = diagnostic.primary.unwrap();
    assert_eq!((location.line, location.column), (2, 1));
    assert_eq!(&source[location.span.start..location.span.end], "iso");
    assert_eq!(diagnostic.message, error.message());
    // Trivia and longer ordinary identifiers are not retired source tokens.
    ParsedProgram::parse(BTreeMap::from([(
        "main".into(),
        "/* iso fn */ fn isotope(iso_value: Bit) -> Bit { iso_value }".into(),
    )]))
    .unwrap();
}

#[test]
fn adopted_isometry_assertion_does_not_override_observation_or_seed_inference() {
    use qleisli::frontend::compile::{ErrorCode, check_project};
    let observing = common::current_source_text(
        "tests/fixtures/authoring_sessions/isometry-vocabulary-v030/attempt-01/observing-assertion.qli",
    );
    let observing = observing.as_str();
    let error =
        ParsedProgram::parse(BTreeMap::from([("main".into(), observing.into())])).unwrap_err();
    assert_eq!(error.code(), "effect");
    assert!(error.message().contains("body effect `Observe`"));
    assert_eq!(
        check_project(&SourceRoot::new(observing).0)
            .unwrap_err()
            .code,
        ErrorCode::Effect
    );
    let pure = "pub isometry fn main(q:Q<Bit>)->Q<Bit>{q}";
    let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), pure.into())])).unwrap();
    let fact = parsed.function_effect("main::main").unwrap();
    assert_eq!(fact.inferred(), Effect::Unitary);
    assert_eq!(fact.asserted(), Some(Effect::Isometry));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn public_isometry_uses_empty_readout_without_reclassifying_its_unitary_body() {
    use qleisli::frontend::compile::HierarchyEligibility;
    use qleisli::interchange::{hierarchical, native};

    let source = "
        pub isometry fn entry(q:Q<(Unit,Bit)>)->Q<Bit>{
            let(u,b)=split(q);finish(u);global_phase_eighth(b)
        }";
    let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap();
    let fact = parsed.function_effect("main::entry").unwrap();
    assert_eq!(fact.inferred(), Effect::Unitary);
    assert_eq!(fact.public_effect(), Some(Effect::Isometry));
    let elaborated = parsed
        .instantiate("main::entry", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    assert_eq!(
        elaborated.definitions()[elaborated.root()].effect(),
        "unitary"
    );
    assert!(matches!(
        elaborated.hierarchy_eligibility().unwrap(),
        HierarchyEligibility::Eligible
    ));

    let raw = elaborated.lower_raw().unwrap();
    let accepted = native::Kernel::new(kernel())
        .accept(raw.proposal())
        .unwrap();
    raw.validate_source_steps(&accepted).unwrap();
    assert_eq!(accepted.raw().declared_effect, Effect::Unitary);
    assert_eq!(accepted.derived_effect(), Effect::Unitary);
    let hierarchy = elaborated.lower().unwrap();
    assert!(hierarchy.is_instrument());
    let checked = hierarchical::Kernel::new(kernel())
        .check_instrument_native(hierarchy.payload(), hierarchy.comparison_request())
        .unwrap();
    hierarchy
        .validate_initialization_moves_native(&checked)
        .unwrap();

    // The open quantum input stays on the existing empty-readout adapter in
    // both automatic and explicit hierarchy selection. Preserve exact phase.
    let root = SourceRoot::new(source);
    for profile in ["auto", "hierarchy"] {
        for action in ["check", "run"] {
            let bases: &[usize] = if action == "run" { &[0, 1] } else { &[0] };
            for &basis in bases {
                let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
                command
                    .args(["--format=json", action, "--entry=main::entry"])
                    .arg(format!("--ir-profile={profile}"))
                    .arg(format!(
                        "--module=main={}",
                        root.0.join("main.qli").display()
                    ))
                    .arg(format!("--lean-kernel={}", kernel().display()));
                if action == "run" {
                    command.arg(format!("--basis={basis}"));
                }
                let text = result(command.output().unwrap(), action, true, true);
                hierarchy_scope(&text);
                if action == "check" {
                    assert!(text.contains("\"profile\":\"sized-isometry\""), "{text}");
                    assert!(!text.contains("sized-unitary"), "{text}");
                    assert!(!text.contains("sized-instrument"), "{text}");
                } else {
                    let mut expected = [[0.0; 2]; 2];
                    expected[basis] = [std::f64::consts::FRAC_1_SQRT_2; 2];
                    amplitudes(&text, &expected);
                    assert!(!text.contains("\"measured_bits\""), "{text}");
                }
            }
        }
    }

    // A public Observe bound still cannot select either pure hierarchy
    // adapter merely because its concrete implementation happens to be pure.
    let observing = source.replace("pub isometry fn", "pub observe fn");
    let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), observing)])).unwrap();
    assert_eq!(
        parsed.public_function_effect("main::entry"),
        Some(Effect::Observe)
    );
    let elaborated = parsed
        .instantiate("main::entry", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    assert_eq!(
        elaborated.definitions()[elaborated.root()].effect(),
        "unitary"
    );
    let HierarchyEligibility::Ineligible(error) = elaborated.hierarchy_eligibility().unwrap()
    else {
        panic!("public Observe cannot select an empty-readout pure adapter");
    };
    assert_eq!(error.code(), "unsupported");
    assert!(error.message().contains("matching checked public effect"));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn adopted_isometry_cli_retains_scalar_phase_and_the_actual_scope() {
    let text = "use std::state::init0;pub isometry fn main()->Q<Bit>{global_phase_eighth(init0())}";
    let root = SourceRoot::new(text);
    let output = Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .args(["--format=json", "run", "--entry=main::main"])
        .arg(format!(
            "--module=main={}",
            root.0.join("main.qli").display()
        ))
        .arg(format!("--lean-kernel={}", kernel().display()))
        .output()
        .unwrap();
    let text = result(output, "run", true, true);
    assert!(text.contains("\"source_meaning_verified\":false"));
    assert!(text.contains("\"execution_authority\":\"checked-produced-ir\""));
    amplitudes(&text, &[[std::f64::consts::FRAC_1_SQRT_2; 2], [0.0, 0.0]]);
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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
    ] {
        let source = std::fs::read_to_string(fixture(name)).unwrap();
        let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), source)])).unwrap();
        assert_eq!(
            parsed.function_effect("main::entry").unwrap().inferred(),
            Effect::Isometry,
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn isometry_cli_run_retains_preparation_phase_and_zero_width_owner() {
    let omega = [std::f64::consts::FRAC_1_SQRT_2; 2];
    for (name, coefficient) in [
        ("closed-zero", [1.0, 0.0]),
        ("unit-zero", [1.0, 0.0]),
        ("retained-unit", [1.0, 0.0]),
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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
    // The public Isometry contract does not grant an observation API or
    // sampled classical outcomes.
    let files = SourceRoot::new("");
    let absent = files.0.join("absent-kernel");
    for name in ["unit-zero", "unit-phase"] {
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
fn public_observe_contract_does_not_select_a_sharper_pure_hierarchy() {
    let source = std::fs::read_to_string(fixture("empty-classical")).unwrap();
    let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), source)])).unwrap();
    assert_eq!(
        parsed.function_effect("main::entry").unwrap().inferred(),
        Effect::Isometry
    );
    assert_eq!(
        parsed.public_function_effect("main::entry"),
        Some(Effect::Observe)
    );
    let elaborated = parsed
        .instantiate("main::entry", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let qleisli::frontend::compile::HierarchyEligibility::Ineligible(error) =
        elaborated.hierarchy_eligibility().unwrap()
    else {
        panic!("public Observe cannot be sharpened to the pure hierarchy profile");
    };
    assert_eq!(error.code(), "unsupported");
    assert!(error.message().contains("matching checked public effect"));
    let files = SourceRoot::new("");
    let absent = files.0.join("must-not-start-a-native-checker");
    for action in ["check", "run"] {
        for json in [false, true] {
            let output = selected(action, "empty-classical", json)
                .arg("--ir-profile=hierarchy")
                .arg(format!("--lean-kernel={}", absent.display()))
                .output()
                .unwrap();
            let text = result(output, action, json, false);
            assert!(text.contains("matching checked public effect"), "{text}");
            assert!(!text.contains("\"amplitudes\""), "{text}");
            if json {
                assert!(text.contains("\"code\":\"unsupported\""), "{text}");
            }
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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
