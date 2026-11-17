mod common;

use common::SourceRoot;
use std::process::{Command, Output};

fn cli(args: &[&std::ffi::OsStr]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_qleisli"))
        .args(args)
        .output()
        .unwrap()
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn exact_zero_presentation_keeps_the_numerical_distribution() {
    let project = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/authoring_sessions/numerical-zero-presentation-v030/attempt-01");
    let numerical = cli(&["run".as_ref(), project.as_os_str()]);
    assert!(numerical.status.success(), "{numerical:?}");
    let annotated = cli(&[
        "run".as_ref(),
        project.as_os_str(),
        "--show-exact-zeros".as_ref(),
    ]);
    assert!(annotated.status.success(), "{annotated:?}");
    assert_eq!(annotated.stderr, numerical.stderr);
    let annotated = String::from_utf8(annotated.stdout).unwrap();
    let numerical = String::from_utf8(numerical.stdout).unwrap();
    assert_eq!(annotated.replace(" [exact zero]", ""), numerical);
    assert_eq!(annotated.matches(" [exact zero]").count(), 16);
    let residue = annotated
        .lines()
        .find_map(|line| line.strip_prefix("00001: "))
        .and_then(|value| value.strip_suffix(" [exact zero]"))
        .unwrap()
        .parse::<f64>()
        .unwrap();
    assert!(0.0 < residue && residue < 1e-28, "{residue}");
    let small = annotated
        .lines()
        .find_map(|line| line.strip_prefix("11110: "))
        .unwrap()
        .parse::<f64>()
        .unwrap();
    let expected = ((2.0 - std::f64::consts::SQRT_2) / 4.0).powi(4);
    assert!((small - expected).abs() < 1e-14, "{small}");

    let machine = cli(&[
        "run".as_ref(),
        project.as_os_str(),
        "--format=json".as_ref(),
    ]);
    assert!(machine.status.success(), "{machine:?}");
    let json = String::from_utf8(machine.stdout).unwrap();
    assert!(!json.contains("exact zero"), "{json}");
    let json_residue = json
        .split_once("\"bits\":[false,false,false,false,true],\"probability\":")
        .unwrap()
        .1
        .split_once('}')
        .unwrap()
        .0
        .parse::<f64>()
        .unwrap();
    assert!((json_residue - residue).abs() <= residue * 1e-12);

    let invalid = cli(&[
        "run".as_ref(),
        project.as_os_str(),
        "--show-exact-zeros".as_ref(),
        "--format=json".as_ref(),
    ]);
    assert_eq!(invalid.status.code(), Some(2), "{invalid:?}");
    assert!(String::from_utf8_lossy(&invalid.stdout).contains("\"code\":\"usage\""));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn exact_zero_presentation_keeps_numeric_output_when_branching_is_outside_its_profile() {
    let root = SourceRoot::new(
        "use std::state::init0; observe fn main() -> Bit { let b = measure_z(h(init0())); if b { 1 } else { 0 } }",
    );
    let numerical = cli(&["run".as_ref(), root.0.as_os_str()]);
    let requested = cli(&[
        "run".as_ref(),
        root.0.as_os_str(),
        "--show-exact-zeros".as_ref(),
    ]);
    assert!(numerical.status.success(), "{numerical:?}");
    assert!(requested.status.success(), "{requested:?}");
    assert_eq!(requested.stdout, numerical.stdout);
    assert!(String::from_utf8_lossy(&requested.stderr).contains(
        "exact-zero classification unavailable: outside the exact-zero terminal profile"
    ));
}

fn source_check_json(root: &std::path::Path, entry: &str, selected: bool, status: i32) -> String {
    let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
    command.args(["check", "--format=json"]);
    if selected {
        command
            .arg(format!("--entry=main::{entry}"))
            .arg(format!("--module=main={}", root.join("main.qli").display()));
    } else {
        command.arg(root);
    }
    let output = command.output().unwrap();
    assert_eq!(
        output.status.code(),
        Some(status),
        "{root:?}, entry {entry}, selected {selected}: {output:?}"
    );
    assert!(output.stderr.is_empty(), "{output:?}");
    String::from_utf8(output.stdout).unwrap()
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn ownership_boundary_json_preserves_rejection_scope_and_locations() {
    for (source, rejected, name_error, reason) in [
        (
            "pub unitary fn client(q:Q<Bit>)->Q<Bit>{drop(q);q}",
            "drop",
            true,
            Some(("unresolved_disposal", "if_live_quantum_owner")),
        ),
        (
            "pub unitary fn client(q:Q<Bit>)->Q<Bit>{drop(0);q}",
            "drop",
            true,
            Some(("unresolved_disposal", "if_live_quantum_owner")),
        ),
        (
            "pub unitary fn client(q:Q<Bit>)->Q<Bit>{missing(not q);q}",
            "missing",
            true,
            None,
        ),
        (
            "pub unitary fn client(owner:Q<Unit>)->Unit{()}",
            "owner",
            false,
            Some(("implicit_quantum_disposal", "live_quantum_owner")),
        ),
        (
            "use std::state::init0; pub unitary fn client(q:Q<Bit>)->Q<Bit>{clean(q,h){|a,scratch|(h(a),init0())}}",
            "scratch",
            false,
            Some(("clean_workspace_return", "live_quantum_owner")),
        ),
        (
            "use std::state::init0; pub unitary fn client(q:Q<Bit>,d:Q<Bit>)->(Q<Bit>,Q<Bit>){dirty(q,d,h){|a,scratch|(h(a),init0())}}",
            "scratch",
            false,
            Some(("dirty_workspace_return", "live_quantum_owner")),
        ),
        (
            "use std::state::init0; classical fn p(b:Bit)->Bit{b} pub unitary fn client(q:Q<Bit>)->Q<Bit>{with_computed(q,p){|scratch|init0()}}",
            "scratch",
            false,
            Some(("computed_workspace_return", "live_quantum_owner")),
        ),
    ] {
        let root = SourceRoot::new(source);
        for selected in [false, true] {
            let json = source_check_json(&root.0, "client", selected, 1);
            let code = match (name_error, selected) {
                (true, true) => "name",
                (true, false) => "unknown_name",
                (false, _) => "ownership",
            };
            assert!(json.contains(&format!("\"code\":\"{code}\"")), "{json}");
            let start = source.find(rejected).unwrap();
            let end = start + rejected.len();
            assert!(
                json.contains(&format!("\"start\":{start},\"end\":{end}")),
                "{json}"
            );
            if let Some((reason, applies_to)) = reason {
                assert!(
                    json.contains(&format!(
                        "\"ownership_boundary\":{{\"boundary\":\"affine_to_linear\",\"reason\":\"{reason}\",\"applies_to\":\"{applies_to}\"}}"
                    )),
                    "{json}"
                );
            } else {
                assert!(!json.contains("\"ownership_boundary\""), "{json}");
            }
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn control_flow_diagnostics_teach_the_original_boundary() {
    let attempts = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(
        "tests/fixtures/authoring_sessions/classical-quantum-control-diagnostics-v030/attempt-01",
    );
    for (case, rejected, reason, guidance) in [
        (
            "ordinary-if",
            "condition",
            "if_condition",
            "It preserves coherence between control sectors.",
        ),
        (
            "ordinary-match",
            "match selector { Choice::Left => 0, Choice::Right => 1 }",
            "match_selector",
            "Coherent `qmatch` selects checked controlled arms",
        ),
        (
            "coherent-qif",
            "condition",
            "qif_control",
            "To branch on an ordinary `Bit`, use ordinary `if`.",
        ),
        (
            "coherent-qmatch",
            "qmatch(selector, target) { 0 => h, 1 => h }",
            "qmatch_selector",
            "To branch on an ordinary `Bit`, use ordinary `if`.",
        ),
    ] {
        let project = attempts.join(case);
        let source = std::fs::read_to_string(project.join("main.qli")).unwrap();
        let start = source.rfind(rejected).unwrap();
        let end = start + rejected.len();
        let text = cli(&["check".as_ref(), project.as_os_str()]);
        assert_eq!(text.status.code(), Some(1), "{text:?}");
        assert!(text.stdout.is_empty(), "{text:?}");
        let text = String::from_utf8(text.stderr).unwrap();
        assert!(text.contains(guidance), "{text}");
        assert!(!text.contains("measure_z"), "{text}");
        for selected in [false, true] {
            let json = source_check_json(&project, "branch", selected, 1);
            let code = if selected { "type" } else { "type_mismatch" };
            assert!(json.contains(&format!("\"code\":\"{code}\"")), "{json}");
            assert!(
                json.contains(&format!("\"start\":{start},\"end\":{end}")),
                "{json}"
            );
            assert!(json.contains(guidance), "{json}");
            assert!(
                json.contains(&format!(
                    "\"control_flow_boundary\":{{\"boundary\":\"classical_quantum_control\",\"reason\":\"{reason}\"}}"
                )),
                "{json}"
            );
        }
    }
    let source = "pub fn branch() -> Bit { if h(0) { 1 } else { 0 } }";
    let inner = SourceRoot::new(source);
    let start = source.find("h(0)").unwrap();
    let end = start + "h(0)".len();
    for selected in [false, true] {
        let json = source_check_json(&inner.0, "branch", selected, 1);
        assert!(!json.contains("\"control_flow_boundary\""), "{json}");
        assert!(
            json.contains(&format!("\"start\":{start},\"end\":{end}")),
            "{json}"
        );
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn control_flow_corrections_check_with_explicit_observation_or_owner_threading() {
    let observed = SourceRoot::new(
        "use std::state::init0; observe fn main() -> Bit { let condition = measure_z(h(init0())); if condition { 1 } else { 0 } }",
    );
    assert!(source_check_json(&observed.0, "main", false, 0).contains("\"outcome\":\"ok\""));

    let coherent = SourceRoot::new(
        "use std::state::init0;
         unitary fn keep(q:Q<Bit>)->Q<Bit>{q}
         observe fn main() -> (Bit,Bit,Bit,Bit) {
             let (c,q) = qif(init0(),init0()) {0=>keep,1=>h};
             let (s,q) = qmatch(init0(),q) {0=>keep,1=>h};
             let q = qfor static i in 0..1 carry owner=q { yield owner; };
             let bit = for static i in 0..1 carry value=0 { yield not value; };
             (measure_z(c),measure_z(s),measure_z(q),bit)
         }",
    );
    let result = cli(&[
        "run".as_ref(),
        coherent.0.as_os_str(),
        "--format=json".as_ref(),
    ]);
    assert!(result.status.success(), "{result:?}");
    let json = String::from_utf8(result.stdout).unwrap();
    assert!(
        json.contains("\"distribution\":[{\"bits\":[false,false,false,true],\"probability\":1}]"),
        "{json}"
    );

    for (source, reason, guidance) in [
        (
            "pub unitary fn branch(q:Q<Bit>)->Q<Bit>{for static i in 0..1 carry owner=q{yield owner;}}",
            "for_carry",
            "use qfor static with explicit carry and yield",
        ),
        (
            "pub fn branch(x:Bit)->Bit{qfor static i in 0..1 carry value=x{yield value;}}",
            "qfor_carry",
            "use for static for ordinary values",
        ),
    ] {
        let root = SourceRoot::new(source);
        for selected in [false, true] {
            let json = source_check_json(&root.0, "branch", selected, 1);
            assert!(json.contains(guidance), "{json}");
            assert!(json.contains(&format!("\"reason\":\"{reason}\"")), "{json}");
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn native_transport_failures_use_the_closed_v1_project_code() {
    let root = SourceRoot::new("observe fn main()->Bit{1}");
    let artifact = root.0.join("valid.qirf");
    let emitted = cli(&[
        "emit-ir".as_ref(),
        root.0.as_os_str(),
        format!("--output={}", artifact.display()).as_ref(),
    ]);
    assert!(emitted.status.success(), "{emitted:?}");
    for command in ["check", "run", "sample", "emit-ir", "verify-ir"] {
        let mut process = Command::new(env!("CARGO_BIN_EXE_qleisli"));
        process
            .arg(command)
            .arg(if command == "verify-ir" {
                &artifact
            } else {
                &root.0
            })
            .arg("--format=json")
            .arg(format!("--lean-kernel={}", root.0.join("absent").display()));
        if command == "sample" {
            process.args(["--shots=1", "--seed=1"]);
        }
        if command == "verify-ir" {
            process.arg("--edition=2026");
        }
        if command == "emit-ir" {
            process.arg(format!(
                "--output={}",
                root.0.join("blocked.qirf").display()
            ));
        }
        let output = process.output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        let text = String::from_utf8(output.stdout).unwrap();
        assert!(text.contains("\"code\":\"project\""), "{command}: {text}");
        assert!(!text.contains("\"code\":\"io\"") && !text.contains("\"code\":\"kernel\""));
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn function_equation_mismatch_has_the_same_contract_code_in_text_and_json() {
    let root = SourceRoot::new(&common::current_source_text(
        "tests/fixtures/frontend_v030/ordinary-type-cutover/current/review_v029/contract_mismatch/main.qli",
    ));
    for json in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
        command.arg("check").arg(&root.0);
        if json {
            command.arg("--format=json");
        }
        let output = command.output().unwrap();
        assert_eq!(output.status.code(), Some(1));
        let text = String::from_utf8(if json { output.stdout } else { output.stderr }).unwrap();
        assert!(
            text.contains(if json {
                "\"code\":\"contract\""
            } else {
                ": contract:"
            }),
            "{text}"
        );
        assert!(text.contains("function semantic contract"), "{text}");
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn equation_counterexample_text_and_json_preserve_axis_order_and_phase() {
    let attempts = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/authoring_sessions/contract-counterexample-v030/attempt-01");
    for (project, message, input_column, output_row) in [
        (
            "permutation",
            "input |(0, 1)⟩, output |(1, 0)⟩: actual 0, expected 1",
            2,
            1,
        ),
        (
            "phase",
            "input |1⟩, output |1⟩: actual -1, expected i",
            1,
            1,
        ),
    ] {
        let root = attempts.join(project);
        let source = std::fs::read_to_string(root.join("main.qli")).unwrap();
        let start = source.find("apply_contract(").unwrap();
        let end = start + source[start..].find('\n').unwrap();
        let line = source[..start]
            .bytes()
            .filter(|&byte| byte == b'\n')
            .count()
            + 1;
        let output = cli(&["check".as_ref(), root.as_os_str()]);
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
        let text = String::from_utf8(output.stderr).unwrap();
        assert!(
            text.contains(&format!("main.qli:{line}:5: contract:")),
            "{text}"
        );
        assert!(text.contains(message), "{text}");
        assert!(
            !text.contains("input column") && !text.contains("1*i"),
            "{text}"
        );

        let output = cli(&["check".as_ref(), root.as_os_str(), "--format=json".as_ref()]);
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(output.stderr.is_empty(), "{output:?}");
        let json = String::from_utf8(output.stdout).unwrap();
        assert!(json.contains("\"code\":\"contract\""), "{json}");
        assert!(json.contains(message), "{json}");
        assert!(
            json.contains(&format!(
                "\"primary\":{{\"path\":\"main.qli\",\"start\":{start},\"end\":{end},\"line\":{line},\"column\":5}}"
            )),
            "{json}"
        );
        assert!(
            json.contains(&format!(
                "\"counterexample\":{{\"input_column\":{input_column},\"output_row\":{output_row}}}"
            )),
            "{json}"
        );
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn truncated_static_arguments_emit_one_located_json_parse_error() {
    for source in [
        "unitary fn f(q: Q<Bit>) -> Q<Bit> { g[",
        "unitary fn f(q: Q<Bit>) -> Q<Bit> { g[power(",
    ] {
        let root = SourceRoot::new(source);
        let end = source.len();
        let column = end + 1;
        for command in ["check", "run"] {
            let output = cli(&[
                command.as_ref(),
                root.0.as_os_str(),
                "--format=json".as_ref(),
            ]);
            assert_eq!(output.status.code(), Some(1), "{output:?}");
            assert!(output.stderr.is_empty(), "{output:?}");
            assert_eq!(
                String::from_utf8(output.stdout).unwrap(),
                format!(
                    "{{\"format\":\"qleisli.result\",\"version\":1,\"command\":\"{command}\",\"outcome\":\"error\",\"diagnostics\":[{{\"code\":\"parse\",\"severity\":\"error\",\"message\":\"expected a static operation description\",\"primary\":{{\"path\":\"main.qli\",\"start\":{end},\"end\":{end},\"line\":1,\"column\":{column}}},\"related\":[]}}],\"result\":null}}\n"
                )
            );
        }
    }
}

#[test]
fn retired_operation_diagnostics_preserve_utf8_crlf_spans_without_native_setup() {
    for (body, token, replacement) in [
        ("adjoint(U,q)", "adjoint", "adjoint(U)(q)"),
        ("g[repeat_op(2,U)](q)", "repeat_op", "power(U, k)"),
        ("repeat_static(2,U,q)", "repeat_static", "power(U, k)(q)"),
        ("inverse(U)(q)", "inverse", "adjoint(U)(q)"),
        ("g[inverse_op(U)](q)", "inverse_op", "adjoint(U)"),
        ("g[controlled_op(U)](q)", "controlled_op", "controlled(U)"),
    ] {
        let source = format!("// 位相\r\nunitary fn f(q:Q<Bit>)->Q<Bit>{{{body}}}");
        let root = SourceRoot::new(&source);
        let kernel = root.0.join("absent");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            // If parsing accidentally probes/spawns the checker, record it.
            root.write(
                "absent",
                "#!/bin/sh\nprintf called > \"$0.called\"\nexit 91\n",
            );
            std::fs::set_permissions(&kernel, std::fs::Permissions::from_mode(0o700)).unwrap();
        }
        let start = source.find(token).unwrap();
        let end = start + token.len();
        let column = source[source.find('\n').unwrap() + 1..start]
            .chars()
            .count()
            + 1;
        for command in ["check", "run"] {
            for json in [false, true] {
                let mut process = Command::new(env!("CARGO_BIN_EXE_qleisli"));
                process
                    .arg(command)
                    .arg(&root.0)
                    .arg(format!("--lean-kernel={}", kernel.display()));
                if json {
                    process.arg("--format=json");
                }
                let output = process.output().unwrap();
                assert_eq!(output.status.code(), Some(1));
                let text =
                    String::from_utf8(if json { output.stdout } else { output.stderr }).unwrap();
                assert!(
                    text.contains("is retired") && text.contains(replacement),
                    "{text}"
                );
                if json {
                    assert!(text.contains("\"code\":\"parse\""), "{text}");
                    assert!(
                        text.contains(&format!(
                            "\"start\":{start},\"end\":{end},\"line\":2,\"column\":{column}"
                        )),
                        "{text}"
                    );
                } else {
                    assert!(
                        text.contains(&format!("main.qli:2:{column}: parse:")),
                        "{text}"
                    );
                }
            }
        }
        assert!(!kernel.with_file_name("absent.called").exists());
    }
}

#[test]
fn quantum_surface_guidance_reaches_text_and_json_with_original_locations() {
    for (source, at, offset, width, guidance) in [
        (
            include_str!(
                "fixtures/authoring_sessions/parser-surface-diagnostics-v030/attempt-01/qlet/main.qli"
            ),
            "qlet next",
            0,
            "qlet".len(),
            "let owner = value;",
        ),
        (
            include_str!(
                "fixtures/authoring_sessions/parser-surface-diagnostics-v030/attempt-01/qif/main.qli"
            ),
            "qif c",
            "qif ".len(),
            1,
            "qif(control, target) { 0 => first, 1 => second }",
        ),
    ] {
        let source = format!("// 位相\r\n{}", source.replace('\n', "\r\n"));
        let root = SourceRoot::new(&source);
        let start = source.find(at).unwrap() + offset;
        let end = start + width;
        let line = source[..start]
            .bytes()
            .filter(|&byte| byte == b'\n')
            .count()
            + 1;
        let column = source[..start].rsplit('\n').next().unwrap().chars().count() + 1;
        let missing_kernel = format!("--lean-kernel={}", root.0.join("absent").display());
        for command in ["check", "run"] {
            for json in [false, true] {
                let mut process = Command::new(env!("CARGO_BIN_EXE_qleisli"));
                process.arg(command).arg(&root.0).arg(&missing_kernel);
                if json {
                    process.arg("--format=json");
                }
                let output = process.output().unwrap();
                assert_eq!(output.status.code(), Some(1), "{output:?}");
                if json {
                    assert!(output.stderr.is_empty(), "{output:?}");
                    let text = String::from_utf8(output.stdout).unwrap();
                    assert_eq!(text.matches("\"code\":\"parse\"").count(), 1, "{text}");
                    assert!(text.contains(guidance), "{text}");
                    let location = format!(
                        "\"path\":\"main.qli\",\"start\":{start},\"end\":{end},\"line\":{line},\"column\":{column}"
                    );
                    assert!(
                        text.contains(&location) && text.ends_with("\"result\":null}\n"),
                        "{text}"
                    );
                } else {
                    assert!(output.stdout.is_empty(), "{output:?}");
                    let text = String::from_utf8(output.stderr).unwrap();
                    let location = format!("main.qli:{line}:{column}: parse:");
                    assert!(
                        text.contains(&location) && text.contains(guidance),
                        "{text}"
                    );
                }
            }
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn json_check_and_run_have_golden_envelopes_in_every_flag_position() {
    let root = SourceRoot::new("observe fn main() -> Bit { 1 }");
    for command in ["check", "run"] {
        let mut first = None;
        for flag_index in 0..3 {
            let mut args = vec![command.as_ref(), root.0.as_os_str()];
            args.insert(flag_index, "--format=json".as_ref());
            let output = cli(&args);
            assert_eq!(output.status.code(), Some(0), "{output:?}");
            assert!(output.stderr.is_empty(), "{output:?}");
            let text = String::from_utf8(output.stdout).unwrap();
            if command == "run" {
                assert_eq!(
                    text,
                    "{\"format\":\"qleisli.result\",\"version\":1,\"command\":\"run\",\"outcome\":\"ok\",\"diagnostics\":[],\"result\":{\"distribution\":[{\"bits\":[true],\"probability\":1}]}}\n"
                );
            } else {
                assert!(text.starts_with("{\"format\":\"qleisli.result\",\"version\":1,\"command\":\"check\",\"outcome\":\"ok\",\"diagnostics\":[],\"result\":{\"checker_paths\":["), "{text}");
                assert!(text.contains("\"checker_identity\":\"unpinned\""), "{text}");
                assert!(
                    text.contains("\"entry\":{\"present\":true,\"request_checked\":false,\"ordinary_result_checked\":false,\"runtime_result_checked\":false}"),
                    "{text}"
                );
                assert!(
                    text.contains("\"source_preservation_verified\":false"),
                    "{text}"
                );
                assert!(!text.contains("\"verified\":true"), "{text}");
            }
            if let Some(expected) = &first {
                assert_eq!(&text, expected);
            } else {
                first = Some(text);
            }
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn json_command_identity_is_independent_of_leading_options() {
    let root = SourceRoot::new("observe fn main() -> Bit { 1 }");
    for (command, flags, status) in [
        ("check", vec!["--source-bytes=1048576"], 0),
        ("run", vec!["--legacy-source-limits"], 0),
        ("sample", vec!["--shots=2", "--seed=0"], 0),
        ("check", vec!["--project-bytes=1"], 1),
    ] {
        let trailing = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .arg(command)
            .arg(&root.0)
            .args(&flags)
            .arg("--format=json")
            .output()
            .unwrap();
        let leading = Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .args(&flags)
            .arg(command)
            .arg(&root.0)
            .arg("--format=json")
            .output()
            .unwrap();
        assert_eq!(trailing.status.code(), Some(status), "{trailing:?}");
        assert_eq!(leading.status.code(), Some(status), "{leading:?}");
        assert!(trailing.stderr.is_empty() && leading.stderr.is_empty());
        assert!(
            String::from_utf8_lossy(&trailing.stdout)
                .contains(&format!("\"command\":\"{command}\"")),
            "{trailing:?}"
        );
        assert_eq!(leading.stdout, trailing.stdout);
    }
}

#[test]
fn json_usage_is_atomic_and_keeps_the_usage_exit_code() {
    // Preserve the historical golden; apply the reviewed current help changes.
    let historical = include_str!("fixtures/frontend_v030/basis-polymorphism/current-usage.txt");
    let retired = "  qleisli sized <check|run|sample|emit-proposal> --entry=MODULE::FUNCTION [sized-options]\n";
    assert_eq!(historical.matches(retired).count(), 1);
    let retired_documentation = concat!(
        "  Canonical contract: docs/src/reference/discovery.md\n",
        "  https://github.com/MGYamada/Qleisli/blob/main/docs/src/reference/discovery.md\n"
    );
    assert_eq!(historical.matches(retired_documentation).count(), 1);
    let verify_ir = "  qleisli verify-ir <artifact-file> [--against=REQUEST] [--lean-kernel=PATH] [--format=json]\n";
    assert_eq!(historical.matches(verify_ir).count(), 1);
    let run = "  qleisli run <source-root> [--format=json] [source-options]\n";
    assert_eq!(historical.matches(run).count(), 1);
    let usage = historical
        .replace(retired, "")
        .replace(
            run,
            "  qleisli run <source-root> [--format=json | --show-exact-zeros] [source-options]\n",
        )
        .replace(
            verify_ir,
            &format!(concat!(
                "{verify_ir}  qleisli engineering compare-pure ACTUAL --edition=2026 --against=REQUEST [--lean-kernel=PATH] [--format=json]\n",
                "  qleisli engineering compare-pure-tensor ACTUAL --edition=2026 --against=REQUEST [--lean-kernel=PATH] [--format=json]\n",
                "  qleisli engineering compare-instrument ACTUAL --edition=2026 --against=REQUEST [--lean-kernel=PATH] [--format=json]\n",
                "  qleisli engineering compare-openqasm3 TARGET --edition=2026 --against=REQUEST [--lean-kernel=PATH] [--format=json]\n",
                "  qleisli engineering compare-openqasm3-gate TARGET --edition=2026 --against=REQUEST [--lean-kernel=PATH] [--format=json]\n"
            ), verify_ir = verify_ir.replace("<artifact-file>", "<artifact-file> --edition=2026")),
        )
        .replace(
            "<file|-> --input=<qasm|qirf|qli>",
            "<file|-> --input=<qasm|qirf> --edition=2026",
        )
        .replace(
            "  interop always returns JSON; qli input takes a project directory.\n",
            concat!(
                "  qleisli interop <check|run|sample|emit-ir|emit-qasm|emit-qir> <source> --input=qli [--expect-edition=2026] [--shots=N --seed=S] [--lean-kernel=PATH]\n",
                "  qleisli interop emit-qasm <source> --input=qli --resources [--expect-edition=2026] [--lean-kernel=PATH]\n",
                "  interop always returns JSON; qli input takes a project directory.\n",
                "  Raw qirf/qasm interop requires --edition=2026; source projects select it in Qargo.toml.\n",
                "  Edition selects the constitutional regime, independently of the compiler release.\n"
            ),
        )
        .replace(
            retired_documentation,
            "  Documentation: https://github.com/MGYamada/Qleisli/blob/main/docs/src/introduction.md\n",
        )
        .trim_end()
        .replace('\n', "\\u000a");
    for args in [
        vec!["check", "--format=json"],
        vec!["check", ".", "--format=json", "--format=json"],
        vec!["check", ".", "--unknown", "--format=json"],
        vec!["check", ".", "--format", "--format=json"],
        vec!["check", ".", "--format=xml", "--format=json"],
        vec!["check", "--unknown", "--format=json"],
        vec!["--source-bytes=0", "check", ".", "--format=json"],
        vec!["--unknown", "check", ".", "--format=json"],
        vec!["--format=json", "--shots=01", "check", "."],
    ] {
        let args: Vec<_> = args.iter().map(std::ffi::OsStr::new).collect();
        let output = cli(&args);
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stderr.is_empty());
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            concat!(
                "{\"format\":\"qleisli.result\",\"version\":1,\"command\":\"check\",\"outcome\":\"error\",",
                "\"diagnostics\":[{\"code\":\"usage\",\"severity\":\"error\",",
                "\"message\":\"USAGE\",",
                "\"primary\":null,\"related\":[]}],\"result\":null}\n"
            ).replace("USAGE", &usage)
        );
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn json_runtime_limit_does_not_emit_a_partial_distribution() {
    let mut source = String::from("use std::state::init0;  observe fn main() -> Unit {");
    for i in 0..17 {
        source.push_str(&format!("let q{i} = init0();"));
    }
    for i in 0..17 {
        source.push_str(&format!("discard(q{i});"));
    }
    source.push_str("() }");
    let root = SourceRoot::new(&source);
    let output = cli(&["run".as_ref(), root.0.as_os_str(), "--format=json".as_ref()]);
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stderr.is_empty());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        concat!(
            "{\"format\":\"qleisli.result\",\"version\":1,\"command\":\"run\",\"outcome\":\"error\",",
            "\"diagnostics\":[{\"code\":\"limit\",\"severity\":\"error\",",
            "\"message\":\"simulation requires 17 qubits; limit is 16\",",
            "\"primary\":null,\"related\":[]}],\"result\":null}\n"
        )
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn json_type_failure_is_located_in_the_original_source() {
    let root = SourceRoot::new("observe fn main() -> Bit { () }");
    let output = cli(&[
        "check".as_ref(),
        "--format=json".as_ref(),
        root.0.as_os_str(),
    ]);
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stderr.is_empty());
    let output = String::from_utf8(output.stdout).unwrap();
    assert!(output.contains("\"code\":\"type_mismatch\""), "{output}");
    assert!(output.contains("\"path\":\"main.qli\""), "{output}");
    assert!(!output.contains(&root.0.display().to_string()), "{output}");
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn terminal_export_locates_the_exact_rejected_source_specialization() {
    let invoke = |project: &SourceRoot, action: &str| {
        cli(&[
            "interop".as_ref(),
            action.as_ref(),
            project.0.as_os_str(),
            "--input=qli".as_ref(),
        ])
    };
    let first = SourceRoot::new(include_str!(
        "fixtures/authoring_sessions/target-specialization-v030/attempt-01/n1/main.qli"
    ));
    first.write(
        "Qargo.toml",
        include_str!(
            "fixtures/authoring_sessions/target-specialization-v030/attempt-01/n1/Qargo.toml.rejected"
        ),
    );
    let refused_manifest = invoke(&first, "emit-qasm");
    assert_eq!(refused_manifest.status.code(), Some(1));
    assert!(
        String::from_utf8(refused_manifest.stdout)
            .unwrap()
            .contains("requires schema-version = 2")
    );

    let trials = [
        (
            include_str!(
                "fixtures/authoring_sessions/target-specialization-v030/attempt-02/n0/main.qli"
            ),
            include_str!(
                "fixtures/authoring_sessions/target-specialization-v030/attempt-02/n0/Qargo.toml"
            ),
        ),
        (
            include_str!(
                "fixtures/authoring_sessions/target-specialization-v030/attempt-02/n1/main.qli"
            ),
            include_str!(
                "fixtures/authoring_sessions/target-specialization-v030/attempt-02/n1/Qargo.toml"
            ),
        ),
    ];
    for (actual, (source, manifest)) in trials.into_iter().enumerate() {
        let project = SourceRoot::new(source);
        project.write("Qargo.toml", manifest);
        assert!(invoke(&project, "check").status.success());
        for (action, target) in [
            ("emit-qasm", "OpenQASM 3"),
            ("emit-qir", "QIR 2.0 Base Profile"),
        ] {
            let export = invoke(&project, action);
            let result = String::from_utf8(export.stdout).unwrap();
            if actual == 0 {
                assert!(export.status.success(), "{result}");
                continue;
            }
            assert_eq!(export.status.code(), Some(1));
            assert!(result.contains("\"code\":\"unsupported\""), "{result}");
            assert!(
                result.contains(&format!("{target} export of main::specialize[1]")),
                "{result}"
            );
            assert!(result.contains("uncontrolled scalar phase"), "{result}");
            let failing = "global_phase_eighth(q)";
            let start = source.find(failing).unwrap();
            assert!(
                result.contains(&format!(
                    "\"primary\":{{\"path\":\"main.qli\",\"start\":{start},\"end\":{}",
                    start + failing.len()
                )),
                "{result}"
            );
            assert!(result.contains("\"result\":null"), "{result}");
        }

        if actual == 1 {
            let program = qleisli::frontend::compile::compile_project(&project.0).unwrap();
            let path = project.0.join("accepted.qirf");
            std::fs::write(&path, program.portable_artifact().unwrap()).unwrap();
            let imported = cli(&[
                "interop".as_ref(),
                "emit-qasm".as_ref(),
                path.as_os_str(),
                "--input=qirf".as_ref(),
                "--edition=2026".as_ref(),
            ]);
            let result = String::from_utf8(imported.stdout).unwrap();
            assert_eq!(imported.status.code(), Some(1));
            assert!(result.contains("uncontrolled scalar phase"), "{result}");
            assert!(result.contains("\"primary\":null"), "{result}");
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn terminal_workspace_failure_locates_the_original_specialization() {
    let source = include_str!(
        "fixtures/authoring_sessions/target-specialization-v030/attempt-03/n2/main.qli"
    );
    let project = SourceRoot::new(source);
    project.write(
        "Qargo.toml",
        include_str!(
            "fixtures/authoring_sessions/target-specialization-v030/attempt-03/n2/Qargo.toml"
        ),
    );
    for resources in [false, true] {
        let mut args = vec![
            "interop".as_ref(),
            "emit-qasm".as_ref(),
            project.0.as_os_str(),
            "--input=qli".as_ref(),
        ];
        if resources {
            args.push("--resources".as_ref());
        }
        let export = cli(&args);
        assert_eq!(export.status.code(), Some(1));
        let result = String::from_utf8(export.stdout).unwrap();
        assert!(
            result.contains("OpenQASM 3 export of main::specialize[2]"),
            "{result}"
        );
        assert!(result.contains("uncontrolled scalar phase"), "{result}");
        let expression = "global_phase_eighth(q)";
        let start = source.find(expression).unwrap();
        assert!(
            result.contains(&format!(
                "\"primary\":{{\"path\":\"main.qli\",\"start\":{start},\"end\":{}",
                start + expression.len()
            )),
            "{result}"
        );
        assert!(result.contains("\"result\":null"), "{result}");
    }
}
