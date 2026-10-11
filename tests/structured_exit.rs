//! Structured source exits and ordinary names through the shared grammar.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::frontend::compile::{ParsedProgram, check_project_with_kernel};
use qleisli::frontend::parser::parse_module;
use qleisli::frontend::project::SourcePolicy;
use qleisli::interchange::native::Kernel;
use std::collections::BTreeMap;
use std::process::Command;

const EXITS: &[(&str, &str, &str)] = &[
    ("return q", "return", "early `return`"),
    ("q?", "?", "`?` residual propagation"),
    ("panic!();q", "!", "`panic!` runtime exits"),
    ("assert!(1);q", "!", "`assert!` runtime exits"),
    ("unreachable!();q", "!", "`unreachable!` runtime exits"),
];

fn source(kind: &str, body: &str) -> String {
    format!("{kind} fn bad(q:Q<Bit>)->Q<Bit>{{{body}}}\nobserve fn main()->Bit{{1}}")
}

#[test]
fn forbidden_exits_have_original_locations_and_structured_alternatives() {
    for kind in ["unitary", "isometry", "observe"] {
        for (body, token, reason) in EXITS {
            for body in [body.to_string(), format!("if 1 {{{body}}} else {{q}}")] {
                let text = source(kind, &body);
                let error = parse_module(&text).unwrap_err();
                assert_eq!(&text[error.span.start..error.span.end], *token);
                assert!(error.message.contains(reason), "{error}");
                assert!(error.message.contains("final expression"), "{error}");
                assert!(error.message.contains("every quantum owner"), "{error}");
                let selected =
                    ParsedProgram::parse(BTreeMap::from([("main".into(), text.clone())]))
                        .unwrap_err();
                assert_eq!(selected.code(), "parse");
                assert_eq!(selected.span(), error.span);
                let root = SourceRoot::new(&text);
                let absent = Kernel::new(root.0.join("not-executed-kernel"));
                let finite = check_project_with_kernel(&root.0, SourcePolicy::default(), &absent)
                    .unwrap_err();
                assert_eq!(finite.code, "parse");
                assert_eq!(finite.primary.unwrap().span, error.span);
                assert!(finite.message.contains(reason));
            }
        }
    }
}

#[test]
fn ordinary_names_comments_and_inequality_never_become_runtime_exits() {
    let text = "unitary fn panic(q:Q<Bit>)->Q<Bit>{q}
        unitary fn return(q:Q<Bit>)->Q<Bit>{let return=panic(q);return}
        unitary fn forward(q:Q<Bit>)->Q<Bit>{return(q)}
        // return q? panic!(); unreachable!()
        /* assert!(1); q? */
        observe fn main()->Bit{1}";
    let tokens = qleisli::frontend::lexer::lex("1 != 0").unwrap();
    assert_eq!(
        tokens[1].kind,
        qleisli::frontend::lexer::TokenKind::NotEqual
    );
    let selected = ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())])).unwrap();
    assert!(selected.function_effect("main::forward").is_some());
    let root = SourceRoot::new(text);
    check_project_with_kernel(
        &root.0,
        SourcePolicy::default(),
        &Kernel::selected().unwrap(),
    )
    .unwrap();
    for kind in ["unitary", "isometry", "observe"] {
        parse_module(&source(kind, "let return=q;return")).unwrap();
    }
}

#[test]
fn other_abort_macros_refuse_but_unrelated_punctuation_stays_distinct() {
    for name in [
        "assert_eq",
        "assert_ne",
        "debug_assert",
        "debug_assert_eq",
        "debug_assert_ne",
        "todo",
        "unimplemented",
    ] {
        let error = parse_module(&source("unitary", &format!("{name}!();q"))).unwrap_err();
        assert!(error.message.contains(&format!("`{name}!` runtime exits")));
    }
    let error = parse_module(&source("unitary", "custom!();q")).unwrap_err();
    assert_eq!(error.message, "unexpected character `!`");
}

#[test]
fn exit_refusals_match_cli_text_and_json_without_contacting_native_checker() {
    for (body, token, reason) in EXITS {
        let text = format!("// π origin\r\n{}", source("unitary", body));
        let root = SourceRoot::new(&text);
        for json in [false, true] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
            command.arg("check").arg(&root.0).arg(format!(
                "--lean-kernel={}",
                root.0.join("not-executed-kernel").display()
            ));
            if json {
                command.arg("--format=json");
            }
            let output = command.output().unwrap();
            assert_eq!(output.status.code(), Some(1));
            if json {
                let result = String::from_utf8(output.stdout).unwrap();
                let error = parse_module(&text).unwrap_err();
                assert_eq!(&text[error.span.start..error.span.end], *token);
                assert!(result.contains("\"code\":\"parse\""), "{result}");
                assert!(result.contains(reason), "{result}");
                assert!(
                    result.contains(&format!(
                        "\"start\":{},\"end\":{}",
                        error.span.start, error.span.end
                    )),
                    "{result}"
                );
            } else {
                let result = String::from_utf8(output.stderr).unwrap();
                assert!(result.contains(reason), "{result}");
                assert!(result.contains("final expression"), "{result}");
            }
        }
    }
}

#[test]
fn final_branches_cannot_drop_or_exchange_unaccounted_quantum_owners() {
    for text in [
        "unitary fn bad(q:Q<Bit>)->Q<Bit>{if 1 {q} else {()}}",
        "unitary fn bad(q:Q<Bit>,r:Q<Bit>)->Q<Bit>{if 1 {q} else {r}}",
        "unitary fn bad(q:Q<Bit>)->Unit{()}",
    ] {
        let text = format!("{text}\nobserve fn main()->Bit{{1}}");
        parse_module(&text).unwrap();
        let selected =
            ParsedProgram::parse(BTreeMap::from([("main".into(), text.clone())])).unwrap_err();
        assert_ne!(selected.code(), "parse");
        assert_ne!(selected.code(), "unsupported");
        let root = SourceRoot::new(&text);
        let finite = check_project_with_kernel(
            &root.0,
            SourcePolicy::default(),
            &Kernel::new(root.0.join("not-executed-kernel")),
        )
        .unwrap_err();
        assert_ne!(finite.code, "parse");
        assert_ne!(finite.code, "unsupported");
        assert_ne!(finite.code, "project");
    }
}

#[test]
fn static_range_arithmetic_and_shape_refuse_before_native_acceptance() {
    for (text, selected_code, finite_code) in [
        (
            "use std::registers::take_bit; pub unitary fn bad[const n:Nat](q:Q<Bits<n>>)->(Q<Bits<n-1>>,Q<Bit>) requires n>=1 {take_bit[n,n](q)} observe fn main()->Bit{0}",
            "size",
            "type_mismatch",
        ),
        (
            "pub observe fn main()->Bit{static let n=170141183460469231731687303715884105727+1;0}",
            "limit",
            "limit",
        ),
        (
            "pub unitary fn bad(b:Bit,q:Q<Bit>)->Q<Bit>{if b {q} else {()}} observe fn main()->Bit{0}",
            "type",
            "type_mismatch",
        ),
    ] {
        parse_module(text).unwrap();
        let selected =
            ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())])).unwrap_err();
        assert_eq!(selected.code(), selected_code);
        let root = SourceRoot::new(text);
        let finite = check_project_with_kernel(
            &root.0,
            SourcePolicy::default(),
            &Kernel::new(root.0.join("not-executed-kernel")),
        )
        .unwrap_err();
        assert_eq!(finite.code, finite_code, "{}", finite.message);
        assert!(finite.primary.is_some());
    }
}

#[test]
fn explicit_alternatives_keep_correlated_owners_and_host_limits_stay_separate() {
    use qleisli::frontend::compile::compile_project;
    use qleisli::ir::RawOp;
    use qleisli::sim::{SimulationError, SimulationLimits, run_closed};

    let text = "use std::quantum::init0;use std::quantum::h;
        use std::quantum::x;use std::quantum::cnot;use std::observe::measure_z;
        fn choose(b:Bit,q:Q<Bit>)->(Bit,Q<Bit>){if b {(0,q)}else{(1,x(q))}}
        pub observe fn main()->(Bit,Bit,Bit,Bit){
            let (a,r)=cnot(h(init0()),init0());
            let b=measure_z(h(init0()));
            let (tag,a)=choose(b,a);
            (b,tag,measure_z(a),measure_z(r))
        }";
    let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())])).unwrap();
    // The common body judgment succeeds. The selected lowering's existing
    // runtime-if restriction is a preparation refusal, not an execution edge.
    let error = parsed
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap_err();
    assert_eq!(error.code(), "unsupported");
    let accepted = compile_project(&SourceRoot::new(text).0).unwrap();
    let branch = accepted
        .program()
        .operations
        .iter()
        .find_map(|op| match op {
            RawOp::ClassicalBranch { quantum_phis, .. } => Some(quantum_phis),
            _ => None,
        })
        .unwrap();
    assert_eq!(branch.len(), 2); // returned a and the inaccessible caller r
    let distribution = run_closed(&accepted, SimulationLimits::default()).unwrap();
    let expected = [
        vec![false, true, true, false],
        vec![false, true, false, true],
        vec![true, false, false, false],
        vec![true, false, true, true],
    ];
    assert_eq!(distribution.len(), expected.len());
    for outcome in expected {
        assert!((distribution[&outcome] - 0.25).abs() < 1e-12);
    }
    assert_eq!(
        run_closed(
            &accepted,
            SimulationLimits {
                max_execution_steps: 0,
                ..SimulationLimits::default()
            }
        )
        .unwrap_err(),
        SimulationError::ExecutionLimit { max: 0 }
    );
}
