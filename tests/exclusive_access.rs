//! Whole-owner exclusive calls through both public source paths.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::frontend::compile::{ErrorCode, ParsedProgram, check_project, compile_project};
use qleisli::interchange::native::Kernel;
use qleisli::sim::{SimulationLimits, run_closed};
use std::collections::BTreeMap;

const IMPORTS: &str = "use std::quantum::init0; use std::quantum::h;
    use std::quantum::x; use std::quantum::cnot; use std::observe::measure_z;";

fn selected(source: &str) -> ParsedProgram {
    ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap()
}

#[test]
fn updated_owners_survive_nested_blocks_calls_and_measurement() {
    for (body, expected) in [
        ("let q=init0(); x(excl q); measure_z(q)", vec![true]),
        (
            "let q=init0(); h(excl q); h(excl q); x(excl q); measure_z(q)",
            vec![true],
        ),
        (
            "let c=init0(); let t=init0(); x(excl c); cnot(excl c,excl t); (measure_z(c),measure_z(t))",
            vec![true, true],
        ),
    ] {
        let output = if expected.len() == 1 {
            "Bit"
        } else {
            "(Bit,Bit)"
        };
        let source = format!("{IMPORTS} pub observe fn main()->{output}{{{body}}}");
        let finite = compile_project(&SourceRoot::new(&source).0).unwrap();
        let proposal = selected(&source)
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap()
            .lower_raw()
            .unwrap();
        let concrete = Kernel::selected()
            .unwrap()
            .accept(proposal.proposal())
            .unwrap();
        // These expected computational outcomes come from X/CNOT algebra,
        // independently of either frontend's ownership or lowering bookkeeping.
        for accepted in [&finite, &concrete] {
            let actual = run_closed(accepted, SimulationLimits::default()).unwrap();
            assert_eq!(actual.len(), 1, "{source}: {actual:?}");
            assert!((actual[&expected] - 1.0).abs() < 1e-12, "{source}");
        }
    }
}

#[test]
fn global_calls_preserve_exact_coefficient_and_external_reference() {
    let source = format!(
        "{IMPORTS}
        unitary fn flip(q:Q<Bit>)->Q<Bit>{{x(q)}}
        pub unitary fn apply(q:Q<Bit>)->Q<Bit>{{flip(excl q);q}}"
    );
    let proposal = selected(&source)
        .instantiate("main::apply", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower()
        .unwrap();
    let kernel = qleisli::interchange::hierarchical::Kernel::new(
        std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
    );
    let accepted = kernel
        .check_against_native(proposal.payload(), proposal.comparison_request())
        .unwrap();
    let input = vec![[0.25, -0.5], [0.75, 0.125], [-0.25, 0.375], [0.5, -0.625]];
    let actual = accepted
        .execute_pure(
            &input,
            2,
            qleisli::interchange::hierarchical::execution::ExecutionLimits {
                max_amplitudes: 16,
                max_steps: 1000,
            },
        )
        .unwrap();
    // The system axis occupies the low bit. X toggles it while the
    // reference index (high bit) and each complex coefficient stay unchanged.
    assert_eq!(
        actual.amplitudes,
        (0..4).map(|i| input[i ^ 1]).collect::<Vec<_>>()
    );
}

#[test]
fn finite_nested_runtime_branch_retains_updated_owner() {
    let source = format!(
        "{IMPORTS} pub observe fn main()->Bit{{
        let q=init0();let u=if 1{{x(excl q);()}}else{{()}};measure_z(q)}}"
    );
    let finite = compile_project(&SourceRoot::new(&source).0).unwrap();
    assert_eq!(
        run_closed(&finite, SimulationLimits::default()).unwrap(),
        BTreeMap::from([(vec![true], 1.0)])
    );
    // Runtime conditional preparation remains outside the existing selected
    // projection profile. Do not silently expand that unrelated contract.
    let error = selected(&source)
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .expect_err("runtime conditional remains outside selected projection");
    assert_eq!(error.code(), "unsupported");
}

#[test]
fn overlap_spent_owner_wrong_interface_and_nonunitary_calls_refuse() {
    for body in [
        "let q=init0(); cnot(excl q,excl q);measure_z(q)",
        "let q=init0(); let b=measure_z(q);x(excl q);b",
        "let q=init0();measure_z(excl q);0",
        "let q=init0();bad(excl q);measure_z(q)",
        "let q=init0();x(ctrl q);measure_z(q)",
        "let q=0;x(excl q);q",
    ] {
        let source = format!(
            "{IMPORTS}
            observe fn bad(q:Q<Bit>)->Q<Bit>{{let b=measure_z(q);init0()}}
            pub observe fn main()->Bit{{{body}}}"
        );
        assert!(
            check_project(&SourceRoot::new(&source).0).is_err(),
            "{source}"
        );
        assert!(
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.clone())])).is_err(),
            "{source}"
        );
    }
}

#[test]
fn access_markers_remain_ordinary_contextual_names() {
    let source = "unitary fn excl(q:Q<Bit>)->Q<Bit>{q}
        unitary fn ctrl(q:Q<Bit>)->Q<Bit>{excl(q)}
        pub unitary fn f(q:Q<Bit>)->Q<Bit>{ctrl(q)}";
    selected(source)
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
}

#[test]
fn zero_width_owner_keeps_phase_and_cannot_be_duplicated() {
    let source = "use std::quantum::phase_eighth;
        pub unitary fn f(q:Q<Unit>)->Q<Unit>{phase_eighth(excl q);q}";
    let proposal = selected(source)
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower()
        .unwrap();
    let kernel = qleisli::interchange::hierarchical::Kernel::new(
        std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
    );
    let accepted = kernel
        .check_against_native(proposal.payload(), proposal.comparison_request())
        .unwrap();
    let input = vec![[0.25, -0.5], [0.75, 0.125]];
    let actual = accepted
        .execute_pure(
            &input,
            2,
            qleisli::interchange::hierarchical::execution::ExecutionLimits {
                max_amplitudes: 16,
                max_steps: 1000,
            },
        )
        .unwrap();
    let s = std::f64::consts::FRAC_1_SQRT_2;
    for (actual, [re, im]) in actual.amplitudes.iter().zip(input) {
        assert!((actual[0] - (re - im) * s).abs() < 1e-12);
        assert!((actual[1] - (re + im) * s).abs() < 1e-12);
    }
    let source = "unitary fn pair(q:Q<Unit>,r:Q<Unit>)->(Q<Unit>,Q<Unit>){(q,r)}
        pub unitary fn f(q:Q<Unit>)->Q<Unit>{pair(excl q,excl q);q}";
    assert!(check_project(&SourceRoot::new(source).0).is_err());
    assert!(ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).is_err());
}

#[test]
fn exact_owner_shape_and_actual_body_effect_are_required() {
    for (definition, finite_code, selected_code) in [
        (
            "unitary fn change(q:Q<(Bit,Unit)>)->(Q<Bit>,Q<Unit>){split(q)}",
            ErrorCode::TypeMismatch,
            "type",
        ),
        (
            "fn change(q:Q<(Bit,Unit)>)->Q<(Bit,Unit)>{let (b,u)=split(q);let m=measure_z(b);discard(u);join(init0(),unit(()))}",
            ErrorCode::Effect,
            "effect",
        ),
        (
            "unitary fn change(q:Q<(Bit,Unit)>)->Q<(Unit,Bit)>{basis q as (b,()){((),b)}}",
            ErrorCode::TypeMismatch,
            "type",
        ),
    ] {
        let source = format!(
            "{IMPORTS} use std::quantum::split;
            use std::quantum::join;use std::quantum::unit;use std::observe::discard;
            {definition} pub fn f(q:Q<(Bit,Unit)>)->Q<(Bit,Unit)>{{change(excl q);q}}"
        );
        let finite = check_project(&SourceRoot::new(&source).0).unwrap_err();
        assert_eq!(finite.code, finite_code, "{source}\n{finite}");
        let selected =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.clone())])).unwrap_err();
        assert_eq!(selected.code(), selected_code, "{source}\n{selected}");
        if selected_code == "type" {
            assert!(selected.message().contains("exclusive call must return"));
            assert!(finite.message.contains("exclusive call must return"));
        } else {
            assert!(
                selected
                    .message()
                    .contains("\"externally unitary\" is not supported")
            );
            assert!(
                finite
                    .message
                    .contains("\"externally unitary\" is not supported")
            );
        }
    }
}

#[test]
fn reassembled_owner_and_callee_binders_do_not_restore_old_snapshot() {
    let source = format!(
        "{IMPORTS} use std::quantum::join;use std::quantum::split;
        unitary fn transform(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{{
            let (a,b)=split(q);x(excl a);join(a,b)
        }}
        pub observe fn main()->(Bit,Bit){{
            let q=join(init0(),init0());transform(excl q);
            let (a,b)=split(q);(measure_z(a),measure_z(b))
        }}"
    );
    let finite = compile_project(&SourceRoot::new(&source).0).unwrap();
    let proposal = selected(&source)
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower_raw()
        .unwrap();
    let concrete = Kernel::selected()
        .unwrap()
        .accept(proposal.proposal())
        .unwrap();
    for accepted in [&finite, &concrete] {
        assert_eq!(
            run_closed(accepted, SimulationLimits::default()).unwrap(),
            BTreeMap::from([(vec![true, false], 1.0)])
        );
    }
}

#[test]
fn contextual_markers_keep_original_locations_and_bounded_arity() {
    use qleisli::frontend::ast::{ExprKind, FnBody, QuantumAccess, StmtKind};
    use qleisli::frontend::parser::parse_module;
    let source = "// π source\r\npub unitary fn f(q:Q<Bit>)->Q<Bit>{h(excl q);q}";
    let module = parse_module(source).unwrap();
    let FnBody::Quantum(body) = &module.decls[0].body else {
        panic!("quantum body")
    };
    let StmtKind::Expr(call) = &body.statements[0].kind else {
        panic!("expression statement")
    };
    let ExprKind::AccessCall { args, .. } = &call.kind else {
        panic!("access call")
    };
    assert_eq!(args[0].access, QuantumAccess::Excl);
    assert_eq!(
        &source[args[0].value.span.start..args[0].value.span.end],
        "excl q"
    );
    let ExprKind::Name(owner) = &args[0].value.kind else {
        panic!("lexical owner")
    };
    assert_eq!(&source[owner.span.start..owner.span.end], "q");
    for arguments in ["excl q,q", "q,excl q", "excl q[0]", "excl q()"] {
        assert!(
            parse_module(&format!("fn f(q:Q<Bit>)->Q<Bit>{{h({arguments});q}}")).is_err(),
            "{arguments}"
        );
    }
    // Whitespace before a normal call's parenthesis does not turn the
    // ordinary identifier `excl` into an argument marker.
    parse_module("fn f(q:Q<Bit>)->Q<Bit>{h(excl (q));q}").unwrap();
    let source = format!(
        "fn f(q:Q<Bit>)->Q<Bit>{{h({});q}}",
        vec!["excl q"; 65].join(",")
    );
    let error = parse_module(&source).unwrap_err();
    assert!(error.message.contains("64"), "{error}");
}

#[test]
fn closed_static_branches_and_empty_fold_thread_updated_carry() {
    let source = "use std::quantum::x;
        pub unitary fn f[const rounds:Nat](q:Q<Bit>)->Q<Bit>{
            qfor static k in 0..rounds carry r=q {
                let u=if static k==0 {x(excl r);()} else {x(excl r);()};
                yield r;
            }
        }";
    let parsed = selected(source);
    let kernel = qleisli::interchange::hierarchical::Kernel::new(
        std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
    );
    let input = vec![[0.25, -0.5], [0.75, 0.125], [-0.25, 0.375], [0.5, -0.625]];
    for rounds in 0..=3 {
        let proposal = parsed
            .instantiate(
                "main::f",
                BTreeMap::from([("rounds".into(), rounds)]),
                BTreeMap::new(),
            )
            .unwrap()
            .elaborate()
            .unwrap()
            .lower()
            .unwrap();
        let accepted = kernel
            .check_against_native(proposal.payload(), proposal.comparison_request())
            .unwrap();
        let actual = accepted
            .execute_pure(
                &input,
                2,
                qleisli::interchange::hierarchical::execution::ExecutionLimits {
                    max_amplitudes: 16,
                    max_steps: 1000,
                },
            )
            .unwrap();
        assert_eq!(
            actual.amplitudes,
            (0..4)
                .map(|i| input[i ^ (rounds as usize % 2)])
                .collect::<Vec<_>>()
        );
    }
}
