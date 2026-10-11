//! The constructor rename preserves finite evidence and existing profile refusals.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
mod common;

use common::SourceRoot;
use qleisli::contract::exact::Exact;
use qleisli::contract::{BasisType, ContractError, FunctionEvidence};
use qleisli::frontend::ast::{ExprKind, FnBody, Span, StaticOp, StaticOpKind};
use qleisli::frontend::compile::ParsedProgram;
use qleisli::frontend::compile::{
    ErrorCode, check_project, check_project_diagnostic, compile_project,
};
use qleisli::frontend::lexer::{TokenKind, lex};
use qleisli::frontend::parser::{parse_documented_module, parse_module};
use qleisli::ir::{CircuitAction, RawOp};
use qleisli::sim::{SimulationLimits, run_closed};
use std::collections::BTreeMap;
use std::process::Command;
use std::sync::Arc;

const PRELUDE: &str = "
use std::quantum::init0; use std::quantum::h; use std::quantum::x;
use std::quantum::z; use std::quantum::t;
use std::quantum::join; use std::quantum::split;
use std::observe::measure_z;
classical fn z_phase(b:Bit)->(Bit,(Bit,Bit)){(0,(0,b))}
meaning ZMeaning:Bit=phase_by(z_phase);
unitary fn provider(q:Q<Bit>)->Q<Bit>{power(t,4)(q)}
unitary fn use_op[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
";

#[test]
fn canonical_constructed_inverse_finite_keeps_order_and_zero_power_effects() {
    use qleisli::contract::exact::{Budget, Matrix};
    use qleisli::contract::{Circuit, DEFAULT_EXACT_WORK};
    let text = "use std::quantum::{h,z,init0};use std::observe::measure_z;
        unitary fn oracle(q:Q<Bit>)->Q<Bit>{h(z(q))}
        observe fn main()->Bit{measure_z(adjoint(power(oracle,2))(init0()))}";
    let accepted = compile_project(&SourceRoot::new(text).0).unwrap();
    let steps = accepted
        .raw()
        .operations
        .iter()
        .find_map(|op| match op {
            RawOp::ApplyUnitary { steps, .. } => Some(steps.clone()),
            _ => None,
        })
        .unwrap();
    let actual = Circuit::new(BasisType::Bit, steps)
        .unwrap()
        .matrix(&mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    // (HZ)^2 inverse is [[0,1],[-1,0]], including its complete sign.
    assert_eq!(
        actual,
        Matrix::new(
            2,
            2,
            vec![
                Exact::zero(),
                Exact::one(),
                Exact::integer(-1),
                Exact::zero()
            ]
        )
        .unwrap()
    );
    assert!(
        (run_closed(&accepted, SimulationLimits::default()).unwrap()[&vec![true]] - 1.0).abs()
            < 1e-12
    );
    let text = "use std::quantum::{h,z,x,init0};use std::observe::measure_z;
        unitary fn oracle(q:Q<Bit>)->Q<Bit>{h(z(q))}
        observe fn main()->Bit{measure_z(adjoint(power(oracle,0))(x(init0())))}";
    let accepted = compile_project(&SourceRoot::new(text).0).unwrap();
    assert!(
        (run_closed(&accepted, SimulationLimits::default()).unwrap()[&vec![true]] - 1.0).abs()
            < 1e-12
    );
}

#[test]
fn canonical_constructed_inverse_finite_preserves_scalar_and_refuses_false_meaning() {
    use qleisli::contract::exact::{Budget, Matrix};
    use qleisli::contract::{Circuit, DEFAULT_EXACT_WORK};
    let text = "use std::quantum::{init0,split,phase_eighth};use std::observe::{discard,measure_z};
        unitary fn scalar(q:Q<Unit>)->Q<Unit>{phase_eighth(q)}
        observe fn main()->Bit{
            let(unit,bit)=split(basis(init0()) as b{((),b)});
            let unit=adjoint(power(scalar,1))(unit);
            discard(unit);measure_z(bit)
        }";
    let accepted = compile_project(&SourceRoot::new(text).0).unwrap();
    let steps = accepted
        .raw()
        .operations
        .iter()
        .find_map(|op| match op {
            RawOp::ApplyUnitary { steps, .. } => Some(steps.clone()),
            _ => None,
        })
        .unwrap();
    let actual = Circuit::new(BasisType::Unit, steps)
        .unwrap()
        .matrix(&mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    assert_eq!(
        actual,
        Matrix::new(1, 1, vec![Exact::new([0, 1, 0, -1], 1).unwrap()]).unwrap()
    );
    assert!(
        (run_closed(&accepted, SimulationLimits::default()).unwrap()[&vec![false]] - 1.0).abs()
            < 1e-12
    );
    let text = "use std::quantum::{x,init0};use std::observe::measure_z;
        classical fn z_phase(b:Bit)->(Bit,(Bit,Bit)){(0,(0,b))}
        meaning ZMeaning:Bit=phase_by(z_phase);
        unitary fn liar(q:Q<Bit>)->Q<Bit>{x(q)}
        observe fn main()->Bit{measure_z(adjoint(power(checked_op(liar,ZMeaning),0))(init0()))}";
    assert_eq!(
        compile_project(&SourceRoot::new(text).0).unwrap_err().code,
        ErrorCode::Contract
    );
    let text = "unitary fn unused[const U:Op<Bit>](q:Q<Unit>)->Q<Unit> requires Applicable(U),Adjointable(U){adjoint(power(U,0))(q)}";
    assert!(check_project(&SourceRoot::new(text).0).is_err());
}

#[test]
fn canonical_control_finite_keeps_ordered_axes_and_ordinary_names() {
    use qleisli::contract::exact::{Budget, Matrix};
    use qleisli::contract::{Circuit, DEFAULT_EXACT_WORK};
    for count in [0, 1, 2] {
        let text = format!(
            "use std::quantum::{{x,init0}};use std::observe::measure_z;
            unitary fn controlled(q:Q<Bit>)->Q<Bit>{{q}}
            unitary fn oracle(q:Q<Bit>)->Q<Bit>{{x(q)}}
            observe fn main()->(Bit,Bit){{
                let(c,q)=controlled(power(oracle,{count}))(controlled(x(init0())),init0());
                (measure_z(c),measure_z(q))
            }}"
        );
        let accepted = compile_project(&SourceRoot::new(&text).0).unwrap();
        let distribution = run_closed(&accepted, SimulationLimits::default()).unwrap();
        assert!((distribution[&vec![true, count % 2 == 1]] - 1.0).abs() < 1e-12);
        if count != 0 {
            let steps = accepted
                .raw()
                .operations
                .iter()
                .find_map(|op| match op {
                    RawOp::ApplyUnitary { steps, .. }
                        if steps.iter().any(|s| !s.controls.is_empty()) =>
                    {
                        Some(steps.clone())
                    }
                    _ => None,
                })
                .expect("actual controlled circuit");
            let actual = Circuit::new(BasisType::pair(BasisType::Bit, BasisType::Bit), steps)
                .unwrap()
                .matrix(&mut Budget::new(DEFAULT_EXACT_WORK))
                .unwrap();
            // Control is the low axis. This differs from reversing the two
            // input owners; probabilities for one chosen input alone are insufficient.
            let permutation = if count == 1 {
                [0, 3, 2, 1]
            } else {
                [0, 1, 2, 3]
            };
            let mut entries = vec![Exact::zero(); 16];
            for (column, row) in permutation.into_iter().enumerate() {
                entries[row * 4 + column] = Exact::one();
            }
            assert_eq!(actual, Matrix::new(4, 4, entries).unwrap());
        }
    }
}

#[test]
fn canonical_control_finite_preserves_zero_width_phase_and_owner() {
    use qleisli::contract::exact::{Budget, Matrix};
    use qleisli::contract::{Circuit, DEFAULT_EXACT_WORK};
    for count in [1, 4] {
        let text = format!(
            "use std::quantum::{{init0,h,split,phase_eighth}};
             use std::observe::{{discard,measure_z}};
             unitary fn scalar(q:Q<Unit>)->Q<Unit>{{phase_eighth(q)}}
             observe fn main()->Bit{{
                 let pair=basis(init0()) as bit {{((),bit)}};
                 let(unit,bit)=split(pair);
                 let(c,unit)=controlled(power(scalar,{count}))(h(init0()),unit);
                 discard(unit);discard(bit);measure_z(h(c))
             }}"
        );
        let accepted = compile_project(&SourceRoot::new(&text).0).unwrap();
        let steps = accepted
            .raw()
            .operations
            .iter()
            .find_map(|op| match op {
                RawOp::ApplyUnitary { steps, .. }
                    if steps.iter().any(|s| !s.controls.is_empty()) =>
                {
                    Some(steps.clone())
                }
                _ => None,
            })
            .unwrap();
        let actual = Circuit::new(BasisType::pair(BasisType::Bit, BasisType::Unit), steps)
            .unwrap()
            .matrix(&mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap();
        let phase = if count == 1 {
            Exact::new([0, 1, 0, 1], 1).unwrap()
        } else {
            Exact::integer(-1)
        };
        assert_eq!(
            actual,
            Matrix::new(
                2,
                2,
                vec![Exact::one(), Exact::zero(), Exact::zero(), phase]
            )
            .unwrap()
        );
        let distribution = run_closed(&accepted, SimulationLimits::default()).unwrap();
        let expected = if count == 1 {
            (2.0 - 2.0_f64.sqrt()) / 4.0
        } else {
            1.0
        };
        assert!((distribution[&vec![true]] - expected).abs() < 1e-12);
        // The empty target remains an owner and is explicitly consumed.
        assert!(
            accepted
                .raw()
                .operations
                .iter()
                .any(|op| matches!(op, RawOp::Discard { .. }))
        );
    }
}

#[test]
fn canonical_control_rejects_alias_arity_type_and_missing_access() {
    for (signature, body) in [
        ("(q:Q<Bit>)->(Q<Bit>,Q<Bit>)", "controlled(oracle)(q,q)"),
        ("(q:Q<Bit>)->Q<Bit>", "controlled(oracle)(q)"),
        (
            "(c:Bit,q:Q<Bit>)->(Q<Bit>,Q<Bit>)",
            "controlled(oracle)(c,q)",
        ),
        (
            "(c:Q<Bit>,q:Q<Unit>)->(Q<Bit>,Q<Unit>)",
            "controlled(oracle)(c,q)",
        ),
    ] {
        let text = format!(
            "use std::quantum::x;unitary fn oracle(q:Q<Bit>)->Q<Bit>{{x(q)}}unitary fn unused{signature}{{{body}}}"
        );
        assert!(check_project(&SourceRoot::new(&text).0).is_err(), "{text}");
        assert!(ParsedProgram::parse(sources(&text)).is_err(), "{text}");
    }
    let text = "unitary fn unused[const U:Op<Bit>](c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Applicable(U){controlled(power(U,0))(c,q)}";
    let error = check_project(&SourceRoot::new(text).0).unwrap_err();
    assert_eq!(error.code, ErrorCode::Capability);
    assert!(error.message.contains("Controllable"));
    let text = "use std::quantum::{x,init0};use std::observe::measure_z;
        classical fn z_phase(b:Bit)->(Bit,(Bit,Bit)){(0,(0,b))}
        meaning ZMeaning:Bit=phase_by(z_phase);
        unitary fn liar(q:Q<Bit>)->Q<Bit>{x(q)}
        observe fn main()->(Bit,Bit){
            let(c,q)=controlled(power(checked_op(liar,ZMeaning),0))(init0(),init0());
            (measure_z(c),measure_z(q))
        }";
    let error = compile_project(&SourceRoot::new(text).0).unwrap_err();
    assert_eq!(error.code, ErrorCode::Contract);
}

#[test]
fn canonical_control_zero_power_evaluates_effectful_arguments_in_source_order() {
    let text = "use std::quantum::{init0,h,x,cnot};use std::observe::measure_z;
        unitary fn oracle(q:Q<Bit>)->Q<Bit>{x(q)}
        observe fn recreate(q:Q<Bit>)->Q<Bit>{
            let b=measure_z(q);if b{x(init0())}else{init0()}
        }
        observe fn main()->(Bit,Bit){
            let(a,r)=cnot(h(init0()),init0());
            let(c,q)=controlled(power(oracle,0))(recreate(a),recreate(r));
            (measure_z(c),measure_z(q))
        }";
    let accepted = compile_project(&SourceRoot::new(text).0).unwrap();
    let distribution = run_closed(&accepted, SimulationLimits::default()).unwrap();
    assert!((distribution[&vec![false, false]] - 0.5).abs() < 1e-12);
    assert!((distribution[&vec![true, true]] - 0.5).abs() < 1e-12);
    let (a, r) = accepted
        .raw()
        .operations
        .iter()
        .find_map(|op| match op {
            RawOp::Cnot {
                control_out,
                target_out,
                ..
            } => Some((*control_out, *target_out)),
            _ => None,
        })
        .unwrap();
    let measured = accepted
        .raw()
        .operations
        .iter()
        .filter_map(|op| match op {
            RawOp::MeasureZ { input, .. } => Some(*input),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(measured.len(), 4);
    assert_eq!(measured[0], a);
    // The first argument's branch carries the untouched reference through
    // fresh phi owners before the second argument consumes it.
    let mut carried_r = r;
    for op in &accepted.raw().operations {
        match op {
            RawOp::ClassicalBranch { quantum_phis, .. } => {
                if let Some(phi) = quantum_phis
                    .iter()
                    .find(|phi| phi.then_token == carried_r && phi.else_token == carried_r)
                {
                    carried_r = phi.output;
                }
            }
            RawOp::MeasureZ { input, .. } if *input != a => break,
            _ => {}
        }
    }
    assert_eq!(measured[1], carried_r);
}

#[test]
fn canonical_inverse_application_preserves_ordinary_names_and_both_consumers() {
    let text = "use std::quantum::{h,init0}; use std::observe::measure_z;
        unitary fn inverse(q:Q<Bit>)->Q<Bit>{q}
        unitary fn oracle(q:Q<Bit>)->Q<Bit>{h(q)}
        unitary fn undo(q:Q<Bit>)->Q<Bit>{adjoint(oracle)(q)}
        pub observe fn main()->Bit{measure_z(h(undo(inverse(init0()))))}";
    let finite = compile_project(&SourceRoot::new(text).0).unwrap();
    let selected = ParsedProgram::parse(sources(text))
        .unwrap()
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower_raw()
        .unwrap();
    let native =
        qleisli::interchange::native::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
    let accepted = native.accept(selected.proposal()).unwrap();
    selected.validate_source_steps(&accepted).unwrap();
    for distribution in [
        run_closed(&finite, SimulationLimits::default()).unwrap(),
        run_closed(&accepted, SimulationLimits::default()).unwrap(),
    ] {
        // Ordinary inverse is identity; the two-stage inverse of H is H.
        // H H |0> = |0>, including interference missed by one H measurement.
        assert!((distribution[&vec![false]] - 1.0).abs() < 1e-12);
    }
}

#[test]
fn canonical_inverse_checks_unused_zero_count_generic_access() {
    for body in ["adjoint(U)(q)", "adjoint(power(U,0))(q)"] {
        let text = format!(
            "// 日本語\r\npub unitary fn bad[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>
            requires Applicable(U){{{body}}}"
        );
        let finite = check_project(&SourceRoot::new(&text).0).unwrap_err();
        let selected = ParsedProgram::parse(sources(&text)).unwrap_err();
        assert!(finite.message.contains("Adjointable"), "{finite}");
        assert!(selected.message().contains("Adjointable"), "{selected}");
        let start = text.find(body).unwrap();
        assert_eq!(selected.span(), Span::new(start, start + body.len()));
        let root = SourceRoot::new(&text);
        let module = format!("--module=main={}", root.0.join("main.qli").display());
        for json in [false, true] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
            command.args(["check", "--entry=main::bad", "--ir-profile=raw", &module]);
            if json {
                command.arg("--format=json");
            }
            let output = command.output().unwrap();
            assert!(!output.status.success());
            if json {
                let decoded = Command::new("python3")
                    .args([
                        "-c",
                        "import json,sys; v=json.loads(sys.argv[1]); d=v['diagnostics'][0]; assert v['outcome']=='error'; assert 'Adjoint' in d['message']; print(d['code']); print(d['primary']['start']); print(d['primary']['end'])",
                        std::str::from_utf8(&output.stdout).unwrap(),
                    ])
                    .output()
                    .unwrap();
                assert!(decoded.status.success(), "{decoded:?}");
                assert_eq!(
                    String::from_utf8(decoded.stdout).unwrap(),
                    format!("{}\n{}\n{}\n", selected.code(), start, start + body.len())
                );
            } else {
                assert!(
                    String::from_utf8(output.stderr)
                        .unwrap()
                        .contains("Adjointable")
                );
            }
        }
    }
}

#[test]
fn adjoint_construction_checks_access_before_outer_or_unused_descriptions() {
    for (basis, runtime_basis, constraint, body, missing) in [
        (
            "Bit",
            "Bit",
            "Applicable(U)",
            "ignored[type(Bit),adjoint(U)](q)",
            "adjoint(U)",
        ),
        (
            "Bit",
            "(Bit,Bit)",
            "Controllable(U)",
            "ignored[type((Bit,Bit)),controlled(adjoint(U))](q)",
            "adjoint(U)",
        ),
        (
            "Bit",
            "Bit",
            "Applicable(U)",
            "ignored[type(Bit),adjoint(adjoint(U))](q)",
            "adjoint(U)",
        ),
        (
            "Bit",
            "Bit",
            "Applicable(U)",
            "ignored[type(Bit),power(adjoint(U),0)](q)",
            "adjoint(U)",
        ),
        (
            "Bit",
            "Bit",
            "Applicable(U)",
            "ignored[type(Bit),adjoint(power(U,0))](q)",
            "adjoint(power(U,0))",
        ),
        (
            "Bit",
            "Bit",
            "Applicable(U)",
            "if 0 {ignored[type(Bit),adjoint(U)](q)} else {q}",
            "adjoint(U)",
        ),
        (
            "Unit",
            "Unit",
            "Applicable(U)",
            "ignored[type(Unit),adjoint(U)](q)",
            "adjoint(U)",
        ),
    ] {
        let text = format!(
            "// 日本語\r\nunitary fn ignored[const A:Basis,const V:Op<A>](q:Q<A>)->Q<A>{{q}}
             unitary fn bad[const U:Op<{basis}>](q:Q<{runtime_basis}>)->Q<{runtime_basis}>
             requires {constraint}{{{body}}}"
        );
        let selected = match ParsedProgram::parse(sources(&text)) {
            Err(error) => error,
            Ok(_) => panic!("adjoint construction accepted without its path: {text}"),
        };
        let finite = check_project_diagnostic(&SourceRoot::new(&text).0).unwrap_err();
        let start = text.find(missing).unwrap();
        let expected = Span::new(start, start + missing.len());
        assert_eq!(selected.code(), "access", "{text}\n{selected}");
        assert_eq!(selected.message(), "missing Adjointable operation access");
        assert_eq!(selected.span(), expected);
        assert_eq!(finite.code, "capability", "{text}\n{finite:?}");
        assert_eq!(finite.message, selected.message());
        assert_eq!(finite.primary.unwrap().span, expected);

        // A real declared path makes construction valid; double adjoints keep
        // their independent original Applicable requirement as well.
        let supplied = text.replace(
            &format!("requires {constraint}"),
            &format!("requires {constraint},Adjointable(U)"),
        );
        ParsedProgram::parse(sources(&supplied)).unwrap_or_else(|error| {
            panic!("{supplied}\n{error}");
        });
    }
}

fn sources(source: &str) -> BTreeMap<String, String> {
    BTreeMap::from([("main".into(), source.into())])
}

fn retirement(message: &str) {
    assert!(
        message.contains("`bind_op` was renamed to `checked_op`"),
        "{message}"
    );
    assert!(
        message.contains("checked_op(implementation, Meaning)"),
        "{message}"
    );
}

fn assert_bind(operation: &StaticOp, source: &str, implementation: &str) {
    let StaticOpKind::Bind {
        implementation: actual,
        meaning,
    } = &operation.kind
    else {
        panic!("expected the existing Bind AST, got {operation:?}");
    };
    assert_eq!(actual.text, implementation);
    assert_eq!(meaning.text, "M");
    assert_eq!(
        &source[operation.span.start..operation.span.end],
        format!("checked_op({implementation},M)")
    );
    assert_eq!(&source[actual.span.start..actual.span.end], implementation);
    assert_eq!(&source[meaning.span.start..meaning.span.end], "M");
}

#[test]
fn checked_constructor_retains_nested_static_trees_and_original_spans() {
    let source = "// 日本語\r\nunitary fn client(q:Q<Bit>)->Q<Bit>{apply[tensor_op(then_op(adjoint(checked_op(first,M)),power(checked_op(second,M),2)),controlled(checked_op(third,M)))](q)}";
    let tokens = lex(source).unwrap();
    let checked: Vec<_> = tokens
        .iter()
        .filter(|t| t.kind == TokenKind::BindOp)
        .collect();
    assert_eq!(checked.len(), 3);
    for token in checked {
        assert_eq!(&source[token.span.start..token.span.end], "checked_op");
        assert_eq!(token.kind.description(), "`checked_op`");
    }
    let module = parse_module(source).unwrap();
    let FnBody::Quantum(body) = &module.decls[0].body else {
        panic!("quantum body")
    };
    let ExprKind::Call { static_args, .. } = &body.result.kind else {
        panic!("static application")
    };
    assert_eq!(static_args.len(), 1);
    let StaticOpKind::Tensor(left, right) = &static_args[0].kind else {
        panic!("tensor")
    };
    let StaticOpKind::Then(inverse, repeat) = &left.kind else {
        panic!("ordered composition")
    };
    let StaticOpKind::Inverse(first) = &inverse.kind else {
        panic!("inverse")
    };
    let StaticOpKind::Repeat(_, second) = &repeat.kind else {
        panic!("repeat")
    };
    let StaticOpKind::Controlled(third) = &right.kind else {
        panic!("controlled")
    };
    assert_bind(first, source, "first");
    assert_bind(second, source, "second");
    assert_bind(third, source, "third");
}

#[test]
fn legacy_exact_word_is_rejected_in_identifier_and_constructor_positions() {
    for source in [
        "unitary fn bind_op(q:Q<Bit>)->Q<Bit>{q}",
        "unitary fn client(bind_op:Q<Bit>)->Q<Bit>{bind_op}",
        "unitary fn client[const bind_op:Op<Bit>](q:Q<Bit>)->Q<Bit>{q}",
        "use provider::bind_op;",
        "use bind_op::provider;",
        "unitary fn client(q:Q<Bit>)->Q<Bit>{let bind_op=q; bind_op}",
        "unitary fn client(q:Q<Bit>)->Q<Bit>{apply[adjoint(bind_op(provider,M))](q)}",
        // Complete-file lexing deliberately precedes the earlier grammar error.
        "unitary fn ; bind_op",
    ] {
        let start = source.find("bind_op").unwrap();
        let span = Span::new(start, start + "bind_op".len());
        let lexical = lex(source).unwrap_err();
        retirement(&lexical.message);
        assert_eq!(lexical.span, span, "{source}");
        for parsed in [
            parse_module(source),
            parse_documented_module(source).map(|m| m.syntax),
        ] {
            let error = parsed.unwrap_err();
            retirement(&error.message);
            assert_eq!(error.span, span, "{source}");
        }
        let root = SourceRoot::new(source);
        let finite = check_project_diagnostic(&root.0).unwrap_err();
        assert_eq!(finite.code, "parse", "{finite:?}");
        retirement(&finite.message);
        assert_eq!(finite.primary.unwrap().span, span);
        let selected = ParsedProgram::parse(sources(source)).unwrap_err();
        assert_eq!(selected.code(), "parse", "{selected}");
        assert_eq!(selected.module(), Some("main"));
        retirement(selected.message());
        assert_eq!(selected.span(), span);
    }
}

#[test]
fn comments_and_longer_names_survive_but_the_new_constructor_is_reserved() {
    let source = "/// bind_op(provider, M) is historical prose.\r\n/* bind_op /* checked_op */ */\r\npub unitary fn bind_op2(q:Q<Bit>)->Q<Bit>{q}\r\npub unitary fn checked_op2(q:Q<Bit>)->Q<Bit>{bind_op2(q)}";
    let root = SourceRoot::new(source);
    check_project(&root.0).unwrap();
    parse_documented_module(source).unwrap();
    ParsedProgram::parse(sources(source))
        .unwrap()
        .instantiate("main::checked_op2", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    for source in [
        "unitary fn checked_op(q:Q<Bit>)->Q<Bit>{q}",
        "unitary fn client(checked_op:Q<Bit>)->Q<Bit>{checked_op}",
        "use provider::checked_op;",
        "unitary fn client(q:Q<Bit>)->Q<Bit>{checked_op(provider,M)}",
    ] {
        let error = parse_module(source).unwrap_err();
        let start = source.find("checked_op").unwrap();
        assert_eq!(error.span, Span::new(start, start + "checked_op".len()));
        assert!(!error.message.contains("was renamed"), "{error}");
    }
    // Filesystem discovery still reserves the old word and reserves the new one.
    for name in ["bind_op", "checked_op"] {
        let root = SourceRoot::new("pub unitary fn id(q:Q<Bit>)->Q<Bit>{q}");
        root.write(
            &format!("{name}.qli"),
            "pub unitary fn id(q:Q<Bit>)->Q<Bit>{q}",
        );
        let error = check_project_diagnostic(&root.0).unwrap_err();
        assert_eq!(error.code, "project", "{error:?}");
        assert!(
            error.message.contains("invalid module path component"),
            "{error:?}"
        );
        assert!(error.message.contains(name), "{error:?}");
    }
}

#[test]
fn loading_checks_retired_words_even_in_an_unused_module() {
    let root = SourceRoot::new("pub unitary fn client(q:Q<Bit>)->Q<Bit>{q}");
    let dep = "// Δ\r\npub unitary fn unused(q:Q<Bit>)->Q<Bit>{apply[bind_op(provider,M)](q)}";
    root.write("dep.qli", dep);
    let start = dep.find("bind_op").unwrap();
    let span = Span::new(start, start + "bind_op".len());
    let finite = check_project_diagnostic(&root.0).unwrap_err();
    assert_eq!(finite.code, "parse");
    let primary = finite.primary.unwrap();
    assert_eq!(primary.path, root.0.join("dep.qli").canonicalize().unwrap());
    assert_eq!(primary.span, span);
    let selected = ParsedProgram::load(BTreeMap::from([
        ("main".into(), root.0.join("main.qli")),
        ("dep".into(), root.0.join("dep.qli")),
    ]))
    .unwrap_err();
    assert_eq!(selected.code(), "parse");
    assert_eq!(selected.module(), Some("dep"));
    retirement(selected.message());
    assert_eq!(selected.span(), span);
}

#[test]
fn text_and_json_preserve_utf8_crlf_migration_locations_in_both_clis() {
    let source = "// 日本語 π\r\npub unitary fn client(q:Q<Bit>)->Q<Bit>{\r\n  apply[bind_op(provider,M)](q)\r\n}";
    let root = SourceRoot::new(source);
    let start = source.find("bind_op").unwrap();
    let end = start + "bind_op".len();
    for selected in [false, true] {
        for json in [false, true] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
            command.arg("check");
            if selected {
                command.arg("--entry=main::client").arg(format!(
                    "--module=main={}",
                    root.0.join("main.qli").display()
                ));
            } else {
                command.arg(&root.0);
            }
            if json {
                command.arg("--format=json");
            }
            let output = command.output().unwrap();
            assert_eq!(output.status.code(), Some(1), "{output:?}");
            if json {
                assert!(output.stderr.is_empty(), "{output:?}");
                let text = String::from_utf8(output.stdout).unwrap();
                assert!(text.contains("\"outcome\":\"error\""), "{text}");
                assert!(text.ends_with("\"result\":null}\n"), "{text}");
                assert_eq!(text.matches("\"code\":").count(), 1, "{text}");
                assert!(
                    text.contains("\"diagnostics\":[{\"code\":\"parse\""),
                    "{text}"
                );
                retirement(&text);
                let primary = if selected {
                    let path = root
                        .0
                        .join("main.qli")
                        .to_str()
                        .unwrap()
                        .replace('\\', "\\\\")
                        .replace('"', "\\\"");
                    // The selected transport reports bytes; it does not invent coordinates.
                    format!(
                        "\"primary\":{{\"module\":\"main\",\"path\":\"{path}\",\"start\":{start},\"end\":{end}}}"
                    )
                } else {
                    format!(
                        "\"primary\":{{\"path\":\"main.qli\",\"start\":{start},\"end\":{end},\"line\":3,\"column\":9}}"
                    )
                };
                assert!(text.contains(&primary), "{text}");
            } else {
                assert!(output.stdout.is_empty(), "{output:?}");
                let text = String::from_utf8(output.stderr).unwrap();
                retirement(&text);
                if selected {
                    assert!(text.contains(&format!("main:{start}..{end}:")), "{text}");
                } else {
                    assert!(text.contains("main.qli:3:9: parse:"), "{text}");
                }
            }
        }
    }
}

fn receipt(operations: &[RawOp]) -> Arc<FunctionEvidence> {
    operations
        .iter()
        .find_map(|operation| match operation {
            RawOp::ApplyUnitary { steps, .. } => steps.iter().find_map(|step| match &step.action {
                CircuitAction::Contract { evidence, .. } => Some(Arc::clone(evidence)),
                _ => None,
            }),
            _ => None,
        })
        .expect("a checked source operation retains its receipt")
}

#[test]
fn checked_operation_keeps_controlled_phase_and_exact_source_binding() {
    let source = format!("{PRELUDE}
        unitary fn pair[const U:Op<(Bit,Bit)>](q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>
        requires Applicable(U){{U(q)}}
        observe fn main()->(Bit,Bit){{
          let q=pair[controlled(adjoint(power(checked_op(provider,ZMeaning),3)))](join(h(init0()),x(init0())));
          let(c,q)=split(q); (measure_z(h(c)),measure_z(q))
        }}");
    let root = SourceRoot::new(&source);
    let program = compile_project(&root.0).unwrap();
    // Z^3 and its inverse are Z. Its controlled phase on |+>|1> produces |->|1>.
    let distribution = run_closed(&program, SimulationLimits::default()).unwrap();
    assert!(
        (distribution[&vec![true, true]] - 1.0).abs() < 1e-12,
        "{distribution:?}"
    );
    let receipt = receipt(&program.raw().operations);
    let exact_z = [Exact::one(), Exact::zero(), Exact::zero(), Exact::phase(4)];
    assert_eq!((receipt.meaning().rows(), receipt.meaning().cols()), (2, 2));
    assert_eq!(receipt.meaning().entries(), exact_z);
    let identity = receipt.identity().clone();
    assert_eq!(identity.specification, "meaning main::ZMeaning");
    assert!(
        identity
            .sources
            .iter()
            .any(|(name, text)| name == "main" && text == &source)
    );
    receipt
        .check_binding(
            &BasisType::Bit,
            &identity,
            receipt.implementation(),
            receipt.specification(),
        )
        .unwrap();
    let mut stale = identity.clone();
    let retained = &mut stale
        .sources
        .iter_mut()
        .find(|(name, _)| name == "main")
        .unwrap()
        .1;
    *retained = retained.replace("checked_op(", "bind_op(");
    assert_ne!(stale, identity);
    assert_eq!(
        receipt.check_binding(
            &BasisType::Bit,
            &stale,
            receipt.implementation(),
            receipt.specification()
        ),
        Err(ContractError::EvidenceMismatch)
    );
    root.write("main.qli", &source.replace("checked_op(", "bind_op("));
    let error = check_project_diagnostic(&root.0).unwrap_err();
    assert_eq!(error.code, "parse");
    retirement(&error.message);
    // Editing the file does not modify the already accepted, owned artifact.
    assert!(
        (run_closed(&program, SimulationLimits::default()).unwrap()[&vec![true, true]] - 1.0).abs()
            < 1e-12
    );
    receipt
        .check_binding(
            &BasisType::Bit,
            &identity,
            receipt.implementation(),
            receipt.specification(),
        )
        .unwrap();
}

#[test]
fn rename_does_not_relax_phase_tree_or_generic_access_checks() {
    let phase = format!(
        "{PRELUDE}
        unitary fn minus_z(q:Q<Bit>)->Q<Bit>{{x(z(x(q)))}}
        unitary fn bad(q:Q<Bit>)->Q<Bit>{{use_op[checked_op(minus_z,ZMeaning)](q)}}"
    );
    let error = check_project(&SourceRoot::new(&phase).0).unwrap_err();
    assert_eq!(error.code, ErrorCode::Contract, "{error}");
    // -Z and Z have identical measurement probabilities but different exact phases.
    for (body, finite_code, common_code) in [
        (
            "unitary fn wrong(q:Q<(Unit,Bit)>)->Q<(Unit,Bit)>{q}
          unitary fn bad(q:Q<Bit>)->Q<Bit>{use_op[checked_op(wrong,ZMeaning)](q)}",
            ErrorCode::TypeMismatch,
            "type",
        ),
        (
            "unitary fn missing[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Controllable(U){U(q)}
          unitary fn bad(q:Q<Bit>)->Q<Bit>{missing[checked_op(provider,ZMeaning)](q)}",
            ErrorCode::Capability,
            "access",
        ),
    ] {
        let source = format!("{PRELUDE}{body}");
        let error = check_project(&SourceRoot::new(&source).0).unwrap_err();
        assert_eq!(error.code, finite_code, "{error}");
        let selected = ParsedProgram::parse(sources(&source)).unwrap_err();
        assert_eq!(selected.code(), common_code, "{selected}");
        assert!(
            !selected
                .message()
                .contains("unsupported static operation constructor")
        );
    }
}

#[test]
fn abstract_checked_provider_is_still_refused_by_finite_materialization() {
    let source = format!("{PRELUDE}
        unitary fn abstracted[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){{use_op[checked_op(U,ZMeaning)](q)}}
        observe fn main()->Bit{{measure_z(abstracted[provider](init0()))}}");
    let error = compile_project(&SourceRoot::new(&source).0).unwrap_err();
    assert_eq!(error.code, ErrorCode::TypeMismatch, "{error}");
    assert!(
        error
            .message
            .contains("checked_op requires closed declarations"),
        "{error}"
    );
}

#[test]
fn selected_checked_constructor_retains_requests_and_checks_real_provider() {
    let source = format!(
        "{PRELUDE}
        pub unitary fn client(q:Q<Bit>)->Q<Bit>{{use_op[checked_op(provider,ZMeaning)](q)}}"
    );
    // Preserve the old repeat_static provider's concrete-profile limit;
    // checked_op itself is now projected with its original request intact.
    let parsed = ParsedProgram::parse(sources(&source)).unwrap();
    let instance = parsed
        .instantiate("main::client", BTreeMap::new(), BTreeMap::new())
        .unwrap();
    assert_eq!(instance.elaborate().unwrap_err().code(), "unsupported");
    for honest in [true, false] {
        let provider = if honest { "phase[1,1](q)" } else { "q" };
        let text = source.replace("power(t,4)(q)", provider).replace(
            "use std::quantum::init0;",
            "use std::quantum::init0; use std::quantum::phase;",
        );
        let source = ParsedProgram::parse(sources(&text))
            .unwrap()
            .instantiate("main::client", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        assert!(source.has_operation_meanings());
        assert_eq!(source.lower().unwrap_err().code(), "meaning");
        let checked = source.check_operation_meanings(
            &qleisli::interchange::native::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap()),
            &mut qleisli::contract::exact::Budget::new(qleisli::contract::DEFAULT_EXACT_WORK),
        );
        if honest {
            let graph = checked.unwrap().lower_hierarchy().unwrap();
            qleisli::interchange::hierarchical::Kernel::new(
                std::env::var_os("QLEISLI_KERNEL").unwrap(),
            )
            .check_against_native(graph.payload(), graph.comparison_request())
            .unwrap();
        } else {
            assert_eq!(checked.unwrap_err().code(), "contract");
        }
    }
}

#[test]
fn canonical_power_retains_operation_count_and_original_source_spans() {
    let text = "// 日本語\r\npub unitary fn f(q:Q<Bit>)->Q<Bit>{power(adjoint(U),2^e)(q)}";
    let module = parse_module(text).unwrap();
    let FnBody::Quantum(body) = &module.decls[0].body else {
        panic!("quantum body")
    };
    let ExprKind::ApplyStatic { operation, input } = &body.result.kind else {
        panic!("explicit constructed application")
    };
    assert_eq!(
        &text[body.result.span.start..body.result.span.end],
        "power(adjoint(U),2^e)(q)"
    );
    assert_eq!(
        &text[operation.span.start..operation.span.end],
        "power(adjoint(U),2^e)"
    );
    assert_eq!(&text[input.span.start..input.span.end], "q");
    let StaticOpKind::Repeat(qleisli::frontend::ast::Count::Power(exponent), child) =
        &operation.kind
    else {
        panic!("retained repeat description")
    };
    assert_eq!(&text[exponent.span.start..exponent.span.end], "e");
    assert!(matches!(child.kind, StaticOpKind::Inverse(_)));
}

#[test]
fn canonical_power_literal_execution_keeps_ordinary_names_in_both_consumers() {
    for (count, expected) in [(0, false), (1, true), (2, false)] {
        let text = format!(
            "use std::quantum::{{x,init0}}; use std::observe::measure_z;
            unitary fn power(q:Q<Bit>,b:Bit)->Q<Bit>{{q}}
            unitary fn oracle(q:Q<Bit>)->Q<Bit>{{x(q)}}
            pub observe fn main()->Bit{{measure_z(power(oracle,{count})(power(init0(),0)))}}"
        );
        let finite = compile_project(&SourceRoot::new(&text).0).unwrap();
        let selected = ParsedProgram::parse(sources(&text))
            .unwrap()
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap()
            .lower_raw()
            .unwrap();
        let accepted = qleisli::interchange::native::Kernel::selected()
            .unwrap()
            .accept(selected.proposal())
            .unwrap();
        selected.validate_source_steps(&accepted).unwrap();
        for program in [&finite, &accepted] {
            let distribution = run_closed(program, SimulationLimits::default()).unwrap();
            assert!((distribution[&vec![expected]] - 1.0).abs() < 1e-12);
        }
    }
}

#[test]
fn canonical_power_zero_and_unused_still_require_apply_and_a_valid_count() {
    for body in [
        "power(U,0)(q)",
        "adjoint(power(U,0))(q)",
        "controlled(power(U,0))(c,q)",
    ] {
        let (signature, access) = if body.starts_with("controlled") {
            ("(c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)", "Applicable(U)")
        } else if body.starts_with("adjoint") {
            ("(q:Q<Bit>)->Q<Bit>", "Applicable(U)")
        } else {
            ("(q:Q<Bit>)->Q<Bit>", "Adjointable(U)")
        };
        let text = format!(
            "// 日本語\r\nunitary fn unused[const U:Op<Bit>]{signature} requires {access} {{{body}}}"
        );
        let error = ParsedProgram::parse(sources(&text)).unwrap_err();
        let wanted = if body.starts_with("controlled") {
            "Controllable"
        } else if body.starts_with("adjoint") {
            "Adjointable"
        } else {
            "Applicable"
        };
        assert!(error.message().contains(wanted), "{error}");
        let start = text.find(body).unwrap();
        assert_eq!(error.span(), Span::new(start, start + body.len()));
        assert!(check_project(&SourceRoot::new(&text).0).is_err());
    }
    for expression in [
        "power(U,3^2)(q)",
        "power(U,0,1)(q)",
        "power(U)(q)",
        "power(U,-1)(q)",
    ] {
        assert!(
            parse_module(&format!("unitary fn f(q:Q<Bit>)->Q<Bit>{{{expression}}}")).is_err(),
            "{expression}"
        );
    }
}

#[test]
fn canonical_power_zero_evaluates_its_argument_and_bounded_counts_reject() {
    let text = "use std::quantum::{x,init0}; use std::observe::measure_z; unitary fn oracle(q:Q<Bit>)->Q<Bit>{x(q)} pub observe fn main()->Bit{measure_z(power(oracle,0)(x(init0())))}";
    let finite = compile_project(&SourceRoot::new(text).0).unwrap();
    let raw = ParsedProgram::parse(sources(text))
        .unwrap()
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower_raw()
        .unwrap();
    let accepted = qleisli::interchange::native::Kernel::selected()
        .unwrap()
        .accept(raw.proposal())
        .unwrap();
    raw.validate_source_steps(&accepted).unwrap();
    for program in [&finite, &accepted] {
        assert!(
            (run_closed(program, SimulationLimits::default()).unwrap()[&vec![true]] - 1.0).abs()
                < 1e-12
        );
    }
    let text = "use std::quantum::x; unitary fn oracle(q:Q<Bit>)->Q<Bit>{x(q)} pub unitary fn f(q:Q<Bit>)->Q<Bit>{power(oracle,4097)(q)}";
    assert!(compile_project(&SourceRoot::new(text).0).is_err());
    assert!(
        ParsedProgram::parse(sources(text))
            .and_then(|program| program.instantiate("main::f", BTreeMap::new(), BTreeMap::new()))
            .and_then(|instance| instance.elaborate())
            .is_err()
    );
    let text = "use helper::power; pub unitary fn f(q:Q<Bit>)->Q<Bit>{power(q)}";
    let helper = "pub unitary fn power(q:Q<Bit>)->Q<Bit>{q}";
    let root = SourceRoot::new(text);
    root.write("helper.qli", helper);
    check_project(&root.0).unwrap();
    ParsedProgram::parse(BTreeMap::from([
        ("main".into(), text.into()),
        ("helper".into(), helper.into()),
    ]))
    .unwrap()
    .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
    .unwrap()
    .elaborate()
    .unwrap();
    // Direct qualified runtime calls remain outside the existing grammar.
    assert!(parse_module("unitary fn power(q:Q<Bit>)->Q<Bit>{q} pub unitary fn f(q:Q<Bit>)->Q<Bit>{main::power(q)}").is_err());
}
