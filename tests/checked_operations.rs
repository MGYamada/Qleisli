//! The constructor rename preserves finite evidence and existing profile refusals.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
mod common;

use common::SourceRoot;
use qleisli::contract::exact::Exact;
use qleisli::contract::{BasisType, ContractError, FunctionEvidence};
use qleisli::frontend::ast::{ExprKind, FnBody, Span, StaticOp, StaticOpKind};
use qleisli::frontend::compile::{
    ErrorCode, check_project, check_project_diagnostic, compile_project,
};
use qleisli::frontend::lexer::{TokenKind, lex};
use qleisli::frontend::parser::{parse_documented_module, parse_module};
use qleisli::frontend::sized::ParsedProgram;
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
unitary fn provider(q:Q<Bit>)->Q<Bit>{repeat_static(4,t,q)}
unitary fn use_op[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){U(q)}
";

#[test]
fn canonical_inverse_application_preserves_ordinary_names_and_both_consumers() {
    let text = "use std::quantum::{h,init0}; use std::observe::measure_z;
        unitary fn inverse(q:Q<Bit>)->Q<Bit>{q}
        unitary fn oracle(q:Q<Bit>)->Q<Bit>{h(q)}
        unitary fn undo(q:Q<Bit>)->Q<Bit>{inverse(oracle)(q)}
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
    for body in ["inverse(U)(q)", "inverse(repeat_op(0,U))(q)"] {
        let text = format!(
            "// 日本語\r\npub unitary fn bad[static U:Op<Bit>](q:Q<Bit>)->Q<Bit>
            requires Apply(U){{{body}}}"
        );
        let finite = check_project(&SourceRoot::new(&text).0).unwrap_err();
        let selected = ParsedProgram::parse(sources(&text)).unwrap_err();
        assert!(finite.message.contains("Adjoint"), "{finite}");
        assert!(selected.message().contains("Adjoint"), "{selected}");
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
                        .contains("Adjoint")
                );
            }
        }
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
    let source = "// 日本語\r\nunitary fn client(q:Q<Bit>)->Q<Bit>{apply[tensor_op(then_op(inverse_op(checked_op(first,M)),repeat_op(2,checked_op(second,M))),controlled_op(checked_op(third,M)))](q)}";
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
        "unitary fn client[static bind_op:Op<Bit>](q:Q<Bit>)->Q<Bit>{q}",
        "use provider::bind_op;",
        "use bind_op::provider;",
        "unitary fn client(q:Q<Bit>)->Q<Bit>{let bind_op=q; bind_op}",
        "unitary fn client(q:Q<Bit>)->Q<Bit>{apply[inverse_op(bind_op(provider,M))](q)}",
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
        unitary fn pair[static U:Op<(Bit,Bit)>](q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>
        requires Apply(U){{U(q)}}
        observe fn main()->(Bit,Bit){{
          let q=pair[controlled_op(inverse_op(repeat_op(3,checked_op(provider,ZMeaning))))](join(h(init0()),x(init0())));
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
            "unitary fn missing[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Controlled(U){U(q)}
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
        unitary fn abstracted[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){{use_op[checked_op(U,ZMeaning)](q)}}
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
        let text = source.replace("repeat_static(4,t,q)", provider).replace(
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
