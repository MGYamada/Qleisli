//! Small first-order/static conformance checks, not source-preservation proofs.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
mod common;

use common::SourceRoot;
use qleisli::contract::exact::Exact;
use qleisli::frontend::ast::Span;
use qleisli::frontend::compile::ParsedProgram;
use qleisli::frontend::compile::{check_project, check_project_with_kernel, compile_project};
use qleisli::frontend::project::SourcePolicy;
use qleisli::interchange::native::Kernel;
use qleisli::ir::{CircuitAction, Effect, RawOp};
use qleisli::sim::{SimulationLimits, run_closed};
use std::collections::BTreeMap;

fn sources(source: &str) -> BTreeMap<String, String> {
    BTreeMap::from([("main".into(), source.into())])
}

fn shared_rejection(
    source: &str,
    common_code: &str,
    finite_code: &str,
    located: &str,
    message: &str,
) {
    let start = source.rfind(located).unwrap();
    let span = Span::new(start, start + located.len());
    let selected = ParsedProgram::parse(sources(source)).unwrap_err();
    assert_eq!(selected.code(), common_code, "{source}\n{selected}");
    assert_eq!(selected.module(), Some("main"));
    assert_eq!(selected.span(), span, "{source}\n{selected}");
    assert_eq!(selected.message(), message);

    let root = SourceRoot::new(source);
    let absent = root.0.join("must-not-start-a-native-checker");
    assert!(!absent.exists());
    // Configure the existing public gate explicitly. An accidental acceptance
    // would reach the missing checker and fail with a different diagnostic.
    let finite = check_project_with_kernel(&root.0, SourcePolicy::default(), &Kernel::new(absent))
        .unwrap_err();
    assert_eq!(finite.code, finite_code, "{source}\n{finite:?}");
    assert_eq!(finite.message, message);
    let location = finite.primary.unwrap();
    assert_eq!(
        location.path,
        root.0.join("main.qli").canonicalize().unwrap()
    );
    assert_eq!(location.span, span, "{source}");
}

#[test]
fn ordinary_calls_are_complete_first_order_calls_in_both_source_paths() {
    let declaration = "unitary fn pair(flag:Bit,q:Q<Bit>)->(Bit,Q<Bit>){(flag,q)}";
    let complete = format!(
        "{declaration}
        pub unitary fn client(q:Q<Bit>)->(Bit,Q<Bit>){{pair(1,q)}}"
    );
    check_project(&SourceRoot::new(&complete).0).unwrap();
    let prepared = ParsedProgram::parse(sources(&complete)).unwrap();
    prepared
        .instantiate("main::client", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    // Neither omission constructs a partially applied callable. Arity is
    // checked before the lone argument can be interpreted as a captured value.
    for partial in ["pair(1)", "pair(q)"] {
        let source = format!(
            "{declaration}
            pub unitary fn client(q:Q<Bit>)->(Bit,Q<Bit>){{{partial}}}"
        );
        shared_rejection(
            &source,
            "arity",
            "arity",
            partial,
            "runtime argument arity mismatch",
        );
    }
    let local = format!(
        "{declaration}
        pub unitary fn client(q:Q<Bit>)->Q<Bit>{{let pair=0; pair(q)}}"
    );
    shared_rejection(
        &local,
        "type",
        "type_mismatch",
        "pair",
        "a local value is not callable",
    );
}

#[test]
fn nested_quantum_environments_cannot_be_reused_as_callables_or_providers() {
    let declarations = "
        unitary fn operator(q:Q<Bit>)->Q<Bit>{q}
        unitary fn apply[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}";
    // The first environment owns no physical wire, but still contains Q<Unit>.
    // The second hides one physical qubit as well; neither becomes classical
    // merely because an ordinary tuple/Bit surrounds that quantum ownership.
    for environment in ["(Bit,(Q<Unit>,Unit))", "(Bit,(Q<Unit>,Q<Bit>))"] {
        for spent in [false, true] {
            let transfer = if spent { "let saved=operator;" } else { "" };
            let result = if spent { "saved" } else { "operator" };
            for (call, message) in [
                ("operator(q)", "a local value is not callable"),
                (
                    "apply[operator](q)",
                    "a local or spent runtime value cannot be a static operation",
                ),
            ] {
                let source = format!(
                    "{declarations}
                    pub unitary fn client(env:{environment},q:Q<Bit>)->({environment},Q<Bit>){{
                        let operator=env; {transfer} ({result},{call})
                    }}"
                );
                shared_rejection(&source, "type", "type_mismatch", "operator", message);
            }
        }
        let duplicated = format!(
            "pub unitary fn client(env:{environment})->({environment},{environment}){{(env,env)}}"
        );
        shared_rejection(
            &duplicated,
            "ownership",
            "ownership",
            "env",
            "quantum ownership `env` has already been consumed",
        );
    }
}

#[test]
fn reusing_a_static_formal_composes_actions_without_duplicating_its_live_owner() {
    let source = "
        use std::quantum::init0; use std::quantum::h;
        use std::quantum::x; use std::quantum::cnot;
        use std::observe::measure_z;
        unitary fn flip(q:Q<Bit>)->Q<Bit>{x(q)}
        unitary fn apply[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
        pub unitary fn twice[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>
        requires Applicable(U){apply[then_op(U,U)](q)}
        unitary fn actual(q:Q<Bit>)->Q<Bit>{twice[flip](q)}
        unitary fn identity(q:Q<Bit>)->Q<Bit>{q}
        unitary fn exact(q:Q<Bit>)->Q<Bit>{apply_contract(actual,identity,q)}
        observe fn main()->(Bit,Bit){
            let(a,r)=cnot(h(init0()),init0());
            let a=exact(a);
            (measure_z(h(a)),measure_z(h(r)))
        }";
    let common = ParsedProgram::parse(sources(source)).unwrap();
    assert_eq!(
        common.function_effect("main::twice").unwrap().inferred(),
        Effect::Unitary
    );
    // The common judgment is a preparation result, not a selected-profile
    // lowering or evidence claim. Native execution below uses the finite path.
    let program = compile_project(&SourceRoot::new(source).0).unwrap();
    // Request the complete, phase-fixed equation X ∘ X = +I at the existing
    // native function-contract gate. The target identity is separate source;
    // a measurement histogram or equality up to global phase is insufficient.
    let receipt = program
        .raw()
        .operations
        .iter()
        .find_map(|operation| match operation {
            RawOp::ApplyUnitary { steps, .. } => steps.iter().find_map(|step| match &step.action {
                CircuitAction::Contract { evidence, .. }
                    if evidence.identity().implementation == "main::actual"
                        && evidence.identity().specification == "main::identity" =>
                {
                    Some(evidence)
                }
                _ => None,
            }),
            _ => None,
        })
        .expect("the actual/identity equation retains native checked evidence");
    assert_eq!(receipt.meaning().rows(), 2);
    assert_eq!(receipt.meaning().cols(), 2);
    assert_eq!(
        receipt.meaning().entries(),
        [Exact::one(), Exact::zero(), Exact::zero(), Exact::one()]
    );
    assert!(
        receipt
            .identity()
            .sources
            .iter()
            .any(|(module, retained)| module == "main" && retained == source)
    );
    let actual = run_closed(&program, SimulationLimits::default()).unwrap();
    // Supplemental reference control: identity on one Bell half leaves
    // (|00>+|11>)/sqrt(2); X readout gives only 00 and 11, each with weight 1/2.
    let expected = BTreeMap::from([(vec![false, false], 0.5), (vec![true, true], 0.5)]);
    assert!(
        (actual.values().sum::<f64>() - 1.0).abs() < 1e-12,
        "{actual:?}"
    );
    for outcome in actual.keys().chain(expected.keys()) {
        let got = actual.get(outcome).copied().unwrap_or(0.0);
        let want = expected.get(outcome).copied().unwrap_or(0.0);
        assert!(
            (got - want).abs() < 1e-12,
            "{outcome:?}: {got}, expected {want}; {actual:?}"
        );
    }
    let duplicate = "pub unitary fn bad[const U:Op<Bit>](q:Q<Bit>)->(Q<Bit>,Q<Bit>)
        requires Applicable(U){(U(q),U(q))}";
    shared_rejection(
        duplicate,
        "ownership",
        "ownership",
        "q",
        "quantum ownership `q` has already been consumed",
    );
}
