//! Explicit, retained function-contract boundaries through the real frontend.

mod common;

use std::collections::BTreeMap;
use std::sync::Arc;

use common::SourceRoot;
use qleisli::contract::FunctionEvidence;
use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::frontend::parser::parse_module;
use qleisli::ir::{CircuitAction, RawOp};
use qleisli::sim::{SimulationError, SimulationLimits, run_closed};

const IMPORTS: &str = "
use std::quantum::init0; use std::quantum::h; use std::quantum::x;
use std::quantum::z; use std::quantum::t; use std::quantum::cnot;
use std::quantum::join; use std::quantum::split;
use std::observe::measure_z; use std::observe::discard;
classical fn predicate(value: Bit) -> Bit { value }
unitary fn identity(q: Q<Bit>) -> Q<Bit> { q }
unitary fn specified_phase(q: Q<Bit>) -> Q<Bit> { z(q) }
";

fn probability(actual: &BTreeMap<Vec<bool>, f64>, outcome: &[bool], expected: f64) {
    assert!(
        (actual.get(outcome).copied().unwrap_or(0.0) - expected).abs() < 1e-12,
        "{actual:?}: expected {outcome:?} with probability {expected}"
    );
}

#[test]
fn observing_contracts_compare_complete_instruments_on_the_emitted_call() {
    for implementation in ["measure_z(h(h(q)))", "measure_z(t(q))"] {
        let source = format!(
            "{IMPORTS}
            fn reference(q: Q<Bit>) -> Bit {{ measure_z(q) }}
            fn implementation(q: Q<Bit>) -> Bit {{ {implementation} }}
            observe fn main() -> Bit {{ apply_contract(implementation,reference,x(init0())) }}"
        );
        let root = SourceRoot::new(&source);
        let accepted = compile_project(&root.0).unwrap_or_else(|error| panic!("{source}\n{error}"));
        assert!(
            accepted.request().is_none(),
            "a call is not a whole-root request"
        );
        assert!(
            evidence(accepted.program().operations.as_slice()).is_empty(),
            "Observe does not become a pure circuit action"
        );
        probability(
            &run_closed(&accepted, SimulationLimits::default()).unwrap(),
            &[true],
            1.0,
        );
        assert!(format!("{accepted:?}").contains("InstrumentCall"));
    }
}

#[test]
fn observing_contracts_reject_public_relabeling_and_wrong_residual_channels() {
    rejects(
        &format!(
            "{IMPORTS}
        fn reference(q: Q<Bit>) -> Bit {{ measure_z(q) }}
        fn implementation(q: Q<Bit>) -> Bit {{ not(measure_z(q)) }}
        observe fn main() -> Bit {{ apply_contract(implementation,reference,init0()) }}"
        ),
        ErrorCode::Contract,
    );
    // Both public probabilities agree for every input. The outcome-one
    // residual differs, which an off-diagonal-capable instrument gate detects.
    rejects(
        &format!(
            "{IMPORTS}
        fn reference(q: Q<Bit>) -> (Bit,Q<Bit>) {{
            let (q,copy)=cnot(q,init0()); (measure_z(copy),q)
        }}
        fn implementation(q: Q<Bit>) -> (Bit,Q<Bit>) {{ (measure_z(q),init0()) }}
        fn unused(q: Q<Bit>) -> (Bit,Q<Bit>) {{ apply_contract(implementation,reference,q) }}"
        ),
        ErrorCode::Contract,
    );
}

#[test]
fn observing_contracts_keep_zero_owners_nested_results_and_external_references() {
    let result = run(&format!("{IMPORTS}
        fn reference(q: Q<Bit>) -> (Unit,(Bit,Q<Unit>)) {{ let (q,empty)=split(basis q as value {{ (value,()) }}); ((),(measure_z(q),empty)) }}
        fn implementation(q: Q<Bit>) -> (Unit,(Bit,Q<Unit>)) {{ let (q,empty)=split(basis q as value {{ (value,()) }}); ((),(measure_z(h(h(q))),empty)) }}
        fn main() -> (Bit,Bit) {{
            let (r,q)=cnot(h(init0()),init0());
            let (u,(b,empty))=apply_contract(implementation,reference,q);
            discard(empty); (measure_z(r),b)
        }}"));
    probability(&result, &[false, false], 0.5);
    probability(&result, &[true, true], 0.5);
    assert_eq!(result.len(), 2);
}

#[test]
fn observing_contracts_preserve_unused_false_obligations_and_principal_effects() {
    rejects(
        &format!(
            "{IMPORTS}
        observe fn reference(q: Q<Bit>) -> Q<Bit> {{ q }}
        fn implementation(q: Q<Bit>) -> Q<Bit> {{ let b=measure_z(init0()); q }}
        fn unused(q: Q<Bit>) -> Q<Bit> {{ apply_contract(implementation,reference,q) }}"
        ),
        ErrorCode::Effect,
    );
    rejects(
        &format!(
            "{IMPORTS}
        fn reference(q: Q<Bit>) -> (Bit,Unit) {{ (measure_z(q),()) }}
        fn implementation(q: Q<Bit>) -> (Unit,Bit) {{ ((),measure_z(q)) }}
        fn unused(q: Q<Bit>) -> (Unit,Bit) {{ apply_contract(implementation,reference,q) }}"
        ),
        ErrorCode::TypeMismatch,
    );
    rejects(&format!("{IMPORTS}
        fn reference(q: Q<Bit>) -> Bit {{ measure_z(q) }}
        fn implementation(q: Q<Bit>) -> Bit {{ not(measure_z(q)) }}
        fn unused[const o: Op<Bit>](q: Q<Bit>) -> Bit {{ apply_contract(implementation,reference,q) }}"), ErrorCode::Contract);
}

#[test]
fn observing_contracts_check_nested_calls_branches_and_hidden_discard_histories() {
    let result = run(&format!(
        "{IMPORTS}
        fn reference(q: Q<Bit>) -> Bit {{ measure_z(q) }}
        fn inner(q: Q<Bit>) -> Bit {{ apply_contract(reference,reference,q) }}
        fn implementation(q: Q<Bit>) -> Bit {{ discard(h(init0())); inner(q) }}
        fn main() -> (Bit,Bit) {{
            let flag=measure_z(h(init0()));
            let q=x(init0());
            let value=if flag {{ apply_contract(implementation,reference,q) }}
                       else {{ apply_contract(inner,reference,q) }};
            (flag,value)
        }}"
    ));
    probability(&result, &[false, true], 0.5);
    probability(&result, &[true, true], 0.5);
}

#[test]
fn observing_reference_source_replacement_requires_a_fresh_equation() {
    let root = SourceRoot::new(&format!(
        "{IMPORTS}
        use reference::readout;
        fn implementation(q: Q<Bit>) -> Bit {{ measure_z(h(h(q))) }}
        fn main() -> Bit {{ apply_contract(implementation,readout,x(init0())) }}"
    ));
    root.write(
        "reference.qli",
        "use std::observe::measure_z; pub fn readout(q: Q<Bit>) -> Bit { measure_z(q) }",
    );
    let original = compile_project(&root.0).unwrap();
    root.write(
        "reference.qli",
        "use std::observe::measure_z; pub fn readout(q: Q<Bit>) -> Bit { not(measure_z(q)) }",
    );
    assert_eq!(
        compile_project(&root.0).unwrap_err().code,
        ErrorCode::Contract
    );
    probability(
        &run_closed(&original, SimulationLimits::default()).unwrap(),
        &[true],
        1.0,
    );
}

#[test]
fn pure_contracts_still_reject_equal_width_non_endomorphic_basis_trees() {
    let source = "fn reshape(q: Q<Bit>) -> Q<(Bit,Unit)> { basis q as value { (value,()) } }
        fn unused(q: Q<Bit>) -> Q<(Bit,Unit)> { apply_contract(reshape,reshape,q) }";
    let error = qleisli::frontend::compile::ParsedProgram::parse(BTreeMap::from([(
        "main".into(),
        source.into(),
    )]))
    .unwrap_err();
    assert_eq!(error.code(), "type");
    assert!(error.to_string().contains("same exact Q<A> output"));
    rejects(source, ErrorCode::TypeMismatch);
}

fn run(source: &str) -> BTreeMap<Vec<bool>, f64> {
    let root = SourceRoot::new(source);
    let ir = compile_project(&root.0).unwrap_or_else(|error| panic!("{source}\n{error}"));
    let result = run_closed(&ir, SimulationLimits::default()).unwrap();
    assert!((result.values().sum::<f64>() - 1.0).abs() < 1e-12);
    result
}

fn evidence(operations: &[RawOp]) -> Vec<&Arc<FunctionEvidence>> {
    operations
        .iter()
        .filter_map(|op| match op {
            RawOp::ApplyUnitary { steps, .. } => Some(steps),
            _ => None,
        })
        .flatten()
        .filter_map(|step| match &step.action {
            CircuitAction::Contract { evidence, .. } => Some(evidence),
            _ => None,
        })
        .collect()
}

fn rejects(source: &str, expected: ErrorCode) {
    let root = SourceRoot::new(source);
    let error = check_project(&root.0).unwrap_err();
    assert_eq!(error.code, expected, "{source}\n{error}");
}

#[test]
fn unchanged_client_requires_one_specification_across_private_layouts() {
    let root = SourceRoot::new(&format!(
        "{IMPORTS} use implementation::phase;
        unitary fn client(q: Q<Bit>) -> Q<Bit> {{ apply_contract(phase,specified_phase,q) }}
        observe fn main() -> ((Bit,Bit),Bit) {{
            let (r,q)=cnot(h(init0()),init0());
            let q=client(q);
            let (r,q)=cnot(r,q);
            let pair=(measure_z(h(r)),measure_z(q));
            let (c,target)=qif(h(init0()),x(init0())) {{ 0 => identity, 1 => client }};
            discard(target);
            (pair,measure_z(h(c)))
        }}"
    ));
    for body in [
        "z(q)",
        "with_computed(q,predicate) { |a| z(a) }",
        "with_computed(q,predicate,specified_phase) { |d,a| (d,h(h(z(a)))) }",
    ] {
        root.write(
            "implementation.qli",
            &format!("{IMPORTS} pub unitary fn phase(q: Q<Bit>) -> Q<Bit> {{ {body} }}"),
        );
        let program = compile_project(&root.0).unwrap();
        let attached = evidence(&program.program().operations);
        assert_eq!(attached.len(), 2);
        assert!(Arc::ptr_eq(attached[0], attached[1]));
        assert_eq!(
            attached[0].identity().implementation,
            "implementation::phase"
        );
        assert_eq!(
            attached[0].identity().specification,
            "main::specified_phase"
        );
        probability(
            &run_closed(&program, SimulationLimits::default()).unwrap(),
            &[true, false, true],
            1.0,
        );
    }
}

#[test]
fn nested_function_evidence_survives_external_inverse_and_control() {
    let root = SourceRoot::new(&format!(
        "{IMPORTS}
        unitary fn implementation(q: Q<Bit>) -> Q<Bit> {{ with_computed(q,predicate) {{ |a| t(a) }} }}
        unitary fn specified(q: Q<Bit>) -> Q<Bit> {{ t(q) }}
        unitary fn first(q: Q<Bit>) -> Q<Bit> {{ apply_contract(implementation,specified,q) }}
        unitary fn second(q: Q<Bit>) -> Q<Bit> {{ apply_contract(first,specified,q) }}
        unitary fn top(q: Q<Bit>) -> Q<Bit> {{ apply_contract(second,specified,q) }}
        unitary fn inverse(q: Q<Bit>) -> Q<Bit> {{ adjoint(top)(q) }}
        observe fn main() -> (Bit,Bit) {{
            let q=power(top,2)(h(init0()));
            let q=adjoint(top)(adjoint(top)(q));
            let (c,target)=qif(h(init0()),x(init0())) {{ 0 => identity, 1 => inverse }};
            discard(target);
            let c=power(t,6)(c);
            (measure_z(h(q)),measure_z(h(c)))
        }}"
    ));
    let program = compile_project(&root.0).unwrap();
    let attached = evidence(&program.program().operations);
    assert_eq!(attached.len(), 5);
    assert_eq!(attached[0].depth(), 3);
    assert!(attached.iter().all(|value| Arc::ptr_eq(attached[0], value)));
    let result = run_closed(&program, SimulationLimits::default()).unwrap();
    probability(&result, &[false, false], (1.0 - 1.0 / 2.0_f64.sqrt()) / 2.0);
    probability(&result, &[false, true], (1.0 + 1.0 / 2.0_f64.sqrt()) / 2.0);
}

#[test]
fn incorrect_implementations_cannot_change_the_clients_meaning() {
    for body in ["q", "x(q)", "t(q)", "with_computed(q,zero) { |a| z(a) }"] {
        rejects(
            &format!(
                "{IMPORTS} classical fn zero(value: Bit) -> Bit {{ 0 }}
                unitary fn implementation(q: Q<Bit>) -> Q<Bit> {{ {body} }}
                unitary fn client(q: Q<Bit>) -> Q<Bit> {{
                    apply_contract(implementation,specified_phase,q)
                }}"
            ),
            ErrorCode::Contract,
        );
    }
}

#[test]
fn repeated_calls_reuse_one_immutable_evidence_object() {
    let root = SourceRoot::new(&format!(
        "{IMPORTS}
        unitary fn implementation(q: Q<Bit>) -> Q<Bit> {{
            with_computed(q,predicate) {{ |a| z(a) }}
        }}
        unitary fn phase(q: Q<Bit>) -> Q<Bit> {{ apply_contract(implementation,specified_phase,q) }}
        observe fn main() -> Bit {{
            let q=phase(h(init0()));
            let q=phase(q);
            measure_z(h(q))
        }}"
    ));
    let program = compile_project(&root.0).unwrap();
    let attached = evidence(&program.program().operations);
    assert_eq!(attached.len(), 2);
    assert!(Arc::ptr_eq(attached[0], attached[1]));
    probability(
        &run_closed(&program, SimulationLimits::default()).unwrap(),
        &[false],
        1.0,
    );
}

#[test]
fn repeated_contract_calls_do_not_recompare_frozen_source_snapshots() {
    let statements = "let q=apply_contract(specified_phase,specified_phase,q);".repeat(60);
    let source = format!(
        "{IMPORTS}\n// {}\nobserve fn main() -> Bit {{
            let q=init0(); {statements} measure_z(q)
        }}",
        "metadata".repeat(1500)
    );
    let root = SourceRoot::new(&source);
    let program = compile_project(&root.0).unwrap();
    let attached = evidence(&program.program().operations);
    assert_eq!(attached.len(), 60);
    assert!(attached.iter().all(|item| Arc::ptr_eq(item, attached[0])));
    probability(
        &run_closed(&program, SimulationLimits::default()).unwrap(),
        &[false],
        1.0,
    );
}

#[test]
fn unrelated_source_comments_do_not_multiply_contract_reuse_work() {
    let root = SourceRoot::new(&format!(
        "{IMPORTS}
        unitary fn first(q: Q<Bit>) -> Q<Bit> {{ apply_contract(specified_phase,specified_phase,q) }}
        unitary fn second(q: Q<Bit>) -> Q<Bit> {{ apply_contract(first,specified_phase,q) }}
        unitary fn third(q: Q<Bit>) -> Q<Bit> {{ apply_contract(second,specified_phase,q) }}
        unitary fn fourth(q: Q<Bit>) -> Q<Bit> {{ apply_contract(third,specified_phase,q) }}
        unitary fn fifth(q: Q<Bit>) -> Q<Bit> {{ apply_contract(fourth,specified_phase,q) }}
        observe fn main() -> Bit {{
            let q=fifth(h(init0())); let q=fifth(q); measure_z(h(q))
        }}"
    ));
    let comments = format!("// {}\n", "metadata".repeat(12_500));
    root.write("unrelated.qli", &comments);
    let program = compile_project(&root.0).unwrap();
    let attached = evidence(&program.program().operations);
    assert_eq!(attached.len(), 2);
    assert!(Arc::ptr_eq(attached[0], attached[1]));
    assert_eq!(attached[0].depth(), 5);
    // Source binding remains exact and retains the whole loaded project.
    assert!(
        attached[0]
            .identity()
            .sources
            .iter()
            .any(|(name, text)| name == "unrelated" && text == &comments)
    );
    probability(
        &run_closed(&program, SimulationLimits::default()).unwrap(),
        &[false],
        1.0,
    );
}

const BUDGETED_FUNCTIONS: &str = "
unitary fn implementation(q: Q<Bit>) -> Q<Bit> { power(t,8)(q) }
unitary fn inner(q: Q<Bit>) -> Q<Bit> { apply_contract(implementation,identity,q) }
unitary fn outer(q: Q<Bit>) -> Q<Bit> { apply_contract(inner,identity,q) }
";

#[test]
fn repeated_nested_contracts_share_one_execution_budget() {
    let root = SourceRoot::new(&format!(
        "{IMPORTS} {BUDGETED_FUNCTIONS}
        observe fn main() -> Bit {{
            measure_z(h(power(outer,30)(h(init0()))))
        }}"
    ));
    let program = compile_project(&root.0).unwrap();
    let attached = evidence(&program.program().operations);
    assert_eq!(attached.len(), 30);
    assert!(attached.iter().all(|item| Arc::ptr_eq(item, attached[0])));
    assert_eq!(attached[0].depth(), 2);
    // Every individual call fits easily; the complete repeated computation
    // exceeds this budget. Reusing a proof must not reset execution accounting.
    let limited = SimulationLimits {
        max_execution_steps: 100,
        ..SimulationLimits::default()
    };
    assert_eq!(
        run_closed(&program, limited),
        Err(SimulationError::ExecutionLimit { max: 100 })
    );
    let enough = SimulationLimits {
        max_execution_steps: 5000,
        ..SimulationLimits::default()
    };
    probability(&run_closed(&program, enough).unwrap(), &[false], 1.0);
}

#[test]
fn classical_branches_and_ensemble_components_share_execution_budget() {
    let root = SourceRoot::new(&format!(
        "{IMPORTS} {BUDGETED_FUNCTIONS}
        observe fn main() -> (Bit,Bit) {{
            let coin=measure_z(h(init0()));
            let q=if coin {{ power(outer,8)(init0()) }}
                  else {{ power(outer,8)(init0()) }};
            (coin,measure_z(q))
        }}"
    ));
    let program = compile_project(&root.0).unwrap();
    // Each selected branch individually fits, while the two nonzero ensemble
    // components together exceed the run-wide capacity.
    let limited = SimulationLimits {
        max_execution_steps: 100,
        ..SimulationLimits::default()
    };
    assert_eq!(
        run_closed(&program, limited),
        Err(SimulationError::ExecutionLimit { max: 100 })
    );
    let enough = SimulationLimits {
        max_execution_steps: 5000,
        ..SimulationLimits::default()
    };
    let result = run_closed(&program, enough).unwrap();
    probability(&result, &[false, false], 0.5);
    probability(&result, &[true, false], 0.5);
}

#[test]
fn adjoint_control_and_repetition_keep_evidence_and_relative_phase() {
    let root = SourceRoot::new(&format!(
        "{IMPORTS}
        unitary fn implementation(q: Q<Bit>) -> Q<Bit> {{ with_computed(q,predicate) {{ |a| t(a) }} }}
        unitary fn specified(q: Q<Bit>) -> Q<Bit> {{ t(q) }}
        unitary fn phase(q: Q<Bit>) -> Q<Bit> {{ apply_contract(implementation,specified,q) }}
        observe fn main() -> (Bit,Bit) {{
            let q=power(phase,2)(h(init0()));
            let q=adjoint(phase)(adjoint(phase)(q));
            let (c,tgt)=qif(h(init0()),x(init0())) {{ 0 => identity, 1 => phase }};
            discard(tgt);
            (measure_z(h(q)),measure_z(h(c)))
        }}"
    ));
    let program = compile_project(&root.0).unwrap();
    let attached = evidence(&program.program().operations);
    assert_eq!(attached.len(), 5);
    assert!(attached.iter().all(|value| Arc::ptr_eq(attached[0], value)));
    let actions: Vec<_> = program
        .program()
        .operations
        .iter()
        .filter_map(|op| match op {
            RawOp::ApplyUnitary { steps, .. } => Some(steps),
            _ => None,
        })
        .flatten()
        .collect();
    assert_eq!(
        actions
            .iter()
            .filter(|step| matches!(step.action, CircuitAction::Contract { adjoint: true, .. }))
            .count(),
        2
    );
    assert!(actions.iter().any(|step| !step.controls.is_empty()));
    let result = run_closed(&program, SimulationLimits::default()).unwrap();
    probability(&result, &[false, false], (1.0 + 1.0 / 2.0_f64.sqrt()) / 2.0);
    probability(&result, &[false, true], (1.0 - 1.0 / 2.0_f64.sqrt()) / 2.0);
}

#[test]
fn retained_contract_preserves_phase_with_an_entangled_reference() {
    let result = run(&format!(
        "{IMPORTS}
        unitary fn implementation(q: Q<Bit>) -> Q<Bit> {{ with_computed(q,predicate) {{ |a| z(a) }} }}
        observe fn main() -> (Bit,Bit) {{
            let (r,q)=cnot(h(init0()),init0());
            let q=apply_contract(implementation,specified_phase,q);
            let (r,q)=cnot(r,q);
            (measure_z(h(r)),measure_z(q))
        }}"
    ));
    probability(&result, &[true, false], 1.0);
}

#[test]
fn ordered_function_outputs_are_part_of_the_contract() {
    let definitions = format!(
        "{IMPORTS}
        unitary fn implementation(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {{
            let (a,b)=split(q); join(b,a)
        }}
        unitary fn specified(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {{
            basis q as (a,b) {{ (b,a) }}
        }}"
    );
    let result = run(&format!(
        "{definitions} observe fn main() -> (Bit,Bit) {{
            let q=apply_contract(implementation,specified,join(x(init0()),init0()));
            let (a,b)=split(q); (measure_z(a),measure_z(b))
        }}"
    ));
    probability(&result, &[false, true], 1.0);
    rejects(
        &format!(
            "{definitions}
        unitary fn wrong(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {{ q }}
        unitary fn client(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {{
            apply_contract(implementation,wrong,q)
        }}"
        ),
        ErrorCode::Contract,
    );
}

#[test]
fn dependency_source_changes_invalidate_the_previous_compilation() {
    let root = SourceRoot::new(&format!(
        "{IMPORTS} use implementation::phase;
        observe fn main() -> Bit {{ measure_z(h(apply_contract(phase,specified_phase,h(init0())))) }}"
    ));
    root.write(
        "implementation.qli",
        "use helper::step; pub unitary fn phase(q: Q<Bit>) -> Q<Bit> { step(q) }",
    );
    root.write(
        "helper.qli",
        "use std::quantum::z; pub unitary fn step(q: Q<Bit>) -> Q<Bit> { z(q) }",
    );
    let previous = compile_project(&root.0).unwrap();
    assert!(
        evidence(&previous.program().operations)[0]
            .identity()
            .sources
            .iter()
            .any(|(name, text)| name == "helper" && text.contains("z(q)"))
    );
    root.write(
        "helper.qli",
        "use std::quantum::x; pub unitary fn step(q: Q<Bit>) -> Q<Bit> { x(q) }",
    );
    assert_eq!(
        compile_project(&root.0).unwrap_err().code,
        ErrorCode::Contract
    );
    // Already checked immutable programs retain their original meaning.
    probability(
        &run_closed(&previous, SimulationLimits::default()).unwrap(),
        &[true],
        1.0,
    );
}

#[test]
fn exact_source_types_declared_effects_and_ordinary_targets_are_required() {
    for (declaration, code) in [
        (
            "observe fn implementation(q:Q<Bit>)->Q<Bit>{let b=measure_z(init0());z(q)}",
            ErrorCode::Effect,
        ),
        (
            "unitary fn implementation(q: Q<(Bit,Unit)>) -> Q<(Bit,Unit)> { q }",
            ErrorCode::TypeMismatch,
        ),
        (
            "unitary fn implementation(flag: Bit,q: Q<Bit>) -> Q<Bit> { z(q) }",
            ErrorCode::TypeMismatch,
        ),
    ] {
        rejects(&format!("{IMPORTS} {declaration}
            unitary fn client(q: Q<Bit>) -> Q<Bit> {{ apply_contract(implementation,specified_phase,q) }}"), code);
    }
    rejects(
        &format!(
            "{IMPORTS} unitary fn client(q: Q<Bit>) -> Q<Bit> {{ apply_contract(z,specified_phase,q) }}"
        ),
        ErrorCode::TypeMismatch,
    );
}

#[test]
fn names_remain_shadowed_after_input_evaluation_and_dependencies_are_acyclic() {
    for name in ["implementation", "specified_phase"] {
        rejects(&format!("{IMPORTS}
            unitary fn implementation(q: Q<Bit>) -> Q<Bit> {{ z(q) }}
            unitary fn client({name}: Q<Bit>) -> Q<Bit> {{ apply_contract(implementation,specified_phase,{name}) }}"), ErrorCode::TypeMismatch);
    }
    rejects(
        &format!(
            "{IMPORTS} unitary fn client(q: Q<Bit>) -> Q<Bit> {{ apply_contract(client,specified_phase,q) }}"
        ),
        ErrorCode::RecursiveCall,
    );
}

#[test]
fn input_ownership_is_consumed_once_and_quantum_frames_remain_owned() {
    rejects(
        &format!(
            "{IMPORTS} unitary fn client(q: Q<Bit>) -> (Q<Bit>,Q<Bit>) {{
        (apply_contract(specified_phase,specified_phase,q),q)
    }}"
        ),
        ErrorCode::Ownership,
    );
    let result = run(&format!(
        "{IMPORTS}
        observe fn main() -> (Bit,Bit) {{
            let frame=x(init0());
            let q=apply_contract(specified_phase,specified_phase,h(init0()));
            (measure_z(frame),measure_z(h(q)))
        }}"
    ));
    probability(&result, &[true, true], 1.0);
}

#[test]
fn zero_width_contract_phase_survives_coherent_control() {
    let result = run(&format!(
        "{IMPORTS}
        classical fn yes(value: Unit) -> Bit {{ 1 }}
        unitary fn implementation(q: Q<Unit>) -> Q<Unit> {{ with_computed(q,yes) {{ |a| z(a) }} }}
        unitary fn specified(q: Q<Unit>) -> Q<Unit> {{ with_computed(q,yes) {{ |a| t(t(t(t(a)))) }} }}
        unitary fn unit_identity(q: Q<Unit>) -> Q<Unit> {{ q }}
        unitary fn phase(q: Q<Unit>) -> Q<Unit> {{ apply_contract(implementation,specified,q) }}
        observe fn main() -> Bit {{
            let pair=basis init0() as value {{ ((),value) }};
            let (unit,q)=split(pair);
            let (control,unit)=qif(h(init0()),unit) {{ 0 => unit_identity, 1 => phase }};
            discard(unit); discard(q); measure_z(h(control))
        }}"
    ));
    probability(&result, &[true], 1.0);
}

#[test]
fn apply_contract_is_reserved_and_has_exact_static_name_syntax() {
    for source in [
        "unitary fn apply_contract(q: Q<Bit>) -> Q<Bit> { q }",
        "unitary fn f(q: Q<Bit>) -> Q<Bit> { apply_contract(f,f,q,) }",
        "unitary fn f(q: Q<Bit>) -> Q<Bit> { apply_contract(f(q),f,q) }",
        "unitary fn f(q: Q<Bit>) -> Q<Bit> { apply_contract(f,q) }",
    ] {
        assert!(parse_module(source).is_err(), "{source}");
    }
    let nested = format!(
        "unitary fn f(q: Q<Bit>) -> Q<Bit> {{ {}q{} }}",
        "apply_contract(f,f,".repeat(512),
        ")".repeat(512)
    );
    std::thread::spawn(move || {
        assert!(parse_module(&nested).unwrap_err().message.contains("limit"));
    })
    .join()
    .unwrap();
}
