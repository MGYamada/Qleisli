//! Tiny original-source/actual-root controls for the zero-basis adapter.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::compile::ParsedProgram;
use crate::interchange::hierarchical;

fn elaborate(source: &str) -> ElaboratedProgram {
    ParsedProgram::parse(
        crate::edition::Edition::E2026,
        BTreeMap::from([("main".into(), source.into())]),
    )
    .unwrap()
    .instantiate("main::entry", BTreeMap::new(), BTreeMap::new())
    .unwrap()
    .elaborate()
    .unwrap()
}
fn lower(source: &str) -> HierarchyProposal {
    elaborate(source).lower().unwrap()
}
fn kernel() -> hierarchical::Kernel {
    hierarchical::Kernel::new(
        std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
        crate::edition::Edition::E2026,
    )
}
fn map(value: &mut Value) -> &mut BTreeMap<String, Value> {
    let Value::Object(fields) = value else {
        panic!("object");
    };
    fields
}
fn change_graph(proposal: &mut HierarchyProposal, change: impl FnOnce(&mut Value)) {
    let mut graph = json::parse(&proposal.graph).unwrap();
    change(&mut graph);
    proposal.graph = json::encode(&graph).unwrap();
    if proposal.instrument {
        let mut payload = json::parse(&proposal.payload).unwrap();
        map(&mut payload).insert("circuit".into(), graph);
        proposal.payload = json::encode(&payload).unwrap();
    } else {
        proposal.payload = proposal.graph.clone();
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn zero_basis_maps_preserve_distinct_empty_atoms_and_native_owner_obligations() {
    for input in ["Unit", "Bits<0>"] {
        for output in ["Unit", "Bits<0>"] {
            let label = if output == "Unit" {
                "()"
            } else {
                "empty_bits()"
            };
            let source = format!(
                "pub unitary fn entry(q:Q<{input}>)->Q<{output}>{{basis q as label {{{label}}}}}"
            );
            let proposal = lower(&source);
            validate(&proposal).unwrap();
            assert!(!proposal.instrument);
            assert_eq!(proposal.zero_basis.len(), 1);
            let interval = &proposal.zero_basis[0];
            assert_eq!(
                interval.input.basis.kind(),
                if input == "Unit" { "unit" } else { "bits" }
            );
            assert_eq!(
                interval.output.basis.kind(),
                if output == "Unit" { "unit" } else { "bits" }
            );
            assert_ne!(interval.input.owner, interval.output.owner);
            assert!(interval.input.axes.is_empty() && interval.output.axes.is_empty());
            kernel()
                .check_against_native(proposal.payload(), proposal.comparison_request())
                .unwrap();
        }
    }
}

#[test]
fn zero_basis_preparation_replay_rejects_table_and_fresh_axis_substitution() {
    let valid = lower("pub isometry fn entry(q:Q<Unit>)->Q<Bit>{basis q as label {0}}");
    validate(&valid).unwrap();
    p::validate(&valid).unwrap();
    let mut wrong = valid.clone();
    wrong.source = elaborate("pub isometry fn entry(q:Q<Unit>)->Q<Bit>{basis q as label {1}}");
    assert!(
        validate(&wrong)
            .unwrap_err()
            .message()
            .contains("original table/types/effect")
    );
    let mut wrong = valid.clone();
    wrong.zero_basis[0].prepared.as_mut().unwrap().axes[0] = 1;
    assert!(validate(&wrong).is_err());
    let mut wrong = valid.clone();
    wrong
        .events
        .iter_mut()
        .find(|event| event.preparation.is_some())
        .unwrap()
        .preparation = None;
    assert!(
        p::validate(&wrong)
            .unwrap_err()
            .message()
            .contains("original zero-basis interval")
    );
}

#[test]
fn retained_zero_interval_cannot_replace_the_actual_pure_entry_or_ordered_root() {
    let valid =
        lower("pub unitary fn entry(q:Q<Unit>)->Q<Bits<0>>{basis q as label {empty_bits()}}");
    let mut wrong = valid.clone();
    let interval = wrong.zero_basis[0].node;
    change_graph(&mut wrong, |graph| {
        map(map(graph).get_mut("entry").unwrap())
            .insert("implementation".into(), Value::Number(interval as u64));
    });
    assert!(
        validate(&wrong)
            .unwrap_err()
            .message()
            .contains("original source-bound root")
    );
    let mut wrong = valid.clone();
    let root = wrong.pure_traces[0].root;
    change_graph(&mut wrong, |graph| {
        let Value::Array(definitions) = map(graph).get_mut("definitions").unwrap() else {
            panic!("definitions")
        };
        let body = map(&mut definitions[root]).get_mut("body").unwrap();
        map(body).insert(
            "children".into(),
            Value::Array(vec![
                Value::Number(interval as u64),
                Value::Number(interval as u64),
            ]),
        );
    });
    assert!(
        validate(&wrong)
            .unwrap_err()
            .message()
            .contains("extra operation")
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn a_native_valid_extra_scalar_cannot_use_an_unchanged_zero_interval_as_source_evidence() {
    let valid =
        lower("pub unitary fn entry(q:Q<Unit>)->Q<Bits<0>>{basis q as label {empty_bits()}}");
    let mut changed = lower(
        "pub unitary fn entry(q:Q<Unit>)->Q<Bits<0>>{let z=basis q as label {empty_bits()};global_phase_eighth(z)}",
    );
    kernel()
        .check_against_native(changed.payload(), changed.comparison_request())
        .unwrap();
    assert_eq!(changed.zero_basis[0].input, valid.zero_basis[0].input);
    assert_eq!(changed.zero_basis[0].output, valid.zero_basis[0].output);
    // The correct +1 interval remains reachable in a valid phased candidate;
    // it cannot justify the original source's different complete root.
    changed.source = valid.source.clone();
    assert!(
        validate(&changed)
            .unwrap_err()
            .message()
            .contains("step count")
    );
}

#[test]
fn pure_atomic_helpers_bind_their_original_child_root_and_complete_caller_frame() {
    let valid = lower(
        "unitary fn helper(q:Q<Unit>)->Q<Bits<0>>{let z=basis q as label {empty_bits()};global_phase_eighth(z)}pub isometry fn entry(r:Q<Bit>,q:Q<Unit>)->(Q<Bit>,Q<Bits<0>>){(r,helper(q))}",
    );
    validate(&valid).unwrap();
    p::validate(&valid).unwrap();
    assert_eq!(valid.pure_traces.len(), 1);
    let mut wrong = valid.clone();
    let call = wrong
        .events
        .iter()
        .find(|event| event.node.is_some())
        .unwrap()
        .node
        .unwrap();
    let child = wrong.pure_traces[0].root;
    let interval = wrong.zero_basis[0].node;
    assert_ne!(child, interval);
    change_graph(&mut wrong, |graph| {
        let Value::Array(definitions) = map(graph).get_mut("definitions").unwrap() else {
            panic!("definitions")
        };
        let body = map(&mut definitions[call]).get_mut("body").unwrap();
        let Value::Array(children) = map(body).get_mut("children").unwrap() else {
            panic!("children")
        };
        children[1] = Value::Number(interval as u64);
    });
    assert!(
        p::validate(&wrong)
            .unwrap_err()
            .message()
            .contains("different child root")
    );
}

#[test]
fn zero_basis_composition_retains_intervals_and_nonzero_tables_keep_profile_refusal() {
    let source = elaborate(
        "unitary fn zero(q:Q<Unit>)->Q<Unit>{basis q as label {()}} fn invoke[const U:Op<Unit>](q:Q<Unit>)->Q<Unit> requires Applicable(U){U(q)} pub unitary fn entry(q:Q<Unit>)->Q<Unit>{invoke[then_op(zero,zero)](q)}",
    );
    let proposal = source.lower().unwrap();
    validate(&proposal).unwrap();
    assert_eq!(proposal.zero_basis.len(), 1);
    let source = elaborate("pub unitary fn entry(q:Q<Bit>)->Q<Bit>{basis q as label {not label}}");
    assert!(
        source
            .lower()
            .unwrap_err()
            .message()
            .contains("does not support coherent basis tables")
    );
}

#[test]
fn aggregate_pure_trace_exhaustion_precedes_another_event_copy() {
    let proposal =
        lower("pub unitary fn entry(q:Q<Unit>)->Q<Bits<0>>{basis q as label {empty_bits()}}");
    let trace = &proposal.pure_traces[0];
    let event = &trace.events[0];
    let step = &proposal.source.definitions()[event.definition].steps()[event.step];
    let state = Instrument {
        inputs: trace.inputs.clone(),
        fresh: vec![],
        initializations: vec![],
        pure_steps: vec![],
        measured: vec![],
        next_axis: 0,
        next_classical: 1_000_000,
        current: trace.inputs.clone(),
        events: vec![],
        call_path: vec![],
        trace_cells: 0,
    };
    let mut used = 100_000;
    let error = p::reserve_pure_trace(
        &state,
        &event.inputs,
        &quantum(&event.outputs),
        &mut used,
        step,
    )
    .unwrap_err();
    assert_eq!(error.code(), "limit");
    assert_eq!(used, 100_000);
    assert_eq!(state.current, trace.inputs);
    assert!(state.events.is_empty());
}

#[test]
fn original_source_obligations_survive_omitted_interval_and_pure_trace_tables() {
    let pure =
        lower("pub unitary fn entry(q:Q<Unit>)->Q<Bits<0>>{basis q as label {empty_bits()}}");
    for (intervals, traces) in [(true, false), (false, true), (true, true)] {
        let mut wrong = pure.clone();
        if intervals {
            wrong.zero_basis.clear();
        }
        if traces {
            wrong.pure_traces.clear();
        }
        assert!(
            validate(&wrong).is_err(),
            "original source still requires both interval/root replay tables"
        );
    }
    let mut preparation = lower("pub isometry fn entry(q:Q<Unit>)->Q<Bit>{basis q as label {0}}");
    preparation.zero_basis.clear();
    preparation.pure_traces.clear();
    assert!(
        validate(&preparation).is_err(),
        "original preparation event requires its interval"
    );
    let mut helper = lower(
        "unitary fn helper(q:Q<Unit>)->Q<Bits<0>>{let z=basis q as label {empty_bits()};global_phase_eighth(z)}pub isometry fn entry(r:Q<Bit>,q:Q<Unit>)->(Q<Bit>,Q<Bits<0>>){(r,helper(q))}",
    );
    helper.zero_basis.clear();
    helper.pure_traces.clear();
    assert!(
        validate(&helper)
            .unwrap_err()
            .message()
            .contains("original child root")
    );
    let mut no_table = lower("pub unitary fn entry(q:Q<Unit>)->Q<Unit>{q}");
    no_table.zero_basis = pure.zero_basis;
    assert!(
        validate(&no_table).is_err(),
        "extra producer metadata does not invent an original source obligation"
    );
}
