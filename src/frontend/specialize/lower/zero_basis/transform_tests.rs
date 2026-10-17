//! Original-source bindings for the zero-basis hierarchy transport adapter.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::compile::ParsedProgram;
use crate::interchange::hierarchical;

const HELPERS: &str = r#"


unitary fn empty()->Q<Bits<0>>{basis unit(()) as () {empty_bits()}}
unitary fn consume_empty(q:Q<Bits<0>>)->Unit{finish(basis q as label {()})}
unitary fn scalar(q:Q<Bit>)->Q<Bit>{
    let e=empty();let phased=global_phase_eighth(e);consume_empty(phased);q
}
"#;

/// Elaborate the exact retained ordinary source using the production frontend.
fn elaborate(entry: &str) -> ElaboratedProgram {
    ParsedProgram::parse(BTreeMap::from([(
        "main".into(),
        format!("{HELPERS}{entry}"),
    )]))
    .unwrap()
    .instantiate("main::entry", BTreeMap::new(), BTreeMap::new())
    .unwrap()
    .elaborate()
    .unwrap()
}

/// Select the same hierarchy producer that the source transport validator sees.
fn lower(entry: &str) -> HierarchyProposal {
    elaborate(entry).lower().unwrap()
}

/// Obtain a mutable test JSON object without formatting source-bearing values.
fn object_mut(value: &mut Value) -> &mut BTreeMap<String, Value> {
    let Value::Object(fields) = value else {
        panic!("expected JSON object")
    };
    fields
}

/// Obtain a mutable table entry in the proposal's actual hierarchy graph.
fn table_entry<'a>(graph: &'a mut Value, table: &str, index: usize) -> &'a mut Value {
    let Value::Array(entries) = object_mut(graph).get_mut(table).unwrap() else {
        panic!("expected JSON table")
    };
    &mut entries[index]
}

/// Keep the payload and graph identical so a mutation cannot fail only that binding.
fn change_graph(proposal: &mut HierarchyProposal, change: impl FnOnce(&mut Value)) {
    assert!(!proposal.instrument);
    let mut graph = json::parse(&proposal.graph).unwrap();
    change(&mut graph);
    proposal.graph = json::encode(&graph).unwrap();
    proposal.payload = proposal.graph.clone();
}

/// Find an actual constructor in the original graph without inventing an index.
fn node_with_tag(proposal: &HierarchyProposal, tag: &str) -> usize {
    let graph = json::parse(&proposal.graph).unwrap();
    p::array(p::field(&graph, "definitions").unwrap())
        .unwrap()
        .iter()
        .position(|node| p::tag(p::field(node, "body").unwrap()).unwrap() == tag)
        .expect("the requested constructor is present")
}

/// Locate the original event carrying this source operation's full interface.
fn operation_event(proposal: &HierarchyProposal) -> SourceEvent {
    proposal
        .pure_traces
        .iter()
        .flat_map(|trace| &trace.events)
        .find(|event| {
            proposal.source.definitions()[event.definition].steps()[event.step]
                .operation()
                .is_some()
        })
        .expect("retained source operation event")
        .clone()
}

/// Exercise just the new correspondence hook, keeping original source identity.
fn check_event(proposal: &HierarchyProposal, event: &SourceEvent) -> Result<()> {
    let graph = json::parse(&proposal.graph).unwrap();
    let defs = p::array(p::field(&graph, "definitions").unwrap()).unwrap();
    let step = &proposal.source.definitions()[event.definition].steps()[event.step];
    validate_operation_event(proposal, event, step, defs, true)
}

#[test]
fn named_zero_basis_transforms_retain_all_original_empty_owner_intervals() {
    for entry in [
        "pub unitary fn entry(q:Q<Bit>)->Q<Bit>{power(scalar,0)(q)}",
        "pub unitary fn entry(q:Q<Bit>)->Q<Bit>{power(scalar,1)(q)}",
        "pub unitary fn entry(q:Q<Bit>)->Q<Bit>{power(scalar,2)(q)}",
        "pub unitary fn entry(q:Q<Bit>)->Q<Bit>{adjoint(scalar)(q)}",
        "pub unitary fn entry(c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){controlled(scalar)(c,q)}",
        "pub unitary fn entry(r:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){(r,power(scalar,2)(q))}",
        "pub unitary fn entry(r:Q<Unit>,q:Q<Bit>)->(Q<Unit>,Q<Bit>){(r,power(scalar,2)(q))}",
    ] {
        let proposal = lower(entry);
        validate(&proposal).unwrap();
        assert_eq!(proposal.zero_basis.len(), 2);
        assert!(proposal.zero_basis.iter().all(|interval| {
            interval.input.axes.is_empty()
                && interval.output.axes.is_empty()
                && interval.input.owner != interval.output.owner
                && interval.input.basis != interval.output.basis
        }));
        check_event(&proposal, &operation_event(&proposal)).unwrap();
    }
}

#[test]
fn zero_repetitions_bind_the_original_child_and_literal_count() {
    let valid = lower("pub unitary fn entry(q:Q<Bit>)->Q<Bit>{power(scalar,0)(q)}");
    let repeat = node_with_tag(&valid, "repeat");
    let event = operation_event(&valid);
    let mut wrong_count = valid.clone();
    change_graph(&mut wrong_count, |graph| {
        let body = object_mut(table_entry(graph, "definitions", repeat))
            .get_mut("body")
            .unwrap();
        object_mut(body).insert("count".into(), Value::Number(1));
    });
    assert!(
        check_event(&wrong_count, &event)
            .unwrap_err()
            .message()
            .contains("original count")
    );
    let mut wrong_child = valid.clone();
    change_graph(&mut wrong_child, |graph| {
        let body = object_mut(table_entry(graph, "definitions", repeat))
            .get_mut("body")
            .unwrap();
        // An earlier identity has the same exact input/output interface here.
        let original = p::number(p::field(body, "definition").unwrap()).unwrap();
        let closed = p::field(table_entry(graph, "definitions", original), "body").unwrap();
        let identity = p::indices(p::field(closed, "children").unwrap()).unwrap()[0];
        let body = object_mut(table_entry(graph, "definitions", repeat))
            .get_mut("body")
            .unwrap();
        object_mut(body).insert("definition".into(), Value::Number(identity as u64));
    });
    assert!(check_event(&wrong_child, &event).is_err());
    let mut omitted = valid.clone();
    omitted.zero_basis.clear();
    assert!(validate(&omitted).is_err());
    let mut duplicate = valid.clone();
    duplicate.pure_traces.push(duplicate.pure_traces[0].clone());
    assert!(
        validate(&duplicate)
            .unwrap_err()
            .message()
            .contains("duplicate source roots")
    );
}

#[test]
fn inverse_and_control_bind_the_original_direction_and_polarity() {
    let valid = lower("pub unitary fn entry(q:Q<Bit>)->Q<Bit>{adjoint(scalar)(q)}");
    let inverse = node_with_tag(&valid, "inverse");
    let event = operation_event(&valid);
    let mut wrong = valid.clone();
    change_graph(&mut wrong, |graph| {
        let body = object_mut(table_entry(graph, "definitions", inverse))
            .get_mut("body")
            .unwrap();
        object_mut(body).insert("tag".into(), Value::String("repeat".into()));
        object_mut(body).insert("count".into(), Value::Number(1));
    });
    assert!(
        check_event(&wrong, &event)
            .unwrap_err()
            .message()
            .contains("original inverse")
    );
    let valid =
        lower("pub unitary fn entry(c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){controlled(scalar)(c,q)}");
    let control = node_with_tag(&valid, "control");
    let event = operation_event(&valid);
    let mut wrong = valid.clone();
    change_graph(&mut wrong, |graph| {
        let body = object_mut(table_entry(graph, "definitions", control))
            .get_mut("body")
            .unwrap();
        object_mut(body).insert("polarity".into(), Value::Bool(false));
    });
    assert!(
        check_event(&wrong, &event)
            .unwrap_err()
            .message()
            .contains("original polarity")
    );
}

#[test]
fn operation_return_axes_cannot_relabel_an_untouched_reference() {
    let valid =
        lower("pub unitary fn entry(r:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){(r,power(scalar,2)(q))}");
    let mut event = operation_event(&valid);
    let Item::Quantum(returned) = &mut event.outputs[0] else {
        panic!("quantum result")
    };
    assert_eq!(returned.axes, vec![1]);
    returned.axes = vec![0];
    let outputs = quantum(&event.outputs);
    let mut wrong = valid.clone();
    change_graph(&mut wrong, |graph| {
        let id = event.node.unwrap();
        let body = p::field(table_entry(graph, "definitions", id), "body").unwrap();
        let last = *p::indices(p::field(body, "children").unwrap())
            .unwrap()
            .last()
            .unwrap();
        for node in [id, last] {
            let header = object_mut(table_entry(graph, "definitions", node))
                .get_mut("interface")
                .unwrap();
            object_mut(header).insert(
                "outputs".into(),
                json::parse(side(&outputs, &[]).as_bytes()).unwrap(),
            );
        }
    });
    assert!(
        check_event(&wrong, &event)
            .unwrap_err()
            .message()
            .contains("source output axis mapping")
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn native_valid_count_mutation_cannot_replace_the_original_repeat_source() {
    let valid = lower("pub unitary fn entry(q:Q<Bit>)->Q<Bit>{power(scalar,2)(q)}");
    let kernel = hierarchical::Kernel::new(
        std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
    );
    kernel
        .check_against_native(valid.payload(), valid.comparison_request())
        .unwrap();
    let repeat = node_with_tag(&valid, "repeat");
    let mut wrong = valid.clone();
    change_graph(&mut wrong, |graph| {
        // Keep implementation and equation consistent; the source still says 2.
        for table in ["definitions", "meanings"] {
            let body = object_mut(table_entry(graph, table, repeat))
                .get_mut("body")
                .unwrap();
            object_mut(body).insert("count".into(), Value::Number(3));
        }
    });
    kernel.inspect(wrong.payload()).unwrap();
    assert!(validate(&wrong).is_err());
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn native_comparison_checks_the_actual_named_transform_payloads() {
    let kernel = hierarchical::Kernel::new(
        std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
    );
    for entry in [
        "pub unitary fn entry(q:Q<Bit>)->Q<Bit>{power(scalar,0)(q)}",
        "pub unitary fn entry(q:Q<Bit>)->Q<Bit>{adjoint(scalar)(q)}",
        "pub unitary fn entry(c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){controlled(scalar)(c,q)}",
        "pub unitary fn entry(r:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){(r,power(scalar,2)(q))}",
        "pub unitary fn entry(r:Q<Unit>,q:Q<Bit>)->(Q<Unit>,Q<Bit>){(r,power(scalar,2)(q))}",
    ] {
        let proposal = lower(entry);
        validate(&proposal).unwrap();
        kernel
            .check_against_native(proposal.payload(), proposal.comparison_request())
            .unwrap();
    }
}

#[test]
fn preparation_operation_retains_its_explicit_hierarchy_refusal() {
    let source = elaborate(
        "isometry fn prepare(q:Q<Unit>)->Q<Bit>{basis q as label {0}}fn invoke[const U:Op<Unit -> Bit>](q:Q<Unit>)->Q<Bit> requires Applicable(U){U(q)}pub isometry fn entry(q:Q<Unit>)->Q<Bit>{invoke[prepare](q)}",
    );
    assert!(
        source
            .lower()
            .unwrap_err()
            .message()
            .contains("original structural unitary tables")
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn native_valid_identity_cannot_replace_the_original_zero_repeat_child_root() {
    let valid = lower("pub unitary fn entry(q:Q<Bit>)->Q<Bit>{power(scalar,0)(q)}");
    let repeat = node_with_tag(&valid, "repeat");
    let event = operation_event(&valid);
    let mut wrong = valid.clone();
    change_graph(&mut wrong, |graph| {
        let body = p::field(table_entry(graph, "definitions", repeat), "body").unwrap();
        let closed = p::number(p::field(body, "definition").unwrap()).unwrap();
        let body = p::field(table_entry(graph, "definitions", closed), "body").unwrap();
        let mut children = p::indices(p::field(body, "children").unwrap()).unwrap();
        let identity = children[0];
        let original = children[1];
        assert_eq!(
            p::endpoints(table_entry(graph, "definitions", identity)).unwrap(),
            p::endpoints(table_entry(graph, "definitions", original)).unwrap(),
        );
        children[1] = identity;
        let children = Value::Array(
            children
                .into_iter()
                .map(|i| Value::Number(i as u64))
                .collect(),
        );
        for table in ["definitions", "meanings"] {
            let body = object_mut(table_entry(graph, table, closed))
                .get_mut("body")
                .unwrap();
            object_mut(body).insert("children".into(), children.clone());
        }
        object_mut(table_entry(graph, "proofs", closed)).insert("premises".into(), children);
    });
    let kernel = hierarchical::Kernel::new(
        std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
    );
    kernel.inspect(wrong.payload()).unwrap();
    assert!(
        check_event(&wrong, &event)
            .unwrap_err()
            .message()
            .contains("another original root")
    );
    assert!(validate(&wrong).is_err());
}

#[test]
fn operation_rename_rejects_wrong_length_permutations_before_decoding_entries() {
    let valid = lower("pub unitary fn entry(q:Q<Bit>)->Q<Bit>{power(scalar,2)(q)}");
    let event = operation_event(&valid);
    for key in ["owners", "axes"] {
        let mut wrong = valid.clone();
        change_graph(&mut wrong, |graph| {
            let body = p::field(
                table_entry(graph, "definitions", event.node.unwrap()),
                "body",
            )
            .unwrap();
            let enter = p::indices(p::field(body, "children").unwrap()).unwrap()[0];
            let body = object_mut(table_entry(graph, "definitions", enter))
                .get_mut("body")
                .unwrap();
            let permutation = object_mut(body).get_mut("permutation").unwrap();
            // Invalid elements would report a number error if decoded first.
            object_mut(permutation).insert(key.into(), Value::Array(vec![Value::Bool(false); 2]));
        });
        assert!(
            check_event(&wrong, &event)
                .unwrap_err()
                .message()
                .contains("ordered source coordinates")
        );
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn native_valid_direction_and_polarity_changes_remain_different_source_actions() {
    let kernel = hierarchical::Kernel::new(
        std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
    );
    let valid = lower("pub unitary fn entry(q:Q<Bit>)->Q<Bit>{adjoint(scalar)(q)}");
    let inverse = node_with_tag(&valid, "inverse");
    let event = operation_event(&valid);
    let mut wrong = valid.clone();
    change_graph(&mut wrong, |graph| {
        for (table, tag) in [("definitions", "repeat"), ("meanings", "power")] {
            let body = object_mut(table_entry(graph, table, inverse))
                .get_mut("body")
                .unwrap();
            object_mut(body).insert("tag".into(), Value::String(tag.into()));
            object_mut(body).insert("count".into(), Value::Number(1));
        }
        let rule = object_mut(table_entry(graph, "proofs", inverse))
            .get_mut("rule")
            .unwrap();
        object_mut(rule).insert("tag".into(), Value::String("repeat".into()));
    });
    kernel.inspect(wrong.payload()).unwrap();
    assert!(
        check_event(&wrong, &event)
            .unwrap_err()
            .message()
            .contains("original inverse")
    );
    let valid =
        lower("pub unitary fn entry(c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){controlled(scalar)(c,q)}");
    let control = node_with_tag(&valid, "control");
    let event = operation_event(&valid);
    let mut wrong = valid.clone();
    change_graph(&mut wrong, |graph| {
        for table in ["definitions", "meanings"] {
            let body = object_mut(table_entry(graph, table, control))
                .get_mut("body")
                .unwrap();
            object_mut(body).insert("polarity".into(), Value::Bool(false));
        }
    });
    kernel.inspect(wrong.payload()).unwrap();
    assert!(
        check_event(&wrong, &event)
            .unwrap_err()
            .message()
            .contains("original polarity")
    );
}

mod composite_tests;
mod native_source_tests;
