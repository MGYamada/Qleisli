//! Original checked Raw provenance survives hierarchy overrides and dormant roots.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::contract::{DEFAULT_EXACT_WORK, exact::Budget, meaning::FiniteMeaning};
use crate::interchange::native;

/// Use an original binder site, retaining the selected complete constructor tree.
fn finite_override(operation: &str, exponent: u8) -> HierarchyProposal {
    finite_override_entry(&format!("invoke[{operation}](q)"), exponent)
}

/// Keep the checked binder's entry context explicit for source-mutation fixtures.
fn finite_override_entry(entry: &str, exponent: u8) -> HierarchyProposal {
    let source = elaborate(&format!(
        "fn invoke[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){{U(q)}}pub unitary fn entry(q:Q<Bit>)->Q<Bit>{{{entry}}}"
    ));
    let caller = source
        .definitions()
        .iter()
        .position(|d| d.path() == "main::invoke")
        .unwrap();
    let raw = source.lower_raw_operation_at(caller, "U").unwrap();
    let required = FiniteMeaning::phase(BasisType::Bit, vec![exponent, exponent]).unwrap();
    let kernel =
        native::Kernel::new(std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"));
    let checked = raw
        .check_finite_meaning(&kernel, &required, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    let proposal = checked.lower_hierarchy().unwrap();
    assert!(!proposal.native_sources.is_empty());
    assert!(
        proposal
            .native_sources
            .iter()
            .any(|trace| { std::ptr::eq(trace.witness.meaning(), checked.leaf().meaning()) }),
        "source retention shares the existing exact matrix without a JSON copy"
    );
    assert!(
        proposal
            .native_sources
            .iter()
            .any(|trace| trace.witness.payload() == checked.leaf().payload())
    );
    proposal
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn checked_finite_overrides_keep_actual_bytes_and_each_original_zero_interval() {
    let kernel = hierarchical::Kernel::new(
        std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
    );
    for (operation, exponent) in [
        ("scalar", 1),
        ("then_op(scalar,scalar)", 2),
        ("adjoint(scalar)", 7),
        ("power(scalar,0)", 0),
    ] {
        let proposal = finite_override(operation, exponent);
        validate(&proposal).unwrap();
        kernel
            .check_against_native(proposal.payload(), proposal.comparison_request())
            .unwrap();
        assert_eq!(proposal.zero_basis.len(), 2);
        let mut missing = proposal.clone();
        missing.native_sources.clear();
        assert!(validate(&missing).is_err());
        let mut missing = proposal.clone();
        missing.zero_basis.clear();
        assert!(validate(&missing).is_err());
        let mut duplicated = proposal.clone();
        duplicated
            .native_sources
            .push(duplicated.native_sources[0].clone());
        assert!(validate(&duplicated).is_err());
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn a_zero_repeat_override_cannot_erase_its_original_dormant_source_child() {
    // The distinct repeat-one call keeps the original closed child reachable.
    // Seven direct eighth-turns cancel that call without sharing its wrapper.
    let valid = finite_override_entry(
        "let q=power(scalar,1)(q);let q=invoke[power(scalar,0)](q);
         let q=global_phase_eighth(q);let q=global_phase_eighth(q);
         let q=global_phase_eighth(q);let q=global_phase_eighth(q);
         let q=global_phase_eighth(q);let q=global_phase_eighth(q);
         global_phase_eighth(q)",
        0,
    );
    let trace = valid
        .native_sources
        .iter()
        .find(|trace| trace.witness.operation().repeat_count() == Some(0))
        .unwrap()
        .clone();
    let mut wrong = valid.clone();
    change_graph(&mut wrong, |graph| {
        let body = p::field(table_entry(graph, "definitions", trace.original), "body").unwrap();
        assert_eq!(p::tag(body).unwrap(), "repeat");
        let child = p::number(p::field(body, "definition").unwrap()).unwrap();
        let body = p::field(table_entry(graph, "definitions", child), "body").unwrap();
        let identity = p::indices(p::field(body, "children").unwrap()).unwrap()[0];
        for (table, field) in [("definitions", "definition"), ("meanings", "child")] {
            let body = object_mut(table_entry(graph, table, trace.original))
                .get_mut("body")
                .unwrap();
            object_mut(body).insert(field.into(), Value::Number(identity as u64));
        }
        object_mut(table_entry(graph, "proofs", trace.original)).insert(
            "premises".into(),
            Value::Array(vec![Value::Number(identity as u64)]),
        );
    });
    let kernel = hierarchical::Kernel::new(
        std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
    );
    // Native validity of this complete graph cannot discharge the original
    // child of this particular zero repeat, even though the full phase is kept.
    kernel.inspect(wrong.payload()).unwrap();
    assert!(validate(&wrong).is_err());
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn checked_source_witness_cannot_move_to_a_fresh_equal_shaped_source_collection() {
    let valid = finite_override("scalar", 1);
    let mut changed = valid.clone();
    let other = finite_override("scalar", 1);
    assert_eq!(
        valid.native_sources[0].witness.key(),
        other.native_sources[0].witness.key()
    );
    changed.source = other.source;
    assert!(
        validate(&changed)
            .unwrap_err()
            .message()
            .contains("another original source operation")
    );
    let witness = &valid.native_sources[0].witness;
    assert!(
        witness
            .validate(
                &valid.source,
                witness.operation(),
                witness.payload(),
                &crate::interchange::finite_matrix::encode(witness.meaning()).unwrap(),
                &mut Budget::new(0)
            )
            .is_err()
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn reference_meaning_override_retains_both_original_raw_and_actual_receipt_wrapper() {
    let source = elaborate(
        "unitary fn reference_scalar(q:Q<Bit>)->Q<Bit>{global_phase_eighth(q)}meaning M:Bit=reference(reference_scalar);fn invoke[const U:Op<Bit,M>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}pub unitary fn entry(q:Q<Bit>)->Q<Bit>{invoke[scalar](q)}",
    );
    let executable = std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker");
    let kernel = native::Kernel::new(executable.clone());
    let mut budget = Budget::new(DEFAULT_EXACT_WORK);
    let source = source
        .check_function_contracts(&kernel, &mut budget)
        .unwrap();
    let checked = source
        .check_operation_meanings(&kernel, &mut budget)
        .unwrap();
    let proposal = checked.lower_hierarchy().unwrap();
    validate(&proposal).unwrap();
    assert!(!proposal.native_sources.is_empty());
    assert_eq!(proposal.zero_basis.len(), 2);
    let native = hierarchical::Kernel::new(executable);
    native
        .check_against_native(proposal.payload(), proposal.comparison_request())
        .unwrap();
    let mut wrong = proposal.clone();
    let actual = wrong.native_sources[0].actual;
    change_graph(&mut wrong, |graph| {
        let body = p::field(table_entry(graph, "definitions", actual), "body").unwrap();
        let leaf = p::indices(p::field(body, "children").unwrap()).unwrap()[0];
        let body = object_mut(table_entry(graph, "definitions", leaf))
            .get_mut("body")
            .unwrap();
        object_mut(body).insert("program".into(), Value::String("{}".into()));
    });
    assert!(validate(&wrong).is_err());
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn ordinary_meaning_bindings_without_basis_tables_do_not_retain_new_witnesses() {
    let source = elaborate(
        "classical fn phases(b:Bit)->(Bit,(Bit,Bit)){(1,(0,0))}meaning M:Bit=phase_by(phases);unitary fn plain(q:Q<Bit>)->Q<Bit>{global_phase_eighth(q)}fn invoke[const U:Op<Bit,M>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}pub unitary fn entry(q:Q<Bit>)->Q<Bit>{invoke[plain](q)}",
    );
    let kernel =
        native::Kernel::new(std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"));
    let checked = source
        .check_operation_meanings(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    assert!(checked.source_witnesses.is_empty());
    let proposal = checked.lower_hierarchy().unwrap();
    assert!(proposal.native_sources.is_empty());
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn reference_override_compares_complete_nested_receipt_snapshots_after_native_decode() {
    let source = elaborate(
        "unitary fn actual_phase(q:Q<Bit>)->Q<Bit>{global_phase_eighth(q)}unitary fn specified_phase(q:Q<Bit>)->Q<Bit>{global_phase_eighth(q)}unitary fn nested(q:Q<Bit>)->Q<Bit>{let e=empty();consume_empty(e);apply_contract(actual_phase,specified_phase,q)}meaning M:Bit=reference(specified_phase);fn invoke[const U:Op<Bit,M>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}pub unitary fn entry(q:Q<Bit>)->Q<Bit>{invoke[nested](q)}",
    );
    let executable = std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker");
    let kernel = native::Kernel::new(executable.clone());
    let mut budget = Budget::new(DEFAULT_EXACT_WORK);
    let source = source
        .check_function_contracts(&kernel, &mut budget)
        .unwrap();
    let checked = source
        .check_operation_meanings(&kernel, &mut budget)
        .unwrap();
    let proposal = checked.lower_hierarchy().unwrap();
    validate(&proposal).unwrap();
    assert!(!proposal.native_sources.is_empty());
    hierarchical::Kernel::new(executable)
        .check_against_native(proposal.payload(), proposal.comparison_request())
        .unwrap();
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn retained_witness_ceiling_rejects_before_extending_the_existing_aggregate() {
    let source = elaborate(
        "fn invoke[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}pub unitary fn entry(q:Q<Bit>)->Q<Bit>{invoke[scalar](q)}",
    );
    let caller = source
        .definitions()
        .iter()
        .position(|d| d.path() == "main::invoke")
        .unwrap();
    let raw = source.lower_raw_operation_at(caller, "U").unwrap();
    let required = FiniteMeaning::phase(BasisType::Bit, vec![1, 1]).unwrap();
    let kernel =
        native::Kernel::new(std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"));
    let checked = raw
        .check_finite_meaning(&kernel, &required, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    let mut cells = 100_000;
    let mut budget = Budget::new(DEFAULT_EXACT_WORK);
    let result = checked.source_witness(&mut budget, &mut cells);
    let error = match result {
        Err(error) => error,
        Ok(_) => panic!("exhausted retained source capacity must reject"),
    };
    assert_eq!(error.code(), "limit");
    assert_eq!(cells, 100_000);
    assert_eq!(budget.remaining(), DEFAULT_EXACT_WORK);
}
