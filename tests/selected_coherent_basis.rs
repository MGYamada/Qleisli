//! Small selected-source regressions for complete coherent basis tables.
//! Native checks and replay remain separate from source-meaning proof claims.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use qleisli::frontend::compile::{ElaboratedProgram, ParsedProgram};
use std::collections::BTreeMap;

fn source(text: &str) -> ElaboratedProgram {
    ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())]))
        .unwrap()
        .instantiate("main::f", Default::default(), Default::default())
        .unwrap()
        .elaborate()
        .unwrap()
}

fn table(graph: &ElaboratedProgram) -> &[u16] {
    graph.definitions()[graph.root()]
        .steps()
        .iter()
        .find_map(|step| step.basis_table())
        .expect("one original coherent table")
}

#[test]
fn selected_coherent_unit_empty_bits_and_product_trees_remain_exact() {
    for (body, output) in [
        ("()", "Unit"),
        ("empty_bits()", "Bits<0>"),
        ("label()", "Bits<0>"),
    ] {
        let graph = source(&format!(
            "use std::classical::empty_bits;
            classical fn label()->Bits<0>{{empty_bits()}}
            pub unitary fn f(q:Q<Unit>)->Q<{output}>{{basis q as () {{{body}}}}}"
        ));
        assert_eq!(table(&graph), [0]);
        let definition = &graph.definitions()[graph.root()];
        let step = definition.steps().last().unwrap();
        assert_eq!(step.kind(), "lift_basis");
        assert_eq!(step.effect(), "unitary");
        assert_ne!(step.inputs()[0].identity(), step.output().identity());
        assert_eq!(
            step.output().ty().kind(),
            if output == "Unit" { "unit" } else { "bits" }
        );
        assert!(step.output().ty().is_quantum());
        graph.lower_raw().unwrap();
    }
    let graph = source(
        "pub unitary fn f(q:Q<(Unit,(Bit,Bit))>)->Q<((Bit,Unit),Bit)>{
        basis q as ((),(a,b)) {((b,()),a)}}",
    );
    assert_eq!(table(&graph), [0, 2, 1, 3]);
    let output = graph.definitions()[graph.root()]
        .output()
        .ty()
        .quantum_basis()
        .unwrap();
    assert_eq!(output.fields()[0].kind(), "tuple");
    assert_eq!(output.fields()[0].fields()[1].kind(), "unit");
    graph.lower_raw().unwrap();
}

#[test]
fn selected_coherent_calls_use_original_imports_and_full_classical_bodies() {
    let graph = ParsedProgram::parse(BTreeMap::from([
        (
            "labels".into(),
            "pub classical fn twist((a,b):(Bit,Bit))->(Bit,Bit){(a xor b,b)}".into(),
        ),
        (
            "main".into(),
            "use labels::twist;
            classical fn nested(p:(Bit,Bit))->(Bit,Bit){twist(twist(p))}
            pub unitary fn f(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{basis q as p {nested(p)}}"
                .into(),
        ),
    ]))
    .unwrap()
    .instantiate("main::f", Default::default(), Default::default())
    .unwrap()
    .elaborate()
    .unwrap();
    assert_eq!(table(&graph), [0, 1, 2, 3]);
    graph.lower_raw().unwrap();
    // A user declaration with a constructor's spelling retains its own body.
    let graph = source(
        "classical fn empty_bits()->Bit{1}
        pub isometry fn f(q:Q<Unit>)->Q<Bit>{basis q as () {empty_bits()}}",
    );
    assert_eq!(table(&graph), [1]);
    assert_eq!(graph.definitions()[graph.root()].steps()[0].effect(), "iso");
    graph.lower_raw().unwrap();
}

#[test]
fn selected_coherent_injectivity_checks_every_label_and_ordinary_label_copying() {
    let graph = source("pub isometry fn f(q:Q<Bit>)->Q<(Bit,Bit)>{basis q as x {(x,x)}}");
    assert_eq!(table(&graph), [0, 3]);
    graph.lower_raw().unwrap();
    for (basis, body) in [("Bit", "0"), ("(Bit,Bit)", "(a and b,b)")] {
        let pattern = if basis == "Bit" { "a" } else { "(a,b)" };
        let parsed = ParsedProgram::parse(BTreeMap::from([(
            "main".into(),
            format!(
                "pub unitary fn f(q:Q<{basis}>)->Q<{basis}>{{basis q as {pattern} {{{body}}}}}"
            ),
        )]))
        .unwrap();
        let error = parsed
            .instantiate("main::f", Default::default(), Default::default())
            .unwrap()
            .elaborate()
            .unwrap_err();
        assert_eq!(error.code(), "ownership", "{error}");
        assert!(error.to_string().contains("not injective"));
    }
}

#[test]
fn selected_coherent_input_work_precedes_the_isolated_map_once() {
    let graph = source(
        "use std::quantum::x;
        pub unitary fn f(q:Q<Bit>, r:Q<Bit>)->(Q<Bit>,Q<Bit>){
            (basis x(q) as b {not b},r)}",
    );
    let steps = graph.definitions()[graph.root()].steps();
    assert_eq!(steps.len(), 2);
    assert_eq!(steps[0].primitive(), Some("std::quantum::x"));
    assert_eq!(
        steps[0].output().identity(),
        steps[1].inputs()[0].identity()
    );
    assert_eq!(steps[1].basis_table(), Some([1, 0].as_slice()));
    graph.lower_raw().unwrap();
}

#[test]
fn selected_coherent_hierarchy_remains_an_explicit_profile_refusal() {
    let graph = source("pub unitary fn f(q:Q<Bit>)->Q<Bit>{basis q as x {not x}}");
    let error = graph.lower().unwrap_err();
    assert_eq!(error.code(), "unsupported");
    assert!(error.to_string().contains("coherent basis tables"));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn selected_coherent_native_raw_and_replay_preserve_an_entangled_caller() {
    use qleisli::interchange::native::Kernel;
    use qleisli::sim::{SimulationLimits, run_closed};
    let graph = source(
        "use std::quantum::{init0,h,cnot}; use std::observe::measure_z;
        pub observe fn f()->(Bit,Bit){let(a,b)=cnot(h(init0()),init0());
            let a=basis a as x {not x}; (measure_z(a),measure_z(b))}",
    );
    let proposal = graph.lower_raw().unwrap();
    let accepted = Kernel::selected()
        .unwrap()
        .accept(proposal.proposal())
        .unwrap();
    proposal.validate_source_steps(&accepted).unwrap();
    let outcomes = run_closed(&accepted, SimulationLimits::default()).unwrap();
    assert_eq!(outcomes.len(), 2);
    for result in [vec![false, true], vec![true, false]] {
        assert!((outcomes[&result] - 0.5).abs() < 1e-12);
    }
}

fn exact_pair(
    prefix: &str,
    domain: &str,
    codomain: &str,
    implementation: &str,
    reference: &str,
    agrees: bool,
) {
    use qleisli::contract::{DEFAULT_EXACT_WORK, exact::Budget};
    use qleisli::interchange::native::Kernel;

    let entry = if domain == codomain {
        format!(
            "pub unitary fn f(q:Q<{domain}>)->Q<{codomain}>{{
            apply_contract(implementation,specification,q)}}"
        )
    } else {
        // Rectangular maps use the existing arrow Meaning/provider gate.
        // ApplyContract deliberately remains an endomorphism-only API.
        format!(
            "meaning Requested:{domain} -> {codomain}=reference(specification);
            fn invoke[const U:Op<{domain} -> {codomain},Requested>](q:Q<{domain}>)->Q<{codomain}>
                requires Applicable(U){{U(q)}}
            pub isometry fn f(q:Q<{domain}>)->Q<{codomain}>{{
                invoke[checked_op(implementation,Requested)](q)}}"
        )
    };
    let graph = source(&format!(
        "{prefix}
        fn implementation(q:Q<{domain}>)->Q<{codomain}>{{{implementation}}}
        fn specification(q:Q<{domain}>)->Q<{codomain}>{{{reference}}}
        {entry}"
    ));
    let kernel = Kernel::selected().unwrap();
    // This checks every exact complex matrix entry of two separately authored
    // source bodies through fresh native decisions, including full codomain
    // shape. Agreement of a sampled distribution cannot satisfy this request.
    let checked = graph.check_function_contracts(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK));
    if !agrees && domain == codomain {
        assert_eq!(checked.unwrap_err().code(), "contract");
        return;
    }
    let checked = checked.unwrap();
    let meanings = checked.check_operation_meanings(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK));
    if !agrees {
        assert_eq!(meanings.unwrap_err().code(), "contract");
        return;
    }
    let meanings = meanings.unwrap();
    let proposal = meanings
        .lower_raw(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    let accepted = kernel.accept(proposal.proposal()).unwrap();
    proposal.validate_source_steps(&accepted).unwrap();
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn selected_coherent_exact_scalar_phase_survives_a_zero_width_owner_lift() {
    let prefix = "use std::quantum::phase_eighth;";
    let implementation = "basis phase_eighth(q) as () {()}";
    exact_pair(
        prefix,
        "Unit",
        "Unit",
        implementation,
        "phase_eighth(q)",
        true,
    );
    // These have the same sole measurement probability and different exact
    // scalar actions; both incorrect reference requests must be refused.
    for reference in ["q", "phase_eighth(phase_eighth(q))"] {
        exact_pair(prefix, "Unit", "Unit", implementation, reference, false);
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn selected_coherent_exact_inverse_and_control_use_the_original_square_map() {
    let prefix = "use std::quantum::{x,z,cnot,split,join};
        unitary fn lift(q:Q<Bit>)->Q<Bit>{basis q as x {not x}}";
    exact_pair(prefix, "Bit", "Bit", "adjoint(lift)(q)", "x(q)", true);
    exact_pair(prefix, "Bit", "Bit", "adjoint(lift)(q)", "q", false);
    exact_pair(prefix, "Bit", "Bit", "adjoint(lift)(q)", "z(x(q))", false);

    let controlled = "let(c,t)=split(q);let(c,t)=controlled(lift)(c,t);join(c,t)";
    exact_pair(
        prefix,
        "(Bit,Bit)",
        "(Bit,Bit)",
        controlled,
        "let(c,t)=split(q);let(c,t)=cnot(c,t);join(c,t)",
        true,
    );
    for reference in [
        "let(c,t)=split(q);let(t,c)=cnot(t,c);join(c,t)",
        "let(c,t)=split(q);let(c,t)=cnot(c,t);join(z(c),t)",
    ] {
        exact_pair(
            prefix,
            "(Bit,Bit)",
            "(Bit,Bit)",
            controlled,
            reference,
            false,
        );
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn selected_coherent_exact_rectangular_map_binds_phase_table_and_product_axes() {
    let prefix = "use std::quantum::{init0,x,z,cnot,join};";
    let implementation = "basis q as b {(b,not b)}";
    let reference = "let(a,b)=cnot(q,x(init0()));join(a,b)";
    exact_pair(prefix, "Bit", "(Bit,Bit)", implementation, reference, true);
    // The output table [2,1] is deliberately asymmetric, so exchanging output
    // axes is observable. All three references remain valid exact isometries.
    for reference in [
        "let(a,b)=cnot(q,x(init0()));join(b,a)",
        "let(a,b)=cnot(q,x(init0()));join(x(a),b)",
        "let(a,b)=cnot(q,x(init0()));join(z(a),b)",
    ] {
        exact_pair(prefix, "Bit", "(Bit,Bit)", implementation, reference, false);
    }
}
