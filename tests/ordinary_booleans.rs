//! Independent bounded checks for ordinary Boolean source convergence.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::frontend::compile::{ElaboratedProgram, ParsedProgram};
use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::interchange::native::{AcceptedProgram, Kernel};
use qleisli::ir::{Effect, RawOp};
use qleisli::sim::{SimulationError, SimulationLimits, run_closed};
use std::collections::BTreeMap;

fn elaborate(source: &str, entry: &str, naturals: BTreeMap<String, u32>) -> ElaboratedProgram {
    let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap();
    // Retained source and owned lexical identities must survive the original
    // parsed value's lifetime, including helper calls and specialization.
    let retained = parsed.clone();
    drop(parsed);
    assert_eq!(retained.source("main"), Some(source));
    retained
        .instantiate(entry, naturals, BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
}

fn accept(graph: &ElaboratedProgram) -> AcceptedProgram {
    let proposal = graph.lower_raw().unwrap();
    assert_eq!(
        proposal.source().instantiation().program().source("main"),
        graph.instantiation().program().source("main")
    );
    let kernel = Kernel::new(std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"));
    let accepted = kernel.accept(proposal.proposal()).unwrap();
    assert_eq!(accepted.artifact(), proposal.payload());
    assert!(accepted.request().is_none());
    proposal.validate_source_steps(&accepted).unwrap();
    accepted
}

fn both_closed(source: &str, expected: &[bool]) -> ElaboratedProgram {
    let distribution = BTreeMap::from([(expected.to_vec(), 1.0)]);
    let finite = compile_project(&SourceRoot::new(source).0).unwrap();
    assert_eq!(
        run_closed(&finite, SimulationLimits::default()).unwrap(),
        distribution
    );
    let graph = elaborate(source, "main::main", BTreeMap::new());
    let accepted = accept(&graph);
    assert_eq!(
        run_closed(&accepted, SimulationLimits::default()).unwrap(),
        distribution
    );
    graph
}

fn sized_reject(source: &str, code: &str) {
    let error = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
    assert_eq!(error.code(), code, "{error}");
    assert_eq!(error.module(), Some("main"), "{error}");
    assert!(error.span().end > error.span().start, "{error}");
    assert!(error.span().end <= source.len(), "{error}");
}

#[test]
fn all_four_truth_rows_match_independent_constants_in_both_profiles() {
    // These expected rows are independent of both compilers and the simulator:
    // output order is NOT(a), XOR(a,b), AND(a,b), with no packed Bits coercion.
    for (a, b, expected) in [
        (0, 0, [true, false, false]),
        (0, 1, [true, true, false]),
        (1, 0, [false, true, false]),
        (1, 1, [false, false, true]),
    ] {
        let source = format!(
            "unitary fn truth(a: Bit, b: Bit) -> (Bit,Bit,Bit) {{
                (not a, a xor b, a and b)
             }}
             pub observe fn main() -> (Bit,Bit,Bit) {{ truth({a},{b}) }}"
        );
        let graph = both_closed(&source, &expected);
        let truth = graph
            .definitions()
            .iter()
            .find(|definition| definition.path() == "main::truth")
            .unwrap();
        assert_eq!(truth.inputs().len(), 2);
        assert!(
            truth
                .inputs()
                .iter()
                .all(|value| { value.ty().kind() == "bit" && !value.ty().is_quantum() })
        );
        assert_eq!(
            truth
                .steps()
                .iter()
                .map(|step| step.boolean_operator())
                .collect::<Vec<_>>(),
            [Some("not"), Some("xor"), Some("and")]
        );
    }
}

#[test]
fn ordinary_aliases_copy_drop_and_exact_unit_products_survive_raw_flattening() {
    let source = "unitary fn f((u,(a,b)): (Unit,(Bit,Bit))) -> ((Bit,Unit),(Bit,(Bit,Unit))) {
        let alias = a; let _ = b; ((alias,()),(a,(not a,u)))
    }
    pub observe fn main() -> ((Bit,Unit),(Bit,(Bit,Unit))) { f(((),(1,0))) }";
    let graph = both_closed(source, &[true, true, false]);
    let definition = graph
        .definitions()
        .iter()
        .find(|d| d.path() == "main::f")
        .unwrap();
    assert_eq!(definition.inputs().len(), 1);
    let input = &definition.inputs()[0];
    assert_eq!(input.ty().kind(), "tuple");
    assert_eq!(input.fields()[0].ty().kind(), "unit");
    assert_eq!(input.fields()[1].fields().len(), 2);
    let output = definition.output();
    assert_eq!(output.fields().len(), 2);
    assert_eq!(output.fields()[0].fields()[1].ty().kind(), "unit");
    assert_eq!(
        output.fields()[1].fields()[1].fields()[1].ty().kind(),
        "unit"
    );
    assert_eq!(
        output.fields()[0].fields()[0].identity(),
        output.fields()[1].fields()[0].identity()
    );

    // Ordinary Unit consumes no transport bit. Dropping an ordinary result is
    // allowed, but does not erase its already evaluated Boolean source steps.
    let graph = both_closed(
        "unitary fn forget(b: Bit) -> Unit { let _ = not b; () }
         pub observe fn main() -> Unit { let () = forget(1); () }",
        &[],
    );
    let accepted = accept(&graph);
    assert!(accepted.raw().classical_outputs.is_empty());
    assert_eq!(accepted.raw().operations.len(), 2);
    assert!(matches!(
        accepted.raw().operations[0],
        RawOp::ClassicalConst { value: true, .. }
    ));
    assert!(matches!(
        accepted.raw().operations[1],
        RawOp::ClassicalNot { .. }
    ));
}

#[test]
fn repeated_shared_calls_keep_each_invocations_classical_values() {
    let graph = both_closed(
        "unitary fn flip(b: Bit) -> Bit { not b }
         pub observe fn main() -> (Bit,Bit,Bit) { (flip(0),flip(1),flip(flip(0))) }",
        &[true, false, false],
    );
    assert_eq!(
        graph
            .definitions()
            .iter()
            .filter(|d| d.path() == "main::flip")
            .count(),
        1
    );
    let root = &graph.definitions()[graph.root()];
    assert_eq!(
        root.steps()
            .iter()
            .filter(|step| step.called_definition().is_some())
            .count(),
        4
    );
    let accepted = accept(&graph);
    assert_eq!(
        accepted
            .raw()
            .operations
            .iter()
            .filter(|op| matches!(op, RawOp::ClassicalNot { .. }))
            .count(),
        4
    );
}

#[test]
fn static_zero_one_two_folds_and_selection_produce_runtime_bits() {
    let fold = "unitary fn flip(b: Bit) -> Bit { not b }
        pub unitary fn f[const n: Nat]() -> Bit {
            for static i in 0..n carry bit = 0 { yield flip(bit); }
        }";
    let selection = "pub unitary fn f[const n: Nat]() -> Bit {
        if static n == 0 { 0 } else { 1 }
    }";
    for n in 0..=2 {
        for (source, expected) in [(fold, n == 1), (selection, n != 0)] {
            let graph = elaborate(source, "main::f", BTreeMap::from([("n".into(), n)]));
            assert_eq!(graph.definitions()[graph.root()].naturals()["n"], n);
            let accepted = accept(&graph);
            assert_eq!(
                run_closed(&accepted, SimulationLimits::default()).unwrap(),
                BTreeMap::from([(vec![expected], 1.0)])
            );
            if source == fold {
                assert_eq!(accepted.raw().operations.len(), n as usize + 1);
            }
        }
    }
}

#[test]
fn unused_declarations_static_arms_and_zero_fold_bodies_are_still_checked() {
    for expression in ["not q", "q xor 1", "0 and q"] {
        let source = format!(
            "unitary fn bad(q: Q<Bit>) -> Bit {{ {expression} }}
             observe fn main() -> Bit {{ 0 }}"
        );
        sized_reject(&source, "type");
        let error = check_project(&SourceRoot::new(&source).0).unwrap_err();
        assert_eq!(error.code, ErrorCode::TypeMismatch, "{error}");
        assert!(error.span.end > error.span.start, "{error}");
    }
    for (ty, expression) in [
        ("Bits<1>", "not b"),
        ("Bits<0>", "b xor 1"),
        ("Unit", "0 and b"),
    ] {
        sized_reject(
            &format!(
                "unitary fn bad(b: {ty}) -> Bit {{ {expression} }} observe fn main() -> Bit {{ 0 }}"
            ),
            "type",
        );
    }
    sized_reject("pub unitary fn f[const n: Nat]() -> Bit { n }", "type");
    sized_reject(
        "unitary fn keep[const m: Nat](b: Bit) -> Bit { b }
         pub unitary fn f(n: Bit) -> Bit { keep[n](n) }",
        "static",
    );
    sized_reject(
        "pub unitary fn f[const n: Nat]() -> Bit {
            if static n == 0 { 0 } else { not () }
        }",
        "type",
    );
    sized_reject(
        "pub unitary fn f(q: Q<Bit>) -> (Bit,Q<Bit>) {
            let bit = for static i in 0..0 carry bit = 0 { let _ = not q; yield bit; };
            (bit,q)
        }",
        // The quantum value is outside the fold's carry scope. That existing
        // ownership failure precedes checking its Boolean operand type.
        "ownership",
    );
    sized_reject(
        "pub unitary fn f() -> Bit {
            for static i in 0..0 carry bit = 0 { let _ = not (); yield bit; }
        }",
        "type",
    );
}

#[test]
fn ordinary_registers_retain_exact_source_types_at_the_raw_boundary() {
    for width in 0..=2 {
        let source = format!("pub unitary fn f(b: Bits<{width}>) -> Bits<{width}> {{ b }}");
        let graph = elaborate(&source, "main::f", BTreeMap::new());
        let accepted = accept(&graph);
        let root = &graph.definitions()[graph.root()];
        assert_eq!(root.inputs()[0].ty(), root.output().ty());
        assert_eq!(root.inputs()[0].ty().kind(), "bits");
        assert!(root.inputs()[0].fields().is_empty());
        assert_eq!(accepted.raw().classical_inputs.len(), width);
        assert_eq!(
            accepted.raw().classical_inputs,
            accepted.raw().classical_outputs
        );
        assert!(accepted.raw().quantum_inputs.is_empty());
    }

    // An otherwise valid quantum hierarchy cannot silently erase an unused
    // ordinary computation while its explicit target support is unfinished.
    let source = "pub unitary fn f(q: Q<Bit>) -> Q<Bit> { let unused = 0; q }";
    let graph = elaborate(source, "main::f", BTreeMap::new());
    let error = graph.lower().unwrap_err();
    assert_eq!(error.code(), "unsupported", "{error}");
    assert_eq!(error.module(), Some("main"), "{error}");
    assert_eq!(&source[error.span().start..error.span().end], "0");
}

#[test]
fn quantum_bits_raw_boundary_retains_atomic_types_and_zero_width_owner() {
    use qleisli::contract::BasisType;
    for width in 0..=2 {
        let source = format!("pub unitary fn f(q: Q<Bits<{width}>>) -> Q<Bits<{width}>> {{ q }}");
        let graph = elaborate(&source, "main::f", BTreeMap::new());
        let accepted = accept(&graph);
        let interface = accepted.root_interface().unwrap();
        assert_eq!(interface.input, BasisType::Bits(width));
        assert_eq!(interface.output, BasisType::Bits(width));
        assert_eq!(accepted.raw().quantum_inputs.len(), 1);
        assert_eq!(accepted.raw().quantum_inputs[0].wires.len(), width as usize);
        assert_eq!(accepted.raw().quantum_outputs.len(), 1);
        assert_eq!(
            accepted.raw().quantum_outputs[0],
            accepted.raw().quantum_inputs[0].token
        );
    }
}

#[test]
fn false_and_measurement_is_eager_and_cannot_hide_observation_effects() {
    let source = "use std::quantum::{init0,h}; use std::observe::measure_z;
        pub observe fn f(q: Q<Bit>) -> Bit { 0 and measure_z(q) }
        observe fn main() -> Bit { f(h(init0())) }";
    let graph = elaborate(source, "main::f", BTreeMap::new());
    let root = &graph.definitions()[graph.root()];
    assert_eq!(root.effect(), "observe");
    let steps = root.steps();
    assert_eq!(steps.len(), 3);
    assert_eq!(steps[0].boolean_operator(), Some("constant"));
    assert_eq!(steps[0].boolean_literal(), Some(false));
    assert_eq!(steps[1].primitive(), Some("std::observe::measure_z"));
    assert_eq!(steps[1].effect(), "observe");
    assert_eq!(steps[1].inputs()[0].identity(), root.inputs()[0].identity());
    assert_eq!(steps[2].boolean_operator(), Some("and"));
    assert_eq!(
        steps[2].inputs()[0].identity(),
        steps[0].output().identity()
    );
    assert_eq!(
        steps[2].inputs()[1].identity(),
        steps[1].output().identity()
    );
    let mixed = accept(&graph);
    assert_eq!(mixed.derived_effect(), Effect::Observe);
    assert!(matches!(mixed.raw().operations[1], RawOp::MeasureZ { .. }));
    assert!(matches!(
        mixed.raw().operations[2],
        RawOp::ClassicalAnd { .. }
    ));

    // The existing finite endpoint supports this quantum example. Inspect the
    // actual accepted operations: output zero alone cannot show measurement ran.
    let finite = compile_project(&SourceRoot::new(source).0).unwrap();
    assert_eq!(finite.derived_effect(), Effect::Observe);
    let operations = &finite.raw().operations;
    let measured = operations
        .iter()
        .position(|op| matches!(op, RawOp::MeasureZ { .. }))
        .unwrap();
    let conjunction = operations
        .iter()
        .position(|op| matches!(op, RawOp::ClassicalAnd { .. }))
        .unwrap();
    assert!(measured < conjunction);
    let probabilities = run_closed(&finite, SimulationLimits::default()).unwrap();
    assert_eq!(probabilities.len(), 1);
    assert!((probabilities[&vec![false]] - 1.0).abs() < 1e-12);

    let forbidden = "use std::observe::measure_z;
        unitary fn bad(q: Q<Bit>) -> Bit { 0 and measure_z(q) }
        observe fn main() -> Bit { 0 }";
    sized_reject(forbidden, "effect");
    assert_eq!(
        check_project(&SourceRoot::new(forbidden).0)
            .unwrap_err()
            .code,
        ErrorCode::Effect
    );
}

#[test]
fn open_classical_inputs_remain_explicit_and_are_not_quantum_basis_arguments() {
    let graph = elaborate(
        "pub unitary fn f((u,b): (Unit,Bit)) -> (Bit,Bit,Unit) { (b,b,u) }",
        "main::f",
        BTreeMap::new(),
    );
    let accepted = accept(&graph);
    assert!(accepted.raw().quantum_inputs.is_empty());
    assert_eq!(accepted.raw().classical_inputs.len(), 1);
    assert_eq!(
        accepted.raw().classical_outputs,
        vec![accepted.raw().classical_inputs[0]; 2]
    );
    assert!(matches!(
        run_closed(&accepted, SimulationLimits::default()),
        Err(SimulationError::NotClosed("classical inputs are present"))
    ));
}

#[test]
fn ordinary_register_pack_rows_and_nested_copies_have_independent_ordered_results() {
    for (a, b) in [(0, 0), (0, 1), (1, 0), (1, 1)] {
        let source = format!("use std::classical::{{empty_bits,prepend_bit}};
            unitary fn pack(a:Bit,b:Bit)->Bits<2>{{prepend_bit[1](a,prepend_bit[0](b,empty_bits()))}}
            pub unitary fn main()->Bits<2>{{pack({a},{b})}}");
        let graph = elaborate(&source, "main::main", BTreeMap::new());
        let accepted = accept(&graph);
        assert_eq!(
            run_closed(&accepted, SimulationLimits::default()).unwrap(),
            BTreeMap::from([(vec![a == 1, b == 1], 1.0)])
        );
    }
    let source = include_str!(
        "fixtures/authoring_sessions/ordinary-bits-v030/attempt-02/nested-copy/main.qli"
    );
    let graph = elaborate(source, "main::main", BTreeMap::new());
    assert_eq!(
        run_closed(&accept(&graph), SimulationLimits::default()).unwrap(),
        BTreeMap::from([(vec![false, true, true, false, true], 1.0)])
    );
}

#[test]
fn zero_register_and_nat_helpers_copy_and_drop_without_quantum_owners() {
    let source = "use std::classical::empty_bits;
        classical fn copy(b:Bits<0>)->(Bits<0>,Bits<0>){(b,b)}
        unitary fn discard(b:Bits<0>)->Unit{let _=b;()}
        pub unitary fn main()->(Bits<0>,Bits<0>){let b=empty_bits();let _=discard(b);copy(b)}";
    let graph = elaborate(source, "main::main", BTreeMap::new());
    assert_eq!(
        run_closed(&accept(&graph), SimulationLimits::default()).unwrap(),
        BTreeMap::from([(vec![], 1.0)])
    );
    for n in 0..=2 {
        let graph = elaborate(
            "pub unitary fn f[const n:Nat](b:Bits<n>)->Bits<n>{b}",
            "main::f",
            BTreeMap::from([("n".into(), n)]),
        );
        let accepted = accept(&graph);
        assert_eq!(accepted.raw().classical_inputs.len(), n as usize);
        assert_eq!(
            accepted.raw().classical_inputs,
            accepted.raw().classical_outputs
        );
    }
}

#[test]
fn copied_measured_registers_preserve_bell_correlation_and_eager_effects() {
    let source = include_str!(
        "fixtures/authoring_sessions/ordinary-bits-v030/attempt-03/measured-copy/main.qli"
    );
    let graph = elaborate(source, "main::main", BTreeMap::new());
    let accepted = accept(&graph);
    assert_eq!(accepted.raw().declared_effect, Effect::Observe);
    let distribution = run_closed(&accepted, SimulationLimits::default()).unwrap();
    assert_eq!(distribution.len(), 2);
    for key in [vec![false; 4], vec![true; 4]] {
        assert!((distribution[&key] - 0.5).abs() < 1e-12);
    }
    // Dropping an ordinary packed result cannot erase its measurement.
    let graph = elaborate(
        "use std::classical::{empty_bits,prepend_bit};use std::quantum::init0;
        use std::observe::measure_z; pub observe fn main()->Unit{
        let _=prepend_bit[0](measure_z(init0()),empty_bits());()}",
        "main::main",
        BTreeMap::new(),
    );
    let accepted = accept(&graph);
    assert_eq!(accepted.raw().declared_effect, Effect::Observe);
    assert!(
        accepted
            .raw()
            .operations
            .iter()
            .any(|op| matches!(op, RawOp::MeasureZ { .. }))
    );
}

#[test]
fn ordinary_basis_substitutions_keep_register_and_product_tags() {
    use qleisli::frontend::compile::BasisBinding;
    let parsed = ParsedProgram::parse(BTreeMap::from([(
        "main".into(),
        "pub unitary fn f[const A:Basis](b:A)->A{b}".into(),
    )]))
    .unwrap();
    for (ty, width) in [
        ("Unit", 0),
        ("Bits<0>", 0),
        ("Bit", 1),
        ("Bits<1>", 1),
        ("Bits<2>", 2),
        ("(Bits<0>,(Bit,Bits<1>))", 2),
    ] {
        let graph = parsed
            .instantiate_with_types(
                "main::f",
                BTreeMap::from([("A".into(), BasisBinding::parse(ty).unwrap())]),
                BTreeMap::new(),
                BTreeMap::new(),
            )
            .unwrap()
            .elaborate()
            .unwrap();
        let root = &graph.definitions()[graph.root()];
        assert_eq!(
            root.inputs()[0].ty().kind(),
            match ty {
                "Unit" => "unit",
                "Bit" => "bit",
                "(Bits<0>,(Bit,Bits<1>))" => "tuple",
                _ => "bits",
            }
        );
        if ty.starts_with("Bits") {
            assert_eq!(root.inputs()[0].ty().width(), Some(width as u32));
        }
        if ty.starts_with('(') {
            let fields = root.inputs()[0].ty().fields();
            assert_eq!(fields[0].kind(), "bits");
            assert_eq!(fields[0].width(), Some(0));
            assert_eq!(fields[1].fields()[0].kind(), "bit");
            assert_eq!(fields[1].fields()[1].kind(), "bits");
        }
        assert_eq!(root.inputs()[0].ty(), root.output().ty());
        let accepted = accept(&graph);
        assert_eq!(accepted.raw().classical_inputs.len(), width);
        assert_eq!(
            accepted.raw().classical_inputs,
            accepted.raw().classical_outputs
        );
    }
}

#[test]
fn quantum_provider_calls_retain_unused_ordinary_register_computation() {
    use qleisli::frontend::compile::{BasisBinding, OperationBinding};
    let text = "use std::classical::{empty_bits,prepend_bit};
        classical fn copy(b:Bits<2>)->(Bits<2>,Bits<2>){(b,b)}
        unitary fn provider[const B:Basis](q:Q<B>)->Q<B>{
        let b=prepend_bit[1](0,prepend_bit[0](1,empty_bits()));let _=copy(b);q}
        pub unitary fn f[const A:Basis,const U:Op<A>](q:Q<A>)->Q<A> requires Apply(U){U(q)}";
    let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())])).unwrap();
    for ty in ["Unit", "Bits<0>", "Bits<1>", "Bits<2>"] {
        let binding = BasisBinding::parse(ty).unwrap();
        let graph = parsed
            .instantiate_with_types(
                "main::f",
                BTreeMap::from([("A".into(), binding.clone())]),
                BTreeMap::new(),
                BTreeMap::from([(
                    "U".into(),
                    OperationBinding::with_types(
                        "main::provider",
                        BTreeMap::from([("B".into(), binding)]),
                        BTreeMap::new(),
                    ),
                )]),
            )
            .unwrap()
            .elaborate()
            .unwrap();
        let accepted = accept(&graph);
        assert_eq!(accepted.raw().quantum_inputs.len(), 1);
        assert_eq!(accepted.raw().quantum_outputs.len(), 1);
        assert!(accepted.raw().classical_outputs.is_empty());
        assert_eq!(accepted.raw().operations.len(), 2);
        assert!(
            accepted
                .raw()
                .operations
                .iter()
                .all(|op| matches!(op, RawOp::ClassicalConst { .. }))
        );
    }
    let error = parsed
        .instantiate_with_types(
            "main::f",
            BTreeMap::from([("A".into(), BasisBinding::parse("Bits<1>").unwrap())]),
            BTreeMap::new(),
            BTreeMap::from([(
                "U".into(),
                OperationBinding::with_types(
                    "main::provider",
                    BTreeMap::from([("B".into(), BasisBinding::parse("Bit").unwrap())]),
                    BTreeMap::new(),
                ),
            )]),
        )
        .unwrap_err();
    assert_eq!(error.code(), "type");
}

#[test]
fn register_type_coercions_and_quantum_copy_drop_still_reject() {
    for source in [
        "pub unitary fn f(b:Bits<0>)->Unit{b}",
        "pub unitary fn f(b:Bits<1>)->Bit{b}",
        "pub unitary fn f(b:Bits<2>)->(Bit,Bit){b}",
        "pub unitary fn f(b:(Bits<0>,Bit))->(Unit,Bit){b}",
    ] {
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
        assert_eq!(error.code(), "type", "{error}");
    }
    for source in [
        "pub unitary fn f(q:Q<Bits<0>>)->(Q<Bits<0>>,Q<Bits<0>>){(q,q)}",
        "pub unitary fn f(q:Q<Bits<1>>)->Unit{let _=q;()}",
    ] {
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
        assert_eq!(error.code(), "ownership", "{error}");
    }
}

#[test]
fn retained_register_source_rejects_another_native_accepted_artifact() {
    let text = "use std::classical::{empty_bits,prepend_bit};
        pub unitary fn main()->Bits<2>{prepend_bit[1](0,prepend_bit[0](1,empty_bits()))}";
    let graph = elaborate(text, "main::main", BTreeMap::new());
    let proposal = graph.lower_raw().unwrap();
    let changed = text.replace(
        "prepend_bit[1](0,prepend_bit[0](1",
        "prepend_bit[1](1,prepend_bit[0](0",
    );
    let other = elaborate(&changed, "main::main", BTreeMap::new());
    let accepted = accept(&other);
    let error = proposal.validate_source_steps(&accepted).unwrap_err();
    assert_eq!(error.code(), "preservation");
    assert!(error.message().contains("differs"));
    assert_eq!(
        proposal.source().instantiation().program().source("main"),
        Some(text)
    );
}
