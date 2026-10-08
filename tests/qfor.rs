//! Independent small-system checks for explicit quantum-owner folds.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
use qleisli::frontend::compile::ParsedProgram;
use qleisli::interchange::hierarchical::{Kernel, execution::ExecutionLimits};
use std::collections::BTreeMap;

fn parsed(source: &str) -> ParsedProgram {
    ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap()
}

#[test]
fn quantum_fold_preserves_an_external_reference_and_zero_iteration_identity() {
    let program = parsed(
        "use std::quantum::x; pub unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit>{qfor static i in 0..n carry a=q{yield x(a);}}",
    );
    let input = vec![[0.25, 0.5], [-0.75, 0.125], [0.375, -0.5], [-0.25, -0.625]];
    for n in 0..=3 {
        let instance = program
            .instantiate(
                "main::f",
                BTreeMap::from([("n".into(), n)]),
                BTreeMap::new(),
            )
            .unwrap();
        let proposal = instance.elaborate().unwrap().lower().unwrap();
        let repeated = instance.elaborate().unwrap().lower().unwrap();
        assert_eq!(
            proposal.payload(),
            repeated.payload(),
            "same source and bindings must elaborate deterministically"
        );
        let accepted = Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap())
            .check_against_native(proposal.payload(), proposal.comparison_request())
            .unwrap();
        let output = accepted
            .execute_pure(
                &input,
                2,
                ExecutionLimits {
                    max_amplitudes: 16,
                    max_steps: 1000,
                },
            )
            .unwrap();
        let expected: Vec<_> = (0..4)
            .map(|i| input[(i & !1) | ((i & 1) ^ (n as usize & 1))])
            .collect();
        assert_eq!(output.amplitudes, expected);
    }
}

#[test]
fn multiple_carried_owners_keep_the_complete_entangled_interface() {
    let program = parsed(
        "use std::quantum::cnot; pub unitary fn f[const n:Nat](a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){qfor static i in 0..n carry pair=(a,b){let(a,b)=pair;yield cnot(a,b);}}",
    );
    let input: Vec<_> = (0..8).map(|i| [i as f64 + 0.125, 0.5 - i as f64]).collect();
    for n in [0, 2] {
        let proposal = program
            .instantiate(
                "main::f",
                BTreeMap::from([("n".into(), n)]),
                BTreeMap::new(),
            )
            .unwrap()
            .elaborate()
            .unwrap()
            .lower()
            .unwrap();
        let accepted = Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap())
            .check_against_native(proposal.payload(), proposal.comparison_request())
            .unwrap();
        let output = accepted
            .execute_pure(
                &input,
                2,
                ExecutionLimits {
                    max_amplitudes: 32,
                    max_steps: 1000,
                },
            )
            .unwrap();
        // Independently, two controlled-X maps compose to identity on both
        // owners and any reference; no separability premise is used.
        assert_eq!(output.amplitudes, input);
    }
}

#[test]
fn zero_width_carry_does_not_erase_its_scalar_operator() {
    let program = parsed(
        "use std::quantum::phase_eighth; pub unitary fn f(q:Q<Unit>)->Q<Unit>{qfor static i in 0..4 carry a=q{yield phase_eighth(a);}}",
    );
    let proposal = program
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower()
        .unwrap();
    let accepted = Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap())
        .check_against_native(proposal.payload(), proposal.comparison_request())
        .unwrap();
    let input = vec![[0.25, 0.5], [-0.75, 0.125]];
    let output = accepted
        .execute_pure(
            &input,
            2,
            ExecutionLimits {
                max_amplitudes: 8,
                max_steps: 1000,
            },
        )
        .unwrap();
    // Four exact eighth turns are -1, including on the reference amplitudes.
    for (actual, value) in output.amplitudes.iter().zip(input) {
        assert!((actual[0] + value[0]).abs() < 1e-12 && (actual[1] + value[1]).abs() < 1e-12);
    }
}

#[test]
fn ordinary_and_quantum_folds_have_distinct_staging_and_carry_rules() {
    for (source, code, fragment) in [
        (
            "pub unitary fn f(q:Q<Bit>)->Q<Bit>{for static i in 0..0 carry a=q{yield a;}}",
            "type",
            "use qfor static",
        ),
        (
            "pub observe fn main()->Bit{qfor static i in 0..0 carry a=0{yield a;}}",
            "type",
            "must contain a quantum owner",
        ),
        (
            "pub unitary fn f(q:Q<Bit>)->Q<Bit>{qfor i in 0..1 carry a=q{yield a;}}",
            "parse",
            "static",
        ),
        (
            "pub unitary fn f(q:Q<Bit>)->Q<Bit>{qfor static i in 0..0 carry a=q{let b=a;yield a;}}",
            "ownership",
            "consumed",
        ),
        (
            "pub unitary fn f(q:Q<Bit>,r:Q<Bit>)->(Q<Bit>,Q<Bit>){let q=qfor static i in 0..0 carry a=q{yield r;};(q,r)}",
            "ownership",
            "consumed",
        ),
        (
            "pub unitary fn f(q:Q<Bit>)->Q<Bit>{qfor static i in 0..0 carry a=q{a}}",
            "parse",
            "requires yield",
        ),
        (
            "pub unitary fn f(q:Q<Bit>)->Q<Bit>{qfor static i in 0..1 carry a=q{yield(a,());}}",
            "type",
            "type",
        ),
    ] {
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
        assert_eq!(error.code(), code, "{source}: {error}");
        assert!(error.message().contains(fragment), "{source}: {error}");
    }
    let ordinary =
        parsed("pub observe fn main()->Bit{for static i in 0..3 carry a=0{yield not a;}}");
    let proposal = ordinary
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower_raw()
        .unwrap();
    let accepted = qleisli::interchange::native::Kernel::selected()
        .unwrap()
        .accept(proposal.proposal())
        .unwrap();
    assert_eq!(
        qleisli::sim::run_closed(&accepted, qleisli::sim::SimulationLimits::default()).unwrap(),
        BTreeMap::from([(vec![true], 1.0)])
    );
}
