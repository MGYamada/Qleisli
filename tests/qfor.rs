//! Independent small-system checks for explicit quantum-owner folds.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
// Fixture edition: "tests/fixtures/frontend_v030/qfor/reference-current/Qargo.toml".
// Fixed Fourier edition: "tests/fixtures/frontend_v030/qfor/fixed-fourier/Qargo.toml".
use qleisli::frontend::compile::ParsedProgram;
use qleisli::interchange::hierarchical::{Kernel, execution::ExecutionLimits};
use std::collections::BTreeMap;

fn parsed(source: &str) -> ParsedProgram {
    ParsedProgram::parse(
        qleisli::edition::Edition::E2026,
        BTreeMap::from([("main".into(), source.into())]),
    )
    .unwrap()
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn informed_fixed_fourier_fold_keeps_full_matrix_phase_and_axes() {
    use qleisli::contract::exact::{Budget, Exact, Matrix};
    use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK};
    use qleisli::edition::Edition;
    use qleisli::interchange::pure_leaf::{PureBoundary, check_pure};

    // Independently specify every F4[y,x] = i^(x*y)/2 coefficient. This is
    // fixed two-qubit conformance, separate from the Reference-only study.
    let entries = (0..4)
        .flat_map(|y| {
            (0..4).map(move |x| {
                Exact::new(
                    match (x * y) % 4 {
                        0 => [1, 0, 0, 0],
                        1 => [0, 0, 1, 0],
                        2 => [-1, 0, 0, 0],
                        _ => [0, 0, -1, 0],
                    },
                    1,
                )
                .unwrap()
            })
        })
        .collect::<Vec<_>>();
    let expected = Matrix::new(4, 4, entries.clone()).unwrap();
    let wrong_phase = Matrix::new(
        4,
        4,
        entries.iter().map(|value| value.neg().unwrap()).collect(),
    )
    .unwrap();
    let source = include_str!("fixtures/frontend_v030/qfor/fixed-fourier/main.qli");
    let wrong_axes = source.replace("join(b,a)", "join(a,b)");
    assert_ne!(source, wrong_axes);
    let kernel = qleisli::interchange::native::Kernel::selected(Edition::E2026).unwrap();
    for (input, matches) in [(source, true), (wrong_axes.as_str(), false)] {
        let proposal = parsed(input)
            .instantiate("main::fourier2", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap()
            .lower_raw()
            .unwrap();
        // The altered-axis graph must itself pass structural acceptance;
        // only the independent whole-matrix requirement distinguishes it.
        let accepted = kernel.accept(proposal.proposal()).unwrap();
        let basis = BasisType::Pair(Box::new(BasisType::Bit), Box::new(BasisType::Bit));
        let boundary = PureBoundary::new(
            basis.clone(),
            basis,
            accepted.raw().quantum_inputs[0].clone(),
            accepted.output_ports()[0].clone(),
        )
        .unwrap();
        let payload = proposal.proposal().artifact();
        let actual = check_pure(
            Edition::E2026,
            payload,
            &boundary,
            &expected,
            &mut Budget::new(DEFAULT_EXACT_WORK),
        );
        if matches {
            assert!(actual.unwrap().matches(payload, &boundary, &expected));
            assert!(
                check_pure(
                    Edition::E2026,
                    payload,
                    &boundary,
                    &wrong_phase,
                    &mut Budget::new(DEFAULT_EXACT_WORK),
                )
                .is_err()
            );
        } else {
            assert!(
                actual.is_err(),
                "wrong output axes must fail the F4 equation"
            );
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn reference_authoring_derivatives_match_independent_closed_distributions() {
    // Maintained current inputs, separate from the immutable first-authoring
    // archive. The paired authors wrote identical GHZ/accumulator bodies;
    // their phase-kickback preparations use two equivalent existing forms.
    let cases = [
        (
            include_str!("fixtures/frontend_v030/qfor/reference-current/ghz.qli"),
            BTreeMap::from([
                (vec![false, false, false], 0.5),
                (vec![true, true, true], 0.5),
            ]),
        ),
        (
            include_str!("fixtures/frontend_v030/qfor/reference-current/arithmetic.qli"),
            BTreeMap::from([(vec![false, false], 0.5), (vec![true, true], 0.5)]),
        ),
        (
            include_str!("fixtures/frontend_v030/qfor/reference-current/qpe-phase.qli"),
            BTreeMap::from([(vec![true, true], 1.0)]),
        ),
        (
            include_str!("fixtures/frontend_v030/qfor/reference-current/qpe-z.qli"),
            BTreeMap::from([(vec![true, true], 1.0)]),
        ),
    ];
    let kernel =
        qleisli::interchange::native::Kernel::selected(qleisli::edition::Edition::E2026).unwrap();
    for (source, expected) in cases {
        let proposal = parsed(source)
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap()
            .lower_raw()
            .unwrap();
        let accepted = kernel.accept(proposal.proposal()).unwrap();
        let actual =
            qleisli::sim::run_closed(&accepted, qleisli::sim::SimulationLimits::default()).unwrap();
        for (outcome, probability) in &actual {
            assert!(probability.is_finite());
            let wanted = expected.get(outcome).copied().unwrap_or(0.0);
            assert!((probability - wanted).abs() < 1e-10, "{source}: {actual:?}");
        }
        for (outcome, wanted) in expected {
            let probability = actual.get(&outcome).copied().unwrap_or(0.0);
            assert!((probability - wanted).abs() < 1e-10, "{source}: {actual:?}");
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn quantum_fold_preserves_an_external_reference_and_zero_iteration_identity() {
    let program = parsed(
        "use std::gate::x; pub unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit>{qfor static i in 0..n carry a=q{yield x(a);}}",
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
        let accepted = Kernel::new(
            std::env::var_os("QLEISLI_KERNEL").unwrap(),
            qleisli::edition::Edition::E2026,
        )
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
        assert_eq!(output.amplitudes.len(), expected.len());
        if n == 0 {
            assert_eq!(output.amplitudes, expected);
        }
        for (index, (actual, expected)) in output.amplitudes.iter().zip(&expected).enumerate() {
            for coordinate in 0..2 {
                assert!(actual[coordinate].is_finite() && expected[coordinate].is_finite());
                if n != 0 {
                    assert!(
                        (actual[coordinate] - expected[coordinate]).abs() < 1e-12,
                        "n={n}, amplitude={index}, coordinate={coordinate}: {actual:?} != {expected:?}"
                    );
                }
            }
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn multiple_carried_owners_keep_the_complete_entangled_interface() {
    let program = parsed(
        "use std::gate::cnot; pub unitary fn f[const n:Nat](a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){qfor static i in 0..n carry pair=(a,b){let(a,b)=pair;yield cnot(a,b);}}",
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
        let accepted = Kernel::new(
            std::env::var_os("QLEISLI_KERNEL").unwrap(),
            qleisli::edition::Edition::E2026,
        )
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
        assert_eq!(output.amplitudes.len(), input.len());
        if n == 0 {
            assert_eq!(output.amplitudes, input);
        }
        for (index, (actual, expected)) in output.amplitudes.iter().zip(&input).enumerate() {
            for coordinate in 0..2 {
                assert!(actual[coordinate].is_finite() && expected[coordinate].is_finite());
                if n != 0 {
                    assert!(
                        (actual[coordinate] - expected[coordinate]).abs() < 1e-12,
                        "n={n}, amplitude={index}, coordinate={coordinate}: {actual:?} != {expected:?}"
                    );
                }
            }
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn zero_width_carry_does_not_erase_its_scalar_operator() {
    let program = parsed(
        " pub unitary fn f(q:Q<Unit>)->Q<Unit>{qfor static i in 0..4 carry a=q{yield global_phase_eighth(a);}}",
    );
    let proposal = program
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower()
        .unwrap();
    let accepted = Kernel::new(
        std::env::var_os("QLEISLI_KERNEL").unwrap(),
        qleisli::edition::Edition::E2026,
    )
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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
        let error = ParsedProgram::parse(
            qleisli::edition::Edition::E2026,
            BTreeMap::from([("main".into(), source.into())]),
        )
        .unwrap_err();
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
    let accepted = qleisli::interchange::native::Kernel::selected(qleisli::edition::Edition::E2026)
        .unwrap()
        .accept(proposal.proposal())
        .unwrap();
    assert_eq!(
        qleisli::sim::run_closed(&accepted, qleisli::sim::SimulationLimits::default()).unwrap(),
        BTreeMap::from([(vec![true], 1.0)])
    );
}
