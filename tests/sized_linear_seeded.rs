// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
//! Bounded independent enumeration of accepted generic size implications.
//! This regression is not a completeness or soundness proof of the solver.

use qleisli::frontend::sized::ParsedProgram;
use std::collections::BTreeMap;
use std::fmt::Write;

#[test]
fn seeded_generic_size_implications_agree_with_concrete_enumeration() {
    const CASES: usize = 512;
    const BOUND: u64 = 3;
    let mut seed = 42_u64;
    let mut random = |bound: u64| {
        seed = seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (seed >> 32) % bound
    };
    let expression = |coefficients: [u64; 3]| {
        format!(
            "{}+{}*n+{}*m",
            coefficients[0], coefficients[1], coefficients[2]
        )
    };
    let signs = ["==", "!=", "<", "<=", ">", ">="];
    let mut accepted_programs = 0;
    let mut concrete_environments = 0;
    for case in 0..CASES {
        let input = [random(4), random(3), random(3)];
        let output = if case % 4 == 0 {
            input
        } else {
            [random(4), random(3), random(3)]
        };
        let guards: Vec<_> = (0..3)
            .map(|_| ([random(4), random(3), random(3)], random(6), random(10)))
            .collect();
        let mut clauses = String::new();
        for (coefficients, sign, constant) in &guards {
            write!(
                clauses,
                ", {} {} {}",
                expression(*coefficients),
                signs[*sign as usize],
                constant
            )
            .unwrap();
        }
        let source = format!(
            "pub unitary fn f[static n: Nat, static m: Nat](q: Q<Bits<{}>>) \
             -> Q<Bits<{}>> requires n <= {BOUND}, m <= {BOUND}{clauses} {{ q }}",
            expression(input),
            expression(output)
        );
        if ParsedProgram::parse(BTreeMap::from([("main".into(), source.clone())])).is_err() {
            continue;
        }
        accepted_programs += 1;
        // Ordinary integer arithmetic is the independent oracle. Every
        // environment permitted by these finite source premises is checked,
        // including those of inconsistent (vacuously accepted) premises.
        for n in 0..=BOUND {
            for m in 0..=BOUND {
                let evaluate = |x: [u64; 3]| x[0] + x[1] * n + x[2] * m;
                let allowed = guards.iter().all(|(coefficients, sign, constant)| {
                    let value = evaluate(*coefficients);
                    match sign {
                        0 => value == *constant,
                        1 => value != *constant,
                        2 => value < *constant,
                        3 => value <= *constant,
                        4 => value > *constant,
                        _ => value >= *constant,
                    }
                });
                if allowed {
                    concrete_environments += 1;
                    assert_eq!(
                        evaluate(input),
                        evaluate(output),
                        "accepted counterexample (seed 42, case {case}, n={n}, m={m}): {source}"
                    );
                }
            }
        }
    }
    // Avoid a vacuous pass if parsing or all generated premises regress.
    assert!(accepted_programs > 0 && accepted_programs < CASES);
    assert!(concrete_environments > 0);
    eprintln!(
        "seed 42: {CASES} generated programs; {accepted_programs} accepted; \
         {concrete_environments} concrete environments checked (n,m in 0..={BOUND})"
    );
}
