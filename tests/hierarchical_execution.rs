//! Independent small-system coefficient oracles for the checked runtime adapter.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use qleisli::interchange::hierarchical::{
    CheckedInstrument, Kernel,
    execution::{ExecutionLimits, SamplingError, SamplingLimits},
};
use qleisli::sim::{RandomSource, SplitMix64};
use std::path::Path;

fn kernel() -> Kernel {
    Kernel::new(
        std::env::var_os("QLEISLI_HIERARCHY_KERNEL").expect("select the built, audited kernel"),
    )
}
fn coefficients(path: &Path) -> Vec<[f64; 2]> {
    std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .map(|line| {
            let values: Vec<f64> = line
                .split_whitespace()
                .map(|x| x.parse().unwrap())
                .collect();
            assert_eq!(values.len(), 2);
            [values[0], values[1]]
        })
        .collect()
}
fn compare(actual: &[[f64; 2]], expected: &[[f64; 2]]) -> f64 {
    assert_eq!(actual.len(), expected.len());
    let error = actual
        .iter()
        .flatten()
        .zip(expected.iter().flatten())
        .map(|(a, b)| (a - b).abs())
        .fold(0.0, f64::max);
    assert!(error < 1e-11, "full complex coefficient error {error}");
    error
}

#[test]
#[ignore = "requires the separately built and audited Lean kernel"]
fn frozen_finite_leaf_executes_through_its_actual_definition_index() {
    let root =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/verification_v022/hierarchy");
    let checked = kernel()
        .check_against(
            &std::fs::read(root.join("h.qirh")).unwrap(),
            &std::fs::read(root.join("h.request.json")).unwrap(),
        )
        .unwrap();
    let limits = ExecutionLimits {
        max_amplitudes: 8,
        max_steps: 1000,
    };
    let input = [[1.0, 0.0], [0.0, 0.0], [0.0, 0.0], [0.0, 2.0]];
    let result = checked.execute(&input, 2, limits).unwrap();
    let h = std::f64::consts::FRAC_1_SQRT_2;
    compare(
        &result.amplitudes,
        &[[h, 0.0], [h, 0.0], [0.0, 2.0 * h], [0.0, -2.0 * h]],
    );
    assert_eq!(
        checked
            .execute(
                &input,
                2,
                ExecutionLimits {
                    max_amplitudes: 7,
                    ..limits
                }
            )
            .unwrap_err()
            .code,
        "limit"
    );
    assert_eq!(
        checked
            .execute(
                &input,
                2,
                ExecutionLimits {
                    max_steps: result.steps - 1,
                    ..limits
                }
            )
            .unwrap_err()
            .code,
        "limit"
    );
    checked
        .execute(
            &input,
            2,
            ExecutionLimits {
                max_steps: result.steps,
                ..limits
            },
        )
        .unwrap();
    for invalid in [
        [f64::NAN, 0.0],
        [f64::INFINITY, 0.0],
        [0.0, f64::NEG_INFINITY],
    ] {
        assert_eq!(
            checked
                .execute(&[invalid, [0.0, 0.0]], 1, limits)
                .unwrap_err()
                .code,
            "execution"
        );
    }
    assert_eq!(
        checked.execute(&input, 0, limits).unwrap_err().code,
        "execution"
    );
    assert_eq!(
        checked.execute(&input, 1, limits).unwrap_err().code,
        "execution"
    );
}

#[test]
#[ignore = "run scripts/test_hierarchical_execution.py with the audited Lean kernel"]
fn small_source_clients_match_independent_complex_reference_branches() {
    let directory =
        std::env::var_os("QLEISLI_HIERARCHICAL_EXECUTION").expect("source oracle fixtures");
    let directory = Path::new(&directory);
    let kernel = kernel();
    let limits = ExecutionLimits {
        max_amplitudes: 1 << 16,
        max_steps: 10_000_000,
    };
    for line in std::fs::read_to_string(directory.join("cases.tsv"))
        .unwrap()
        .lines()
    {
        let fields: Vec<_> = line.split('\t').collect();
        assert_eq!(fields.len(), 5);
        let (name, kind) = (fields[0], fields[1]);
        let reference = fields[2].parse().unwrap();
        let output_bits: usize = fields[3].parse().unwrap();
        let measured_bits: usize = fields[4].parse().unwrap();
        let actual = std::fs::read(directory.join(format!("{name}.json"))).unwrap();
        let request = std::fs::read(directory.join(format!("{name}.request.json"))).unwrap();
        let input = coefficients(&directory.join(format!("{name}.input")));
        let expected = coefficients(&directory.join(format!("{name}.expected")));
        if kind == "pure" {
            let checked = kernel.check_against(&actual, &request).unwrap();
            let result = checked.execute(&input, reference, limits).unwrap();
            assert_eq!(result.quantum_bits, output_bits);
            let error = compare(&result.amplitudes, &expected);
            assert_eq!(
                checked
                    .execute(
                        &input,
                        reference,
                        ExecutionLimits {
                            max_steps: result.steps - 1,
                            ..limits
                        }
                    )
                    .unwrap_err()
                    .code,
                "limit"
            );
            checked
                .execute(
                    &input,
                    reference,
                    ExecutionLimits {
                        max_steps: result.steps,
                        ..limits
                    },
                )
                .unwrap();
            assert_eq!(
                checked
                    .execute(
                        &input,
                        reference,
                        ExecutionLimits {
                            max_amplitudes: 2 * expected.len() - 1,
                            ..limits
                        }
                    )
                    .unwrap_err()
                    .code,
                "limit"
            );
            println!(
                "EXECUTION|{name}|{}|{}|{error}",
                expected.len(),
                result.steps
            );
        } else {
            assert_eq!(kind, "instrument");
            let checked = kernel.check_instrument(&actual, &request).unwrap();
            let result = checked.execute(&input, reference, limits).unwrap();
            assert_eq!(result.residual_quantum_bits, output_bits);
            assert_eq!(result.measured_bits, measured_bits);
            assert_eq!(result.branches.len(), 1 << measured_bits);
            let flattened: Vec<_> = result.branches.into_iter().flatten().collect();
            let error = compare(&flattened, &expected);
            assert_eq!(
                checked
                    .execute(
                        &input,
                        reference,
                        ExecutionLimits {
                            max_steps: result.steps - 1,
                            ..limits
                        }
                    )
                    .unwrap_err()
                    .code,
                "limit"
            );
            checked
                .execute(
                    &input,
                    reference,
                    ExecutionLimits {
                        max_steps: result.steps,
                        ..limits
                    },
                )
                .unwrap();
            assert_eq!(
                checked
                    .execute(
                        &input,
                        reference,
                        ExecutionLimits {
                            max_amplitudes: 2 * expected.len() - 1,
                            ..limits
                        }
                    )
                    .unwrap_err()
                    .code,
                "limit"
            );
            println!(
                "EXECUTION|{name}|{}|{}|{error}",
                expected.len(),
                result.steps
            );
        }
    }
}

// Small classical clients consume actual packed measurement values. Candidate
// validation is essential: a dyadic phase fraction alone is not an order proof.
fn order_candidate(outcome: usize, measured_bits: usize) -> Option<usize> {
    if outcome == 0 {
        return None;
    }
    let denominator = 1usize << measured_bits;
    let (mut a, mut b) = (outcome, denominator);
    while b != 0 {
        (a, b) = (b, a % b);
    }
    let candidate = denominator / a;
    let mut value = 1;
    for _ in 0..candidate {
        value = value * 2 % 3;
    }
    (value == 1).then_some(candidate)
}

// This is a finite-resolution grid estimate, not an unbiased estimate or a
// claim that a fixed two-bit readout recovers the ideal amplitude exactly.
fn amplitude_grid_estimate(outcome: usize, measured_bits: usize) -> f64 {
    (std::f64::consts::PI * outcome as f64 / (1usize << measured_bits) as f64)
        .sin()
        .powi(2)
}

fn sampling_faults(
    checked: &CheckedInstrument,
    input: &[[f64; 2]],
    reference: usize,
    cells: usize,
) {
    let limits = SamplingLimits {
        max_shots: 256,
        execution: ExecutionLimits {
            max_amplitudes: 1 << 16,
            max_steps: 10_000_000,
        },
    };
    let mut draws = 0;
    {
        let mut rng = || {
            draws += 1;
            Ok::<_, ()>(0)
        };
        for bad in [
            vec![[0.0, 0.0]; input.len()],
            vec![[f64::NAN, 0.0]; input.len()],
            vec![[f64::MAX, 0.0]; input.len()],
        ] {
            assert!(
                checked
                    .sample_normalized_shots(&bad, reference, 1, &mut rng, limits)
                    .is_err()
            );
        }
        for changed in [
            SamplingLimits {
                max_shots: 0,
                ..limits
            },
            SamplingLimits {
                execution: ExecutionLimits {
                    max_steps: 0,
                    ..limits.execution
                },
                ..limits
            },
            SamplingLimits {
                execution: ExecutionLimits {
                    max_amplitudes: 0,
                    ..limits.execution
                },
                ..limits
            },
        ] {
            assert!(
                checked
                    .sample_normalized_shots(input, reference, 1, &mut rng, changed)
                    .is_err()
            );
        }
        assert!(
            checked
                .sample_normalized_shots(input, reference, 0, &mut rng, limits)
                .is_err()
        );
        assert!(
            checked
                .sample_normalized_shots(
                    input,
                    reference,
                    usize::MAX,
                    &mut rng,
                    SamplingLimits {
                        max_shots: usize::MAX,
                        ..limits
                    }
                )
                .is_err()
        );
        assert!(
            checked
                .sample_normalized_shots(input, usize::MAX, 1, &mut rng, limits)
                .is_err()
        );
    }
    assert_eq!(draws, 0);
    let mut failing = || Err::<u64, _>("rng unavailable");
    assert!(matches!(
        checked.sample_normalized_shots(input, reference, 1, &mut failing, limits),
        Err(SamplingError::RandomSource("rng unavailable"))
    ));
    let mut deterministic_input = vec![[0.0, 0.0]; input.len()];
    deterministic_input[0] = [2.0, 0.0];
    let mut words = 0;
    let mut deterministic_rng = || {
        words += 1;
        Ok::<_, ()>(u64::MAX)
    };
    let deterministic = checked
        .sample_normalized_shots(
            &deterministic_input,
            reference,
            2,
            &mut deterministic_rng,
            limits,
        )
        .unwrap();
    assert_eq!(words, 2);
    assert!(deterministic.shots.iter().all(|shot| shot.outcome == 0));
    assert_eq!(deterministic.input_norm_squared, 4.0);

    let result = checked
        .sample_normalized_shots(input, reference, 3, &mut SplitMix64::new(42), limits)
        .unwrap();
    let branch_cells = result.shots[0].amplitudes.len();
    let exact = SamplingLimits {
        execution: ExecutionLimits {
            max_steps: result.steps,
            max_amplitudes: input.len() + 2 * branch_cells + 2 * cells,
        },
        ..limits
    };
    let replay = checked
        .sample_normalized_shots(input, reference, 3, &mut SplitMix64::new(42), exact)
        .unwrap();
    assert_eq!(replay.steps, result.steps);
    for (a, b) in result.shots.iter().zip(&replay.shots) {
        assert_eq!(a.outcome, b.outcome);
        compare(&a.amplitudes, &b.amplitudes);
    }
    for execution in [
        ExecutionLimits {
            max_steps: exact.execution.max_steps - 1,
            ..exact.execution
        },
        ExecutionLimits {
            max_amplitudes: exact.execution.max_amplitudes - 1,
            ..exact.execution
        },
    ] {
        let mut draws = 0;
        let mut rng = || {
            draws += 1;
            Ok::<_, ()>(0)
        };
        assert!(
            matches!(checked.sample_normalized_shots(input, reference, 3, &mut rng,
            SamplingLimits { execution, ..exact }), Err(SamplingError::Execution(ref e)) if e.code=="limit")
        );
        assert_eq!(
            draws, 2,
            "third shot must fail before consuming its random word"
        );
    }
    let mut words = [0, u64::MAX].into_iter();
    let mut random = || Ok::<_, ()>(words.next().unwrap());
    let two = checked
        .sample_normalized_shots(input, reference, 2, &mut random, limits)
        .unwrap();
    assert_ne!(
        two.shots[0].outcome, two.shots[1].outcome,
        "fresh input cannot reuse a collapsed branch"
    );
}

#[test]
#[ignore = "run scripts/test_hierarchical_execution.py with the audited Lean kernel"]
fn seeded_fresh_shots_match_independent_branches_and_classical_clients() {
    let directory =
        std::env::var_os("QLEISLI_HIERARCHICAL_EXECUTION").expect("source oracle fixtures");
    let directory = Path::new(&directory);
    let limits = SamplingLimits {
        max_shots: 256,
        execution: ExecutionLimits {
            max_amplitudes: 1 << 16,
            max_steps: 10_000_000,
        },
    };
    for line in std::fs::read_to_string(directory.join("sampling.tsv"))
        .unwrap()
        .lines()
    {
        let fields: Vec<_> = line.split('\t').collect();
        assert_eq!(fields.len(), 7);
        let (name, client) = (fields[0], fields[1]);
        let reference = fields[2].parse().unwrap();
        let output_bits: usize = fields[3].parse().unwrap();
        let measured_bits: usize = fields[4].parse().unwrap();
        let shots = fields[5].parse().unwrap();
        let seed = fields[6].parse().unwrap();
        let checked = kernel()
            .check_instrument(
                &std::fs::read(directory.join(format!("{name}.json"))).unwrap(),
                &std::fs::read(directory.join(format!("{name}.request.json"))).unwrap(),
            )
            .unwrap();
        let input = coefficients(&directory.join(format!("{name}.input")));
        let expected = coefficients(&directory.join(format!("{name}.expected")));
        let branch_cells = (1 << output_bits) * reference;
        let weight = |v: &[[f64; 2]]| v.iter().map(|[re, im]| re * re + im * im).sum::<f64>();
        let input_norm = weight(&input);
        let weights: Vec<_> = expected.chunks_exact(branch_cells).map(weight).collect();
        assert!((weights.iter().sum::<f64>() - input_norm).abs() < 1e-11);
        let result = checked
            .sample_normalized_shots(&input, reference, shots, &mut SplitMix64::new(seed), limits)
            .unwrap();
        assert_eq!(result.input_norm_squared, input_norm);
        assert_eq!(result.measured_bits, measured_bits);
        assert_eq!(result.reference_dimension, reference);
        assert_eq!(result.shots.len(), shots);
        let normalized: Vec<_> = input
            .iter()
            .map(|[re, im]| [re / input_norm.sqrt(), im / input_norm.sqrt()])
            .collect();
        let one = checked
            .execute(&normalized, reference, limits.execution)
            .unwrap();
        assert!(
            result.steps >= shots * one.steps,
            "fresh repeated circuit work must be charged per shot"
        );
        let mut oracle_rng = SplitMix64::new(seed);
        let mut counts = vec![0; 1 << measured_bits];
        let mut candidates = 0;
        let mut estimates = 0.0;
        for sample in &result.shots {
            let u = (oracle_rng.next_u64().unwrap() >> 11) as f64 / (1_u64 << 53) as f64;
            let mut cumulative = 0.0;
            let wanted = weights
                .iter()
                .position(|p| {
                    cumulative += p / input_norm;
                    u < cumulative
                })
                .unwrap();
            assert_eq!(sample.outcome, wanted);
            assert!((sample.probability - weights[wanted] / input_norm).abs() < 1e-11);
            counts[wanted] += 1;
            let state: Vec<_> = expected[wanted * branch_cells..(wanted + 1) * branch_cells]
                .iter()
                .map(|[re, im]| [re / weights[wanted].sqrt(), im / weights[wanted].sqrt()])
                .collect();
            compare(&sample.amplitudes, &state);
            assert!((weight(&sample.amplitudes) - 1.0).abs() < 1e-11);
            if client == "order" {
                if let Some(candidate) = order_candidate(sample.outcome, measured_bits) {
                    assert_eq!(candidate, 2);
                    candidates += 1;
                }
            } else if client == "amplitude" {
                let estimate = amplitude_grid_estimate(sample.outcome, measured_bits);
                assert!((0.0..=1.0).contains(&estimate));
                estimates += estimate;
            } else if sample.outcome != 0 {
                assert!(
                    sample.amplitudes[..3]
                        .iter()
                        .flatten()
                        .all(|x| x.abs() < 1e-11)
                );
                assert!((weight(&sample.amplitudes[3..]) - 1.0).abs() < 1e-11);
            }
        }
        assert!(counts.iter().filter(|n| **n > 0).count() > 1);
        if client == "order" {
            assert!(candidates > 0 && candidates < shots);
        }
        if client == "amplitude" {
            assert!(estimates > 0.0 && estimates < shots as f64);
        }
        if client == "qpe" {
            sampling_faults(&checked, &input, reference, expected.len());
        }
        println!(
            "SAMPLING|{name}|{shots}|{}|{counts:?}|{candidates}|{}",
            result.steps,
            estimates / shots as f64
        );
    }
}
