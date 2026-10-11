//! Finite instrument checks, independent of the QFT circuit and feedback code.
mod common;

use common::SourceRoot;
use qleisli::frontend::compile::compile_project;
use qleisli::sim::{SimulationLimits, run_closed};
use std::collections::BTreeMap;

type Distribution = BTreeMap<Vec<bool>, f64>;
type Complex = (f64, f64);

fn read(path: &str) -> String {
    common::current_source_text(path)
}

fn project(client: &str, coherent: bool) -> SourceRoot {
    let source = read(&format!(
        "tests/fixtures/frontend_v030/ordinary-type-cutover/current/iterative_qpe/{client}.qli"
    ));
    let root = SourceRoot::new(&if coherent {
        source.replace("use iterative::phase3;", "use estimation::phase3;")
    } else {
        source
    });
    root.write(
        "iterative.qli",
        &read("examples/iterative_phase_estimation/iterative.qli"),
    );
    for name in ["estimation", "gates"] {
        root.write(
            &format!("{name}.qli"),
            &read(&format!("examples/operation_algorithms/{name}.qli")),
        );
    }
    root
}

fn execute(root: &SourceRoot) -> Distribution {
    let program = compile_project(&root.0).unwrap_or_else(|e| panic!("{e}"));
    run_closed(&program, SimulationLimits::default()).unwrap()
}

fn assert_distribution(actual: &Distribution, expected: &Distribution) {
    assert!((actual.values().sum::<f64>() - 1.0).abs() < 1e-12);
    for key in actual.keys().chain(expected.keys()) {
        assert!(
            (actual.get(key).copied().unwrap_or_default()
                - expected.get(key).copied().unwrap_or_default())
            .abs()
                < 1e-12,
            "{key:?}: {actual:?}, expected {expected:?}"
        );
    }
}

#[test]
fn iterative_phase3_recovers_all_eighth_roots_and_both_x_eigenstates() {
    for k in 0..8 {
        let expected = BTreeMap::from([(vec![k & 1 != 0, k & 2 != 0, k & 4 != 0, true], 1.0)]);
        for coherent in [false, true] {
            assert_distribution(
                &execute(&project(&format!("phase_t{k}"), coherent)),
                &expected,
            );
        }
    }
    for (name, bit) in [("plus", false), ("minus", true)] {
        let expected = BTreeMap::from([(vec![false, false, bit, bit], 1.0)]);
        for coherent in [false, true] {
            assert_distribution(
                &execute(&project(&format!("x_{name}"), coherent)),
                &expected,
            );
        }
    }
}

fn add(a: Complex, b: Complex) -> Complex {
    (a.0 + b.0, a.1 + b.1)
}
fn mul(a: Complex, b: Complex) -> Complex {
    (a.0 * b.0 - a.1 * b.1, a.0 * b.1 + a.1 * b.0)
}
fn scale(a: Complex, b: f64) -> Complex {
    (a.0 * b, a.1 * b)
}
fn single(state: &mut [Complex; 4], axis: usize, matrix: [[Complex; 2]; 2]) {
    for i in 0..4 {
        if i & (1 << axis) != 0 {
            continue;
        }
        let j = i | (1 << axis);
        let (a, b) = (state[i], state[j]);
        state[i] = add(mul(matrix[0][0], a), mul(matrix[0][1], b));
        state[j] = add(mul(matrix[1][0], a), mul(matrix[1][1], b));
    }
}

/// Apply the Fourier polynomial directly to half a Bell pair, then measure.
/// No compiled IR, QFT circuit or iterative recurrence supplies this oracle.
fn fourier_instrument(reference_basis: char, target_basis: char) -> Distribution {
    let h = std::f64::consts::FRAC_1_SQRT_2;
    let hadamard = [[(h, 0.0), (h, 0.0)], [(h, 0.0), (-h, 0.0)]];
    let t = (h, h);
    // Matrix of H T in column-vector convention.
    let unitary = [[(h, 0.0), scale(t, h)], [(h, 0.0), scale(t, -h)]];
    let mut result = BTreeMap::new();
    for y in 0..8 {
        let mut power = [(h, 0.0), (0.0, 0.0), (0.0, 0.0), (h, 0.0)];
        let mut branch = [(0.0, 0.0); 4];
        for r in 0..8 {
            let angle = -std::f64::consts::TAU * f64::from(r * y) / 8.0;
            let coefficient = (angle.cos() / 8.0, angle.sin() / 8.0);
            for (out, value) in branch.iter_mut().zip(power) {
                *out = add(*out, mul(coefficient, value));
            }
            single(&mut power, 1, unitary);
        }
        for (axis, basis) in [reference_basis, target_basis].into_iter().enumerate() {
            if basis == 'y' {
                single(
                    &mut branch,
                    axis,
                    [[(1.0, 0.0), (0.0, 0.0)], [(0.0, 0.0), (0.0, -1.0)]],
                );
            }
            if basis != 'z' {
                single(&mut branch, axis, hadamard);
            }
        }
        for (index, (real, imag)) in branch.into_iter().enumerate() {
            result.insert(
                vec![
                    y & 1 != 0,
                    y & 2 != 0,
                    y & 4 != 0,
                    index & 1 != 0,
                    index & 2 != 0,
                ],
                real * real + imag * imag,
            );
        }
    }
    assert!((result.values().sum::<f64>() - 1.0).abs() < 1e-12);
    result
}

#[test]
fn adaptive_and_coherent_qpe_match_independent_off_grid_branch_tomography() {
    for reference in ['x', 'y', 'z'] {
        for target in ['x', 'y', 'z'] {
            let expected = fourier_instrument(reference, target);
            for coherent in [false, true] {
                assert_distribution(
                    &execute(&project(
                        &format!("tilted_bell_{reference}{target}"),
                        coherent,
                    )),
                    &expected,
                );
            }
        }
    }
}

#[test]
fn degenerate_phase_preserves_reference_coherence() {
    for coherent in [false, true] {
        assert_distribution(
            &execute(&project("identity_reference", coherent)),
            &BTreeMap::from([(vec![false; 5], 1.0)]),
        );
    }
}

#[test]
fn semantic_oracles_detect_compiling_feedback_and_weight_faults() {
    let expected = vec![true, false, false, true];
    for fault in ["missing_feedback", "swapped_weights"] {
        let root = project("phase_t1", false);
        root.write(
            "iterative.qli",
            &read(&format!("tests/fixtures/frontend_v030/ordinary-type-cutover/current/iterative_qpe/faults/{fault}.qli")),
        );
        let actual = execute(&root);
        assert!(actual.get(&expected).copied().unwrap_or_default() < 0.75);
    }
}

#[test]
fn explicit_current_derivative_of_first_attempt_and_shipped_example_execute() {
    for directory in [
        "tests/fixtures/frontend_v030/ordinary-type-cutover/current/authoring_sessions/iterative-qpe/attempt-01",
        "examples/iterative_phase_estimation",
    ] {
        // Preserve the first attempt and select its header-only migration.
        let selected = SourceRoot::new(&read(&format!("{directory}/main.qli")));
        selected.write(
            "iterative.qli",
            &read(&format!("{directory}/iterative.qli")),
        );
        let program = compile_project(&selected.0).unwrap();
        let actual = run_closed(&program, SimulationLimits::default()).unwrap();
        assert_distribution(
            &actual,
            &BTreeMap::from([(vec![true, false, false, true], 1.0)]),
        );
    }
}
