mod common;

use common::SourceRoot;
use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::sim::{RandomSource, SampleError, SampleLimits, SplitMix64, sample_closed};
use std::path::Path;

#[test]
fn splitmix_words_are_the_specified_unsigned_algorithm() {
    let mut rng = SplitMix64::new(0);
    for word in [
        0xe220a8397b1dcdaf,
        0x6e789e6aa1b965f4,
        0x06c45d188009454f,
        0xf88bb8a8724c81ec,
    ] {
        assert_eq!(rng.next_u64().unwrap(), word);
    }
}

#[test]
fn bell_draws_follow_the_word_threshold_and_consume_deterministic_words() {
    let p = compile_project(Path::new("examples/bell")).unwrap();
    for (word, expected) in [(0, false), (u64::MAX, true)] {
        let mut words = 0;
        let mut rng = || {
            words += 1;
            Ok::<_, ()>(word)
        };
        let sample = sample_closed(&p, &mut rng, SampleLimits::default()).unwrap();
        assert_eq!(sample.bits, vec![expected, expected]);
        assert_eq!(words, 2);
        assert!(sample.execution_steps > 0);
    }
}

#[test]
fn stochastic_samples_match_independent_bell_and_reset_feedback_contracts() {
    let source = SourceRoot::new(
        "use std::quantum::init0; use std::quantum::h; use std::quantum::cnot; use std::quantum::x; use std::observe::measure_z; use std::observe::reset; observe fn main() -> (CBit,CBit) { let (a,b) = cnot(h(init0()),init0()); let a = reset(a); let flag = measure_z(b); let a = if flag { x(a) } else { a }; (flag,measure_z(a)) }",
    );
    for p in [
        compile_project(Path::new("examples/bell")).unwrap(),
        compile_project(&source.0).unwrap(),
    ] {
        let mut rng = SplitMix64::new(42);
        let mut ones = 0;
        for _ in 0..4096 {
            let sample = sample_closed(&p, &mut rng, SampleLimits::default()).unwrap();
            assert_eq!(sample.bits[0], sample.bits[1]);
            ones += usize::from(sample.bits[0]);
        }
        // Bernoulli(1/2): Hoeffding gives 2 exp(-2*4096*.06^2) < 3.2e-13.
        assert!((ones as f64 / 4096.0 - 0.5).abs() < 0.06);
    }
}

#[test]
fn discarded_entangled_half_is_sampled_and_no_state_is_reused() {
    let source = SourceRoot::new(
        "use std::quantum::init0; use std::quantum::h; use std::quantum::cnot; use std::observe::measure_z; use std::observe::discard; observe fn main() -> CBit { let (a,b)=cnot(h(init0()),init0()); discard(a); measure_z(b) }",
    );
    let p = compile_project(&source.0).unwrap();
    let mut draws = 0;
    let mut random = || {
        draws += 1;
        Ok::<_, ()>(if draws <= 2 { 0 } else { u64::MAX })
    };
    assert_eq!(
        sample_closed(&p, &mut random, SampleLimits::default())
            .unwrap()
            .bits,
        vec![false]
    );
    assert_eq!(
        sample_closed(&p, &mut random, SampleLimits::default())
            .unwrap()
            .bits,
        vec![true]
    );
    assert_eq!(draws, 4);
}

#[test]
fn failures_are_errors_and_limits_apply_before_draws() {
    let p = compile_project(Path::new("examples/bell")).unwrap();
    let mut random = || Err::<u64, _>("rng unavailable");
    assert_eq!(
        sample_closed(&p, &mut random, SampleLimits::default()),
        Err(SampleError::RandomSource("rng unavailable"))
    );
    let mut words = 0;
    let mut rng = || {
        words += 1;
        Ok::<_, ()>(0)
    };
    assert!(matches!(
        sample_closed(
            &p,
            &mut rng,
            SampleLimits {
                max_execution_steps: 0,
                ..SampleLimits::default()
            }
        ),
        Err(SampleError::Limit(_))
    ));
    assert!(matches!(
        sample_closed(
            &p,
            &mut rng,
            SampleLimits {
                max_amplitude_cells: 0,
                ..SampleLimits::default()
            }
        ),
        Err(SampleError::Limit(_))
    ));
    assert!(matches!(
        sample_closed(
            &p,
            &mut rng,
            SampleLimits {
                max_qubits: 1,
                ..SampleLimits::default()
            }
        ),
        Err(SampleError::Limit(_))
    ));
    assert_eq!(words, 0);
}

#[test]
fn projection_copy_limits_precede_visible_and_hidden_random_draws() {
    use qleisli::ir::{ClassicalId, Effect, RawOp, RawProgram, TokenId, WireId};
    use qleisli::sim::SimulationError;
    let measure = |input| RawOp::MeasureZ {
        input: TokenId(input),
        output: ClassicalId(0),
    };
    for (tail, outputs, insufficient, sufficient, expected_draws) in [
        (vec![measure(0)], vec![ClassicalId(0)], 2, 3, 1),
        (
            vec![
                RawOp::Reset {
                    input: TokenId(0),
                    output: TokenId(1),
                    fresh_wire: WireId(1),
                },
                measure(1),
            ],
            vec![ClassicalId(0)],
            3,
            6,
            2,
        ),
        (vec![RawOp::Discard { input: TokenId(0) }], vec![], 3, 4, 1),
    ] {
        let mut operations = vec![RawOp::Init0 {
            output: TokenId(0),
            wire: WireId(0),
        }];
        operations.extend(tail);
        let program = common::accept(RawProgram {
            quantum_inputs: vec![],
            classical_inputs: vec![],
            operations,
            quantum_outputs: vec![],
            classical_outputs: outputs,
            declared_effect: Effect::Observe,
        })
        .unwrap();
        let mut draws = 0;
        let mut failing_rng = || {
            draws += 1;
            Err::<u64, _>("rng unavailable")
        };
        assert_eq!(
            sample_closed(
                &program,
                &mut failing_rng,
                SampleLimits {
                    max_execution_steps: insufficient,
                    ..SampleLimits::default()
                }
            ),
            Err(SampleError::Limit(SimulationError::ExecutionLimit {
                max: insufficient
            }))
        );
        assert_eq!(draws, 0);
        let mut rng = || {
            draws += 1;
            Ok::<_, ()>(0)
        };
        let sample = sample_closed(
            &program,
            &mut rng,
            SampleLimits {
                max_execution_steps: sufficient,
                ..SampleLimits::default()
            },
        )
        .unwrap();
        assert_eq!(sample.execution_steps, sufficient as u64);
        assert_eq!(draws, expected_draws);
        assert!(sample.bits.iter().all(|bit| !bit));
    }
}

#[test]
fn preserved_grover_trial_has_an_explicit_current_predicate_translation() {
    let original = check_project(Path::new(
        "tests/fixtures/authoring_sessions/grover-trial-v020/attempt-02",
    ))
    .unwrap_err();
    assert_eq!(original.code, ErrorCode::Arity);
    assert!(
        original
            .message
            .contains("exactly one explicit basis parameter")
    );
    let p = compile_project(Path::new(
        "tests/fixtures/frontend_v030/predicate-domain/current/grover-trial-v020",
    ))
    .unwrap();
    let mut rng = SplitMix64::new(0);
    for _ in 0..20 {
        assert_eq!(
            sample_closed(&p, &mut rng, SampleLimits::default())
                .unwrap()
                .bits,
            vec![true, true]
        );
    }
}

#[test]
fn interference_probability_matches_an_independent_analytic_value() {
    let root = SourceRoot::new(
        "use std::quantum::init0; use std::quantum::h; use std::quantum::t; use std::observe::measure_z; observe fn main() -> CBit { measure_z(h(t(h(init0())))) }",
    );
    let p = compile_project(&root.0).unwrap();
    let mut rng = SplitMix64::new(17);
    let mut zero = 0;
    for _ in 0..8192 {
        zero += usize::from(
            !sample_closed(&p, &mut rng, SampleLimits::default())
                .unwrap()
                .bits[0],
        );
    }
    // H T H on |0>: p0 = (2 + sqrt(2))/4. Hoeffding for epsilon .04
    // at 8192 independent draws gives failure probability < 8.4e-12.
    assert!((zero as f64 / 8192.0 - (2.0 + 2.0_f64.sqrt()) / 4.0).abs() < 0.04);
}

#[test]
fn sampler_rejects_open_interfaces_before_requesting_randomness() {
    use common::accept;
    use qleisli::ir::*;
    let p = accept(RawProgram {
        quantum_inputs: vec![QuantumPort {
            token: TokenId(0),
            wires: vec![],
            shape: BasisShape::UNIT,
        }],
        classical_inputs: vec![],
        operations: vec![],
        quantum_outputs: vec![TokenId(0)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    })
    .unwrap();
    let mut rng = || -> Result<u64, ()> { panic!("open program must not draw") };
    assert!(matches!(
        sample_closed(&p, &mut rng, SampleLimits::default()),
        Err(SampleError::NotClosed(_))
    ));
}
