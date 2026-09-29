use qleisli::host::{
    MAX_TRIAL_ATTEMPTS, TrialDecision, TrialFailure, TrialRetry, TrialRun, run_trials,
};

#[test]
fn accepted_trials_stop_and_retain_typed_retries() {
    let mut calls = 0;
    let result = run_trials(10, |attempt| {
        calls += 1;
        Ok::<_, ()>(if attempt < 3 {
            TrialDecision::Retry("candidate")
        } else {
            TrialDecision::Accepted(42)
        })
    })
    .unwrap();
    assert_eq!(calls, 3);
    assert_eq!(
        result,
        TrialRun::Accepted {
            value: 42,
            attempts: 3,
            retries: vec![
                TrialRetry {
                    attempt: 1,
                    reason: "candidate"
                },
                TrialRetry {
                    attempt: 2,
                    reason: "candidate"
                }
            ]
        }
    );
    assert_eq!(
        run_trials(2, |_| Ok::<_, ()>(TrialDecision::<_, ()>::Accepted(7))).unwrap(),
        TrialRun::Accepted {
            value: 7,
            attempts: 1,
            retries: vec![]
        }
    );
}

#[test]
fn zero_invalid_and_exhausted_bounds() {
    let never = |_| -> Result<TrialDecision<(), ()>, ()> { panic!("must not invoke callback") };
    assert_eq!(
        run_trials(0, never).unwrap(),
        TrialRun::Exhausted {
            attempts: 0,
            retries: vec![]
        }
    );
    assert_eq!(
        run_trials(MAX_TRIAL_ATTEMPTS + 1, never),
        Err(TrialFailure::InvalidLimit {
            requested: MAX_TRIAL_ATTEMPTS + 1,
            max: MAX_TRIAL_ATTEMPTS
        })
    );
    assert_eq!(
        run_trials(2, |_| Ok::<_, ()>(TrialDecision::<(), _>::Retry(false))).unwrap(),
        TrialRun::Exhausted {
            attempts: 2,
            retries: vec![
                TrialRetry {
                    attempt: 1,
                    reason: false
                },
                TrialRetry {
                    attempt: 2,
                    reason: false
                }
            ]
        }
    );
}

#[test]
fn execution_error_is_never_a_retry() {
    assert_eq!(
        run_trials(10, |n| if n == 1 {
            Ok(TrialDecision::<(), _>::Retry("bad period"))
        } else {
            Err("rng failed")
        }),
        Err(TrialFailure::Execution {
            attempts_started: 2,
            error: "rng failed",
            retries: vec![TrialRetry {
                attempt: 1,
                reason: "bad period"
            }]
        })
    );
}

#[test]
fn phase_trials_validate_periods_factors_and_distinct_retry_reasons() {
    use qleisli::host::{
        FactorPrecheck, FactorRetry, PeriodFactors, factor_precheck, factor_trial_from_phase,
    };
    assert_eq!(
        factor_trial_from_phase(15, 2, 3, 2).unwrap(),
        TrialDecision::Accepted(PeriodFactors {
            period: 4,
            factor: 3,
            cofactor: 5
        })
    );
    assert_eq!(
        factor_trial_from_phase(15, 2, 3, 4).unwrap(),
        TrialDecision::Retry(FactorRetry::InvalidCandidate)
    );
    assert_eq!(
        factor_trial_from_phase(7, 2, 3, 3).unwrap(),
        TrialDecision::Retry(FactorRetry::OddPeriod)
    );
    assert_eq!(
        factor_trial_from_phase(15, 14, 3, 4).unwrap(),
        TrialDecision::Retry(FactorRetry::TrivialFactor)
    );
    assert_eq!(
        factor_precheck(12, 5).unwrap(),
        FactorPrecheck::Factors {
            factor: 2,
            cofactor: 6
        }
    );
    assert_eq!(
        factor_precheck(15, 3).unwrap(),
        FactorPrecheck::Factors {
            factor: 3,
            cofactor: 5
        }
    );
    assert_eq!(
        factor_precheck(15, 2).unwrap(),
        FactorPrecheck::QuantumTrial
    );
    for args in [
        (1, 2, 3, 0),
        (15, 1, 3, 0),
        (15, 3, 3, 0),
        (15, 2, 0, 0),
        (15, 2, 3, 8),
    ] {
        assert!(factor_trial_from_phase(args.0, args.1, args.2, args.3).is_err());
    }
}
