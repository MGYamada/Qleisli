use qleisli_core::VerifiedProgram;
use qleisli_core::frontend::diagnostic::Diagnostic;
use qleisli_core::sim::{Sample, SampleError, SampleLimits, SplitMix64, sample_closed};

pub(super) fn collect(
    program: &VerifiedProgram,
    shots: u64,
    seed: u64,
) -> Result<(Vec<Sample>, u64), Diagnostic> {
    collect_with_budget(program, shots, seed, 10_000_000)
}

fn collect_with_budget(
    program: &VerifiedProgram,
    shots: u64,
    seed: u64,
    max_steps: u64,
) -> Result<(Vec<Sample>, u64), Diagnostic> {
    let mut random = SplitMix64::new(seed);
    let mut result = Vec::new();
    let mut total = 0;
    for _ in 0..shots {
        let limits = SampleLimits {
            max_execution_steps: (max_steps - total).min(1_000_000) as usize,
            ..SampleLimits::default()
        };
        let sample = sample_closed(program, &mut random, limits).map_err(|e| Diagnostic {
            code: match &e {
                SampleError::Limit(_) => "limit",
                SampleError::RandomSource(_) => "random_source",
                SampleError::Numerical(_) => "numerical",
                _ => "simulation",
            },
            message: e.to_string(),
            primary: None,
        })?;
        total += sample.execution_steps;
        result.push(sample);
    }
    Ok((result, total))
}

#[cfg(test)]
mod tests {
    use super::*;
    use qleisli_core::{ir::*, verify};
    #[test]
    fn aggregate_failure_does_not_return_earlier_shots() {
        let p = verify(RawProgram {
            quantum_inputs: vec![],
            classical_inputs: vec![],
            operations: vec![RawOp::ClassicalConst {
                value: true,
                output: ClassicalId(0),
            }],
            quantum_outputs: vec![],
            classical_outputs: vec![ClassicalId(0)],
            declared_effect: Effect::Observe,
        })
        .unwrap();
        assert_eq!(collect_with_budget(&p, 2, 0, 2).unwrap().1, 2);
        assert_eq!(collect_with_budget(&p, 3, 0, 2).unwrap_err().code, "limit");
    }
}
