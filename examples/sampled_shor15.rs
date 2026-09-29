//! Fresh finite QPE trials, distinct from the exhaustive shor15 example.
use qleisli::frontend::compile::compile_project;
use qleisli::host::{factor_trial_from_phase, run_trials};
use qleisli::sim::{SampleLimits, SplitMix64, sample_closed};
use std::path::Path;

fn main() -> Result<(), String> {
    let program =
        compile_project(&Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/order_finding"))
            .map_err(|e| e.to_string())?;
    let mut random = SplitMix64::new(0);
    let result = run_trials(16, |_| {
        let shot = sample_closed(&program, &mut random, SampleLimits::default())
            .map_err(|e| e.to_string())?;
        let y = shot
            .bits
            .iter()
            .enumerate()
            .fold(0, |v, (k, b)| v | (u32::from(*b) << k));
        factor_trial_from_phase(15, 2, 3, y).map_err(|e| e.to_string())
    })
    .map_err(|e| format!("{e:?}"))?;
    println!("{result:?}");
    Ok(())
}
