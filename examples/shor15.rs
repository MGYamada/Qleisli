//! Enumerate the ideal finite distribution; this is not a hardware sampler.
use std::error::Error;
use std::path::Path;

use qleisli_core::frontend::compile::compile_project;
use qleisli_core::host::factor_from_phase;
use qleisli_core::sim::{SimulationLimits, run_closed};

fn main() -> Result<(), Box<dyn Error>> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/order_finding");
    let program = compile_project(&root)?;
    let distribution = run_closed(&program, SimulationLimits::default())?;
    let mut success = 0.0;
    let mut retry = 0.0;
    for (bits, probability) in distribution {
        let outcome = bits
            .iter()
            .enumerate()
            .fold(0, |value, (i, bit)| value | (u32::from(*bit) << i));
        match factor_from_phase(15, 2, 3, outcome)? {
            Some(result) => {
                success += probability;
                println!(
                    "y={outcome}/8 p={probability:.12}: r={}, {} * {} = 15",
                    result.period_candidate, result.factor, result.cofactor
                );
            }
            None => {
                retry += probability;
                println!("y={outcome}/8 p={probability:.12}: retry");
            }
        }
    }
    println!("ideal success probability: {success:.12}; retry: {retry:.12}");
    Ok(())
}
