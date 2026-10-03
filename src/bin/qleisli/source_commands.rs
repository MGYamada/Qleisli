//! Shared source execution for the text and JSON CLI transports.

use std::collections::BTreeMap;
use std::path::Path;

use qleisli::frontend::compile::{check_project_with_kernel, compile_project_with_kernel};
use qleisli::frontend::diagnostic::Diagnostic;
use qleisli::interchange::native::Kernel;
use qleisli::sim::{Sample, SimulationError, SimulationLimits, run_closed};

use super::options::Options;

pub(super) enum Success {
    Checked,
    Distribution(BTreeMap<Vec<bool>, f64>),
    Samples {
        shots: Vec<Sample>,
        seed: u64,
        execution_steps: u64,
    },
}

pub(super) enum Failure {
    Source(Diagnostic),
    Simulation(SimulationError),
}

impl From<Diagnostic> for Failure {
    fn from(error: Diagnostic) -> Self {
        Self::Source(error)
    }
}

pub(super) fn execute(options: &Options, root: &Path) -> Result<Success, Failure> {
    let kernel = options
        .lean_kernel
        .as_ref()
        .map(Kernel::new)
        .map(Ok)
        .unwrap_or_else(Kernel::selected)
        .map_err(|error| Diagnostic {
            code: error.code,
            message: error.message,
            primary: None,
        })?;
    if options.command == "check" {
        match &options.selected_root {
            Some(selected) => selected.check_with_kernel(options.policy, &kernel)?,
            None => check_project_with_kernel(root, options.policy, &kernel)?,
        }
        return Ok(Success::Checked);
    }
    let program = match &options.selected_root {
        Some(selected) => selected.compile_with_kernel(options.policy, &kernel)?,
        None => compile_project_with_kernel(root, options.policy, &kernel)?,
    };
    if options.command == "sample" {
        let seed = options.seed.expect("parsed sample seed");
        let (shots, execution_steps) =
            super::samples::collect(&program, options.shots.expect("parsed shots"), seed)?;
        return Ok(Success::Samples {
            shots,
            seed,
            execution_steps,
        });
    }
    let distribution =
        run_closed(&program, SimulationLimits::default()).map_err(Failure::Simulation)?;
    Ok(Success::Distribution(distribution))
}
