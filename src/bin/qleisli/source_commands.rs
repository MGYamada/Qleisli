//! Shared source execution for the text and JSON CLI transports.

use std::collections::BTreeMap;
use std::path::Path;

use qleisli::frontend::compile::{check_project_with_policy, compile_project_with_policy};
use qleisli::frontend::diagnostic::Diagnostic;
use qleisli::interchange::{self, Version, dual::Kernel};
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
    Artifact(interchange::Error),
}

impl From<Diagnostic> for Failure {
    fn from(error: Diagnostic) -> Self {
        Self::Source(error)
    }
}

pub(super) fn execute(options: &Options, root: &Path) -> Result<Success, Failure> {
    if options.command == "check" && options.lean_kernel.is_none() {
        match &options.selected_root {
            Some(selected) => selected.check_with_policy(options.policy)?,
            None => check_project_with_policy(root, options.policy)?,
        }
        return Ok(Success::Checked);
    }
    let program = match &options.selected_root {
        Some(selected) => selected.compile_with_policy(options.policy)?,
        None => compile_project_with_policy(root, options.policy)?,
    };
    let program = if let Some(path) = &options.lean_kernel {
        let bytes = interchange::export(&program, None, Version::V2).map_err(Failure::Artifact)?;
        Kernel::new(path)
            .check(&bytes, None)
            .map_err(Failure::Artifact)?
            .into_program()
    } else {
        program
    };
    if options.command == "check" {
        return Ok(Success::Checked);
    }
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
