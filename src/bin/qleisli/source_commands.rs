//! Shared source execution for the text and JSON CLI transports.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use qleisli::frontend::compile::{check_project_with_kernel, compile_project_with_kernel};
use qleisli::frontend::diagnostic::Diagnostic;
use qleisli::frontend::project::{QrateSource, SourcePolicy};
use qleisli::interchange::native::Kernel;
use qleisli::sim::{Sample, SimulationError, SimulationLimits, run_closed};

use super::options::Options;

enum Root {
    Path(PathBuf),
    Qrate(QrateSource),
}

/// One selected input and its loading policy. A qrate retains its directory
/// handle; a diagnostic path can never replace that identity during execution.
/// Selection does not load/check source or grant native acceptance.
pub(super) struct Input {
    root: Root,
    policy: SourcePolicy,
}

impl Input {
    pub fn select(options: &Options) -> Result<Self, Diagnostic> {
        let root = if options.qrate {
            Root::Qrate(QrateSource::select(&options.path)?)
        } else {
            Root::Path(options.path.clone())
        };
        Ok(Self {
            root,
            policy: options.policy,
        })
    }

    /// JSON uses canonical ordinary paths for relative diagnostic labels. Never
    /// re-resolve a qrate selection; its held directory remains authoritative.
    pub fn canonicalize(mut self) -> Self {
        if let Root::Path(path) = &mut self.root {
            if let Ok(canonical) = std::fs::canonicalize(&*path) {
                *path = canonical;
            }
        }
        self
    }

    pub fn path(&self) -> &Path {
        match &self.root {
            Root::Path(path) => path,
            Root::Qrate(selected) => selected.path(),
        }
    }

    fn check(&self, kernel: &Kernel) -> Result<(), Diagnostic> {
        match &self.root {
            Root::Path(path) => check_project_with_kernel(path, self.policy, kernel),
            Root::Qrate(selected) => selected.check_with_kernel(self.policy, kernel),
        }
    }

    pub fn compile(&self, kernel: &Kernel) -> Result<qleisli::AcceptedProgram, Diagnostic> {
        match &self.root {
            Root::Path(path) => compile_project_with_kernel(path, self.policy, kernel),
            Root::Qrate(selected) => selected.compile_with_kernel(self.policy, kernel),
        }
    }
}

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

pub(super) fn execute(options: &Options, input: &Input) -> Result<Success, Failure> {
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
        input.check(&kernel)?;
        return Ok(Success::Checked);
    }
    let program = input.compile(&kernel)?;
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
