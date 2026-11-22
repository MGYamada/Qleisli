//! Shared source execution for the text and JSON CLI transports.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsString;
use std::path::{Path, PathBuf};

use qleisli::frontend::compile::ProjectCheckReport;
use qleisli::frontend::diagnostic::Diagnostic;
use qleisli::frontend::project::{Project, QrateSource, SourcePolicy};
use qleisli::sim::{
    ExactZeroUnavailable, Sample, SimulationError, SimulationLimits, run_closed,
    terminal_exact_zeros,
};

use super::{artifacts, options::Options};

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

    pub fn load_project(&self) -> Result<Project, Diagnostic> {
        match &self.root {
            Root::Path(path) => Project::load_with_policy(path, self.policy),
            Root::Qrate(selected) => selected.load_with_policy(self.policy),
        }
    }
}

pub(super) enum Success {
    Checked(ProjectCheckReport),
    Artifact(artifacts::Success),
    Documentation(String),
    Distribution {
        probabilities: BTreeMap<Vec<bool>, f64>,
        exact_zeros: Option<Result<BTreeSet<Vec<bool>>, ExactZeroUnavailable>>,
    },
    Samples {
        shots: Vec<Sample>,
        seed: u64,
        execution_steps: u64,
    },
}

pub(super) enum Failure {
    Source(Diagnostic),
    Artifact(qleisli::interchange::Error),
    Simulation(Diagnostic),
}

impl From<Diagnostic> for Failure {
    fn from(error: Diagnostic) -> Self {
        Self::Source(error)
    }
}

fn execute(options: &Options, input: &Input) -> Result<Success, Failure> {
    let project = input.load_project()?;
    let kernel = options
        .kernel(project.edition())
        .map_err(|error| Diagnostic {
            counterexample: error.counterexample,
            boundary: None,
            code: error.code,
            message: error.message,
            primary: None,
        })?;
    if options.command == "check" {
        return Ok(Success::Checked(project.check_report_with_kernel(&kernel)?));
    }
    let program = project.compile_with_kernel(&kernel)?;
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
    let distribution = run_closed(&program, SimulationLimits::default())
        .map_err(|error| Failure::Simulation(simulation_failure(error)))?;
    let exact_zeros = options
        .show_exact_zeros
        .then(|| terminal_exact_zeros(&program));
    Ok(Success::Distribution {
        probabilities: distribution,
        exact_zeros,
    })
}

pub(super) struct Outcome {
    pub(super) root: PathBuf,
    pub(super) command: String,
    pub(super) warnings: Vec<Diagnostic>,
    pub(super) result: Result<Success, Failure>,
}

pub(super) fn dispatch(args: &[OsString], json: bool) -> Outcome {
    let Some(options) = Options::parse(args, json) else {
        let command = args
            .iter()
            .find(|arg| !arg.as_encoded_bytes().starts_with(b"-"))
            .and_then(|arg| arg.to_str())
            .unwrap_or_default()
            .to_owned();
        return Outcome {
            root: PathBuf::new(),
            command,
            warnings: Vec::new(),
            result: Err(Failure::Source(failure("usage", super::options::USAGE))),
        };
    };
    let mut root = options.path.clone();
    let mut warnings = Vec::new();
    let result = (|| {
        let input = Input::select(&options).map_err(|error| {
            if json {
                root = std::fs::canonicalize(&root).unwrap_or_else(|_| root.clone());
            }
            error
        })?;
        if json && root.to_str().is_none() {
            return Err(failure("project", "source root is not valid UTF-8").into());
        }
        let input = if json { input.canonicalize() } else { input };
        root = input.path().to_owned();
        if json && root.to_str().is_none() {
            return Err(failure("project", "source root is not valid UTF-8").into());
        }
        if !matches!(options.command.as_str(), "verify-ir" | "doc") {
            warnings = qleisli::frontend::project::manifest_warnings(&root).unwrap_or_default();
        }
        match options.command.as_str() {
            "emit-ir" | "verify-ir" => artifacts::execute(&options, &input, json)
                .map(Success::Artifact)
                .map_err(|error| match error {
                    artifacts::Failure::Source(error) => Failure::Source(error),
                    artifacts::Failure::Artifact(error) => Failure::Artifact(error),
                }),
            "doc" => {
                let source = qleisli::frontend::project::read_source_file(&root, options.policy)?;
                qleisli::frontend::documentation::render_markdown(&source)
                    .map(Success::Documentation)
                    .map_err(|error| failure("doc", error.to_string()).into())
            }
            _ => execute(&options, &input),
        }
    })();
    Outcome {
        root,
        command: options.command,
        warnings,
        result,
    }
}

pub(super) fn simulation_failure(error: SimulationError) -> Diagnostic {
    let code = match error {
        SimulationError::DimensionLimit { .. }
        | SimulationError::ComponentLimit { .. }
        | SimulationError::AmplitudeLimit { .. }
        | SimulationError::ExecutionLimit { .. } => "limit",
        SimulationError::NotClosed(_) | SimulationError::InconsistentVerifiedIr(_) => "simulation",
    };
    failure(code, error.to_string())
}

pub(super) fn failure(code: &'static str, message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        counterexample: None,
        boundary: None,
        code,
        message: message.into(),
        primary: None,
    }
}
