//! Bounded host transport; every imported artifact is independently verified.
use std::ffi::OsString;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use qleisli::VerifiedProgram;
use qleisli::frontend::compile::compile_project_with_policy;
use qleisli::frontend::diagnostic::{Diagnostic, SourceLocation};
use qleisli::frontend::project::SourcePolicy;
use qleisli::interchange::{self, Version};
use qleisli::interop::{self, InteropErrorKind};
use qleisli::sim::{SimulationLimits, run_closed};

use super::json::{
    artifact_diagnostic_json, diagnostic_json, distribution_json, envelope, quoted, samples_json,
    simulation_failure,
};
use super::options::natural;

enum Failure {
    Diagnostic(Diagnostic),
    Artifact(interchange::Error),
}

impl From<Diagnostic> for Failure {
    fn from(value: Diagnostic) -> Self {
        Self::Diagnostic(value)
    }
}

fn failure(code: &'static str, message: impl Into<String>) -> Failure {
    Failure::Diagnostic(Diagnostic {
        code,
        message: message.into(),
        primary: None,
    })
}

fn adapter(error: interop::InteropError, source: Option<(&Path, &str)>) -> Failure {
    let primary = source.and_then(|(path, text)| {
        let span = error.span?;
        let prefix = text.get(..span.start)?;
        text.get(span.start..span.end)?;
        let (mut line, mut column, mut previous_cr) = (1, 1, false);
        for ch in prefix.chars() {
            match ch {
                '\r' => {
                    line += 1;
                    column = 1;
                }
                '\n' => {
                    if !previous_cr {
                        line += 1;
                    }
                    column = 1;
                }
                _ => column += 1,
            }
            previous_cr = ch == '\r';
        }
        Some(SourceLocation {
            path: path.into(),
            span,
            line,
            column,
        })
    });
    Failure::Diagnostic(Diagnostic {
        code: match error.kind {
            InteropErrorKind::Parse => "parse",
            InteropErrorKind::Unsupported => "unsupported",
            InteropErrorKind::Limit => "limit",
            InteropErrorKind::InvalidIr => "invalid_ir",
        },
        message: error.to_string(),
        primary,
    })
}

fn artifact(error: interchange::Error) -> Failure {
    Failure::Artifact(error)
}

fn bytes(path: &Path, limit: usize) -> Result<Vec<u8>, Failure> {
    let reader: Box<dyn Read> = if path == Path::new("-") {
        Box::new(std::io::stdin())
    } else {
        Box::new(std::fs::File::open(path).map_err(|e| failure("project", e.to_string()))?)
    };
    let mut data = Vec::new();
    reader
        .take(limit as u64 + 1)
        .read_to_end(&mut data)
        .map_err(|e| failure("project", e.to_string()))?;
    if data.len() > limit {
        return Err(failure("limit", "input byte limit exceeded"));
    }
    Ok(data)
}

fn load(format: &str, path: &Path) -> Result<VerifiedProgram, Failure> {
    match format {
        "qli" if path != Path::new("-") => compile_project_with_policy(
            path,
            SourcePolicy::Bounded {
                source_bytes: 1 << 20,
                project_bytes: 16 << 20,
            },
        )
        .map_err(Failure::Diagnostic),
        "qasm" => {
            let data = bytes(path, interop::MAX_OPENQASM_BYTES)?;
            let text =
                std::str::from_utf8(&data).map_err(|_| failure("parse", "input is not UTF-8"))?;
            interop::import_openqasm3(text).map_err(|e| adapter(e, Some((path, text))))
        }
        "qirf" => Ok(interchange::import(&bytes(path, 16 << 20)?, None)
            .map_err(artifact)?
            .program),
        _ => Err(failure(
            "usage",
            "input must be qasm, qirf, or a qli project directory",
        )),
    }
}

fn execute(args: &[OsString], root: &mut PathBuf) -> Result<String, Failure> {
    let usage = || failure("usage", super::options::USAGE);
    if args.len() < 3 {
        return Err(usage());
    }
    let action = args[0].to_str().ok_or_else(usage)?;
    *root = PathBuf::from(&args[1]);
    let (mut format, mut shots, mut seed, mut json) = (None, None, None, false);
    for arg in &args[2..] {
        match arg.to_str() {
            Some("--format=json") if !json => json = true,
            Some(s) if s.starts_with("--input=") && format.is_none() => format = Some(&s[8..]),
            Some(s) if s.starts_with("--shots=") && shots.is_none() => {
                shots = Some(natural(&s[8..]).ok_or_else(usage)?)
            }
            Some(s) if s.starts_with("--seed=") && seed.is_none() => {
                seed = Some(natural(&s[7..]).ok_or_else(usage)?)
            }
            _ => return Err(usage()),
        }
    }
    if !matches!(
        action,
        "check" | "run" | "sample" | "emit-ir" | "emit-qasm" | "emit-qir"
    ) || if action == "sample" {
        !shots.is_some_and(|n| (1..=1_000_000).contains(&n)) || seed.is_none()
    } else {
        shots.is_some() || seed.is_some()
    } {
        return Err(usage());
    }
    let format = format.ok_or_else(usage)?;
    if matches!(format, "qli" | "qasm") && root != Path::new("-") {
        // Match the source loader's absolute identities for JSON source spans.
        *root = std::fs::canonicalize(&*root).unwrap_or_else(|_| root.clone());
    }
    let program = load(format, root)?;
    let text = match action {
        "check" => return Ok("{\"verified\":true}".into()),
        "run" => {
            return distribution_json(
                run_closed(&program, SimulationLimits::default()).map_err(simulation_failure)?,
            )
            .map_err(Failure::Diagnostic);
        }
        "sample" => {
            let seed = seed.unwrap();
            let (samples, steps) = super::samples::collect(&program, shots.unwrap(), seed)?;
            return Ok(samples_json(&samples, seed, steps, ", "));
        }
        "emit-ir" => {
            String::from_utf8(interchange::export(&program, None, Version::V2).map_err(artifact)?)
                .map_err(|_| failure("format", "export is not UTF-8"))?
        }
        "emit-qasm" => interop::export_openqasm3(&program).map_err(|e| adapter(e, None))?,
        "emit-qir" => interop::export_qir_base(&program).map_err(|e| adapter(e, None))?,
        _ => unreachable!(),
    };
    Ok(format!("{{\"text\":{}}}", quoted(&text)))
}

pub(super) fn run(args: &[OsString]) -> ExitCode {
    let action = args.first().and_then(|s| s.to_str()).unwrap_or("");
    let command = format!("interop {action}");
    let mut root = PathBuf::new();
    let (document, status) = match execute(args, &mut root) {
        Ok(result) => (envelope(&command, None, &result), ExitCode::SUCCESS),
        Err(error) => {
            let (diagnostic, status) = match error {
                Failure::Artifact(error) => (
                    artifact_diagnostic_json(error.code, &error.message, &error.json_pointer),
                    1,
                ),
                Failure::Diagnostic(error) => {
                    let source_root = if error.primary.as_ref().is_some_and(|p| p.path == root) {
                        root.parent().unwrap_or(Path::new(""))
                    } else {
                        &root
                    };
                    (
                        diagnostic_json(source_root, &error),
                        if error.code == "usage" { 2 } else { 1 },
                    )
                }
            };
            (
                envelope(&command, Some(&diagnostic), "null"),
                ExitCode::from(status),
            )
        }
    };
    match std::io::stdout().lock().write_all(document.as_bytes()) {
        Ok(()) => status,
        Err(e) => {
            eprintln!("could not write connection result: {e}");
            ExitCode::FAILURE
        }
    }
}
