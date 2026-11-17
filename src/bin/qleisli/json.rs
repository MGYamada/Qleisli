//! Version-1 CLI result transport, outside the IR/evidence acceptance boundary.

use std::ffi::OsString;
use std::fmt::Write as _;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use qleisli::frontend::diagnostic::{
    Diagnostic, DiagnosticBoundary, QuantumOwnershipBoundary, SourceLocation,
};
use qleisli::sim::{Sample, SimulationError};

use super::source_commands::{Failure, Success};

pub(super) fn quoted(text: &str) -> String {
    let mut output = String::from("\"");
    for ch in text.chars() {
        match ch {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\u{0}'..='\u{1f}' => write!(output, "\\u{:04x}", ch as u32).unwrap(),
            _ => output.push(ch),
        }
    }
    output.push('"');
    output
}

pub(super) fn envelope(command: &str, diagnostic: Option<&str>, result: &str) -> String {
    format!(
        "{{\"format\":\"qleisli.result\",\"version\":1,\"command\":{},\"outcome\":{},\"diagnostics\":[{}],\"result\":{result}}}\n",
        quoted(command),
        quoted(if diagnostic.is_some() { "error" } else { "ok" }),
        diagnostic.unwrap_or("")
    )
}

fn path_label(root: &Path, path: &Path) -> Option<String> {
    // Check the entire identity before removing prefixes; never lossy-encode it.
    path.to_str()?;
    if let Ok(relative) = path.strip_prefix("<bundled>/std") {
        return Some(format!("std://{}", slash_path(relative)?));
    }
    if let Ok(relative) = path.strip_prefix(root) {
        return if relative.as_os_str().is_empty() {
            Some(".".into())
        } else {
            slash_path(relative)
        };
    }
    // A selected source root may be below its owning qrate manifest. Only
    // that ancestor filename can escape the source root, without host labels.
    if path.file_name()? == "Qargo.toml" {
        let relative = root.strip_prefix(path.parent()?).ok()?;
        return Some(format!(
            "{}Qargo.toml",
            "../".repeat(relative.components().count())
        ));
    }
    None
}

fn slash_path(path: &Path) -> Option<String> {
    path.components()
        .map(|component| component.as_os_str().to_str())
        .collect::<Option<Vec<_>>>()
        .map(|parts| parts.join("/"))
}

fn location_json(root: &Path, location: &SourceLocation) -> Option<String> {
    Some(format!(
        "{{\"path\":{},\"start\":{},\"end\":{},\"line\":{},\"column\":{}}}",
        quoted(&path_label(root, &location.path)?),
        location.span.start,
        location.span.end,
        location.line,
        location.column
    ))
}

pub(super) fn diagnostic_json(root: &Path, diagnostic: &Diagnostic) -> String {
    located_diagnostic_json(root, diagnostic, "error")
}

// Native setup/transport errors are host configuration failures in the closed
// v1 CLI vocabulary. Internal library codes do not extend that wire contract.
fn v1_code(code: &str) -> &str {
    match code {
        "io" | "kernel" => "project",
        _ => code,
    }
}

fn counterexample_json(
    counterexample: Option<&qleisli::contract::EquationCounterexample>,
) -> String {
    counterexample.map_or_else(String::new, |counterexample| {
        format!(
            ",\"counterexample\":{{\"input_column\":{},\"output_row\":{}}}",
            counterexample.input_column, counterexample.output_row,
        )
    })
}

pub(super) fn boundary_json(boundary: Option<DiagnosticBoundary>) -> String {
    match boundary {
        Some(DiagnosticBoundary::QuantumOwnership(ownership)) => {
            let applies_to = if ownership == QuantumOwnershipBoundary::UnresolvedDisposal {
                "if_live_quantum_owner"
            } else {
                "live_quantum_owner"
            };
            format!(
                ",\"ownership_boundary\":{{\"boundary\":\"affine_to_linear\",\"reason\":{},\"applies_to\":{}}}",
                quoted(ownership.reason()),
                quoted(applies_to),
            )
        }
        Some(DiagnosticBoundary::ControlFlow(control)) => format!(
            ",\"control_flow_boundary\":{{\"boundary\":\"classical_quantum_control\",\"reason\":{}}}",
            quoted(control.reason()),
        ),
        None => String::new(),
    }
}

fn located_diagnostic_json(root: &Path, diagnostic: &Diagnostic, severity: &str) -> String {
    let primary = diagnostic
        .primary
        .as_ref()
        .and_then(|p| location_json(root, p));
    let code = if diagnostic.primary.is_some() && primary.is_none() {
        "project"
    } else {
        diagnostic.code
    };
    format!(
        "{{\"code\":{},\"severity\":{},\"message\":{},\"primary\":{},\"related\":[]{}{}}}",
        quoted(v1_code(code)),
        quoted(severity),
        quoted(&diagnostic.message),
        primary.as_deref().unwrap_or("null"),
        counterexample_json(diagnostic.counterexample.as_deref()),
        boundary_json(diagnostic.boundary),
    )
}

fn artifact_diagnostic_with_counterexample_json(
    code: &str,
    message: &str,
    pointer: &str,
    counterexample: Option<&qleisli::contract::EquationCounterexample>,
) -> String {
    format!(
        "{{\"code\":{},\"severity\":\"error\",\"message\":{},\"primary\":null,\"related\":[{{\"message\":{},\"location\":null}}]{}}}",
        quoted(v1_code(code)),
        quoted(message),
        quoted(&format!("json_pointer: {pointer}")),
        counterexample_json(counterexample),
    )
}

pub(super) fn artifact_diagnostic_json(code: &str, message: &str, pointer: &str) -> String {
    artifact_diagnostic_with_counterexample_json(code, message, pointer, None)
}

pub(super) fn artifact_error_json(error: &qleisli::interchange::Error) -> String {
    artifact_diagnostic_with_counterexample_json(
        error.code,
        &error.message,
        &error.json_pointer,
        error.counterexample.as_deref(),
    )
}

fn failure(code: &'static str, message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        counterexample: None,
        boundary: None,
        code,
        message: message.into(),
        primary: None,
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

pub(super) fn distribution_json(
    distribution: std::collections::BTreeMap<Vec<bool>, f64>,
) -> Result<String, Diagnostic> {
    let mut output = String::from("{\"distribution\":[");
    for (index, (bits, probability)) in distribution.into_iter().enumerate() {
        // Transport finite reference output without silently normalizing a broken
        // distribution. Only endpoint roundoff within the specified 2^-40 is clamped.
        const TOLERANCE: f64 = 1.0 / ((1_u64 << 40) as f64);
        if !probability.is_finite() || !(-TOLERANCE..=1.0 + TOLERANCE).contains(&probability) {
            return Err(failure(
                "numerical",
                "reference probability is not finite and within [0,1]",
            ));
        }
        let probability = probability.clamp(0.0, 1.0);
        if index != 0 {
            output.push(',');
        }
        output.push_str("{\"bits\":[");
        for (index, bit) in bits.into_iter().enumerate() {
            if index != 0 {
                output.push(',');
            }
            output.push_str(if bit { "true" } else { "false" });
        }
        write!(output, "],\"probability\":{probability}}}").unwrap();
    }
    output.push_str("]}");
    Ok(output)
}

/// Keep each transport's existing whitespace as well as its sample fields.
pub(super) fn samples_json(
    samples: &[Sample],
    seed: u64,
    total: u64,
    bit_separator: &str,
) -> String {
    let mut result = format!("{{\"rng\":\"splitmix64-v1\",\"seed\":\"{seed}\",\"shots\":[");
    for (index, sample) in samples.iter().enumerate() {
        if index > 0 {
            result.push(',');
        }
        result.push_str("{\"bits\":[");
        for (i, bit) in sample.bits.iter().enumerate() {
            if i > 0 {
                result.push_str(bit_separator);
            }
            result.push_str(if *bit { "true" } else { "false" });
        }
        write!(result, "],\"execution_steps\":{}}}", sample.execution_steps).unwrap();
    }
    write!(result, "],\"execution_steps\":{total}}}").unwrap();
    result
}

fn execute(
    options: &super::options::Options,
    input: &super::source_commands::Input,
) -> Result<String, Diagnostic> {
    match super::source_commands::execute(options, input).map_err(|error| match error {
        Failure::Source(error) => error,
        Failure::Simulation(error) => simulation_failure(error),
    })? {
        Success::Checked(report) => super::check_report::project_json(&report),
        Success::Distribution { probabilities, .. } => distribution_json(probabilities),
        Success::Samples {
            shots,
            seed,
            execution_steps,
        } => Ok(samples_json(&shots, seed, execution_steps, ",")),
    }
}

pub(super) fn run(args: &[OsString]) -> ExitCode {
    let options = super::options::Options::parse(args, true);
    let command = options.as_ref().map_or_else(
        || {
            args.iter()
                .find(|arg| !arg.as_encoded_bytes().starts_with(b"-"))
                .and_then(|arg| arg.to_str())
                .unwrap_or("")
                .to_owned()
        },
        |options| options.command.clone(),
    );
    let mut root = PathBuf::new();
    let mut artifact_pointer = None;
    let mut warnings = vec![];
    let result = if let Some(options) = options {
        root = options.path.clone();
        let selected = super::source_commands::Input::select(&options);
        if let Err(error) = selected {
            root = std::fs::canonicalize(&root).unwrap_or(root);
            Err(error)
        } else if root.to_str().is_none() {
            Err(failure("project", "source root is not valid UTF-8"))
        } else {
            let input = selected.expect("checked root selection").canonicalize();
            root = input.path().to_owned();
            if root.to_str().is_none() {
                Err(failure("project", "source root is not valid UTF-8"))
            } else {
                if options.command != "verify-ir" {
                    warnings =
                        qleisli::frontend::project::manifest_warnings(&root).unwrap_or_default();
                }
                if matches!(options.command.as_str(), "emit-ir" | "verify-ir") {
                    // Keep source spans from emission separate from artifact pointers.
                    match super::artifacts::execute(&options, &input, true) {
                        Ok(super::artifacts::Success::Emitted(path, report)) => {
                            report.json(Some(&path))
                        }
                        Ok(super::artifacts::Success::Checked(report)) => report.json(None),
                        Err(super::artifacts::Failure::Source(error)) => Err(error),
                        Err(super::artifacts::Failure::Artifact(error)) => {
                            artifact_pointer = Some(error.json_pointer);
                            let mut diagnostic = failure(error.code, error.message);
                            diagnostic.counterexample = error.counterexample;
                            Err(diagnostic)
                        }
                    }
                } else {
                    // The final canonical root also supplies relative identities.
                    // Failed canonicalization remains a handled project-load error.
                    execute(&options, &input)
                }
            }
        }
    } else {
        Err(failure("usage", super::options::USAGE))
    };
    let (document, status) = match result {
        Ok(result) => {
            let warnings = warnings
                .iter()
                .map(|warning| located_diagnostic_json(&root, warning, "warning"))
                .collect::<Vec<_>>()
                .join(",");
            let document = format!(
                "{{\"format\":\"qleisli.result\",\"version\":1,\"command\":{},\"outcome\":\"ok\",\"diagnostics\":[{warnings}],\"result\":{result}}}\n",
                quoted(&command)
            );
            (document, ExitCode::SUCCESS)
        }
        Err(error) => {
            let status = if error.code == "usage" { 2 } else { 1 };
            let diagnostic = match artifact_pointer {
                None => diagnostic_json(&root, &error),
                Some(pointer) => artifact_diagnostic_with_counterexample_json(
                    error.code,
                    &error.message,
                    &pointer,
                    error.counterexample.as_deref(),
                ),
            };
            (
                envelope(&command, Some(&diagnostic), "null"),
                ExitCode::from(status),
            )
        }
    };
    match std::io::stdout().lock().write_all(document.as_bytes()) {
        Ok(()) => status,
        Err(error) => {
            eprintln!("could not write JSON result: {error}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use qleisli::frontend::ast::Span;

    #[test]
    fn json_escaping_covers_controls_quotes_backslashes_and_unicode() {
        assert_eq!(
            quoted("\"\\\n\r\t\0日本語🦀"),
            "\"\\\"\\\\\\u000a\\u000d\\u0009\\u0000日本語🦀\""
        );
        for byte in 0..32 {
            assert_eq!(
                quoted(&char::from(byte).to_string()),
                format!("\"\\u{byte:04x}\"")
            );
        }
    }

    #[test]
    fn bundled_and_local_locations_have_portable_identities() {
        let mut location = SourceLocation {
            path: PathBuf::from("<bundled>/std/basis.qli"),
            span: Span { start: 3, end: 5 },
            line: 2,
            column: 1,
        };
        assert_eq!(
            location_json(Path::new("/project"), &location).unwrap(),
            "{\"path\":\"std://basis.qli\",\"start\":3,\"end\":5,\"line\":2,\"column\":1}"
        );
        location.path = PathBuf::from("/project/nested/code.qli");
        assert_eq!(
            path_label(Path::new("/project"), &location.path).unwrap(),
            "nested/code.qli"
        );
    }

    #[test]
    fn invalid_probabilities_fail_before_a_success_document_is_written() {
        for probability in [f64::NAN, f64::INFINITY, -0.01, 1.01] {
            let error = distribution_json([(vec![], probability)].into()).unwrap_err();
            assert_eq!(error.code, "numerical");
            assert!(error.primary.is_none());
        }
        assert_eq!(
            distribution_json([(vec![], 1.0 + f64::EPSILON)].into()).unwrap(),
            "{\"distribution\":[{\"bits\":[],\"probability\":1}]}"
        );
    }
}
