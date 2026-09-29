//! Version-1 CLI result transport, outside the IR/evidence acceptance boundary.

use std::ffi::OsString;
use std::fmt::Write as _;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use qleisli::frontend::compile::{check_project_with_policy, compile_project_with_policy};
use qleisli::frontend::diagnostic::{Diagnostic, SourceLocation};
use qleisli::sim::{SimulationError, SimulationLimits, run_closed};

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
    slash_path(path.strip_prefix(root).ok()?)
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
        "{{\"code\":{},\"severity\":\"error\",\"message\":{},\"primary\":{},\"related\":[]}}",
        quoted(code),
        quoted(&diagnostic.message),
        primary.as_deref().unwrap_or("null")
    )
}

fn failure(code: &'static str, message: impl Into<String>) -> Diagnostic {
    Diagnostic {
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

fn execute(options: &super::options::Options, root: &Path) -> Result<String, Diagnostic> {
    if root.to_str().is_none() {
        return Err(failure("project", "source root is not valid UTF-8"));
    }
    if options.command == "check" {
        check_project_with_policy(root, options.policy)?;
        Ok("{\"verified\":true}".into())
    } else {
        let program = compile_project_with_policy(root, options.policy)?;
        if options.command == "sample" {
            let seed = options.seed.expect("parsed sample seed");
            let (samples, total) =
                super::samples::collect(&program, options.shots.expect("parsed shots"), seed)?;
            let mut result = format!("{{\"rng\":\"splitmix64-v1\",\"seed\":\"{seed}\",\"shots\":[");
            for (index, sample) in samples.iter().enumerate() {
                if index > 0 {
                    result.push(',');
                }
                result.push_str("{\"bits\":[");
                for (i, bit) in sample.bits.iter().enumerate() {
                    if i > 0 {
                        result.push(',');
                    }
                    result.push_str(if *bit { "true" } else { "false" });
                }
                write!(result, "],\"execution_steps\":{}}}", sample.execution_steps).unwrap();
            }
            write!(result, "],\"execution_steps\":{total}}}").unwrap();
            return Ok(result);
        }
        let distribution =
            run_closed(&program, SimulationLimits::default()).map_err(simulation_failure)?;
        distribution_json(distribution)
    }
}

pub(super) fn run(args: &[OsString]) -> ExitCode {
    let positional: Vec<_> = args.iter().filter(|arg| *arg != "--format=json").collect();
    let command = positional
        .first()
        .and_then(|arg| arg.to_str())
        .unwrap_or("");
    let options = super::options::Options::parse(args, true);
    let mut root = PathBuf::new();
    let mut artifact_pointer = None;
    let result = if let Some(options) = options {
        root = options.path.clone();
        if root.to_str().is_none() {
            Err(failure("project", "source root is not valid UTF-8"))
        } else if matches!(options.command.as_str(), "emit-ir" | "verify-ir") {
            // Keep source spans from emission separate from artifact pointers.
            root = std::fs::canonicalize(&root).unwrap_or(root);
            match super::artifacts::execute(&options) {
                Ok(super::artifacts::Success::Emitted(path)) => {
                    Ok(format!("{{\"path\":{}}}", quoted(&path)))
                }
                Ok(super::artifacts::Success::Verified(request)) => Ok(format!(
                    "{{\"verified\":true,\"request_checked\":{request}}}"
                )),
                Err(super::artifacts::Failure::Source(error)) => Err(error),
                Err(super::artifacts::Failure::Artifact(error)) => {
                    artifact_pointer = Some(error.json_pointer);
                    Err(failure(error.code, error.message))
                }
            }
        } else {
            // Use the same canonical root for compilation and relative identities.
            // Failed canonicalization remains a handled project-load error.
            root = std::fs::canonicalize(&root).unwrap_or(root);
            execute(&options, &root)
        }
    } else {
        Err(failure("usage", super::options::USAGE))
    };
    let (document, status) = match result {
        Ok(result) => (envelope(command, None, &result), ExitCode::SUCCESS),
        Err(error) => {
            let status = if error.code == "usage" { 2 } else { 1 };
            let diagnostic = match artifact_pointer {
                None => diagnostic_json(&root, &error),
                Some(pointer) => format!(
                    "{{\"code\":{},\"severity\":\"error\",\"message\":{},\"primary\":null,\"related\":[{{\"message\":{},\"location\":null}}]}}",
                    quoted(error.code),
                    quoted(&error.message),
                    quoted(&format!("json_pointer: {pointer}"))
                ),
            };
            (
                envelope(command, Some(&diagnostic), "null"),
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
