//! Explicit engineering comparisons, separate from source/realization acceptance.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use std::ffi::OsString;
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use qleisli::interchange::Error;
use qleisli::interchange::engineering_pure::{EngineeringPureReport, check_serialized_with_kernel};
use qleisli::interchange::native::Kernel;

use super::json::{artifact_diagnostic_json, envelope, quoted};

const USAGE: &str = "qleisli engineering compare-pure ACTUAL --against=REQUEST [--lean-kernel=PATH] [--format=json]";

pub(super) struct Options {
    pub(super) actual: PathBuf,
    pub(super) request: PathBuf,
    pub(super) checker: Option<PathBuf>,
}

pub(super) fn parse(args: &[OsString], command: &str) -> Option<Options> {
    let mut positional = Vec::new();
    let (mut request, mut checker, mut json) = (None, None, false);
    for arg in args {
        match arg.to_str() {
            Some("--format=json") if !json => json = true,
            Some(text)
                if text.starts_with("--against=") && text.len() > 10 && request.is_none() =>
            {
                request = Some(PathBuf::from(&text[10..]));
            }
            Some(text)
                if text.starts_with("--lean-kernel=") && text.len() > 14 && checker.is_none() =>
            {
                checker = Some(PathBuf::from(&text[14..]));
            }
            _ if !arg.as_encoded_bytes().starts_with(b"-") => positional.push(arg),
            _ => return None,
        }
    }
    if positional.len() != 2 || positional[0] != command {
        return None;
    }
    Some(Options {
        actual: positional[1].into(),
        request: request?,
        checker,
    })
}

pub(super) fn error(code: &'static str, message: impl Into<String>) -> Error {
    Error {
        code,
        message: message.into(),
        json_pointer: String::new(),
    }
}

pub(super) fn read(path: &Path) -> Result<Vec<u8>, Error> {
    let mut bytes = Vec::new();
    File::open(path)
        .map_err(|e| error("io", format!("{}: {e}", path.display())))?
        .take((16 << 20) + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| error("io", e.to_string()))?;
    if bytes.is_empty() || bytes.len() > 16 << 20 {
        return Err(error(
            "limit",
            "engineering input must contain 1..16777216 bytes per file",
        ));
    }
    Ok(bytes)
}

fn json_report(report: &EngineeringPureReport) -> Result<String, Error> {
    let checker = report
        .checker()
        .to_str()
        .ok_or_else(|| error("format", "checker path is not valid UTF-8"))?;
    let bound = report.request().epsilon();
    Ok(format!(
        concat!(
            "{{\"claim_kind\":{},\"metric\":{},\"checker_profile\":{},\"target_profile\":{},",
            "\"composition\":{},\"error_category\":{},",
            "\"epsilon\":{{\"numerator\":{},\"denominator_bits\":{}}},",
            "\"identity_algorithm\":\"sha256\",\"actual_artifact_sha256\":{},",
            "\"ideal_artifact_sha256\":{},\"request_sha256\":{},",
            "\"checker_path\":{},\"checker_identity\":\"unpinned\",\"native_exact_work\":{},",
            "\"native_check_scope\":\"both-original-pure-artifacts-and-engineering-bound\",",
            "\"source_preservation_verified\":false,\"exact_source_correspondence_verified\":false,",
            "\"resource_bound_verified\":false,\"instrument_bound_verified\":false,",
            "\"error_categories\":{{\"implementation_distance\":\"checked-declared-bound\",",
            "\"sampling\":\"not-claimed\",\"algorithmic_resolution\":\"not-claimed\",",
            "\"numerical_runtime\":\"not-claimed\"}}}}"
        ),
        quoted(report.claim_kind()),
        quoted(report.metric()),
        quoted(report.checker_profile()),
        quoted(report.target_profile()),
        quoted(report.composition()),
        quoted(report.error_category()),
        quoted(&bound.numerator().to_string()),
        bound.denominator_bits(),
        quoted(&super::digest::sha256(report.actual_artifact())),
        quoted(&super::digest::sha256(report.ideal_artifact())),
        quoted(&super::digest::sha256(report.request_bytes())),
        quoted(checker),
        report.exact_work()
    ))
}

pub(super) fn checker_text(path: &Path) -> String {
    format!("{path:?}")
}

fn execute(options: Options) -> Result<EngineeringPureReport, Error> {
    let actual = read(&options.actual)?;
    let request = read(&options.request)?;
    let kernel = options
        .checker
        .as_ref()
        .map(Kernel::new)
        .map(Ok)
        .unwrap_or_else(Kernel::selected)?;
    check_serialized_with_kernel(&kernel, &actual, &request)
}

pub(super) fn run(args: &[OsString]) -> ExitCode {
    if args
        .iter()
        .find(|arg| !arg.as_encoded_bytes().starts_with(b"-"))
        .is_some_and(|arg| arg == "compare-instrument")
    {
        return super::engineering_instrument::run(args);
    }
    let json = args.iter().any(|arg| arg == "--format=json");
    let Some(options) = parse(args, "compare-pure") else {
        let failure = error("usage", USAGE);
        if json {
            let diagnostic = artifact_diagnostic_json(failure.code, &failure.message, "");
            let _ = super::write_stdout(
                envelope("engineering compare-pure", Some(&diagnostic), "null").as_bytes(),
                "usage diagnostic",
            );
        } else {
            eprintln!("usage: {USAGE}");
        }
        return ExitCode::from(2);
    };
    match execute(options) {
        Ok(report) => {
            let fields = match json_report(&report) {
                Ok(fields) => fields,
                Err(failure) => return fail(failure, json),
            };
            if json {
                super::write_stdout(
                    envelope("engineering compare-pure", None, &fields).as_bytes(),
                    "engineering result",
                )
            } else {
                let bound = report.request().epsilon();
                let text = format!(
                    "engineering bound checked: {} <= {}/2^{}\nprofile: {}; {}; {}\nactual sha256: {}\nideal sha256: {}\nrequest sha256: {}\nchecker: {} (unpinned); native work: {}\nsource correspondence, instrument bound and target resource bound: not established\nsampling, algorithmic resolution and numerical runtime error: not claimed\n",
                    report.metric(),
                    bound.numerator(),
                    bound.denominator_bits(),
                    report.checker_profile(),
                    report.target_profile(),
                    report.composition(),
                    super::digest::sha256(report.actual_artifact()),
                    super::digest::sha256(report.ideal_artifact()),
                    super::digest::sha256(report.request_bytes()),
                    checker_text(report.checker()),
                    report.exact_work()
                );
                super::write_stdout(text.as_bytes(), "engineering result")
            }
        }
        Err(failure) => fail(failure, json),
    }
}

fn fail(failure: Error, json: bool) -> ExitCode {
    fail_for_command(failure, json, "engineering compare-pure")
}

pub(super) fn fail_for_command(failure: Error, json: bool, command: &str) -> ExitCode {
    if json {
        let diagnostic =
            artifact_diagnostic_json(failure.code, &failure.message, &failure.json_pointer);
        let _ = super::write_stdout(
            envelope(command, Some(&diagnostic), "null").as_bytes(),
            "engineering diagnostic",
        );
    } else {
        eprintln!("{failure}");
    }
    ExitCode::FAILURE
}

#[cfg(test)]
mod tests {
    use super::checker_text;
    use std::path::Path;

    #[test]
    fn checker_path_controls_cannot_inject_an_engineering_scope_line() {
        let text = checker_text(Path::new("/checker\nresource_bound_verified: true\r\t"));
        assert!(!text.contains(['\n', '\r', '\t']));
        assert!(text.contains("\\nresource_bound_verified: true\\r\\t"));
    }
}
