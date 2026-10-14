//! Complete instrument engineering reports, distinct from exact acceptance.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use std::ffi::OsString;
use std::process::ExitCode;

use qleisli::interchange::Error;
use qleisli::interchange::engineering_instrument::{
    EngineeringInstrumentReport, check_serialized_with_kernel,
};
use qleisli::interchange::native::Kernel;

use super::engineering::{Options, checker_text, error, fail_for_command, parse, read};
use super::json::{artifact_diagnostic_json, envelope, quoted};

const COMMAND: &str = "engineering compare-instrument";
const USAGE: &str = "qleisli engineering compare-instrument ACTUAL --against=REQUEST [--lean-kernel=PATH] [--format=json]";

fn execute(options: Options) -> Result<EngineeringInstrumentReport, Error> {
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

fn json_report(report: &EngineeringInstrumentReport) -> Result<String, Error> {
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
            "\"native_check_scope\":\"both-original-instruments-and-complete-adjoint-bound\",",
            "\"instrument_bound_verified\":true,\"pure_phase_bound_verified\":false,",
            "\"source_preservation_verified\":false,\"exact_source_correspondence_verified\":false,",
            "\"coherent_control_verified\":false,\"inverse_capability_verified\":false,",
            "\"cleanup_verified\":false,\"resource_bound_verified\":false,",
            "\"constitutional_pr_verified\":false,\"constitutional_rs_verified\":false,",
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

pub(super) fn run(args: &[OsString]) -> ExitCode {
    let json = args.iter().any(|arg| arg == "--format=json");
    let Some(options) = parse(args, "compare-instrument") else {
        if json {
            let diagnostic = artifact_diagnostic_json("usage", USAGE, "");
            let _ = super::write_stdout(
                envelope(COMMAND, Some(&diagnostic), "null").as_bytes(),
                "usage diagnostic",
            );
        } else {
            eprintln!("usage: {USAGE}");
        }
        return ExitCode::from(2);
    };
    let report = match execute(options) {
        Ok(report) => report,
        Err(failure) => return fail_for_command(failure, json, COMMAND),
    };
    if json {
        match json_report(&report) {
            Ok(fields) => super::write_stdout(
                envelope(COMMAND, None, &fields).as_bytes(),
                "engineering instrument result",
            ),
            Err(failure) => fail_for_command(failure, true, COMMAND),
        }
    } else {
        let bound = report.request().epsilon();
        let text = format!(
            concat!(
                "instrument engineering bound checked: {} <= {}/2^{}\n",
                "profile: {}; {}; {}\nactual sha256: {}\nideal sha256: {}\nrequest sha256: {}\n",
                "checker: {} (unpinned); native work: {}\n",
                "source correspondence, pure phase agreement, coherent control, inverse, clean release and target resource bounds: not established\n",
                "sampling, algorithmic resolution and numerical runtime error: not claimed\n"
            ),
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
        super::write_stdout(text.as_bytes(), "engineering instrument result")
    }
}
