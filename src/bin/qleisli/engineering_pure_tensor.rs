//! Explicit two-component engineering tensor comparison.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use std::ffi::OsString;
use std::process::ExitCode;

use qleisli::interchange::Error;
use qleisli::interchange::engineering_pure_tensor::{
    EngineeringPureTensorReport, check_serialized_with_kernel,
};
use qleisli::interchange::native::Kernel;

use super::engineering::{checker_text, error, fail_for_command, parse, read};
use super::json::{artifact_diagnostic_json, envelope, quoted};

const COMMAND: &str = "engineering compare-pure-tensor";
const USAGE: &str = "qleisli engineering compare-pure-tensor ACTUAL --against=REQUEST [--lean-kernel=PATH] [--format=json]";

fn json_report(report: &EngineeringPureTensorReport) -> Result<String, Error> {
    let checker = report
        .checker()
        .to_str()
        .ok_or_else(|| error("format", "checker path is not valid UTF-8"))?;
    let epsilon = |request: &qleisli::interchange::engineering_pure::EngineeringPureRequest| {
        let bound = request.epsilon();
        format!(
            "{{\"numerator\":{},\"denominator_bits\":{}}}",
            quoted(&bound.numerator().to_string()),
            bound.denominator_bits()
        )
    };
    let digests = report.artifacts().map(super::digest::sha256);
    Ok(format!(
        concat!(
            "{{\"claim_kind\":{},\"metric\":{},\"checker_profile\":{},\"target_profile\":{},",
            "\"composition\":{},\"error_category\":{},\"epsilon\":{},\"component_epsilons\":[{},{}],",
            "\"identity_algorithm\":\"sha256\",\"actual_artifact_sha256\":{},\"ideal_artifact_sha256\":{},",
            "\"component_artifact_sha256\":[{{\"actual\":{},\"ideal\":{}}},{{\"actual\":{},\"ideal\":{}}}],",
            "\"request_sha256\":{},\"checker_path\":{},\"checker_identity\":\"unpinned\",\"native_exact_work\":{},",
            "\"native_check_scope\":\"six-original-pure-artifacts-ordered-tensor-equations-and-additive-component-bounds\",",
            "\"source_preservation_verified\":false,\"exact_source_correspondence_verified\":false,",
            "\"phase_agreement_verified\":false,\"control_access_verified\":false,\"inverse_access_verified\":false,",
            "\"clean_workspace_verified\":false,\"dirty_workspace_verified\":false,\"resource_bound_verified\":false,",
            "\"target_realization_verified\":false,\"constitutional_pr_verified\":false,\"constitutional_rs_verified\":false,",
            "\"instrument_bound_verified\":false,\"error_categories\":{{\"implementation_distance\":\"checked-declared-bound\",",
            "\"sampling\":\"not-claimed\",\"algorithmic_resolution\":\"not-claimed\",\"numerical_runtime\":\"not-claimed\"}}}}"
        ),
        quoted(report.claim_kind()),
        quoted(report.metric()),
        quoted(report.checker_profile()),
        quoted(report.target_profile()),
        quoted(report.composition()),
        quoted(report.error_category()),
        epsilon(report.request().parent()),
        epsilon(report.request().left()),
        epsilon(report.request().right()),
        quoted(&digests[0]),
        quoted(&digests[1]),
        quoted(&digests[2]),
        quoted(&digests[3]),
        quoted(&digests[4]),
        quoted(&digests[5]),
        quoted(&super::digest::sha256(report.request_bytes())),
        quoted(checker),
        report.exact_work()
    ))
}

fn execute(options: super::engineering::Options) -> Result<EngineeringPureTensorReport, Error> {
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
    let json = args.iter().any(|arg| arg == "--format=json");
    let Some(options) = parse(args, "compare-pure-tensor") else {
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
    match execute(options) {
        Ok(report) => {
            if json {
                let fields = match json_report(&report) {
                    Ok(fields) => fields,
                    Err(failure) => return fail_for_command(failure, json, COMMAND),
                };
                super::write_stdout(
                    envelope(COMMAND, None, &fields).as_bytes(),
                    "engineering tensor result",
                )
            } else {
                let bound = report.request().parent().epsilon();
                let left = report.request().left().epsilon();
                let right = report.request().right().epsilon();
                let digests = report.artifacts().map(super::digest::sha256);
                let text = format!(
                    "engineering tensor bound checked: {} <= {}/2^{}\ncomponent budgets: {}/2^{} + {}/2^{}\nprofile: {}; {}; {}\nnative scope: six original pure artifacts, both ordered tensor equations and additive component bounds\nparent actual sha256: {}\nparent ideal sha256: {}\nleft actual sha256: {}\nleft ideal sha256: {}\nright actual sha256: {}\nright ideal sha256: {}\nrequest sha256: {}\nchecker: {} (unpinned); native work: {}\nsource correspondence, exact phase agreement, control/inverse access, cleanup, instrument bound, target realization/resource bound and constitutional PR/RS: not established\nsampling, algorithmic resolution and numerical runtime error: not claimed\n",
                    report.metric(),
                    bound.numerator(),
                    bound.denominator_bits(),
                    left.numerator(),
                    left.denominator_bits(),
                    right.numerator(),
                    right.denominator_bits(),
                    report.checker_profile(),
                    report.target_profile(),
                    report.composition(),
                    digests[0],
                    digests[1],
                    digests[2],
                    digests[3],
                    digests[4],
                    digests[5],
                    super::digest::sha256(report.request_bytes()),
                    checker_text(report.checker()),
                    report.exact_work()
                );
                super::write_stdout(text.as_bytes(), "engineering tensor result")
            }
        }
        Err(failure) => fail_for_command(failure, json, COMMAND),
    }
}
