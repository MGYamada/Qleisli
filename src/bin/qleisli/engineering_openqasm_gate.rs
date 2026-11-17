//! Engineering reports for gate definitions with ordered, open interfaces.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use std::ffi::OsString;
use std::process::ExitCode;

use qleisli::interchange::Error;
use qleisli::interchange::engineering_openqasm_gate::{
    EngineeringOpenQasmGateReport, MAX_TARGET_BYTES, RESOURCE_MODEL, compare_serialized_with_kernel,
};
use qleisli::interchange::engineering_pure::DyadicBound;

use super::engineering::{
    Options, checker_text, error, fail_for_command, kernel, parse, read, read_bounded,
};
use super::json::{artifact_diagnostic_json, envelope, quoted};

const COMMAND: &str = "engineering compare-openqasm3-gate";
const USAGE: &str = "qleisli engineering compare-openqasm3-gate TARGET --edition=2026 --against=REQUEST [--lean-kernel=PATH] [--format=json]";

fn execute(options: Options) -> Result<EngineeringOpenQasmGateReport, Error> {
    let actual = read_bounded(
        &options.actual,
        MAX_TARGET_BYTES,
        "canonical OpenQASM gate target requires 1..1024 bytes",
    )?;
    let request = read(&options.request)?;
    compare_serialized_with_kernel(&kernel(&options)?, &actual, &request)
}

fn bound_json(bound: DyadicBound) -> String {
    format!(
        "{{\"numerator\":{},\"denominator_bits\":{}}}",
        quoted(&bound.numerator().to_string()),
        bound.denominator_bits(),
    )
}

fn json_report(report: &EngineeringOpenQasmGateReport) -> Result<String, Error> {
    let checker = report
        .checker()
        .to_str()
        .ok_or_else(|| error("format", "checker path is not valid UTF-8"))?;
    let ideals = report
        .ideal_artifacts()
        .map(|bytes| quoted(&super::digest::sha256(bytes)))
        .collect::<Vec<_>>()
        .join(",");
    let components = report
        .sequential()
        .map_or_else(String::new, |(split, [first, second])| {
            format!(
                "\"composition_split\":{split},\"component_epsilons\":[{},{}],",
                bound_json(first),
                bound_json(second),
            )
        });
    let limits = report.resource_limits();
    let counts = report.checked_gate_counts();
    Ok(format!(
        concat!(
            "{{\"claim_kind\":{},\"metric\":{},\"checker_profile\":{},\"target_profile\":{},",
            "\"composition\":{},\"error_category\":{},\"epsilon\":{},{}",
            "\"identity_algorithm\":\"sha256\",\"target_artifact_sha256\":{},",
            "\"ideal_artifact_sha256\":[{}],\"request_sha256\":{},",
            "\"checker_path\":{},\"checker_identity\":\"unpinned\",\"native_exact_work\":{},",
            "\"engineering_resource_model\":{},",
            "\"engineering_resource_limits\":{{\"gates\":{},\"t_gates\":{}}},",
            "\"engineering_resource_counts\":{{\"wires\":{},\"gates\":{},\"t_gates\":{}}},",
            "\"target_artifact_bound_verified\":true,\"pure_phase_bound_verified\":true,",
            "\"resource_bound_verified\":true,\"instrument_bound_verified\":false,",
            "\"source_preservation_verified\":false,\"exact_source_correspondence_verified\":false,",
            "\"coherent_control_verified\":false,\"inverse_capability_verified\":false,\"cleanup_verified\":false,",
            "\"constitutional_pr_verified\":false,\"constitutional_rs_verified\":false}}"
        ),
        quoted(report.claim_kind()),
        quoted(report.metric()),
        quoted(report.checker_profile()),
        quoted(report.target_profile()),
        quoted(report.composition()),
        quoted(report.error_category()),
        bound_json(report.epsilon()),
        components,
        quoted(&super::digest::sha256(report.target_bytes())),
        ideals,
        quoted(&super::digest::sha256(report.request_bytes())),
        quoted(checker),
        report.exact_work(),
        quoted(RESOURCE_MODEL),
        limits.gates,
        limits.t_gates,
        report.wires(),
        counts.gates,
        counts.t_gates,
    ))
}

fn text_report(report: &EngineeringOpenQasmGateReport) -> String {
    let epsilon = report.epsilon();
    let counts = report.checked_gate_counts();
    let limits = report.resource_limits();
    let components = report
        .sequential()
        .map_or_else(String::new, |(split, [first, second])| {
            format!(
                "split after {split} gates; component budgets: {}/2^{} + {}/2^{}\n",
                first.numerator(),
                first.denominator_bits(),
                second.numerator(),
                second.denominator_bits(),
            )
        });
    let ideals = report
        .ideal_artifacts()
        .map(super::digest::sha256)
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        concat!(
            "OpenQASM gate engineering bound checked: {} <= {}/2^{}\n",
            "profile: {}; {}; {}\n{}",
            "literal resources ({}): {} wires, {} <= {} gates, {} <= {} T/TDG gates\n",
            "target sha256: {}\nideal sha256 (ordered): {}\nrequest sha256: {}\n",
            "checker: {} (unpinned); native work: {}\n",
            "Scope: phase-sensitive engineering comparison of ordered gate definitions and literal resources.\n",
            "Source correspondence, source capabilities and constitutional PR/RS: not established.\n"
        ),
        report.metric(),
        epsilon.numerator(),
        epsilon.denominator_bits(),
        report.checker_profile(),
        report.target_profile(),
        report.composition(),
        components,
        RESOURCE_MODEL,
        report.wires(),
        counts.gates,
        limits.gates,
        counts.t_gates,
        limits.t_gates,
        super::digest::sha256(report.target_bytes()),
        ideals,
        super::digest::sha256(report.request_bytes()),
        checker_text(report.checker()),
        report.exact_work(),
    )
}

pub(super) fn run(args: &[OsString]) -> ExitCode {
    let json = args.iter().any(|arg| arg == "--format=json");
    let Some(options) = parse(args, "compare-openqasm3-gate") else {
        if json {
            let diagnostic = artifact_diagnostic_json("usage", USAGE, "");
            let written = super::write_stdout(
                envelope(COMMAND, Some(&diagnostic), "null").as_bytes(),
                "usage diagnostic",
            );
            if written != ExitCode::SUCCESS {
                return written;
            }
        } else {
            eprintln!("usage: {USAGE}");
        }
        return ExitCode::from(2);
    };
    let report = match execute(options) {
        Ok(report) => report,
        Err(failure) => return fail_for_command(failure, json, COMMAND),
    };
    let result = if json {
        match json_report(&report) {
            Ok(fields) => envelope(COMMAND, None, &fields),
            Err(failure) => return fail_for_command(failure, true, COMMAND),
        }
    } else {
        text_report(&report)
    };
    super::write_stdout(result.as_bytes(), "engineering gate result")
}
