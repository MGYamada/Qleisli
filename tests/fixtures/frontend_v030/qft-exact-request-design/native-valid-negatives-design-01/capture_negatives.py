#!/usr/bin/env python3
"""At most six fixed fresh calls; request only follows successful inspection.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import json
import os
import sys

sys.dont_write_bytecode = True
import generate_negatives as design

OUTPUT = design.SESSION / "native-valid-negative-capture-01"


def prepared_barrier(args, canon, old):
    base, association = design.barrier(args,canon,old)
    post = design.targets(base,association,canon)
    path = design.PREPARED / "prepared-files.json"
    design.require(design.sha(design.read(path)) == args.negative_prepared_map_sha256,
                   "explicit reviewed negative prepared map changed")
    fixed = design.parse(design.read(path))
    prerequisites = {k:v for k,v in vars(args).items() if k != "negative_prepared_map_sha256"}
    design.require(fixed["format"] == "qleisli.untrusted-n2-negative-prepared-files" and fixed["version"] == 1
                   and fixed["reviewed_prerequisites"] == prerequisites, "negative map prerequisite mismatch")
    names = {"started.json","summary.json"}
    names.update(case + "." + suffix for case in design.CASES for suffix in ("proposal.json","delta.json"))
    design.require(len(fixed["files"]) == len(names) and {r["path"] for r in fixed["files"]} == names,
                   "negative prepared map must contain exactly eight fixed files")
    for row in fixed["files"]:
        p = design.PREPARED / row["path"]
        design.require(p.stat().st_size == row["bytes"] and old.digest(p) == row["sha256"]
                       and p.stat().st_mode & 0o777 == row["mode"], "prepared negative changed")
    for case in design.CASES:
        payload = design.PREPARED / (case + ".proposal.json")
        delta = design.parse(design.read(design.PREPARED / (case + ".delta.json")))
        value = design.parse(design.read(payload))
        design.require(delta["case"] == case and delta["width"] == 2
                       and delta["positive_payload_sha256"] == design.sha(design.read(design.POSITIVE / "n2.proposal.json"))
                       and delta["mutant_payload_sha256"] == design.sha(design.read(payload))
                       and delta["frozen_request_sha256"] == design.REQUEST_SHA
                       and delta["post_DMP_from_actual_association"] == list(post), "negative origin/association mismatch")
        design.require(design.diffs(base,value) == delta["changed_field_paths"]
                       and sorted(delta["changed_field_paths"],key=str) == sorted(design.expected_paths(case,post),key=str)
                       and value["proofs"] == base["proofs"] and value["encodings"] == base["encodings"]
                       and canon.graph(value) == canon.graph(base), "negative fields/P/E/typed roots changed")
        design.require(delta["expected_fresh_inspect"] == "success-required-before-request"
                       and delta["expected_frozen_request"] == "reject-contract", "fixed expectations changed")


def command(case, action, old):
    # Only literal reviewed case/action values select argv, never map metadata.
    design.require(case in design.CASES and action in ("inspect","request"), "unexpected fixed command")
    argv = [str(old.CLIENT),action,str(old.FORWARDER),str(design.PREPARED / (case + ".proposal.json"))]
    if action == "request":
        argv.append(str(design.SESSION / "requests/n2.json"))
    return argv


def observe(case, action, old):
    folder = OUTPUT / (case + "-" + action)
    folder.mkdir()
    native_logs = folder / "native"
    native_logs.mkdir()
    argv = command(case,action,old)
    env = dict(os.environ)
    env.pop("QLEISLI_KERNEL",None)
    env.pop("QLEISLI_HIERARCHY_KERNEL",None)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env[old.CAPTURE_ENV] = str(native_logs)
    old.write_json(folder / "command-before.json",{"recorded_utc":old.timestamp(),"argv":argv,
        "cwd":str(design.REPO),"fixed_native_capture_directory":str(native_logs),"width":2,"case":case,
        "independent_request_unchanged":action == "request","payload_untrusted":True})
    result = old.capture(argv,design.REPO,env,b"",seconds=55,output_limit=design.LIMIT)
    stdout, stderr = result.pop("stdout"), result.pop("stderr")
    with (folder / "stdout.bin").open("xb") as stream:
        stream.write(stdout)
    with (folder / "stderr.bin").open("xb") as stream:
        stream.write(stderr)
    attempts = sorted(p for p in native_logs.iterdir() if p.is_dir())
    native = []
    for p in attempts:
        record = design.parse(design.read(p / "result.json")) if (p / "result.json").exists() else None
        native.append({"directory":str(p),"process_started_record":(p / "process-started.json").exists(),"result":record})
    calls = sum(item["process_started_record"] for item in native)
    try:
        api = design.parse(stdout)
    except (ValueError,UnicodeError):
        api = None
    stage = ("actual-native-process-observed" if calls else
             "forwarder-attempt-without-recorded-native-process" if attempts else
             "no-forwarder-or-native-process-observed-see-api-error")
    event = {"recorded_utc":old.timestamp(),"width":2,"case":case,"action":action,"argv":argv,"cwd":str(design.REPO),
        "client_capture":result,"api_record":api,"raw_stdout":design.describe(folder / "stdout.bin"),
        "raw_stderr":design.describe(folder / "stderr.bin"),"forwarder_attempts":len(attempts),"actual_native_calls":calls,
        "native_records":native,"observed_stage":stage,
        "stage_scope":"Actual fresh client/native observations only; no source/adapter/general Fourier proof or guarantee discharge."}
    old.write_json(folder / "result.json",event)
    return event, folder


def request_classification(event, folder, old):
    client = event["client_capture"]
    api = event["api_record"]
    native = event["native_records"]
    if not (client.get("spawned") is True and client.get("reason") is None and client.get("error") is None
            and client.get("stdout_limited") is False and client.get("stderr_limited") is False
            and event["forwarder_attempts"] == event["actual_native_calls"] == 1 and len(native) == 1
            and native[0]["process_started_record"] is True and type(native[0]["result"]) is dict):
        return "operational-or-incomplete-request-observation"
    actual = native[0]["result"]
    capture = actual.get("capture",{})
    if not (actual.get("actual_native_spawned") is True and actual.get("native_sha256_before") == design.NATIVE_SHA
            and actual.get("native_sha256_after") == design.NATIVE_SHA and "wrapper_rejection" not in actual
            and capture.get("spawned") is True and capture.get("reason") is None and capture.get("error") is None
            and capture.get("stdout_limited") is False and capture.get("stderr_limited") is False):
        return "operational-or-incomplete-request-observation"
    try:
        native_folder = folder / "native/call-01"
        expected = [str(old.NATIVE),"--hierarchy-fourier-pending","0.3.0-alpha"]
        start = design.parse(design.read(native_folder / "process-started.json"))
        if (start.get("argv") != expected or start.get("native_sha256_before") != design.NATIVE_SHA
                or actual.get("requested_native_argv") != expected
                or actual.get("wrapper_argv") != [str(old.FORWARDER),"--hierarchy-fourier-pending","0.3.0-alpha"]
                or actual.get("ordinal") != 1 or actual.get("stdin_limited_prefix") is not False
                or capture.get("stdin_written") != actual.get("stdin_bytes")
                or event["argv"] != command(event["case"],"request",old)
                or event["api_record"] != design.parse(design.read(folder / "stdout.bin"))
                or sorted(p.name for p in (folder / "native").iterdir()) != ["call-01"]
                or event["native_records"] != [{"directory":str(native_folder),"process_started_record":True,
                                               "result":design.parse(design.read(native_folder / "result.json"))}]):
            return "operational-or-incomplete-request-observation"
        for label in ("stdout","stderr"):
            if event["raw_" + label] != design.describe(folder / (label + ".bin")):
                return "operational-or-incomplete-request-observation"
        for label in ("stdin","stdout","stderr"):
            data = design.read(native_folder / (label + ".bin"))
            if actual.get(label + "_bytes") != len(data) or actual.get(label + "_sha256") != design.sha(data):
                return "operational-or-incomplete-request-observation"
    except (OSError,ValueError,KeyError,TypeError,AttributeError):
        return "operational-or-incomplete-request-observation"
    if (type(api) is dict and api.get("action") == "request" and api.get("status") == "error"
            and api.get("stage") == "hierarchical-kernel-api" and api.get("code") == "contract"
            and client.get("returncode") == actual.get("actual_native_returncode") == actual.get("wrapper_exit_code") == 1):
        return "predicted-native-contract-rejection-observed"
    if type(api) is dict and api.get("status") == "ok":
        return "unexpected-request-success-retained"
    return "unexpected-request-outcome-retained"


def main():
    design.require(sys.version_info >= (3,11), "Python 3.11 or newer required")
    parser = argparse.ArgumentParser(description=__doc__)
    design.arguments(parser)
    parser.add_argument("--negative-prepared-map-sha256",required=True)
    args = parser.parse_args()
    canon, old = design.load(args)
    prepared_barrier(args,canon,old)
    OUTPUT.mkdir()  # One shot; partial/existing output is never overwritten.
    old.write_json(OUTPUT / "started.json",{"recorded_utc":old.timestamp(),"status":"capture-started-no-outcome-observed",
        "reviewed_prerequisites":vars(args),"width":2,"cases":list(design.CASES),"maximum_client_calls":6,
        "request_only_after_complete_fresh_inspect_success":True})
    events, outcomes = [], []
    try:
        for case in design.CASES:
            prepared_barrier(args,canon,old)
            event, folder = observe(case,"inspect",old)
            events.append(event)
            prepared_barrier(args,canon,old)
            try:
                ok, reason = design.successful(event,folder,"inspect",design.PREPARED / (case + ".proposal.json"),old)
            except (OSError,ValueError,KeyError,TypeError,AttributeError) as error:
                ok, reason = False, "incomplete inspection validation: " + type(error).__name__ + ": " + str(error)
            if not ok:
                outcome = {"case":case,"inspection_successful":False,"request_executed":False,
                    "classification":"request-check-skipped-inspection-not-successful","reason":reason,
                    "semantic_negative_claim":False}
                old.write_json(OUTPUT / (case + "-request-skipped.json"),outcome)
                outcomes.append(outcome)
                continue
            prepared_barrier(args,canon,old)
            request, request_folder = observe(case,"request",old)
            events.append(request)
            prepared_barrier(args,canon,old)
            outcomes.append({"case":case,"inspection_successful":True,"inspection_validation":reason,
                "request_executed":True,"classification":request_classification(request,request_folder,old),
                "claim_scope":"Bounded actual payload/request gate observation; public contract code does not identify an internal predicate uniquely."})
        old.write_json(OUTPUT / "summary.json",{"recorded_utc":old.timestamp(),"status":"fixed-bounded-capture-completed",
            "client_observations":len(events),"maximum_client_calls":6,"actual_native_calls":sum(e["actual_native_calls"] for e in events),
            "events":[e["case"] + "-" + e["action"] + "/result.json" for e in events],"outcomes":outcomes,
            "identity_barriers":"pass","independent_request_unchanged":True,"expected_outcomes_changed":False,
            "source_meaning_verified":False,"scope":"Recorder completion only; raw errors/unexpected successes remain without repair/retry."})
    except BaseException as error:
        old.write_json(OUTPUT / "aborted.json",{"recorded_utc":old.timestamp(),"completed_observations":len(events),
            "error_type":type(error).__name__,"message":str(error),"note":"Partial records retained; no retries/input/expectation repair."})
        raise


if __name__ == "__main__":
    main()
