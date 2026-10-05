#!/usr/bin/env python3
"""One fresh n2 inspect, then at most one unchanged Fourier request.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
OUTPUT = REPO / "tests/fixtures/authoring_sessions/qft-exact-request-v030/native-valid-reversal-capture-02"


def load(args):
    # Hash the complete frozen input map before importing local executable code.
    path = HERE / "script-inputs.json"
    if hashlib.sha256(path.read_bytes()).hexdigest() != args.reversal_design_map_sha256:
        raise ValueError("explicit reviewed reversal input map changed")
    fixed = json.loads(path.read_bytes())
    if fixed.get("format") != "qleisli.unexecuted-reversal-script-inputs" or fixed.get("version") != 1:
        raise ValueError("unexpected reversal input map")
    for row in fixed["files"]:
        item = (REPO / row["path"]).resolve()
        item.relative_to(REPO)
        if item.stat().st_size > (1 << 20) or item.stat().st_size != row["bytes"]:
            raise ValueError("unbounded/changed reviewed reversal input")
        if hashlib.sha256(item.read_bytes()).hexdigest() != row["sha256"] or item.stat().st_mode & 0o777 != row["mode"]:
            raise ValueError("reviewed reversal input changed")
    spec = importlib.util.spec_from_file_location("qft_reviewed_reversal02_generation", HERE / "generate_reversal.py")
    if spec is None or spec.loader is None:
        raise ValueError("cannot load reviewed fixed generator")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def prepared_barrier(args, design, first, canon, old):
    base, association = design.barrier(args, first, canon, old)
    path = design.PREPARED / "prepared-files.json"
    design.require(design.sha(design.read(path)) == args.reversal_prepared_map_sha256,
                   "explicit reviewed reversal prepared map changed")
    fixed = design.parse(design.read(path))
    prerequisites = {k: v for k, v in vars(args).items() if k != "reversal_prepared_map_sha256"}
    design.require(fixed["format"] == "qleisli.untrusted-reversal02-prepared-files" and fixed["version"] == 1
                   and fixed["reviewed_prerequisites"] == prerequisites, "prepared prerequisite mismatch")
    names = {"started.json", "summary.json", design.CASE + ".proposal.json", design.CASE + ".delta.json"}
    design.require(len(fixed["files"]) == 4 and {r["path"] for r in fixed["files"]} == names,
                   "prepared map must contain its exact four files")
    for row in fixed["files"]:
        item = design.PREPARED / row["path"]
        design.require(item.stat().st_size == row["bytes"] and old.digest(item) == row["sha256"]
                       and item.stat().st_mode & 0o777 == row["mode"], "prepared reversal changed")
    # Fixed pure data construction validates the full intended delta; no output
    # files are generated here, and it is never the independent request oracle.
    expected, delta = design.construct(base, association, first, canon)
    design.require(design.read(design.PREPARED / (design.CASE + ".proposal.json")) == expected
                   and design.parse(design.read(design.PREPARED / (design.CASE + ".delta.json"))) == delta,
                   "prepared bytes/association differ from the reviewed fixed construction")


def command(action, design, old):
    design.require(action in ("inspect", "request"), "unexpected fixed action")
    argv = [str(old.CLIENT), action, str(old.FORWARDER), str(design.PREPARED / (design.CASE + ".proposal.json"))]
    if action == "request":
        argv.append(str(design.SESSION / "requests/n2.json"))
    return argv


def observe(action, design, first, old):
    folder = OUTPUT / (design.CASE + "-" + action)
    folder.mkdir()
    native_logs = folder / "native"
    native_logs.mkdir()
    argv = command(action, design, old)
    env = dict(os.environ)
    env.pop("QLEISLI_KERNEL", None)
    env.pop("QLEISLI_HIERARCHY_KERNEL", None)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env[old.CAPTURE_ENV] = str(native_logs)
    old.write_json(folder / "command-before.json", {"recorded_utc": old.timestamp(), "argv": argv,
        "cwd": str(REPO), "fixed_native_capture_directory": str(native_logs), "width": 2, "case": design.CASE,
        "independent_request_unchanged": action == "request", "payload_untrusted": True})
    captured = old.capture(argv, REPO, env, b"", seconds=55, output_limit=design.LIMIT)
    stdout, stderr = captured.pop("stdout"), captured.pop("stderr")
    for name, raw in (("stdout.bin", stdout), ("stderr.bin", stderr)):
        with (folder / name).open("xb") as stream:
            stream.write(raw)
    native = []
    attempts = sorted(p for p in native_logs.iterdir() if p.is_dir())
    for item in attempts:
        record, error = None, None
        if (item / "result.json").exists():
            try:
                record = design.parse(design.read(item / "result.json"))
            except (OSError, ValueError, UnicodeError) as failure:
                error = type(failure).__name__ + ": " + str(failure)
        entry = {"directory": str(item), "process_started_record": (item / "process-started.json").exists(), "result": record}
        if error is not None:
            entry["result_read_error"] = error
        native.append(entry)
    calls = sum(item["process_started_record"] for item in native)
    try:
        api = design.parse(stdout)
    except (ValueError, UnicodeError):
        api = None
    stage = ("actual-native-process-observed" if calls else
             "forwarder-attempt-without-recorded-native-process" if attempts else
             "no-forwarder-or-native-process-observed-see-api-error")
    event = {"recorded_utc": old.timestamp(), "width": 2, "case": design.CASE, "action": action,
        "argv": argv, "cwd": str(REPO), "client_capture": captured, "api_record": api,
        "raw_stdout": first.describe(folder / "stdout.bin"), "raw_stderr": first.describe(folder / "stderr.bin"),
        "forwarder_attempts": len(attempts), "actual_native_calls": calls, "native_records": native,
        "observed_stage": stage,
        "scope": "Actual fresh observations only; no source/adapter/general Fourier proof or guarantee discharge."}
    old.write_json(folder / "result.json", event)
    return event, folder


def completion(event, folder, action, design, first, old):
    """Validate completed real client/native records independently of success."""
    try:
        capture = event["client_capture"]
        def transport(record):
            return (record.get("spawned") is True and record.get("reason") is None and record.get("error") is None
                    and record.get("stdout_limited") is False and record.get("stderr_limited") is False)
        if not transport(capture) or event["action"] != action or event["width"] != 2:
            return False, "client operational/incomplete capture"
        if event["argv"] != command(action, design, old) or event["cwd"] != str(REPO):
            return False, "fixed client command mismatch"
        for label in ("stdout", "stderr"):
            if event["raw_" + label] != first.describe(folder / (label + ".bin")):
                return False, "client raw record mismatch"
        api = design.parse(design.read(folder / "stdout.bin"))
        if event["api_record"] != api or type(api) is not dict or api.get("action") != action:
            return False, "missing/malformed client API record"
        if event["forwarder_attempts"] != event["actual_native_calls"] or event["actual_native_calls"] != 1:
            return False, "not exactly one actual fresh native start"
        native_folder = folder / "native/call-01"
        if sorted(p.name for p in (folder / "native").iterdir()) != ["call-01"]:
            return False, "unexpected native attempt inventory"
        actual = design.parse(design.read(native_folder / "result.json"))
        start = design.parse(design.read(native_folder / "process-started.json"))
        if event["native_records"] != [{"directory": str(native_folder), "process_started_record": True, "result": actual}]:
            return False, "native event does not bind actual completed records"
        mode = "--hierarchy-pending" if action == "inspect" else "--hierarchy-fourier-pending"
        argv = [str(old.NATIVE), mode, "0.3.0-alpha"]
        inner = actual.get("capture", {})
        if not (transport(inner) and actual.get("actual_native_spawned") is True
                and start.get("argv") == actual.get("requested_native_argv") == argv
                and actual.get("wrapper_argv") == [str(old.FORWARDER), mode, "0.3.0-alpha"]
                and actual.get("ordinal") == 1 and "wrapper_rejection" not in actual
                and start.get("native_sha256_before") == actual.get("native_sha256_before")
                    == actual.get("native_sha256_after") == design.NATIVE_SHA
                and actual.get("stdin_limited_prefix") is False
                and inner.get("stdin_written") == actual.get("stdin_bytes")
                and capture.get("returncode") == actual.get("actual_native_returncode")
                    == inner.get("returncode") == actual.get("wrapper_exit_code")):
            return False, "native operational/incomplete/identity or return-code mismatch"
        for label in ("stdin", "stdout", "stderr"):
            data = design.read(native_folder / (label + ".bin"))
            if actual.get(label + "_bytes") != len(data) or actual.get(label + "_sha256") != design.sha(data):
                return False, "native raw record mismatch"
        if event["observed_stage"] != "actual-native-process-observed":
            return False, "native observation stage mismatch"
        return True, "complete actual client/native return with retained raw records"
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as error:
        return False, "incomplete raw validation: " + type(error).__name__ + ": " + str(error)


def outcome(event, folder, action, design, first, old):
    complete, reason = completion(event, folder, action, design, first, old)
    if not complete:
        return {"classification": "operational-or-incomplete-observation", "reason": reason, "success": False}
    api = event["api_record"]
    native_raw = design.read(folder / "native/call-01/stdout.bin")
    header = b"qleisli.hierarchy-pending 3" if action == "inspect" else b"qleisli.hierarchy-fourier-pending 3"
    lines = native_raw.splitlines()
    code = api.get("code")
    if (api.get("status") == "error" and api.get("stage") == "hierarchical-kernel-api" and type(code) is str
            and lines == [header, b"error", code.encode()]
            and event["client_capture"]["returncode"] == 1):
        predicted = action == "request" and code == "contract"
        return {"classification": "predicted-native-contract-rejection-observed" if predicted
                else "complete-native-semantic-refusal", "reason": "actual native refusal: " + code,
                "code": code, "success": False}
    try:
        successful, success_reason = first.successful(event, folder, action,
            design.PREPARED / (design.CASE + ".proposal.json"), old)
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as error:
        successful, success_reason = False, "successful-API validation failed: " + type(error).__name__
    length = 7 if action == "inspect" else 10
    if (successful and len(lines) == length and lines[:2] == [header, b"pending"]
            and all(line.isdigit() for line in lines[2:])):
        return {"classification": "complete-fresh-inspection-success" if action == "inspect"
                else "unexpected-request-success-retained", "reason": success_reason, "success": True}
    return {"classification": "complete-unexpected-outcome-retained", "reason": reason + "; " + success_reason,
            "success": False}


def main():
    if sys.version_info < (3, 11):
        raise ValueError("Python 3.11 or newer required")
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("client", "negative-design-map", "canonical-design-map", "canonical-prepared-map",
                 "positive-inspect-result", "positive-request-result", "reversal-design-map", "reversal-prepared-map"):
        parser.add_argument("--" + name + "-sha256", required=True)
    args = parser.parse_args()
    design = load(args)
    first, canon, old = design.load(args)
    prepared_barrier(args, design, first, canon, old)
    OUTPUT.mkdir()  # One shot; no existing/partial directory may be replaced.
    old.write_json(OUTPUT / "started.json", {"recorded_utc": old.timestamp(), "reviewed_prerequisites": vars(args),
        "width": 2, "case": design.CASE, "maximum_client_calls": 2, "status": "capture-started-no-outcome-observed",
        "request_only_after_complete_fresh_inspection_success": True})
    events, outcomes = [], []
    try:
        event, folder = observe("inspect", design, first, old)
        events.append(event)
        prepared_barrier(args, design, first, canon, old)
        inspection = outcome(event, folder, "inspect", design, first, old)
        outcomes.append({"action": "inspect", **inspection})
        if not inspection["success"]:
            old.write_json(OUTPUT / "request-skipped.json", {"case": design.CASE, "request_executed": False,
                "inspection_classification": inspection["classification"], "reason": inspection["reason"],
                "semantic_negative_claim": False})
        else:
            prepared_barrier(args, design, first, canon, old)
            event, folder = observe("request", design, first, old)
            events.append(event)
            prepared_barrier(args, design, first, canon, old)
            outcomes.append({"action": "request", **outcome(event, folder, "request", design, first, old)})
        old.write_json(OUTPUT / "summary.json", {"recorded_utc": old.timestamp(), "status": "fixed-bounded-capture-completed",
            "maximum_client_calls": 2, "client_observations": len(events),
            "actual_native_calls": sum(e["actual_native_calls"] for e in events), "outcomes": outcomes,
            "events": [e["case"] + "-" + e["action"] + "/result.json" for e in events],
            "identity_barriers": "pass", "independent_request_unchanged": True, "expected_outcomes_changed": False,
            "source_meaning_verified": False,
            "scope": "Recorder completion only; complete native refusals and operational faults are distinct, raw unexpected outcomes retained."})
    except BaseException as error:
        old.write_json(OUTPUT / "aborted.json", {"recorded_utc": old.timestamp(), "completed_observations": len(events),
            "error_type": type(error).__name__, "message": str(error),
            "note": "Partial records retained; no retries/input/request/expectation repair."})
        raise


if __name__ == "__main__":
    main()
