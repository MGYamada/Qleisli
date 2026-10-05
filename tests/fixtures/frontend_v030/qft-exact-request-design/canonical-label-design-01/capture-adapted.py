#!/usr/bin/env python3
"""Eight fixed fresh inspect/request observations of untrusted label adapters.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import json
import os
import sys

sys.dont_write_bytecode = True
import generate as design

OUTPUT = design.SESSION / "canonical-native-capture-01"


def prepared_barrier(args, old):
    design.barrier(args.design_map_sha256, old)
    design.require(args.client_sha256 == design.CLIENT_SHA256, "explicit observed client hash differs")
    map_path = design.PREPARED / "prepared-files.json"
    design.require(design.valid_sha(args.prepared_map_sha256) and old.digest(map_path) == args.prepared_map_sha256,
                   "explicit root-reviewed generated input map changed")
    fixed = json.loads(design.read_bounded(map_path))
    design.require(fixed["format"] == "qleisli.untrusted-canonical-label-prepared-files"
                   and fixed["version"] == 1 and fixed["reviewed_design_map_sha256"] == args.design_map_sha256,
                   "generated map does not refer to this reviewed candidate")
    names = {"started.json", "summary.json"}
    names.update("n" + str(width) + "." + suffix for width in range(4)
                 for suffix in ("proposal.json", "association.json"))
    rows = fixed["files"]
    design.require(len(rows) == len(names) and {row["path"] for row in rows} == names,
                   "generated map must contain exactly the fixed ten data files")
    for row in rows:
        path = design.PREPARED / row["path"]
        design.read_bounded(path)
        design.require(path.stat().st_size == row["bytes"] and old.digest(path) == row["sha256"]
                       and path.stat().st_mode & 0o777 == row["mode"], "generated data changed: " + row["path"])
    for width in range(4):
        payload = design.PREPARED / ("n" + str(width) + ".proposal.json")
        association = json.loads(design.read_bounded(design.PREPARED / ("n" + str(width) + ".association.json")))
        design.require(association["width"] == width and association["original_payload_sha256"] == design.ORIGINAL_SHA256[width]
                       and association["adapted_payload_sha256"] == old.digest(payload), "generated association/data identity mismatch")


def command(width, action, old):
    # These literal paths/actions select argv. Neither a packet nor a map can
    # supply an executable, option, request, provider or command string.
    argv = [str(old.CLIENT), action, str(old.FORWARDER),
            str(design.PREPARED / ("n" + str(width) + ".proposal.json"))]
    if action == "request":
        argv.append(str(design.SESSION / "requests" / ("n" + str(width) + ".json")))
    return argv


def main():
    design.require(sys.version_info >= (3, 11), "development Python 3.11 or newer is required")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--client-sha256", required=True)
    parser.add_argument("--design-map-sha256", required=True)
    parser.add_argument("--prepared-map-sha256", required=True)
    args = parser.parse_args()
    design.require(all(design.valid_sha(value) for value in vars(args).values()), "reviewed SHA-256 arguments must be lowercase hexadecimal")
    old = design.old_capture()
    prepared_barrier(args, old)
    OUTPUT.mkdir()  # One shot; existing/partial output is never rewritten.
    old.write_json(OUTPUT / "started.json", dict(recorded_utc=old.timestamp(), widths=[0, 1, 2, 3],
        actions=["inspect", "request"], reviewed_client_sha256=args.client_sha256,
        reviewed_design_map_sha256=args.design_map_sha256, reviewed_prepared_map_sha256=args.prepared_map_sha256,
        status="capture-started-no-outcome-predicted"))
    events = []
    try:
        for width in range(4):
            for action in ("inspect", "request"):
                prepared_barrier(args, old)
                case = OUTPUT / ("n" + str(width) + "-" + action)
                case.mkdir()
                native_logs = case / "native"
                native_logs.mkdir()
                argv = command(width, action, old)
                env = dict(os.environ)
                env.pop("QLEISLI_KERNEL", None)
                env.pop("QLEISLI_HIERARCHY_KERNEL", None)
                env["PYTHONDONTWRITEBYTECODE"] = "1"
                env[old.CAPTURE_ENV] = str(native_logs)
                old.write_json(case / "command-before.json", dict(recorded_utc=old.timestamp(), argv=argv,
                    cwd=str(design.REPO), fixed_native_capture_directory=str(native_logs),
                    independent_request_unchanged=action == "request", generated_payload_untrusted=True))
                result = old.capture(argv, design.REPO, env, b"", seconds=55, output_limit=design.LIMIT)
                stdout, stderr = result.pop("stdout"), result.pop("stderr")
                (case / "stdout.bin").write_bytes(stdout)
                (case / "stderr.bin").write_bytes(stderr)
                attempts = sorted(path for path in native_logs.iterdir() if path.is_dir())
                native = []
                for path in attempts:
                    record = json.loads(design.read_bounded(path / "result.json")) if (path / "result.json").exists() else None
                    native.append(dict(directory=str(path), process_started_record=(path / "process-started.json").exists(), result=record))
                actual_calls = sum(item["process_started_record"] for item in native)
                try:
                    api = json.loads(stdout)
                except (ValueError, UnicodeError):
                    api = None
                if actual_calls:
                    stage = "actual-native-process-observed"
                elif attempts:
                    stage = "forwarder-attempt-without-recorded-native-process"
                elif isinstance(api, dict) and api.get("message") == "requested meaning has different child arity":
                    stage = "Rust-pair-construction-rejection-no-forwarder-observed"
                else:
                    stage = "no-forwarder-or-native-process-observed-see-api-error"
                event = dict(recorded_utc=old.timestamp(), width=width, action=action, argv=argv, cwd=str(design.REPO),
                    client_capture=result, api_record=api, raw_stdout=old.describe(case / "stdout.bin"),
                    raw_stderr=old.describe(case / "stderr.bin"), forwarder_attempts=len(attempts), actual_native_calls=actual_calls,
                    native_records=native, observed_stage=stage,
                    stage_scope="Actual logs/API diagnostics only; no inferred source preservation, exact Fourier theorem or proof discharge.")
                old.write_json(case / "result.json", event)
                events.append(event)
                prepared_barrier(args, old)
        old.write_json(OUTPUT / "summary.json", dict(recorded_utc=old.timestamp(),
            status="eight-fixed-adapted-calls-captured", client_observations=len(events),
            actual_native_calls=sum(e["actual_native_calls"] for e in events),
            events=["n" + str(e["width"]) + "-" + e["action"] + "/result.json" for e in events],
            identity_barriers="pass", independent_requests_unchanged=True, expected_outcomes_changed=False,
            source_meaning_verified=False, adapter_preservation_proved=False,
            scope="Capture completion only; unexpected rejection or operational failure remains raw evidence, without repair or retry."))
    except BaseException as error:
        old.write_json(OUTPUT / "aborted.json", dict(recorded_utc=old.timestamp(), completed_observations=len(events),
            error_type=type(error).__name__, message=str(error), note="Partial records retained; no retry, packet or expectation repair."))
        raise


if __name__ == "__main__":
    main()
