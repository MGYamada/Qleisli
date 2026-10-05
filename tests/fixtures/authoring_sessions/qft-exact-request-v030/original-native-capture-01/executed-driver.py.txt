#!/usr/bin/env python3
"""Exactly eight original-payload inspect/request observations; no adapters.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import sys

sys.dont_write_bytecode = True
from bounded_process import capture

DESIGN = Path(__file__).resolve().parent
REPO = DESIGN.parents[4]
SESSION = REPO / "tests/fixtures/authoring_sessions/qft-exact-request-v030"
OUTPUT = SESSION / "original-native-capture-01"
CLIENT = Path("/private/tmp/qleisli-bounded-validation-target/debug/qleisli-qft-native-gate-design")
ROOT_OBSERVED_CLIENT_SHA256 = "683b29749f752652b3ddb8dba7fac0ea2d832f848178963f3056d2f5c03d8294"
NATIVE = REPO / "lean-kernel/.lake/build/bin/qleisli-kernel"
NATIVE_SHA256 = "39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85"
FORWARDER = DESIGN / "log-native.py"
CAPTURE_ENV = "QLEISLI_QFT_NATIVE_CAPTURE_DIRECTORY"
WIDTHS = (0, 1, 2, 3)


def timestamp():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def digest(path):
    sha = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            sha.update(block)
    return sha.hexdigest()


def describe(path):
    return dict(path=str(path), bytes=path.stat().st_size, sha256=digest(path))


def write_json(path, value):
    with path.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(value, indent=2) + "\n")


def local(name):
    path = (REPO / name).resolve()
    path.relative_to(REPO)
    return path


def inventories():
    rust = sorted(str(path.relative_to(REPO)) for path in (REPO / "src").rglob("*.rs"))
    lean = []
    for directory, children, files in os.walk(REPO / "lean-kernel"):
        children[:] = sorted(name for name in children if name != ".lake")
        lean.extend(str((Path(directory) / name).relative_to(REPO))
                    for name in files if name.endswith(".lean"))
    std = sorted(str(path.relative_to(REPO)) for path in (REPO / "stdlib").rglob("*")
                 if path.is_file() and (path.suffix == ".qli" or path.name == "Qargo.toml"))
    return dict(rust_sources=rust, lean_sources=sorted(lean), stdlib_inputs=std)


def barrier(args, fixed, first_identity):
    if args.client_sha256 != ROOT_OBSERVED_CLIENT_SHA256 or digest(CLIENT) != args.client_sha256:
        raise RuntimeError("explicit root-reviewed client hash barrier failed")
    if digest(DESIGN / "capture-inputs.json") != args.capture_inputs_sha256:
        raise RuntimeError("explicit reviewed capture-input map hash barrier failed")
    if digest(NATIVE) != NATIVE_SHA256:
        raise RuntimeError("fixed native bytes changed")
    for row in fixed["files"]:
        path = local(row["path"])
        if path.stat().st_size != row["bytes"] or digest(path) != row["sha256"]:
            raise RuntimeError("frozen capture input changed: " + row["path"])
        if path.stat().st_mode & 0o777 != row["mode"]:
            raise RuntimeError("frozen capture input mode changed: " + row["path"])
    if inventories() != first_identity["inventories"]:
        raise RuntimeError("FIRST source inventory changed")
    for row in first_identity["files"]:
        path = local(row["path"])
        if path.stat().st_size != row["bytes"] or digest(path) != row["sha256"]:
            raise RuntimeError("FIRST declared identity changed: " + row["path"])
    for label, path in [("cli", Path(first_identity["cli"]["path"])), ("native", NATIVE)]:
        if digest(path) != first_identity[label]["sha256"]:
            raise RuntimeError("FIRST binary file changed: " + label)
    if not os.access(CLIENT, os.X_OK) or not os.access(FORWARDER, os.X_OK):
        raise RuntimeError("client or fixed forwarder is not executable")


def command(width, action):
    payload = SESSION / "first-emissions" / ("n" + str(width) + ".proposal.json")
    argv = [str(CLIENT), action, str(FORWARDER), str(payload)]
    if action == "request":
        argv.append(str(SESSION / "requests" / ("n" + str(width) + ".json")))
    return argv


def main():
    if sys.version_info < (3, 11):
        raise RuntimeError("development Python 3.11 or newer is required")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--client-sha256", required=True)
    parser.add_argument("--capture-inputs-sha256", required=True)
    args = parser.parse_args()
    if any(len(value) != 64 or any(c not in "0123456789abcdef" for c in value)
           for value in (args.client_sha256, args.capture_inputs_sha256)):
        parser.error("reviewed SHA-256 arguments must be 64 lowercase hexadecimal digits")
    OUTPUT.mkdir()
    write_json(OUTPUT / "started.json", dict(
        recorded_utc=timestamp(), widths=list(WIDTHS), actions=["inspect", "request"],
        reviewed_client_sha256=args.client_sha256,
        reviewed_capture_inputs_sha256=args.capture_inputs_sha256,
        status="capture-started-no-outcome-predicted",
    ))
    (OUTPUT / "executed-driver.py.txt").write_bytes(Path(__file__).read_bytes())
    (OUTPUT / "executed-forwarder.py.txt").write_bytes(FORWARDER.read_bytes())
    (OUTPUT / "executed-bounded-process.py.txt").write_bytes((DESIGN / "bounded_process.py").read_bytes())
    events = []
    try:
        fixed = json.loads((DESIGN / "capture-inputs.json").read_bytes())
        first_identity = json.loads((SESSION / "identity-before.json").read_bytes())
        barrier(args, fixed, first_identity)
        write_json(OUTPUT / "observed-inputs.json", dict(
            recorded_utc=timestamp(), client=describe(CLIENT), native=describe(NATIVE),
            capture_inputs=describe(DESIGN / "capture-inputs.json"),
            interpreter=sys.executable, python_version=sys.version,
            scope="File observations and barriers; not compiled-HEAD/running-image attestation.",
        ))
        for width in WIDTHS:
            for action in ("inspect", "request"):
                barrier(args, fixed, first_identity)
                label = "n" + str(width) + "-" + action
                case = OUTPUT / label
                case.mkdir()
                native_logs = case / "native"
                native_logs.mkdir()
                argv = command(width, action)
                env = dict(os.environ)
                env.pop("QLEISLI_KERNEL", None)
                env.pop("QLEISLI_HIERARCHY_KERNEL", None)
                env["PYTHONDONTWRITEBYTECODE"] = "1"
                env[CAPTURE_ENV] = str(native_logs)
                write_json(case / "command-before.json", dict(
                    recorded_utc=timestamp(), argv=argv, cwd=str(REPO),
                    fixed_native_capture_directory=str(native_logs),
                    independent_request_unchanged=action == "request",
                ))
                result = capture(argv, REPO, env, b"", seconds=55, output_limit=1 << 20)
                stdout, stderr = result.pop("stdout"), result.pop("stderr")
                (case / "stdout.bin").write_bytes(stdout)
                (case / "stderr.bin").write_bytes(stderr)
                attempts = sorted(path for path in native_logs.iterdir() if path.is_dir())
                native = []
                for path in attempts:
                    record = json.loads((path / "result.json").read_bytes()) if (path / "result.json").exists() else None
                    native.append(dict(directory=str(path),
                                       process_started_record=(path / "process-started.json").exists(),
                                       result=record))
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
                event = dict(recorded_utc=timestamp(), width=width, action=action,
                             argv=argv, cwd=str(REPO), client_capture=result, api_record=api,
                             raw_stdout=describe(case / "stdout.bin"),
                             raw_stderr=describe(case / "stderr.bin"),
                             forwarder_attempts=len(attempts), actual_native_calls=actual_calls,
                             native_records=native, observed_stage=stage,
                             stage_scope="Logs and exact API diagnostic only; no inferred success or source preservation.")
                write_json(case / "result.json", event)
                events.append(event)
                barrier(args, fixed, first_identity)
        write_json(OUTPUT / "summary.json", dict(
            recorded_utc=timestamp(), status="eight-fixed-original-calls-captured",
            client_observations=len(events), actual_native_calls=sum(e["actual_native_calls"] for e in events),
            events=["n" + str(e["width"]) + "-" + e["action"] + "/result.json" for e in events],
            identity_barriers="pass", adapter_or_mutant_created=False,
            expected_outcomes_changed=False, source_meaning_verified=False,
            scope="Capture completion only; request rejection is retained data, not recorder failure or proof.",
        ))
    except BaseException as error:
        write_json(OUTPUT / "aborted.json", dict(
            recorded_utc=timestamp(), completed_observations=len(events),
            error_type=type(error).__name__, message=str(error),
            note="No retry, packet rewrite, adapter or expectation repair was attempted.",
        ))
        raise


if __name__ == "__main__":
    main()
