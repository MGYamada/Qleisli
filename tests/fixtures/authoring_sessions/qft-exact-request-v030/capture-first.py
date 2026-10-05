#!/usr/bin/env python3
"""Four fixed untrusted QFT emissions; no native or request checking.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""

import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


PACKET = Path(__file__).resolve().parent
REPO = PACKET.parents[3]
CLI = Path("/private/tmp/qleisli-bounded-validation-target/debug/qleisli")
NATIVE = REPO / "lean-kernel/.lake/build/bin/qleisli-kernel"
SOURCE = PACKET / "attempt-01/transform.qli"
RECORDS = PACKET / "first-emissions"
SENTINEL = PACKET / "native-sentinel.py"
WIDTHS = (0, 1, 2, 3)


def timestamp():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def digest(path):
    sha = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            sha.update(block)
    return sha.hexdigest()


def describe(path, base):
    return {
        "path": str(path.relative_to(base)),
        "bytes": path.stat().st_size,
        "sha256": digest(path),
    }


def write_json(path, value):
    with path.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(value, indent=2) + "\n")


def local(base, name):
    path = (base / name).resolve()
    path.relative_to(base.resolve())
    return path


def rust_inventory():
    return sorted(str(path.relative_to(REPO)) for path in (REPO / "src").rglob("*.rs"))


def lean_inventory():
    paths = []
    for directory, children, files in os.walk(REPO / "lean-kernel"):
        children[:] = sorted(name for name in children if name != ".lake")
        paths.extend(
            str((Path(directory) / name).relative_to(REPO))
            for name in files if name.endswith(".lean")
        )
    return sorted(paths)


def stdlib_inventory():
    return sorted(
        str(path.relative_to(REPO))
        for path in (REPO / "stdlib").rglob("*")
        if path.is_file() and (path.suffix == ".qli" or path.name == "Qargo.toml")
    )


def unchanged(identity, first_files):
    if digest(CLI) != identity["cli"]["sha256"]:
        raise RuntimeError("fixed CLI bytes changed before or during FIRST capture")
    if digest(NATIVE) != identity["native"]["sha256"]:
        raise RuntimeError("observed native bytes changed before or during FIRST capture")
    inventories = {
        "rust_sources": rust_inventory(),
        "lean_sources": lean_inventory(),
        "stdlib_inputs": stdlib_inventory(),
    }
    if inventories != identity["inventories"]:
        raise RuntimeError("declared source inventory changed")
    for row in identity["files"]:
        path = local(REPO, row["path"])
        if path.stat().st_size != row["bytes"] or digest(path) != row["sha256"]:
            raise RuntimeError("source/dependency identity changed: " + row["path"])
    for row in first_files["files"]:
        path = local(PACKET, row["path"])
        if path.stat().st_size != row["bytes"] or digest(path) != row["sha256"]:
            raise RuntimeError("frozen first packet changed: " + row["path"])
        if path.stat().st_mode & 0o777 != row["mode"]:
            raise RuntimeError("frozen first packet file mode changed: " + row["path"])
    if not os.access(SENTINEL, os.X_OK):
        raise RuntimeError("fixed native sentinel is not executable")


def command(width):
    # This fixed code chooses argv. Neither fixture nor artifact metadata can
    # choose an executable, width, command, request or native checker.
    return [
        str(CLI),
        "emit-proposal",
        "--entry=transform::qft",
        "--module=transform=" + str(SOURCE),
        "--nat=n=" + str(width),
        "--ir-profile=hierarchy",
        "--output=" + str(RECORDS / ("n" + str(width) + ".proposal.json")),
        "--format=json",
    ]


def main():
    # A capture directory is never reused or overwritten, including a failed
    # first capture. A later authorized repetition needs a separate driver/dir.
    RECORDS.mkdir()
    write_json(RECORDS / "started.json", {
        "recorded_utc": timestamp(),
        "widths": list(WIDTHS),
        "operation": "untrusted-emission-only",
        "native_checker_requested": False,
        "request_check_performed": False,
    })
    (RECORDS / "executed-driver.py.txt").write_bytes(Path(__file__).read_bytes())
    native_log = RECORDS / "native-attempts.jsonl"
    native_log.touch()
    events = []
    try:
        identity = json.loads((PACKET / "identity-before.json").read_text())
        first_files = json.loads((PACKET / "first-files.json").read_text())
        session = json.loads((PACKET / "session-before.json").read_text())
        if (PACKET / "session.json").exists():
            raise RuntimeError("live session already exists; FIRST capture is one-shot")
        unchanged(identity, first_files)
        write_json(RECORDS / "input-identities.json", {
            "identity_before": describe(PACKET / "identity-before.json", PACKET),
            "first_files": describe(PACKET / "first-files.json", PACKET),
            "cli_sha256": digest(CLI),
            "native_sha256": digest(NATIVE),
            "native_sentinel": describe(SENTINEL, PACKET),
            "native_environment": {
                "QLEISLI_KERNEL": str(SENTINEL),
                "QLEISLI_HIERARCHY_KERNEL": str(SENTINEL),
            },
            "note": "Byte observations and hash barriers, not build-to-HEAD attestation.",
        })
        env = dict(os.environ)
        env["QLEISLI_KERNEL"] = str(SENTINEL)
        env["QLEISLI_HIERARCHY_KERNEL"] = str(SENTINEL)
        for width in WIDTHS:
            unchanged(identity, first_files)
            argv = command(width)
            label = "n" + str(width)
            started = timestamp()
            begin = time.monotonic()
            execution_error = None
            native_before = native_log.read_bytes()
            try:
                result = subprocess.run(argv, cwd=REPO, env=env, capture_output=True, timeout=60)
                stdout, stderr, code = result.stdout, result.stderr, result.returncode
            except subprocess.TimeoutExpired as error:
                stdout, stderr, code = error.stdout or b"", error.stderr or b"", None
                execution_error = {"kind": "timeout", "seconds": 60}
            except OSError as error:
                stdout, stderr, code = b"", b"", None
                execution_error = {"kind": "spawn-error", "message": str(error)}
            stdout_path = RECORDS / (label + ".stdout.txt")
            stderr_path = RECORDS / (label + ".stderr.txt")
            stdout_path.write_bytes(stdout)
            stderr_path.write_bytes(stderr)
            native_after = native_log.read_bytes()
            if not native_after.startswith(native_before):
                raise RuntimeError("native sentinel log was changed instead of appended")
            native_delta = native_after[len(native_before):]
            native_case = RECORDS / (label + ".native.jsonl")
            native_case.write_bytes(native_delta)
            proposal_path = RECORDS / (label + ".proposal.json")
            event = {
                "command": argv,
                "cwd": str(REPO),
                "width": width,
                "started_utc": started,
                "recorded_utc": timestamp(),
                "timestamp_note": "Local clock only; not authenticated provenance.",
                "exit_code": code,
                "execution_error": execution_error,
                "seconds": time.monotonic() - begin,
                "raw_stdout": describe(stdout_path, PACKET),
                "raw_stderr": describe(stderr_path, PACKET),
                "stderr": stderr.decode("utf-8", errors="replace"),
                "proposal": describe(proposal_path, PACKET) if proposal_path.exists() else None,
                "proposal_status": "untrusted-output" if proposal_path.exists() else "absent",
                "native_checker_requested": False,
                "native_environment": {
                    "QLEISLI_KERNEL": str(SENTINEL),
                    "QLEISLI_HIERARCHY_KERNEL": str(SENTINEL),
                },
                "native_attempts_observed": len(native_delta.splitlines()),
                "native_attempt_log": describe(native_case, PACKET),
                "native_monitor_scope": "Calls selecting the fixed sentinel through the two recorded kernel environment variables; not a system-wide process trace.",
                "actual_native_checker_forwarded": False,
                "request_check_performed": False,
            }
            try:
                event["stdout"] = json.loads(stdout)
            except (ValueError, UnicodeError):
                event["transcript"] = (stdout + stderr).decode("utf-8", errors="replace")
            if code is not None:
                session["attempts"][0]["observations"].append(
                    "first-emissions/" + label + ".json"
                )
            event_path = RECORDS / (label + ".json")
            write_json(event_path, event)
            events.append(str(event_path.relative_to(PACKET)))
            # First metadata is immutable; only this new append-only observation
            # index receives actual completed-process observations.
            (PACKET / "session.json").write_text(json.dumps(session, indent=2) + "\n")
            unchanged(identity, first_files)
            print(label, "exit", code, "untrusted-proposal", proposal_path.exists(), flush=True)
        unchanged(identity, first_files)
        write_json(RECORDS / "summary.json", {
            "recorded_utc": timestamp(),
            "status": "four-fixed-emission-calls-captured",
            "events": events,
            "identity_barriers": "pass",
            "checked_or_executed_meaning": False,
            "independent_requests_used": False,
            "native_attempts_observed": len(native_log.read_bytes().splitlines()),
            "actual_native_checker_forwarded": False,
        })
    except Exception as error:
        write_json(RECORDS / "capture-failure.json", {
            "recorded_utc": timestamp(),
            "kind": type(error).__name__,
            "message": str(error),
            "completed_event_records": events,
            "note": "Original logs/output and failed FIRST directory are retained; no rebinding or retry.",
        })
        raise


if __name__ == "__main__":
    main()
