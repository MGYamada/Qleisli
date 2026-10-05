#!/usr/bin/env python3
"""Fixed original-QFT native logging forwarder; no acceptance authority.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import datetime
import hashlib
import json
import os
from pathlib import Path
import selectors
import sys
import time

sys.dont_write_bytecode = True
from bounded_process import capture

REPO = Path(__file__).resolve().parents[5]
NATIVE = REPO / "lean-kernel/.lake/build/bin/qleisli-kernel"
NATIVE_SHA256 = "39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85"
ALLOWED = {(mode, "0.3.0-alpha") for mode in (
    "--hierarchy-pending", "--hierarchy-request-pending", "--hierarchy-fourier-pending",
)}
INPUT_LIMIT = 1 << 20
OUTPUT_LIMIT = 1 << 20
CAPTURE_ENV = "QLEISLI_QFT_NATIVE_CAPTURE_DIRECTORY"


def timestamp():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def digest(path):
    sha = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            sha.update(block)
    return sha.hexdigest()


def write_json(path, value):
    with path.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(value, indent=2) + "\n")


def input_bytes():
    data = bytearray()
    deadline = time.monotonic() + 5
    selector = selectors.DefaultSelector()
    descriptor = sys.stdin.fileno()
    os.set_blocking(descriptor, False)
    selector.register(descriptor, selectors.EVENT_READ)
    try:
        while True:
            remaining = deadline-time.monotonic()
            if remaining <= 0:
                return bytes(data), "input-timeout"
            if not selector.select(min(0.1, remaining)):
                continue
            try:
                block = os.read(descriptor, min(65536, INPUT_LIMIT+1-len(data)))
            except BlockingIOError:
                continue
            if not block:
                return bytes(data), None
            data.extend(block)
            if len(data) > INPUT_LIMIT:
                return bytes(data), "input-limit"
    finally:
        selector.close()


def main():
    if sys.version_info < (3, 11):
        raise RuntimeError("development Python 3.11 or newer is required")
    destination = Path(os.environ[CAPTURE_ENV])
    if not destination.is_absolute() or not destination.is_dir():
        raise RuntimeError("caller must select an existing absolute capture directory")
    # One invocation is expected per current API action. A second is retained
    # and refused rather than silently generating unbounded records/processes.
    call = destination / "call-01"
    try:
        call.mkdir()
        ordinal = 1
    except FileExistsError:
        call = destination / "call-02-refused"
        call.mkdir()
        ordinal = 2
    args = tuple(sys.argv[1:])
    event = dict(started_utc=timestamp(), wrapper_argv=sys.argv,
                 requested_native_argv=[str(NATIVE), *args], ordinal=ordinal,
                 actual_native_spawned=False, actual_native_returncode=None,
                 interpreter=sys.executable, python_version=sys.version,
                 identity_scope="File observations only, not running-image/build attestation.")
    write_json(call / "attempt.json", event)
    data, input_error = input_bytes()
    (call / "stdin.bin").write_bytes(data)
    event["stdin_bytes"] = len(data)
    event["stdin_sha256"] = hashlib.sha256(data).hexdigest()
    event["stdin_limited_prefix"] = input_error == "input-limit"
    rejection = input_error
    if ordinal != 1:
        rejection = "unexpected-second-forwarder-invocation"
    elif args not in ALLOWED:
        rejection = "mode-version-refused"
    elif rejection is None and digest(NATIVE) != NATIVE_SHA256:
        rejection = "native-identity-changed"
    if rejection is not None:
        stderr = ("fixed native forwarder refused: " + rejection + "\n").encode()
        (call / "stdout.bin").write_bytes(b"")
        (call / "stderr.bin").write_bytes(stderr)
        event.update(finished_utc=timestamp(), wrapper_rejection=rejection,
                     wrapper_exit_code=97, native_identity_checked=False)
        write_json(call / "result.json", event)
        sys.stderr.buffer.write(stderr)
        return 97

    def spawned(pid):
        write_json(call / "process-started.json", dict(
            recorded_utc=timestamp(), pid=pid, argv=[str(NATIVE), *args],
            native_sha256_before=NATIVE_SHA256,
        ))

    result = capture([str(NATIVE), *args], REPO, dict(os.environ), data,
                     seconds=45, output_limit=OUTPUT_LIMIT, on_spawn=spawned)
    stdout, stderr = result.pop("stdout"), result.pop("stderr")
    (call / "stdout.bin").write_bytes(stdout)
    (call / "stderr.bin").write_bytes(stderr)
    identity_after = digest(NATIVE)
    event.update(finished_utc=timestamp(), capture=result,
                 actual_native_spawned=result["spawned"],
                 actual_native_returncode=result["returncode"],
                 native_sha256_before=NATIVE_SHA256, native_sha256_after=identity_after,
                 stdout_bytes=len(stdout), stderr_bytes=len(stderr),
                 stdout_sha256=hashlib.sha256(stdout).hexdigest(),
                 stderr_sha256=hashlib.sha256(stderr).hexdigest())
    if identity_after != NATIVE_SHA256:
        exit_code = 97
        event["wrapper_rejection"] = "native-identity-changed-after-invocation"
    elif result["reason"] == "timeout":
        exit_code = 124
    elif result["reason"] == "output-limit":
        exit_code = 98
    elif not result["spawned"]:
        exit_code = 127
    else:
        code = result["returncode"]
        exit_code = code if code >= 0 else 128-code
    event["wrapper_exit_code"] = exit_code
    write_json(call / "result.json", event)
    sys.stdout.buffer.write(stdout)
    sys.stderr.buffer.write(stderr)
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
