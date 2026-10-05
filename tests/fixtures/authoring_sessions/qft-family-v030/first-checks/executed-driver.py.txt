#!/usr/bin/env python3
"""Fixed bounded QFT checks; recorded metadata never chooses commands.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""

import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

root = Path(__file__).resolve().parent
repo = root.parents[3]
identity = json.loads((root / "identity-before.json").read_text())
binary = Path("/private/tmp/qleisli-bounded-validation-target/debug/qleisli")
native = repo / "lean-kernel/.lake/build/bin/qleisli-kernel"
wrapper = root / "native-log.py"
source = root / "attempt-01/transform.qli"
records = root / "first-checks"
records.mkdir()
digest = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
frozen = json.loads((root / "first-files.json").read_text())["files"]


def unchanged():
    assert digest(binary) == identity["cli_sha256"], "CLI identity changed"
    assert digest(native) == identity["native_sha256"], "native identity changed"
    assert all(digest(root / name) == sha for name, sha in frozen.items())
    assert all(digest(repo / name) == sha for name, sha in identity["source_files"].items())
    assert all(digest(repo / name) == sha for name, sha in identity["current_stdlib_sources"].items())


unchanged()
(records / "executed-driver.py.txt").write_bytes(Path(__file__).read_bytes())
help_command = [str(binary), "--help"]
help_result = subprocess.run(help_command, cwd=repo, capture_output=True, timeout=10)
(records / "help.stdout.txt").write_bytes(help_result.stdout)
(records / "help.stderr.txt").write_bytes(help_result.stderr)
(records / "help.json").write_text(json.dumps({
    "command": help_command, "exit_code": help_result.returncode,
    "recorded_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "stdout": "help.stdout.txt", "stderr": "help.stderr.txt",
}, indent=2) + "\n")
assert help_result.returncode == 0
assert b"--module=NAME=PATH" in help_result.stdout
session_path = root / "session.json"
session = json.loads(session_path.read_text())
attempt = session["attempts"][0]
assert not attempt["observations"], "first-check directory is one capture only"
for n in range(4):
    for presentation in ("text", "json"):
        unchanged()
        label = f"n{n}-{presentation}"
        native_log = records / (label + ".native.jsonl")
        native_log.touch()
        command = [str(binary), "check", "--entry=transform::qft",
                   "--module=transform=" + str(source), "--nat=n=" + str(n),
                   "--lean-kernel=" + str(wrapper)]
        if presentation == "json":
            command.append("--format=json")
        env = dict(os.environ, QLEISLI_STUDY_NATIVE=str(native),
                   QLEISLI_STUDY_NATIVE_LOG=str(native_log))
        start = time.monotonic()
        result = subprocess.run(command, cwd=repo, env=env,
                                capture_output=True, timeout=60)
        (records / (label + ".stdout.txt")).write_bytes(result.stdout)
        (records / (label + ".stderr.txt")).write_bytes(result.stderr)
        event = {"command": command, "exit_code": result.returncode,
                 "stderr": result.stderr.decode(),
                 "native_invocations": len(native_log.read_text().splitlines()),
                 "seconds": time.monotonic() - start,
                 "recorded_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                 "timestamp_note": "Clock after completion; not authenticated provenance."}
        if presentation == "json":
            event["stdout"] = json.loads(result.stdout)
        else:
            event["transcript"] = result.stdout.decode() + result.stderr.decode()
        path = records / (label + ".json")
        path.write_text(json.dumps(event, indent=2) + "\n")
        attempt["observations"].append(str(path.relative_to(root)))
        session_path.write_text(json.dumps(session, indent=2) + "\n")
        unchanged()
        print(label, result.returncode, event["native_invocations"], flush=True)
unchanged()
