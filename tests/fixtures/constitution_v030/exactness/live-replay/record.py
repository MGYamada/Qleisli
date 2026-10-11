#!/usr/bin/env python3
"""Capture one actual constitutional replay using the existing Lean build.

This driver never builds, changes source or retries. Only hashes, small records
and the requested command's actual output are saved; no source snapshot is made.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
sys.path.insert(0, str(ROOT / "scripts"))
import check_constitution as constitution
import check_initial_guarantees as initial
import check_guarantee_continuity as continuity


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(128 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def save(name, data):
    with (HERE / name).open("x", encoding="utf-8") as output:
        output.write(json.dumps(data, indent=2, sort_keys=True) + "\n")


def identities():
    registry = json.loads((ROOT / "lean/schema-registry.json").read_bytes())
    current = json.loads((ROOT / constitution.CURRENT_PATH).read_bytes())
    paths = set(constitution.FROZEN_PATHS) | set(registry["source_revision"]["files"])
    paths |= set(current["validation"]["files"])
    paths |= {constitution.LEDGER_PATH, constitution.CURRENT_PATH, "lean/schema-registry.json",
              continuity.CURRENT_PATH, str(Path(__file__).resolve().relative_to(ROOT))}
    paths |= {"scripts/" + name for name in (
        "check_constitution.py", "check_guarantee_ledger.py", "check_ratification_packet.py",
        "check_initial_guarantees.py", "check_guarantee_continuity.py", "check_schema_registry.py",
        "check_release_ready.py", "test_check_constitution.py", "test_check_release_ready.py")}
    return {"registry_source_revision": registry["source_revision"]["sha256"],
            "files": {name: digest(ROOT / name) for name in sorted(paths)}}


def main():
    argv = ["python3", "scripts/check_constitution.py", "--base-ref",
            "a26e29bc19e06324e8b394d9d1dbb97ea2d163e1", "--verify-lean"]
    # Exclusive creation makes an accidental second run fail before execution.
    save("command.json", {
        "argv": argv, "cwd": str(ROOT),
        "environment_overrides": {"PYTHONDONTWRITEBYTECODE": "1"},
        "selected_executables": {name: shutil.which(name) for name in ("python3", "lake")},
        "fixed_lean_calls_from_reviewed_code": [initial.REVIEW_ARGV, initial.BINDING_ARGV, continuity.ARGV],
        "fixed_lean_cwd": "lean",
        "scope": "One real replay in the existing built environment; no build, audit rerun, native binary replay or new guarantee discharge.",
    })
    before = identities()
    save("before.json", before)
    started = datetime.now(timezone.utc).isoformat()
    clock = time.monotonic()
    with (HERE / "stdout.txt").open("xb") as stdout, (HERE / "stderr.txt").open("xb") as stderr:
        process = subprocess.run(argv, cwd=ROOT, stdout=stdout, stderr=stderr, check=False,
                                 env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
    seconds = time.monotonic() - clock
    finished = datetime.now(timezone.utc).isoformat()
    after = identities()
    save("after.json", after)
    changed = sorted(name for name in before["files"].keys() | after["files"].keys()
                     if before["files"].get(name) != after["files"].get(name))
    stable = before == after
    result = {
        "format": "qleisli.constitution-live-replay", "version": 1,
        "started_at_utc": started, "finished_at_utc": finished, "seconds": seconds,
        "exit_code": process.returncode, "inputs_unchanged_during_run": stable,
        "changed_inputs": changed, "status": "passed" if process.returncode == 0 and stable else "failed",
        "scope": "Recorded adoption/ledger and the two existing scoped guarantee verifiers, including identity transport. No additional QS/PR/RS discharge, human authentication or release approval.",
        "files": {name: digest(HERE / name) for name in
                  ("record.py", "command.json", "before.json", "after.json", "stdout.txt", "stderr.txt")},
    }
    save("result.json", result)
    print(json.dumps({"status": result["status"], "exit_code": process.returncode,
                      "seconds": seconds, "inputs_unchanged_during_run": stable,
                      "result_sha256": digest(HERE / "result.json")}, sort_keys=True))
    return 0 if result["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
