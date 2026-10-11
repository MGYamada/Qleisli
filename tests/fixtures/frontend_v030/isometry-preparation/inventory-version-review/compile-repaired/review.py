#!/usr/bin/env python3
"""Capture fixed inventory checks and current source identity; never replay records.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[6]
HERE = Path(__file__).resolve().parent
FIXTURES = [
    "tests/fixtures/verification_v022/inventory.json",
    "tests/fixtures/verification_v029/coverage.json",
]
COMMANDS = [
    [sys.executable, "scripts/check_verification_inventory.py"],
    [sys.executable, "scripts/check_production_coverage.py"],
]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def source_map():
    paths = {p for base in ("src", "python/qleisli", "stdlib/src")
             for p in (ROOT / base).rglob("*")
             if p.suffix in (".rs", ".py", ".qli")}
    paths |= {p for p in (ROOT / "lean-kernel").rglob("*.lean")
              if ".lake" not in p.parts}
    return {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in sorted(paths)}


def main():
    if len(sys.argv) != 2 or sys.argv[1] not in (
            "before", "inventory-refreshed", "after"):
        raise SystemExit("choose before, inventory-refreshed or after")
    phase = sys.argv[1]
    folder = HERE / phase
    folder.mkdir(exist_ok=False)
    before = source_map()
    encoded_map = (json.dumps(before, indent=2) + "\n").encode()
    (folder / "source-files.json").write_bytes(encoded_map)
    if phase != "before":
        assert before == json.loads((HERE / "before/source-files.json").read_text()), \
            "source tree changed during inventory review; review the new source first"
    rows = []
    for index, argv in enumerate(COMMANDS):
        started = time.monotonic()
        result = subprocess.run(argv, cwd=ROOT, capture_output=True, timeout=120)
        stdout = f"{index + 1}.stdout.txt"
        stderr = f"{index + 1}.stderr.txt"
        (folder / stdout).write_bytes(result.stdout)
        (folder / stderr).write_bytes(result.stderr)
        rows.append({"argv": argv, "cwd": str(ROOT),
                     "exit_code": result.returncode,
                     "seconds": time.monotonic() - started,
                     "stdout": stdout, "stderr": stderr})
    after = source_map()
    assert after == before, "source tree changed while checks ran"
    record = {"format": "qleisli.isometry-inventory-version-review", "version": 1,
              "phase": phase,
              "observed_at_utc": datetime.now(timezone.utc).isoformat(),
              "driver_sha256": sha(Path(__file__).read_bytes()),
              "source_files": "source-files.json",
              "source_files_sha256": sha(encoded_map),
              "source_tree_unchanged": True,
              "metadata_sha256": {path: sha((ROOT / path).read_bytes())
                                  for path in FIXTURES},
              "commands": rows,
              "scope": "Inventory identities and route metadata only; no Cargo, "
                       "Lean build/replay, source-preservation proof or guarantee admission."}
    (folder / "validation.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"phase": phase,
                      "exit_codes": [row["exit_code"] for row in rows],
                      "source_files_sha256": sha(encoded_map),
                      "source_tree_unchanged": True}))
    return int(any(row["exit_code"] for row in rows))


if __name__ == "__main__":
    raise SystemExit(main())
