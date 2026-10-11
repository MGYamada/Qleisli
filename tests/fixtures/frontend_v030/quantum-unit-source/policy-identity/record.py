#!/usr/bin/env python3
"""Record source-only institutional and inventory checks without rebuilding.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BASE = "d753962de3eedd39629c8441f2b82521ce01d70f"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def selected_inputs():
    paths = set(ROOT.glob("*.md"))
    paths.update(path for path in (ROOT / "governance").rglob("*") if path.is_file())
    paths.update((ROOT / "docs/src").rglob("*.md"))
    paths.update(ROOT / name for name in (
        "scripts/check_constitution.py", "scripts/check_ratification_packet.py",
        "scripts/check_guarantee_ledger.py", "scripts/check_guarantee_continuity.py",
        "scripts/check_initial_guarantees.py", "scripts/check_verification_inventory.py",
        "scripts/check_production_coverage.py", "scripts/check_docs.py",
        "lean/schema-registry.json", "tests/fixtures/verification_v022/inventory.json",
        "tests/fixtures/verification_v029/coverage.json",
        "tests/fixtures/frontend_v030/quantum-unit-source/policy-docs/files.json",
        "tests/fixtures/frontend_v030/quantum-unit-source/policy-docs-final/files.json",
    ))
    inventory = json.loads((ROOT / "tests/fixtures/verification_v022/inventory.json").read_text())
    paths.update(ROOT / entry["path"] for entry in inventory["sources"])
    return {str(path.relative_to(ROOT)): digest(path) for path in sorted(paths)}


def main():
    destination = HERE / "actual"
    destination.mkdir(exist_ok=False)
    before = selected_inputs()
    write(destination / "inputs-before.json", before)
    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    metadata = {
        "scope": "Source/evidence identity, supplied-base continuity, maintained inventory/route metadata and handoff documentation; no fresh proof replay or release approval.",
        "trusted_base": BASE,
        "trusted_base_origin": "Exact previously reviewed commit supplied by the parent task; not inferred from the current checkout.",
        "cwd": str(ROOT),
        "environment_overrides": {"PYTHONDONTWRITEBYTECODE": "1"},
        "recorder_sha256": digest(Path(__file__)),
        "commands": [],
    }
    write(destination / "commands.json", metadata)
    commands = [
        ["python3", "scripts/check_constitution.py", "--base-ref", BASE],
        ["python3", "scripts/check_verification_inventory.py"],
        ["python3", "scripts/check_production_coverage.py"],
        ["python3", "scripts/check_docs.py"],
    ]
    for index, argv in enumerate(commands, 1):
        start = datetime.now(timezone.utc).isoformat()
        clock = time.monotonic()
        result = subprocess.run(argv, cwd=ROOT, env=environment, capture_output=True, check=False)
        elapsed = time.monotonic() - clock
        out, err = destination / f"{index}.stdout.txt", destination / f"{index}.stderr.txt"
        out.write_bytes(result.stdout)
        err.write_bytes(result.stderr)
        metadata["commands"].append({
            "argv": argv, "cwd": str(ROOT), "started_at_utc": start,
            "elapsed_seconds": elapsed, "exit_code": result.returncode,
            "stdout": out.name, "stdout_sha256": digest(out),
            "stderr": err.name, "stderr_sha256": digest(err),
        })
        write(destination / "commands.json", metadata)
        print(f"{index}: exit {result.returncode}: {' '.join(argv)}", flush=True)
    after = selected_inputs()
    write(destination / "inputs-after.json", after)
    changed = [name for name in sorted(before.keys() | after.keys()) if before.get(name) != after.get(name)]
    write(destination / "result.json", {
        "all_commands_passed": all(command["exit_code"] == 0 for command in metadata["commands"]),
        "command_count": len(metadata["commands"]), "trusted_base": BASE,
        "selected_input_scope": "Root Markdown, governance records, book chapters, named checker/registry/inventory/coverage files, every maintained inventory source path and the two prior policy-packet manifests; not the complete repository.",
        "selected_inputs_count": len(before), "selected_inputs_changed": changed,
        "commands_sha256": digest(destination / "commands.json"),
        "inputs_before_sha256": digest(destination / "inputs-before.json"),
        "inputs_after_sha256": digest(destination / "inputs-after.json"),
        "fresh_lean_replay": False, "rust_or_lean_build": False,
    })


if __name__ == "__main__":
    main()
