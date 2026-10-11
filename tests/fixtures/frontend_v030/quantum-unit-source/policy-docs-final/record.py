#!/usr/bin/env python3
"""Record documentation checks after the primitive catalog count correction.

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
MDBOOK = Path("/private/tmp/qleisli-mdbook-0.5.4-bin/mdbook")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def selected_inputs():
    paths = set(ROOT.glob("*.md"))
    paths.update((ROOT / "docs/src").rglob("*.md"))
    paths.update(ROOT / name for name in (
        "docs/book.toml", "scripts/check_docs.py", "scripts/check_book.py",
        "src/frontend/core.rs", "src/frontend/sized/primitive.rs",
        "tests/fixtures/frontend_v030/quantum-unit-source/policy-docs/files.json",
    ))
    return {str(path.relative_to(ROOT)): digest(path) for path in sorted(paths)}


def main():
    destination = HERE / "actual"
    destination.mkdir(exist_ok=False)
    before = selected_inputs()
    write(destination / "inputs-before.json", before)
    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    metadata = {
        "scope": "Documentation and rendered-link validation only, after the 14 sized / six overlapping catalog count correction.",
        "cwd": str(ROOT),
        "environment_overrides": {"PYTHONDONTWRITEBYTECODE": "1"},
        "recorder_sha256": digest(Path(__file__)),
        "mdbook": {"path": str(MDBOOK), "sha256": digest(MDBOOK)},
        "commands": [],
    }
    write(destination / "commands.json", metadata)
    commands = [
        ["python3", "scripts/check_docs.py"],
        [str(MDBOOK), "--version"],
        [str(MDBOOK), "build", "docs"],
        ["python3", "scripts/check_book.py"],
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
        "command_count": len(metadata["commands"]),
        "selected_input_scope": "Root Markdown, mdBook chapter/configuration files, documentation checkers, the two named catalog sources and the prior frozen policy-doc manifest; not the complete repository.",
        "selected_inputs_count": len(before), "selected_inputs_changed": changed,
        "commands_sha256": digest(destination / "commands.json"),
        "inputs_before_sha256": digest(destination / "inputs-before.json"),
        "inputs_after_sha256": digest(destination / "inputs-after.json"),
        "authoring_or_scheduler_tests_repeated": False,
        "rust_or_lean_build": False,
    })


if __name__ == "__main__":
    main()
