#!/usr/bin/env python3
"""Validate the actual task manifest without invoking the native CI harness.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(ROOT / "scripts"))
from run_native_ci import MANIFEST, load_tasks

tasks = load_tasks(MANIFEST)
print(json.dumps({
    "mode": "selected-function-only",
    "function": "run_native_ci.load_tasks",
    "manifest": str(MANIFEST.relative_to(ROOT)),
    "manifest_sha256": hashlib.sha256(MANIFEST.read_bytes()).hexdigest(),
    "task_count": len(tasks),
    "command_count": sum(len(task["commands"]) for task in tasks),
    "quantum_unit_source_commands": [
        {"task_id": task["id"], "argv": command}
        for task in tasks for command in task["commands"]
        if "quantum_unit_source" in command
    ],
    "native_build_or_comparison_execution": False,
}, indent=2))
