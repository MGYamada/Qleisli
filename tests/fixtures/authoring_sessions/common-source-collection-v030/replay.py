#!/usr/bin/env python3
"""Replay the fixed capture only after authorization; verify frozen baseline.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

root = Path(__file__).resolve().parent
repo = root.parents[3]
phase, = sys.argv[1:]
if not re.fullmatch(r"after(?:-[a-z0-9]+)?", phase):
    raise SystemExit("use a distinct after[-label] capture only after root authorization")
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
EXPECTED_BASELINE_MAP = "513ad285040c1292bf3954e5a371d92601e3042625e6ef8af7a0a2fc8c11c924"


def unchanged_baseline():
    assert sha(root / "baseline-files.json") == EXPECTED_BASELINE_MAP
    baseline = json.loads((root / "baseline-files.json").read_text())
    for group in ("files", "frozen_input_files"):
        assert all(sha(root / name) == digest for name, digest in baseline[group].items())


unchanged_baseline()
# A fixed script and validated output label choose the commands; no recorded
# command or metadata-supplied executable is run.
command = [sys.executable, str(root / "capture.py"), phase]
result = subprocess.run(command, cwd=repo)
unchanged_baseline()
raise SystemExit(result.returncode)
