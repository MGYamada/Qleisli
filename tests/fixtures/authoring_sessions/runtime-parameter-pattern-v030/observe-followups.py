#!/usr/bin/env python3
"""Preserve explicit follow-up checks and three unchanged named-control IRs.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
identity = json.loads((HERE / "identity-before.json").read_text())
binary, kernel = (Path(identity[key]["path"]) for key in ("binary", "kernel"))
assert sha(binary) == identity["binary"]["sha256"]
assert sha(kernel) == identity["kernel"]["sha256"]
projects = json.loads((HERE / "followup-projects.json").read_text())["projects"]
for row in projects:
    assert sha(HERE / row["path"] / "main.qli") == row["source_sha256"]
    assert sha(HERE / row["path"] / "Qargo.toml") == row["manifest_sha256"]
(HERE / "baseline-artifacts").mkdir(exist_ok=False)
calls = []
for row in projects:
    project = HERE / row["path"]
    calls.append((row["name"], "finite", [str(binary), "check", str(project), "--format=json"]))
    if not row["name"].startswith("closed-"):
        calls.append((row["name"], "sized", [
            str(binary), "sized", "check", "--entry=main::f",
            f"--module=main={project / 'main.qli'}", f"--kernel={kernel}",
        ]))
for name, project in [
    ("closed-named-unit", HERE / "followups/closed-named-unit"),
    ("closed-named-swap", HERE / "followups/closed-named-swap"),
    ("named-effectful-unit", HERE / "controls/named-effectful-unit"),
]:
    calls.append((name, "emit-ir", [str(binary), "emit-ir", str(project),
                                    f"--output={HERE / 'baseline-artifacts' / (name + '.qirf.json')}"]))
results = []
for name, mode, command in calls:
    started = time.monotonic()
    result = subprocess.run(command, cwd=ROOT, capture_output=True, timeout=45,
                            env=os.environ | {"QLEISLI_KERNEL": str(kernel)})
    record = dict(command=command, cwd=str(ROOT), exit_code=result.returncode,
                  recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  elapsed_seconds=time.monotonic() - started,
                  stdout_raw=result.stdout.decode(), stderr=result.stderr.decode(),
                  binary_sha256=sha(binary), kernel_sha256=sha(kernel))
    if mode == "finite":
        record["stdout"] = json.loads(result.stdout)
    else:
        record["transcript"] = record["stdout_raw"] + record["stderr"]
    artifact = HERE / "baseline-artifacts" / (name + ".qirf.json")
    if mode == "emit-ir" and artifact.exists():
        record["artifact"] = {"path": artifact.relative_to(HERE).as_posix(), "sha256": sha(artifact)}
    output = HERE / "observations" / f"followup-{mode}-{name}.json"
    assert not output.exists()
    output.write_text(json.dumps(record, indent=2) + "\n")
    results.append({"name": name, "mode": mode, "exit_code": result.returncode,
                    "observation": output.relative_to(HERE).as_posix()})
    print(name, mode, result.returncode, flush=True)
assert sha(binary) == identity["binary"]["sha256"]
assert sha(kernel) == identity["kernel"]["sha256"]
for row in projects:
    assert sha(HERE / row["path"] / "main.qli") == row["source_sha256"]
    assert sha(HERE / row["path"] / "Qargo.toml") == row["manifest_sha256"]
(HERE / "followup-summary.json").write_text(json.dumps({
    "status": "observed", "commands": results, "sources_and_executables_unchanged": True,
    "scope": "Reuse the frozen prior CLI while production edits may begin. No current-working-tree rebuild or full source stability claim.",
}, indent=2) + "\n")
