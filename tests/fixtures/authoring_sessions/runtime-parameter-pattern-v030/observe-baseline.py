#!/usr/bin/env python3
"""Observe fixed small first sources with an existing CLI; never build or repair.
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


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    identity = json.loads((HERE / "identity-before.json").read_text())
    first = json.loads((HERE / "first-files.json").read_text())["files"]
    for name, digest in first.items():
        assert sha(HERE / name) == digest, name
    binary = Path(identity["binary"]["path"])
    kernel = Path(identity["kernel"]["path"])
    assert sha(binary) == identity["binary"]["sha256"]
    assert sha(kernel) == identity["kernel"]["sha256"]
    rows = json.loads((HERE / "projects.json").read_text())
    rows += json.loads((HERE / "additional-projects.json").read_text())
    (HERE / "observations").mkdir(exist_ok=False)
    results = []
    for row in rows:
        project = HERE / row["path"]
        commands = [("finite", [str(binary), "check", str(project), "--format=json"])]
        if row["sized"]:
            commands.append(("sized", [
                str(binary), "sized", "check", "--entry=main::f",
                f"--module=main={project / 'main.qli'}", f"--kernel={kernel}",
                *row["sized_arguments"],
            ]))
        for profile, command in commands:
            started = time.monotonic()
            result = subprocess.run(
                command, cwd=ROOT, capture_output=True, timeout=45,
                env=os.environ | {"QLEISLI_KERNEL": str(kernel)},
            )
            record = dict(
                command=command, cwd=str(ROOT), exit_code=result.returncode,
                recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                elapsed_seconds=time.monotonic() - started,
                stdout_raw=result.stdout.decode(), stderr=result.stderr.decode(),
                source_sha256=row["source_sha256"], manifest_sha256=row["manifest_sha256"],
                binary_sha256=sha(binary), kernel_sha256=sha(kernel), profile=profile,
            )
            if profile == "finite":
                record["stdout"] = json.loads(result.stdout)
            else:
                record["transcript"] = record["stdout_raw"] + record["stderr"]
            name = f"observations/{profile}-{row['category']}-{row['name']}.json"
            (HERE / name).write_text(json.dumps(record, indent=2) + "\n")
            results.append(dict(profile=profile, project=row["path"],
                                exit_code=result.returncode, observation=name))
            print(profile, row["path"], result.returncode, flush=True)
    for name, digest in first.items():
        assert sha(HERE / name) == digest, name
    after = {name: sha(ROOT / name) for name in identity["current_source_sha256"]}
    assert after == identity["current_source_sha256"]
    assert sha(binary) == identity["binary"]["sha256"]
    assert sha(kernel) == identity["kernel"]["sha256"]
    summary = dict(
        status="observed", commands=results, sources_and_executables_unchanged=True,
        current_source_sha256_after=after,
        scope="Actual first diagnostics from fixed small CLI checks. Rejections and unsupported profiles are retained; no Cargo/Lean build or semantic correctness claim.",
    )
    (HERE / "baseline-summary.json").write_text(json.dumps(summary, indent=2) + "\n")


if __name__ == "__main__":
    main()
