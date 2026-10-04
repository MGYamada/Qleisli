#!/usr/bin/env python3
"""Observe frozen small sources with prior executables; no builds or repairs.
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
    frozen = json.loads((HERE / "first-files.json").read_text())["files"]
    for name, digest in frozen.items():
        assert sha(HERE / name) == digest, name
    binary, kernel = (Path(identity[key]["path"]) for key in ("binary", "kernel"))
    assert sha(binary) == identity["binary"]["sha256"]
    assert sha(kernel) == identity["kernel"]["sha256"]
    projects = json.loads((HERE / "projects.json").read_text())
    (HERE / "observations").mkdir(exist_ok=False)
    results = []
    for project in projects:
        path = HERE / project["path"]
        calls = [
            ("finite", [str(binary), "check", str(path), "--format=json"]),
            ("sized", [str(binary), "sized", "check", "--entry=main::f",
                       f"--module=main={path / 'main.qli'}", f"--kernel={kernel}",
                       *project["sized_arguments"]]),
        ]
        if project["closed_probe"]:
            calls.append(("closed", [str(binary), "run", str(path), "--format=json"]))
        for mode, command in calls:
            started = time.monotonic()
            result = subprocess.run(
                command, cwd=ROOT, capture_output=True, timeout=60,
                env=os.environ | {"QLEISLI_KERNEL": str(kernel)},
            )
            record = dict(
                command=command, cwd=str(ROOT), exit_code=result.returncode,
                recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                elapsed_seconds=time.monotonic() - started,
                stdout_raw=result.stdout.decode(), stderr=result.stderr.decode(),
                source_sha256=project["source_sha256"],
                manifest_sha256=project["manifest_sha256"],
                binary_sha256=sha(binary), kernel_sha256=sha(kernel), mode=mode,
                scope=("Closed observe-main wrapper only; no ordinary-input assignment API."
                       if mode == "closed" else "Diagnostic/native check at the stages actually reached."),
            )
            if mode == "sized":
                record["transcript"] = record["stdout_raw"] + record["stderr"]
            else:
                record["stdout"] = json.loads(result.stdout)
            output = f"observations/{mode}-{project['name']}.json"
            (HERE / output).write_text(json.dumps(record, indent=2) + "\n")
            results.append(dict(name=project["name"], mode=mode,
                                exit_code=result.returncode, observation=output))
            print(project["name"], mode, result.returncode, flush=True)
    for name, digest in frozen.items():
        assert sha(HERE / name) == digest, name
    after = {name: sha(ROOT / name) for name in identity["current_source_sha256"]}
    assert after == identity["current_source_sha256"]
    assert sha(binary) == identity["binary"]["sha256"]
    assert sha(kernel) == identity["kernel"]["sha256"]
    (HERE / "summary.json").write_text(json.dumps(dict(
        status="observed", commands=results,
        sources_and_executables_unchanged=True, current_source_sha256_after=after,
        scope="Twelve first-source finite/sized checks and nine separately labelled closed probes. Actual unsupported stages and failures retained; no source-preservation or release claim.",
    ), indent=2) + "\n")


if __name__ == "__main__":
    main()
