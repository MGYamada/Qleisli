"""Bounded public CLI capture of frozen informed #68 source controls.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
Commands are constructed here, never loaded from observation records.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import subprocess
import time

REPOSITORY = Path(__file__).resolve().parents[4]
ROOT = Path(__file__).resolve().parent
KERNEL = REPOSITORY / "lean-kernel/.lake/build/bin/qleisli-kernel"
EXPECTED_KERNEL = "39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85"
BEFORE_CLI = Path("/private/tmp/qleisli-rust-boundary-before")
EXPECTED_BEFORE = "bd9219f7847f1a7a52a3bd1346d39e8455edf0988e04582595471ae439b5feef"
CASES = (
    "classical-drop-controls", "unresolved-classical-drop",
    "unresolved-quantum-drop", "user-quantum-drop", "local-drop-category",
    "nested-unit-wildcard", "nested-unit-scope", "reset-result-discarded",
    "reset-result-returned",
)
RUN_CASES = (
    "classical-drop-controls", "user-quantum-drop", "reset-result-returned",
)


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def write_new(path, value):
    with path.open("x", encoding="utf-8") as out:
        out.write(json.dumps(value, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("phase", choices=("before", "after"))
    parser.add_argument("--cli", type=Path)
    parser.add_argument("--cli-sha256")
    options = parser.parse_args()
    if options.phase == "before":
        if options.cli or options.cli_sha256:
            parser.error("the before executable is fixed, not overrideable")
        cli, expected = BEFORE_CLI, EXPECTED_BEFORE
    else:
        if not options.cli or not options.cli_sha256:
            parser.error("after needs the separately supplied CLI and identity")
        cli, expected = options.cli.resolve(), options.cli_sha256
    inventory = json.loads((ROOT / "first-files.json").read_text())

    def identity():
        executable = {
            "cli": {"path": str(cli), "sha256": sha(cli)},
            "kernel": {"path": str(KERNEL), "sha256": sha(KERNEL)},
        }
        if executable["cli"]["sha256"] != expected:
            raise RuntimeError("selected CLI identity differs from the supplied fixed identity")
        if executable["kernel"]["sha256"] != EXPECTED_KERNEL:
            raise RuntimeError("selected native checker identity changed")
        for name, digest in inventory["files"].items():
            if sha(ROOT / name) != digest:
                raise RuntimeError("frozen first-source/context/prediction changed: " + name)
        return executable

    first_identity = identity()
    output = ROOT / ("observations-" + options.phase)
    output.mkdir()
    events = []

    def observe(case, verb="check", text=False):
        before = identity()
        project = ROOT / "attempt-01" / case
        command = [str(cli), verb, str(project)]
        if not text:
            command.append("--format=json")
        name = case + "-" + verb + ("-text" if text else "-json")
        env = os.environ.copy()
        env["QLEISLI_KERNEL"] = str(KERNEL)
        started = datetime.datetime.now(datetime.timezone.utc).isoformat()
        began = time.monotonic()
        result = subprocess.run(
            command, cwd=REPOSITORY, env=env, capture_output=True, timeout=30,
        )
        elapsed = time.monotonic() - began
        ended = datetime.datetime.now(datetime.timezone.utc).isoformat()
        streams = {"stdout": result.stdout, "stderr": result.stderr}
        for stream, data in streams.items():
            with (output / (name + "." + stream + ".txt")).open("xb") as out:
                out.write(data)
        after = {
            "cli": {"path": str(cli), "sha256": sha(cli)},
            "kernel": {"path": str(KERNEL), "sha256": sha(KERNEL)},
        }
        event = {
            "command": command, "cwd": str(REPOSITORY),
            "environment_overrides": {"QLEISLI_KERNEL": str(KERNEL)},
            "case": case, "phase": options.phase, "mode": "finite",
            "exit_code": result.returncode, "started_utc": started,
            "recorded_utc": ended, "seconds": elapsed,
            "binary_before": before, "binary_after": after,
            "binary_identity_stable": before == after,
            "source_sha256": sha(project / "main.qli"),
            "manifest_sha256": sha(project / "Qargo.toml"),
            "raw_streams": {
                stream: {
                    "path": str((output / (name + "." + stream + ".txt")).relative_to(ROOT)),
                    "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data),
                } for stream, data in streams.items()
            },
            "scope": "Actual bounded public CLI observation; selected native bytes identify a path, not child-start attestation, authenticated build provenance or a source/runtime theorem.",
        }
        try:
            parsed = json.loads(result.stdout)
        except (ValueError, UnicodeDecodeError):
            parsed = None
        if isinstance(parsed, dict) and parsed.get("format") == "qleisli.result":
            event["stdout"] = parsed
        else:
            event["transcript"] = (
                "stdout:\n" + result.stdout.decode("utf-8", errors="replace")
                + "\nstderr:\n" + result.stderr.decode("utf-8", errors="replace")
            )
        path = output / (name + ".json")
        write_new(path, event)
        events.append(str(path.relative_to(ROOT)))
        if before != after:
            raise RuntimeError("executable identity changed; original result retained")
        identity()
        detail = parsed.get("diagnostics", []) if isinstance(parsed, dict) else None
        print(json.dumps({
            "case": case, "verb": verb, "text": text,
            "exit_code": result.returncode, "diagnostics": detail,
        }), flush=True)
        return result.returncode

    for case in CASES:
        observe(case)
        observe(case, text=True)
    for case in RUN_CASES:
        checked = json.loads((output / (case + "-check-json.json")).read_text())
        if checked["exit_code"] == 0:
            observe(case, verb="run")
        else:
            print("Actual desired control rejected; run skipped: " + case, flush=True)
    write_new(output / "capture.json", {
        "format": "qleisli.informed-public-source-capture", "version": 1,
        "phase": options.phase,
        "recorded_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "actual_observations": events,
        "first_inventory_sha256": sha(ROOT / "first-files.json"),
        "prediction_sha256": sha(ROOT / "predictions-before.json"),
        "pending_session_sha256": sha(ROOT / "session.pending.json"),
        "observer_sha256": sha(Path(__file__)),
        "binary_first": first_identity, "binary_final": identity(),
        "scope": "First sources/results unchanged; no commands taken from records, no source repairs, builds, maximum-size cases or generic QFT.",
    })
    print(json.dumps({"observations": len(events), "binary_final": identity()}), flush=True)


if __name__ == "__main__":
    main()
