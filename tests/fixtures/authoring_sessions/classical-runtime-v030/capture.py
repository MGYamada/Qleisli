"""Capture only constructed small commands; never replay stored observations.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import subprocess

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[3]
KERNEL = REPO / "lean-kernel/.lake/build/bin/qleisli-kernel"
KERNEL_SHA = "39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85"
BEFORE = Path("/private/tmp/qleisli-default-boundary-after")
BEFORE_SHA = "0340621153f39c92a9493c19c389039ccbae4f7ab43b5e742cd643428c428db7"
CASES = ("shared-flip", "ordinary-and", "nested-label", "quantum-argument")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    with path.open("x", encoding="utf-8") as out:
        json.dump(value, out, indent=2)
        out.write("\n")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("phase", choices=("before", "after"))
    parser.add_argument("--cli", type=Path)
    parser.add_argument("--sha256")
    options = parser.parse_args()
    if options.phase == "before":
        if options.cli or options.sha256:
            parser.error("before uses the fixed unchanged executable")
        cli, expected = BEFORE, BEFORE_SHA
    else:
        if not options.cli or not options.sha256:
            parser.error("after requires the separately built CLI and its digest")
        cli, expected = options.cli.resolve(), options.sha256
    frozen = json.loads((ROOT / "first-files.json").read_text())["files"]

    def identity():
        assert sha(cli) == expected and sha(KERNEL) == KERNEL_SHA
        assert all(sha(ROOT / path) == digest for path, digest in frozen.items())
        return {"cli": {"path": str(cli), "sha256": expected},
                "kernel": {"path": str(KERNEL), "sha256": KERNEL_SHA}}

    identity()
    output = ROOT / ("observations-" + options.phase)
    output.mkdir()
    events = []
    commands = [(case, mode, "check") for case in CASES for mode in ("finite", "selected")]
    if options.phase == "after":
        commands += [(case, mode, "run") for case in CASES[:3]
                     for mode in ("finite", "selected")
                     if (case, mode) != ("shared-flip", "selected")]
    for case, mode, verb in commands:
        project = ROOT / "attempt-01" / case
        command = [str(cli), verb]
        command += ([str(project)] if mode == "finite" else
                    ["--entry=main::main", "--module=main=" + str(project / "main.qli")])
        command.append("--format=json")
        before = identity()
        env = dict(os.environ, QLEISLI_KERNEL=str(KERNEL))
        result = subprocess.run(command, cwd=REPO, env=env, capture_output=True, timeout=30)
        event = {"command": command, "cwd": str(REPO), "exit_code": result.returncode,
                 "recorded_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                 "case": case, "mode": mode, "phase": options.phase,
                 "binary_before": before, "binary_after": identity(),
                 "scope": "Actual bounded CLI observation; no child-start attestation, source-preservation proof or exact oracle."}
        name = case + "-" + mode + "-" + verb
        streams = {}
        for stream, data in (("stdout", result.stdout), ("stderr", result.stderr)):
            path = output / (name + "." + stream + ".txt")
            with path.open("xb") as out:
                out.write(data)
            streams[stream] = {"path": str(path.relative_to(ROOT)), "sha256": sha(path)}
        event["raw_streams"] = streams
        try:
            parsed = json.loads(result.stdout)
        except (ValueError, UnicodeDecodeError):
            parsed = None
        if isinstance(parsed, dict) and parsed.get("format") == "qleisli.result":
            event["stdout"] = parsed
        else:
            event["transcript"] = "stdout:\n" + result.stdout.decode(errors="replace") + "\nstderr:\n" + result.stderr.decode(errors="replace")
        path = output / (name + ".json")
        write(path, event)
        events.append(str(path.relative_to(ROOT)))
        print(json.dumps({"case": case, "mode": mode, "verb": verb,
                          "exit": result.returncode, "result": parsed}), flush=True)
    write(output / "capture.json", {"observations": events, "identity": identity()})


if __name__ == "__main__":
    main()
