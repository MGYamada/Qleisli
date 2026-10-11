"""Observe four first sources with constructed small commands, without replay.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[3]
CLI = Path("/private/tmp/qleisli-classical-functions-after")
CLI_SHA = "8291ddad7119af45ec24fe6c1a9266384470b4d0556ebedd6c0c87b710844e5a"
KERNEL = REPO / "lean-kernel/.lake/build/bin/qleisli-kernel"
KERNEL_SHA = "39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85"
CASES = ("copy-ordinary", "observe-pair", "implicit-readout", "duplicate-owner")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    with path.open("x", encoding="utf-8") as stream:
        json.dump(value, stream, indent=2)
        stream.write("\n")


def main():
    frozen = json.loads((ROOT / "first-files-02.json").read_text())["files"]

    def identity():
        assert sha(CLI) == CLI_SHA and sha(KERNEL) == KERNEL_SHA
        assert all(sha(ROOT / path) == digest for path, digest in frozen.items())
        return {"cli": {"path": str(CLI), "sha256": CLI_SHA},
                "kernel": {"path": str(KERNEL), "sha256": KERNEL_SHA}}

    identity()
    output = ROOT / "observations-02"
    output.mkdir()
    events = []
    commands = [(case, mode, "check") for case in CASES
                for mode in ("finite", "selected")]
    commands += [(case, mode, "run") for case in CASES[:2]
                 for mode in ("finite", "selected")]
    for case, mode, verb in commands:
        project = ROOT / "attempt-02" / case
        command = [str(CLI), verb]
        command += ([str(project)] if mode == "finite" else
                    ["--entry=main::main", "--module=main=" + str(project / "main.qli")])
        command.append("--format=json")
        before = identity()
        result = subprocess.run(command, cwd=REPO,
                                env=dict(os.environ, QLEISLI_KERNEL=str(KERNEL)),
                                capture_output=True, timeout=30)
        event = {"command": command, "cwd": str(REPO), "exit_code": result.returncode,
                 "recorded_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                 "case": case, "mode": mode, "verb": verb,
                 "binary_before": before, "binary_after": identity(),
                 "scope": "Actual bounded observation; no child-start attestation, general LLM benchmark or source-preservation proof."}
        name = case + "-" + mode + "-" + verb
        streams = {}
        for stream, data in (("stdout", result.stdout), ("stderr", result.stderr)):
            path = output / (name + "." + stream + ".txt")
            with path.open("xb") as raw:
                raw.write(data)
            streams[stream] = {"path": str(path.relative_to(ROOT)), "sha256": sha(path)}
        event["raw_streams"] = streams
        parsed = json.loads(result.stdout)
        event["stdout"] = parsed
        write(output / (name + ".json"), event)
        events.append(str((output / (name + ".json")).relative_to(ROOT)))
        print(json.dumps({"case": case, "mode": mode, "verb": verb,
                          "exit": result.returncode, "diagnostics": parsed.get("diagnostics", []),
                          "outcome": parsed.get("outcome")}), flush=True)
    write(output / "capture.json", {"observations": events, "identity": identity()})


if __name__ == "__main__":
    main()
