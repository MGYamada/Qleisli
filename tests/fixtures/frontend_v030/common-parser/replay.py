#!/usr/bin/env python3
"""Replay these source observations against an explicitly selected checkout.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tree", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    tree = args.tree.resolve()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    here = Path(__file__).resolve().parent
    baseline = json.loads((here / "before.json").read_text())
    records = []

    def run(label, argv):
        result = subprocess.run(argv, cwd=tree, capture_output=True, timeout=120)
        (out / f"{label}.stdout.txt").write_bytes(result.stdout)
        (out / f"{label}.stderr.txt").write_bytes(result.stderr)
        records.append({
            "argv": argv, "cwd": str(tree), "exit_code": result.returncode,
            "stdout": f"{label}.stdout.txt", "stderr": f"{label}.stderr.txt",
        })
        (out / "commands.json").write_text(json.dumps(records, indent=2) + "\n")
        if result.returncode:
            raise RuntimeError(f"{label} failed; inspect {out}")

    run("build", ["cargo", "build", "--offline", "--lib", "--bin", "qleisli"])
    executable = out / "observe"
    run("observer-build", [
        "rustc", "--edition=2024", str(here / "observe.rs"), "--extern",
        "qleisli=" + str(tree / "target/debug/libqleisli.rlib"), "-L",
        "dependency=" + str(tree / "target/debug/deps"), "-o", str(executable),
    ])
    for case in baseline["observations"]:
        source = here / case["source"]
        assert hashlib.sha256(source.read_bytes()).hexdigest() == case["sha256"]
        run(case["name"], [str(executable), str(source)])
    for name, bindings in [
        ("shared", []), ("contextual-type-name", []),
        ("static-fold", ["--nat=n=1"]), ("empty-owner", []),
    ]:
        run(name + "-proposal", [
            str(tree / "target/debug/qleisli"), "sized", "emit-proposal",
            "--entry=main::f", "--module=main=" + str(here / (name + ".qli")),
            *bindings, "--output=" + str(out / (name + ".proposal.json")),
        ])
    print(f"Saved ten source observations and four untrusted proposals in {out}")


if __name__ == "__main__":
    main()
