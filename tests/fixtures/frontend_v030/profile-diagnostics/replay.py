#!/usr/bin/env python3
"""Observe the bounded rejection corpus without modifying recorded results.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--kernel", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    binary, kernel = args.binary.resolve(), args.kernel.resolve()
    sources = Path(__file__).resolve().parent / "sources"
    records = []
    for source in sorted(sources.glob("*.qli")):
        with tempfile.TemporaryDirectory(prefix="qleisli-profile-diagnostic-") as temporary:
            project = Path(temporary)
            shutil.copyfile(sources / "Qargo.toml", project / "Qargo.toml")
            shutil.copyfile(source, project / "main.qli")
            argv = [str(binary), "check", str(project), "--format=json"]
            result = subprocess.run(argv, env=dict(os.environ, QLEISLI_KERNEL=str(kernel)),
                                    capture_output=True, text=True, timeout=60)
            records.append(dict(case=source.stem, source_sha256=sha(source), argv=argv,
                                exit_code=result.returncode, stdout=result.stdout, stderr=result.stderr))
    record = dict(scope="Twelve original rejected finite-source examples; diagnostic observations, not proofs.",
                  binary=dict(path=str(binary), sha256=sha(binary)),
                  kernel=dict(path=str(kernel), sha256=sha(kernel)),
                  manifest_sha256=sha(sources / "Qargo.toml"), observations=records)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x") as output:
        output.write(json.dumps(record, indent=2) + "\n")
    print(f"Saved {len(records)} observations to {args.output}")


if __name__ == "__main__":
    main()
