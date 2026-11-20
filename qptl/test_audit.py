"""Run the compiled declaration audit and its isolated negative regression.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""

import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
LEAN = ["lean", "-DwarningAsError=true"]


def main():
    subprocess.run([*LEAN, "Audit.lean"], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory(prefix="qptl-audit-") as directory:
        scratch = Path(directory)
        probe = scratch / "QPTLTests.lean"
        probe.write_text(
            "import QPTL\n"
            "namespace AuditProbe\n"
            "private axiom forbidden : True\n"
            "theorem dependsOnForbidden : True := forbidden\n"
            "end AuditProbe\n",
            encoding="utf-8",
        )
        subprocess.run(
            [*LEAN, "-o", str(probe.with_suffix(".olean")), str(probe.relative_to(scratch))],
            cwd=scratch,
            check=True,
        )
        search = [str(scratch)]
        if existing := os.environ.get("LEAN_PATH"):
            search.append(existing)
        result = subprocess.run(
            [*LEAN, "Audit.lean"],
            cwd=ROOT,
            env=os.environ | {"LEAN_PATH": os.pathsep.join(search)},
            capture_output=True,
            text=True,
            check=False,
        )
        output = result.stdout + result.stderr
        if result.returncode == 0 or "AuditProbe.forbidden" not in output or not (
            "QPTL project axiom" in output or "depends on forbidden axiom" in output
        ):
            raise SystemExit(f"Negative QPTL audit did not reject the private axiom:\n{output}")
        print("QPTL audit rejected the private project axiom")


if __name__ == "__main__":
    main()
