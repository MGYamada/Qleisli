#!/usr/bin/env python3
"""Fixed tiny Fourier coefficient/reference probes; no expected IR copied.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""

import cmath
import datetime
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import time

root = Path(__file__).resolve().parent
repo = root.parents[3]
binary = Path("/private/tmp/qleisli-bounded-validation-target/debug/qleisli")
native = repo / "lean-kernel/.lake/build/bin/qleisli-kernel"
wrapper = root / "native-log.py"
identity = json.loads((root / "identity-before.json").read_text())
records = root / "small-probes"
records.mkdir()
digest = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
frozen = {}
for file in ("first-files.json", "probe-files.json"):
    frozen.update(json.loads((root / file).read_text())["files"])


def unchanged():
    assert digest(binary) == identity["cli_sha256"], "CLI identity changed"
    assert digest(native) == identity["native_sha256"], "native identity changed"
    assert all(digest(root / name) == sha for name, sha in frozen.items())
    assert all(digest(repo / name) == sha for name, sha in identity["source_files"].items())
    assert all(digest(repo / name) == sha for name, sha in identity["current_stdlib_sources"].items())


unchanged()
(records / "executed-driver.py.txt").write_bytes(Path(__file__).read_bytes())
session_path = root / "session.json"
session = json.loads(session_path.read_text())
attempt = session["attempts"][1]
assert not attempt["observations"], "one bounded capture only"
summary = {"checks": 0, "basis_columns": 0, "reference_columns": 0,
           "maximum_complex_coefficient_error": 0.0,
           "comparison_tolerance": 1e-11,
           "oracle": "Independent analytic positive Fourier coefficients and explicitly specified reference preparations.",
           "scope": "Small numerical corroboration, not exact native Fourier requests or a constitutional guarantee."}


def capture(label, command_name, entry, n=None, basis=None, expected=None):
    unchanged()
    log = records / (label + ".native.jsonl")
    log.touch()
    command = [str(binary), command_name, "--entry=" + entry,
               "--module=transform=" + str(root / "attempt-02/transform.qli"),
               "--module=reference=" + str(root / "attempt-02/reference.qli"),
               "--lean-kernel=" + str(wrapper), "--format=json"]
    if n is not None:
        command.append("--nat=n=" + str(n))
    if basis is not None:
        command.append("--basis=" + str(basis))
    env = dict(os.environ, QLEISLI_STUDY_NATIVE=str(native),
               QLEISLI_STUDY_NATIVE_LOG=str(log))
    start = time.monotonic()
    result = subprocess.run(command, cwd=repo, env=env, capture_output=True, timeout=60)
    (records / (label + ".stdout.txt")).write_bytes(result.stdout)
    (records / (label + ".stderr.txt")).write_bytes(result.stderr)
    output = json.loads(result.stdout)
    native_args = [json.loads(line) for line in log.read_text().splitlines()]
    event = {"command": command, "exit_code": result.returncode,
             "stdout": output, "stderr": result.stderr.decode(),
             "native_invocations": len(native_args),
             "seconds": time.monotonic() - start,
             "recorded_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
             "timestamp_note": "Clock after completion; not authenticated provenance."}
    if expected is not None:
        event["independent_expected_coefficients"] = [[z.real, z.imag] for z in expected]
    path = records / (label + ".json")
    path.write_text(json.dumps(event, indent=2) + "\n")
    attempt["observations"].append(str(path.relative_to(root)))
    session_path.write_text(json.dumps(session, indent=2) + "\n")
    unchanged()
    assert result.returncode == 0, f"{label}: {result.stdout!r} {result.stderr!r}"
    assert output["outcome"] == "ok"
    assert len(native_args) == 1
    assert native_args[0][0] == "--hierarchy-request-pending"
    assert output["result"]["verification"]["source_meaning_verified"] is False
    if expected is not None:
        actual = [complex(*z) for z in output["result"]["amplitudes"]]
        assert len(actual) == len(expected)
        error = max(abs(a - b) for a, b in zip(actual, expected))
        summary["maximum_complex_coefficient_error"] = max(summary["maximum_complex_coefficient_error"], error)
        event["maximum_complex_coefficient_error"] = error
        path.write_text(json.dumps(event, indent=2) + "\n")
        assert error < summary["comparison_tolerance"], f"{label}: error {error}"
    else:
        summary["checks"] += 1
    (records / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(label, result.returncode, flush=True)


# Check the added clients before any of their executions. Every supplied body
# participates; these are not selected-body-only source checks.
capture("zero-reference-check", "check", "reference::zero_reference")
for n in (1, 2, 3):
    capture(f"entangled-n{n}-check", "check", "reference::entangled", n=n)

# The formula does not inspect source gates, native receipts or proposed meanings.
for n in (0, 1, 2, 3):
    dimension = 1 << n
    for x in range(dimension):
        expected = [cmath.exp(2j * math.pi * x * y / dimension) / math.sqrt(dimension)
                    for y in range(dimension)]
        capture(f"qft-n{n}-basis{x}", "run", "transform::qft", n=n,
                basis=x, expected=expected)
        summary["basis_columns"] += 1

omega = cmath.exp(1j * math.pi / 4)
capture("zero-reference-run", "run", "reference::zero_reference", basis=0,
        expected=[omega / math.sqrt(2), 1j * omega / math.sqrt(2)])
summary["reference_columns"] += 1
for n in (1, 2, 3):
    dimension = 1 << n
    expected = [cmath.exp(2j * math.pi * (index % dimension) * (index // dimension) / dimension)
                / math.sqrt(2 * dimension) for index in range(2 * dimension)]
    capture(f"entangled-n{n}-run", "run", "reference::entangled", n=n,
            basis=0, expected=expected)
    summary["reference_columns"] += 1
(records / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
unchanged()
print(json.dumps(summary, indent=2), flush=True)
