#!/usr/bin/env python3
"""Bounded replay of existing mathematical oracles after a keyword migration.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
No upstream framework, maximum sized input or new acceptance rule is exercised.
"""
import datetime
import os
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts"))
import check_input_corpus as corpus

BINARY = Path("/private/tmp/qleisli-classical-functions-after")
KERNEL = ROOT / "lean-kernel/.lake/build/bin/qleisli-kernel"
CLI_SHA = "8291ddad7119af45ec24fe6c1a9266384470b4d0556ebedd6c0c87b710844e5a"
NATIVE_SHA = "39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85"
STAGE = Path(__file__).resolve().parent
REPORT = STAGE / "semantic-replay-first.json"

case_ids = ["quantum_katas/grover2", "quantum_katas/deutsch_jozsa3", "qualtran/less_than2",
            "qualtran/and_phase", "qualtran/reflection2", "qualtran/reflection_minus1",
            "qualtran/control_zero_reflection2", "pennylane_demos/vqe_excitation",
            "pennylane_demos/phase_lock", "pennylane_demos/rx_quarter"]
fault_ids = ["majority_replaced_by_parity", "erased_rotation_scalar", "rx_missing_scalar",
             "zz_erased_scalar", "negative_rx_missing_scalar", "reflection_minus_missing_phase",
             "controlled_reflection_missing_phase"]
manifest = corpus.migration_json(corpus.CORPUS / "manifest.json")
by_id = {case["id"]: case for case in manifest["cases"]}
cases = [by_id[name] for name in case_ids]
all_faults = corpus.migration_json(corpus.CORPUS / "semantic_faults/manifest.json")["cases"]
by_fault = {case["id"]: case for case in all_faults}
faults = [by_fault[name] for name in fault_ids]
negatives = corpus.current_negatives()
os.environ["QLEISLI_KERNEL"] = str(KERNEL)
corpus.require(corpus.sha256(BINARY) == CLI_SHA and corpus.sha256(KERNEL) == NATIVE_SHA,
               "fixed CLI/native identity changed before replay")
binding = corpus.input_binding(cases, faults, negatives, BINARY)
report = {
    "format": 1, "status": "incomplete", "failures": [], "cases": [],
    "semantic_faults": [], "negative_cases": [], **binding,
    "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "scope": "Existing bounded numerical contract oracles, including coherent X/Y phase interference, on ten selected finite projects, seven retained type-correct semantic faults and four original negative controls. No upstream framework or maximum sized case is executed. Configured native bytes are identified, not child-start/completion attested. This is not a universal source-preservation theorem, new QS/PR/RS/EXACT discharge or release certification.",
    "driver_sha256": corpus.sha256(Path(__file__)),
    "native_kernel": {"path": str(KERNEL), "sha256": NATIVE_SHA, "bytes": KERNEL.stat().st_size},
    "compiler": {"path": str(BINARY), "sha256": CLI_SHA, "bytes": BINARY.stat().st_size},
    "expected_ids": {"cases": case_ids, "semantic_faults": fault_ids,
                     "negative_cases": [case["id"] for case in negatives]},
    "qubit_counts": {case["id"]: case["qubits"] for case in cases},
    "oracle_numeric_tolerance": corpus.TOLERANCE,
}
corpus.save_report(REPORT, report)
started = time.monotonic()


def completed(stage, identifier, action):
    try:
        report[stage].append(action())
        outcome = "passed"
    except Exception as error:
        corpus.record_failure(report, stage, identifier, error)
        outcome = "failed: " + str(error)
    corpus.save_report(REPORT, report)
    print(stage, identifier, outcome, flush=True)


for case in cases:
    completed("cases", case["id"], lambda: corpus.check_case(case, BINARY, False))
for fault in faults:
    completed("semantic_faults", fault["id"],
              lambda: corpus.check_semantic_fault(fault, by_id[fault["reference"]], BINARY))
for negative in negatives:
    completed("negative_cases", negative["id"], lambda: corpus.check_negative(negative, BINARY))
try:
    corpus.require(binding == corpus.input_binding(cases, faults, negatives, BINARY),
                   "validation source/oracle inputs changed during replay")
    corpus.require(corpus.sha256(BINARY) == CLI_SHA and corpus.sha256(KERNEL) == NATIVE_SHA,
                   "fixed CLI/native identity changed during replay")
except Exception as error:
    corpus.record_failure(report, "identity", None, error)
report["seconds"] = time.monotonic() - started
report["recorded_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
report["status"] = "failed" if report["failures"] else "passed"
report["compiler_identity_stable"] = corpus.sha256(BINARY) == CLI_SHA
report["native_kernel_identity_stable"] = corpus.sha256(KERNEL) == NATIVE_SHA
corpus.save_report(REPORT, report)
print("status", report["status"], "probes", sum(case["semantic_probes"] for case in report["cases"]),
      "seconds", report["seconds"], flush=True)
sys.exit(0 if report["status"] == "passed" else 1)
