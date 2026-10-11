#!/usr/bin/env python3
"""Check the current enforcer against the preserved witness mutation in /tmp.

The mutable current-identity records here are synthetic test inputs. This does
not run or claim a whole-project proof build and never executes archived code.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

import hashlib
import json
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
FIXTURE = Path(__file__).resolve().parent
ROOT = FIXTURE.parents[3]
sys.path.insert(0, str(ROOT / "scripts"))

import check_initial_guarantees as checker
import test_check_initial_guarantees as fixtures
from check_ratification_packet import PacketError


def main():
    with tempfile.TemporaryDirectory(prefix="qleisli-witness-rejection-") as directory:
        root = Path(directory)
        record, _ = fixtures.copy_evidence_fixture(root)
        baseline = checker.check(root)
        changed = (FIXTURE / "weakened-validity.lean.txt").read_bytes()
        (root / checker.NATIVE_SOURCE).write_bytes(changed)
        case = fixtures.InitialGuaranteeEvidence()
        case.root = root
        case.record = record
        changed_revision = case.refresh_test_current_identity()
        try:
            checker.check(root)
        except PacketError as error:
            diagnostic = str(error)
            if "admitted Acceptance binding fields changed" not in diagnostic:
                raise AssertionError("mutation failed for an unrelated reason: " + diagnostic) from error
        else:
            raise AssertionError("the weakened original-packet witness was accepted")
        result = {
            "format": "qleisli.witness-binding-rejection",
            "version": 1,
            "status": "same-compiled-mutation-rejected-by-current-enforcer",
            "baseline_identity_check": baseline,
            "changed_source_revision": changed_revision["sha256"],
            "mutation_sha256": hashlib.sha256(changed).hexdigest(),
            "current_checker_sha256": hashlib.sha256((ROOT / "scripts/check_initial_guarantees.py").read_bytes()).hexdigest(),
            "fixture_helper_sha256": hashlib.sha256((ROOT / "scripts/test_check_initial_guarantees.py").read_bytes()).hexdigest(),
            "rejected": True,
            "diagnostic": diagnostic,
            "scope": "Identity-only regression; rejection occurs before any external Lean invocation. The prior fixture separately records real compilation and indistinguishable old review output. No new guarantee admission or fresh full build is asserted.",
        }
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
