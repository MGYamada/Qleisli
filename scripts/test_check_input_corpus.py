#!/usr/bin/env python3
"""Regression checks for corpus provenance and phase-sensitive oracles.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch
import check_input_corpus as corpus


class IntakeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "corpus"
        shutil.copytree(corpus.CORPUS, self.root)

    def edit_manifest(self, mutation):
        path = self.root / "manifest.json"
        manifest = json.loads(path.read_text())
        mutation(manifest)
        path.write_text(json.dumps(manifest))

    def test_current_intake_passes(self):
        self.assertEqual(len(corpus.check_manifest(self.root)["cases"]), 30)

    def test_sized_experiment_cannot_add_an_input_source(self):
        self.edit_manifest(lambda m: m["sized_experiments"][0].update(source="unapproved"))
        with self.assertRaisesRegex(ValueError, "unapproved sized source"):
            corpus.check_manifest(self.root)

    def test_sized_experiment_source_changes_require_recording(self):
        path = self.root / "sized/qualtran_xor/bitwise.qli"
        path.write_text(path.read_text()+"// changed\n")
        with self.assertRaisesRegex(ValueError, "sized source hash mismatch"):
            corpus.check_manifest(self.root)

    def test_new_repository_is_rejected(self):
        self.edit_manifest(lambda m: m["sources"][0].update(repository="unapproved/repo"))
        with self.assertRaisesRegex(ValueError, "unapproved source"):
            corpus.check_manifest(self.root)

    def test_changed_original_is_rejected(self):
        path = self.root / "upstream/quantum_katas/BasicGates__ReferenceImplementation.qs"
        path.write_text(path.read_text() + "// changed\n")
        with self.assertRaisesRegex(ValueError, "upstream hash mismatch"):
            corpus.check_manifest(self.root)

    def test_removed_attribution_is_rejected(self):
        path = self.root / "quantum_katas/global_phase/kernel.qli"
        path.write_text(path.read_text().replace("Copyright (c) Microsoft Corporation", "Other"))
        with self.assertRaisesRegex(ValueError, "lost Microsoft attribution"):
            corpus.check_manifest(self.root)

    def test_altered_first_attempt_is_rejected(self):
        path = self.root / "authoring/attempt-01/quantum_katas/global_phase/kernel.qli"
        path.write_text(path.read_text() + "// later rewrite\n")
        with self.assertRaisesRegex(ValueError, "snapshot changed"):
            corpus.check_manifest(self.root)

    def test_unrecorded_input_is_rejected(self):
        (self.root / "upstream/qualtran/extra.py").write_text("# unreviewed\n")
        with self.assertRaisesRegex(ValueError, "unrecorded or missing upstream"):
            corpus.check_manifest(self.root)

    def test_old_observations_keep_their_frozen_scope(self):
        old = json.loads((self.root / "authoring/check-initial.json").read_text())
        new = json.loads((self.root / "authoring/v021-expansion/check-initial.json").read_text())
        self.assertEqual((len(old["results"]), len(new["results"])), (24, 6))
        corpus.check_manifest(self.root)

    def test_duplicate_observation_cannot_hide_a_missing_project(self):
        path = self.root / "authoring/v021-expansion/check-initial.json"
        data = json.loads(path.read_text())
        data["results"][-1] = data["results"][0]
        path.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "incomplete authoring check"):
            corpus.check_manifest(self.root)

    def test_expansion_session_cannot_be_omitted(self):
        self.edit_manifest(lambda m: m["authoring_sessions"].pop())
        with self.assertRaisesRegex(ValueError, "unrecorded authoring session"):
            corpus.check_manifest(self.root)

    def test_extra_current_source_requires_a_snapshot(self):
        (self.root / "qualtran/equals2/extra.qli").write_text("// unrecorded module\n")
        with self.assertRaisesRegex(ValueError, "missing authoring snapshots"):
            corpus.check_manifest(self.root)


class OracleTests(unittest.TestCase):
    def test_lcu_zero_block_is_projector_but_selector_is_not_clean(self):
        case = {"id": "pennylane_demos/lcu_projector", "qubits": 2}
        for x in range(2):
            column = corpus.reference_column(case, 2 * x)
            for y in range(2):
                self.assertEqual(column[2 * y], int(x == y == 0))
        self.assertEqual(corpus.reference_column(case, 2)[3], 1)

    def test_nonfinite_expected_entry_is_not_a_success(self):
        with self.assertRaisesRegex(ValueError, "unnormalized oracle"):
            corpus.compare({(False,): 1}, {(False,): 1, (True,): float("nan")}, "bad oracle")

    def test_fault_harness_error_does_not_count_as_detection(self):
        fault = {"id": "fault", "project": "semantic_faults/missing_lcu_unprepare"}
        with patch.object(corpus.subprocess, "run") as run, patch.object(corpus, "check_case") as check:
            run.return_value.returncode = 0
            run.return_value.stderr = ""
            run.return_value.stdout = '{"outcome":"ok"}'
            check.side_effect = ValueError("run failed")
            with self.assertRaisesRegex(ValueError, "run failed"):
                corpus.check_semantic_fault(fault, {"id": "reference"}, Path("qleisli"))

    def test_global_sign_changes_control_interference(self):
        a = corpus.interference([1, 0], 0, "x")
        b = corpus.interference([-1, 0], 0, "x")
        with self.assertRaises(ValueError):
            corpus.compare(a, b, "erased global phase")

    def test_y_probe_distinguishes_conjugate_phase(self):
        a = corpus.interference([1j, 0], 0, "y")
        b = corpus.interference([-1j, 0], 0, "y")
        with self.assertRaises(ValueError):
            corpus.compare(a, b, "conjugated phase")

    def test_oracle_columns_are_unitary(self):
        # This guards transcription of the independent mathematical reference,
        # not the QLI implementation. Measurement cases have separate oracles.
        for case in corpus.check_manifest()["cases"]:
            if case["kind"] != "unitary":
                continue
            columns = [corpus.reference_column(case, x) for x in range(1 << case["qubits"])]
            for x, left in enumerate(columns):
                for y, right in enumerate(columns):
                    inner = sum(complex(a).conjugate() * b for a, b in zip(left, right))
                    self.assertLess(abs(inner - (x == y)), corpus.TOLERANCE, (case["id"], x, y))


if __name__ == "__main__":
    unittest.main()
