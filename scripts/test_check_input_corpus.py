#!/usr/bin/env python3
"""Regression checks for corpus provenance and phase-sensitive oracles.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import json
from pathlib import Path
import shutil
import tempfile
import unittest
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
        self.assertEqual(len(corpus.check_manifest(self.root)["cases"]), 24)

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


class OracleTests(unittest.TestCase):
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
