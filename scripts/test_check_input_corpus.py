#!/usr/bin/env python3
"""Regression checks for corpus provenance and phase-sensitive oracles.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import json
import math
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
        self.assertEqual(len(corpus.check_manifest(self.root)["cases"]), 54)

    def test_sized_experiment_cannot_add_an_input_source(self):
        self.edit_manifest(lambda m: m["sized_experiments"][0].update(source="unapproved"))
        with self.assertRaisesRegex(ValueError, "unapproved sized source"):
            corpus.check_manifest(self.root)

    def test_sized_experiment_source_changes_require_recording(self):
        path = self.root / "sized/qualtran_xor/bitwise.qli"
        path.write_text(path.read_text()+"// changed\n")
        with self.assertRaisesRegex(ValueError, "sized source hash mismatch"):
            corpus.check_manifest(self.root)

    def test_local_composition_is_pinned_and_cannot_introduce_upstream(self):
        self.edit_manifest(lambda m: m["sized_local_compositions"][0].update(source="unapproved"))
        with self.assertRaisesRegex(ValueError, "unknown local composition fields"):
            corpus.check_manifest(self.root)

    def test_local_composition_changed_source_and_dependency_reject(self):
        path = self.root / "sized/measured_qpe/initialization.qli"
        original = path.read_text()
        path.write_text(original + "// changed\n")
        with self.assertRaisesRegex(ValueError, "local composition hash mismatch"):
            corpus.check_manifest(self.root)
        path.write_text(original)
        self.edit_manifest(lambda m: m["sized_local_compositions"][0].update(dependencies=["sized/unregistered.qli"]))
        with self.assertRaisesRegex(ValueError, "unregistered local composition dependency"):
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
        simple = json.loads((self.root / "authoring/v022-simple/check-initial.json").read_text())
        self.assertEqual((len(old["results"]), len(new["results"]), len(simple["results"])), (24, 6, 6))
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
    def test_comparison_equality_boundary_and_arbitrary_target(self):
        inclusive = {"id": "qualtran/less_equal1", "qubits": 3}
        strict = {"id": "qualtran/greater_than1", "qubits": 3}
        for value in range(2):
            for target in range(2):
                source = 3 * value + 4 * target
                self.assertEqual(corpus.reference_column(inclusive, source),
                                 [int(row == (source ^ 4)) for row in range(8)])
                self.assertEqual(corpus.reference_column(strict, source),
                                 [int(row == source) for row in range(8)])

    def test_mixed_rotation_matches_chronological_rx_then_negative_ry(self):
        case = {"id": "pennylane_demos/rotation_mixed_sign", "qubits": 1}
        c, s = math.cos(math.pi / 4), math.sin(math.pi / 4)
        rx = [[c, -1j * s], [-1j * s, c]]
        negative_ry = [[c, s], [-s, c]]
        for column in range(2):
            expected = [sum(negative_ry[row][k] * rx[k][column] for k in range(2))
                        for row in range(2)]
            self.assertLess(max(abs(a-b) for a, b in zip(
                corpus.reference_column(case, column), expected)), corpus.TOLERANCE)
        reversed_entry = sum(rx[0][k] * negative_ry[k][0] for k in range(2))
        self.assertGreater(abs(reversed_entry - corpus.reference_column(case, 0)[0]), .5)

    def test_qaoa_mixer_keeps_tensor_rotation_scalar(self):
        case = {"id": "pennylane_demos/qaoa_mixer2", "qubits": 2}
        c, s = math.cos(math.pi / 4), math.sin(math.pi / 4)
        rx = [[c, -1j * s], [-1j * s, c]]
        for column in range(4):
            expected = [rx[row & 1][column & 1] * rx[row >> 1][column >> 1]
                        for row in range(4)]
            self.assertLess(max(abs(a-b) for a, b in zip(
                corpus.reference_column(case, column), expected)), corpus.TOLERANCE)
        self.assertEqual(corpus.reference_column(case, 0)[3], -.5)

    def test_odd_parity_support_and_signed_nonzero_input(self):
        case = {"id": "quantum_katas/odd_parity3", "qubits": 3}
        self.assertEqual(corpus.reference_column(case, 0), [0, .5, .5, 0, .5, 0, 0, .5])
        self.assertEqual(corpus.reference_column(case, 1), [0, -.5, .5, 0, .5, 0, 0, -.5])

    def test_singlet_keeps_upstream_wire_order_and_sign(self):
        case = {"id": "quantum_katas/bell_singlet2", "qubits": 2}
        column = corpus.reference_column(case, 0)
        self.assertEqual(column[0], 0)
        self.assertEqual(column[3], 0)
        self.assertGreater(column[2], 0)
        self.assertEqual(column[1], -column[2])

    def test_constant_predicates_preserve_input_and_toggle_both_target_values(self):
        for name, predicate in [("less_than_constant2", lambda x: x < 3),
                                ("equals_constant2", lambda x: x == 1)]:
            case = {"id": "qualtran/" + name, "qubits": 3}
            for x in range(4):
                for target in range(2):
                    col = corpus.reference_column(case, x + 4 * target)
                    self.assertEqual(col, [int(i == x + 4 * (target ^ predicate(x))) for i in range(8)])

    def test_zz_preserves_the_absolute_rotation_scalar(self):
        case = {"id": "pennylane_demos/ising_zz_quarter2", "qubits": 2}
        even = corpus.reference_column(case, 0)[0]
        odd = corpus.reference_column(case, 1)[1]
        self.assertAlmostEqual(even.real, 2 ** -.5)
        self.assertAlmostEqual(even.imag, -(2 ** -.5))
        self.assertEqual(odd, even.conjugate())

    def test_fredkin_preserves_control_and_leaves_zero_control_unchanged(self):
        case = {"id": "quantum_katas/fredkin3", "qubits": 3}
        self.assertEqual(corpus.reference_column(case, 4), [int(i == 4) for i in range(8)])
        self.assertEqual(corpus.reference_column(case, 5), [int(i == 3) for i in range(8)])

    def test_constant_xor_uses_low_bit_and_kickback_retains_key(self):
        xor = {"id": "qualtran/xor_constant2", "qubits": 2}
        kickback = {"id": "pennylane_demos/phase_kickback1", "qubits": 2}
        self.assertEqual(corpus.reference_column(xor, 2), [0, 0, 0, 1])
        self.assertEqual(corpus.reference_column(kickback, 0), [1, 0, 0, 0])
        self.assertEqual(corpus.reference_column(kickback, 2), [0, 0, 0, 1])

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
