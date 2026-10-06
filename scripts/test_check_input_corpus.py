#!/usr/bin/env python3
"""Regression checks for corpus provenance and phase-sensitive oracles.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import json
import hashlib
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
        self.assertEqual(len(corpus.check_manifest(self.root)["cases"]), 87)

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

    def pennylane_sized_case(self, attribution=True):
        path = self.root / "sized/qualtran_xor/bitwise.qli"
        text = path.read_text().replace("// Copyright 2024 Google LLC\n", "")
        if attribution:
            text = "// Upstream authors (repository usernames): josh. See upstream metadata.\n" + text
        path.write_text(text)
        def mutate(manifest):
            upstream = next(c for c in manifest["cases"] if c["id"] == "pennylane_demos/qubit_rotation")
            case = next(c for c in manifest["sized_experiments"] if c["file"] == "sized/qualtran_xor/bitwise.qli")
            case.update(source=upstream["source"], license=upstream["license"],
                        upstream_path=upstream["upstream_path"], sha256=corpus.sha256(path))
        self.edit_manifest(mutate)

    def test_sized_pennylane_uses_its_authors_not_google_attribution(self):
        self.pennylane_sized_case()
        corpus.check_manifest(self.root)

    def test_missing_sized_pennylane_authors_reject(self):
        self.pennylane_sized_case(attribution=False)
        with self.assertRaisesRegex(ValueError, "lost PennyLane attribution"):
            corpus.check_manifest(self.root)

    def test_missing_sized_google_or_microsoft_attribution_reject(self):
        manifest = json.loads((self.root / "manifest.json").read_text())
        for source, token, label in [("qualtran", "Google LLC", "Google"),
                                     ("quantum_katas", "Copyright (c) Microsoft Corporation", "Microsoft")]:
            with self.subTest(source=source):
                case = next(c for c in manifest["sized_experiments"] if c["source"] == source)
                path = self.root / case["file"]
                original = path.read_text()
                path.write_text(original.replace(token, "removed"))
                self.edit_manifest(lambda m: next(c for c in m["sized_experiments"]
                                                 if c["file"] == case["file"]).update(sha256=corpus.sha256(path)))
                with self.assertRaisesRegex(ValueError, f"lost {label} attribution"):
                    corpus.check_manifest(self.root)
                path.write_text(original)
                self.edit_manifest(lambda m: next(c for c in m["sized_experiments"]
                                                 if c["file"] == case["file"]).update(sha256=corpus.sha256(path)))

    def test_missing_finite_pennylane_authors_reject(self):
        path = self.root / "pennylane_demos/qubit_rotation/kernel.qli"
        path.write_text('\n'.join(path.read_text().splitlines()[1:]) + '\n')
        with self.assertRaisesRegex(ValueError, "lost PennyLane attribution"):
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

    def test_current_negatives_preserve_baseline_and_source_identities(self):
        original = json.loads((self.root / "negative/manifest.json").read_text())
        current = corpus.current_negatives(self.root)
        self.assertEqual([(c["id"], c["project"]) for c in current],
                         [(c["id"], c["project"]) for c in original["cases"]])
        changed = [c["id"] for b, c in zip(original["cases"], current) if b != c]
        self.assertEqual(changed, ["measurement_adjoint"])

    def test_missing_current_negative_selection_rejects(self):
        self.edit_manifest(lambda m: m.pop("negative_expectations"))
        with self.assertRaisesRegex(ValueError, "missing or invalid current negative"):
            corpus.check_manifest(self.root)

    def test_changed_current_negative_bytes_reject(self):
        path = self.root / "negative/current-manifest.json"
        path.write_text(path.read_text() + " ")
        with self.assertRaisesRegex(ValueError, "expectation identity changed"):
            corpus.current_negatives(self.root)

    def test_current_negative_cannot_drop_or_replace_rejected_source(self):
        path = self.root / "negative/current-manifest.json"
        initial = json.loads(path.read_text())
        for drop in (True, False):
            data = json.loads(json.dumps(initial))
            if drop:
                data["cases"].pop()
            else:
                data["cases"][0]["project"] = "negative/measurement_adjoint"
            path.write_text(json.dumps(data))
            self.edit_manifest(lambda m: m["negative_expectations"].update(sha256=corpus.sha256(path)))
            with self.assertRaisesRegex(ValueError, "current negative (coverage|identity or contract) changed"):
                corpus.current_negatives(self.root)

    def test_current_negative_rejects_stale_baseline(self):
        path = self.root / "negative/manifest.json"
        path.write_text(path.read_text() + " ")
        with self.assertRaisesRegex(ValueError, "baseline changed"):
            corpus.current_negatives(self.root)

    def test_current_negative_path_cannot_escape(self):
        self.edit_manifest(lambda m: m["negative_expectations"].update(path="../outside.json"))
        with self.assertRaises(ValueError):
            corpus.current_negatives(self.root)


class MigrationTests(unittest.TestCase):
    """Small synthetic records test chaining, not genuine compiler acceptance."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.project = "qualtran/example"
        self.before = {self.project + "/" + name: self.digest("before " + name)
                       for name in ("main.qli", "kernel.qli")}
        self.paths = []

    @staticmethod
    def digest(text):
        return hashlib.sha256(text.encode()).hexdigest()

    def write(self, path, value):
        path.write_text(json.dumps(value))

    def migration(self, name, before):
        root = self.root / "migrations" / name
        root.mkdir(parents=True)
        files = {}
        for rel, digest in before.items():
            path = root / "sources" / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(name + " " + rel)
            files[rel] = {"before": digest, "after": corpus.sha256(path)}
        after = {rel: r["after"] for rel, r in files.items()}
        self.write(root / "checks.json", {
            "sources": after,
            "results": [{"project": self.project, "argv": ["synthetic-check"],
                         "cwd": str(root), "exit_code": 0, "stderr": "",
                         "stdout": json.dumps({"outcome": "ok"})}],
        })
        self.write(root / "migration.json", {
            "format": 1, "kind": "explicit-source-migration", "issue": 25,
            "project_version": "0.3.0-alpha", "created_utc": "2026-10-05T00:00:00Z",
            "context": "Synthetic validator regression, not compiler evidence.",
            "projects": [self.project], "files": files, "observations": ["checks.json"],
        })
        self.paths.append(str((root / "migration.json").relative_to(self.root)))
        return root, after

    def check(self):
        return corpus.migrated_sources(self.root, self.paths, self.before)

    def mutate(self, path, action):
        data = json.loads(path.read_text())
        action(data)
        self.write(path, data)

    def test_ordered_successive_migrations_preserve_predecessors(self):
        _, after = self.migration("first", self.before)
        _, final = self.migration("second", after)
        self.assertEqual(self.check(), final)
        self.paths.reverse()
        with self.assertRaisesRegex(ValueError, "stale migration predecessor"):
            self.check()

    def snapshot_selection(self):
        first, after = self.migration("first", self.before)
        for source in after:
            target = self.root / source
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(first / "sources" / source, target)
        selected, final = self.migration("selected", after)
        self.mutate(selected / "migration.json", lambda m: m.update(source_selection="snapshot"))
        self.write(self.root / "manifest.json", {"source_migrations": self.paths})
        return selected, after, final

    def test_explicit_snapshot_selects_current_files_and_preserves_old_directory(self):
        selected, after, final = self.snapshot_selection()
        locations = {}
        self.assertEqual(corpus.migrated_sources(self.root, self.paths, self.before,
                                                source_paths=locations), final)
        self.assertEqual({source: corpus.sha256(self.root / source) for source in after}, after)
        self.assertEqual(locations, {source: (selected / "sources" / source).resolve() for source in final})
        self.assertEqual(corpus.current_project({"project": self.project}, self.root),
                         (selected / "sources" / self.project).resolve())
        self.assertEqual(corpus.current_project({"project": "unaffected/project"}, self.root),
                         (self.root / "unaffected/project").resolve())

    def test_snapshot_selection_rejects_changed_retained_predecessor(self):
        self.snapshot_selection()
        (self.root / self.project / "kernel.qli").write_text("changed preserved source")
        with self.assertRaisesRegex(ValueError, "selected migration predecessor changed"):
            self.check()

    def test_snapshot_selection_rejects_stale_current_file_and_extra_manifest(self):
        selected, _, _ = self.snapshot_selection()
        project = selected / "sources" / self.project
        source = project / "kernel.qli"
        original = source.read_text()
        source.write_text("stale derivative")
        with self.assertRaisesRegex(ValueError, "selected migration snapshot changed"):
            corpus.current_project({"project": self.project}, self.root)
        source.write_text(original)
        (project / "Qargo.toml").write_text("unrecorded edition override")
        with self.assertRaisesRegex(ValueError, "selected migration snapshot changed"):
            corpus.current_project({"project": self.project}, self.root)

    def test_snapshot_root_symlink_cannot_escape_corpus(self):
        selected, _, _ = self.snapshot_selection()
        with tempfile.TemporaryDirectory() as directory:
            outside = Path(directory) / "sources"
            shutil.move(selected / "sources", outside)
            (selected / "sources").symlink_to(outside, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, "snapshot root escapes intake"):
                self.check()
            with self.assertRaisesRegex(ValueError, "snapshot root escapes intake"):
                corpus.current_project({"project": self.project}, self.root)

    def test_unknown_snapshot_selection_cannot_silently_use_original(self):
        selected, _, _ = self.snapshot_selection()
        self.mutate(selected / "migration.json", lambda m: m.update(source_selection="original"))
        with self.assertRaisesRegex(ValueError, "unknown migration source selection"):
            self.check()
        with self.assertRaisesRegex(ValueError, "unknown migration source selection"):
            corpus.current_project({"project": self.project}, self.root)

    def test_execution_and_report_binding_use_selected_snapshot(self):
        selected, _, _ = self.snapshot_selection()
        case = {"id": self.project, "project": self.project, "kind": "measure"}
        for name in ("Qargo.toml", "semantic_faults/manifest.json"):
            path = self.root / name
            path.parent.mkdir(exist_ok=True)
            path.write_text("{}")
        (self.root / "negative").mkdir()
        for name in ("manifest.json", "current-manifest.json"):
            shutil.copyfile(corpus.CORPUS / "negative" / name, self.root / "negative" / name)
        manifest_path = self.root / "manifest.json"
        manifest = json.loads(manifest_path.read_text())
        manifest["negative_expectations"] = json.loads((corpus.CORPUS / "manifest.json").read_text())["negative_expectations"]
        manifest_path.write_text(json.dumps(manifest))
        with patch.object(corpus, "CORPUS", self.root), \
             patch.object(corpus, "run", return_value={(True,): 1.0}) as run, \
             patch.object(corpus, "protocol_probes", return_value=[]):
            corpus.check_case(case, Path(__file__), False)
            self.assertEqual(run.call_args.args[1], (selected / "sources" / self.project).resolve())
            binding = corpus.input_binding([case], [], [], Path(__file__))
        selected_prefix = str((selected / "sources" / self.project).relative_to(self.root))
        self.assertEqual(set(binding["source_sha256"]),
                         {selected_prefix + "/" + name for name in ("main.qli", "kernel.qli")})
        self.assertEqual(set(binding["source_migration_sha256"]), set(self.paths))

    def test_removed_or_duplicate_migration_rejects(self):
        self.migration("first", self.before)
        original = list(self.paths)
        self.paths = []
        with self.assertRaisesRegex(ValueError, "unrecorded source migration"):
            self.check()
        self.paths = original * 2
        with self.assertRaisesRegex(ValueError, "duplicate source migration"):
            self.check()

    def test_stale_predecessor_rejects(self):
        root, _ = self.migration("first", self.before)
        self.mutate(root / "migration.json", lambda m: next(iter(m["files"].values())).update(before="0" * 64))
        with self.assertRaisesRegex(ValueError, "stale migration predecessor"):
            self.check()

    def test_alias_paths_cannot_duplicate_migrations_or_observations(self):
        root, _ = self.migration("first", self.before)
        self.paths.append("migrations/first/../first/migration.json")
        with self.assertRaisesRegex(ValueError, "duplicate source migration path"):
            self.check()
        self.paths.pop()
        self.mutate(root / "migration.json", lambda m: m.update(observations=["checks.json", "./checks.json"]))
        with self.assertRaisesRegex(ValueError, "duplicate migration observation path"):
            self.check()

    def test_missing_project_file_rejects(self):
        root, _ = self.migration("first", self.before)
        self.mutate(root / "migration.json", lambda m: m["files"].pop(self.project + "/kernel.qli"))
        with self.assertRaisesRegex(ValueError, "incomplete migration project snapshots"):
            self.check()

    def test_unknown_project_rejects(self):
        root, _ = self.migration("first", self.before)
        self.mutate(root / "migration.json", lambda m: m.update(projects=["unknown/project"]))
        with self.assertRaisesRegex(ValueError, "unknown/duplicate migrated project"):
            self.check()

    def test_changed_snapshot_rejects(self):
        root, _ = self.migration("first", self.before)
        (root / "sources" / self.project / "kernel.qli").write_text("altered")
        with self.assertRaisesRegex(ValueError, "migration snapshot changed"):
            self.check()

    def test_extra_snapshot_rejects(self):
        root, _ = self.migration("first", self.before)
        (root / "sources" / self.project / "extra.qli").write_text("extra")
        with self.assertRaisesRegex(ValueError, "migration snapshot inventory changed"):
            self.check()

    def test_missing_observations_rejects(self):
        root, _ = self.migration("first", self.before)
        self.mutate(root / "migration.json", lambda m: m.update(observations=[]))
        with self.assertRaisesRegex(ValueError, "missing/duplicate migration observations"):
            self.check()

    def test_stale_observation_identity_rejects(self):
        root, _ = self.migration("first", self.before)
        self.mutate(root / "checks.json", lambda m: m.update(sources=self.before))
        with self.assertRaisesRegex(ValueError, "observation source identity mismatch"):
            self.check()

    def test_incomplete_observation_rejects(self):
        root, _ = self.migration("first", self.before)
        self.mutate(root / "checks.json", lambda m: m.update(results=[]))
        with self.assertRaisesRegex(ValueError, "incomplete migration observations"):
            self.check()

    def test_missing_command_rejects(self):
        root, _ = self.migration("first", self.before)
        self.mutate(root / "checks.json", lambda m: m["results"][0].pop("argv"))
        with self.assertRaisesRegex(ValueError, "missing migration command observation"):
            self.check()

    def test_contradictory_observation_rejects(self):
        root, _ = self.migration("first", self.before)
        self.mutate(root / "checks.json", lambda m: m["results"][0].update(exit_code=1))
        with self.assertRaisesRegex(ValueError, "contradictory migration observation"):
            self.check()

    def test_duplicate_json_fields_rejects(self):
        root, _ = self.migration("first", self.before)
        path = root / "migration.json"
        path.write_text(path.read_text()[:-1] + ', "format": 1}')
        with self.assertRaisesRegex(ValueError, "duplicate migration JSON field"):
            self.check()

    def test_malformed_path_list_rejects(self):
        self.paths = [{}]
        with self.assertRaisesRegex(ValueError, "invalid/duplicate source migration"):
            self.check()


class OracleTests(unittest.TestCase):
    def test_even_preparation_keeps_low_bit_on_all_input_columns(self):
        case = {"id": "quantum_katas/even_numbers3", "qubits": 3}
        for column in range(8):
            values = corpus.reference_column(case, column)
            self.assertTrue(all(value == 0 for row, value in enumerate(values)
                                if row % 2 != column % 2))
        self.assertEqual(corpus.reference_column(case, 0), [.5, 0, .5, 0, .5, 0, .5, 0])

    def test_half_rotations_keep_phase_in_y_interference(self):
        rx = {"id": "pennylane_demos/rotation_half_x", "qubits": 1}
        self.assertEqual(corpus.reference_column(rx, 0), [0, -1j])
        with self.assertRaises(corpus.SemanticMismatch):
            corpus.compare(corpus.interference([0, -1j], 1, "y"),
                           corpus.interference([0, 1], 1, "y"), "missing half-turn scalar")

    def test_greater_constant_equality_and_arbitrary_target(self):
        case = {"id": "qualtran/greater_constant2", "qubits": 3}
        for target in range(2):
            boundary = 1 + 4 * target
            above = 2 + 4 * target
            self.assertEqual(corpus.reference_column(case, boundary),
                             [int(row == boundary) for row in range(8)])
            self.assertEqual(corpus.reference_column(case, above),
                             [int(row == (above ^ 4)) for row in range(8)])

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

    def test_minus_preparation_requires_the_upstream_second_column(self):
        case = {"id": "quantum_katas/minus_state1", "qubits": 1}
        first = corpus.reference_column(case, 0)
        second = corpus.reference_column(case, 1)
        scale = 1 / math.sqrt(2)
        self.assertEqual(first, [scale, -scale])
        self.assertEqual(second, [scale, scale])
        # H X = Z H; adding Z on the input is the actual wrong extension.
        with self.assertRaises(ValueError):
            corpus.compare(corpus.interference(second, 0, "x"),
                           corpus.interference([-v for v in second], 0, "x"), "input phase")

    def test_decrement_and_zero_predicate_cover_wraparound_and_both_targets(self):
        case = {"id": "qualtran/add_minus_one3", "qubits": 3}
        for x in range(8):
            self.assertEqual(corpus.reference_column(case, x)[(x - 1) % 8], 1)
        case = {"id": "qualtran/less_than_one2", "qubits": 3}
        for x in range(4):
            for target in range(2):
                result = corpus.reference_column(case, x | (target << 2))
                self.assertEqual(result[x | ((target ^ (x == 0)) << 2)], 1)

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


class ReportTests(unittest.TestCase):
    def test_partial_results_and_failures_survive_parallel_completion(self):
        import subprocess
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "report.json"
            report = dict(status="incomplete", failures=[], cases=[], semantic_faults=[], negative_cases=[])
            def check(case, *args):
                if case["id"] == "bad":
                    raise subprocess.TimeoutExpired("compiler", 1, output=b"partial output", stderr=b"diagnostic")
                return dict(id=case["id"], semantic_probes=1)
            with patch.object(corpus, "check_case", side_effect=check), patch.object(corpus, "check_semantic_fault", side_effect=ValueError("escaped")), patch.object(corpus, "check_negative", return_value={"id": "negative"}):
                corpus.run_checks([dict(id="good"), dict(id="bad")], [dict(id="fault", reference="good")],
                                  [dict(id="negative")], Path("unused"), True, report, path)
            observed = json.loads(path.read_text())
            self.assertEqual(observed["cases"], [dict(id="good", semantic_probes=1)])
            self.assertEqual(observed["negative_cases"], [dict(id="negative")])
            self.assertEqual([f["id"] for f in observed["failures"]], ["bad", "fault"])
            self.assertEqual(observed["failures"][0]["stdout"], "partial output")
            self.assertEqual(observed["failures"][0]["stderr"], "diagnostic")
            self.assertEqual(observed["status"], "incomplete")

    def test_manifest_failure_overwrites_stale_success_with_failed_report(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "report.json"
            path.write_text('{"status":"passed"}')
            with patch.object(corpus, "check_manifest", side_effect=ValueError("invalid provenance")):
                self.assertEqual(corpus.main(["--report", str(path)]), 1)
            observed = json.loads(path.read_text())
            self.assertEqual(observed["status"], "failed")
            self.assertEqual(observed["failures"][0]["message"], "invalid provenance")
            self.assertIn("manifest_sha256", observed)

    def test_success_and_runtime_failure_keep_input_bindings(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "report.json"
            case = "quantum_katas/minus_state1"
            binary = Path(__file__).resolve()
            for failure in (False, True):
                def check(*args):
                    if failure:
                        raise corpus.SemanticMismatch("wrong phase")
                    return dict(id=case, semantic_probes=10)
                with patch.object(corpus, "check_case", side_effect=check), patch.object(corpus, "check_semantic_fault", return_value=dict(id="fault")), patch.object(corpus, "check_negative", side_effect=lambda c, b: dict(id=c["id"])):
                    self.assertEqual(corpus.main([str(binary), "--case", case, "--report", str(path)]), int(failure))
                observed = json.loads(path.read_text())
                self.assertEqual(observed["status"], "failed" if failure else "passed")
                self.assertEqual(observed["compiler_sha256"], corpus.sha256(binary))
                self.assertEqual(observed["expected_ids"]["cases"], [case])
                self.assertTrue(observed["source_sha256"])


if __name__ == "__main__":
    unittest.main()
