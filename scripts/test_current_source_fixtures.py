#!/usr/bin/env python3
"""Regressions for explicit historical/current source fixture selection.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import hashlib
import json
import copy
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import current_source_fixtures as fixtures


class SourceFixtureIdentity(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="qleisli-fixture-identity-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.original = self.root / "historical"
        self.current = self.root / "current"
        self.manifest = self.root / "source-map.json"
        self.namespace_manifest = self.root / "namespace-source-map.json"
        self.coherent_manifest = self.root / "coherent-source-map.json"
        self.checked_manifest = self.root / "checked-source-map.json"
        self.classical_manifest = self.root / "classical-source-map.json"
        self.qfor_manifest = self.root / "qfor-source-map.json"
        self.application_manifest = self.root / "application-source-map.json"
        self.application_manifest.write_text(json.dumps(dict(format="qleisli.operation-application-source-map", version=1, files=[], projects=[])))
        self.application_manifest = self.root / "application-source-map.json"
        self.application_manifest.write_text(json.dumps(dict(format="qleisli.operation-application-source-map", version=1, files=[], projects=[])))
        self.const_manifest = self.root / "const-source-map.json"
        self.const_manifest.write_text(json.dumps(dict(format="qleisli.const-parameter-source-map", version=1, files=[], projects=[])))
        self.qfor_manifest.write_text(json.dumps(dict(format="qleisli.qfor-source-map", version=1, files=[], projects=[])))
        self.classical_manifest.write_text(json.dumps(dict(format="qleisli.classical-function-source-map", version=1, files=[], projects=[])))
        files = []
        for directory in (self.original, self.current):
            directory.mkdir()
            (directory / "Qargo.toml").write_text('schema-version = 2\n[qrate]\nedition = "2026"\n')
            (directory / "main.qli").write_text(
                "observe fn main() -> " + ("CBit { false }" if directory == self.original else "Bit { 0 }"))
        for name in ("Qargo.toml", "main.qli"):
            files.append(dict(path=name, historical_sha256=self.sha(self.original / name),
                              current_sha256=self.sha(self.current / name)))
        self.entry = dict(historical_path="historical", current_path="current", files=files)
        self.write_map([self.entry])
        self.write_namespaces([])
        self.coherent_manifest.write_text(json.dumps(dict(
            format="qleisli.coherent-basis-source-map", version=1, files=[], projects=[])))
        self.write_checked_projects([])
        for name, value in (("ROOT", self.root), ("MAP", self.manifest),
                            ("NAMESPACE_MAP", self.namespace_manifest.name),
                            ("COHERENT_MAP", self.coherent_manifest.name),
                            ("CHECKED_MAP", self.checked_manifest.name),
                            ("CLASSICAL_MAP", self.classical_manifest.name),
                            ("QFOR_MAP", self.qfor_manifest.name),
                            ("CONST_MAP", self.const_manifest.name),
                            ("APPLICATION_MAP", self.application_manifest.name)):
            patched = patch.object(fixtures, name, value)
            patched.start()
            self.addCleanup(patched.stop)

    @staticmethod
    def sha(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def write_map(self, entries):
        self.manifest.write_text(json.dumps(dict(projects=entries)))

    def write_namespaces(self, entries):
        self.namespace_manifest.write_text(json.dumps(dict(
            format="qleisli.semantic-namespace-source-map", version=1, files=[], projects=entries)))

    def write_checked_projects(self, entries):
        self.checked_manifest.write_text(json.dumps(dict(
            format="qleisli.checked-operation-source-map", version=1, files=[], projects=entries)))

    def namespace_entry(self):
        self.selected = self.root / "namespace-current"
        shutil.copytree(self.current, self.selected)
        (self.selected / "main.qli").write_text(
            "use std::transform::qft2; observe fn main() -> Bit { 0 }")
        entry = dict(before_path="current", current_path="namespace-current", files=[
            dict(path=name, before_sha256=self.sha(self.current / name),
                 current_sha256=self.sha(self.selected / name))
            for name in ("Qargo.toml", "main.qli")])
        self.write_namespaces([entry])
        return entry

    def checked_project_entry(self):
        self.namespace_entry()
        self.coherent = self.root / "coherent-current"
        shutil.copytree(self.selected, self.coherent)
        (self.coherent / "main.qli").write_text(
            "fn f(q: Q<Bit>) -> Q<Bit> { apply[bind_op(u,m)](basis q as x { not x }) }")
        coherent_entry = dict(before_path="namespace-current", current_path="coherent-current", files=[
            dict(path=name, before_sha256=self.sha(self.selected / name),
                 current_sha256=self.sha(self.coherent / name))
            for name in ("Qargo.toml", "main.qli")])
        self.coherent_manifest.write_text(json.dumps(dict(
            format="qleisli.coherent-basis-source-map", version=1,
            files=[], projects=[coherent_entry])))
        self.checked = self.root / "checked-current"
        shutil.copytree(self.coherent, self.checked)
        source = self.checked / "main.qli"
        source.write_text(source.read_text().replace("bind_op", "checked_op"))
        entry = dict(before_path="coherent-current", current_path="checked-current", files=[
            dict(path=name, before_sha256=self.sha(self.coherent / name),
                 current_sha256=self.sha(self.checked / name))
            for name in ("Qargo.toml", "main.qli")])
        self.write_checked_projects([entry])
        return entry

    def test_selects_only_recorded_current_source_and_keeps_original(self):
        before = (self.original / "main.qli").read_bytes()
        self.assertEqual(fixtures.current_source_fixture(self.original), self.current)
        self.assertEqual((self.original / "main.qli").read_bytes(), before)
        self.assertEqual(fixtures.source_hashes(self.current), {
            file["path"]: file["current_sha256"] for file in self.entry["files"]})

    def test_stale_original_rejects(self):
        (self.original / "main.qli").write_text("changed historical source")
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_fixture(self.original)

    def test_stale_derivative_rejects(self):
        (self.current / "main.qli").write_text("changed current source")
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_fixture(self.original)

    def test_extra_source_or_manifest_rejects_in_either_snapshot(self):
        for directory in (self.original, self.current):
            for name in ("unused.qli", "nested/Qargo.toml"):
                with self.subTest(directory=directory.name, file=name):
                    extra = directory / name
                    extra.parent.mkdir(exist_ok=True)
                    extra.write_text("unexpected project input")
                    try:
                        with self.assertRaisesRegex(ValueError, "identity changed"):
                            fixtures.current_source_fixture(self.original)
                    finally:
                        extra.unlink()

    def test_missing_source_or_manifest_rejects_in_either_snapshot(self):
        for directory in (self.original, self.current):
            for name in ("main.qli", "Qargo.toml"):
                with self.subTest(directory=directory.name, file=name):
                    missing = directory / name
                    original = missing.read_bytes()
                    missing.unlink()
                    try:
                        with self.assertRaisesRegex(ValueError, "identity changed"):
                            fixtures.current_source_fixture(self.original)
                    finally:
                        missing.write_bytes(original)

    def test_missing_or_duplicate_project_mapping_rejects(self):
        for entries in ([], [self.entry, self.entry]):
            with self.subTest(entries=len(entries)):
                self.write_map(entries)
                with self.assertRaisesRegex(ValueError, "missing or duplicate"):
                    fixtures.current_source_fixture(self.original)

    def test_namespace_selection_checks_both_links_and_preserves_predecessors(self):
        entry = self.namespace_entry()
        original = (self.original / "main.qli").read_bytes()
        current = (self.current / "main.qli").read_bytes()
        self.assertEqual(fixtures.current_source_fixture(self.original), self.selected)
        self.assertEqual((self.original / "main.qli").read_bytes(), original)
        self.assertEqual((self.current / "main.qli").read_bytes(), current)
        self.assertEqual(fixtures.source_hashes(self.selected), {
            file["path"]: file["current_sha256"] for file in entry["files"]})

    def test_missing_namespace_map_rejects_without_previous_source_fallback(self):
        self.namespace_manifest.unlink()
        with self.assertRaisesRegex(ValueError, "missing semantic namespace source map"):
            fixtures.current_source_fixture(self.original)

    def test_missing_coherent_map_rejects_without_previous_project_fallback(self):
        self.coherent_manifest.unlink()
        with self.assertRaisesRegex(ValueError, "missing coherent basis source map"):
            fixtures.current_source_fixture(self.original)

    def test_missing_checked_map_rejects_without_previous_project_fallback(self):
        self.checked_manifest.unlink()
        with self.assertRaisesRegex(ValueError, "missing checked operation source map"):
            fixtures.current_source_fixture(self.original)

    def test_checked_project_chain_preserves_every_predecessor_and_complete_inventory(self):
        entry = self.checked_project_entry()
        before = {path: fixtures.source_hashes(path)
                  for path in (self.original, self.current, self.selected, self.coherent)}
        self.assertEqual(fixtures.current_source_fixture(self.original), self.checked)
        self.assertEqual({path: fixtures.source_hashes(path) for path in before}, before)
        self.assertEqual(fixtures.source_hashes(self.checked), {
            file["path"]: file["current_sha256"] for file in entry["files"]})

    def test_checked_map_cannot_hide_changed_coherent_project_predecessor(self):
        entry = self.checked_project_entry()
        source = self.coherent / "main.qli"
        source.write_text("changed predecessor")
        entry["files"][1]["before_sha256"] = self.sha(source)
        self.write_checked_projects([entry])
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_fixture(self.original)

    def test_checked_project_rejects_missing_extra_and_stale_final_inputs(self):
        self.checked_project_entry()
        source = self.checked / "main.qli"
        original = source.read_bytes()
        for change in ("missing", "stale", "extra"):
            with self.subTest(change=change):
                if change == "missing":
                    source.unlink()
                elif change == "stale":
                    source.write_text("stale final source")
                else:
                    (self.checked / "unexpected.qli").write_text("extra input")
                try:
                    with self.assertRaisesRegex(ValueError, "identity changed"):
                        fixtures.current_source_fixture(self.original)
                finally:
                    source.write_bytes(original)
                    (self.checked / "unexpected.qli").unlink(missing_ok=True)

    def test_checked_project_symlink_cannot_escape_snapshot(self):
        self.checked_project_entry()
        source = self.checked / "main.qli"
        source.unlink()
        source.symlink_to(self.coherent / "main.qli")
        with self.assertRaisesRegex(ValueError, "escaping"):
            fixtures.current_source_fixture(self.original)

    def test_unmapped_current_project_keeps_previous_selection(self):
        entry = self.namespace_entry()
        shutil.copytree(self.current, self.root / "other-current")
        entry["before_path"] = "other-current"
        self.write_namespaces([entry])
        self.assertEqual(fixtures.current_source_fixture(self.original), self.current)

    def test_namespace_cannot_hide_changed_original_or_prior_current(self):
        entry = self.namespace_entry()
        for directory in (self.original, self.current):
            with self.subTest(directory=directory.name):
                source = directory / "main.qli"
                before = source.read_bytes()
                source.write_text("changed previous source")
                if directory == self.current:
                    entry["files"][1]["before_sha256"] = self.sha(source)
                    self.write_namespaces([entry])
                try:
                    with self.assertRaisesRegex(ValueError, "identity changed"):
                        fixtures.current_source_fixture(self.original)
                finally:
                    source.write_bytes(before)

    def test_namespace_stale_before_hash_or_final_source_rejects(self):
        entry = self.namespace_entry()
        stale = copy.deepcopy(entry)
        stale["files"][1]["before_sha256"] = "0" * 64
        self.write_namespaces([stale])
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_fixture(self.original)
        self.write_namespaces([entry])
        (self.selected / "main.qli").write_text("changed final source")
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_fixture(self.original)

    def test_namespace_extra_source_or_manifest_rejects(self):
        self.namespace_entry()
        for name in ("unused.qli", "nested/Qargo.toml"):
            with self.subTest(file=name):
                extra = self.selected / name
                extra.parent.mkdir(exist_ok=True)
                extra.write_text("unrecorded selected input")
                try:
                    with self.assertRaisesRegex(ValueError, "identity changed"):
                        fixtures.current_source_fixture(self.original)
                finally:
                    extra.unlink()

    def test_namespace_missing_source_or_manifest_rejects(self):
        self.namespace_entry()
        for name in ("main.qli", "Qargo.toml"):
            with self.subTest(file=name):
                missing = self.selected / name
                before = missing.read_bytes()
                missing.unlink()
                try:
                    with self.assertRaisesRegex(ValueError, "identity changed"):
                        fixtures.current_source_fixture(self.original)
                finally:
                    missing.write_bytes(before)

    def test_namespace_partial_recorded_inventory_rejects(self):
        entry = self.namespace_entry()
        entry["files"].pop()
        self.write_namespaces([entry])
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_fixture(self.original)

    def test_namespace_duplicate_predecessor_or_destination_rejects(self):
        entry = self.namespace_entry()
        for other_before in ("current", "other-current"):
            with self.subTest(before=other_before):
                other = dict(entry, before_path=other_before)
                self.write_namespaces([entry, other])
                with self.assertRaisesRegex(ValueError, "duplicate namespace"):
                    fixtures.current_source_fixture(self.original)

    def test_duplicate_inventory_paths_reject_at_either_link(self):
        entry = self.namespace_entry()
        for prior in (True, False):
            with self.subTest(prior=prior):
                changed = copy.deepcopy(self.entry if prior else entry)
                changed["files"].append(changed["files"][0])
                self.write_map([changed if prior else self.entry])
                self.write_namespaces([entry if prior else changed])
                with self.assertRaisesRegex(ValueError, "duplicate source fixture file"):
                    fixtures.current_source_fixture(self.original)

    def test_unmapped_namespace_metadata_cannot_hide_duplicate_or_escaping_files(self):
        entry = self.namespace_entry()
        entry["before_path"] = "unselected-current"
        for escaping in (False, True):
            with self.subTest(escaping=escaping):
                changed = copy.deepcopy(entry)
                if escaping:
                    changed["files"][0]["path"] = "../outside.qli"
                else:
                    changed["files"].append(changed["files"][0])
                self.write_namespaces([changed])
                with self.assertRaises(ValueError):
                    fixtures.current_source_fixture(self.original)

    def test_escaping_project_paths_reject_at_either_link(self):
        entry = self.namespace_entry()
        for prior, field in ((True, "historical_path"), (True, "current_path"),
                             (False, "before_path"), (False, "current_path")):
            for escaping in ("../outside", str(self.root.parent / "outside")):
                with self.subTest(prior=prior, field=field, path=escaping):
                    changed = copy.deepcopy(self.entry if prior else entry)
                    changed[field] = escaping
                    self.write_map([changed if prior else self.entry])
                    self.write_namespaces([entry if prior else changed])
                    with self.assertRaisesRegex(ValueError, "escaping"):
                        fixtures.current_source_fixture(self.original)

    def test_escaping_file_paths_reject_at_either_link(self):
        entry = self.namespace_entry()
        for prior in (True, False):
            changed = copy.deepcopy(self.entry if prior else entry)
            changed["files"][0]["path"] = "../escape.qli"
            self.write_map([changed if prior else self.entry])
            self.write_namespaces([entry if prior else changed])
            with self.subTest(prior=prior), self.assertRaisesRegex(ValueError, "escaping"):
                fixtures.current_source_fixture(self.original)

    def test_project_or_source_symlink_cannot_escape_its_snapshot(self):
        entry = self.namespace_entry()
        external = tempfile.TemporaryDirectory(prefix="qleisli-fixture-outside-")
        self.addCleanup(external.cleanup)
        (self.root / "escaped-project").symlink_to(external.name, target_is_directory=True)
        self.write_namespaces([dict(entry, current_path="escaped-project")])
        with self.assertRaisesRegex(ValueError, "escaping"):
            fixtures.current_source_fixture(self.original)
        self.write_namespaces([entry])
        source = self.selected / "main.qli"
        source.unlink()
        source.symlink_to(self.current / "main.qli")
        with self.assertRaisesRegex(ValueError, "escaping"):
            fixtures.current_source_fixture(self.original)

    def test_duplicate_json_fields_and_wrong_namespace_schema_reject(self):
        self.namespace_entry()
        self.namespace_manifest.write_text('{"projects": [], "projects": []}')
        with self.assertRaisesRegex(ValueError, "duplicate source migration JSON field"):
            fixtures.current_source_fixture(self.original)
        self.namespace_manifest.write_text(json.dumps(dict(
            format="other-source-map", version=1, projects=[])))
        with self.assertRaisesRegex(ValueError, "invalid semantic namespace"):
            fixtures.current_source_fixture(self.original)


class SourceFileIdentity(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="qleisli-file-identity-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.original = self.root / "original.qli"
        self.namespace = self.root / "namespace.qli"
        self.coherent = self.root / "coherent.qli"
        self.current = self.root / "checked.qli"
        self.original.write_text("use std::routines::qft2; fn f(q: Q<Bit>) -> Q<Bit> { apply[bind_op(u,m)](do x <- q; pure not x) }")
        self.namespace.write_text("use std::transform::qft2; fn f(q: Q<Bit>) -> Q<Bit> { apply[bind_op(u,m)](do x <- q; pure not x) }")
        self.coherent.write_text("use std::transform::qft2; fn f(q: Q<Bit>) -> Q<Bit> { apply[bind_op(u,m)](basis q as x { not x }) }")
        self.current.write_text("use std::transform::qft2; fn f(q: Q<Bit>) -> Q<Bit> { apply[checked_op(u,m)](basis q as x { not x }) }")
        self.namespace_manifest = self.root / "namespace-map.json"
        self.coherent_manifest = self.root / "coherent-map.json"
        self.checked_manifest = self.root / "checked-map.json"
        self.classical_manifest = self.root / "classical-map.json"
        self.qfor_manifest = self.root / "qfor-map.json"
        self.application_manifest = self.root / "application-source-map.json"
        self.application_manifest.write_text(json.dumps(dict(format="qleisli.operation-application-source-map", version=1, files=[], projects=[])))
        self.application_manifest = self.root / "application-source-map.json"
        self.application_manifest.write_text(json.dumps(dict(format="qleisli.operation-application-source-map", version=1, files=[], projects=[])))
        self.const_manifest = self.root / "const-source-map.json"
        self.const_manifest.write_text(json.dumps(dict(format="qleisli.const-parameter-source-map", version=1, files=[], projects=[])))
        self.qfor_manifest.write_text(json.dumps(dict(format="qleisli.qfor-source-map", version=1, files=[], projects=[])))
        self.classical_manifest.write_text(json.dumps(dict(format="qleisli.classical-function-source-map", version=1, files=[], projects=[])))
        self.namespace_entry = self.entry(self.original, self.namespace)
        self.coherent_entry = self.entry(self.namespace, self.coherent)
        self.checked_entry = self.entry(self.coherent, self.current)
        self.write_maps()
        for name, value in (("ROOT", self.root),
                            ("NAMESPACE_MAP", self.namespace_manifest.name),
                            ("COHERENT_MAP", self.coherent_manifest.name),
                            ("CHECKED_MAP", self.checked_manifest.name),
                            ("CLASSICAL_MAP", self.classical_manifest.name),
                            ("QFOR_MAP", self.qfor_manifest.name),
                            ("CONST_MAP", self.const_manifest.name),
                            ("APPLICATION_MAP", self.application_manifest.name)):
            patched = patch.object(fixtures, name, value)
            patched.start()
            self.addCleanup(patched.stop)

    @staticmethod
    def sha(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def entry(self, before, current):
        return dict(before_path=before.relative_to(self.root).as_posix(),
                    current_path=current.relative_to(self.root).as_posix(),
                    before_sha256=self.sha(before), current_sha256=self.sha(current))

    def write_maps(self, namespace=None, coherent=None, checked=None):
        for path, format_name, entries in (
                (self.namespace_manifest, "qleisli.semantic-namespace-source-map",
                 [self.namespace_entry] if namespace is None else namespace),
                (self.coherent_manifest, "qleisli.coherent-basis-source-map",
                 [self.coherent_entry] if coherent is None else coherent),
                (self.checked_manifest, "qleisli.checked-operation-source-map",
                 [self.checked_entry] if checked is None else checked)):
            path.write_text(json.dumps(dict(format=format_name, version=1,
                                           files=entries, projects=[])))

    def test_complete_file_chain_keeps_all_predecessors(self):
        originals = {path: path.read_bytes() for path in (self.original, self.namespace, self.coherent)}
        self.assertEqual(fixtures.current_source_file(self.original), self.current)
        self.assertEqual(fixtures.current_source_file(self.original.name), self.current)
        self.assertEqual(fixtures.current_source_file(self.namespace), self.current)
        self.assertEqual(fixtures.current_source_file(self.coherent), self.current)
        self.assertEqual({path: path.read_bytes() for path in originals}, originals)

    def test_unmapped_file_is_returned_unchanged(self):
        source = self.root / "unmapped.qli"
        source.write_text("fn identity(q: Q<Bit>) -> Q<Bit> { q }")
        original = source.read_bytes()
        self.assertEqual(fixtures.current_source_file(source), source)
        self.assertEqual(source.read_bytes(), original)

    def test_classical_file_stage_preserves_every_previous_source(self):
        before = {path: path.read_bytes() for path in
                  (self.original, self.namespace, self.coherent, self.current)}
        selected = self.root / "classical-current.qli"
        selected.write_text("classical fn flip(b: Bit) -> Bit { not b }")
        entry = self.entry(self.current, selected)
        self.classical_manifest.write_text(json.dumps(dict(
            format="qleisli.classical-function-source-map", version=1,
            files=[entry], projects=[])))
        self.assertEqual(fixtures.current_source_file(self.original), selected)
        self.assertEqual({path: path.read_bytes() for path in before}, before)
        selected.write_text("changed classical function")
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_file(self.original)

    def test_missing_classical_stage_has_no_old_spelling_fallback(self):
        self.classical_manifest.unlink()
        with self.assertRaisesRegex(ValueError, "missing classical function source map"):
            fixtures.current_source_file(self.original)

    def test_quantum_fold_stage_preserves_history_and_rejects_stale_final_source(self):
        before = {path: path.read_bytes() for path in
                  (self.original, self.namespace, self.coherent, self.current)}
        selected = self.root / "qfor-current.qli"
        selected.write_text("fn f(q: Q<Bit>) -> Q<Bit> { qfor static i in 0..0 carry a=q { yield a; } }")
        self.qfor_manifest.write_text(json.dumps(dict(
            format="qleisli.qfor-source-map", version=1,
            files=[self.entry(self.current, selected)], projects=[])))
        self.assertEqual(fixtures.current_source_file(self.original), selected)
        self.assertEqual({path: path.read_bytes() for path in before}, before)
        selected.write_text("stale quantum fold source")
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_file(self.original)

    def test_missing_quantum_fold_stage_has_no_previous_source_fallback(self):
        self.qfor_manifest.unlink()
        with self.assertRaisesRegex(ValueError, "missing quantum fold source map"):
            fixtures.current_source_file(self.original)

    def test_const_stage_retains_history_and_rejects_stale_sources(self):
        before = self.current.read_bytes()
        selected = self.root / "const-current.qli"
        selected.write_text("fn identity[const n: Nat](q: Q<Bits<n>>) -> Q<Bits<n>> { q }")
        self.const_manifest.write_text(json.dumps(dict(
            format="qleisli.const-parameter-source-map", version=1,
            files=[self.entry(self.current, selected)], projects=[])))
        self.assertEqual(fixtures.current_source_file(self.original), selected)
        self.assertEqual(self.current.read_bytes(), before)
        selected.write_text("stale const source")
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_file(self.original)

    def test_missing_const_stage_has_no_previous_source_fallback(self):
        self.const_manifest.unlink()
        with self.assertRaisesRegex(ValueError, "missing const parameter source map"):
            fixtures.current_source_file(self.original)

    def test_application_stage_rejects_stale_final_source(self):
        original = self.current.read_bytes()
        selected = self.root / "application-current.qli"
        selected.write_text("unitary fn f(q: Q<Bit>) -> Q<Bit> { inverse(f)(q) }")
        self.application_manifest.write_text(json.dumps(dict(
            format="qleisli.operation-application-source-map", version=1,
            files=[self.entry(self.current, selected)], projects=[])))
        self.assertEqual(fixtures.current_source_file(self.original), selected)
        self.assertEqual(self.current.read_bytes(), original)
        selected.write_text("stale application source")
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_file(self.original)

    def test_missing_application_stage_has_no_previous_source_fallback(self):
        self.application_manifest.unlink()
        with self.assertRaisesRegex(ValueError, "missing operation application source map"):
            fixtures.current_source_file(self.original)

    def test_classical_stage_cannot_hide_stale_checked_predecessor(self):
        selected = self.root / "classical-current.qli"
        selected.write_text("classical fn flip(b: Bit) -> Bit { not b }")
        self.current.write_text("changed checked predecessor")
        self.classical_manifest.write_text(json.dumps(dict(
            format="qleisli.classical-function-source-map", version=1,
            files=[self.entry(self.current, selected)], projects=[])))
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_file(self.original)

    def test_all_file_maps_are_required_even_for_unmapped_input(self):
        for path, label in ((self.namespace_manifest, "semantic namespace"),
                            (self.coherent_manifest, "coherent basis"),
                            (self.checked_manifest, "checked operation")):
            with self.subTest(map=label):
                data = path.read_bytes()
                path.unlink()
                try:
                    with self.assertRaisesRegex(ValueError, f"missing {label} source map"):
                        fixtures.current_source_file(self.current)
                finally:
                    path.write_bytes(data)

    def test_stale_bytes_reject_at_every_selected_link(self):
        for path in (self.original, self.namespace, self.coherent, self.current):
            with self.subTest(source=path.name):
                original = path.read_bytes()
                path.write_text("changed source")
                try:
                    with self.assertRaisesRegex(ValueError, "identity changed"):
                        fixtures.current_source_file(self.original)
                finally:
                    path.write_bytes(original)

    def test_later_map_cannot_hide_changed_namespace_predecessor(self):
        self.namespace.write_text("changed predecessor")
        changed = dict(self.coherent_entry, before_sha256=self.sha(self.namespace))
        self.write_maps(coherent=[changed])
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_file(self.original)

    def test_checked_map_cannot_hide_changed_coherent_predecessor(self):
        self.coherent.write_text("changed predecessor")
        changed = dict(self.checked_entry, before_sha256=self.sha(self.coherent))
        self.write_maps(checked=[changed])
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_file(self.original)

    def test_missing_selected_source_rejects(self):
        self.current.unlink()
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_file(self.original)

    def test_duplicate_before_or_destination_rejects_in_every_map(self):
        for label, entry in (("namespace", self.namespace_entry),
                             ("coherent", self.coherent_entry), ("checked", self.checked_entry)):
            for field in ("before_path", "current_path"):
                with self.subTest(map=label, duplicate=field):
                    other = dict(entry)
                    other["current_path" if field == "before_path" else "before_path"] = "other.qli"
                    kwargs = {label: [entry, other]}
                    self.write_maps(**kwargs)
                    with self.assertRaisesRegex(ValueError, "duplicate.*source file migration"):
                        fixtures.current_source_file(self.original)
                    self.write_maps()

    def test_file_entries_require_exact_fields_hashes_and_source_extensions(self):
        changes = [dict(self.coherent_entry, unknown=True)]
        for field in ("before_sha256", "current_sha256"):
            changes.extend(dict(self.coherent_entry, **{field: value})
                           for value in (None, "0" * 63, "A" * 64))
        for field in ("before_path", "current_path"):
            changes.append(dict(self.coherent_entry, **{field: "source.txt"}))
        for changed in changes:
            with self.subTest(entry=changed):
                self.write_maps(coherent=[changed])
                with self.assertRaises(ValueError):
                    fixtures.current_source_file(self.original)

    def test_escaping_and_noncanonical_file_paths_reject_even_if_unmapped(self):
        for field in ("before_path", "current_path"):
            for path in ("../outside.qli", str(self.root / "absolute.qli"),
                         "nested//source.qli", "./source.qli", "nested/../source.qli"):
                with self.subTest(field=field, path=path):
                    changed = dict(self.coherent_entry, before_path="unmapped.qli")
                    changed[field] = path
                    self.write_maps(coherent=[changed])
                    with self.assertRaisesRegex(ValueError, "escaping|noncanonical"):
                        fixtures.current_source_file(self.original)

    def test_file_or_map_symlink_cannot_escape_root(self):
        external = tempfile.TemporaryDirectory(prefix="qleisli-file-outside-")
        self.addCleanup(external.cleanup)
        outside = Path(external.name)
        (outside / "source.qli").write_text("outside source")
        self.current.unlink()
        self.current.symlink_to(outside / "source.qli")
        with self.assertRaisesRegex(ValueError, "escaping"):
            fixtures.current_source_file(self.original)
        self.current.unlink()
        self.current.write_text("current source")
        self.checked_manifest.unlink()
        self.checked_manifest.symlink_to(outside / "map.json")
        with self.assertRaisesRegex(ValueError, "escaping"):
            fixtures.current_source_file(self.original)

    def test_map_identity_and_duplicate_json_fields_reject(self):
        for path in (self.namespace_manifest, self.coherent_manifest, self.checked_manifest):
            original = path.read_text()
            for invalid in (original.replace('"version": 1', '"version": true'),
                            original.replace('"version": 1', '"version": 2'),
                            original.replace('"format": "qleisli.', '"format": "wrong.'),
                            original.replace('"before_sha256":', '"current_sha256":', 1)):
                with self.subTest(map=path.name, data=invalid):
                    path.write_text(invalid)
                    with self.assertRaises(ValueError):
                        fixtures.current_source_file(self.original)
            path.write_text(original)

    def test_malformed_json_or_missing_map_inventories_reject(self):
        for path in (self.namespace_manifest, self.coherent_manifest, self.checked_manifest):
            original = path.read_text()
            for invalid in ("not JSON", "[]", "{}", original.replace('"files": [', '"omitted": [')):
                with self.subTest(map=path.name, data=invalid):
                    path.write_text(invalid)
                    with self.assertRaises(ValueError):
                        fixtures.current_source_file(self.original)
            path.write_text(original)

    def test_unselected_project_metadata_is_not_ignored_by_file_selection(self):
        data = json.loads(self.checked_manifest.read_text())
        data["projects"] = [dict(before_path="unselected", current_path="../outside", files=[])]
        self.checked_manifest.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "escaping"):
            fixtures.current_source_file(self.original)


class RepositoryMigrationTests(unittest.TestCase):
    def test_qpe_application_map_changes_only_adopted_operator_forms(self):
        data = json.loads((fixtures.ROOT / fixtures.APPLICATION_MAP).read_text())
        entries = fixtures._file_entries(data, "operation application")
        self.assertEqual(len(entries), 1)
        entry = next(iter(entries.values()))
        before = fixtures.ROOT / entry["before_path"]
        current = fixtures.ROOT / entry["current_path"]
        transformed = before.read_bytes().replace(
            b'controlled(repeat_op(2^k,U))', b'controlled(power(U,2^k))').replace(
            b'adjoint(fourier[m],phase)', b'inverse(fourier[m])(phase)')
        self.assertNotEqual(transformed, before.read_bytes())
        self.assertEqual(current.read_bytes(), transformed)
        self.assertEqual(fixtures.current_source_file(
            "corpus/sized/qualtran_qpe/estimation.qli"), current)

    def test_actual_quantum_fold_map_has_canonical_entries_and_matching_sources(self):
        # Synthetic maps alone did not catch explanatory metadata inserted in
        # real strict file records. Exercise the same entry point as Rust tests.
        data = json.loads((fixtures.ROOT / fixtures.QFOR_MAP).read_text())
        entries = fixtures._file_entries(data, "quantum fold")
        self.assertEqual(len(entries), 16)
        for entry in entries.values():
            before = fixtures.ROOT / entry["before_path"]
            current = fixtures.ROOT / entry["current_path"]
            self.assertEqual(fixtures.current_source_file(before),
                             fixtures.current_source_file(current))

    def test_const_map_changes_only_parameter_markers(self):
        import re
        data = json.loads((fixtures.ROOT / fixtures.CONST_MAP).read_text())
        entries = fixtures._file_entries(data, "const parameter")
        expected = {p.relative_to(fixtures.ROOT).as_posix() for p in
                    (fixtures.ROOT / "corpus/sized").rglob("*.qli")
                    if "qualtran_qft" not in p.parts}
        destinations = set()
        for entry in entries.values():
            before = fixtures.ROOT / entry["before_path"]
            current = fixtures.ROOT / entry["current_path"]
            self.assertEqual(fixtures.current_source_file(before),
                             fixtures.current_source_file(current))
            transformed, count = re.subn(rb"\bstatic(?= [A-Za-z_]\w*\s*:)",
                                        b"const", before.read_bytes())
            self.assertGreater(count, 0)
            self.assertEqual(current.read_bytes(), transformed)
            destinations.add(current.relative_to(
                fixtures.ROOT / "tests/fixtures/frontend_v030/const-parameters/current").as_posix())
        self.assertEqual(destinations, expected)


if __name__ == "__main__":
    unittest.main()
