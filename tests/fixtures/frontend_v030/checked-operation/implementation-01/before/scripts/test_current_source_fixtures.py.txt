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
        for name, value in (("ROOT", self.root), ("MAP", self.manifest),
                            ("NAMESPACE_MAP", self.namespace_manifest.name),
                            ("COHERENT_MAP", self.coherent_manifest.name)):
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
        self.current = self.root / "coherent.qli"
        self.original.write_text("use std::routines::qft2; fn f(q: Q<Bit>) -> Q<Bit> { do x <- q; pure not x }")
        self.namespace.write_text("use std::transform::qft2; fn f(q: Q<Bit>) -> Q<Bit> { do x <- q; pure not x }")
        self.current.write_text("use std::transform::qft2; fn f(q: Q<Bit>) -> Q<Bit> { basis q as x { not x } }")
        self.namespace_manifest = self.root / "namespace-map.json"
        self.coherent_manifest = self.root / "coherent-map.json"
        self.namespace_entry = self.entry(self.original, self.namespace)
        self.coherent_entry = self.entry(self.namespace, self.current)
        self.write_maps()
        for name, value in (("ROOT", self.root),
                            ("NAMESPACE_MAP", self.namespace_manifest.name),
                            ("COHERENT_MAP", self.coherent_manifest.name)):
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

    def write_maps(self, namespace=None, coherent=None):
        for path, format_name, entries in (
                (self.namespace_manifest, "qleisli.semantic-namespace-source-map",
                 [self.namespace_entry] if namespace is None else namespace),
                (self.coherent_manifest, "qleisli.coherent-basis-source-map",
                 [self.coherent_entry] if coherent is None else coherent)):
            path.write_text(json.dumps(dict(format=format_name, version=1,
                                           files=entries, projects=[])))

    def test_complete_file_chain_keeps_both_predecessors(self):
        originals = {path: path.read_bytes() for path in (self.original, self.namespace)}
        self.assertEqual(fixtures.current_source_file(self.original), self.current)
        self.assertEqual(fixtures.current_source_file(self.original.name), self.current)
        self.assertEqual(fixtures.current_source_file(self.namespace), self.current)
        self.assertEqual({path: path.read_bytes() for path in originals}, originals)

    def test_unmapped_file_is_returned_unchanged(self):
        source = self.root / "unmapped.qli"
        source.write_text("fn identity(q: Q<Bit>) -> Q<Bit> { q }")
        original = source.read_bytes()
        self.assertEqual(fixtures.current_source_file(source), source)
        self.assertEqual(source.read_bytes(), original)

    def test_both_file_maps_are_required_even_for_unmapped_input(self):
        for path, label in ((self.namespace_manifest, "semantic namespace"),
                            (self.coherent_manifest, "coherent basis")):
            with self.subTest(map=label):
                data = path.read_bytes()
                path.unlink()
                try:
                    with self.assertRaisesRegex(ValueError, f"missing {label} source map"):
                        fixtures.current_source_file(self.current)
                finally:
                    path.write_bytes(data)

    def test_stale_bytes_reject_at_every_selected_link(self):
        for path in (self.original, self.namespace, self.current):
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

    def test_missing_selected_source_rejects(self):
        self.current.unlink()
        with self.assertRaisesRegex(ValueError, "identity changed"):
            fixtures.current_source_file(self.original)

    def test_duplicate_before_or_destination_rejects_in_either_map(self):
        for label, entry in (("namespace", self.namespace_entry), ("coherent", self.coherent_entry)):
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
        self.coherent_manifest.unlink()
        self.coherent_manifest.symlink_to(outside / "map.json")
        with self.assertRaisesRegex(ValueError, "escaping"):
            fixtures.current_source_file(self.original)

    def test_map_identity_and_duplicate_json_fields_reject(self):
        for path in (self.namespace_manifest, self.coherent_manifest):
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
        for path in (self.namespace_manifest, self.coherent_manifest):
            original = path.read_text()
            for invalid in ("not JSON", "[]", "{}", original.replace('"files": [', '"omitted": [')):
                with self.subTest(map=path.name, data=invalid):
                    path.write_text(invalid)
                    with self.assertRaises(ValueError):
                        fixtures.current_source_file(self.original)
            path.write_text(original)

    def test_unselected_project_metadata_is_not_ignored_by_file_selection(self):
        data = json.loads(self.coherent_manifest.read_text())
        data["projects"] = [dict(before_path="unselected", current_path="../outside", files=[])]
        self.coherent_manifest.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "escaping"):
            fixtures.current_source_file(self.original)


if __name__ == "__main__":
    unittest.main()
