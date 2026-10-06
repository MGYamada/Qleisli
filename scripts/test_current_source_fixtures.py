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
        for name, value in (("ROOT", self.root), ("MAP", self.manifest),
                            ("NAMESPACE_MAP", self.namespace_manifest.name)):
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
            format="qleisli.semantic-namespace-source-map", version=1, projects=entries)))

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


if __name__ == "__main__":
    unittest.main()
