#!/usr/bin/env python3
"""Regressions for explicit historical/current source fixture selection.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import hashlib
import json
from pathlib import Path
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
        for name, value in (("ROOT", self.root), ("MAP", self.manifest)):
            patched = patch.object(fixtures, name, value)
            patched.start()
            self.addCleanup(patched.stop)

    @staticmethod
    def sha(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def write_map(self, entries):
        self.manifest.write_text(json.dumps(dict(projects=entries)))

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


if __name__ == "__main__":
    unittest.main()
