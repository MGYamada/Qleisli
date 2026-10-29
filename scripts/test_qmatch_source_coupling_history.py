"""Passively verify original qmatch counterexample and repair history.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import hashlib
import io
import json
import lzma
from pathlib import Path, PurePosixPath
import tarfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
README = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/README.md"
ARCHIVE = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/first.tar.xz"
INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/index.json"
VALIDATION = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/validation.json"


class OriginalCouplingHistory(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.index = json.loads((ROOT / INDEX).read_text())
        cls.archive = (ROOT / ARCHIVE).read_bytes()
        if len(cls.archive) > 1024 * 1024:
            raise ValueError("historical archive exceeds expected bounded size")
        with lzma.open(io.BytesIO(cls.archive)) as stream:
            data = stream.read(32 * 1024 * 1024 + 1)
        if len(data) > 32 * 1024 * 1024:
            raise ValueError("historical container exceeds expected bounded size")
        cls.members = {}
        with tarfile.open(fileobj=io.BytesIO(data)) as archive:
            for member in archive:
                name = PurePosixPath(member.name)
                if (not member.isfile() or name.is_absolute() or ".." in name.parts
                        or member.name in cls.members or member.name not in cls.index["records"]):
                    raise ValueError("nonregular, duplicate or unlisted history member")
                cls.members[member.name] = archive.extractfile(member).read()

    def test_every_original_byte_is_retained(self):
        self.assertEqual(set(self.members), set(self.index["records"]))
        self.assertEqual(len(self.members), 785)
        self.assertEqual(hashlib.sha256(self.archive).hexdigest(), self.index["archive"]["sha256"])
        self.assertEqual(len(self.archive), self.index["archive"]["bytes"])
        for name, content in self.members.items():
            with self.subTest(member=name):
                self.assertEqual(len(content), self.index["records"][name]["bytes"])
                self.assertEqual(hashlib.sha256(content).hexdigest(), self.index["records"][name]["sha256"])
        self.assertTrue((ROOT / README).is_file())

    def test_first_failure_and_separate_repair_keep_their_scopes(self):
        def report(label):
            return json.loads(self.members[f"observations/{label}/report.json.txt"])

        self.assertEqual(report("source-sector-runtime-first")["exit_code"], 1)
        first = (self.members["observations/source-sector-runtime-first/stdout.txt"]
                 + self.members["observations/source-sector-runtime-first/stderr.txt"])
        self.assertIn(b"UNRESOLVED: source-function substitution survived", first)
        self.assertEqual(report("source-sector-runtime-fourth")["exit_code"], 0)
        self.assertIn(b"22 bounded source/evidence observations passed",
                      self.members["observations/source-sector-runtime-fourth/stdout.txt"])
        current = json.loads((ROOT / VALIDATION).read_text())
        self.assertEqual(current["goal"]["issue195"], "OPEN")
        self.assertIn("NOT RUN", current["uncompleted_checks"]["proof_records"])


if __name__ == "__main__":
    unittest.main()
