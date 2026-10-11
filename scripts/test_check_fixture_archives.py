"""Adversarial tests for historical archive integrity.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import copy
import gzip
import io
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import check_fixture_archives as check


class ArchiveIntegrity(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.prefix = "tests/fixtures/history"
        self.name = self.prefix + "/original.txt"
        self.archive = self.root / "tests/fixtures/history.tar.gz"
        self.archive.parent.mkdir(parents=True)
        self.manifest = self.root / "tests/fixtures/history.archive.json"
        self.data = {
            "format": "qleisli.historical-fixture-archive", "version": 1,
            "source_commit": "a" * 40, "prefix": self.prefix,
            "archive": "tests/fixtures/history.tar.gz", "archive_sha256": "",
            "entries": {self.name: {"bytes": 8, "sha256": check.sha(b"original"),
                                    "mode": "100644"}},
        }
        self.pack([(self.name, b"original", None)])

    def pack(self, members):
        with tarfile.open(self.archive, "w:gz") as tar:
            for name, content, kind in members:
                info = tarfile.TarInfo(name)
                info.mode = 0o644
                info.size = len(content)
                if kind is not None:
                    info.type = kind
                    info.linkname = self.name
                tar.addfile(info, io.BytesIO(content))
        self.data["archive_sha256"] = check.sha(self.archive.read_bytes())
        self.write()

    def write(self):
        self.manifest.write_text(json.dumps(self.data))

    def verify(self, **kwargs):
        return check.verify(self.root, self.manifest, **kwargs)

    def test_valid_and_missing_member(self):
        self.assertEqual(self.verify(), (1, 8))
        self.pack([])
        with self.assertRaisesRegex(ValueError, "missing archived"):
            self.verify()

    def test_duplicate_member(self):
        self.pack([(self.name, b"original", None)] * 2)
        with self.assertRaisesRegex(ValueError, "duplicate"):
            self.verify()

    def test_content_and_mode_changes(self):
        self.pack([(self.name, b"tampered", None)])
        with self.assertRaisesRegex(ValueError, "content differs"):
            self.verify()
        self.pack([(self.name, b"original", None)])
        self.data["entries"][self.name]["mode"] = "100755"
        self.write()
        with self.assertRaisesRegex(ValueError, "mode differs"):
            self.verify()

    def test_links_traversal_and_unlisted_members(self):
        for name, kind in [(self.name, tarfile.SYMTYPE),
                           (self.name, tarfile.LNKTYPE),
                           ("tests/fixtures/../escape", None),
                           ("tests/fixtures/extra", None)]:
            with self.subTest(name=name, kind=kind):
                self.pack([(name, b"original", kind)])
                with self.assertRaises(ValueError):
                    self.verify()

    def test_container_expansion_is_bounded_before_tar_parsing(self):
        self.archive.write_bytes(gzip.compress(b"x" * 16385))
        self.data["archive_sha256"] = check.sha(self.archive.read_bytes())
        self.write()
        with patch.object(check, "MAX_BYTES", 2048), patch.object(check, "MAX_MEMBERS", 2):
            with self.assertRaisesRegex(ValueError, "container exceeds capacity"):
                self.verify()

    def test_archive_identity(self):
        self.data["archive_sha256"] = "0" * 64
        self.write()
        with self.assertRaisesRegex(ValueError, "digest mismatch"):
            self.verify()

    def test_fail_closed_manifest_and_expansion(self):
        baseline = copy.deepcopy(self.data)
        mutations = [lambda d: d.update(version=True),
                     lambda d: d.update(unknown="ignored"),
                     lambda d: d["entries"][self.name].update(bytes=check.MAX_BYTES + 1),
                     lambda d: d.update(prefix="tests/fixtures/other")]
        for mutate in mutations:
            self.data = copy.deepcopy(baseline)
            mutate(self.data)
            self.write()
            with self.assertRaises(ValueError):
                self.verify()
        self.manifest.write_text('{"version":1,"version":1}')
        with self.assertRaisesRegex(ValueError, "duplicate JSON"):
            self.verify()

    def test_complete_git_inventory_and_original_bytes(self):
        def git(*args):
            return subprocess.check_output(["git", *args], cwd=self.root).decode().strip()
        git("init", "-q")
        git("config", "user.name", "Archive test")
        git("config", "user.email", "archive@example.invalid")
        source = self.root / self.name
        source.parent.mkdir(parents=True)
        source.write_bytes(b"original")
        git("add", self.name)
        git("commit", "-qm", "original")
        self.data["source_commit"] = git("rev-parse", "HEAD")
        self.write()
        self.assertEqual(self.verify(git_baseline=True), (1, 8))
        # A self-consistent rewritten archive still cannot replace Git originals.
        self.data["entries"][self.name]["sha256"] = check.sha(b"tampered")
        self.pack([(self.name, b"tampered", None)])
        with self.assertRaisesRegex(ValueError, "original Git source"):
            self.verify(git_baseline=True)
        self.data["entries"][self.name]["sha256"] = check.sha(b"original")
        self.pack([(self.name, b"original", None)])
        (source.parent / "omitted.txt").write_bytes(b"other")
        git("add", self.prefix)
        git("commit", "-qm", "second original")
        self.data["source_commit"] = git("rev-parse", "HEAD")
        self.write()
        with self.assertRaisesRegex(ValueError, "bounded inventory|complete Git"):
            self.verify(git_baseline=True)


if __name__ == "__main__":
    unittest.main()
