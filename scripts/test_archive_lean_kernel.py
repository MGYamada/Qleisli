#!/usr/bin/env python3
"""Distribution archives reject changed payloads and incomplete proof validation.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

from archive_lean_kernel import archive_bundle, sha


class ArchiveTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.bundle = self.root / "bundle"
        self.source = self.root / "source"
        self.source.mkdir()
        (self.source / "Main.lean").write_text("-- retained source\n")
        self.files = {"bin/qleisli-kernel": b"executable", "LICENSE": b"Apache-2.0",
                      "NOTICE": b"notice", "lean-runtime-licenses/LICENSE": b"Lean license"}
        for name, data in self.files.items():
            path = self.bundle / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        self.manifest = dict(format="qleisli.native-bundle", version=1,
                             package_version="0.2.9", platform="Darwin", machine="arm64",
                             validation=dict(lane="full", fresh_replay=True),
                             sources={"Main.lean": sha((self.source / "Main.lean").read_bytes())},
                             files={name: sha(data) for name, data in self.files.items()})

    def archive(self, destination="output"):
        (self.bundle / "manifest.json").write_text(json.dumps(self.manifest))
        return archive_bundle(self.bundle, self.root / destination, "a" * 40, self.source)

    def test_roundtrip_modes_licenses_binding_and_checksum(self):
        archive = self.archive()
        self.assertEqual(archive.name, "qleisli-kernel-0.2.9-aarch64-apple-darwin.tar.gz")
        self.assertEqual(Path(str(archive) + ".sha256").read_text(), f"{sha(archive.read_bytes())}  {archive.name}\n")
        with tarfile.open(archive) as tar:
            entries = {entry.name.split("/", 1)[1]: entry for entry in tar}
            for name, data in self.files.items():
                self.assertEqual(tar.extractfile(entries[name]).read(), data)
            self.assertEqual(entries["bin/qleisli-kernel"].mode, 0o755)
            self.assertEqual(json.load(tar.extractfile(entries["distribution.json"]))["source_commit"], "a" * 40)
        self.assertEqual(archive.read_bytes(), self.archive("second").read_bytes())
        with self.assertRaisesRegex(ValueError, "already exists"):
            self.archive()

    def test_changed_payload_or_source_cannot_be_distributed(self):
        (self.bundle / "bin/qleisli-kernel").write_bytes(b"changed")
        with self.assertRaisesRegex(ValueError, "hashes differ"):
            self.archive()
        (self.bundle / "bin/qleisli-kernel").write_bytes(self.files["bin/qleisli-kernel"])
        (self.source / "Main.lean").write_text("changed")
        with self.assertRaisesRegex(ValueError, "source identity differs"):
            self.archive()

    def test_tests_lane_or_missing_fresh_replay_cannot_be_released(self):
        for validation in [dict(lane="tests", fresh_replay=False), dict(lane="full", fresh_replay=False)]:
            self.manifest["validation"] = validation
            with self.assertRaisesRegex(ValueError, "full fresh proof replay"):
                self.archive()

    def test_symlinks_extra_files_and_missing_licenses_reject(self):
        (self.bundle / "link").symlink_to("LICENSE")
        with self.assertRaisesRegex(ValueError, "link/special"):
            self.archive()
        (self.bundle / "link").unlink()
        (self.bundle / "extra").write_text("unbound")
        with self.assertRaisesRegex(ValueError, "hashes differ"):
            self.archive()
        (self.bundle / "extra").unlink()
        (self.bundle / "NOTICE").unlink()
        del self.manifest["files"]["NOTICE"]
        with self.assertRaisesRegex(ValueError, "required licenses"):
            self.archive()


if __name__ == "__main__":
    unittest.main()
