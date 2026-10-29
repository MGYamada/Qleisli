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
OPERANDS = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/operands-first.tar.xz"
OPERAND_INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/operands-index.json"
OPERAND_VALIDATION = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/operands-validation.json"
TRANSPORT = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/transport-first.tar.xz"
TRANSPORT_INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/transport-index.json"
TRANSPORT_VALIDATION = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/transport-validation.json"
NATIVE_BINDING = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/native-binding-first.tar.xz"
NATIVE_BINDING_INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/native-binding-index.json"
NATIVE_BINDING_VALIDATION = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/native-binding-validation.json"


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

    def test_operand_counterexamples_and_generated_partial_repair(self):
        index = json.loads((ROOT / OPERAND_INDEX).read_text())
        compressed = (ROOT / OPERANDS).read_bytes()
        self.assertLessEqual(len(compressed), 1024 * 1024)
        self.assertEqual(hashlib.sha256(compressed).hexdigest(), index["sha256"])
        with lzma.open(io.BytesIO(compressed)) as stream:
            contents = stream.read(32 * 1024 * 1024 + 1)
        self.assertLessEqual(len(contents), 32 * 1024 * 1024)
        members = {}
        with tarfile.open(fileobj=io.BytesIO(contents)) as archive:
            for member in archive:
                name = PurePosixPath(member.name)
                self.assertTrue(member.isfile())
                self.assertFalse(name.is_absolute())
                self.assertNotIn("..", name.parts)
                self.assertNotIn(member.name, members)
                self.assertIn(member.name, index["records"])
                content = archive.extractfile(member).read()
                self.assertEqual(len(content), index["records"][member.name]["bytes"])
                self.assertEqual(hashlib.sha256(content).hexdigest(), index["records"][member.name]["sha256"])
                members[member.name] = content
        self.assertEqual(set(members), set(index["records"]))
        self.assertEqual(len(members), 195)
        for label in ("source-operands-first", "source-operands-effect-first",
                      "source-operands-equal-width-first", "source-operands-audit"):
            self.assertEqual(json.loads(members[f"observations/{label}/report.json.txt"])["exit_code"], 1)
        self.assertIn(b"partial project declaration", members["observations/source-operands-audit/stdout.txt"])
        for label in ("source-operands-final", "source-evidence-final", "source-operands-effect-final",
                      "source-operands-equal-width-final", "source-operands-audit-second"):
            self.assertEqual(json.loads(members[f"observations/{label}/report.json.txt"])["exit_code"], 0)
        current = json.loads((ROOT / OPERAND_VALIDATION).read_text())
        self.assertFalse(current["native_activated"])

    def test_original_transport_mismatch_and_repairs_are_inert_and_retained(self):
        index = json.loads((ROOT / TRANSPORT_INDEX).read_text())
        compressed = (ROOT / TRANSPORT).read_bytes()
        self.assertLessEqual(len(compressed), 1024 * 1024)
        self.assertEqual(hashlib.sha256(compressed).hexdigest(), index["sha256"])
        with lzma.open(io.BytesIO(compressed)) as stream:
            contents = stream.read(32 * 1024 * 1024 + 1)
        self.assertLessEqual(len(contents), 32 * 1024 * 1024)
        members = {}
        with tarfile.open(fileobj=io.BytesIO(contents)) as archive:
            for member in archive:
                name = PurePosixPath(member.name)
                self.assertTrue(member.isfile())
                self.assertFalse(name.is_absolute())
                self.assertNotIn("..", name.parts)
                self.assertNotIn(member.name, members)
                self.assertIn(member.name, index["records"])
                content = archive.extractfile(member).read()
                self.assertEqual(len(content), index["records"][member.name]["bytes"])
                self.assertEqual(hashlib.sha256(content).hexdigest(), index["records"][member.name]["sha256"])
                members[member.name] = content
        self.assertEqual(set(members), set(index["records"]))
        self.assertEqual(len(members), 112)
        for label, code in [("qmatch-shape-runtime-first", 1), ("qmatch-shape-runtime-second", 0),
                            ("qmatch-protocol-runtime-first", 1), ("qmatch-protocol-runtime-second", 0),
                            ("qmatch-complete-order-first", 1), ("qmatch-complete-order-second", 0),
                            ("qmatch-transport-tests-first", 1), ("qmatch-transport-tests-second", 0),
                            ("qmatch-execution-runtime-observed-first", 1),
                            ("qmatch-execution-runtime-observed-second", 0)]:
            self.assertEqual(json.loads(members[f"observations/{label}/report.json.txt"])["exit_code"], code)
        self.assertIn(b"port-bits-outside-u8: expected false, observed true",
                      members["observations/qmatch-shape-runtime-first/stdout.txt"])
        self.assertIn(b"2 exact phase controls and 24 QLV3",
                      members["observations/qmatch-execution-runtime-observed-second/stdout.txt"])
        notes = json.loads(members["observations/observer-notes.json.txt"])
        self.assertIn("neither a semantic", notes["first_native_observation"])
        current = json.loads((ROOT / TRANSPORT_VALIDATION).read_text())
        self.assertFalse(current["native_activated"])
        self.assertEqual(current["goal"]["percent"], 58.27)

    def test_first_retained_graph_compile_failure_and_native_test_limits_survive(self):
        index = json.loads((ROOT / NATIVE_BINDING_INDEX).read_text())
        compressed = (ROOT / NATIVE_BINDING).read_bytes()
        self.assertLessEqual(len(compressed), 1024 * 1024)
        self.assertEqual(hashlib.sha256(compressed).hexdigest(), index["sha256"])
        with lzma.open(io.BytesIO(compressed)) as stream:
            contents = stream.read(32 * 1024 * 1024 + 1)
        self.assertLessEqual(len(contents), 32 * 1024 * 1024)
        members = {}
        with tarfile.open(fileobj=io.BytesIO(contents)) as archive:
            for member in archive:
                name = PurePosixPath(member.name)
                self.assertTrue(member.isfile())
                self.assertFalse(name.is_absolute())
                self.assertNotIn("..", name.parts)
                self.assertNotIn(member.name, members)
                self.assertIn(member.name, index["records"])
                content = archive.extractfile(member).read()
                self.assertEqual(len(content), index["records"][member.name]["bytes"])
                self.assertEqual(hashlib.sha256(content).hexdigest(), index["records"][member.name]["sha256"])
                members[member.name] = content
        self.assertEqual(len(members), 167)
        self.assertEqual(set(members), set(index["records"]))
        first = json.loads(members["observations/qmatch-rust-binding-first/report.json.txt"])
        self.assertEqual(first["exit_code"], 101)
        self.assertIn(b"3 previous errors", members["observations/qmatch-rust-binding-first/0.stderr.txt"])
        for label in ["qmatch-rust-binding-second", "qmatch-rust-binding-msrv"]:
            self.assertEqual(json.loads(members[f"observations/{label}/report.json.txt"])["exit_code"], 0)
            self.assertIn(b"3 passed; 0 failed; 2 ignored", members[f"observations/{label}/0.stdout.txt"])
        current = json.loads((ROOT / NATIVE_BINDING_VALIDATION).read_text())
        self.assertFalse(current["compiled_native_validated"])
        self.assertEqual(current["goal"]["issue195"], "OPEN")


if __name__ == "__main__":
    unittest.main()
