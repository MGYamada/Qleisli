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
CI_TYPECHECK = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/ci-typecheck-first.tar.xz"
CI_TYPECHECK_INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/ci-typecheck-index.json"
CI_TYPECHECK_VALIDATION = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/ci-typecheck-validation.json"
NOMINAL = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/nominal-first.tar.xz"
NOMINAL_INDEX = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/nominal-index.json"
NOMINAL_VALIDATION = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/nominal-validation.json"
BODY_ROOT = "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030"


def bounded_history(directory, stem):
    """Read inert member bytes only; never extract or replay saved commands."""
    index = json.loads((directory / (stem + '-index.json')).read_text())
    packed = (directory / index['archive']).read_bytes()
    if (len(packed) > 1024 * 1024 or len(packed) != index['bytes']
            or hashlib.sha256(packed).hexdigest() != index['sha256']):
        raise ValueError('history archive identity/capacity differs')
    decoder = lzma.LZMADecompressor(format=lzma.FORMAT_XZ, memlimit=64 * 1024 * 1024)
    expanded = decoder.decompress(packed, max_length=32 * 1024 * 1024 + 1)
    if len(expanded) > 32 * 1024 * 1024 or not decoder.eof or decoder.unused_data:
        raise ValueError('incomplete, trailing or oversized history')
    members = {}
    with tarfile.open(fileobj=io.BytesIO(expanded)) as archive:
        for entry in archive:
            name = PurePosixPath(entry.name)
            if (not entry.isfile() or name.is_absolute() or '..' in name.parts
                    or entry.name in members or entry.name not in index['records']):
                raise ValueError('unlisted, duplicate or nonregular history member')
            content = archive.extractfile(entry).read()
            row = index['records'][entry.name]
            if len(content) != row['bytes'] or hashlib.sha256(content).hexdigest() != row['sha256']:
                raise ValueError('history member identity differs')
            members[entry.name] = content
    if set(members) != set(index['records']):
        raise ValueError('history member missing')
    return members


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

    def test_first_hosted_failure_stays_distinct_from_component_repair(self):
        index = json.loads((ROOT / CI_TYPECHECK_INDEX).read_text())
        packed = (ROOT / CI_TYPECHECK).read_bytes()
        self.assertEqual(len(packed), index["bytes"])
        self.assertEqual(hashlib.sha256(packed).hexdigest(), index["sha256"])
        self.assertLessEqual(len(packed), 1024 * 1024)
        with lzma.open(io.BytesIO(packed)) as stream:
            expanded = stream.read(32 * 1024 * 1024 + 1)
        self.assertLessEqual(len(expanded), 32 * 1024 * 1024)
        members = {}
        with tarfile.open(fileobj=io.BytesIO(expanded)) as archive:
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
        self.assertEqual(len(members), 9)
        self.assertEqual(set(members), set(index["records"]))
        self.assertEqual(json.loads(members["observed/kernel-build.command.json.txt"])["exit_code"], 1)
        self.assertIn("Unknown identifier `α`", members["observed/kernel-build.stdout.txt"].decode())
        self.assertIn(b"autoImplicit", members["observed/kernel-build.stdout.txt"])
        repaired = json.loads(members["repair/changed-sources-report.json.txt"])
        self.assertEqual(repaired["exit_code"], 0)
        self.assertTrue(repaired["stable_inputs"])
        self.assertEqual(len(repaired["commands"]), 98)
        self.assertTrue(all(row["exit_code"] == 0 for row in repaired["commands"]))
        current = json.loads((ROOT / CI_TYPECHECK_VALIDATION).read_text())
        self.assertFalse(current["compiled_native_validated"])
        self.assertEqual(current["issue195"], "OPEN")

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


    def test_complete_body_failures_and_remaining_native_obligations_survive(self):
        directory = ROOT / BODY_ROOT
        index = json.loads((directory / 'body-index.json').read_text())
        packed = (directory / 'body-first.tar.xz').read_bytes()
        self.assertLessEqual(len(packed), 1024 * 1024)
        self.assertEqual(len(packed), index['bytes'])
        self.assertEqual(hashlib.sha256(packed).hexdigest(), index['sha256'])
        with lzma.open(io.BytesIO(packed)) as stream:
            expanded = stream.read(32 * 1024 * 1024 + 1)
        self.assertLessEqual(len(expanded), 32 * 1024 * 1024)
        members = {}
        with tarfile.open(fileobj=io.BytesIO(expanded)) as archive:
            for entry in archive:
                self.assertTrue(entry.isfile())
                self.assertFalse(PurePosixPath(entry.name).is_absolute())
                self.assertNotIn('..', PurePosixPath(entry.name).parts)
                self.assertNotIn(entry.name, members)
                self.assertIn(entry.name, index['records'])
                content = archive.extractfile(entry).read()
                self.assertEqual(len(content), index['records'][entry.name]['bytes'])
                self.assertEqual(hashlib.sha256(content).hexdigest(), index['records'][entry.name]['sha256'])
                members[entry.name] = content
        self.assertEqual(set(members), set(index['records']))
        self.assertEqual(len(members), 151)
        failed = json.loads(members['observations/qmatch-complete-body-runtime-first/report.json.txt'])
        passed = json.loads(members['observations/qmatch-complete-body-runtime-second/report.json.txt'])
        self.assertEqual(failed['exit_code'], 1)
        self.assertIn(b'Gate.Error.decodedView', members['observations/qmatch-complete-body-runtime-first/stderr.txt'])
        self.assertEqual(passed['exit_code'], 0)
        self.assertIn(b'4 exact controls and 8 QLV3', members['observations/qmatch-complete-body-runtime-second/stdout.txt'])
        current = json.loads((directory / 'body-validation.json').read_text())
        self.assertFalse(current['compiled_native_validated'])
        self.assertEqual(current['issue195'], 'OPEN')

    def test_raw_owner_counterexample_and_matching_permutation_remain_distinct(self):
        directory = ROOT / BODY_ROOT
        members = bounded_history(directory, 'owner-flow')
        self.assertEqual(len(members), 118)
        first = members['observations/qmatch-raw-return-owner-swap-first/stderr.txt']
        second = members['observations/qmatch-raw-return-owner-swap-second/stderr.txt']
        self.assertIn(b'Gate.Error.decodedView', first)
        self.assertIn(b'qmatch original bytes/acceptance mismatch', second)
        current = json.loads(members['observations/qmatch-raw-owner-flow-permutation-context-first/report.json.txt'])
        self.assertEqual(current['exit_code'], 0)
        self.assertTrue(current['stable_inputs'])
        self.assertIn(b'5 exact controls and 9 QLV3',
                      members['observations/qmatch-raw-owner-flow-permutation-context-first/stdout.txt'])
        validation = json.loads((directory / 'owner-flow-validation.json').read_text())
        self.assertFalse(validation['compiled_native_validated'])
        self.assertEqual(validation['issue195'], 'OPEN')

    def test_nominal_first_proposals_and_precise_refusals_remain_separate(self):
        index = json.loads((ROOT / NOMINAL_INDEX).read_text())
        packed = (ROOT / NOMINAL).read_bytes()
        self.assertLessEqual(len(packed), 1024 * 1024)
        self.assertEqual(len(packed), index["bytes"])
        self.assertEqual(hashlib.sha256(packed).hexdigest(), index["sha256"])
        with lzma.open(io.BytesIO(packed)) as stream:
            data = stream.read(32 * 1024 * 1024 + 1)
        self.assertLessEqual(len(data), 32 * 1024 * 1024)
        members = {}
        with tarfile.open(fileobj=io.BytesIO(data)) as archive:
            for member in archive:
                self.assertTrue(member.isfile())
                self.assertFalse(PurePosixPath(member.name).is_absolute())
                self.assertNotIn("..", PurePosixPath(member.name).parts)
                self.assertNotIn(member.name, members)
                self.assertIn(member.name, index["records"])
                content = archive.extractfile(member).read()
                self.assertEqual(len(content), index["records"][member.name]["bytes"])
                self.assertEqual(hashlib.sha256(content).hexdigest(), index["records"][member.name]["sha256"])
                members[member.name] = content
        self.assertEqual(set(members), set(index["records"]))
        self.assertEqual(len(members), 72)
        for label in ["qmatch-nominal-context-first", "qmatch-nominal-context-third"]:
            self.assertEqual(json.loads(members[f"observations/{label}/report.json.txt"])["exit_code"], 1)
        self.assertIn(b"Finite.Error.invalid", members["observations/qmatch-nominal-context-first/stderr.txt"])
        self.assertIn(b"Gate.Error.decodedView", members["observations/qmatch-nominal-context-third/stderr.txt"])
        self.assertEqual(json.loads(members["observations/qmatch-nominal-maintained-first/report.json.txt"])["exit_code"], 0)
        diagnostics = members["observations/qmatch-nominal-context-diagnostic/stdout.txt"]
        self.assertEqual(diagnostics.count(b"Finite.Error.equation"), 10)
        self.assertEqual(diagnostics.count(b"Finite.Error.request"), 12)
        self.assertEqual(diagnostics.count(b"Gate.Error.decodedView"), 2)
        current = json.loads((ROOT / NOMINAL_VALIDATION).read_text())
        self.assertFalse(current["compiled_native_validated"])
        self.assertEqual(current["issue195"], "OPEN")


if __name__ == "__main__":
    unittest.main()
