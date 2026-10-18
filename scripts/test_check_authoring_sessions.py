"""Detect accidental evidence loss without turning records into executable input."""
from pathlib import Path
import hashlib
import json
import os
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
from check_authoring_sessions import check_session


class AuthoringRecords(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root / "attempt-01").mkdir()
        source = b"observe fn main() -> Bit { 1 }\n"
        (self.root / "attempt-01/main.qli").write_bytes(source)
        (self.root / "context.md").write_text("An informed authoring session.")
        self.event = dict(command=["qleisli", "check", "attempt-01"], recorded_utc="2026-09-28T00:00:00Z", exit_code=0, stdout=dict(format="qleisli.result", version=1, outcome="ok"))
        self.data = dict(format=1, kind="informed_first_attempt", task="example", author="test", project_version="0.1.8", baseline_commit="a" * 40, context="context.md", attempts=[dict(id="attempt-01", reason="initial", sha256={"main.qli": hashlib.sha256(source).hexdigest()}, observations=["check.json"])])
        self.save()

    def save(self):
        (self.root / "session.json").write_text(json.dumps(self.data))
        (self.root / "check.json").write_text(json.dumps(self.event))

    def check(self):
        return check_session(self.root / "session.json")

    def test_first_success_needs_no_fabricated_repair(self):
        self.assertEqual(self.check(), (1, 1))

    def test_snapshot_edits_are_detected(self):
        (self.root / "attempt-01/main.qli").write_text("changed")
        with self.assertRaisesRegex(ValueError, "hash mismatch"):
            self.check()

    def test_unregistered_source_is_detected(self):
        (self.root / "attempt-01/helper.qli").write_text("extra")
        with self.assertRaisesRegex(ValueError, "inventory"):
            self.check()

    def test_missing_observations_and_false_success_are_detected(self):
        self.event["exit_code"] = 1
        self.save()
        with self.assertRaisesRegex(ValueError, "contradicts"):
            self.check()
        (self.root / "check.json").unlink()
        with self.assertRaisesRegex(ValueError, "missing"):
            self.check()

    def test_context_cannot_escape_and_attempts_cannot_disappear(self):
        self.data["context"] = "../outside.md"
        self.save()
        with self.assertRaisesRegex(ValueError, "relative path"):
            self.check()
        self.data["context"] = "context.md"
        self.save()
        (self.root / "attempt-02").mkdir()
        with self.assertRaisesRegex(ValueError, "unregistered attempt"):
            self.check()

    def test_reports_preserve_diagnostics_without_fabricated_command_metadata(self):
        (self.root / "report.json").write_text(json.dumps({"diagnostic": "historical error"}))
        self.data["attempts"][0]["reports"] = ["report.json"]
        self.save()
        self.assertEqual(self.check(), (1, 1))
        (self.root / "report.json").unlink()
        with self.assertRaisesRegex(ValueError, "missing"):
            self.check()

    def test_related_sources_have_independent_hashes_and_local_paths(self):
        source = self.root / "client.qli"
        source.write_bytes(b"client")
        record = dict(id="client-01", reason="related client", sha256={"client.qli": hashlib.sha256(b"client").hexdigest()})
        self.data["source_records"] = [record]
        self.save()
        self.assertEqual(check_session(self.root / "session.json", repository=self.root), (1, 1))
        source.write_bytes(b"changed")
        with self.assertRaisesRegex(ValueError, "source record hash mismatch"):
            check_session(self.root / "session.json", repository=self.root)
        record["sha256"] = {"../client.qli": "0" * 64}
        self.save()
        with self.assertRaisesRegex(ValueError, "relative path"):
            check_session(self.root / "session.json", repository=self.root)


class RetainedSourceRecords(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.repository = Path(temporary.name)
        self.authoring = self.repository / "tests/fixtures/authoring_sessions"
        self.session = self.authoring / "probe/session.json"
        (self.session.parent / "attempt-01").mkdir(parents=True)
        source = b"observe fn main() -> Bit { 1 }\n"
        (self.session.parent / "attempt-01/main.qli").write_bytes(source)
        (self.session.parent / "context.md").write_text("Retained related-source test.")
        event = dict(command=["never-run-recorded-command"], recorded_utc="2026-10-17T00:00:00Z", exit_code=0,
                     stdout=dict(format="qleisli.result", version=1, outcome="ok"))
        (self.session.parent / "check.json").write_text(json.dumps(event))
        self.old = b"use std::quantum::h;\n"
        self.logical = "examples/probe.qli"
        self.digest = hashlib.sha256(self.old).hexdigest()
        self.data = dict(format=1, kind="informed_first_attempt", task="retention", author="test", project_version="0.1.8",
                         baseline_commit="a" * 40, context="context.md", attempts=[dict(id="attempt-01", reason="initial",
                         sha256={"main.qli": hashlib.sha256(source).hexdigest()}, observations=["check.json"])],
                         source_records=[dict(id="related-01", reason="related source", sha256={self.logical: self.digest})])
        self.session.write_text(json.dumps(self.data))
        self.active = self.repository / self.logical
        self.active.parent.mkdir()
        self.active.write_bytes(b"// Current language-owned h needs no import.\n")
        self.copy = self.authoring / "retained-source-records-v1/probe/related-01/examples/probe.qli.txt"
        self.copy.parent.mkdir(parents=True)
        self.copy.write_bytes(self.old)
        self.entry = dict(kind="source_record", session="probe/session.json", id="related-01", path=self.logical,
                          session_sha256=hashlib.sha256(self.session.read_bytes()).hexdigest(), sha256=self.digest,
                          git_commit="b" * 40, git_blob=hashlib.sha1(b"blob " + str(len(self.old)).encode() + b"\0" + self.old).hexdigest())
        self.index = self.authoring / "retained-source-records-v1.json"
        self.write_index()

    def write_index(self):
        self.index.write_text(json.dumps(dict(format=1, entries=[self.entry])))

    def check(self):
        return check_session(self.session, repository=self.repository)

    def test_fixed_copy_preserves_history_without_git_or_current_source_identity(self):
        before = self.session.read_bytes()
        self.assertFalse((self.repository / ".git").exists())
        self.assertEqual(self.check(), (1, 1))
        self.assertEqual(self.session.read_bytes(), before)
        self.assertNotEqual(hashlib.sha256(self.active.read_bytes()).hexdigest(), self.digest)
        self.active.write_bytes(b"another active migration")
        self.assertEqual(self.check(), (1, 1))

    def test_wrong_copy_never_falls_back_to_matching_active_bytes(self):
        self.active.write_bytes(self.old)
        self.copy.write_bytes(b"changed")
        with self.assertRaisesRegex(ValueError, "retained source hash mismatch"):
            self.check()

    def test_missing_copy_does_not_fall_back(self):
        self.active.write_bytes(self.old)
        self.copy.unlink()
        with self.assertRaisesRegex(ValueError, "missing or nonlocal"):
            self.check()

    def test_original_session_and_expected_hash_cannot_drift(self):
        self.session.write_bytes(self.session.read_bytes() + b"\n")
        with self.assertRaisesRegex(ValueError, "original session hash mismatch"):
            self.check()
        self.entry["session_sha256"] = hashlib.sha256(self.session.read_bytes()).hexdigest()
        self.entry["sha256"] = "0" * 64
        self.write_index()
        with self.assertRaisesRegex(ValueError, "original record path/hash"):
            self.check()

    def test_copy_paths_are_derived_and_source_class_is_fixed(self):
        for value in ["../outside.qli", "examples/other.qli", "examples/report.json"]:
            with self.subTest(path=value):
                self.entry["path"] = value
                self.write_index()
                with self.assertRaises(ValueError):
                    self.check()
        self.entry["path"] = self.logical
        self.entry["kind"] = "attempt"
        self.write_index()
        with self.assertRaisesRegex(ValueError, "source_record class"):
            self.check()
        self.entry["kind"] = "source_record"
        self.entry["retained_path"] = "arbitrary/source.qli"
        self.write_index()
        with self.assertRaisesRegex(ValueError, "source_record class"):
            self.check()

    def test_extra_copies_and_unregistered_directory_reject(self):
        (self.copy.parent / "unrelated.qli.txt").write_bytes(b"unrelated")
        with self.assertRaisesRegex(ValueError, "inventory"):
            self.check()
        self.index.unlink()
        with self.assertRaisesRegex(ValueError, "unregistered"):
            self.check()

    def test_recovery_blob_and_duplicate_index_rows_are_checked(self):
        self.entry["git_blob"] = "0" * 40
        self.write_index()
        with self.assertRaisesRegex(ValueError, "recovery blob mismatch"):
            self.check()
        self.entry["git_blob"] = hashlib.sha1(b"blob " + str(len(self.old)).encode() + b"\0" + self.old).hexdigest()
        self.index.write_text(json.dumps(dict(format=1, entries=[self.entry, self.entry])))
        with self.assertRaisesRegex(ValueError, "duplicate retained source"):
            self.check()

    @unittest.skipUnless(hasattr(os, "mkfifo"), "requires POSIX FIFO support")
    def test_unindexed_fifo_is_rejected_without_opening_it(self):
        os.mkfifo(self.copy.parent / "unindexed.fifo")
        with self.assertRaisesRegex(ValueError, "nonregular archive entries"):
            self.check()

    def test_symbolic_link_cannot_replace_retained_copy(self):
        self.copy.unlink()
        self.active.write_bytes(self.old)
        self.copy.symlink_to(self.active)
        with self.assertRaisesRegex(ValueError, "symbolic links"):
            self.check()


if __name__ == "__main__":
    unittest.main()
