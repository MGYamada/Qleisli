"""Detect accidental evidence loss without turning records into executable input."""
from pathlib import Path
import hashlib
import json
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
        source = b"observe fn main() -> CBit { true }\n"
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


if __name__ == "__main__":
    unittest.main()
