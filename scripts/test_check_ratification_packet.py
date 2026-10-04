"""Adversarial checks for candidate integrity without claiming ratification.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
from check_ratification_packet import GOVERNANCE_SNAPSHOT, ISSUE_URL, PACKET_PATH, PacketError, check_packet


@unittest.skipUnless(os.open in os.supports_dir_fd and hasattr(os, "O_NOFOLLOW"),
                     "descriptor-relative no-follow file reads are required")
class RatificationCandidate(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name).resolve()
        self.constitution = "# Qleisli 2026 Constitution\n\n## Preamble\nCandidate text.\n"
        self.constitution += "".join(f"\n## Article {n} — Title\nCandidate text.\n"
                                   for n in ("I", "II", "III", "IV", "V", "VI", "VII", "VIII", "IX"))
        self.write("CONSTITUTION.md", self.constitution)
        self.write("GOVERNANCE.md", "# Governance candidate\nNo appointment has occurred.\n")
        self.write(GOVERNANCE_SNAPSHOT, (self.root / "GOVERNANCE.md").read_text())
        self.issue_path = "tests/fixtures/constitution_v030/issue-129.json"
        self.baseline_path = "tests/fixtures/constitution_v030/baseline.json"
        self.issue = dict(number=129, url=ISSUE_URL, updatedAt="2026-10-04T01:45:16Z", body="Draft 5 body")
        self.write(self.issue_path, json.dumps(self.issue))
        self.write(self.baseline_path, '{"sources": []}')
        self.packet = dict(
            format="qleisli.ratification-candidate", version=1, edition="2026",
            status="awaiting-human-ratification", proposed_guardian="Masahiko G. Yamada",
            source_issue=dict(number=129, url=ISSUE_URL, updated_at=self.issue["updatedAt"],
                              body_path=self.issue_path, body_sha256=self.digest(self.issue_path)),
            artifacts=[dict(path=name, sha256=self.digest(name))
                       for name in ("CONSTITUTION.md", "GOVERNANCE.md")],
            baseline=dict(manifest_path=self.baseline_path, manifest_sha256=self.digest(self.baseline_path)),
            human_ratification=None, binding_interpretations=[], discharged_guarantees=[])
        self.save()

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        return path

    def digest(self, name):
        return hashlib.sha256((self.root / name).read_bytes()).hexdigest()

    def save(self):
        self.write(PACKET_PATH, json.dumps(self.packet))

    def rejected(self, phrase=None):
        with self.assertRaisesRegex(PacketError, phrase or ".+"):
            check_packet(self.root)

    def test_candidate_integrity_never_establishes_ratification(self):
        check_packet(self.root)
        with self.assertRaisesRegex(PacketError, "human ratification event required"):
            check_packet(self.root, require_ratified=True)
        before = {p.relative_to(self.root): p.read_bytes() for p in self.root.rglob("*") if p.is_file()}
        script = Path(__file__).with_name("check_ratification_packet.py")
        result = subprocess.run([sys.executable, str(script), "--root", str(self.root)],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Historical ratification candidate", result.stdout)
        self.assertIn("pending status is archived", result.stdout)
        self.assertIn("does not verify human approval", result.stdout)
        result = subprocess.run([sys.executable, str(script), "--root", str(self.root), "--require-ratified"],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn("human ratification event required", result.stderr)
        self.assertEqual(before, {p.relative_to(self.root): p.read_bytes()
                                  for p in self.root.rglob("*") if p.is_file()})

    def test_status_and_approval_cannot_confer_authority(self):
        original = copy.deepcopy(self.packet)
        for field, value in (("status", "ratified"), ("human_ratification", True),
                             ("human_ratification", "approved"),
                             ("human_ratification", {"human": "Masahiko G. Yamada"}),
                             ("proposed_guardian", "AI proxy"),
                             ("binding_interpretations", ["binding"]),
                             ("discharged_guarantees", ["Soundness"])):
            with self.subTest(field=field, value=value):
                self.packet = copy.deepcopy(original)
                self.packet[field] = value
                self.save()
                self.rejected()

    def test_schema_rejects_unknown_missing_and_wrong_typed_fields(self):
        original = copy.deepcopy(self.packet)
        for field, value in (("version", True), ("version", "1"), ("edition", 2026),
                             ("edition", "2027"), ("format", "ratified"),
                             ("artifacts", {}), ("binding_interpretations", {}),
                             ("discharged_guarantees", False), ("unknown", "field")):
            with self.subTest(field=field, value=value):
                self.packet = copy.deepcopy(original)
                self.packet[field] = value
                self.save()
                self.rejected()
        del self.packet["edition"]
        self.save()
        self.rejected()

    def test_changed_and_missing_files_reject(self):
        for name in ("CONSTITUTION.md", GOVERNANCE_SNAPSHOT, self.issue_path, self.baseline_path):
            with self.subTest(name=name):
                path = self.root / name
                original = path.read_bytes()
                path.write_bytes(original + b"\nchanged\n")
                self.rejected("SHA-256 mismatch")
                path.unlink()
                self.rejected("cannot read")
                path.write_bytes(original)

    def test_digest_and_artifact_set_are_strict(self):
        original = copy.deepcopy(self.packet)
        for value in ("A" * 64, "a" * 63, None, 12):
            with self.subTest(value=value):
                self.packet = copy.deepcopy(original)
                self.packet["artifacts"][0]["sha256"] = value
                self.save()
                self.rejected("SHA-256 digest")
        for artifacts in ([], original["artifacts"][:1], [original["artifacts"][0]] * 2,
                          original["artifacts"] + [original["artifacts"][0]],
                          [dict(path="OTHER.md", sha256="a" * 64), original["artifacts"][1]]):
            with self.subTest(artifacts=artifacts):
                self.packet = copy.deepcopy(original)
                self.packet["artifacts"] = artifacts
                self.save()
                self.rejected("artifacts")

    def test_duplicate_fields_reject_in_all_json_inputs(self):
        packet_text = (self.root / PACKET_PATH).read_text()
        self.write(PACKET_PATH, packet_text.replace('"version": 1', '"version": 1, "version": 1'))
        self.rejected("duplicate JSON field")
        self.save()
        self.write(PACKET_PATH, packet_text.replace('"number": 129', '"number": 129, "number": 129'))
        self.rejected("duplicate JSON field")
        self.save()
        self.write(self.issue_path, json.dumps(self.issue).replace('"number": 129', '"number": 129, "number": 129'))
        self.packet["source_issue"]["body_sha256"] = self.digest(self.issue_path)
        self.save()
        self.rejected("duplicate JSON field")
        self.write(self.issue_path, json.dumps(self.issue))
        self.packet["source_issue"]["body_sha256"] = self.digest(self.issue_path)
        self.write(self.baseline_path, '{"sources": [], "sources": []}')
        self.packet["baseline"]["manifest_sha256"] = self.digest(self.baseline_path)
        self.save()
        self.rejected("duplicate JSON field")

    def test_source_issue_identity_and_timestamp_must_match(self):
        original = copy.deepcopy(self.packet)
        for field, value in (("number", 128), ("number", True), ("url", ISSUE_URL + "/"),
                             ("updated_at", "2026-10-04"), ("updated_at", "2026-99-04T01:45:16Z"),
                             ("updated_at", "2026-10-04T01:45:17Z")):
            with self.subTest(field=field, value=value):
                self.packet = copy.deepcopy(original)
                self.packet["source_issue"][field] = value
                self.save()
                self.rejected()
        self.packet = copy.deepcopy(original)
        for field, value in (("number", 128), ("number", True), ("url", "https://example.org/129"),
                             ("updatedAt", "2026-10-04T01:45:17Z"), ("body", ""), ("body", [])):
            with self.subTest(saved_field=field, value=value):
                saved = dict(self.issue)
                saved[field] = value
                self.write(self.issue_path, json.dumps(saved))
                self.packet["source_issue"]["body_sha256"] = self.digest(self.issue_path)
                self.save()
                self.rejected("saved number")

    def test_paths_cannot_escape_or_alias(self):
        original = copy.deepcopy(self.packet)
        for path in ("../outside.json", str(self.root / self.baseline_path), "./baseline.json",
                     "tests//baseline.json", "tests/../baseline.json", "tests\\baseline.json",
                     "C:/outside.json", "tests/\x00baseline.json", ".", ""):
            with self.subTest(path=path):
                self.packet = copy.deepcopy(original)
                self.packet["baseline"]["manifest_path"] = path
                self.save()
                self.rejected("path")

    def test_symlink_artifact_and_intermediate_directory_reject(self):
        path = self.root / GOVERNANCE_SNAPSHOT
        content = path.read_text()
        self.write("other.md", content)
        path.unlink()
        path.symlink_to(self.root / "other.md")
        self.rejected("cannot read")
        path.unlink()
        path.write_text(content)
        fixture = self.root / "tests/fixtures/constitution_v030"
        moved = self.root / "saved-fixture"
        fixture.rename(moved)
        fixture.symlink_to(moved, target_is_directory=True)
        self.rejected("cannot read")

    @unittest.skipUnless(hasattr(os, "mkfifo"), "FIFO needs Unix")
    def test_special_file_rejects_without_waiting_for_a_writer(self):
        path = self.root / GOVERNANCE_SNAPSHOT
        path.unlink()
        os.mkfifo(path)
        self.rejected("regular file")

    def test_active_governance_is_not_substituted_for_approved_snapshot(self):
        self.write("GOVERNANCE.md", "Active status now refers to the recorded human event.\n")
        check_packet(self.root)
        (self.root / GOVERNANCE_SNAPSHOT).unlink()
        self.rejected("cannot read")

    def test_constitution_sections_and_excluded_notes_are_checked(self):
        for text in (self.constitution.replace("## Article IV", "## Article III"),
                     self.constitution.replace("## Preamble", "Preamble"),
                     "```markdown\n" + self.constitution + "```\n",
                     self.constitution + "\n## Explanatory notes — not proposed constitutional text\nNotes\n"):
            with self.subTest(text=text[-100:]):
                self.write("CONSTITUTION.md", text)
                self.packet["artifacts"][0]["sha256"] = self.digest("CONSTITUTION.md")
                self.save()
                self.rejected("CONSTITUTION.md")

    def test_malformed_and_nonstandard_json_reject(self):
        for value in ("[]", "null", '{"version": NaN}', '{"version": Infinity}', "{"):
            with self.subTest(value=value):
                self.write(PACKET_PATH, value)
                self.rejected()
        (self.root / PACKET_PATH).write_bytes(b"\xff")
        self.rejected("UTF-8 JSON")


if __name__ == "__main__":
    unittest.main()
