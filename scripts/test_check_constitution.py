"""Recorded identities, pending obligations and trusted-base regression checks.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
import check_constitution as checker
from check_ratification_packet import GOVERNANCE_SNAPSHOT, PACKET_PATH, ROOT, PacketError
from test_check_initial_guarantees import copy_evidence_fixture


@unittest.skipUnless(os.open in os.supports_dir_fd and hasattr(os, "O_NOFOLLOW"),
                     "descriptor-relative no-follow file reads are required")
class ConstitutionalRecords(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name).resolve()
        # These are the exact historical inputs, not synthesized human approvals.
        for name in (*checker.FROZEN_PATHS, checker.LEDGER_PATH):
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / name, target)
        copy_evidence_fixture(self.root)
        self.event = json.loads((self.root / checker.EVENT_PATH).read_text())
        self.adoption = json.loads((self.root / checker.ADOPTION_PATH).read_text())
        self.admission = json.loads((self.root / checker.ADMISSION_PATH).read_text())
        self.ledger = json.loads((self.root / checker.LEDGER_PATH).read_text())
        self.ledger["current_evidence"]["sha256"] = self.digest(checker.CURRENT_PATH)
        self.write_json(checker.LEDGER_PATH, self.ledger)
        self.bootstrap_bytes = (self.root / checker.BOOTSTRAP_PATH).read_bytes()
        self.bootstrap = json.loads(self.bootstrap_bytes)
        self.pending_bytes = (self.root / checker.PENDING_PATH).read_bytes()
        self.pending = json.loads(self.pending_bytes)

    def write_json(self, name, value):
        (self.root / name).write_text(json.dumps(value), encoding="utf-8")

    def digest(self, name):
        return hashlib.sha256((self.root / name).read_bytes()).hexdigest()

    def rejected(self, phrase=None, **kwargs):
        with self.assertRaisesRegex(PacketError, phrase or ".+"):
            checker.check_constitution(self.root, **kwargs)

    def git(self, *args):
        # These disposable repositories must not leave background maintenance
        # writing .git after the subprocess returns and cleanup begins.
        return subprocess.run(["git", "-C", str(self.root), "-c", "user.name=Record Test",
                               "-c", "user.email=record-test@example.invalid", "-c", "commit.gpgsign=false",
                               "-c", "core.hooksPath=/dev/null", "-c", "maintenance.auto=false",
                               "-c", "gc.auto=0", "-c", "gc.autoDetach=false", *args],
                              check=True, capture_output=True).stdout

    def commit(self):
        self.git("add", "--all")
        self.git("commit", "--quiet", "-m", "Test baseline")
        return self.git("rev-parse", "HEAD").decode().strip()

    def test_recorded_identity_is_not_release_readiness_or_independent_authentication(self):
        checker.check_constitution(self.root)
        self.rejected("three broader binding interpretations remain pending", require_release_ready=True)
        script = Path(__file__).with_name("check_constitution.py")
        result = subprocess.run([sys.executable, str(script), "--root", str(self.root)],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("two scoped guarantee admissions verified", result.stdout)
        self.assertIn("not independently established", result.stdout)
        self.assertIn("Three broader binding interpretations remain pending", result.stdout)
        result = subprocess.run([sys.executable, str(script), "--root", str(self.root), "--require-release-ready"],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn("admission is not release approval", result.stderr)

    def test_changed_or_removed_exact_records_reject(self):
        for name in checker.FROZEN_PATHS:
            with self.subTest(name=name):
                path = self.root / name
                original = path.read_bytes()
                path.write_bytes(original + b"\nchanged\n")
                self.rejected("SHA-256 mismatch")
                path.unlink()
                self.rejected("cannot read")
                path.write_bytes(original)

    def test_editing_record_and_its_ledger_digest_does_not_replace_the_human_event(self):
        event = copy.deepcopy(self.event)
        event["provenance"]["answer"] = "The assistant says approved."
        self.write_json(checker.EVENT_PATH, event)
        self.ledger["ratification"]["sha256"] = self.digest(checker.EVENT_PATH)
        self.write_json(checker.LEDGER_PATH, self.ledger)
        self.rejected("SHA-256 mismatch")

    def test_event_schema_and_appointment_do_not_accept_implicit_values(self):
        for field, value in (("version", True), ("edition", 2026), ("effective_date", "2026-10-05"),
                             ("effective_timezone", "UTC"), ("unknown", "field"),
                             ("guardian_appointment", {"office": "Constitution Guardian Office",
                                                       "holder": "AI", "form": "human proxy"})):
            with self.subTest(field=field):
                event = copy.deepcopy(self.event)
                event[field] = value
                with self.assertRaises(PacketError):
                    checker.validate_event(event)
        event = copy.deepcopy(self.event)
        del event["adopter"]
        with self.assertRaises(PacketError):
            checker.validate_event(event)

    def test_adoption_schema_requires_exact_scope_identifiers_and_appointment(self):
        for field, value in (("version", True), ("edition", 2026), ("adopted_on", "2026-10-05"),
                             ("timezone", "UTC"), ("status", "discharged"), ("unknown", "field"),
                             ("interpretation_ids", ["QS-2026-01", "PR-2026-01", "PR-2026-01"]),
                             ("interpretation_ids", list(checker.INTERPRETATIONS)[:2]),
                             ("interpretation_ids", list(checker.INTERPRETATIONS) + ["AI-2026-01"]),
                             ("reviewed_packet", {"approved": True})):
            with self.subTest(field=field, value=value):
                adoption = copy.deepcopy(self.adoption)
                adoption[field] = value
                with self.assertRaises(PacketError):
                    checker.validate_adoption(adoption)
        for field, value in (("name", "Assistant"), ("capacity", "acting guardian"),
                             ("appointment_record", {"path": checker.EVENT_PATH, "sha256": "0" * 64})):
            with self.subTest(guardian_field=field):
                adoption = copy.deepcopy(self.adoption)
                adoption["guardian"][field] = value
                with self.assertRaises(PacketError):
                    checker.validate_adoption(adoption)

    def test_edited_adoption_with_rebound_ledger_cannot_replace_human_event(self):
        adoption = copy.deepcopy(self.adoption)
        adoption["provenance"]["answer"] = "The assistant adopted the interpretations."
        self.write_json(checker.ADOPTION_PATH, adoption)
        for row in self.ledger["binding_interpretations"]:
            row["adoption"]["sha256"] = self.digest(checker.ADOPTION_PATH)
        self.write_json(checker.LEDGER_PATH, self.ledger)
        self.rejected("SHA-256 mismatch")

    def test_edited_snapshot_with_rebound_adoption_and_ledger_cannot_replace_reviewed_text(self):
        path = self.root / checker.REVIEWED_PATH
        path.write_bytes(path.read_bytes() + b"\nThe obligations are optional.\n")
        self.adoption["reviewed_packet"]["sha256"] = self.digest(checker.REVIEWED_PATH)
        self.write_json(checker.ADOPTION_PATH, self.adoption)
        for row in self.ledger["binding_interpretations"]:
            row["reviewed_text"]["sha256"] = self.digest(checker.REVIEWED_PATH)
            row["adoption"]["sha256"] = self.digest(checker.ADOPTION_PATH)
        self.write_json(checker.LEDGER_PATH, self.ledger)
        self.rejected("SHA-256 mismatch")

    def test_binding_and_pending_rows_cannot_be_removed_duplicated_or_invented(self):
        for field, id_field in (("binding_interpretations", "id"), ("pending_obligations", "interpretation")):
            missing = copy.deepcopy(self.ledger[field][:-1])
            duplicate = copy.deepcopy(self.ledger[field])
            duplicate[-1] = copy.deepcopy(duplicate[0])
            invented = copy.deepcopy(self.ledger[field])
            invented[-1][id_field] = "AI-2026-01"
            for rows in (missing, duplicate, invented, False, {}):
                with self.subTest(field=field, rows=rows):
                    ledger = copy.deepcopy(self.ledger)
                    ledger[field] = rows
                    self.write_json(checker.LEDGER_PATH, ledger)
                    self.rejected("guarantee ledger")

    def test_bindings_and_pending_obligations_cannot_be_weakened(self):
        for field, edits in (
            ("binding_interpretations", (("jurisdiction", "RS"), ("section", "Unreviewed scope"),
                                        ("adoption", {"path": checker.ADOPTION_PATH, "sha256": "0" * 64}),
                                        ("reviewed_text", {"path": "docs/src/design/initial-interpretations.md",
                                                           "sha256": checker.REVIEWED_SHA256}))),
            ("pending_obligations", (("formalization_status", "complete"), ("proof_status", "discharged"),
                                    ("evidence_bindings", [{"theorem": "Unadmitted.sound"}]),
                                    ("evidence_bindings", False))),
        ):
            for key, value in edits:
                with self.subTest(field=field, key=key):
                    ledger = copy.deepcopy(self.ledger)
                    ledger[field][0][key] = value
                    self.write_json(checker.LEDGER_PATH, ledger)
                    self.rejected("guarantee ledger")

    def test_reviewed_sections_are_exact_and_unique(self):
        data = (self.root / checker.REVIEWED_PATH).read_bytes()
        section = next(iter(checker.INTERPRETATIONS.values()))[1].encode()
        for changed in (data.replace(b"## " + section, b"## Different scope"),
                        data + b"\n## " + section + b"\n", b"\xff"):
            with self.subTest(changed=changed[-100:]):
                with self.assertRaises(PacketError):
                    checker.validate_reviewed_sections(changed)

    def test_stale_or_indirect_ledger_binding_rejects(self):
        for binding in ({"path": checker.EVENT_PATH, "sha256": "0" * 64},
                        {"path": "../ratification.json", "sha256": checker.EVENT_SHA256},
                        {"path": checker.EVENT_PATH, "sha256": checker.EVENT_SHA256, "approved": True}):
            with self.subTest(binding=binding):
                ledger = copy.deepcopy(self.ledger)
                ledger["ratification"] = binding
                self.write_json(checker.LEDGER_PATH, ledger)
                self.rejected("ratification")

    def test_active_schema_cannot_admit_fabricated_guarantees_or_interpretations(self):
        for field, value in (("version", True), ("version", 4), ("edition", "2027"),
                             ("status", "release-ready"), ("scope", "No obligations apply."),
                             ("discharged_guarantees", [{"theorem": "Soundness", "proved": True}]),
                             ("pending_obligations", [{"name": "QS"}]),
                             ("binding_interpretations", ["AI-approved ruling"]),
                             ("discharged_guarantees", False), ("unknown", [])):
            with self.subTest(field=field, value=value):
                ledger = copy.deepcopy(self.ledger)
                ledger[field] = value
                self.write_json(checker.LEDGER_PATH, ledger)
                self.rejected("ledger")

    def test_duplicate_fields_reject_in_event_and_ledger(self):
        path = self.root / checker.EVENT_PATH
        path.write_text(json.dumps(self.event).replace('"edition": "2026"',
                                                      '"edition": "2026", "edition": "2026"'))
        # Emulate an edited local digest too; strict parsing still rejects.
        with patch.object(checker, "EVENT_SHA256", self.digest(checker.EVENT_PATH)):
            self.rejected("duplicate JSON field")
        shutil.copyfile(ROOT / checker.EVENT_PATH, path)
        self.write_json(checker.LEDGER_PATH, self.ledger)
        path = self.root / checker.LEDGER_PATH
        path.write_text(path.read_text().replace('"version": 3', '"version": 3, "version": 3'))
        self.rejected("duplicate JSON field")

    def test_duplicate_fields_reject_in_adoption_even_with_edited_pin(self):
        path = self.root / checker.ADOPTION_PATH
        path.write_text(json.dumps(self.adoption).replace('"status": "binding-pending-discharge"',
                        '"status": "binding-pending-discharge", "status": "binding-pending-discharge"'))
        with patch.object(checker, "ADOPTION_SHA256", self.digest(checker.ADOPTION_PATH)):
            self.rejected("duplicate JSON field")

    def test_symlink_records_and_governance_directory_reject(self):
        for name in (*checker.FROZEN_PATHS, checker.LEDGER_PATH):
            with self.subTest(name=name):
                path = self.root / name
                original = path.read_bytes()
                other = self.root / "other-record"
                other.write_bytes(original)
                path.unlink()
                path.symlink_to(other)
                self.rejected("cannot read")
                path.unlink()
                path.write_bytes(original)
        governance = self.root / "governance"
        moved = self.root / "records"
        governance.rename(moved)
        governance.symlink_to(moved, target_is_directory=True)
        self.rejected("cannot read")

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_base_allows_first_introduction_and_identical_recorded_state(self):
        self.git("init", "--quiet")
        self.git("commit", "--quiet", "--allow-empty", "-m", "Before bootstrap")
        empty_base = self.git("rev-parse", "HEAD").decode().strip()
        checker.check_constitution(self.root, base_ref=empty_base)
        recorded_base = self.commit()
        checker.check_constitution(self.root, base_ref=recorded_base)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_admitted_base_allows_later_continuity_baseline_without_re_admission(self):
        self.git("init", "--quiet")
        later = {name: (self.root / name).read_bytes() for name in checker.CONTINUITY_PATHS}
        current_bytes = (self.root / checker.CURRENT_PATH).read_bytes()
        old_current = json.loads(current_bytes)
        old_current["version"] = 1
        old_current.pop("continuity", None)
        self.write_json(checker.CURRENT_PATH, old_current)
        old_ledger = copy.deepcopy(self.ledger)
        old_ledger["current_evidence"]["sha256"] = self.digest(checker.CURRENT_PATH)
        self.write_json(checker.LEDGER_PATH, old_ledger)
        for name in later:
            (self.root / name).unlink()
        base = self.commit()
        for name, data in later.items():
            (self.root / name).write_bytes(data)
        (self.root / checker.CURRENT_PATH).write_bytes(current_bytes)
        self.write_json(checker.LEDGER_PATH, self.ledger)
        checker.check_constitution(self.root, base_ref=base)
        self.assertEqual((self.root / checker.ADMISSION_PATH).read_bytes(),
                         (ROOT / checker.ADMISSION_PATH).read_bytes())

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_existing_continuity_anchor_cannot_reintroduce_missing_generation_evidence(self):
        self.git("init", "--quiet")
        name = f"{checker.CONTINUITY_ROOT}/historical-build.stdout.txt"
        original = (self.root / name).read_bytes()
        (self.root / name).unlink()
        base = self.commit()
        (self.root / name).write_bytes(original)
        self.rejected("recorded stage is missing.*historical-build.stdout", base_ref=base)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_continuity_preexisting_file_is_protected_even_before_baseline_anchor(self):
        self.git("init", "--quiet")
        name = f"{checker.CONTINUITY_ROOT}/Extract.lean"
        later = {path: (self.root / path).read_bytes() for path in checker.CONTINUITY_PATHS if path != name}
        for path in later:
            (self.root / path).unlink()
        base = self.commit()
        for path, data in later.items():
            (self.root / path).write_bytes(data)
        # Editing the proposed extractor and all its editable local hashes
        # cannot erase the already recorded source selected by the trusted base.
        path = self.root / name
        path.write_bytes(path.read_bytes() + b"\n-- replaced extractor\n")
        self.rejected("protected artifact changed.*Extract.lean", base_ref=base)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_ratified_v1_base_allows_initial_interpretation_adoption_without_later_files(self):
        self.git("init", "--quiet")
        later = {name: (self.root / name).read_bytes() for name in (*checker.INTERPRETATION_PATHS, *checker.GUARANTEE_PATHS, *checker.CONTINUITY_PATHS)}
        for name in later:
            (self.root / name).unlink()
        (self.root / checker.LEDGER_PATH).write_bytes(self.bootstrap_bytes)
        base = self.commit()
        for name, data in later.items():
            (self.root / name).write_bytes(data)
        self.write_json(checker.LEDGER_PATH, self.ledger)
        checker.check_constitution(self.root, base_ref=base)
        self.rejected("three broader binding interpretations remain pending", base_ref=base, require_release_ready=True)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_v1_transition_preserves_exact_bootstrap_bytes(self):
        self.git("init", "--quiet")
        later = {name: (self.root / name).read_bytes() for name in (*checker.INTERPRETATION_PATHS, *checker.GUARANTEE_PATHS, *checker.CONTINUITY_PATHS)}
        for name in later:
            (self.root / name).unlink()
        (self.root / checker.LEDGER_PATH).write_bytes(self.bootstrap_bytes + b"\n")
        base = self.commit()
        for name, data in later.items():
            (self.root / name).write_bytes(data)
        self.write_json(checker.LEDGER_PATH, self.ledger)
        self.rejected("archived bootstrap must preserve", base_ref=base)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_active_v2_base_cannot_lose_or_waive_adopted_obligations(self):
        self.git("init", "--quiet")
        base = self.commit()
        self.write_json(checker.LEDGER_PATH, self.bootstrap)
        self.rejected("cannot roll back to pending or bootstrap", base_ref=base)
        for field in ("binding_interpretations", "pending_obligations"):
            with self.subTest(field=field):
                ledger = copy.deepcopy(self.ledger)
                ledger[field] = []
                self.write_json(checker.LEDGER_PATH, ledger)
                self.rejected("retain all three adopted obligations", base_ref=base)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_previously_populated_v1_ledger_cannot_be_discarded_during_upgrade(self):
        self.git("init", "--quiet")
        later = {name: (self.root / name).read_bytes() for name in (*checker.INTERPRETATION_PATHS, *checker.GUARANTEE_PATHS, *checker.CONTINUITY_PATHS)}
        for field in checker.LEDGER_LISTS:
            with self.subTest(field=field):
                for name in later:
                    (self.root / name).unlink()
                old = copy.deepcopy(self.bootstrap)
                old[field] = [{"id": "previously-recorded-obligation"}]
                self.write_json(checker.LEDGER_PATH, old)
                base = self.commit()
                for name, data in later.items():
                    (self.root / name).write_bytes(data)
                self.write_json(checker.LEDGER_PATH, self.ledger)
                self.rejected("trusted-base ledger.*must be empty", base_ref=base)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_base_with_unsupported_future_ledger_cannot_be_reset_to_v2(self):
        self.git("init", "--quiet")
        ledger = copy.deepcopy(self.ledger)
        ledger["version"] = 4
        ledger["discharged_guarantees"] = [{"interpretation": "QS-2026-01", "proof": "future-admission"}]
        self.write_json(checker.LEDGER_PATH, ledger)
        base = self.commit()
        self.write_json(checker.LEDGER_PATH, self.ledger)
        self.rejected("cannot discard obligations from another schema", base_ref=base)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_base_stage_cannot_silently_reintroduce_missing_events_or_ledger(self):
        self.git("init", "--quiet")
        for name, message in ((checker.ADOPTION_PATH, "missing its interpretation adoption event"),
                              (checker.EVENT_PATH, "missing its ratification event"),
                              (checker.LEDGER_PATH, "no ledger"),
                              (checker.REVIEWED_PATH, "recorded stage is missing")):
            with self.subTest(name=name):
                data = (self.root / name).read_bytes()
                (self.root / name).unlink()
                base = self.commit()
                (self.root / name).write_bytes(data)
                self.rejected(message, base_ref=base)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_trusted_base_rejects_modification_even_if_local_event_pin_is_edited(self):
        self.git("init", "--quiet")
        base = self.commit()
        event = copy.deepcopy(self.event)
        event["provenance"]["answer"] = "Forged replacement of historical answer"
        self.write_json(checker.EVENT_PATH, event)
        replacement_sha = self.digest(checker.EVENT_PATH)
        self.ledger["ratification"]["sha256"] = replacement_sha
        self.write_json(checker.LEDGER_PATH, self.ledger)
        with patch.object(checker, "EVENT_SHA256", replacement_sha):
            # A caller must provide a trusted base: candidate-controlled hashes
            # alone cannot protect the checker and record against joint editing.
            self.rejected("protected artifact changed", base_ref=base)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_trusted_base_rejects_each_protected_artifact_change_or_removal(self):
        self.git("init", "--quiet")
        base = self.commit()
        for name in checker.FROZEN_PATHS:
            with self.subTest(name=name):
                path = self.root / name
                original = path.read_bytes()
                path.write_bytes(original + b" ")
                self.rejected("protected artifact changed", base_ref=base)
                path.unlink()
                self.rejected("cannot read", base_ref=base)
                path.write_bytes(original)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_previously_discharged_v2_ledger_cannot_be_rolled_back_to_pending(self):
        self.git("init", "--quiet")
        ledger = copy.deepcopy(self.pending)
        ledger["discharged_guarantees"] = [{"id": "previously-recorded-guarantee"}]
        self.write_json(checker.LEDGER_PATH, ledger)
        base = self.commit()
        self.write_json(checker.LEDGER_PATH, self.ledger)
        self.rejected("trusted-base ledger.*must be empty", base_ref=base)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_missing_base_records_are_only_allowed_for_first_introduction(self):
        self.git("init", "--quiet")
        path = self.root / GOVERNANCE_SNAPSHOT
        original = path.read_bytes()
        path.unlink()
        base = self.commit()
        path.write_bytes(original)
        self.rejected("recorded stage is missing", base_ref=base)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_unknown_option_like_and_shell_text_base_refs_fail_without_execution(self):
        self.git("init", "--quiet")
        self.commit()
        for ref in ("unknown-ref", "--help", "HEAD\nHEAD", "$(touch SHOULD_NOT_EXIST)", ";touch SHOULD_NOT_EXIST"):
            with self.subTest(ref=ref):
                self.rejected(base_ref=ref)
                self.assertFalse((self.root / "SHOULD_NOT_EXIST").exists())

    def test_admission_schema_requires_actual_record_and_exact_two_scopes(self):
        for field, value in (("version", True), ("status", "all-guarantees-discharged"),
                             ("guarantee_ids", list(checker.GUARANTEE_IDS)[:1]),
                             ("guarantee_ids", [checker.GUARANTEE_IDS[0]] * 2),
                             ("reviewed_proposal", {"path": checker.PROPOSAL_PATH, "sha256": "0" * 64}),
                             ("previous_ledger", {"path": checker.PENDING_PATH, "sha256": "0" * 64})):
            with self.subTest(field=field, value=value):
                event = copy.deepcopy(self.admission)
                event[field] = value
                with self.assertRaises(PacketError):
                    checker.validate_admission(event)

    def test_editing_admission_and_ledger_hash_does_not_create_human_authority(self):
        event = copy.deepcopy(self.admission)
        event["provenance"]["answer"] = "Assistant discharges all QS duties."
        self.write_json(checker.ADMISSION_PATH, event)
        for entry in self.ledger["discharged_guarantees"]:
            entry["admission"]["sha256"] = self.digest(checker.ADMISSION_PATH)
        self.write_json(checker.LEDGER_PATH, self.ledger)
        self.rejected("SHA-256 mismatch")

    def test_scoped_discharge_cannot_delete_narrow_duplicate_or_invent_guarantees(self):
        for action in ("delete", "duplicate", "invent", "change-reference", "change-scope", "broader-discharge"):
            with self.subTest(action=action):
                ledger = copy.deepcopy(self.ledger)
                rows = ledger["discharged_guarantees"]
                if action == "delete":
                    rows.pop()
                elif action == "duplicate":
                    rows[1] = copy.deepcopy(rows[0])
                elif action == "invent":
                    rows[0]["id"] = "QS-ALL-2026-01"
                elif action == "change-reference":
                    rows[0]["reviewed_proposal"]["sha256"] = "0" * 64
                elif action == "change-scope":
                    rows[0]["proposal_entry"] = checker.GUARANTEE_IDS[1]
                else:
                    ledger["pending_obligations"][0]["proof_status"] = "discharged"
                self.write_json(checker.LEDGER_PATH, ledger)
                self.rejected("guarantee ledger")

    def test_current_evidence_digest_is_live_binding_not_authority(self):
        ledger = copy.deepcopy(self.ledger)
        ledger["current_evidence"]["sha256"] = "0" * 64
        self.write_json(checker.LEDGER_PATH, ledger)
        self.rejected("SHA-256 mismatch")
        current = json.loads((self.root / checker.CURRENT_PATH).read_bytes())
        current["reviewed_proposal"]["sha256"] = "0" * 64
        self.write_json(checker.CURRENT_PATH, current)
        ledger["current_evidence"]["sha256"] = self.digest(checker.CURRENT_PATH)
        self.write_json(checker.LEDGER_PATH, ledger)
        self.rejected("current guarantee evidence")

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_v2_pending_base_allows_first_scoped_admission_and_preserves_history(self):
        self.git("init", "--quiet")
        later = {name: (self.root / name).read_bytes() for name in checker.GUARANTEE_PATHS}
        for name in later:
            (self.root / name).unlink()
        (self.root / checker.LEDGER_PATH).write_bytes(self.pending_bytes)
        base = self.commit()
        for name, data in later.items():
            (self.root / name).write_bytes(data)
        self.write_json(checker.LEDGER_PATH, self.ledger)
        checker.check_constitution(self.root, base_ref=base)
        self.rejected("three broader binding interpretations remain pending", base_ref=base, require_release_ready=True)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_admitted_base_cannot_roll_back_to_pending_or_drop_scoped_entries(self):
        self.git("init", "--quiet")
        base = self.commit()
        self.write_json(checker.LEDGER_PATH, self.pending)
        self.rejected("cannot roll back", base_ref=base)
        ledger = copy.deepcopy(self.ledger)
        ledger["discharged_guarantees"] = []
        self.write_json(checker.LEDGER_PATH, ledger)
        self.rejected("both admitted scoped guarantees must be retained", base_ref=base)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_base_protects_meaning_but_allows_updated_current_evidence_identity(self):
        self.git("init", "--quiet")
        base = self.commit()
        path = self.root / checker.CURRENT_PATH
        path.write_bytes(path.read_bytes() + b"\n")
        ledger = copy.deepcopy(self.ledger)
        ledger["current_evidence"]["sha256"] = self.digest(checker.CURRENT_PATH)
        self.write_json(checker.LEDGER_PATH, ledger)
        checker.check_constitution(self.root, base_ref=base)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_v2_to_v3_upgrade_requires_faithful_pending_ledger_archive(self):
        self.git("init", "--quiet")
        later = {name: (self.root / name).read_bytes() for name in checker.GUARANTEE_PATHS}
        for name in later:
            (self.root / name).unlink()
        (self.root / checker.LEDGER_PATH).write_bytes(self.pending_bytes + b"\n")
        base = self.commit()
        for name, data in later.items():
            (self.root / name).write_bytes(data)
        self.write_json(checker.LEDGER_PATH, self.ledger)
        self.rejected("archived pending ledger must preserve", base_ref=base)


if __name__ == "__main__":
    unittest.main()
