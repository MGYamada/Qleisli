"""Recorded identities, pending obligations and trusted-base regression checks.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

import copy
from contextlib import nullcontext
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
        self.ledger["current_bindings"][0]["evidence"]["sha256"] = self.digest(checker.CURRENT_PATH)
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
        # Hosted environment variables are not authority for these local fixture
        # checks; release delegation must require explicitly supplied context.
        environment = patch.dict(os.environ, {}, clear=True) if kwargs.get("require_release_ready") else nullcontext()
        with environment, self.assertRaisesRegex(PacketError, phrase or ".+"):
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
        self.rejected("caller-selected trusted base", require_release_ready=True)
        script = Path(__file__).with_name("check_constitution.py")
        result = subprocess.run([sys.executable, str(script), "--root", str(self.root)],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("two scoped guarantee admissions verified", result.stdout)
        self.assertIn("not independently established", result.stdout)
        self.assertIn("Three broader obligations and one exactness supplement retain pending proof/enforcement duties", result.stdout)
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
        for field, value in (("version", True), ("version", 6), ("edition", "2027"),
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
        path.write_text(path.read_text().replace('"version": 5', '"version": 5, "version": 5'))
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
        later = {name: (self.root / name).read_bytes() for name in (*checker.CONTINUITY_PATHS, *checker.LEDGER_HISTORY_PATHS, *checker.SUPPLEMENT_PATHS)}
        current_bytes = (self.root / checker.CURRENT_PATH).read_bytes()
        old_current = json.loads(current_bytes)
        old_current["version"] = 1
        old_current.pop("continuity", None)
        self.write_json(checker.CURRENT_PATH, old_current)
        old_ledger = json.loads((self.root / checker.ledger_policy.V3_PATH).read_bytes())
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
        later = {name: (self.root / name).read_bytes() for name in (*checker.INTERPRETATION_PATHS, *checker.GUARANTEE_PATHS, *checker.CONTINUITY_PATHS, *checker.LEDGER_HISTORY_PATHS, *checker.SUPPLEMENT_PATHS)}
        for name in later:
            (self.root / name).unlink()
        (self.root / checker.LEDGER_PATH).write_bytes(self.bootstrap_bytes)
        base = self.commit()
        for name, data in later.items():
            (self.root / name).write_bytes(data)
        self.write_json(checker.LEDGER_PATH, self.ledger)
        checker.check_constitution(self.root, base_ref=base)
        self.rejected("trusted same-run hosted context", base_ref=base, require_release_ready=True)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_v1_transition_preserves_exact_bootstrap_bytes(self):
        self.git("init", "--quiet")
        later = {name: (self.root / name).read_bytes() for name in (*checker.INTERPRETATION_PATHS, *checker.GUARANTEE_PATHS, *checker.CONTINUITY_PATHS, *checker.LEDGER_HISTORY_PATHS, *checker.SUPPLEMENT_PATHS)}
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
        later = {name: (self.root / name).read_bytes() for name in (*checker.INTERPRETATION_PATHS, *checker.GUARANTEE_PATHS, *checker.CONTINUITY_PATHS, *checker.LEDGER_HISTORY_PATHS, *checker.SUPPLEMENT_PATHS)}
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
        ledger["version"] = 6
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
        ledger["current_bindings"][0]["evidence"]["sha256"] = "0" * 64
        self.write_json(checker.LEDGER_PATH, ledger)
        self.rejected("SHA-256 mismatch")
        current = json.loads((self.root / checker.CURRENT_PATH).read_bytes())
        current["reviewed_proposal"]["sha256"] = "0" * 64
        self.write_json(checker.CURRENT_PATH, current)
        ledger["current_bindings"][0]["evidence"]["sha256"] = self.digest(checker.CURRENT_PATH)
        self.write_json(checker.LEDGER_PATH, ledger)
        self.rejected("current guarantee evidence")

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_v2_pending_base_allows_first_scoped_admission_and_preserves_history(self):
        self.git("init", "--quiet")
        later = {name: (self.root / name).read_bytes() for name in (*checker.GUARANTEE_PATHS, *checker.SUPPLEMENT_PATHS)}
        for name in later:
            (self.root / name).unlink()
        (self.root / checker.LEDGER_PATH).write_bytes(self.pending_bytes)
        base = self.commit()
        for name, data in later.items():
            (self.root / name).write_bytes(data)
        self.write_json(checker.LEDGER_PATH, self.ledger)
        checker.check_constitution(self.root, base_ref=base)
        self.rejected("trusted same-run hosted context", base_ref=base, require_release_ready=True)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_admitted_base_cannot_roll_back_to_pending_or_drop_scoped_entries(self):
        self.git("init", "--quiet")
        base = self.commit()
        self.write_json(checker.LEDGER_PATH, self.pending)
        self.rejected("cannot roll back", base_ref=base)
        ledger = copy.deepcopy(self.ledger)
        ledger["discharged_guarantees"] = []
        self.write_json(checker.LEDGER_PATH, ledger)
        self.rejected("admitted scoped guarantees must be retained", base_ref=base)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_base_protects_meaning_but_allows_updated_current_evidence_identity(self):
        self.git("init", "--quiet")
        base = self.commit()
        path = self.root / checker.CURRENT_PATH
        path.write_bytes(path.read_bytes() + b"\n")
        ledger = copy.deepcopy(self.ledger)
        ledger["current_bindings"][0]["evidence"]["sha256"] = self.digest(checker.CURRENT_PATH)
        self.write_json(checker.LEDGER_PATH, ledger)
        checker.check_constitution(self.root, base_ref=base)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_v2_to_v3_upgrade_requires_faithful_pending_ledger_archive(self):
        self.git("init", "--quiet")
        later = {name: (self.root / name).read_bytes() for name in (*checker.GUARANTEE_PATHS, *checker.SUPPLEMENT_PATHS)}
        for name in later:
            (self.root / name).unlink()
        (self.root / checker.LEDGER_PATH).write_bytes(self.pending_bytes + b"\n")
        base = self.commit()
        for name, data in later.items():
            (self.root / name).write_bytes(data)
        self.write_json(checker.LEDGER_PATH, self.ledger)
        self.rejected("archived pending ledger must preserve", base_ref=base)

    def synthetic_append(self):
        """Test-only registration, never a live human admission or proof claim."""
        policy = checker.ledger_policy
        identifier = "QS-SYNTHETIC-TEST-ONLY"
        names = ["tests/synthetic-admission.json", "tests/synthetic-proposal.json", "tests/synthetic-evidence.json"]
        for name in names:
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            self.write_json(name, {"status": "synthetic-test-only", "purpose": name})
        entry = dict(id=identifier, jurisdiction="QS", interpretation="QS-2026-01", proposal_entry=identifier,
                     admission=dict(path=names[0], sha256=self.digest(names[0])),
                     reviewed_proposal=dict(path=names[1], sha256=self.digest(names[1])))
        registrations = (*checker.admission_registrations(), policy.AdmissionRegistration((entry,)))
        calls = []

        def synthetic_verifier(root, *, verify_lean):
            calls.append(verify_lean)
            data_bytes = (root / names[2]).read_bytes()
            data = json.loads(data_bytes)
            if data != {"status": "synthetic-test-only", "purpose": names[2]}:
                raise PacketError("synthetic verifier rejected evidence")
            return {"mode": "synthetic-test-only", "admitted_by_this_check": 0,
                    "current_evidence_sha256": hashlib.sha256(data_bytes).hexdigest()}

        profiles = (*checker.verifier_profiles(), policy.VerifierProfile(
            "synthetic-test-only", ((identifier, policy.identity_sha256(entry)),), names[2], synthetic_verifier))
        ledger = copy.deepcopy(self.ledger)
        ledger["discharged_guarantees"].append({**entry, "identity_sha256": policy.identity_sha256(entry)})
        ledger["current_bindings"].append(dict(guarantee_ids=[identifier], verifier_profile="synthetic-test-only",
                                                evidence=dict(path=names[2], sha256=self.digest(names[2]))))
        return ledger, registrations, profiles, calls

    def test_canonical_identity_ignores_json_order_but_retains_all_typed_meaning_fields(self):
        policy = checker.ledger_policy
        entry = checker.initial_entries()[0]
        reordered = dict(reversed(list(entry.items())))
        reordered["admission"] = dict(reversed(list(entry["admission"].items())))
        self.assertEqual(policy.identity_sha256(entry), policy.identity_sha256(reordered))
        for field, value in (("id", "QS-OTHER"), ("jurisdiction", "PR"),
                             ("interpretation", "QS-OTHER"), ("proposal_entry", "QS-OTHER"),
                             ("admission", {"path": checker.ADMISSION_PATH, "sha256": "0" * 64}),
                             ("reviewed_proposal", {"path": checker.PROPOSAL_PATH, "sha256": "0" * 64})):
            with self.subTest(field=field):
                changed = copy.deepcopy(entry)
                changed[field] = value
                self.assertNotEqual(policy.identity_sha256(entry), policy.identity_sha256(changed))
        for field in policy.IDENTITY_FIELDS:
            changed = copy.deepcopy(entry)
            changed[field] = True
            with self.assertRaises(PacketError):
                policy.identity_sha256(changed)
        changed = {**entry, "current_evidence": {"approved": True}}
        with self.assertRaises(PacketError):
            policy.identity_sha256(changed)

    def test_v4_identity_reordering_is_valid_but_digest_edits_are_not(self):
        ledger = copy.deepcopy(self.ledger)
        ledger["discharged_guarantees"].reverse()
        ledger["current_bindings"][0]["guarantee_ids"].reverse()
        self.write_json(checker.LEDGER_PATH, ledger)
        checker.check_constitution(self.root)
        ledger["discharged_guarantees"][0]["identity_sha256"] = "0" * 64
        self.write_json(checker.LEDGER_PATH, ledger)
        self.rejected("canonical identity")

    def test_new_guarantee_requires_separate_registered_event_and_matching_verifier(self):
        ledger, registrations, profiles, calls = self.synthetic_append()
        self.write_json(checker.LEDGER_PATH, ledger)
        self.rejected("unknown or duplicate admitted guarantee")
        self.rejected("unknown or duplicate fixed verifier", _registrations=registrations)
        # A real existing profile cannot be relabelled to prove a third property.
        changed = copy.deepcopy(ledger)
        changed["current_bindings"] = changed["current_bindings"][:1]
        changed["current_bindings"][0]["guarantee_ids"].append(ledger["discharged_guarantees"][-1]["id"])
        self.write_json(checker.LEDGER_PATH, changed)
        self.rejected("coverage differs", _registrations=registrations, _profiles=profiles)
        self.write_json(checker.LEDGER_PATH, ledger)
        result = checker.check_constitution(self.root, _registrations=registrations, _profiles=profiles)
        self.assertEqual(result["admitted_guarantees"], 3)
        self.assertEqual(calls, [False])
        # Registration is not a subset exception for the current active ledger.
        self.write_json(checker.LEDGER_PATH, self.ledger)
        self.rejected("all registered", _registrations=registrations, _profiles=profiles)

    def test_profile_covers_exact_identity_not_just_identifier(self):
        ledger, registrations, profiles, _ = self.synthetic_append()
        row = copy.deepcopy(registrations[-1].entries[0])
        row["proposal_entry"] = "QS-DIFFERENT-PROPERTY"
        registrations = (*registrations[:-1], checker.ledger_policy.AdmissionRegistration((row,)))
        ledger["discharged_guarantees"][-1] = {**row, "identity_sha256": checker.ledger_policy.identity_sha256(row)}
        self.write_json(checker.LEDGER_PATH, ledger)
        self.rejected("verifier does not cover", _registrations=registrations, _profiles=profiles)

    def test_current_bindings_reject_missing_duplicate_unknown_and_record_commands(self):
        for action in ("missing", "duplicate", "unknown", "omit-id", "fake-id", "command", "alternate-path"):
            with self.subTest(action=action):
                ledger = copy.deepcopy(self.ledger)
                rows = ledger["current_bindings"]
                if action == "missing":
                    rows.clear()
                elif action == "duplicate":
                    rows.append(copy.deepcopy(rows[0]))
                elif action == "unknown":
                    rows[0]["verifier_profile"] = "import.some.code"
                elif action == "omit-id":
                    rows[0]["guarantee_ids"].pop()
                elif action == "fake-id":
                    rows[0]["guarantee_ids"][0] = "QS-UNKNOWN"
                elif action == "command":
                    rows[0]["argv"] = ["echo", "approved"]
                else:
                    rows[0]["evidence"]["path"] = "../current-evidence.json"
                self.write_json(checker.LEDGER_PATH, ledger)
                self.rejected("guarantee ledger")

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_exact_v3_base_migrates_and_cannot_be_rolled_back_from_v4(self):
        self.git("init", "--quiet")
        historical = (self.root / checker.ledger_policy.V3_PATH).read_bytes()
        supplements = {name: (self.root / name).read_bytes() for name in checker.SUPPLEMENT_PATHS}
        for name in supplements:
            (self.root / name).unlink()
        (self.root / checker.ledger_policy.V3_PATH).unlink()
        (self.root / checker.LEDGER_PATH).write_bytes(historical)
        base = self.commit()
        (self.root / checker.ledger_policy.V3_PATH).write_bytes(historical)
        for name, data in supplements.items():
            (self.root / name).write_bytes(data)
        self.write_json(checker.LEDGER_PATH, self.ledger)
        checker.check_constitution(self.root, base_ref=base)
        v4_base = self.commit()
        (self.root / checker.LEDGER_PATH).write_bytes(historical)
        self.rejected("active ledger must be v5", base_ref=v4_base)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_v3_unknown_prior_guarantee_cannot_be_ignored_by_archiving_familiar_snapshot(self):
        self.git("init", "--quiet")
        historical = json.loads((self.root / checker.ledger_policy.V3_PATH).read_bytes())
        historical["discharged_guarantees"].append({"id": "QS-LOST-PRIOR-GUARANTEE"})
        self.write_json(checker.LEDGER_PATH, historical)
        base = self.commit()
        self.write_json(checker.LEDGER_PATH, self.ledger)
        self.rejected("trusted-base ledger.*must be retained", base_ref=base)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_v4_base_can_append_registered_identity_but_never_delete_or_change_it(self):
        self.git("init", "--quiet")
        base = self.commit()
        ledger, registrations, profiles, _ = self.synthetic_append()
        self.write_json(checker.LEDGER_PATH, ledger)
        checker.check_constitution(self.root, base_ref=base, _registrations=registrations, _profiles=profiles)
        appended_base = self.commit()
        # Even deleting the new registration from candidate checker code cannot
        # make the prior v4 entry disappear: historical parsing fails closed.
        self.write_json(checker.LEDGER_PATH, self.ledger)
        self.rejected("trusted-base ledger.*unknown", base_ref=appended_base)
        self.rejected("all registered", base_ref=appended_base, _registrations=registrations, _profiles=profiles)
        changed = copy.deepcopy(ledger)
        changed["discharged_guarantees"][-1]["proposal_entry"] = "QS-NARROWER"
        changed["discharged_guarantees"][-1]["identity_sha256"] = checker.ledger_policy.identity_sha256(
            {key: value for key, value in changed["discharged_guarantees"][-1].items() if key != "identity_sha256"})
        self.write_json(checker.LEDGER_PATH, changed)
        self.rejected("identity changed", base_ref=appended_base, _registrations=registrations, _profiles=profiles)
        self.write_json(checker.LEDGER_PATH, ledger)
        event_path = ledger["discharged_guarantees"][-1]["admission"]["path"]
        (self.root / event_path).write_bytes(b'{"status":"replaced"}')
        self.rejected("protected admission artifact changed", base_ref=appended_base,
                      _registrations=registrations, _profiles=profiles)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_v4_trusted_base_requires_recorded_history(self):
        self.git("init", "--quiet")
        path = self.root / checker.ledger_policy.V3_PATH
        data = path.read_bytes()
        path.unlink()
        base = self.commit()
        path.write_bytes(data)
        self.rejected("missing its immutable v3 history", base_ref=base)

    def test_dispatch_rejects_concurrent_ledger_evidence_and_frozen_artifact_changes(self):
        policy = checker.ledger_policy
        original_profile = checker.verifier_profiles()[0]
        for action in ("ledger", "evidence", "both", "frozen"):
            with self.subTest(action=action):
                ledger_data = (self.root / checker.LEDGER_PATH).read_bytes()
                evidence_data = (self.root / checker.CURRENT_PATH).read_bytes()
                frozen_path = self.root / checker.CONTINUITY_BASELINE
                frozen_data = frozen_path.read_bytes()

                def racing_verifier(root, *, verify_lean):
                    self.assertTrue(verify_lean)
                    if action in {"evidence", "both"}:
                        (root / checker.CURRENT_PATH).write_bytes(evidence_data + b"\n")
                    if action in {"ledger", "both"}:
                        ledger = json.loads(ledger_data)
                        ledger["current_bindings"][0]["evidence"]["sha256"] = self.digest(checker.CURRENT_PATH)
                        self.write_json(checker.LEDGER_PATH, ledger)
                        if action == "ledger":
                            (root / checker.LEDGER_PATH).write_bytes((root / checker.LEDGER_PATH).read_bytes() + b"\n")
                    if action == "frozen":
                        frozen_path.write_bytes(frozen_data + b"\n")
                    return {"mode": "synthetic-race-test"}

                profile = policy.VerifierProfile(original_profile.name, original_profile.identities,
                                                  original_profile.evidence_path, racing_verifier)
                self.rejected("changed during", verify_lean=True, _profiles=(profile,))
                (self.root / checker.LEDGER_PATH).write_bytes(ledger_data)
                (self.root / checker.CURRENT_PATH).write_bytes(evidence_data)
                frozen_path.write_bytes(frozen_data)

    def test_dispatch_replays_each_fixed_profile_then_rechecks_current_identity(self):
        policy = checker.ledger_policy
        profile = checker.verifier_profiles()[0]
        calls = []
        def observed(root, *, verify_lean):
            calls.append(verify_lean)
            return {"mode": "synthetic-dispatch-test",
                    "current_evidence_sha256": hashlib.sha256((root / checker.CURRENT_PATH).read_bytes()).hexdigest()}
        profile = policy.VerifierProfile(profile.name, profile.identities, profile.evidence_path, observed)
        result = checker.check_constitution(self.root, verify_lean=True, _profiles=(profile,))
        self.assertEqual(calls, [True, False])
        self.assertEqual(result["mode"], "current-Lean-replay")

    def test_registered_guarantee_requires_an_adopted_interpretation_and_matching_jurisdiction(self):
        policy = checker.ledger_policy
        for field, value in (("interpretation", "QS-UNADOPTED"), ("jurisdiction", "PR")):
            with self.subTest(field=field):
                ledger, registrations, profiles, _ = self.synthetic_append()
                row = copy.deepcopy(registrations[-1].entries[0])
                row[field] = value
                registrations = (*registrations[:-1], policy.AdmissionRegistration((row,)))
                profile = profiles[-1]
                profiles = (*profiles[:-1], policy.VerifierProfile(profile.name,
                    ((row["id"], policy.identity_sha256(row)),), profile.evidence_path, profile.verify))
                ledger["discharged_guarantees"][-1] = {**row, "identity_sha256": policy.identity_sha256(row)}
                self.write_json(checker.LEDGER_PATH, ledger)
                self.rejected("retained interpretation with matching jurisdiction",
                              _registrations=registrations, _profiles=profiles)

    def test_invalid_initial_and_final_snapshot_cannot_hide_behind_valid_intermediate_reads(self):
        import check_ratification_packet as packet
        path = self.root / "CONSTITUTION.md"
        original = path.read_bytes()
        changed = original + b"\nUnapproved retained change.\n"
        path.write_bytes(changed)
        real_checked_file = packet.checked_file
        reads = []
        def timed_read(root, name, digest):
            if name != "CONSTITUTION.md":
                return real_checked_file(root, name, digest)
            # Only read timing is mocked; the real hash validation sees genuine
            # original bytes. The captured/final snapshot contains changed bytes.
            path.write_bytes(original)
            try:
                result = real_checked_file(root, name, digest)
                reads.append(name)
                return result
            finally:
                path.write_bytes(changed)
        with patch.object(checker, "checked_file", side_effect=timed_read), \
                patch.object(packet, "checked_file", side_effect=timed_read):
            self.rejected("frozen artifact snapshot: SHA-256 mismatch.*CONSTITUTION")
        self.assertEqual(len(reads), 2)
        self.assertEqual(path.read_bytes(), changed)

    def test_frozen_manifest_cannot_select_an_incomplete_snapshot_set(self):
        snapshots = {name: (self.root / name).read_bytes() for name in checker.FROZEN_PATHS}
        manifest = json.loads(snapshots[checker.FROZEN_IDENTITIES_PATH])
        del manifest["files"]["CONSTITUTION.md"]
        data = json.dumps(manifest).encode()
        snapshots[checker.FROZEN_IDENTITIES_PATH] = data
        # Even replacing the local pin does not make incomplete coverage valid.
        with self.assertRaisesRegex(PacketError, "cover every protected snapshot"):
            checker.ledger_policy.validate_frozen_snapshots(
                snapshots, checker.FROZEN_IDENTITIES_PATH, hashlib.sha256(data).hexdigest())

    def test_profile_must_validate_the_exact_ledger_bound_current_evidence_snapshot(self):
        import check_initial_guarantees as initial
        path = self.root / checker.CURRENT_PATH
        original = path.read_bytes()
        changed = json.loads(original)
        changed["validation"]["source_revision"]["sha256"] = "0" * 64
        bad = json.dumps(changed).encode()
        path.write_bytes(bad)
        ledger = copy.deepcopy(self.ledger)
        ledger["current_bindings"][0]["evidence"]["sha256"] = hashlib.sha256(bad).hexdigest()
        self.write_json(checker.LEDGER_PATH, ledger)
        real_read = initial.read_file
        reads = []
        def timed_read(root, name):
            if name != checker.CURRENT_PATH:
                return real_read(root, name)
            path.write_bytes(original)
            try:
                data = real_read(root, name)
                reads.append(hashlib.sha256(data).hexdigest())
                return data
            finally:
                path.write_bytes(bad)
        with patch.object(initial, "read_file", side_effect=timed_read):
            self.rejected("fixed verifier validated different evidence than the ledger binding")
        self.assertEqual(reads, [hashlib.sha256(original).hexdigest()])
        self.assertEqual(path.read_bytes(), bad)

    def test_dispatch_rejects_missing_or_wrong_validated_input_identity(self):
        policy = checker.ledger_policy
        original = checker.verifier_profiles()[0]
        for response in ({"mode": "claimed-success"}, {"current_evidence_sha256": "0" * 64}, None):
            with self.subTest(response=response):
                def unbound(root, *, verify_lean):
                    return response
                profile = policy.VerifierProfile(original.name, original.identities, original.evidence_path, unbound)
                self.rejected("fixed verifier validated different evidence", _profiles=(profile,))


    def historical_v4(self):
        historical = copy.deepcopy(self.ledger)
        historical["version"] = 4
        historical["scope"] = checker.ledger_policy.V4_SCOPE
        del historical["supplemental_interpretations"]
        return historical

    def test_exactness_is_separate_binding_interpretation_not_fourth_jurisdiction_or_discharge(self):
        result = checker.check_constitution(self.root)
        self.assertEqual(result, dict(admitted_guarantees=2, pending_obligations=3,
                                     supplemental_pending_obligations=1,
                                     ledger_sha256=self.digest(checker.LEDGER_PATH), mode="source-identity-only"))
        self.assertEqual(len(self.ledger["binding_interpretations"]), 3)
        self.assertEqual(self.ledger["supplemental_interpretations"], [checker.supplemental_interpretation()])
        original = json.loads((self.root / checker.ledger_policy.V3_PATH).read_bytes())
        self.assertEqual(self.ledger["binding_interpretations"], original["binding_interpretations"])
        self.assertEqual(self.ledger["pending_obligations"], original["pending_obligations"])
        checker.ledger_policy.preserve_entries(original["discharged_guarantees"],
                                               self.ledger["discharged_guarantees"], before_hashed=False)

    def test_returned_ledger_identity_binds_validated_bytes_without_a_later_reread(self):
        original = (self.root / checker.LEDGER_PATH).read_bytes()
        reread = original + b"\n"
        reads = []
        real_read = checker.read_file
        def timed_read(root, name):
            if name != checker.LEDGER_PATH:
                return real_read(root, name)
            reads.append(name)
            return original if len(reads) == 1 else reread
        # Only the constitutional checker's initial read is replaced. The real validator
        # and its final unchanged checks still inspect the genuine ledger.
        # A digest from a new return-time read would certify different bytes.
        with patch.object(checker, "read_file", side_effect=timed_read):
            result = checker.check_constitution(self.root)
        self.assertEqual(reads, [checker.LEDGER_PATH])
        self.assertEqual(result["ledger_sha256"], hashlib.sha256(original).hexdigest())
        self.assertNotEqual(result["ledger_sha256"], hashlib.sha256(reread).hexdigest())

    def test_supplement_cannot_be_missing_duplicated_weakened_or_marked_discharged(self):
        row = checker.supplemental_interpretation()
        for rows in ([], [row, row], False):
            with self.subTest(rows=rows):
                ledger = copy.deepcopy(self.ledger)
                ledger["supplemental_interpretations"] = rows
                self.write_json(checker.LEDGER_PATH, ledger)
                self.rejected("exactness supplement")
        for key, value in (("id", "EXACT-UNKNOWN"), ("jurisdictions", ["EXACT"]),
                           ("jurisdictions", ["QS", "PR"]), ("applies_to", ["QS-2026-01"]),
                           ("proof_status", "discharged"), ("formalization_status", "complete"),
                           ("evidence_bindings", [{"proof": "fake"}]), ("approved", True),
                           ("adoption", {"path": checker.EXACTNESS_ADOPTION_PATH, "sha256": "0" * 64}),
                           ("reviewed_text", {"path": "../outside.md", "sha256": checker.EXACTNESS_REVIEWED_SHA256})):
            with self.subTest(key=key, value=value):
                ledger = copy.deepcopy(self.ledger)
                ledger["supplemental_interpretations"][0][key] = value
                self.write_json(checker.LEDGER_PATH, ledger)
                self.rejected("exactness supplement")

    def test_supplement_event_schema_is_specific_and_does_not_infer_human_authority(self):
        original = json.loads((self.root / checker.EXACTNESS_ADOPTION_PATH).read_bytes())
        checker.validate_exactness_adoption(original)
        for key, value in (("version", True), ("edition", 2026), ("interpretation_ids", []),
                           ("interpretation_ids", ["QS-2026-01"]), ("jurisdictions", ["EXACT"]),
                           ("adopted_on", "2026-10-04"), ("status", "discharged"),
                           ("guardian", {"name": "AI", "capacity": "approved"}),
                           ("reviewed_packet", {"reviewed_path": checker.EXACTNESS_REVIEWED_PATH,
                                                "snapshot_path": checker.EXACTNESS_REVIEWED_PATH, "sha256": "0" * 64})):
            with self.subTest(key=key):
                event = copy.deepcopy(original)
                event[key] = value
                with self.assertRaises(PacketError):
                    checker.validate_exactness_adoption(event)
        event = copy.deepcopy(original)
        event["provenance"]["answer"] = "The assistant approves by default."
        self.write_json(checker.EXACTNESS_ADOPTION_PATH, event)
        ledger = copy.deepcopy(self.ledger)
        ledger["supplemental_interpretations"][0]["adoption"]["sha256"] = self.digest(checker.EXACTNESS_ADOPTION_PATH)
        self.write_json(checker.LEDGER_PATH, ledger)
        self.rejected("exactness supplement|SHA-256 mismatch")

    def test_exactness_duplicate_fields_reject_even_with_replaced_local_event_pin(self):
        path = self.root / checker.EXACTNESS_ADOPTION_PATH
        path.write_text(path.read_text().replace('"version": 1', '"version": 1, "version": 1'))
        with patch.object(checker, "EXACTNESS_ADOPTION_SHA256", self.digest(checker.EXACTNESS_ADOPTION_PATH)):
            ledger = copy.deepcopy(self.ledger)
            ledger["supplemental_interpretations"] = [checker.supplemental_interpretation()]
            self.write_json(checker.LEDGER_PATH, ledger)
            self.rejected("duplicate JSON field")

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_actual_v4_to_v5_transition_preserves_all_prior_entries_and_rejects_rollback(self):
        self.git("init", "--quiet")
        prior = self.historical_v4()
        saved = {name: (self.root / name).read_bytes() for name in checker.SUPPLEMENT_PATHS}
        for name in saved:
            (self.root / name).unlink()
        self.write_json(checker.LEDGER_PATH, prior)
        base = self.commit()
        for name, data in saved.items():
            (self.root / name).write_bytes(data)
        self.write_json(checker.LEDGER_PATH, self.ledger)
        checker.check_constitution(self.root, base_ref=base)
        active = self.commit()
        self.write_json(checker.LEDGER_PATH, prior)
        self.rejected("active ledger must be v5", base_ref=active)
        self.write_json(checker.LEDGER_PATH, self.ledger)
        checker.check_constitution(self.root, base_ref=active)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_supplement_stage_cannot_reintroduce_missing_event_text_or_ledger(self):
        self.git("init", "--quiet")
        for name, message in ((checker.EXACTNESS_ADOPTION_PATH, "missing its exactness adoption"),
                              (checker.EXACTNESS_REVIEWED_PATH, "recorded stage is missing"),
                              (checker.LEDGER_PATH, "no ledger")):
            with self.subTest(name=name):
                path = self.root / name
                original = path.read_bytes()
                path.unlink()
                base = self.commit()
                path.write_bytes(original)
                self.rejected(message, base_ref=base)
        self.write_json(checker.LEDGER_PATH, self.historical_v4())
        old = self.commit()
        self.write_json(checker.LEDGER_PATH, self.ledger)
        self.rejected("exactness adoption cannot retain an older ledger", base_ref=old)

    @unittest.skipUnless(shutil.which("git"), "trusted-base checks need Git")
    def test_reviewed_supplement_is_protected_before_adoption_anchor(self):
        self.git("init", "--quiet")
        event_path = self.root / checker.EXACTNESS_ADOPTION_PATH
        event = event_path.read_bytes()
        event_path.unlink()
        self.write_json(checker.LEDGER_PATH, self.historical_v4())
        base = self.commit()
        event_path.write_bytes(event)
        self.write_json(checker.LEDGER_PATH, self.ledger)
        checker.check_constitution(self.root, base_ref=base)
        path = self.root / checker.EXACTNESS_REVIEWED_PATH
        path.write_bytes(path.read_bytes() + b"\nChanged before introduction.\n")
        self.rejected("protected artifact changed", base_ref=base)

    def test_supplement_snapshots_reject_invalid_captured_bytes_and_mid_dispatch_changes(self):
        snapshots = {name: (self.root / name).read_bytes() for name in checker.SUPPLEMENT_PATHS}
        checker.validate_supplement_snapshots(snapshots)
        for name in checker.SUPPLEMENT_PATHS:
            bad = dict(snapshots)
            bad[name] += b"\nUnapproved change.\n"
            with self.subTest(name=name), self.assertRaisesRegex(PacketError, "frozen artifact snapshot: SHA-256 mismatch"):
                checker.validate_supplement_snapshots(bad)
        original = checker.verifier_profiles()[0]
        for name in checker.SUPPLEMENT_PATHS:
            path = self.root / name
            saved = path.read_bytes()
            def changed(root, *, verify_lean):
                path.write_bytes(saved + b"\nUnapproved concurrent change.\n")
                return {"current_evidence_sha256": self.ledger["current_bindings"][0]["evidence"]["sha256"]}
            profile = checker.ledger_policy.VerifierProfile(original.name, original.identities, original.evidence_path, changed)
            with self.subTest(name=name):
                self.rejected("evidence changed during verification", _profiles=(profile,))
            path.write_bytes(saved)


if __name__ == "__main__":
    unittest.main()
