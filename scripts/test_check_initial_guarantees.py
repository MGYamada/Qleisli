"""Integrity and non-admission tests for the two proposed scoped QS records.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

import copy
import gzip
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import call, patch

sys.dont_write_bytecode = True
import check_initial_guarantees as checker
from check_ratification_packet import ROOT, PacketError


def copy_evidence_fixture(destination):
    """Materialize historical bytes as test sources, never execute archived code."""
    record = json.loads((ROOT / checker.VALIDATION_PATH).read_bytes())
    proposal = json.loads((ROOT / checker.PROPOSAL_PATH).read_bytes())
    archive = checker.historical_sources(ROOT, proposal)
    names = (set(record["files"]) - {checker.REGISTRY_PATH}) | {
        checker.VALIDATION_PATH, checker.PROPOSAL_PATH, checker.ADOPTION_PATH, checker.REVIEWED_PATH,
        checker.ARCHIVE_PATH, checker.ARCHIVED_REGISTRY_PATH, checker.SEMANTIC_PATH,
        checker.BINDING_SOURCE, checker.BINDING_STDOUT, checker.BINDING_STDERR}
    continuity = checker.continuity
    baseline = json.loads((ROOT / continuity.BASELINE_PATH).read_bytes())
    names.update({continuity.BASELINE_PATH, continuity.EXTRACTOR_PATH, continuity.REVIEWED_PATH,
                  continuity.CURRENT_PATH, continuity.STDERR_PATH, *baseline["generation_evidence"]})
    for name in names:
        path = destination / name
        path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / name, path)
    for name, data in archive["sources"].items():
        path = destination / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    shutil.copyfile(ROOT / checker.ARCHIVED_REGISTRY_PATH, destination / checker.REGISTRY_PATH)
    current = json.loads((ROOT / checker.CURRENT_PATH).read_bytes())
    current["validation"] = copy.deepcopy(record)
    current["validation"]["status"] = "checked-current-evidence"
    current["continuity"]["source_revision_sha256"] = record["source_revision"]["sha256"]
    (destination / checker.CURRENT_PATH).write_text(json.dumps(current), encoding="utf-8")
    return record, proposal


@unittest.skipUnless(os.open in os.supports_dir_fd and hasattr(os, "O_NOFOLLOW"),
                     "descriptor-relative no-follow file reads are required")
class InitialGuaranteeEvidence(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name).resolve()
        self.record, self.proposal = copy_evidence_fixture(self.root)

    def write_json(self, name, value):
        (self.root / name).write_text(json.dumps(value, ensure_ascii=False), encoding="utf-8")

    def rejected(self, phrase=".+", **kwargs):
        with self.assertRaisesRegex((PacketError, checker.registry.RegistryError), phrase):
            checker.check(self.root, **kwargs)

    def write_record(self, record):
        current = json.loads((self.root / checker.CURRENT_PATH).read_bytes())
        current["validation"] = copy.deepcopy(record)
        current["validation"]["status"] = "checked-current-evidence"
        self.write_json(checker.CURRENT_PATH, current)

    def refresh_test_current_identity(self, *, continuity_replayed=False):
        """Synthesize updated records for identity-only tests, not real proof evidence."""
        revision = checker.registry.source_revision(self.root)
        manifest = json.loads((self.root / checker.REGISTRY_PATH).read_bytes())
        manifest["source_revision"] = revision
        self.write_json(checker.REGISTRY_PATH, manifest)
        manifest_sha = checker.digest((self.root / checker.REGISTRY_PATH).read_bytes())
        audit = json.loads((self.root / checker.AUDIT_PATH).read_bytes())
        audit["source_revision"] = revision["sha256"]
        audit["manifest_sha256"] = manifest_sha
        self.write_json(checker.CURRENT_AUDIT_PATH, audit)
        record = copy.deepcopy(self.record)
        record["source_revision"] = revision
        record["files"][checker.REGISTRY_PATH] = manifest_sha
        record["build_and_audit_record"] = checker.CURRENT_AUDIT_PATH
        del record["files"][checker.AUDIT_PATH]
        record["files"][checker.CURRENT_AUDIT_PATH] = checker.digest((self.root / checker.CURRENT_AUDIT_PATH).read_bytes())
        self.write_record(record)
        if continuity_replayed:
            # Synthetic metadata for unit tests only; real evidence is obtained
            # by the fixed extractor in the built/audited current environment.
            current = json.loads((self.root / checker.CURRENT_PATH).read_bytes())
            current["continuity"]["source_revision_sha256"] = revision["sha256"]
            self.write_json(checker.CURRENT_PATH, current)
        return revision

    def test_default_checks_identity_without_lean_or_a_local_native_binary(self):
        self.assertFalse((self.root / self.record["observed_native_build"]["path"]).exists())
        with patch.object(checker.subprocess, "run", side_effect=AssertionError("default must not execute commands")):
            result = checker.check(self.root)
        self.assertEqual(result["mode"], "source-identity-only")
        self.assertEqual(result["scoped_guarantees"], 2)
        self.assertEqual(result["admitted_by_this_check"], 0)
        self.rejected("use check_constitution.py", require_adopted=True)

    def test_cli_reports_limits_and_requires_human_admission(self):
        script = Path(__file__).with_name("check_initial_guarantees.py")
        result = subprocess.run([sys.executable, str(script), "--root", str(self.root)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("source-identity-only", result.stdout)
        self.assertIn("does not itself establish human authentication, adequacy, guarantee admission", result.stdout)
        result = subprocess.run([sys.executable, str(script), "--root", str(self.root), "--require-adopted"],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn("historical proposal checker", result.stderr)

    def test_false_human_adoption_discharged_status_and_unknown_fields_reject(self):
        for field, value in (("human_adoption", True), ("human_adoption", {"approved": True}),
                             ("human_adoption", "human approved"), ("status", "discharged"),
                             ("version", True), ("edition", 2026), ("discharged_guarantees", [])):
            with self.subTest(field=field, value=value):
                proposal = copy.deepcopy(self.proposal)
                proposal[field] = value
                self.write_json(checker.PROPOSAL_PATH, proposal)
                self.rejected()

    def test_guarantee_cannot_be_omitted_duplicated_or_promoted(self):
        for action in ("omit", "duplicate", "unknown", "promote", "discharged", "new-field"):
            with self.subTest(action=action):
                proposal = copy.deepcopy(self.proposal)
                rows = proposal["guarantees"]
                if action == "omit":
                    rows.pop()
                elif action == "duplicate":
                    rows[1] = copy.deepcopy(rows[0])
                elif action == "unknown":
                    rows[0]["id"] = "QS-ALL-2026-01"
                elif action in {"promote", "discharged"}:
                    rows[0]["status"] = "adopted" if action == "promote" else "discharged"
                else:
                    rows[0]["proof_status"] = "proved"
                self.write_json(checker.PROPOSAL_PATH, proposal)
                self.rejected()

    def test_native_predicate_declaration_and_statement_cannot_be_substituted(self):
        for action in ("native", "witness", "theorem", "property", "property-path", "statement", "proof-chain", "dependency"):
            with self.subTest(action=action):
                proposal = copy.deepcopy(self.proposal)
                row = proposal["guarantees"][0]
                if action == "native":
                    proposal["native_boundary"]["entrypoint"]["declaration"] = "QleisliKernel.Protocol.NativeContract.check"
                elif action == "witness":
                    proposal["native_boundary"]["acceptance_witness"]["declaration"] = "QleisliKernel.Qirf.Artifact"
                elif action in {"theorem", "property"}:
                    row[action] = copy.deepcopy(proposal["guarantees"][1][action])
                elif action == "property-path":
                    row["property"]["path"] = "lean/Qleisli/NativeValidity.lean"
                elif action == "statement":
                    row["formal_statement"] = row["formal_statement"].replace("QleisliKernel.Protocol.Validity.check", "Rust.check")
                else:
                    row["proof_chain" if action == "proof-chain" else "semantic_dependencies"].pop()
                self.write_json(checker.PROPOSAL_PATH, proposal)
                self.rejected()

    def test_broader_obligations_and_scope_exclusions_cannot_be_erased(self):
        for field in ("pending_obligations", "excluded_claims"):
            with self.subTest(field=field):
                proposal = copy.deepcopy(self.proposal)
                proposal["assumptions_and_limits"][field] = []
                self.write_json(checker.PROPOSAL_PATH, proposal)
                self.rejected()

    def test_stale_parent_interpretation_and_source_binding_reject(self):
        for action in ("adoption", "reviewed_text", "source"):
            with self.subTest(action=action):
                proposal = copy.deepcopy(self.proposal)
                (proposal["source_binding"] if action == "source" else proposal["interpretation"][action])["sha256"] = "0" * 64
                self.write_json(checker.PROPOSAL_PATH, proposal)
                self.rejected()

    def test_current_source_changes_and_omissions_reject(self):
        for name in (checker.NATIVE_SOURCE, "lean/Qleisli/NativeValidity.lean",
                     "lean-kernel/QleisliKernel/Semantics/Ownership.lean", "lean/lean-toolchain"):
            with self.subTest(name=name):
                path = self.root / name
                original = path.read_bytes()
                path.write_bytes(original + b"\n-- source changed\n")
                self.rejected("stale source identity|admitted semantic dependency changed|recorded Lean/Std toolchain")
                path.unlink()
                self.rejected("cannot read")
                path.write_bytes(original)

    def test_new_source_file_invalidates_recorded_complete_closure(self):
        path = self.root / "lean/Qleisli/NewUnreviewed.lean"
        path.write_text("def newUnreviewed : Nat := 1\n")
        self.rejected("source closure differs")

    def test_rebound_record_cannot_omit_a_source_dependency(self):
        record = copy.deepcopy(self.record)
        del record["source_revision"]["files"]["lean/Qleisli/NativeValidity.lean"]
        record["source_revision"]["sha256"] = checker.digest(checker.registry.canonical(record["source_revision"]["files"]))
        self.write_record(record)
        self.rejected("source closure differs")

    def test_all_recorded_artifacts_reject_changes_or_removal(self):
        for name in (*self.record["files"], checker.VALIDATION_PATH, checker.ADOPTION_PATH, checker.REVIEWED_PATH):
            with self.subTest(name=name):
                path = self.root / name
                original = path.read_bytes()
                path.write_bytes(original + b"\nchanged\n")
                self.rejected("SHA-256 mismatch")
                path.unlink()
                self.rejected("cannot read")
                path.write_bytes(original)

    def test_review_script_and_output_cannot_be_rebound_to_different_types(self):
        for field, name in (("review_source", checker.REVIEW_PATH), ("printed_declarations", checker.REVIEW_STDOUT)):
            with self.subTest(field=field):
                path = self.root / name
                original = path.read_bytes()
                path.write_bytes(original.replace(b"check_ownershipSafe", b"check_otherClaim"))
                record = copy.deepcopy(self.record)
                record["files"][name] = checker.digest(path.read_bytes())
                self.write_record(record)
                proposal = json.loads((self.root / checker.PROPOSAL_PATH).read_bytes())
                proposal["evidence"][field]["sha256"] = record["files"][name]
                self.write_json(checker.PROPOSAL_PATH, proposal)
                self.rejected("SHA-256 mismatch|proposal evidence")
                path.write_bytes(original)

    def test_evidence_commands_require_actual_checks_and_success(self):
        for action in ("missing", "argv", "cwd", "exit", "bool-exit", "output", "duration"):
            with self.subTest(action=action):
                record = copy.deepcopy(self.record)
                command = record["commands"][0]
                if action == "missing":
                    record["commands"].pop()
                elif action == "argv":
                    command["argv"] = ["true"]
                elif action == "cwd":
                    command["cwd"] = ".."
                elif action in {"exit", "bool-exit"}:
                    command["exit_code"] = 1 if action == "exit" else False
                elif action == "output":
                    command["stdout"] = checker.REPLAY_STDOUT
                else:
                    command["seconds"] = True
                self.write_record(record)
                self.rejected()

    def test_audit_evidence_cannot_use_stale_source_or_skip_actual_audits(self):
        original = (self.root / checker.AUDIT_PATH).read_bytes()
        for action in ("source", "status", "commands", "audit", "mode"):
            with self.subTest(action=action):
                audit = json.loads(original)
                if action == "source":
                    audit["source_revision"] = "0" * 64
                elif action == "status":
                    audit["status"] = "failed"
                elif action == "commands":
                    audit["commands"].pop()
                elif action == "mode":
                    audit["mode"] = "source-identity-only"
                else:
                    audit["commands"][2]["argv"] = ["lake", "env", "lean", "Unrelated.lean"]
                self.write_json(checker.CURRENT_AUDIT_PATH, audit)
                record = copy.deepcopy(self.record)
                record["build_and_audit_record"] = checker.CURRENT_AUDIT_PATH
                del record["files"][checker.AUDIT_PATH]
                record["files"][checker.CURRENT_AUDIT_PATH] = checker.digest((self.root / checker.CURRENT_AUDIT_PATH).read_bytes())
                self.write_record(record)
                self.rejected()

    def test_duplicate_fields_reject_in_proposal_and_rebound_evidence(self):
        path = self.root / checker.PROPOSAL_PATH
        original = path.read_bytes()
        path.write_bytes(original.replace(b'"version": 1', b'"version": 1, "version": 1'))
        with patch.object(checker, "PROPOSAL_SHA256", checker.digest(path.read_bytes())):
            self.rejected("duplicate JSON field")
        path.write_bytes(original)
        path = self.root / checker.CURRENT_PATH
        path.write_bytes(path.read_bytes().replace(b'"version": 1', b'"version": 1, "version": 1'))
        self.rejected("duplicate JSON field")

    def test_reference_paths_and_symlink_sources_cannot_escape(self):
        proposal = copy.deepcopy(self.proposal)
        proposal["evidence"]["validation_record"]["path"] = "../../outside.json"
        self.write_json(checker.PROPOSAL_PATH, proposal)
        self.rejected("SHA-256 mismatch")
        shutil.copyfile(ROOT / checker.PROPOSAL_PATH, self.root / checker.PROPOSAL_PATH)
        for name in (checker.NATIVE_SOURCE, checker.REVIEW_PATH, checker.VALIDATION_PATH, checker.PROPOSAL_PATH):
            with self.subTest(name=name):
                path = self.root / name
                original = path.read_bytes()
                other = self.root / "other-file"
                other.write_bytes(original)
                path.unlink()
                path.symlink_to(other)
                self.rejected("cannot read")
                path.unlink()
                path.write_bytes(original)

    def test_replay_runs_only_fixed_review_command_and_compares_both_streams(self):
        stdout = (self.root / checker.REVIEW_STDOUT).read_bytes()
        def successful(argv, **kwargs):
            if argv == checker.continuity.ARGV:
                data = gzip.decompress((self.root / checker.continuity.CURRENT_PATH).read_bytes())
            else:
                output = checker.REVIEW_STDOUT if argv == checker.REVIEW_ARGV else checker.BINDING_STDOUT
                data = (self.root / output).read_bytes()
            return subprocess.CompletedProcess(argv, 0, data, b"")
        with patch.object(checker.subprocess, "run", side_effect=successful) as run:
            checked = checker.check(self.root, verify_lean=True)
            self.assertEqual(run.call_args_list, [call(checker.REVIEW_ARGV, cwd=self.root / "lean", capture_output=True, check=False),
                                                 call(checker.BINDING_ARGV, cwd=self.root / "lean", capture_output=True, check=False),
                                                 call(checker.continuity.ARGV, cwd=self.root / "lean", capture_output=True, check=False)])
        self.assertEqual(checked["mode"], "current-Lean-identity-transport-and-source-identity")
        for code, out, err in ((1, stdout, b"proof failed"), (0, stdout + b"changed", b""), (0, stdout, b"warning")):
            with self.subTest(code=code, stderr=err):
                result = subprocess.CompletedProcess(checker.REVIEW_ARGV, code, out, err)
                with patch.object(checker.subprocess, "run", return_value=result):
                    self.rejected("Lean review failed|differs from recorded review", verify_lean=True)

    def test_replay_rechecks_sources_after_external_command(self):
        def edit_source(argv, **kwargs):
            path = self.root / checker.NATIVE_SOURCE
            path.write_bytes(path.read_bytes() + b"\n-- changed during Lean\n")
            if argv == checker.continuity.ARGV:
                data = gzip.decompress((self.root / checker.continuity.CURRENT_PATH).read_bytes())
            else:
                output = checker.REVIEW_STDOUT if argv == checker.REVIEW_ARGV else checker.BINDING_STDOUT
                data = (self.root / output).read_bytes()
            return subprocess.CompletedProcess(argv, 0, data, b"")
        with patch.object(checker.subprocess, "run", side_effect=edit_source):
            self.rejected("stale source identity", verify_lean=True)

    def test_unrelated_current_proof_source_may_evolve_without_repinning_history(self):
        before = (self.root / checker.VALIDATION_PATH).read_bytes()
        path = self.root / "lean/Qleisli/NativeValidity.lean"
        path.write_bytes(path.read_bytes() + b"\n-- implementation-only proof maintenance\n")
        revision = self.refresh_test_current_identity(continuity_replayed=True)
        result = checker.check(self.root)
        self.assertEqual(result["source_revision"], revision["sha256"])
        self.assertNotEqual(result["source_revision"], self.record["source_revision"]["sha256"])
        self.assertEqual((self.root / checker.VALIDATION_PATH).read_bytes(), before)
        self.assertEqual(checker.digest((self.root / checker.PROPOSAL_PATH).read_bytes()), checker.PROPOSAL_SHA256)

    def test_updated_proof_records_cannot_waive_a_changed_semantic_dependency(self):
        path = self.root / "lean-kernel/QleisliKernel/Semantics/Raw.lean"
        path.write_bytes(path.read_bytes() + b"\n-- semantic-source change requires transport review\n")
        self.refresh_test_current_identity()
        self.rejected("stale continuity extraction")

    def test_rebound_current_source_cannot_silently_replace_the_standard_library_basis(self):
        (self.root / "lean/lean-toolchain").write_text("leanprover/lean4:v4.31.0\n")
        self.refresh_test_current_identity()
        self.rejected("recorded Lean/Std toolchain")

    def test_semantic_baseline_cannot_drop_transitive_dependencies(self):
        path = self.root / checker.SEMANTIC_PATH
        baseline = json.loads(path.read_bytes())
        del baseline["files"]["lean-kernel/QleisliKernel/Semantics/Raw.lean"]
        baseline["sha256"] = checker.digest(checker.registry.canonical(baseline["files"]))
        self.write_json(checker.SEMANTIC_PATH, baseline)
        current = json.loads((self.root / checker.CURRENT_PATH).read_bytes())
        current["semantic_baseline"]["sha256"] = checker.digest(path.read_bytes())
        self.write_json(checker.CURRENT_PATH, current)
        self.rejected("differs from the admitted historical dependency closure")

    def test_historical_archives_cannot_be_removed_changed_or_linked(self):
        for name in (checker.ARCHIVE_PATH, checker.ARCHIVED_REGISTRY_PATH):
            with self.subTest(name=name):
                path = self.root / name
                original = path.read_bytes()
                path.write_bytes(original + b"changed")
                self.rejected("SHA-256 mismatch")
                path.unlink()
                self.rejected("cannot read")
                path.write_bytes(original)

    def test_weakened_acceptance_fields_reject_even_after_refreshing_current_source_evidence(self):
        path = self.root / checker.NATIVE_SOURCE
        original = path.read_text()
        for field in ("packetBound", "artifactBound", "requestBound", "accepted", "requested"):
            with self.subTest(field=field):
                weakened = re.sub(r"^  " + field + r" : [^\n]*$", "  " + field + " : True", original, flags=re.M)
                self.assertNotEqual(weakened, original)
                if field == "packetBound":
                    weakened = weakened.replace("requirement,b,c,bound,hd,hr,ha,result.1.symm",
                                                "requirement,b,c,True.intro,hd,hr,ha,result.1.symm")
                path.write_text(weakened)
                self.refresh_test_current_identity()
                self.rejected("stale continuity extraction")

    def test_artifact_root_representation_cannot_escape_the_semantic_baseline(self):
        path = self.root / "lean-kernel/QleisliKernel/Semantics/Qirf.lean"
        original = path.read_text()
        changed = original.replace("  root : Nat", "  root : Bool")
        self.assertNotEqual(changed, original)
        path.write_text(changed)
        self.refresh_test_current_identity()
        self.rejected("stale continuity extraction")

    def test_elaborated_binding_review_detects_changed_field_meaning_even_when_outer_types_match(self):
        first = subprocess.CompletedProcess(checker.REVIEW_ARGV, 0, (self.root / checker.REVIEW_STDOUT).read_bytes(), b"")
        changed = (self.root / checker.BINDING_STDOUT).read_bytes().replace(b"Acceptance.packetBound : @Eq.{1}",
                                                                        b"Acceptance.packetBound : True")
        second = subprocess.CompletedProcess(checker.BINDING_ARGV, 0, changed, b"")
        with patch.object(checker.subprocess, "run", side_effect=[first, second]):
            self.rejected("differs from recorded review evidence", verify_lean=True)

    def test_binding_review_artifacts_and_metadata_cannot_be_rebound_or_skipped(self):
        original = (self.root / checker.CURRENT_PATH).read_bytes()
        for field in ("source", "stdout", "stderr"):
            with self.subTest(field=field):
                current = json.loads(original)
                name = current["binding_review"][field]["path"]
                path = self.root / name
                data = path.read_bytes()
                path.write_bytes(data + b"changed")
                current["binding_review"][field]["sha256"] = checker.digest(path.read_bytes())
                self.write_json(checker.CURRENT_PATH, current)
                self.rejected("binding review")
                path.write_bytes(data)
        current = json.loads(original)
        current["binding_review"]["command"]["argv"] = ["true"]
        self.write_json(checker.CURRENT_PATH, current)
        self.rejected("binding review command")


    def test_semantic_source_formatting_and_proof_body_changes_use_identity_transport(self):
        before = (self.root / checker.PROPOSAL_PATH).read_bytes()
        path = self.root / "lean-kernel/QleisliKernel/Semantics/Ownership.lean"
        path.write_bytes(path.read_bytes().replace(b"def OwnershipSafe", b"def   OwnershipSafe"))
        path = self.root / checker.NATIVE_SOURCE
        path.write_text(path.read_text().replace("exact ⟨binding,", "exact id ⟨binding,"))
        self.refresh_test_current_identity(continuity_replayed=True)
        # This verifies the identity-record protocol, not Lean proof execution.
        # The fixture's isolated real Lean tests cover an actual proof refactor.
        self.assertEqual(checker.check(self.root)["mode"], "source-identity-only")
        self.assertEqual((self.root / checker.PROPOSAL_PATH).read_bytes(), before)

    def test_continuity_evidence_cannot_omit_rebind_or_select_another_extractor(self):
        original = (self.root / checker.CURRENT_PATH).read_bytes()
        for action in ("omit", "stale", "extractor", "baseline", "command", "stdout", "stderr", "promote"):
            with self.subTest(action=action):
                current = json.loads(original)
                binding = current["continuity"]
                if action == "omit":
                    del current["continuity"]
                elif action == "stale":
                    binding["source_revision_sha256"] = "0" * 64
                elif action in {"extractor", "baseline"}:
                    binding[action]["sha256"] = "0" * 64
                elif action == "command":
                    binding["command"]["argv"] = ["true"]
                elif action in {"stdout", "stderr"}:
                    binding[action]["path"] = "../../other"
                else:
                    binding["discharged_guarantees"] = ["QS-2026-01"]
                self.write_json(checker.CURRENT_PATH, current)
                self.rejected()

    def test_historical_continuity_artifacts_are_confined_and_cannot_be_rebound(self):
        for name in (checker.continuity.BASELINE_PATH, checker.continuity.EXTRACTOR_PATH,
                     checker.continuity.REVIEWED_PATH, checker.continuity.CURRENT_PATH,
                     checker.continuity.STDERR_PATH):
            with self.subTest(name=name):
                path = self.root / name
                original = path.read_bytes()
                path.write_bytes(original + b"changed")
                self.rejected("SHA-256 mismatch")
                path.unlink()
                path.symlink_to(ROOT / name)
                self.rejected("cannot read")
                path.unlink()
                path.write_bytes(original)

    def test_actual_extraction_must_match_full_closed_meaning_even_with_rebound_records(self):
        continuity = checker.continuity
        output = gzip.decompress((self.root / continuity.CURRENT_PATH).read_bytes())
        rows = json.loads(output)
        def run_with_extraction(data, code=0, stderr=b""):
            def run(argv, **kwargs):
                if argv == continuity.ARGV:
                    return subprocess.CompletedProcess(argv, code, data, stderr)
                path = checker.REVIEW_STDOUT if argv == checker.REVIEW_ARGV else checker.BINDING_STDOUT
                return subprocess.CompletedProcess(argv, 0, (self.root / path).read_bytes(), b"")
            return run
        for action in ("root-omission", "declaration-omission", "theorem-substitution", "definition-weakening", "origin", "universe", "constructor"):
            with self.subTest(action=action):
                modified = copy.deepcopy(rows)
                if action == "root-omission":
                    modified["roots"].pop()
                elif action == "declaration-omission":
                    modified["declarations"].pop()
                else:
                    # Every nested Expr and origin is part of the exact snapshot;
                    # changing a type, body, constructor or binder cannot hide
                    # behind pretty-printing or another closed theorem.
                    selected = next(row for row in modified["declarations"] if row["project"])
                    selected["module" if action == "origin" else "declaration"] = [action]
                data = json.dumps(modified).encode()
                with patch.object(checker.subprocess, "run", side_effect=run_with_extraction(data)):
                    self.rejected("current elaborated meaning", verify_lean=True)
        for code, err in ((1, b"unknown origin"), (0, b"warning")):
            with patch.object(checker.subprocess, "run", side_effect=run_with_extraction(output, code, err)):
                self.rejected("extraction failed|diagnostics", verify_lean=True)

    def test_live_replay_rejects_simultaneous_source_and_evidence_rebinding(self):
        def rebind_after_extraction(argv, **kwargs):
            if argv == checker.continuity.ARGV:
                data = gzip.decompress((self.root / checker.continuity.CURRENT_PATH).read_bytes())
                path = self.root / checker.NATIVE_SOURCE
                path.write_bytes(path.read_bytes() + b"\n-- concurrently rebound source\n")
                self.refresh_test_current_identity(continuity_replayed=True)
                return subprocess.CompletedProcess(argv, 0, data, b"")
            output = checker.REVIEW_STDOUT if argv == checker.REVIEW_ARGV else checker.BINDING_STDOUT
            return subprocess.CompletedProcess(argv, 0, (self.root / output).read_bytes(), b"")
        with patch.object(checker.subprocess, "run", side_effect=rebind_after_extraction):
            self.rejected("current evidence changed during Lean replay", verify_lean=True)

    def test_dependency_manifest_change_cannot_create_a_new_external_trust_boundary(self):
        path = self.root / "lean/lake-manifest.json"
        path.write_bytes(path.read_bytes() + b" ")
        self.refresh_test_current_identity(continuity_replayed=True)
        self.rejected("external dependency manifest changed")


if __name__ == "__main__":
    unittest.main()
