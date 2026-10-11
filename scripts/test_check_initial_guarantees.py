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
    # These tests intentionally materialize the admitted historical checker.
    # Reconstruct its exact identity profile from the immutable baseline rather
    # than transplant a current representation-extension record into old code.
    shutil.copyfile(destination / continuity.REVIEWED_PATH, destination / continuity.CURRENT_PATH)
    current["continuity"] = dict(
        format="qleisli.current-artifact-identity-transport", version=1,
        baseline=dict(path=continuity.BASELINE_PATH, sha256=continuity.BASELINE_SHA256),
        extractor=dict(path=continuity.EXTRACTOR_PATH, sha256=continuity.EXTRACTOR_SHA256),
        source_revision_sha256=record["source_revision"]["sha256"],
        command=dict(argv=continuity.ARGV, cwd="lean", exit_code=0),
        stdout=dict(path=continuity.CURRENT_PATH, compression="gzip",
                    sha256=baseline["expressions"]["sha256"],
                    uncompressed_sha256=baseline["expressions"]["uncompressed_sha256"]),
        stderr=dict(path=continuity.STDERR_PATH, sha256=continuity.digest(b"")))
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




class ProtectedBasisTransportProjection(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.reviewed = gzip.decompress((ROOT / checker.continuity.REVIEWED_PATH).read_bytes())
        cls.snapshot = json.loads(cls.reviewed)

    def mutated(self, name, change):
        snapshot = copy.deepcopy(self.snapshot)
        for entry in snapshot["declarations"]:
            if checker.continuity.expression_name(entry["name"]) == name:
                change(entry)
                break
        else:
            self.fail("missing real declaration: " + name)
        return json.dumps(snapshot).encode()

    def test_real_independent_meaning_closure_and_bindings_are_selected(self):
        result = checker.continuity.compare_protected_projection(self.reviewed, self.reviewed)
        self.assertGreater(result["independent_meaning_declarations"], 200)
        self.assertGreater(result["protected_declarations"], result["independent_meaning_declarations"])

    def test_changed_property_program_and_actual_success_premise_reject(self):
        for name in (*checker.continuity.SEMANTIC_ROOTS, *checker.continuity.ACTUAL_ENDPOINTS):
            with self.subTest(name=name):
                changed = self.mutated(name, lambda entry: entry.update(declaration=["forged-trivial-type"]))
                with self.assertRaisesRegex(PacketError, "changed protected meaning or original-subject binding"):
                    checker.continuity.compare_protected_projection(changed, self.reviewed)

    def test_original_artifact_and_byte_witness_cannot_change_origin_or_fields(self):
        for name in checker.continuity.BINDING_PREFIXES:
            with self.subTest(name=name):
                changed = self.mutated(name, lambda entry: entry.update(project=False))
                with self.assertRaisesRegex(PacketError, "changed protected meaning or original-subject binding"):
                    checker.continuity.compare_protected_projection(changed, self.reviewed)

    def test_duplicate_declarations_and_changed_roots_reject(self):
        for mutation in ("duplicate", "root", "boolean-version"):
            snapshot = copy.deepcopy(self.snapshot)
            if mutation == "duplicate":
                snapshot["declarations"].append(snapshot["declarations"][0])
            elif mutation == "root":
                snapshot["roots"].pop()
            else:
                snapshot["version"] = True
            with self.subTest(mutation=mutation), self.assertRaises(PacketError):
                checker.continuity.compare_protected_projection(json.dumps(snapshot).encode(), self.reviewed)


class CheckedBasisTransportProfile(unittest.TestCase):
    def setUp(self):
        c = checker.continuity
        self.current = json.loads((ROOT / checker.CURRENT_PATH).read_text())["continuity"]
        self.binding = copy.deepcopy(self.current)
        self.binding.pop("raw_transport", None)
        # Exercise the still-supported Basis profile against the immutable
        # historical expression bytes, independently of the active profile.
        self.compressed = (ROOT / c.REVIEWED_PATH).read_bytes()
        self.binding.update(extractor=dict(path=c.EXTRACTOR_PATH, sha256=c.EXTRACTOR_SHA256),
            command=dict(argv=c.ARGV, cwd="lean", exit_code=0),
            stdout=dict(path=c.CURRENT_PATH, compression="gzip", sha256=c.digest(self.compressed),
                        uncompressed_sha256=c.digest(gzip.decompress(self.compressed))))
        read = checker.read_file
        self.fixture_read = lambda root, name: self.compressed if name == c.CURRENT_PATH else read(root, name)
        patched = patch("check_ratification_packet.read_file", side_effect=self.fixture_read)
        patched.start()
        self.addCleanup(patched.stop)
        self.binding.update(format=c.BASIS_FORMAT, transport=dict(
            source=dict(path=c.TRANSPORT_SOURCE, sha256=c.TRANSPORT_SHA256),
            review=dict(path=c.TRANSPORT_REVIEW, sha256=c.TRANSPORT_REVIEW_SHA256),
            stdout=dict(path=c.TRANSPORT_STDOUT, sha256=c.TRANSPORT_STDOUT_SHA256),
            stderr=dict(path=c.STDERR_PATH, sha256=c.digest(b"")),
            command=dict(argv=c.TRANSPORT_ARGV, cwd="lean", exit_code=0)))
        self.revision = dict(sha256=self.binding["source_revision_sha256"],
                             files={c.TRANSPORT_SOURCE: c.TRANSPORT_SHA256})
        self.expected = json.loads((ROOT / c.BASELINE_PATH).read_text())

    def validate(self):
        # The immutable baseline is already tested separately. Keep these unit
        # tests focused on profile dispatch and real proof/review file binding.
        with patch.object(checker.continuity, "baseline", return_value=self.expected), \
             patch.object(checker.continuity, "compare_protected_projection", return_value={}):
            return checker.continuity.validate(ROOT, self.binding, self.revision, {})

    def test_recorded_projection_and_live_extraction_are_both_checked(self):
        c = checker.continuity
        with patch.object(c, "baseline", return_value=self.expected):
            c.validate(ROOT, self.binding, self.revision, {})
        current = gzip.decompress(self.compressed)
        transport = (ROOT / c.TRANSPORT_STDOUT).read_bytes()
        def run(argv, **kwargs):
            output = transport if argv == c.TRANSPORT_ARGV else current
            return subprocess.CompletedProcess(argv, 0, output, b"")
        with patch.object(c, "baseline", return_value=self.expected), patch.object(c.subprocess, "run", side_effect=run):
            c.replay(ROOT, self.binding, self.revision, {})
        def forged(argv, **kwargs):
            result = run(argv, **kwargs)
            if argv == c.ARGV:
                result.stdout += b" "
            return result
        with patch.object(c, "baseline", return_value=self.expected), patch.object(c.subprocess, "run", side_effect=forged), \
             self.assertRaisesRegex(PacketError, "fresh basis extraction differs"):
            c.replay(ROOT, self.binding, self.revision, {})

    def test_fixed_proof_and_review_are_required(self):
        self.validate()
        for field in ("source", "review", "stdout", "stderr", "command"):
            original = copy.deepcopy(self.binding)
            self.binding["transport"][field] = {}
            with self.subTest(field=field), self.assertRaises(PacketError):
                self.validate()
            self.binding = original
        del self.binding["transport"]
        with self.assertRaises(PacketError):
            self.validate()

    def test_stale_revision_and_missing_source_closure_reject(self):
        self.binding["source_revision_sha256"] = "0" * 64
        with self.assertRaisesRegex(PacketError, "stale continuity"):
            self.validate()
        self.binding["source_revision_sha256"] = self.revision["sha256"]
        self.revision["files"] = {}
        with self.assertRaisesRegex(PacketError, "source closure"):
            self.validate()

    def test_boolean_command_exit_codes_cannot_stand_for_success(self):
        for location in (self.binding["command"], self.binding["transport"]["command"]):
            location["exit_code"] = False
            with self.assertRaisesRegex(PacketError, "exit code type"):
                self.validate()
            location["exit_code"] = 0

    def test_unknown_profile_and_boolean_version_reject(self):
        self.binding["version"] = True
        with self.assertRaisesRegex(PacketError, "version"):
            self.validate()
        self.binding["version"] = 1
        self.binding["format"] += "-unchecked"
        with self.assertRaises(PacketError):
            self.validate()

    def test_changed_transport_source_review_output_or_reference_semantics_reject(self):
        c = checker.continuity
        original_read = self.fixture_read
        for changed_path in (c.TRANSPORT_SOURCE, c.TRANSPORT_REVIEW, c.TRANSPORT_STDOUT, c.QIRF_SEMANTICS):
            def altered(root, name):
                data = original_read(root, name)
                return data + b"\n-- changed evidence\n" if name == changed_path else data
            with self.subTest(path=changed_path), patch("check_ratification_packet.read_file", side_effect=altered), \
                 self.assertRaises(PacketError):
                self.validate()

    def test_live_type_review_rejects_failed_forged_or_warning_output(self):
        c = checker.continuity
        output = (ROOT / c.TRANSPORT_STDOUT).read_bytes()
        for code, stdout, stderr in ((1, output, b""), (0, b"forged", b""), (0, output, b"warning")):
            result = subprocess.CompletedProcess(c.TRANSPORT_ARGV, code, stdout, stderr)
            with self.subTest(code=code, stderr=stderr), patch.object(c.subprocess, "run", return_value=result), \
                 self.assertRaises(PacketError):
                c.replay_transport(ROOT)
        with patch.object(c.subprocess, "run", return_value=subprocess.CompletedProcess(c.TRANSPORT_ARGV, 0, output, b"")):
            c.replay_transport(ROOT)


class CheckedRawTransportProfile(unittest.TestCase):
    def setUp(self):
        c = checker.continuity
        self.reviewed = gzip.decompress((ROOT / c.REVIEWED_PATH).read_bytes())
        old = json.loads(self.reviewed)
        # Bounded in-memory test data, not a regenerated production snapshot.
        entries = {c.expression_name(row["name"]): copy.deepcopy(row) for row in old["declarations"]}
        for row in old["declarations"]:
            before = c.expression_name(row["name"])
            after = c.raw_rename(before)
            if before != after:
                mapped = c.raw_convert(row)
                module = c.expression_name(row["module"]).rsplit(".", 1)[-1]
                mapped["module"] = c.elaborated_name("Qleisli.Semantics.RawLegacy." + module)
                entries[after] = mapped
        old["roots"] += [c.raw_convert(name) for name in old["roots"][:3]]
        old["declarations"] = list(entries.values())
        self.snapshot = old
        self.output = json.dumps(old).encode()
        self.compressed = gzip.compress(self.output, mtime=0)
        self.binding = copy.deepcopy(json.loads((ROOT / checker.CURRENT_PATH).read_text())["continuity"])
        self.binding.update(format=c.RAW_FORMAT,
            extractor=dict(path=c.RAW_EXTRACTOR, sha256=c.RAW_EXTRACTOR_SHA256),
            command=dict(argv=c.RAW_ARGV, cwd="lean", exit_code=0),
            stdout=dict(path=c.CURRENT_PATH, compression="gzip", sha256=c.digest(self.compressed),
                        uncompressed_sha256=c.digest(self.output)),
            raw_transport=dict(sources=c.RAW_SOURCES,
                review=dict(path=c.RAW_REVIEW, sha256=c.RAW_REVIEW_SHA256),
                stdout=dict(path=c.RAW_STDOUT, sha256=c.RAW_STDOUT_SHA256),
                stderr=dict(path=c.STDERR_PATH, sha256=c.digest(b"")),
                command=dict(argv=c.RAW_REVIEW_ARGV, cwd="lean", exit_code=0)))
        self.revision = dict(sha256=self.binding["source_revision_sha256"],
                             files={**c.RAW_SOURCES, c.TRANSPORT_SOURCE: c.TRANSPORT_SHA256})
        self.expected = json.loads((ROOT / c.BASELINE_PATH).read_text())

    def validate(self):
        c = checker.continuity
        read = checker.read_file
        def contents(root, name):
            return self.compressed if name == c.CURRENT_PATH else read(root, name)
        with patch.object(c, "baseline", return_value=self.expected), \
             patch("check_ratification_packet.read_file", side_effect=contents):
            return c.validate(ROOT, self.binding, self.revision, {})

    def test_real_typed_proof_files_and_all_historical_meanings_required(self):
        result = checker.continuity.compare_raw_projection(self.output, self.reviewed)
        self.assertGreater(result["independent_meaning_declarations"], 200)
        self.assertGreater(result["protected_bindings"], 20)
        self.validate()

    def test_weakened_semantics_and_original_subject_rejected(self):
        c = checker.continuity
        names = [c.raw_rename(name) for name in c.SEMANTIC_ROOTS]
        names += ["Qleisli.Semantics.RawLegacy.Ownership.Pure.mk",
                  "Qleisli.Semantics.RawLegacy.Raw.Op", *c.ACTUAL_ENDPOINTS, *c.BINDING_PREFIXES]
        for name in names:
            changed = copy.deepcopy(self.snapshot)
            row = next(row for row in changed["declarations"] if c.expression_name(row["name"]) == name)
            row["declaration"] = ["const", c.elaborated_name("True"), []]
            with self.subTest(name=name), self.assertRaises(PacketError):
                c.compare_raw_projection(json.dumps(changed).encode(), self.reviewed)

    def test_binder_display_names_only_may_change(self):
        c = checker.continuity
        term = ["forall", c.elaborated_name("before"), "default", ["sort", ["zero"]], ["bvar", 0]]
        renamed = copy.deepcopy(term)
        renamed[1] = c.elaborated_name("after")
        self.assertEqual(c.raw_convert(term), c.raw_convert(renamed))
        for index, replacement in ((2, "implicit"), (3, ["sort", ["succ", ["zero"]]]), (4, ["bvar", 1])):
            changed = copy.deepcopy(renamed)
            changed[index] = replacement
            self.assertNotEqual(c.raw_convert(term), c.raw_convert(changed))

    def test_wrong_origin_missing_definition_duplicate_and_roots_reject(self):
        c = checker.continuity
        for mutation in ("origin", "missing", "duplicate", "root", "boolean-version"):
            changed = copy.deepcopy(self.snapshot)
            if mutation == "origin":
                next(row for row in changed["declarations"] if c.expression_name(row["name"]) ==
                     "Qleisli.Semantics.RawLegacy.Ownership.OwnershipSafe")["project"] = False
            elif mutation == "missing":
                changed["declarations"] = [row for row in changed["declarations"] if c.expression_name(row["name"]) !=
                                           "Qleisli.Semantics.RawLegacy.Ownership.Pure.mk"]
            elif mutation == "duplicate":
                changed["declarations"].append(changed["declarations"][0])
            elif mutation == "root":
                changed["roots"].pop()
            else:
                changed["version"] = True
            with self.subTest(mutation=mutation), self.assertRaises(PacketError):
                c.compare_raw_projection(json.dumps(changed).encode(), self.reviewed)

    def test_proof_sources_extractors_and_commands_cannot_be_selected_by_record(self):
        mutations = (
            lambda b: b.pop("raw_transport"),
            lambda b: b["raw_transport"].update(sources={}),
            lambda b: b["raw_transport"]["command"].update(exit_code=False),
            lambda b: b["raw_transport"].update(review={}),
            lambda b: b["extractor"].update(sha256="0" * 64),
            lambda b: b["command"].update(argv=checker.continuity.ARGV),
            lambda b: b.update(version=True),
            lambda b: b.update(source_revision_sha256="0" * 64),
        )
        for mutate in mutations:
            previous = copy.deepcopy(self.binding)
            mutate(self.binding)
            with self.assertRaises(PacketError):
                self.validate()
            self.binding = previous
        self.revision["files"] = {}
        with self.assertRaisesRegex(PacketError, "source closure"):
            self.validate()

    def test_live_review_and_extraction_both_required(self):
        c = checker.continuity
        read = checker.read_file
        def contents(root, name):
            return self.compressed if name == c.CURRENT_PATH else read(root, name)
        outputs = {tuple(c.TRANSPORT_ARGV): read(ROOT, c.TRANSPORT_STDOUT),
                   tuple(c.RAW_REVIEW_ARGV): read(ROOT, c.RAW_STDOUT), tuple(c.RAW_ARGV): self.output}
        for fail in (None, "typed", "extraction", "warning", "exit"):
            def run(argv, **kwargs):
                output = outputs[tuple(argv)]
                if fail == "typed" and argv == c.RAW_REVIEW_ARGV:
                    output += b"forged"
                if fail == "extraction" and argv == c.RAW_ARGV:
                    output += b" "
                return subprocess.CompletedProcess(argv, 1 if fail == "exit" else 0,
                    output, b"warning" if fail == "warning" else b"")
            with patch.object(c, "baseline", return_value=self.expected), \
                 patch("check_ratification_packet.read_file", side_effect=contents), \
                 patch.object(c.subprocess, "run", side_effect=run) as commands:
                if fail is None:
                    c.replay(ROOT, self.binding, self.revision, {})
                    self.assertEqual([call.args[0] for call in commands.call_args_list],
                                     [c.TRANSPORT_ARGV, c.RAW_REVIEW_ARGV, c.RAW_ARGV])
                else:
                    with self.assertRaises(PacketError):
                        c.replay(ROOT, self.binding, self.revision, {})


if __name__ == "__main__":
    unittest.main()
