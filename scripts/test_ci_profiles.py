"""Adversarial routing and required-check regressions, with real Git diffs."""

import copy
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
from ci_profiles import ROOT, SUITES, check_needs, classify, load_policy, main, plan, proof_lane, registry_binding_only


class CIProfiles(unittest.TestCase):
    def setUp(self):
        self.policy = load_policy(ROOT)

    def test_only_explicit_descriptive_documents_and_publication_records_are_light(self):
        for path in self.policy["documentation_only"] + [
            "tests/fixtures/releases/v0.2.5/publication.json",
            "tests/fixtures/ci_latency/measurements.json",
        ]:
            with self.subTest(path=path):
                self.assertEqual(classify([path], self.policy)[0], "docs")

    def test_normative_protected_executable_and_unknown_inputs_are_full(self):
        for path in [
            "TRUSTBOUNDARY.md", "CONSTITUTION.md", ".github/ci/protected-artifacts.json",
            ".github/ci/profiles.json", ".github/workflows/ci.yml", "Cargo.toml", "Cargo.lock",
            "README.crates.md", "LICENSE", "NOTICE", "docs/type-system.md", "docs/syntax-v0.md",
            "docs/release-milestones.md", "docs/finite-contracts.md", "src/verify.rs",
            "lean/Qleisli/Schema.lean", "lean-kernel/QleisliKernel/Raw.lean",
            "lean/schema-registry.json", "corpus/manifest.json", "corpus/upstream/source/file",
            "tests/fixtures/releases/v0.2.5/kernel-refactoring-equivalence.lean",
            "tests/fixtures/releases/v0.2.5/baseline-validation.json", "new/unknown.md",
            "../AGENTS.md", "docs/releases/../type-system.md", "docs/releases/v0.2.6.md\n",
            "docs/releases/v0.2.6.md/child", "tests/fixtures/ci_latency/nested/oracle.json",
        ]:
            with self.subTest(path=path):
                self.assertEqual(classify(["CHANGELOG.md", path], self.policy)[0], "full")
        self.assertEqual(classify([], self.policy)[0], "full")
        broadened = copy.deepcopy(self.policy)
        protected = ["src/verify.rs", ".github/ci/profiles.json", "Cargo.toml", "LICENSE",
                     "docs/type-system.md", "CONSTITUTION.md", "TRUSTBOUNDARY.md", "tests/proof.lean"]
        broadened["documentation_only"] += protected
        for path in protected:
            self.assertEqual(classify([path], broadened)[0], "full")

    def needs(self, profile):
        return {
            "changes": {"result": "success", "outputs": {"profile": profile, "proof_lane": "tests", "head": "a" * 40}},
            **{name: {"result": "success" if profile == "full" or name == "check-docs" else "skipped"} for name in SUITES},
        }

    def test_required_contexts_cannot_hide_selection_or_suite_failures(self):
        for profile in ["docs", "full"]:
            valid = self.needs(profile)
            self.assertEqual(check_needs(valid, "a" * 40), profile)
            for job in valid:
                for failure in ["failure", "cancelled", None]:
                    changed = copy.deepcopy(valid)
                    changed[job]["result"] = failure
                    with self.subTest(profile=profile, job=job, failure=failure):
                        with self.assertRaises(ValueError):
                            check_needs(changed, "a" * 40)
                changed = copy.deepcopy(valid)
                del changed[job]
                with self.assertRaises(ValueError):
                    check_needs(changed, "a" * 40)
        for profile in ["", "unknown", None]:
            with self.assertRaises(ValueError):
                check_needs(self.needs(profile), "a" * 40)
        with self.assertRaises(ValueError):
            check_needs(self.needs("full"), "b" * 40)
        skipped = self.needs("full")
        skipped["check-lean-kernel"]["result"] = "skipped"
        with self.assertRaises(ValueError):
            check_needs(skipped, "a" * 40)

    def test_summary_is_bounded_without_truncating_selection_evidence(self):
        long_diff = ["corpus/" + "nested/" * 8 + f"source-{i}.qli" for i in range(20000)]
        self.assertGreater(len(json.dumps(long_diff).encode()), 1024 * 1024)
        for paths, profile, lane, reason in [
            (long_diff, "full", "full", "protected executable/policy input: scripts/ci_profiles.py"),
            (["CHANGELOG.md"], "docs", "tests", "only explicitly listed descriptive documents/result records"),
            ([], "full", "full", "missing comparison base; full validation required"),
        ]:
            with self.subTest(profile=profile, paths=len(paths)), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                event, report, summary, outputs = [root / name for name in ("event", "report", "summary", "outputs")]
                event.write_text("{}", encoding="utf-8")
                result = dict(format=1, head="a" * 40, base=None, profile=profile,
                              proof_lane=lane, reason=reason, paths=paths)
                stdout = io.StringIO()
                with patch.dict(os.environ, {
                    "GITHUB_EVENT_PATH": str(event), "GITHUB_EVENT_NAME": "pull_request",
                    "GITHUB_SHA": result["head"], "GITHUB_REF": "refs/pull/1/merge",
                    "GITHUB_STEP_SUMMARY": str(summary), "GITHUB_OUTPUT": str(outputs),
                }), patch("ci_profiles.plan", return_value=result), \
                     patch.object(sys, "argv", ["ci_profiles.py", "--report", str(report)]), \
                     patch.object(sys, "stdout", stdout):
                    self.assertEqual(main(), 0)
                self.assertEqual(json.loads(report.read_text()), result)
                self.assertEqual(json.loads(stdout.getvalue()), result)
                self.assertEqual(outputs.read_text(), f"profile={profile}\nproof_lane={lane}\nhead={result['head']}\nbase=\n")
                rendered = summary.read_text()
                self.assertLess(len(rendered.encode()), 16 * 1024)
                displayed = json.loads(rendered.split("```json\n")[1].split("\n```")[0])
                self.assertEqual(displayed, {**{k: v for k, v in result.items() if k != "paths"},
                                             "changed_path_count": len(paths)})
                self.assertIn("ci-selection artifact", rendered)

    def test_test_default_proof_maintenance_and_full_risk_lanes(self):
        for paths, expected in [
            (["src/verify.rs"], "tests"), (["tests/new.rs"], "tests"),
            (["lean-kernel/QleisliKernel/Finite.lean"], "tests"),
            (["lean-kernel/Protocol/HierarchicalFinite.lean"], "tests"),
            (["corpus/manifest.json"], "tests"),
            (["lean/Qleisli/RawPure.lean"], "model"),
            (["docs/type-system.md"], "full"),
            (["TRUSTBOUNDARY.md"], "full"),
            (["CONSTITUTION.md"], "full"),
            (["GOVERNANCE.md"], "full"),
            (["governance/guarantees.json"], "full"),
            (["tests/fixtures/constitution_v030/packet.json"], "full"),
            (["docs/src/reference/authority.md"], "full"),
            (["docs/src/design/initial-interpretations.md"], "full"),
            (["lean/lean-toolchain"], "full"), ([".github/workflows/ci.yml"], "full"),
            (["TRUSTBOUNDARY.md"], "full"),
            (["AGENTS.md", "CLAUDE.md"], "tests"),
            (["scripts/check_schema_registry.py"], "full"),
            (["scripts/package_lean_kernel.py"], "full"),
            (["lean/Audit.lean"], "full"),
            (["lean-kernel/Audit.lean"], "full"),
            (["new/unknown.rs"], "full"), (["../src/new.rs"], "full"),
            (["docs/new-unknown.md"], "full"), ([], "full"),
            (["lean/schema-registry.json"], "full"),
        ]:
            self.assertEqual(proof_lane(paths), expected, paths)
        for lane in ["tests", "model", "full"]:
            needs = self.needs("full")
            needs["changes"]["outputs"]["proof_lane"] = lane
            self.assertEqual(check_needs(needs, "a" * 40), "full")
        for lane in [None, "", "unrecognized"]:
            needs = self.needs("full")
            needs["changes"]["outputs"]["proof_lane"] = lane
            with self.assertRaises(ValueError):
                check_needs(needs, "a" * 40)

    def test_registry_source_updates_do_not_force_full_but_type_changes_do(self):
        old = json.loads((ROOT / "lean/schema-registry.json").read_text())
        new = copy.deepcopy(old)
        new["source_revision"]["sha256"] = "b" * 64
        new["source_revision"]["files"]["new.lean"] = "c" * 64
        with patch("ci_profiles.git", side_effect=[json.dumps(old), json.dumps(new)]):
            self.assertTrue(registry_binding_only(ROOT, "a" * 40, "b" * 40))
        self.assertEqual(proof_lane(["lean-kernel/QleisliKernel/Finite.lean", "lean/schema-registry.json"], self.policy, True), "tests")
        self.assertEqual(proof_lane(["lean/Qleisli/RawPure.lean", "lean/schema-registry.json"], self.policy, True), "model")
        for audit in ["lean/Audit.lean", "lean-kernel/Audit.lean"]:
            with self.subTest(audit=audit):
                self.assertEqual(proof_lane([audit, "lean/schema-registry.json"], self.policy, True), "full")
        for change in [
            lambda m: m["checker"].update(type=["constant", "Bool", []]),
            lambda m: m["entries"][0].update(external_enabled=True),
            lambda m: m.update(version=True),
            lambda m: m.update(unknown=True),
        ]:
            changed = copy.deepcopy(new)
            change(changed)
            with patch("ci_profiles.git", side_effect=[json.dumps(old), json.dumps(changed)]):
                self.assertFalse(registry_binding_only(ROOT, "a" * 40, "b" * 40))
        with patch("ci_profiles.git", side_effect=[json.dumps(old), '{"version":1,"version":1}']):
            self.assertFalse(registry_binding_only(ROOT, "a" * 40, "b" * 40))
        with patch("ci_profiles.git", side_effect=subprocess.CalledProcessError(1, "git")):
            self.assertFalse(registry_binding_only(ROOT, "a" * 40, "b" * 40))

    def test_manual_pr_completion_keeps_cumulative_policy_risk_and_exact_head(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / ".github/ci").mkdir(parents=True)
            (root / ".github/ci/profiles.json").write_text(json.dumps(self.policy))
            def git(*args):
                return subprocess.check_output(["git", *args], cwd=root, stderr=subprocess.DEVNULL).decode().strip()
            git("init", "--quiet")
            git("config", "user.email", "ci-fixture@example.invalid")
            git("config", "user.name", "CI fixture")
            git("add", ".")
            git("commit", "--quiet", "-m", "base")
            base = git("rev-parse", "HEAD")
            (root / ".github/policy").write_text("policy change\n")
            git("add", ".")
            git("commit", "--quiet", "-m", "policy")
            (root / "CHANGELOG.md").write_text("last commit is descriptive\n")
            git("add", ".")
            git("commit", "--quiet", "-m", "docs")
            head = git("rev-parse", "HEAD")
            event = {"repository": {"full_name": "MGYamada/Qleisli"}, "inputs": {
                "completion_issues": "29,69", "completion_pr": "307", "validation": "tests"}}
            metadata = {"number": 307, "base": {"sha": base, "repo": event["repository"]}, "head": {"sha": head}}
            with patch("check_pr_size.completion_pr", return_value=metadata):
                result = plan(root, "workflow_dispatch", event, head, "refs/heads/work")
                self.assertEqual((result["profile"], result["proof_lane"]), ("full", "full"))
                self.assertEqual(result["base"], base)
                self.assertEqual(result["completion_pr"], 307)
                self.assertEqual(result["paths"], [".github/policy", "CHANGELOG.md"])
            with patch("check_pr_size.completion_pr", return_value={**metadata, "head": {"sha": base}}), self.assertRaises(ValueError):
                plan(root, "workflow_dispatch", event, head, "refs/heads/work")

    def test_actual_git_diffs_deleted_renamed_inputs_missing_bases_and_releases(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / ".github/ci").mkdir(parents=True)
            (root / ".github/ci/profiles.json").write_text(json.dumps(self.policy))

            def git(*args):
                return subprocess.check_output(["git", *args], cwd=root, stderr=subprocess.DEVNULL).decode().strip()

            git("init", "--quiet")
            git("config", "user.email", "ci-fixture@example.invalid")
            git("config", "user.name", "CI fixture")
            (root / "AGENTS.md").write_text("working rules\n")
            git("add", ".")
            git("commit", "--quiet", "-m", "base")
            base = git("rev-parse", "HEAD")
            (root / "AGENTS.md").write_text("updated rules\n")
            git("commit", "--quiet", "-am", "docs")
            head = git("rev-parse", "HEAD")
            event = {"pull_request": {"base": {"sha": base}}}
            self.assertEqual(plan(root, "pull_request", event, head, "refs/pull/1/merge")["profile"], "docs")
            self.assertEqual(plan(root, "push", {"before": base}, head, "refs/heads/main")["profile"], "docs")
            completion = {"inputs": {"validation": "tests", "completion_issues": "29,69", "release_base": base}}
            selected = plan(root, "workflow_dispatch", completion, head, "refs/heads/main")
            self.assertEqual(selected["proof_lane"], "tests")
            self.assertEqual(selected["completion_issues"], [29, 69])
            for issues in ["", "0", "-1", "29,29", "#29", "29, 69", "29;echo bad", "9" * 1025,
                           "2147483648"]:
                with self.subTest(issues=issues), self.assertRaises(ValueError):
                    plan(root, "workflow_dispatch", {"inputs": {"completion_issues": issues}}, head, "refs/heads/main")
            with self.assertRaises(ValueError):
                plan(root, "workflow_dispatch", completion, head, "refs/heads/work")
            release = plan(root, "workflow_dispatch", {"inputs": {"release_readiness": "true"}}, head, "refs/heads/work")
            self.assertEqual(release["proof_lane"], "full")
            self.assertEqual(plan(root, "push", {"before": base}, head, "refs/tags/v0.2.7")["proof_lane"], "full")
            self.assertEqual(plan(root, "workflow_dispatch", {"inputs": {"validation": "tests"}}, head, "refs/tags/v0.2.7")["proof_lane"], "full")
            self.assertEqual(plan(root, "pull_request", {"pull_request": {"base": {"sha": base}, "head": {"ref": "codex/release-v027"}}}, head, "refs/pull/1/merge")["proof_lane"], "full")
            with self.assertRaises(ValueError):
                plan(root, "workflow_dispatch", {"inputs": {"validation": "unknown"}}, head, "refs/heads/main")
            for name, payload, ref in [
                ("push", {"before": base}, "refs/tags/v0.2.6"),
                ("push", {"before": base, "forced": True}, "refs/heads/main"),
                ("push", {"before": "0" * 40}, "refs/heads/main"),
                ("pull_request", {"pull_request": {"base": {"sha": "b" * 40}}}, "refs/pull/1/merge"),
            ]:
                self.assertEqual(plan(root, name, payload, head, ref)["profile"], "full")
            with self.assertRaises(ValueError):
                plan(root, "pull_request", event, "a" * 40, "refs/pull/1/merge")
            (root / "src").mkdir()
            git("mv", "AGENTS.md", "src/new.rs")
            git("commit", "--quiet", "-am", "rename to code")
            changed = git("rev-parse", "HEAD")
            result = plan(root, "push", {"before": head}, changed, "refs/heads/main")
            self.assertEqual(result["profile"], "full")
            self.assertEqual(result["proof_lane"], "tests")
            self.assertEqual(result["paths"], ["AGENTS.md", "src/new.rs"])
            git("rm", "src/new.rs")
            git("commit", "--quiet", "-m", "delete code")
            self.assertEqual(plan(root, "push", {"before": changed}, git("rev-parse", "HEAD"), "refs/heads/main")["profile"], "full")
            base = git("rev-parse", "HEAD")
            (root / "AGENTS.md").symlink_to("missing-target")
            git("add", "AGENTS.md")
            git("commit", "--quiet", "-m", "symlink record")
            self.assertEqual(plan(root, "push", {"before": base}, git("rev-parse", "HEAD"), "refs/heads/main")["profile"], "full")


if __name__ == "__main__":
    unittest.main()
