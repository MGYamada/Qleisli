"""Adversarial routing and required-check regressions, with real Git diffs."""

import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
from ci_profiles import ROOT, SUITES, check_needs, classify, load_policy, plan


class CIProfiles(unittest.TestCase):
    def setUp(self):
        self.policy = load_policy(ROOT)

    def test_only_explicit_descriptive_documents_and_publication_records_are_light(self):
        for path in self.policy["documentation_only"] + [
            "docs/releases/v0.2.6.md", "tests/fixtures/releases/v0.2.5/publication.json",
            "tests/fixtures/ci_latency/measurements.json",
        ]:
            with self.subTest(path=path):
                self.assertEqual(classify([path], self.policy)[0], "docs")

    def test_normative_protected_executable_and_unknown_inputs_are_full(self):
        for path in [
            "TRUST_BOUNDARY.md", "CONSTITUTION.md", ".github/ci/protected-artifacts.json",
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
                     "docs/type-system.md", "CONSTITUTION.md", "tests/proof.lean"]
        broadened["documentation_only"] += protected
        for path in protected:
            self.assertEqual(classify([path], broadened)[0], "full")

    def needs(self, profile):
        return {
            "changes": {"result": "success", "outputs": {"profile": profile, "head": "a" * 40}},
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
            for name, payload, ref in [
                ("workflow_dispatch", event, "refs/heads/main"),
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
