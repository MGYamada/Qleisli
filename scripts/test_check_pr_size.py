"""Small synthetic counts and real Git histories exercise the PR-size policy."""

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
import check_pr_size as size
from ci_profiles import SUITES, check_needs


class NumstatPolicy(unittest.TestCase):
    def test_exact_threshold_sums_additions_and_deletions(self):
        for data in [b"999999\t0\ta\0", b"0\t999999\ta\0", b"500000\t499999\ta\0",
                     b"500000\t0\ta\0" + b"0\t499999\tb\0"]:
            with self.subTest(data=data):
                result = size.policy_result(size.parse_numstat(data))
                self.assertEqual(result["changed_lines"], 999_999)
                self.assertEqual(result["status"], "allowed")
        for data in [b"1000000\t0\ta\0", b"0\t1000000\ta\0", b"500001\t499999\ta\0",
                     b"500001\t0\ta\0" + b"0\t499999\tb\0",
                     b"1000001\t0\ta\0", b"0\t1000001\ta\0", b"1\t1000000\ta\0"]:
            with self.subTest(data=data):
                self.assertEqual(size.policy_result(size.parse_numstat(data))["status"], "forbidden")

    def test_binary_records_and_arbitrary_path_characters_are_separate(self):
        result = size.parse_numstat(b"-\t-\tbinary\0" + b"3\t2\ttab\tnewline\ninvalid-utf8-\xff\0")
        self.assertEqual(result, dict(additions=3, deletions=2, text_files=1,
                                      binary_files=1, changed_files=2, changed_lines=5))
        self.assertEqual(size.parse_numstat(b"")["changed_lines"], 0)

    def test_malformed_counts_and_rename_encoding_cannot_understate_size(self):
        for data in [None, "1\t2\ta\0", b"1\t2\ta", b"1\t2\ta\0\0", b"-\t0\ta\0",
                     b"0\t-\ta\0", b"+1\t0\ta\0", b"01\t0\ta\0", b"-1\t2\ta\0",
                     b"1.0\t0\ta\0", b"1\t\ta\0", b"1\t2\t\0", b"1\t2\0",
                     b"0\t0\t\0old\0new\0", b"1\t0\ta\0" * 2]:
            with self.subTest(data=data):
                with self.assertRaises(ValueError):
                    size.parse_numstat(data)

    def test_exception_is_only_the_exact_existing_repository_and_pr(self):
        for data in [b"1000000\t0\tx\0", b"1000001\t0\tx\0"]:
            counts = size.parse_numstat(data)
            self.assertEqual(size.policy_result(counts, "MGYamada/Qleisli", 307)["status"], "allowed")
            for repository, number in [(None, None), ("other/Qleisli", 307), ("MGYamada/Qleisli", 308),
                                       ("mgyamada/qleisli", 307), ("MGYamada/Qleisli", "307"),
                                       ("MGYamada/Qleisli", 307.0)]:
                with self.subTest(data=data, repository=repository, number=number):
                    self.assertEqual(size.policy_result(counts, repository, number)["status"], "forbidden")


class GitBoundPolicy(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.git("init", "--quiet")
        self.git("config", "user.email", "pr-size-fixture@example.invalid")
        self.git("config", "user.name", "PR-size fixture")
        self.git("config", "core.autocrlf", "false")
        (self.root / "old-name").write_text("one\ntwo\nthree\n")
        (self.root / "changed").write_text("old\n")
        self.git("add", ".")
        self.git("commit", "--quiet", "-m", "base")
        self.base = self.git("rev-parse", "HEAD")
        self.git("mv", "old-name", "renamed\tfile\nname")
        (self.root / "changed").write_text("new\nmore\n")
        (self.root / "binary").write_bytes(b"\0binary\n")
        self.git("add", ".")
        self.git("commit", "--quiet", "-m", "head")
        self.head = self.git("rev-parse", "HEAD")
        self.merge = self.git("commit-tree", self.git("rev-parse", f"{self.head}^{{tree}}"),
                              "-p", self.base, "-p", self.head, "-m", "event merge")
        self.git("checkout", "--quiet", "--detach", self.merge)
        self.event = {
            "repository": {"full_name": "MGYamada/Qleisli"}, "number": 308,
            "pull_request": {"number": 308,
                             "base": {"sha": self.base, "repo": {"full_name": "MGYamada/Qleisli"}},
                             "head": {"sha": self.head, "repo": {"full_name": "fork/Qleisli"}}},
        }

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root,
                                       stderr=subprocess.DEVNULL).decode().strip()

    def hosted(self, event=None, number=308, repository="MGYamada/Qleisli", expected=None, ref=None):
        return size.hosted_context(self.root, "pull_request", event or self.event,
                                   expected or self.merge, ref or f"refs/pull/{number}/merge", repository)

    def test_real_diff_counts_moves_twice_and_binary_separately(self):
        result = size.count_diff(self.root, self.base, self.head)
        self.assertEqual((result["additions"], result["deletions"], result["changed_lines"]), (5, 4, 9))
        self.assertEqual((result["text_files"], result["binary_files"]), (3, 1))
        self.assertEqual(result["merge_base"], self.base)
        self.assertEqual(self.hosted()["changed_lines"], 9)
        # Working-tree content never changes this immutable-commit count.
        (self.root / "changed").write_text("uncommitted\n" * 7)
        self.assertEqual(size.count_diff(self.root, self.base, self.head)["changed_lines"], 9)

    def test_merge_base_omits_changes_only_on_the_base_branch(self):
        self.git("checkout", "--quiet", "--detach", self.base)
        (self.root / "base-only").write_text("not a PR addition\n")
        self.git("add", ".")
        self.git("commit", "--quiet", "-m", "new base")
        new_base = self.git("rev-parse", "HEAD")
        result = size.count_diff(self.root, new_base, self.head)
        self.assertEqual(result["base"], new_base)
        self.assertEqual(result["merge_base"], self.base)
        self.assertEqual(result["changed_lines"], 9)

    def test_event_bound_exception_and_no_claimed_number_override(self):
        counts = dict(size.count_diff(self.root, self.base, self.head),
                      additions=1_000_001, deletions=0, changed_lines=1_000_001)
        with patch("check_pr_size.count_diff", return_value=counts):
            self.assertEqual(self.hosted()["status"], "forbidden")
            approved = copy.deepcopy(self.event)
            approved["number"] = approved["pull_request"]["number"] = 307
            self.assertEqual(self.hosted(approved, number=307)["status"], "allowed")
            forged = copy.deepcopy(self.event)
            forged["pull_request"]["number"] = 307
            with self.assertRaises(ValueError):
                self.hosted(forged)
            with self.assertRaises(ValueError):
                self.hosted(number=307)
            wrong_repo = copy.deepcopy(approved)
            wrong_repo["repository"]["full_name"] = "other/Qleisli"
            wrong_repo["pull_request"]["base"]["repo"]["full_name"] = "other/Qleisli"
            self.assertEqual(self.hosted(wrong_repo, number=307,
                                         repository="other/Qleisli")["status"], "forbidden")

    def test_missing_or_inconsistent_context_and_checkout_fail_closed(self):
        mutations = [
            lambda e: e.pop("pull_request"), lambda e: e.pop("number"),
            lambda e: e.update(number="308"), lambda e: e.update(number=True),
            lambda e: e["pull_request"].update(number=308.0),
            lambda e: e["repository"].update(full_name="other/Qleisli"),
            lambda e: e["pull_request"]["base"]["repo"].update(full_name="other/Qleisli"),
            lambda e: e["pull_request"]["base"].pop("sha"),
            lambda e: e["pull_request"]["head"].update(sha=self.base),
            lambda e: e["pull_request"]["base"].update(sha=self.head),
        ]
        for mutate in mutations:
            event = copy.deepcopy(self.event)
            mutate(event)
            with self.subTest(event=event):
                with self.assertRaises(ValueError):
                    self.hosted(event)
        for ref in ["", "refs/heads/codex/large", "refs/pull/308/head", "refs/pull/307/merge"]:
            with self.assertRaises(ValueError):
                size.hosted_context(self.root, "pull_request", self.event, self.merge, ref, "MGYamada/Qleisli")
        with self.assertRaises(ValueError):
            self.hosted(expected=self.head)
        self.git("checkout", "--quiet", "--detach", self.head)
        with self.assertRaises(ValueError):
            self.hosted(expected=self.head)

    def test_invalid_missing_and_shallow_commits_refuse_counts(self):
        for base, head in [("HEAD", self.head), (self.base[:12], self.head),
                           (self.base, "0" * 40), (self.base, "f" * 40)]:
            with self.subTest(base=base, head=head):
                with self.assertRaises((ValueError, subprocess.CalledProcessError)):
                    size.count_diff(self.root, base, head)
        with tempfile.TemporaryDirectory() as directory:
            shallow = Path(directory) / "shallow"
            subprocess.run(["git", "-c", "advice.detachedHead=false", "clone", "--quiet", "--depth=1",
                            self.root.as_uri(), str(shallow)], check=True)
            with self.assertRaisesRegex(ValueError, "shallow"):
                size.count_diff(shallow, self.head, self.head)
        with patch("check_pr_size.git", side_effect=[b"false\n", b".git/info/grafts\n", b"commit\n", self.base.encode(),
                                                    b"commit\n", self.head.encode(),
                                                    self.base.encode() + b"\n" + self.head.encode() + b"\n"]):
            with self.assertRaisesRegex(ValueError, "unique"):
                size.count_diff(self.root, self.base, self.head)

    def test_replacements_and_external_diff_settings_cannot_supply_counts(self):
        self.git("replace", self.head, self.base)
        self.git("config", "diff.external", "nonexistent-pr-size-diff-command")
        self.git("config", "diff.algorithm", "histogram")
        self.assertEqual(size.count_diff(self.root, self.base, self.head)["changed_lines"], 9)

    def test_local_grafts_fail_closed(self):
        (self.root / ".git/info/grafts").write_text(f"{self.head}\n")
        with self.assertRaisesRegex(ValueError, "grafts"):
            size.count_diff(self.root, self.base, self.head)

    def test_non_pr_skips_only_supported_bound_push_or_manual_events(self):
        event = {"repository": {"full_name": "MGYamada/Qleisli"}}
        for name in ["push", "workflow_dispatch"]:
            result = size.hosted_context(self.root, name, event, self.merge,
                                        "refs/heads/main", "MGYamada/Qleisli")
            self.assertEqual(result["status"], "not-applicable")
            with self.assertRaises(ValueError):
                size.hosted_context(self.root, name, self.event, self.merge,
                                    "refs/heads/main", "MGYamada/Qleisli")
        for name in ["", "pull_request_target", "unknown"]:
            with self.assertRaises(ValueError):
                size.hosted_context(self.root, name, event, self.merge,
                                    "refs/heads/main", "MGYamada/Qleisli")

    def test_cli_default_failure_reports_error_and_local_has_no_exception(self):
        with patch.dict(os.environ, {}, clear=True), patch("check_pr_size.ROOT", self.root), (
            patch("sys.stdout", new_callable=io.StringIO)
        ), patch("sys.stderr", new_callable=io.StringIO) as errors:
            report = self.root / "report.json"
            self.assertEqual(size.main(["--report", str(report)]), 1)
            self.assertEqual(json.loads(report.read_text())["status"], "error")
            self.assertIn("GITHUB_EVENT_PATH", errors.getvalue())
            self.assertEqual(size.main(["--base", self.base]), 1)
            counts = dict(size.count_diff(self.root, self.base, self.head),
                          additions=1_000_001, deletions=0, changed_lines=1_000_001)
            with patch("check_pr_size.count_diff", return_value=counts):
                self.assertEqual(size.main(["--base", self.base, "--head", self.head]), 1)
                os.environ.update(ALLOW_LARGE="true", QLEISLI_PR_SIZE_LIMIT="999999999", PR_NUMBER="307")
                self.assertEqual(size.main(["--base", self.base, "--head", self.head]), 1)
            with self.assertRaises(SystemExit) as failure:
                size.main(["--allow-large"])
            self.assertEqual(failure.exception.code, 2)
            os.environ["GITHUB_ACTIONS"] = "true"
            self.assertEqual(size.main(["--base", self.base, "--head", self.head]), 1)

    def test_cli_event_json_rejects_duplicate_fields_and_missing_report_destination(self):
        path = self.root / "event.json"
        context = dict(GITHUB_EVENT_PATH=str(path), GITHUB_EVENT_NAME="pull_request", GITHUB_SHA=self.merge,
                       GITHUB_REF="refs/pull/308/merge", GITHUB_REPOSITORY="MGYamada/Qleisli")
        with patch.dict(os.environ, context, clear=True), patch("check_pr_size.ROOT", self.root), (
            patch("sys.stdout", new_callable=io.StringIO)
        ), patch("sys.stderr", new_callable=io.StringIO):
            path.write_text('{"number":307,"number":308}')
            self.assertEqual(size.main([]), 1)
            path.write_text(json.dumps(self.event))
            self.assertEqual(size.main([]), 0)
            self.assertEqual(size.main(["--report", str(self.root / "absent/report.json")]), 1)

    def test_cli_malformed_event_objects_fail_closed(self):
        path = self.root / "malformed-event.json"
        context = dict(GITHUB_EVENT_PATH=str(path), GITHUB_EVENT_NAME="pull_request", GITHUB_SHA=self.merge,
                       GITHUB_REF="refs/pull/308/merge", GITHUB_REPOSITORY="MGYamada/Qleisli")
        malformed = [None, [], "PR307", {}, {"repository": []}, {"repository": None}]
        for field, value in [("pull_request", None), ("pull_request", []), ("number", False)]:
            event = copy.deepcopy(self.event)
            event[field] = value
            malformed.append(event)
        for field in ["base", "head"]:
            for value in [None, [], {}, {"sha": self.base, "repo": None}]:
                event = copy.deepcopy(self.event)
                event["pull_request"][field] = value
                malformed.append(event)
        with patch.dict(os.environ, context, clear=True), patch("check_pr_size.ROOT", self.root), (
            patch("sys.stdout", new_callable=io.StringIO)
        ), patch("sys.stderr", new_callable=io.StringIO):
            for event in malformed:
                path.write_text(json.dumps(event))
                with self.subTest(event=event):
                    self.assertEqual(size.main([]), 1)


class WorkflowBinding(unittest.TestCase):
    def test_gate_precedes_selection_and_existing_required_contexts_reject_changes_failure(self):
        workflow = (size.ROOT / ".github/workflows/ci.yml").read_text()
        changes = workflow.split("  changes:\n", 1)[1].split("  check-rust:\n", 1)[0]
        self.assertIn("fetch-depth: 0", changes)
        gate = changes.index('python3 scripts/check_pr_size.py --report "$RUNNER_TEMP/pr-size.json"')
        self.assertLess(gate, changes.index('--checks ci-preflight --output'))
        self.assertLess(gate, changes.index("python3 scripts/ci_profiles.py --report"))
        from ci_source_checks import plan
        self.assertIn(['python3', 'scripts/test_check_pr_size.py'], plan('ci-preflight'))
        self.assertNotIn("continue-on-error", changes)
        self.assertIn("${{ runner.temp }}/pr-size.json", changes)
        needs = {"changes": {"result": "failure", "outputs": {"profile": "full", "proof_lane": "full",
                                                               "head": "a" * 40}},
                 **{suite: {"result": "skipped"} for suite in SUITES}}
        with self.assertRaisesRegex(ValueError, "selection failed"):
            check_needs(needs, "a" * 40)


if __name__ == "__main__":
    unittest.main()

# Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
