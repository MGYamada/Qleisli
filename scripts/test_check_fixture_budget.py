"""Bounded synthetic and temporary-Git regressions for fixture size gates."""

from contextlib import nullcontext
import copy
import io
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
import check_fixture_budget as budget
from ci_profiles import SUITES, check_needs


POLICY = json.loads((budget.ROOT / budget.POLICY_PATH).read_bytes())


class BudgetPolicy(unittest.TestCase):
    def test_exact_inclusive_totals_and_added_line_caps(self):
        totals = dict(files=18_000, bytes=157_286_400)
        self.assertEqual(budget.enforce(POLICY, totals, dict(additions=100_000))["status"], "allowed")
        for totals, growth in [
            (dict(files=18_001, bytes=0), None),
            (dict(files=1, bytes=157_286_401), None),
            (dict(files=1, bytes=0), dict(additions=100_001)),
        ]:
            with self.subTest(totals=totals, growth=growth):
                self.assertEqual(budget.enforce(POLICY, totals, growth)["status"], "forbidden")

    def test_canonical_exception_waives_only_pr_growth_never_totals(self):
        totals = dict(files=1, bytes=1)
        growth = dict(additions=100_001)
        self.assertEqual(budget.enforce(POLICY, totals, growth, "MGYamada/Qleisli", 307)["status"], "allowed")
        for repository, number in [(None, None), ("other/Qleisli", 307), ("MGYamada/Qleisli", 308),
                                   ("mgyamada/qleisli", 307), ("MGYamada/Qleisli", "307"),
                                   ("MGYamada/Qleisli", 307.0)]:
            self.assertEqual(budget.enforce(POLICY, totals, growth, repository, number)["status"], "forbidden")
        for totals in [dict(files=18_001, bytes=0), dict(files=1, bytes=157_286_401)]:
            self.assertEqual(budget.enforce(POLICY, totals, growth, "MGYamada/Qleisli", 307)["status"], "forbidden")

    def test_policy_has_exact_schema_no_bool_or_raised_cap_or_extra_exception(self):
        self.assertEqual(budget.validate_policy(copy.deepcopy(POLICY)), POLICY)
        mutations = [
            lambda p: p.update(version=True), lambda p: p.update(version=2),
            lambda p: p.update(unknown=1), lambda p: p.pop("fixture_root"),
            lambda p: p.update(fixture_root="experimental"),
            lambda p: p["totals"].update(max_bytes=True),
            lambda p: p["totals"].update(max_bytes=157_286_401),
            lambda p: p["totals"].update(max_files=18_001),
            lambda p: p["totals"].update(max_files=0),
            lambda p: p["pull_request"].update(max_added_lines=100_001),
            lambda p: p["pull_request"].update(max_added_lines=-1),
            lambda p: p["pull_request"].update(max_added_lines=100_000.0),
            lambda p: p["pull_request"]["exception"].update(number=308),
            lambda p: p["pull_request"]["exception"].update(number=307.0),
            lambda p: p["pull_request"]["exception"].update(repository="other/Qleisli"),
            lambda p: p["pull_request"]["exception"].update(scope="all"),
        ]
        for mutate in mutations:
            value = copy.deepcopy(POLICY)
            mutate(value)
            with self.assertRaises(ValueError):
                budget.validate_policy(value)
        for value in [None, [], {}, True]:
            with self.assertRaises(ValueError):
                budget.validate_policy(value)

    def test_malformed_or_forged_counters_fail_closed(self):
        for totals in [dict(files=True, bytes=0), dict(files=-1, bytes=0), dict(files=0),
                       dict(files=0, bytes="1"), dict(files=0, bytes=1.0)]:
            with self.assertRaises(ValueError):
                budget.enforce(POLICY, totals)
        for value in [None, True, -1, "100", 1.0]:
            with self.assertRaises(ValueError):
                budget.enforce(POLICY, dict(files=0, bytes=0), dict(additions=value))

    def test_git_tree_counts_paths_and_binary_bytes_without_deduplication(self):
        oid = b"a" * 40
        data = (b"100644 blob " + oid + b" 11\ttests/fixtures/.hidden\0"
                + b"100755 blob " + oid + b" 11\ttests/fixtures/tab\tline\n\xff\0")
        totals, candidates = budget.parse_tree_sizes(data)
        self.assertEqual(totals, dict(files=2, bytes=22))
        self.assertEqual(candidates, set())
        _, candidates = budget.parse_tree_sizes(b"100644 blob " + oid + b" 130\ttests/fixtures/pointer\0")
        self.assertEqual(candidates, {"a" * 40})

    def test_tree_parser_rejects_symlinks_gitlinks_malformed_and_duplicate_records(self):
        valid = b"100644 blob " + b"a" * 40 + b" 1\ttests/fixtures/x\0"
        for data in [None, valid[:-1], valid + b"\0", valid * 2,
                     valid.replace(b"100644", b"120000"), valid.replace(b"100644", b"160000"),
                     valid.replace(b"blob", b"commit"), valid.replace(b" 1\t", b" -\t"),
                     valid.replace(b" 1\t", b" -1\t"), valid.replace(b"a" * 40, b"g" * 40),
                     valid.replace(b"tests/fixtures/x", b"tests/fixtures/../x"),
                     valid.replace(b"tests/fixtures/x", b"tests/other/x")]:
            with self.subTest(data=data):
                with self.assertRaises((ValueError, TypeError)):
                    budget.parse_tree_sizes(data)

    def test_growth_counts_additions_not_net_changes_and_accepts_nul_paths(self):
        data = b"100000\t900000\ttests/fixtures/tab\tline\n\xff\0-\t-\ttests/fixtures/binary\0"
        with patch("check_fixture_budget.git", return_value=data):
            growth = budget.fixture_growth(Path("."), "a" * 40, "b" * 40, "c" * 40)
        self.assertEqual((growth["additions"], growth["deletions"], growth["binary_files"]), (100_000, 900_000, 1))
        self.assertEqual(budget.enforce(POLICY, dict(files=1, bytes=1), growth)["status"], "allowed")
        for data in [b"1\t0\tother/x\0", b"1\t0\ttests/fixtures/../x\0", b"1\t0\t\0old\0new\0"]:
            with patch("check_fixture_budget.git", return_value=data):
                with self.assertRaises(ValueError):
                    budget.fixture_growth(Path("."), "a" * 40, "b" * 40, "c" * 40)


class GitFixtureBudget(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.fixtures = self.root / budget.FIXTURE_ROOT
        (self.fixtures / "nested").mkdir(parents=True)
        (self.root / budget.POLICY_PATH).parent.mkdir(parents=True)
        (self.root / budget.POLICY_PATH).write_text(json.dumps(POLICY))
        (self.root / ".gitignore").write_text("tests/fixtures/ignored/**\n")
        (self.fixtures / "a.txt").write_bytes(b"a\n")
        (self.fixtures / "duplicate.txt").write_bytes(b"a\n")
        (self.fixtures / ".hidden").write_bytes(b"h")
        (self.fixtures / "nested/tab\tline\nname").write_bytes(b"n\n")
        self.git("init", "--quiet")
        self.git("config", "user.email", "fixture-budget@example.invalid")
        self.git("config", "user.name", "Fixture budget")
        self.git("config", "core.autocrlf", "false")
        self.git("add", ".")
        self.git("commit", "--quiet", "-m", "initial")
        self.ancestor = self.git("rev-parse", "HEAD")
        (self.fixtures / "a.txt").write_bytes(b"a\nnew\n")
        self.git("mv", "tests/fixtures/duplicate.txt", "tests/fixtures/moved.txt")
        self.git("commit", "--quiet", "-am", "head")
        self.head = self.git("rev-parse", "HEAD")
        self.git("checkout", "--quiet", "--detach", self.ancestor)
        (self.fixtures / "base-only.txt").write_bytes(b"base\n")
        self.git("add", ".")
        self.git("commit", "--quiet", "-m", "base branch")
        self.base = self.git("rev-parse", "HEAD")
        self.git("merge", "--quiet", "--no-ff", "-m", "hosted merge", self.head)
        self.merge = self.git("rev-parse", "HEAD")
        self.event = {
            "repository": {"full_name": "MGYamada/Qleisli"}, "number": 308,
            "pull_request": {"number": 308,
                             "base": {"sha": self.base, "repo": {"full_name": "MGYamada/Qleisli"}},
                             "head": {"sha": self.head, "repo": {"full_name": "fork/Qleisli"}}},
        }

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root,
                                       stderr=subprocess.DEVNULL).decode().strip()

    def context(self, event_name="pull_request", event=None):
        path = self.root / "event.json"
        path.write_text(json.dumps(self.event if event is None else event))
        return dict(GITHUB_ACTIONS="true", GITHUB_EVENT_NAME=event_name,
                    GITHUB_EVENT_PATH=str(path), GITHUB_SHA=self.merge,
                    GITHUB_REF="refs/pull/308/merge" if event_name == "pull_request" else "refs/heads/main",
                    GITHUB_REPOSITORY="MGYamada/Qleisli")

    def run_main(self, argv, environment=None):
        with patch.dict(os.environ, environment or {}, clear=True), patch("check_fixture_budget.ROOT", self.root), (
            patch("sys.stdout", new_callable=io.StringIO)
        ) as out, patch("sys.stderr", new_callable=io.StringIO) as err:
            code = budget.main(argv)
        data = out.getvalue() if code == 0 else err.getvalue()
        return code, json.loads(data)

    def test_immutable_checkout_totals_differ_from_head_and_growth_uses_merge_base(self):
        head = budget.committed_totals(self.root, self.head)
        merge = budget.committed_totals(self.root, self.merge)
        self.assertEqual((head["files"], head["bytes"]), (4, 11))
        self.assertEqual((merge["files"], merge["bytes"]), (5, 16))
        growth = budget.fixture_growth(self.root, self.base, self.head, self.ancestor)
        self.assertEqual((growth["additions"], growth["deletions"]), (2, 1))
        code, result = self.run_main(["--hosted"], self.context())
        self.assertEqual(code, 0)
        self.assertEqual(result["totals"]["commit"], self.merge)
        self.assertEqual(result["growth"]["head"], self.head)
        self.assertEqual(result["growth"]["merge_base"], self.ancestor)

    def test_local_includes_ignored_untracked_hidden_and_hardlinked_paths(self):
        ignored = self.fixtures / "ignored"
        ignored.mkdir()
        (ignored / "new-large.txt").write_bytes(b"xxxx")
        (self.fixtures / ".DS_Store").write_bytes(b"y")
        os.link(self.fixtures / "a.txt", self.fixtures / "hardlink.txt")
        self.assertEqual(self.git("check-ignore", "tests/fixtures/ignored/new-large.txt"),
                         "tests/fixtures/ignored/new-large.txt")
        totals = budget.working_totals(self.root)
        self.assertEqual((totals["files"], totals["bytes"]), (8, 27))
        small = copy.deepcopy(POLICY)
        small["totals"]["max_bytes"] = 26
        (self.root / budget.POLICY_PATH).write_text(json.dumps(small))
        code, result = self.run_main([])
        self.assertEqual((code, result["status"]), (1, "forbidden"))

    def test_missing_and_staged_deleted_tracked_fixture_fail_until_commit(self):
        (self.fixtures / "a.txt").unlink()
        with self.assertRaisesRegex(ValueError, "tracked fixture missing"):
            budget.working_totals(self.root)
        self.git("rm", "--quiet", "tests/fixtures/a.txt")
        with self.assertRaisesRegex(ValueError, "tracked fixture missing"):
            budget.working_totals(self.root)
        self.git("commit", "--quiet", "-m", "reviewed deletion")
        self.assertEqual(budget.working_totals(self.root)["files"], 4)

    def test_local_root_nested_and_ancestor_symlinks_are_not_followed(self):
        nested = self.fixtures / "shortcut"
        nested.symlink_to(self.fixtures / "nested", target_is_directory=True)
        with self.assertRaises(ValueError):
            budget.working_totals(self.root)
        nested.unlink()
        saved = self.root / "saved-fixtures"
        self.fixtures.rename(saved)
        self.fixtures.symlink_to(saved, target_is_directory=True)
        with self.assertRaises(OSError):
            budget.working_totals(self.root)
        self.fixtures.unlink()
        saved.rename(self.fixtures)
        saved_tests = self.root / "saved-tests"
        (self.root / "tests").rename(saved_tests)
        (self.root / "tests").symlink_to(saved_tests, target_is_directory=True)
        with self.assertRaises(OSError):
            budget.working_totals(self.root)

    def test_special_fifo_and_regular_to_fifo_race_fail_without_blocking(self):
        path = self.fixtures / "racefifo"
        os.mkfifo(path)
        with self.assertRaises(ValueError):
            budget.working_totals(self.root)
        actual = path.lstat()
        fake = SimpleNamespace(name="racefifo", stat=lambda **kwargs: SimpleNamespace(
            st_mode=stat.S_IFREG | 0o644, st_dev=actual.st_dev, st_ino=actual.st_ino, st_size=1))
        original = os.open

        def checked_open(name, flags, **kwargs):
            if name == "racefifo":
                self.assertTrue(flags & os.O_NONBLOCK)
            return original(name, flags, **kwargs)

        with patch("check_fixture_budget.os.scandir", return_value=nullcontext([fake])), (
            patch("check_fixture_budget.os.open", new=checked_open)
        ), patch("check_fixture_budget.os.supports_dir_fd", os.supports_dir_fd | {checked_open}):
            with self.assertRaisesRegex(ValueError, "file changed"):
                budget.working_totals(self.root)

    def test_unreadable_file_fails_closed(self):
        original = os.open

        def deny(name, flags, **kwargs):
            if name == "a.txt":
                raise PermissionError("unreadable fixture")
            return original(name, flags, **kwargs)

        with patch("check_fixture_budget.os.open", new=deny), (
            patch("check_fixture_budget.os.supports_dir_fd", os.supports_dir_fd | {deny})
        ):
            with self.assertRaises(PermissionError):
                budget.working_totals(self.root)

    def test_committed_symlink_submodule_and_root_ancestor_are_rejected(self):
        (self.fixtures / "link").symlink_to(self.fixtures / "a.txt")
        self.git("add", ".")
        self.git("commit", "--quiet", "-m", "symlink")
        with self.assertRaises(ValueError):
            budget.committed_totals(self.root, self.git("rev-parse", "HEAD"))
        self.git("checkout", "--quiet", "--detach", self.merge)
        self.git("update-index", "--add", "--cacheinfo", "160000", self.head, "tests/fixtures/vendor")
        self.git("commit", "--quiet", "-m", "gitlink")
        with self.assertRaises(ValueError):
            budget.committed_totals(self.root, self.git("rev-parse", "HEAD"))
        self.git("checkout", "--quiet", "--detach", self.merge)
        self.git("rm", "-r", "--quiet", "tests")
        (self.root / "tests").symlink_to(self.root / "elsewhere", target_is_directory=True)
        self.git("add", "tests")
        self.git("commit", "--quiet", "-m", "ancestor symlink")
        with self.assertRaisesRegex(ValueError, "ancestry"):
            budget.committed_totals(self.root, self.git("rev-parse", "HEAD"))

    def test_lfs_pointer_is_refused_without_fetching_external_payload(self):
        pointer = LFS = (budget.LFS_PREFIX + b"\noid sha256:" + b"f" * 64 + b"\nsize 999999999\n")
        self.assertLess(len(LFS), 1024)
        (self.fixtures / "pointer.bin").write_bytes(pointer)
        with self.assertRaisesRegex(ValueError, "LFS"):
            budget.working_totals(self.root)
        self.git("add", ".")
        self.git("commit", "--quiet", "-m", "unsupported pointer")
        with self.assertRaisesRegex(ValueError, "LFS"):
            budget.committed_totals(self.root, self.git("rev-parse", "HEAD"))

    def test_shallow_missing_or_unbound_commit_and_policy_fail_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            shallow = Path(directory) / "shallow"
            subprocess.run(["git", "-c", "advice.detachedHead=false", "clone", "--quiet", "--depth=1",
                            self.root.as_uri(), str(shallow)], check=True)
            with self.assertRaisesRegex(ValueError, "complete history"):
                budget.committed_totals(shallow, self.merge)
        for commit in ["HEAD", "f" * 40]:
            with self.assertRaises((ValueError, subprocess.CalledProcessError)):
                budget.committed_totals(self.root, commit)
        (self.root / budget.POLICY_PATH).write_text('{"version":1,"version":1}')
        with self.assertRaises(ValueError):
            budget.load_policy(self.root)
        with self.assertRaises(ValueError):
            budget.load_policy(self.root, self.merge)

    def test_hosted_growth_exception_is_event_bound_and_totals_never_waived(self):
        actual = budget.fixture_growth(self.root, self.base, self.head, self.ancestor)
        oversized = dict(actual, additions=100_001)
        with patch("check_fixture_budget.fixture_growth", return_value=oversized):
            code, result = self.run_main(["--hosted"], self.context())
            self.assertEqual((code, result["status"]), (1, "forbidden"))
            approved = copy.deepcopy(self.event)
            approved["number"] = approved["pull_request"]["number"] = 307
            environment = self.context(event=approved)
            environment["GITHUB_REF"] = "refs/pull/307/merge"
            self.assertEqual(self.run_main(["--hosted"], environment)[0], 0)
            environment["GITHUB_REF"] = "refs/pull/308/merge"
            self.assertEqual(self.run_main(["--hosted"], environment)[1]["status"], "error")
            environment["GITHUB_REF"] = "refs/pull/307/merge"
            with patch("check_fixture_budget.committed_totals", return_value=dict(files=18_001, bytes=0)):
                self.assertEqual(self.run_main(["--hosted"], environment)[0], 1)
        self.assertEqual(self.run_main(["--base", self.base, "--head", self.head], self.context())[0], 1)
        with patch("check_fixture_budget.fixture_growth", return_value=oversized):
            self.assertEqual(self.run_main(["--base", self.base, "--head", self.head])[0], 1)

    def test_push_manual_and_local_modes_check_totals_and_never_skip_bad_context(self):
        for name in ["push", "workflow_dispatch"]:
            environment = self.context(name, {"repository": {"full_name": "MGYamada/Qleisli"}})
            code, result = self.run_main(["--hosted"], environment)
            self.assertEqual(code, 0)
            self.assertIsNone(result["growth"])
            with patch("check_fixture_budget.committed_totals", return_value=dict(files=0, bytes=157_286_401)):
                self.assertEqual(self.run_main(["--hosted"], environment)[0], 1)
        self.assertEqual(self.run_main(["--hosted"])[1]["status"], "error")
        self.assertEqual(self.run_main(["--base", self.base])[0], 1)
        self.assertEqual(self.run_main([])[0], 0)
        self.assertEqual(self.run_main(["--base", self.base, "--head", self.head])[0], 0)
        environment = self.context()
        environment["GITHUB_SHA"] = self.head
        self.assertEqual(self.run_main(["--hosted"], environment)[1]["status"], "error")

    def test_report_cannot_add_files_inside_the_counted_tree_or_mask_write_failure(self):
        inside = self.fixtures / "budget-report.json"
        code, result = self.run_main(["--report", str(inside)])
        self.assertEqual((code, result["status"]), (1, "error"))
        self.assertFalse(inside.exists())
        alias = self.root / "alias"
        alias.symlink_to(self.fixtures, target_is_directory=True)
        self.assertEqual(self.run_main(["--report", str(alias / "new/report.json")])[0], 1)
        outside = self.root / "report.json"
        code, result = self.run_main(["--report", str(outside)])
        self.assertEqual(code, 0)
        self.assertEqual(json.loads(outside.read_text()), result)
        with patch.dict(os.environ, {}, clear=True), patch("check_fixture_budget.ROOT", self.root), (
            patch("sys.stdout", new_callable=io.StringIO)
        ), patch("sys.stderr", new_callable=io.StringIO) as errors:
            self.assertEqual(budget.main(["--report", str(self.root / "absent/report.json")]), 1)
            self.assertIn("report failed", errors.getvalue())

    def test_existing_report_hardlink_cannot_overwrite_a_counted_fixture(self):
        fixture = self.fixtures / "a.txt"
        original = fixture.read_bytes()
        outside = self.root / "report.json"
        os.link(fixture, outside)
        with patch.dict(os.environ, {}, clear=True), patch("check_fixture_budget.ROOT", self.root), (
            patch("sys.stdout", new_callable=io.StringIO)
        ), patch("sys.stderr", new_callable=io.StringIO) as errors:
            self.assertEqual(budget.main(["--report", str(outside)]), 1)
            self.assertIn("report failed", errors.getvalue())
        self.assertEqual(fixture.read_bytes(), original)
        self.assertEqual(outside.read_bytes(), original)


class WorkflowBudget(unittest.TestCase):
    def test_fixture_gate_runs_before_selection_and_changes_failure_reaches_required_contexts(self):
        workflow = (budget.ROOT / ".github/workflows/ci.yml").read_text()
        changes = workflow.split("  changes:\n", 1)[1].split("  check-rust:\n", 1)[0]
        gate = changes.index('python3 scripts/check_fixture_budget.py --hosted --report "$RUNNER_TEMP/fixture-budget.json"')
        self.assertLess(gate, changes.index("python3 scripts/ci_profiles.py --report"))
        self.assertIn("python3 scripts/test_check_fixture_budget.py", changes)
        self.assertIn("${{ runner.temp }}/fixture-budget.json", changes)
        self.assertNotIn("continue-on-error", changes)
        needs = {"changes": {"result": "failure", "outputs": {"profile": "full", "proof_lane": "full",
                                                               "head": "a" * 40}},
                 **{suite: {"result": "skipped"} for suite in SUITES}}
        with self.assertRaises(ValueError):
            check_needs(needs, "a" * 40)


if __name__ == "__main__":
    unittest.main()

# Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
