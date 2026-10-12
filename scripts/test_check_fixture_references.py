"""Small retention regressions, including orphan cycles and immutable Git reads.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import json
import contextlib
import io
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_fixture_references as check


class ReferenceGraph(unittest.TestCase):
    def missing(self, contents, fixtures):
        paths = set(contents) | set(fixtures)
        return set(fixtures) - check.reachability(contents, paths)

    def test_real_test_literal_retains_input_but_not_unrelated_neighbor(self):
        source = 'include_str!("fixtures/probe/input.qirf")'
        fixtures = {"tests/fixtures/probe/input.qirf", "tests/fixtures/probe/orphan.txt"}
        self.assertEqual(self.missing({"tests/probe.rs": source}, fixtures),
                         {"tests/fixtures/probe/orphan.txt"})

    def test_source_project_directory_does_not_admit_extra_log(self):
        contents = {"tests/probe.rs": 'check_project("tests/fixtures/probe/project")'}
        files = {"tests/fixtures/probe/project/main.qli",
                 "tests/fixtures/probe/project/Qargo.toml",
                 "tests/fixtures/probe/project/unrelated.log"}
        self.assertEqual(self.missing(contents, files), {"tests/fixtures/probe/project/unrelated.log"})

    def test_fixture_root_inventory_is_not_a_blanket_reference(self):
        contents = {"scripts/count.py": 'ROOT = "tests/fixtures"; pattern = "*"'}
        self.assertEqual(self.missing(contents, {"tests/fixtures/probe/orphan.json"}),
                         {"tests/fixtures/probe/orphan.json"})

    def test_single_component_glob_cannot_admit_nested_neighbor(self):
        contents = {"scripts/read.py": 'load("tests/fixtures/probe/{case}.json")'}
        files = {"tests/fixtures/probe/input.json", "tests/fixtures/probe/nested/orphan.json"}
        self.assertEqual(self.missing(contents, files), {"tests/fixtures/probe/nested/orphan.json"})
        self.assertTrue(check.glob_match("probe/nested/input.json", "probe/**/*.json"))
        self.assertTrue(check.glob_match("probe/input.json", "probe/**/*.json"))

    def test_inspector_and_its_synthetic_graph_tests_cannot_grant_references(self):
        path = "tests/fixtures/probe/orphan.json"
        for name in ["scripts/check_fixture_references.py", "scripts/test_check_fixture_references.py"]:
            self.assertEqual(self.missing({name: f'synthetic_path = "{path}"'}, {path}), {path})

    def test_reachable_manifest_retains_relative_member_transitively(self):
        manifest = "tests/fixtures/probe/packet.json"
        contents = {"scripts/inspect.py": f'load("{manifest}")',
                    manifest: json.dumps({"next": "nested/index.json"}),
                    "tests/fixtures/probe/nested/index.json": json.dumps({"file": "input.bin"})}
        files = {manifest, "tests/fixtures/probe/nested/index.json", "tests/fixtures/probe/nested/input.bin"}
        self.assertFalse(self.missing(contents, files))

    def test_unrooted_manifest_cycle_and_self_declared_approval_reject(self):
        a, b = "tests/fixtures/probe/a.json", "tests/fixtures/probe/b.json"
        contents = {a: json.dumps({"file": "b.json", "reviewed_by_human": True}),
                    b: json.dumps({"file": "a.json", "input": "unused.bin"})}
        self.assertEqual(self.missing(contents, {a, b, "tests/fixtures/probe/unused.bin"}),
                         {a, b, "tests/fixtures/probe/unused.bin"})

    def test_rooted_manifest_cannot_retain_escaping_path(self):
        manifest = "tests/fixtures/probe/index.json"
        contents = {"scripts/read.py": f'load("{manifest}")',
                    manifest: json.dumps({"file": "../other/unused.bin"})}
        self.assertEqual(self.missing(contents, {manifest, "tests/fixtures/other/unused.bin"}),
                         {"tests/fixtures/other/unused.bin"})

    def test_archive_inventory_does_not_admit_unlisted_current_source(self):
        manifest = "tests/fixtures/probe/history.archive.json"
        contents = {"scripts/check_fixture_archives.py": 'inspect_archives()',
                    manifest: json.dumps({"prefix": "tests/fixtures/probe/old",
                                          "archive": "tests/fixtures/probe/history.tar.gz",
                                          "entries": {"tests/fixtures/probe/old/removed.txt": {}}})}
        files = {manifest, "tests/fixtures/probe/history.tar.gz", "tests/fixtures/probe/old/unlisted.qli"}
        self.assertEqual(self.missing(contents, files), {"tests/fixtures/probe/old/unlisted.qli"})

    def test_authoring_session_retains_attempt_and_diagnostic_without_execution(self):
        session = "tests/fixtures/authoring_sessions/probe/session.json"
        contents = {"scripts/check_authoring_sessions.py": 'inspect_sessions()',
                    session: json.dumps({"context": "context.json", "attempts": [
                        {"id": "attempt-01", "sha256": {"main.qli": "hash"},
                         "observations": ["first.json"]}]}),
                    "tests/fixtures/authoring_sessions/probe/first.json":
                        json.dumps({"command": ["never-run-this"]})}
        files = {session, "tests/fixtures/authoring_sessions/probe/context.json",
                 "tests/fixtures/authoring_sessions/probe/attempt-01/main.qli",
                 "tests/fixtures/authoring_sessions/probe/attempt-01/Qargo.toml",
                 "tests/fixtures/authoring_sessions/probe/first.json"}
        self.assertFalse(self.missing(contents, files))

    def test_duplicate_json_cannot_grant_transitive_references(self):
        manifest = "tests/fixtures/probe/index.json"
        contents = {"scripts/read.py": f'load("{manifest}")',
                    manifest: '{"file":"first.bin","file":"second.bin"}'}
        files = {manifest, "tests/fixtures/probe/first.bin", "tests/fixtures/probe/second.bin"}
        self.assertEqual(self.missing(contents, files), files - {manifest})


class GitInspection(unittest.TestCase):
    def test_hosted_reference_gate_precedes_validation_selection(self):
        workflow = (check.ROOT / ".github/workflows/ci.yml").read_text()
        changes = workflow.split("  changes:\n")[1].split("  check-rust:\n")[0]
        self.assertLess(changes.index("scripts/check_fixture_references.py --hosted"),
                        changes.index("id: select"))
        from ci_source_checks import plan
        self.assertIn(["python3", "scripts/test_check_fixture_references.py"], plan("ci-preflight"))

    def test_exact_commit_rejects_orphan_and_ignores_later_working_claim(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def git(*args):
                return subprocess.check_output(["git", *args], cwd=root, stderr=subprocess.DEVNULL).decode().strip()
            git("init", "--quiet")
            git("config", "user.name", "Fixture test")
            git("config", "user.email", "fixture@example.invalid")
            (root / "scripts").mkdir()
            consumer = root / "scripts/read.py"
            consumer.write_text("# No fixture consumed yet.\n")
            git("add", "."); git("commit", "--quiet", "-m", "baseline")
            base = git("rev-parse", "HEAD")
            fixture = root / "tests/fixtures/probe/input.bin"
            fixture.parent.mkdir(parents=True)
            fixture.write_bytes(b"small\0input")
            git("add", "."); git("commit", "--quiet", "-m", "orphan")
            orphan = git("rev-parse", "HEAD")
            consumer.write_text('read("tests/fixtures/probe/input.bin")\n')
            refused = check.inspect(root, base, orphan)
            self.assertEqual(refused["unreferenced"], ["tests/fixtures/probe/input.bin"])
            git("add", "."); git("commit", "--quiet", "-m", "actual reference")
            accepted = check.inspect(root, base, git("rev-parse", "HEAD"))
            self.assertEqual(accepted["status"], "allowed")
            self.assertEqual(accepted["new_fixtures"], 1)
            self.assertEqual(check.inspect(root, base, base)["new_fixtures"], 0)

    def test_reintroduced_historical_orphan_is_a_new_event_addition(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def git(*args):
                return subprocess.check_output(["git", *args], cwd=root, stderr=subprocess.DEVNULL).decode().strip()
            git("init", "--quiet")
            git("config", "user.name", "Fixture test")
            git("config", "user.email", "fixture@example.invalid")
            fixture = root / "tests/fixtures/probe/old.log"
            fixture.parent.mkdir(parents=True)
            fixture.write_text("historical log")
            git("add", "."); git("commit", "--quiet", "-m", "historical baseline")
            base = git("rev-parse", "HEAD")
            fixture.unlink()
            git("add", "."); git("commit", "--quiet", "-m", "removed history")
            previous = git("rev-parse", "HEAD")
            fixture.write_text("historical log")
            git("add", "."); git("commit", "--quiet", "-m", "unreferenced reintroduction")
            result = check.inspect(root, base, git("rev-parse", "HEAD"), previous)
            self.assertEqual(result["unreferenced"], ["tests/fixtures/probe/old.log"])
            self.assertEqual(result["change_base"], previous)

    def test_new_branch_and_tag_check_reintroductions_before_the_head_parent(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def git(*args):
                return subprocess.check_output(["git", *args], cwd=root,
                                               stderr=subprocess.DEVNULL).decode().strip()
            git("init", "--quiet")
            git("config", "user.name", "Fixture test")
            git("config", "user.email", "fixture@example.invalid")
            fixture = root / "tests/fixtures/probe/old.log"
            fixture.parent.mkdir(parents=True)
            fixture.write_text("historical log")
            git("add", "."); git("commit", "--quiet", "-m", "reviewed baseline")
            base = git("rev-parse", "HEAD")
            fixture.unlink()
            git("add", "."); git("commit", "--quiet", "-m", "removed history")
            fixture.write_text("historical log")
            git("add", "."); git("commit", "--quiet", "-m", "reintroduced orphan")
            (root / "unrelated.txt").write_text("new head is not the reintroduction")
            git("add", "."); git("commit", "--quiet", "-m", "later unrelated commit")
            head = git("rev-parse", "HEAD")
            event = root / "event.json"
            event.write_text(json.dumps({"before": "0" * 40,
                                         "repository": {"full_name": "owner/repo"}}))
            for ref in ("refs/heads/new-branch", "refs/tags/v-test"):
                with self.subTest(ref=ref):
                    environment = dict(GITHUB_ACTIONS="true", GITHUB_EVENT_PATH=str(event),
                                       GITHUB_EVENT_NAME="push", GITHUB_SHA=head,
                                       GITHUB_REF=ref, GITHUB_REPOSITORY="owner/repo")
                    output = io.StringIO()
                    with (patch.object(check, "ROOT", root), patch.object(check, "BASELINE", base),
                          patch.dict(os.environ, environment), contextlib.redirect_stdout(output)):
                        self.assertEqual(check.main(["--hosted"]), 1)
                    report = json.loads(output.getvalue())
                    self.assertEqual(report["status"], "forbidden")
                    self.assertEqual(report["unreferenced"], ["tests/fixtures/probe/old.log"])
            # A real committed consumer repairs the defect on the same history.
            (root / "scripts").mkdir()
            (root / "scripts/read.py").write_text('read("tests/fixtures/probe/old.log")\n')
            git("add", "."); git("commit", "--quiet", "-m", "retained consumer")
            self.assertEqual(check.inspect(root, base, git("rev-parse", "HEAD"))["status"], "allowed")

    def test_merge_does_not_reclassify_unchanged_baseline_files_as_additions(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def git(*args):
                return subprocess.check_output(["git", *args], cwd=root,
                                               stderr=subprocess.DEVNULL).decode().strip()
            git("init", "--quiet")
            git("config", "user.name", "Fixture test")
            git("config", "user.email", "fixture@example.invalid")
            (root / "initial.txt").write_text("initial")
            git("add", "."); git("commit", "--quiet", "-m", "initial")
            main = git("branch", "--show-current")
            git("checkout", "--quiet", "-b", "side")
            (root / "side.txt").write_text("unrelated side change")
            git("add", "."); git("commit", "--quiet", "-m", "side")
            git("checkout", "--quiet", main)
            fixture = root / "tests/fixtures/probe/old.log"
            fixture.parent.mkdir(parents=True)
            fixture.write_text("reviewed historical record")
            git("add", "."); git("commit", "--quiet", "-m", "reviewed baseline")
            base = git("rev-parse", "HEAD")
            # The reviewed base is reached through the second merge parent.
            git("checkout", "--quiet", "side")
            git("merge", "--quiet", "--no-ff", main, "-m", "integrate reviewed main")
            report = check.inspect(root, base, git("rev-parse", "HEAD"))
            self.assertEqual(report["status"], "allowed")
            self.assertEqual(report["new_fixtures"], 0)


if __name__ == "__main__":
    unittest.main()
