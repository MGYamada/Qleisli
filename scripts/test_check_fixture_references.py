"""Small retention regressions, including orphan cycles and immutable Git reads.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

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
        self.assertTrue(check.glob_match("tests/fixtures/probe/nested/input.json",
                                         "tests/fixtures/**/*.json"))
        self.assertTrue(check.glob_match("tests/fixtures/input.json", "tests/fixtures/**/*.json"))

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


if __name__ == "__main__":
    unittest.main()
