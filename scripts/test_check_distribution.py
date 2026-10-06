#!/usr/bin/env python3
"""Adversarial checks for release artifact identity and safe extraction.

These tests create local throwaway Git repositories; they do not run Cargo.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import check_distribution

from check_distribution import (
    DistributionError, File, check_package, clean_candidate, compare_files, compare_package_metadata,
    digest, extract_checked, license_inventory, read_archive, tracked_files, validate,
    SOURCE_ROOTS, check_source_roots,
)
from check_installation import check_registry_links


class CommandDiagnosticsTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.report = {"commands": []}
        self.commands = check_distribution.Commands(self.root, self.report)

    def invoke(self, stdout, stderr, exit_code=101, **kwargs):
        def child(argv, **options):
            options["stdout"].write(stdout)
            options["stderr"].write(stderr)
            return subprocess.CompletedProcess(argv, exit_code)

        console = io.StringIO()
        with patch.object(check_distribution.subprocess, "run", child), \
                patch.object(sys, "stderr", console):
            if exit_code:
                with self.assertRaises(DistributionError) as raised:
                    self.commands.run(["synthetic", "test"], self.root, **kwargs)
                result = raised.exception
            else:
                result = self.commands.run(["synthetic", "test"], self.root, **kwargs)
        return result, console.getvalue()

    def test_failure_previews_both_streams_and_retains_exact_bytes_and_exit_code(self):
        stdout, stderr = b"test panic details\n\xff", b"Cargo failed\n"
        error, console = self.invoke(stdout, stderr)
        self.assertIn("stdout preview:", console)
        self.assertIn("stderr preview:", console)
        self.assertIn("test panic details\n\ufffd", console)
        self.assertIn("Cargo failed", console)
        record = self.report["commands"][0]
        self.assertEqual(record["exit_code"], 101)
        self.assertEqual(Path(record["stdout"]).read_bytes(), stdout)
        self.assertEqual(Path(record["stderr"]).read_bytes(), stderr)
        self.assertEqual(str(error),
                         f"command failed (101): ['synthetic', 'test']; see {record['stderr']}")

    def test_large_logs_read_bounded_tails_and_disclose_truncation(self):
        stdout = b"omitted stdout prefix" + b"x" * 8192 + b"stdout panic tail"
        stderr = b"omitted stderr prefix" + b"y" * 8192 + b"stderr error tail"
        reads = []
        real_open = Path.open

        class PreviewReader(io.BytesIO):
            def read(self, size=-1):
                reads.append(size)
                return super().read(size)

        def open_path(path, mode="r", *args, **kwargs):
            if mode == "rb":
                return PreviewReader(stdout if path.suffix == ".stdout" else stderr)
            return real_open(path, mode, *args, **kwargs)

        with patch.object(Path, "open", open_path):
            _, console = self.invoke(stdout, stderr)
        self.assertEqual(reads, [8192, 8192])
        self.assertEqual(console.count("truncated to last 8192"), 2)
        self.assertNotIn("omitted stdout prefix", console)
        self.assertNotIn("omitted stderr prefix", console)
        self.assertIn("stdout panic tail", console)
        self.assertIn("stderr error tail", console)
        self.assertEqual((self.root / "logs/00.stdout").read_bytes(), stdout)
        self.assertEqual((self.root / "logs/00.stderr").read_bytes(), stderr)

    def test_success_is_silent_and_returns_exact_stdout_bytes(self):
        stdout = b"success\n\x00\xff"
        returned, console = self.invoke(stdout, b"successful warning\n", exit_code=0)
        self.assertEqual(returned, stdout)
        self.assertEqual(console, "")
        self.assertEqual(self.report["commands"][0]["exit_code"], 0)

    def test_binary_stdout_artifact_is_retained_without_a_console_dump(self):
        archive = self.root / "source.tar"
        payload = b"binary archive payload\x00\xff"
        _, console = self.invoke(payload, b"archive command failed", stdout_path=archive)
        self.assertIn(f"stdout retained as binary artifact: {archive}; preview omitted", console)
        self.assertNotIn("binary archive payload", console)
        self.assertIn("archive command failed", console)
        self.assertEqual(archive.read_bytes(), payload)
        self.assertEqual(self.report["commands"][0]["stdout"], str(archive))

    def test_unreadable_preview_preserves_child_error_and_previews_other_stream(self):
        real_open = Path.open

        def open_path(path, mode="r", *args, **kwargs):
            if mode == "rb" and path.suffix == ".stdout":
                raise OSError("synthetic preview read failure")
            return real_open(path, mode, *args, **kwargs)

        with patch.object(Path, "open", open_path):
            error, console = self.invoke(b"retained stdout", b"remaining stderr")
        self.assertIn("stdout preview unavailable:", console)
        self.assertIn("synthetic preview read failure", console)
        self.assertIn("remaining stderr", console)
        self.assertIn("command failed (101)", str(error))
        self.assertEqual((self.root / "logs/00.stdout").read_bytes(), b"retained stdout")

    def test_console_write_failure_does_not_mask_child_error(self):
        class BrokenConsole(io.StringIO):
            def write(self, text):
                raise BrokenPipeError("synthetic console failure")

        with patch.object(check_distribution, "sys"), \
                patch.object(check_distribution.subprocess, "run") as child:
            check_distribution.sys.stderr = BrokenConsole()
            child.return_value = subprocess.CompletedProcess(["synthetic"], 101)
            with self.assertRaisesRegex(DistributionError, "command failed \\(101\\)"):
                self.commands.run(["synthetic"], self.root)
        self.assertEqual(self.report["commands"][0]["exit_code"], 101)


class ArchiveTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def test_registry_links_allow_only_current_active_files(self):
        prefix = "https://github.com/MGYamada/Qleisli/blob/"
        historical = prefix + "7844a10d63880a2b6984c093e2dc7a75033d1e1e/docs/language-editions.md"
        (self.root / "README.md").write_text("current")
        self.assertEqual(check_registry_links(self.root,
            f"[current]({prefix}v0.2.8/README.md)", "0.2.8"), [])
        (self.root / "docs/src").mkdir(parents=True)
        (self.root / "docs/src/lean-backend-plan-v0.3.md").write_text("requested plan")
        self.assertEqual(check_registry_links(self.root,
            f"[plan]({prefix}v0.3.0-alpha/docs/src/lean-backend-plan-v0.3.md)", "0.3.0-alpha"), [])
        (self.root / "docs/new-guide.md").write_text("derived from current code")
        self.assertEqual(check_registry_links(self.root,
            f"[guide]({prefix}v0.3.0-alpha/docs/new-guide.md)", "0.3.0-alpha"), [])
        (self.root / "docs-old").mkdir()
        (self.root / "docs-old/design.md").write_text("temporary")
        for target in ["README.md", prefix + "main/README.md", prefix + "v0.2.8/missing.md",
                       historical, prefix + "v0.2.8/docs-old/design.md",
                       historical.replace("language-editions", "unreviewed"),
                       historical.replace("7844a10d63880a2b6984c093e2dc7a75033d1e1e", "v0.2.7")]:
            with self.subTest(target=target), self.assertRaises(ValueError):
                check_registry_links(self.root, f"[link]({target})", "0.2.8")

    def test_complete_archive_requires_kernel_source_audit_and_process_client(self):
        files = {name: File(b"source") for name in SOURCE_ROOTS}
        check_source_roots(files)
        for name in ["lean-kernel/Audit.lean", "lean-kernel/Main.lean", "lean-kernel/Tests.lean",
                     "scripts/check_lean_kernel.py", "examples/lean_kernel.rs"]:
            with self.subTest(name=name), self.assertRaisesRegex(DistributionError, name):
                check_source_roots({key: value for key, value in files.items() if key != name})

    def archive(self, entries):
        path = self.root / "candidate.tar"
        with tarfile.open(path, "w") as archive:
            for name, data, mode, kind in entries:
                member = tarfile.TarInfo(name)
                member.mode, member.type = mode, kind
                member.size = len(data) if kind == tarfile.REGTYPE else 0
                if kind in {tarfile.SYMTYPE, tarfile.LNKTYPE}:
                    member.linkname = "../../outside"
                archive.addfile(member, io.BytesIO(data) if member.isfile() else None)
        return path

    def test_preserves_binary_bytes_executable_mode_and_extracts(self):
        expected = {"NOTICE": File(b"notice\r\n\x00\xff"), "bin/check": File(b"run\n", 0o755)}
        path = self.archive([(name, file.data, file.mode, tarfile.REGTYPE)
                             for name, file in expected.items()])
        actual = read_archive(path, expected=expected)
        destination = self.root / "extracted"
        extract_checked(actual, destination)
        self.assertEqual((destination / "NOTICE").read_bytes(), expected["NOTICE"].data)
        self.assertEqual((destination / "bin/check").stat().st_mode & 0o777, 0o755)

    def test_missing_or_modified_notice_is_rejected(self):
        expected = {"NOTICE": File(b"retain attribution\n"), "src/lib.rs": File(b"code")}
        for changed in [{"src/lib.rs": expected["src/lib.rs"]},
                        dict(expected, NOTICE=File(b"delete attribution\n"))]:
            with self.subTest(changed=changed), self.assertRaises(DistributionError):
                compare_files(changed, expected)

    def test_same_length_byte_corruption_and_mode_change_rejected(self):
        expected = {"source.qli": File(b"original", 0o755)}
        for data, mode in [(b"modified", 0o755), (b"original", 0o644)]:
            path = self.archive([("source.qli", data, mode, tarfile.REGTYPE)])
            with self.subTest(data=data, mode=mode), self.assertRaises(DistributionError):
                read_archive(path, expected=expected)

    def test_traversal_absolute_alias_and_wrong_prefix_rejected(self):
        for name in ["../escape", "/escape", "a/../../escape", "a/./file", "a//file", "a\\file",
                     "C:/escape", "C:escape"]:
            path = self.archive([(name, b"bad", 0o644, tarfile.REGTYPE)])
            with self.subTest(name=name), self.assertRaises(DistributionError):
                read_archive(path)
        path = self.archive([("different/file", b"bad", 0o644, tarfile.REGTYPE)])
        with self.assertRaises(DistributionError):
            read_archive(path, prefix="expected")
        for name in ["expected/C:/escape", "expected/C:escape"]:
            path = self.archive([(name, b"bad", 0o644, tarfile.REGTYPE)])
            with self.subTest(name=name), self.assertRaises(DistributionError):
                read_archive(path, prefix="expected")

    def test_duplicate_regular_or_directory_entries_rejected(self):
        for kind in [tarfile.REGTYPE, tarfile.DIRTYPE]:
            path = self.archive([("same", b"first", 0o644, kind),
                                 ("same", b"second", 0o644, kind)])
            with self.subTest(kind=kind), self.assertRaises(DistributionError):
                read_archive(path)

    def test_links_special_files_and_file_directory_collisions_rejected(self):
        for kind in [tarfile.SYMTYPE, tarfile.LNKTYPE, tarfile.FIFOTYPE, tarfile.CHRTYPE]:
            path = self.archive([("entry", b"", 0o644, kind)])
            with self.subTest(kind=kind), self.assertRaises(DistributionError):
                read_archive(path)
        path = self.archive([("parent", b"file", 0o644, tarfile.REGTYPE),
                             ("parent/child", b"bad", 0o644, tarfile.REGTYPE)])
        with self.assertRaises(DistributionError):
            read_archive(path)

    def test_extra_missing_and_wrong_size_archive_files_rejected(self):
        expected = {"file": File(b"content")}
        for entries in [[], [("extra", b"content", 0o644, tarfile.REGTYPE)],
                        [("file", b"short", 0o644, tarfile.REGTYPE)]]:
            path = self.archive(entries)
            with self.subTest(entries=entries), self.assertRaises(DistributionError):
                read_archive(path, expected=expected)


def fixture_files():
    upstream = b"Upstream permission text\n"
    manifest = {"sources": [{"id": "fixture", "files": [
        {"local": "upstream/fixture/LICENSE", "sha256": digest(upstream)}]}],
        "cases": [{"project": "fixture/case"}]}
    files = {name: File(b"notice\n") for name in
             ["LICENSE", "NOTICE", "CONTRIBUTING.md", "corpus/NOTICE", "corpus/POLICY.md",
              "corpus/fixture/case/main.qli", "corpus/fixture/case/kernel.qli",
              "corpus/fixture/case/README.md"]}
    files["corpus/upstream/fixture/LICENSE"] = File(upstream)
    files["corpus/manifest.json"] = File(json.dumps(manifest).encode())
    files["Cargo.toml"] = File(b"original manifest")
    files["research/semantic-kernel/Cargo.toml"] = File(b"research manifest")
    return files


class PackageTests(unittest.TestCase):
    def setUp(self):
        self.tracked = fixture_files()
        self.candidate = {"commit": "1" * 40, "tree": "2" * 40, "clean": True}
        self.package = {name: file for name, file in self.tracked.items()
                        if not name.startswith("research/")}
        self.package.update({"Cargo.toml": File(b"normalized manifest"),
                             "Cargo.toml.orig": self.tracked["Cargo.toml"],
                             "Cargo.lock": File(b"generated lock"),
                             ".cargo_vcs_info.json": File(json.dumps(
                                 {"git": {"sha1": self.candidate["commit"]}, "path_in_vcs": ""}).encode())})

    def test_manifest_drives_counts_and_research_exclusion_is_explicit(self):
        record = check_package(self.package, self.tracked, list(self.package), self.candidate)
        self.assertEqual(record["upstream_files"], 1)
        self.assertEqual(record["translation_files"], 2)
        self.assertEqual(record["excluded_tracked_files"], ["research/semantic-kernel/Cargo.toml"])

    def test_missing_notice_cannot_be_hidden_by_package_listing(self):
        for name in ["NOTICE", "corpus/NOTICE", "corpus/upstream/fixture/LICENSE",
                     "corpus/fixture/case/main.qli"]:
            package = dict(self.package)
            del package[name]
            with self.subTest(name=name), self.assertRaises(DistributionError):
                check_package(package, self.tracked, list(package), self.candidate)

    def test_corrupt_upstream_and_modified_translation_rejected(self):
        for name in ["corpus/upstream/fixture/LICENSE", "corpus/fixture/case/kernel.qli"]:
            package = dict(self.package, **{name: File(b"changed")})
            with self.subTest(name=name), self.assertRaises(DistributionError):
                check_package(package, self.tracked, list(package), self.candidate)
        files = fixture_files()
        files["corpus/upstream/fixture/LICENSE"] = File(b"corrupt")
        with self.assertRaises(DistributionError):
            license_inventory(files)

    def test_dirty_or_wrong_commit_package_rejected(self):
        for vcs in [{"git": {"sha1": "3" * 40}},
                    {"git": {"sha1": self.candidate["commit"], "dirty": True}}]:
            package = dict(self.package)
            package[".cargo_vcs_info.json"] = File(json.dumps(vcs).encode())
            with self.subTest(vcs=vcs), self.assertRaises(DistributionError):
                check_package(package, self.tracked, list(package), self.candidate)

    def test_generated_metadata_mode_and_vcs_subdirectory_rejected(self):
        for name in ["Cargo.toml", "Cargo.lock", ".cargo_vcs_info.json", "Cargo.toml.orig"]:
            package = dict(self.package)
            package[name] = File(package[name].data, 0o777)
            with self.subTest(name=name), self.assertRaises(DistributionError):
                check_package(package, self.tracked, list(package), self.candidate)
        package = dict(self.package)
        package[".cargo_vcs_info.json"] = File(json.dumps(
            {"git": {"sha1": self.candidate["commit"]}, "path_in_vcs": "nested"}).encode())
        with self.assertRaises(DistributionError):
            check_package(package, self.tracked, list(package), self.candidate)

    def test_normalized_package_identity_license_dependencies_cannot_change(self):
        original = {"name": "qleisli-core", "version": "0.1.9", "license": "Apache-2.0",
                    "dependencies": [], "edition": "2024", "rust_version": "1.85"}
        compare_package_metadata(original, dict(original, manifest_path="different/path"))
        for key, value in [("name", "other"), ("version", "0.2.0"), ("license", "proprietary"),
                           ("dependencies", [{"name": "injected"}]), ("rust_version", "1.99"),
                           ("features", {"default": ["changed"]}),
                           ("readme", "wrong.md"), ("documentation", "https://example.invalid"),
                           ("keywords", ["wrong"]), ("categories", ["wrong"])]:
            with self.subTest(key=key), self.assertRaises(DistributionError):
                compare_package_metadata(original, dict(original, **{key: value}))

    def test_targets_preserve_relative_paths_and_build_options(self):
        original = {"manifest_path": "/candidate/Cargo.toml", "targets": [
            {"name": "core", "kind": ["lib"], "crate_types": ["lib"], "test": True,
             "src_path": "/candidate/src/lib.rs"}]}
        packaged = {"manifest_path": "/package/Cargo.toml", "targets": [
            dict(original["targets"][0], src_path="/package/src/lib.rs")]}
        compare_package_metadata(original, packaged)
        for mutation in [{"src_path": "/package/other.rs"}, {"test": False},
                         {"required-features": ["never-enabled"]}]:
            changed = dict(packaged, targets=[dict(packaged["targets"][0], **mutation)])
            with self.subTest(mutation=mutation), self.assertRaises(DistributionError):
                compare_package_metadata(original, changed)

    def test_untracked_content_and_missing_list_entry_rejected(self):
        package = dict(self.package, unexpected=File(b"injected"))
        with self.assertRaises(DistributionError):
            check_package(package, self.tracked, list(package), self.candidate)
        with self.assertRaises(DistributionError):
            check_package(self.package, self.tracked, ["Cargo.toml"], self.candidate)


class CandidateTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.root = self.base / "repository"
        self.root.mkdir()
        self.run_git("init", "-q")
        self.run_git("config", "user.name", "Distribution test")
        self.run_git("config", "user.email", "distribution-test@example.invalid")
        (self.root / "file").write_bytes(b"candidate\r\n")
        (self.root / ".gitignore").write_text("ignored\n")
        self.run_git("add", ".")
        self.run_git("-c", "commit.gpgsign=false", "commit", "-qm", "fixture")

    def run_git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.root), *args], stderr=subprocess.PIPE)

    def test_clean_commit_and_git_archive_keep_exact_bytes(self):
        candidate = clean_candidate(self.root)
        self.assertTrue(candidate["clean"])
        tracked = tracked_files(self.root, candidate["commit"])
        self.assertEqual(tracked["file"].data, b"candidate\r\n")
        archive = self.base / "source.tar"
        archive.write_bytes(self.run_git("-c", "tar.umask=0022", "archive", "--format=tar", "HEAD"))
        self.assertEqual(read_archive(archive, expected=tracked), tracked)

    def test_unstaged_staged_and_untracked_candidates_rejected(self):
        (self.root / "file").write_text("modified")
        with self.assertRaises(DistributionError):
            clean_candidate(self.root)
        self.run_git("add", "file")
        with self.assertRaises(DistributionError):
            clean_candidate(self.root)
        self.run_git("-c", "commit.gpgsign=false", "commit", "-qm", "next")
        (self.root / "untracked").write_text("untracked")
        with self.assertRaises(DistributionError):
            clean_candidate(self.root)

    def test_ignored_build_files_are_not_source_archive_contents(self):
        (self.root / "ignored").write_text("build output")
        candidate = clean_candidate(self.root)
        self.assertNotIn("ignored", tracked_files(self.root, candidate["commit"]))

    def test_dirty_validation_reports_failure_without_running_builds(self):
        (self.root / "untracked").write_text("dirty")
        destination = self.base / "report.json"
        report = validate(self.root, destination)
        self.assertEqual(report["status"], "failed")
        self.assertFalse(report["candidate"]["clean"])
        self.assertEqual(report["commands"], [])
        self.assertEqual(report["work"],
                         {"path": None, "status": "not-created", "keep_requested": False})
        self.assertEqual(json.loads(destination.read_text()), report)

    def test_report_inside_checkout_or_existing_report_rejected(self):
        with self.assertRaises(DistributionError):
            validate(self.root, self.root / "report.json")
        destination = self.base / "report.json"
        destination.write_text("keep old record")
        with self.assertRaises(DistributionError):
            validate(self.root, destination)
        self.assertEqual(destination.read_text(), "keep old record")


class SyntheticCommands:
    """Tiny command outputs exercising validate, its archives and real log writer.

    Git uses the local fixture repository. Cargo, Rust and client executions
    are simulated; no real compiler, installer or Lean process is started.
    """

    def __init__(self, root, fail=False, fail_package=False):
        self.root, self.fail, self.fail_package = root, fail, fail_package
        self.real_run = subprocess.run
        self.target_paths = set()
        self.installed = None
        self.crate_bytes = None
        self.files = tracked_files(root, "HEAD")
        self.package = {name: file for name, file in self.files.items()
                        if not name.startswith("research/")}
        self.package.update({"Cargo.toml": File(b"normalized manifest"),
                             "Cargo.toml.orig": self.files["Cargo.toml"],
                             "Cargo.lock": File(b"generated lock"),
                             ".cargo_vcs_info.json": File(json.dumps({
                                 "git": {"sha1": clean_candidate(root)["commit"]},
                                 "path_in_vcs": ""}).encode())})

    def __call__(self, argv, **kwargs):
        argv = [str(arg) for arg in argv]
        if argv[0] == "git":
            return self.real_run(argv, **kwargs)
        cwd = Path(kwargs["cwd"])
        output, error, exit_code = b"synthetic command passed\n", b"", 0
        if "--target-dir" in argv:
            target = Path(argv[argv.index("--target-dir") + 1])
            target.mkdir(parents=True, exist_ok=True)
            (target / "synthetic-build-output").write_bytes(b"small scratch\n")
            self.target_paths.add(target)
        if argv[:2] == ["cargo", "metadata"]:
            research = "--manifest-path" in argv
            manifest = cwd / ("research/semantic-kernel/Cargo.toml" if research else "Cargo.toml")
            output = json.dumps({"packages": [{"manifest_path": str(manifest),
                "name": "research" if research else "qleisli", "version": "0.0.0-synthetic",
                "license": "Apache-2.0", "publish": []}]}).encode()
        elif argv[:2] == ["cargo", "package"]:
            if "--list" in argv:
                output = ("\n".join(self.package) + "\n").encode()
            else:
                destination = target / "package" / "qleisli-0.0.0-synthetic.crate"
                destination.parent.mkdir(parents=True, exist_ok=True)
                with tarfile.open(destination, "w:gz") as archive:
                    for name, file in self.package.items():
                        entry = tarfile.TarInfo("qleisli-0.0.0-synthetic/" + name)
                        entry.size, entry.mode = len(file.data), file.mode
                        archive.addfile(entry, io.BytesIO(file.data))
                self.crate_bytes = destination.read_bytes()
                if self.fail_package:
                    error, exit_code = b"synthetic package verification failure\n", 23
        elif argv[:2] == ["cargo", "install"]:
            self.installed = Path(argv[argv.index("--root") + 1])
            (self.installed / "bin").mkdir(parents=True)
            executable = "qleisli.exe" if os.name == "nt" else "qleisli"
            (self.installed / "bin" / executable).write_bytes(b"synthetic executable\n")
        elif len(argv) > 1 and Path(argv[1]).name == "check_installation.py":
            output = json.dumps({"package": "qleisli", "version": "0.0.0-synthetic",
                                 "checks": ["synthetic-only"]}).encode()
        if self.fail and argv[:2] == ["cargo", "test"] and "--all-targets" in argv:
            output, error, exit_code = b"synthetic partial stdout\n", b"synthetic test failure\n", 23
        kwargs["stdout"].write(output)
        kwargs["stderr"].write(error)
        return subprocess.CompletedProcess(argv, exit_code)


class ScratchTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name).resolve()
        self.root = self.base / "repository"
        files = {name: File(b"synthetic source\n") for name in SOURCE_ROOTS}
        files.update(fixture_files())
        extract_checked(files, self.root)
        for args in [("init", "-q"), ("config", "user.name", "Distribution test"),
                     ("config", "user.email", "distribution-test@example.invalid"),
                     ("add", "."), ("-c", "commit.gpgsign=false", "commit", "-qm", "fixture")]:
            subprocess.run(["git", "-C", str(self.root), *args], check=True,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def run_validation(self, *, fail=False, fail_package=False, **kwargs):
        driver = SyntheticCommands(self.root, fail, fail_package)
        destination = self.base / "report.json"
        with patch.object(check_distribution.subprocess, "run", driver):
            report = validate(self.root, destination, **kwargs)
        self.assertEqual(json.loads(destination.read_text()), report)
        return report, driver

    def assert_durable_evidence(self, report):
        artifacts = Path(report["artifacts"])
        self.assertTrue(artifacts.is_dir())
        for key in ["crate", "source_archive"]:
            record = report[key]
            path = Path(record["path"])
            self.assertEqual(path.parent, artifacts)
            self.assertEqual(digest(path.read_bytes()), record["sha256"])
        for command in report["commands"]:
            self.assertTrue(Path(command["stdout"]).is_file())
            self.assertTrue(Path(command["stderr"]).is_file())

    def test_success_removes_owned_work_preserving_evidence(self):
        report, driver = self.run_validation()
        self.assertEqual(report["status"], "passed")
        self.assertEqual(report["work"]["status"], "removed")
        work = Path(report["work"]["path"])
        self.assertFalse(work.exists())
        self.assertEqual(len(driver.target_paths), 5)
        self.assertTrue(all(path.is_relative_to(work) and not path.exists()
                            for path in driver.target_paths))
        self.assertTrue(driver.installed.is_relative_to(work))
        self.assertEqual(report["cargo_target"]["ownership"], "validator")
        self.assert_durable_evidence(report)

    def test_failure_removes_owned_work_preserving_failure_and_evidence(self):
        report, _ = self.run_validation(fail=True)
        self.assertEqual(report["status"], "failed")
        self.assertIn("command failed (23)", report["error"])
        self.assertEqual(report["work"]["status"], "removed")
        self.assertFalse(Path(report["work"]["path"]).exists())
        self.assertEqual(Path(report["commands"][-1]["stderr"]).read_bytes(),
                         b"synthetic test failure\n")
        self.assert_durable_evidence(report)

    def test_failed_package_preserves_unverified_crate_before_cleanup(self):
        report, driver = self.run_validation(fail_package=True)
        self.assertEqual(report["status"], "failed")
        self.assertIn("command failed (23)", report["error"])
        self.assertEqual(report["work"]["status"], "removed")
        self.assertFalse(Path(report["work"]["path"]).exists())
        self.assertNotIn("crate", report)
        record = report["unverified_crate"]
        archive = Path(record["path"])
        self.assertEqual(archive.parent, Path(report["artifacts"]))
        self.assertEqual(digest(archive.read_bytes()), record["sha256"])
        self.assertEqual(archive.read_bytes(), driver.crate_bytes)
        self.assertEqual(record["cargo_verification"], "failed")
        self.assertEqual(record["candidate_binding"], "not-verified")
        self.assertFalse(archive.with_suffix(".crate.partial").exists())
        self.assertTrue(Path(report["source_archive"]["path"]).is_file())
        self.assertEqual(Path(report["commands"][-1]["stderr"]).read_bytes(),
                         b"synthetic package verification failure\n")

    def test_partial_copy_failure_preserves_sole_crate_and_original_failure(self):
        real_open = Path.open

        class FailedWrite:
            def __init__(self, handle):
                self.handle = handle

            def __enter__(self):
                return self

            def __exit__(self, *_):
                self.handle.close()

            def write(self, data):
                self.handle.write(data[:7])
                self.handle.flush()
                raise OSError("synthetic artifact storage full")

        def open_path(path, *args, **kwargs):
            handle = real_open(path, *args, **kwargs)
            if path.name.endswith(".crate.partial") and args == ("xb",):
                return FailedWrite(handle)
            return handle

        for fail_package in [False, True]:
            with self.subTest(fail_package=fail_package):
                with patch.object(Path, "open", open_path):
                    report, _ = self.run_validation(fail_package=fail_package)
                self.assertEqual(report["status"], "failed")
                self.assertEqual(report["work"]["status"], "retained")
                self.assertEqual(report["work"]["retention_reason"], "artifact-preservation-failed")
                self.assertFalse(report["work"]["keep_requested"])
                self.assertIn("command failed (23)" if fail_package else "synthetic artifact storage full",
                              report["error"])
                self.assertIn("synthetic artifact storage full", report["artifact_preservation_error"])
                self.assertNotIn("crate", report)
                self.assertNotIn("unverified_crate", report)
                original = Path(report["unretained_crate_path"])
                self.assertTrue(original.is_file())
                artifacts = Path(report["artifacts"])
                self.assertFalse((artifacts / original.name).exists())
                partial = artifacts / (original.name + ".partial")
                self.assertEqual(partial.read_bytes(), original.read_bytes()[:7])
                self.assertTrue(Path(report["source_archive"]["path"]).is_file())
                (self.base / "report.json").unlink()

    def test_failed_crate_preservation_keeps_external_target_without_retaining_work(self):
        target = self.base / "external-target"
        target.mkdir()
        (target / "sentinel").write_bytes(b"caller owned\n")
        with patch.object(check_distribution, "retain_crate",
                          side_effect=OSError("synthetic artifact storage full")):
            report, _ = self.run_validation(fail_package=True, target_dir=target)
        self.assertEqual(report["status"], "failed")
        self.assertIn("command failed (23)", report["error"])
        self.assertIn("synthetic artifact storage full", report["artifact_preservation_error"])
        self.assertEqual(report["work"]["status"], "removed")
        self.assertNotIn("retention_reason", report["work"])
        self.assertEqual((target / "sentinel").read_bytes(), b"caller owned\n")
        self.assertTrue(Path(report["unretained_crate_path"]).is_file())

    def test_keep_work_retains_success_and_failure(self):
        for fail in [False, True]:
            with self.subTest(fail=fail):
                report, driver = self.run_validation(fail=fail, keep_work=True)
                self.assertEqual(report["status"], "failed" if fail else "passed")
                self.assertEqual(report["work"]["status"], "retained")
                self.assertTrue(report["work"]["keep_requested"])
                work = Path(report["work"]["path"])
                self.assertTrue((work / "source").is_dir())
                self.assertTrue((work / "packaged-source").is_dir())
                self.assertTrue(driver.installed.is_dir())
                self.assertTrue(all(path.is_dir() for path in driver.target_paths))
                self.assert_durable_evidence(report)
                (self.base / "report.json").unlink()

    def test_caller_target_sentinel_and_build_outputs_survive_both_paths(self):
        target = self.base / "external-target"
        target.mkdir()
        sentinel = target / "sentinel"
        sentinel.write_bytes(b"caller owned\n")
        for fail in [False, True]:
            with self.subTest(fail=fail):
                report, driver = self.run_validation(fail=fail, target_dir=target)
                self.assertEqual(report["status"], "failed" if fail else "passed")
                self.assertEqual(report["work"]["status"], "removed")
                self.assertEqual(report["cargo_target"], {"path": str(target), "ownership": "caller"})
                self.assertEqual(sentinel.read_bytes(), b"caller owned\n")
                self.assertTrue(all(path.is_relative_to(target) and path.is_dir()
                                    for path in driver.target_paths))
                self.assert_durable_evidence(report)
                (self.base / "report.json").unlink()

    def test_cleanup_error_fails_success_and_preserves_original_failure(self):
        for fail in [False, True]:
            with self.subTest(fail=fail):
                with patch.object(check_distribution.shutil, "rmtree",
                                  side_effect=OSError("synthetic cleanup denied")):
                    report, _ = self.run_validation(fail=fail)
                self.assertEqual(report["status"], "failed")
                self.assertEqual(report["work"]["status"], "cleanup-failed")
                self.assertIn("synthetic cleanup denied", report["cleanup_error"])
                self.assertIn("command failed (23)" if fail else "cleanup failed", report["error"])
                self.assertTrue(Path(report["work"]["path"]).exists())
                self.assert_durable_evidence(report)
                (self.base / "report.json").unlink()

    def test_cli_keep_work_reaches_real_validation(self):
        destination = self.base / "report.json"
        driver = SyntheticCommands(self.root)
        with patch.object(check_distribution.subprocess, "run", driver), \
                patch.object(sys, "argv", ["check_distribution.py", "--root", str(self.root),
                                          "--report", str(destination), "--keep-work"]), \
                patch("sys.stdout", new_callable=io.StringIO):
            self.assertEqual(check_distribution.main(), 0)
        report = json.loads(destination.read_text())
        self.assertEqual(report["work"]["status"], "retained")
        self.assertTrue(Path(report["work"]["path"]).is_dir())

    def test_cli_reports_both_command_and_cleanup_failures(self):
        destination = self.base / "report.json"
        driver = SyntheticCommands(self.root, fail=True)
        with patch.object(check_distribution.subprocess, "run", driver), \
                patch.object(check_distribution.shutil, "rmtree",
                             side_effect=OSError("synthetic cleanup denied")), \
                patch.object(sys, "argv", ["check_distribution.py", "--root", str(self.root),
                                          "--report", str(destination)]), \
                patch("sys.stdout", new_callable=io.StringIO), \
                patch("sys.stderr", new_callable=io.StringIO) as stderr:
            self.assertEqual(check_distribution.main(), 1)
        self.assertIn("command failed (23)", stderr.getvalue())
        self.assertIn("synthetic cleanup denied", stderr.getvalue())
        report = json.loads(destination.read_text())
        self.assertEqual(report["status"], "failed")
        self.assertEqual(report["work"]["status"], "cleanup-failed")


if __name__ == "__main__":
    unittest.main()
