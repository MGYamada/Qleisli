#!/usr/bin/env python3
"""Adversarial checks for release artifact identity and safe extraction.

These tests create local throwaway Git repositories; they do not run Cargo.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import io
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile
import unittest

from check_distribution import (
    DistributionError, File, check_package, clean_candidate, compare_files, compare_package_metadata,
    digest, extract_checked, license_inventory, read_archive, tracked_files, validate,
    SOURCE_ROOTS, check_source_roots,
)


class ArchiveTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

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
        self.assertEqual(json.loads(destination.read_text()), report)

    def test_report_inside_checkout_or_existing_report_rejected(self):
        with self.assertRaises(DistributionError):
            validate(self.root, self.root / "report.json")
        destination = self.base / "report.json"
        destination.write_text("keep old record")
        with self.assertRaises(DistributionError):
            validate(self.root, destination)
        self.assertEqual(destination.read_text(), "keep old record")


if __name__ == "__main__":
    unittest.main()
