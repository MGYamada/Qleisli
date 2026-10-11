#!/usr/bin/env python3
"""Mutation checks for edition coverage, independently parsed by Python TOML."""

from pathlib import Path
import json
import tempfile
import unittest

from check_editions import HISTORY, HISTORICAL_ROOT, REJECTED_AUTHORING_ROOT, REJECTED_CONST_ROOT, REJECTED_ARROW_ROOT, REJECTED_ADJOINT_ROOT, ROOT, check_editions

MANIFEST = 'schema-version = 2\n[qrate]\nedition = "2026"\n'


class EditionTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.write("Cargo.toml", '[package]\nversion = "0.2.3"\n')
        self.write("corpus/Qargo.toml", MANIFEST)
        self.write("stdlib/Qargo.toml", MANIFEST + 'name = "std"\nversion = "0.2.3"\n'
                   '[source]\nroot = "src"\n[tests]\nroot = "tests"\n[docs]\nroot = "docs"\n')
        self.write("stdlib/tests/README.md", "test root")
        self.write("stdlib/docs/README.md", "documentation root")
        self.write("corpus/sized/main.qli", "source")
        self.write("corpus/tests/meaning.qlt", "draft")
        self.write("stdlib/src/library.qli", "source")

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def test_all_extensions_inherit_their_own_source_tree_manifest(self):
        errors, counts = check_editions(self.root)
        self.assertEqual(errors, [])
        self.assertEqual(counts, {"manifests": 2, "qli": 2, "qlt": 1,
                                  "historical_manifests": 0, "historical_sources": 0})

    def copy_history(self):
        """Copy only exact source inputs and anchors, never build archives."""
        metadata = (ROOT / HISTORY).read_bytes()
        records = json.loads(metadata)["records"]
        files = {HISTORY: metadata}
        for record in records:
            for name in {**record["anchors"], **record["files"]}:
                name = str(Path(record["root"]) / name)
                files[name] = (ROOT / name).read_bytes()
        for name, data in files.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        return self.root / HISTORICAL_ROOT

    def test_exact_historical_inputs_are_not_reported_as_filesystem_admission(self):
        self.copy_history()
        errors, counts = check_editions(self.root)
        self.assertEqual(errors, [])
        self.assertEqual(counts, {"manifests": 2, "qli": 2, "qlt": 1,
                                  "historical_manifests": 31, "historical_sources": 64})

    def test_historical_source_manifest_generator_and_record_are_immutable(self):
        base = self.copy_history()
        for name in ["sources/ab/main.qli", "sources/ab/Qargo.toml", "Generate.rs", "validation.json"]:
            with self.subTest(name=name):
                path = base / name
                original = path.read_bytes()
                path.write_bytes(original + b"\n")
                self.assertTrue(any("historical input identity changed" in e
                                    for e in check_editions(self.root)[0]))
                path.write_bytes(original)
        # Even a valid new spelling must be a separate derivative, not a
        # rewrite of the old observation masquerading as its original input.
        self.write(f"{HISTORICAL_ROOT}/sources/ab/Qargo.toml", MANIFEST)
        self.assertTrue(any("historical input identity changed" in e
                            for e in check_editions(self.root)[0]))

    def test_missing_historical_inputs_and_exception_record_reject(self):
        base = self.copy_history()
        path = base / "first-attempt/sources/ab/main.qli"
        original = path.read_bytes()
        path.unlink()
        self.assertTrue(any("missing historical input" in e
                            for e in check_editions(self.root)[0]))
        path.write_bytes(original)
        (self.root / HISTORY).unlink()
        self.assertTrue(any(f"missing {HISTORY}" in e
                            for e in check_editions(self.root)[0]))

    def test_exception_cannot_expand_to_new_sources_or_projects(self):
        self.copy_history()
        self.write(f"{HISTORICAL_ROOT}/sources/ab/new.qli", "new source")
        self.assertTrue(any("historical source inventory changed" in e
                            for e in check_editions(self.root)[0]))
        (self.root / HISTORICAL_ROOT / "sources/ab/new.qli").unlink()
        self.write(f"{HISTORICAL_ROOT}/sources/new/Qargo.toml", '[qrate]\nschema = 2\nedition = "2026"\n')
        self.write(f"{HISTORICAL_ROOT}/sources/new/main.qli", "new source")
        self.assertTrue(any("requires schema-version = 2" in e
                            for e in check_editions(self.root)[0]))
        self.write(f"{HISTORICAL_ROOT}/sources/new/Qargo.toml", MANIFEST)
        errors, counts = check_editions(self.root)
        self.assertEqual(errors, [])
        self.assertEqual(counts["qli"], 3)  # The new project has ordinary coverage.
        self.assertEqual(counts["historical_sources"], 64)

    def test_const_first_refusals_are_exact_history_and_repaired_sources_are_ordinary(self):
        self.copy_history()
        base = self.root / REJECTED_CONST_ROOT
        for name in ("attempt-01/natural/main.qli", "attempt-01/natural/Qargo.toml",
                     "before/natural-selected.json"):
            with self.subTest(name=name):
                path = base / name
                original = path.read_bytes()
                path.write_bytes(original + b"\n")
                self.assertTrue(any("historical input identity changed" in e
                                    for e in check_editions(self.root)[0]))
                path.write_bytes(original)
        self.write(f"{REJECTED_CONST_ROOT}/attempt-01/natural/new.qli", "new source")
        self.assertTrue(any("historical source inventory changed" in e
                            for e in check_editions(self.root)[0]))
        (base / "attempt-01/natural/new.qli").unlink()
        self.write(f"{REJECTED_CONST_ROOT}/attempt-02/natural/main.qli", "repaired source")
        self.write(f"{REJECTED_CONST_ROOT}/attempt-02/natural/Qargo.toml", MANIFEST)
        self.assertEqual(check_editions(self.root)[0], [])
        self.write(f"{REJECTED_CONST_ROOT}/attempt-02/natural/Qargo.toml", "schema = 2")
        self.assertTrue(any("requires schema-version = 2" in e
                            for e in check_editions(self.root)[0]))

    def test_arrow_refusal_cannot_admit_mutations_or_repaired_invalid_manifest(self):
        self.copy_history()
        base = self.root / REJECTED_ARROW_ROOT
        for name in ("attempt-01/preparation.qli", "attempt-01/Qargo.toml",
                     "observations/preparation-before.json"):
            with self.subTest(name=name):
                path = base / name
                original = path.read_bytes()
                path.write_bytes(original + b"\n")
                self.assertTrue(any("historical input identity changed" in e
                                    for e in check_editions(self.root)[0]))
                path.write_bytes(original)
        self.write(f"{REJECTED_ARROW_ROOT}/attempt-01/new.qli", "new source")
        self.assertTrue(any("historical source inventory changed" in e
                            for e in check_editions(self.root)[0]))
        (base / "attempt-01/new.qli").unlink()
        self.write(f"{REJECTED_ARROW_ROOT}/attempt-02/main.qli", "repaired source")
        self.write(f"{REJECTED_ARROW_ROOT}/attempt-02/Qargo.toml", MANIFEST)
        self.assertEqual(check_editions(self.root)[0], [])
        self.write(f"{REJECTED_ARROW_ROOT}/attempt-02/Qargo.toml", "schema = 2")
        self.assertTrue(any("attempt-02/Qargo.toml: requires schema-version = 2" in e
                            for e in check_editions(self.root)[0]))

    def test_adjoint_refusal_keeps_exact_inputs_and_repaired_attempt_ordinary(self):
        self.copy_history()
        base = self.root / REJECTED_ADJOINT_ROOT
        for name in ("attempt-01/main.qli", "attempt-01/Qargo.toml",
                     "observations/before.json"):
            with self.subTest(name=name):
                path = base / name
                original = path.read_bytes()
                path.write_bytes(original + b"\n")
                self.assertTrue(any("historical input identity changed" in e
                                    for e in check_editions(self.root)[0]))
                path.write_bytes(original)
        self.write(f"{REJECTED_ADJOINT_ROOT}/attempt-01/new.qli", "new source")
        self.assertTrue(any("historical source inventory changed" in e
                            for e in check_editions(self.root)[0]))
        (base / "attempt-01/new.qli").unlink()
        for name in ("main.qli", "Qargo.toml"):
            self.write(f"{REJECTED_ADJOINT_ROOT}/attempt-02/{name}",
                       (ROOT / REJECTED_ADJOINT_ROOT / "attempt-02" / name).read_text())
        errors, counts = check_editions(self.root)
        self.assertEqual(errors, [])
        self.assertEqual(counts["qli"], 3)
        self.assertEqual(counts["manifests"], 3)
        self.assertEqual(counts["historical_sources"], 64)
        self.write(f"{REJECTED_ADJOINT_ROOT}/attempt-02/Qargo.toml", "schema = 2")
        self.assertTrue(any("attempt-02/Qargo.toml: requires schema-version = 2" in e
                            for e in check_editions(self.root)[0]))

    def test_exception_metadata_and_symlinks_cannot_redirect_history(self):
        base = self.copy_history()
        metadata = self.root / HISTORY
        original = metadata.read_bytes()
        value = json.loads(original)
        value["records"][0]["projects"].clear()
        metadata.write_text(json.dumps(value))
        self.assertTrue(any("historical input identity changed" in e
                            for e in check_editions(self.root)[0]))
        metadata.write_bytes(original)
        path = base / "sources/ab/main.qli"
        saved = path.read_bytes()
        other = self.root / "outside.txt"
        other.write_bytes(saved)
        path.unlink()
        path.symlink_to(other)
        self.assertTrue(any("must not follow symlinks" in e
                            for e in check_editions(self.root)[0]))

    def test_rejected_authoring_attempt_preserves_refusal_and_exact_inventory(self):
        self.copy_history()
        base = self.root / REJECTED_AUTHORING_ROOT
        for name in ("attempt-01/main.qli", "attempt-01/Qargo.toml", "observation-before.json"):
            with self.subTest(name=name):
                path = base / name
                original = path.read_bytes()
                path.write_bytes(original + b"\n")
                self.assertTrue(any("historical input identity changed" in e
                                    for e in check_editions(self.root)[0]))
                path.write_bytes(original)
        self.write(f"{REJECTED_AUTHORING_ROOT}/attempt-01/new.qli", "new source")
        self.assertTrue(any("historical source inventory changed" in e
                            for e in check_editions(self.root)[0]))

    def test_corrected_attempt_is_ordinary_and_missing_history_cannot_hide_refusal(self):
        self.copy_history()
        self.write(f"{REJECTED_AUTHORING_ROOT}/attempt-02/main.qli", "corrected source")
        self.write(f"{REJECTED_AUTHORING_ROOT}/attempt-02/Qargo.toml", MANIFEST)
        errors, counts = check_editions(self.root)
        self.assertEqual(errors, [])
        self.assertEqual(counts["qli"], 3)
        self.write(f"{REJECTED_AUTHORING_ROOT}/attempt-02/Qargo.toml", '[qrate]\nedition = "2026"\n')
        self.assertTrue(any("attempt-02/Qargo.toml: requires schema-version = 2" in e
                            for e in check_editions(self.root)[0]))
        # The second historical root also requires its frozen record even if
        # the original in-memory experiment is absent from a checkout.
        import shutil
        shutil.rmtree(self.root / HISTORICAL_ROOT)
        (self.root / HISTORY).unlink()
        self.assertTrue(any(f"missing {HISTORY}" in e
                            for e in check_editions(self.root)[0]))

    def test_omitted_manifest_and_repository_root_placement_fail(self):
        (self.root / "corpus/Qargo.toml").unlink()
        self.assertTrue(check_editions(self.root)[0])
        self.write("Qargo.toml", MANIFEST)
        self.assertIn("repository root", check_editions(self.root)[0][0])

    def test_invalid_nearer_manifest_cannot_fall_back(self):
        for text in ("invalid", 'schema-version = 2\n[qrate]\nedition = "2027"',
                     "schema-version = 2\n[qrate]\nedition = 2026", "schema-version = 2",
                     'schema-version = 1\n[qrate]\nedition = "2026"',
                     MANIFEST + 'edition = "2026"'):
            with self.subTest(text=text):
                self.write("corpus/tests/Qargo.toml", text)
                errors, _ = check_editions(self.root)
                self.assertTrue(any("meaning.qlt: invalid enclosing" in e for e in errors))

    def test_source_outside_declared_trees_is_uncovered(self):
        self.write("new-tree/new.qlt", "draft")
        self.assertTrue(any("new-tree/new.qlt: missing enclosing" in e
                            for e in check_editions(self.root)[0]))

    def test_generated_build_outputs_are_excluded(self):
        self.write("target/generated.qli", "generated")
        self.assertEqual(check_editions(self.root)[0], [])

    def test_std_qrate_requires_full_identity_roots_and_synchronized_version(self):
        original = (self.root / "stdlib/Qargo.toml").read_text()
        for changed in (MANIFEST, original.replace('name = "std"', 'name = "stdlib"'),
                        original.replace('version = "0.2.3"', 'version = "0.2.2"'),
                        original.replace('root = "tests"', 'root = "absent"')):
            with self.subTest(changed=changed):
                self.write("stdlib/Qargo.toml", changed)
                self.assertTrue(any("stdlib/Qargo.toml:" in e
                                    for e in check_editions(self.root)[0]))


if __name__ == "__main__":
    unittest.main()
