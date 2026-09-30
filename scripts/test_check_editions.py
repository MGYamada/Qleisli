#!/usr/bin/env python3
"""Mutation checks for edition coverage, independently parsed by Python TOML."""

from pathlib import Path
import tempfile
import unittest

from check_editions import check_editions

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
        self.assertEqual(counts, {"manifests": 2, "qli": 2, "qlt": 1})

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
