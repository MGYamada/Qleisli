#!/usr/bin/env python3
"""Mutation checks for shipped theorem/source bindings, not proofs of soundness.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import check_schema_registry as registry


class RegistryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = registry.read_json((registry.ROOT / registry.MANIFEST).read_bytes())
        cls.export = registry.manifest_export(cls.manifest)
        cls.revision = registry.source_revision(registry.ROOT)

    def rejects(self, change):
        candidate = copy.deepcopy(self.manifest)
        change(candidate)
        with self.assertRaises(registry.RegistryError):
            registry.verify_manifest(candidate, self.export, self.revision)

    def test_current_manifest(self):
        registry.verify_manifest(self.manifest, self.export, self.revision)

    def test_unknown_or_duplicate_ids(self):
        self.rejects(lambda m: m["entries"][0].update(id="Qleisli.Schema.qft_sound"))
        self.rejects(lambda m: m["entries"].append(copy.deepcopy(m["entries"][0])))

    def test_type_change_under_same_declaration(self):
        # Keeping the theorem name cannot authorize dropping its entire premise.
        self.rejects(lambda m: m["entries"][2]["theorem"].update(
            type=["constant", "True", []]))
        self.rejects(lambda m: m["checker"].update(type=["constant", "Bool", []]))

    def test_theorem_checker_domains_and_enablement(self):
        self.rejects(lambda m: m["entries"][0]["theorem"].update(declaration="True.intro"))
        self.rejects(lambda m: m["checker"].update(declaration="Other.check"))
        self.rejects(lambda m: m["entries"][0]["parameters"][0].update(max=16))
        self.rejects(lambda m: m["entries"][2].update(external_enabled=True))
        self.rejects(lambda m: m["entries"][2].update(template_version=2))

    def test_unknown_fields_and_boolean_version(self):
        self.rejects(lambda m: m.update(load_proof="untrusted.lean"))
        self.rejects(lambda m: m.update(version=True))
        self.rejects(lambda m: m["entries"][0].update(version=True))

    def test_source_revision_change(self):
        self.rejects(lambda m: m["source_revision"].update(sha256="0" * 64))
        self.rejects(lambda m: m["source_revision"]["files"].update(
            {"lean-kernel/QleisliKernel/Schema.lean": "0" * 64}))

    def test_export_must_name_actual_checker_in_theorem(self):
        export = copy.deepcopy(self.export)
        export["entries"][0]["theorem"]["type"] = ["constant", "True", []]
        with self.assertRaisesRegex(registry.RegistryError, "omits actual checker"):
            registry.expected_manifest(export, self.revision)

    def test_export_is_closed_and_versioned(self):
        for change in (
            lambda e: e.update(version=True),
            lambda e: e["entries"][0].update(id="unknown/1"),
            lambda e: e["entries"].reverse(),
            lambda e: e["entries"][0]["theorem"].update(module="Untrusted"),
            lambda e: e["checker"].update(module="Untrusted"),
        ):
            export = copy.deepcopy(self.export)
            change(export)
            with self.assertRaises(registry.RegistryError):
                registry.expected_manifest(export, self.revision)

    def test_strict_json(self):
        for source in ('{"id":1,"id":2}', '{"value":NaN}', '{"value":Infinity}'):
            with self.assertRaises(registry.RegistryError):
                registry.read_json(source.encode())

    def test_source_identity_covers_edits_and_new_modules(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in self.revision["files"]:
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((registry.ROOT / name).read_bytes())
            self.assertEqual(registry.source_revision(root), self.revision)
            path = root / "lean-kernel/QleisliKernel/Schema.lean"
            path.write_bytes(path.read_bytes() + b"\n-- mutation\n")
            self.assertNotEqual(registry.source_revision(root), self.revision)
            path.write_bytes((registry.ROOT / path.relative_to(root)).read_bytes())
            (path.parent / "Added.lean").write_text("def added := true\n")
            self.assertNotEqual(registry.source_revision(root), self.revision)

    def test_source_only_cannot_refresh_theorem_types(self):
        with self.assertRaisesRegex(registry.RegistryError, "requires rebuilt types"):
            registry.check(registry.ROOT, write=True, source_only=True)


if __name__ == "__main__":
    unittest.main()
