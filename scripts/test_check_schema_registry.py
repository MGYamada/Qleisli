#!/usr/bin/env python3
"""Mutation checks for shipped theorem/source bindings, not proofs of soundness.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import copy
import json
import os
from pathlib import Path
import signal
import tempfile
import time
import unittest
from unittest.mock import patch
import subprocess
import sys

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

    def test_source_identity_covers_nested_transport(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in self.revision["files"]:
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((registry.ROOT / name).read_bytes())
            for name in ["Protocol/Core.lean", "Cli/Common.lean"]:
                with self.subTest(module=name):
                    path = root / "lean-kernel" / name
                    original = path.read_bytes()
                    path.write_bytes(original + b"\n-- mutation\n")
                    self.assertNotEqual(registry.source_revision(root), self.revision)
                    path.write_bytes(original)
                    extra = path.parent / "Added.lean"
                    extra.write_text("def added := true\n")
                    self.assertNotEqual(registry.source_revision(root), self.revision)
                    extra.unlink()
                    self.assertEqual(registry.source_revision(root), self.revision)

    def test_source_only_cannot_refresh_theorem_types(self):
        with self.assertRaisesRegex(registry.RegistryError, "requires rebuilt types"):
            registry.check(registry.ROOT, write=True, source_only=True)


class StreamCaptureTests(unittest.TestCase):
    def experiment(self, root, outside=None, failure=None):
        manifest = registry.read_json((registry.ROOT / registry.MANIFEST).read_bytes())
        revision = manifest["source_revision"]
        export = registry.manifest_export(manifest)
        target = root / registry.MANIFEST
        target.parent.mkdir(parents=True, exist_ok=True)
        original = b"original manifest must survive failure\n"
        target.write_bytes(original)
        outputs = [b"source-policy\xff\n", b"native build\n", b"native audit\n", b"math build\n", b"math audit\n", b"", json.dumps(export).encode()]
        expected = [([sys.executable, "scripts/check_lean_kernel.py"], root), (["lake", "build"], root / "lean-kernel"), (["lake", "env", "lean", "-DwarningAsError=true", "Audit.lean"], root / "lean-kernel"), (["lake", "build"], root / "lean"), (["lake", "env", "lean", "-DwarningAsError=true", "Audit.lean"], root / "lean"), (["lake", "env", "leanchecker", "--fresh", "QleisliKernel"], root / "lean-kernel"), (["lake", "env", "lean", "-DwarningAsError=true", "SchemaExport.lean"], root / "lean")]
        calls, report = [], {}

        def synthetic(argv, cwd, **kwargs):
            index = len(calls)
            self.assertEqual((argv, cwd), expected[index])
            stderr = b"failed\xfe" if index == failure else b""
            if outside is None:
                self.assertEqual(kwargs, {"capture_output": True, "check": False})
            else:
                self.assertEqual(set(kwargs), {"stdout", "stderr", "check"})
                self.assertFalse(kwargs["check"])
                kwargs["stdout"].write(outputs[index])
                kwargs["stderr"].write(stderr)
            calls.append((argv, cwd))
            return subprocess.CompletedProcess(argv, 1 if index == failure else 0, outputs[index], stderr)

        with patch.object(registry, "source_revision", return_value=revision), patch.object(registry.subprocess, "run", side_effect=synthetic):
            if failure is None:
                registry.check(root, write=True, report=report, command_output_dir=outside)
            else:
                with self.assertRaises(registry.RegistryError):
                    registry.check(root, write=True, report=report, command_output_dir=outside)
        self.assertEqual(len(calls), 7 if failure is None else failure + 1)
        if failure is not None:
            self.assertEqual(target.read_bytes(), original)
        if outside is not None:
            for index, row in enumerate(report["commands"]):
                self.assertEqual((outside / f"{index:02d}" / "stdout").read_bytes(), outputs[index])
                self.assertEqual(registry.digest((outside / f"{index:02d}" / "stdout").read_bytes()), row["stdout_sha256"])
            if failure is not None:
                self.assertEqual((outside / f"{failure:02d}" / "stderr").read_bytes(), b"failed\xfe")
        return report

    def test_optional_streams_preserve_exact_seven_commands_and_report_shape(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory).resolve()
            first = self.experiment(base / "default")
            second = self.experiment(base / "captured", base / "streams")
            self.assertEqual(set(first), set(second))
            self.assertEqual([row["argv"] for row in first["commands"]], [row["argv"] for row in second["commands"]])
            self.assertTrue(all(set(a) == set(b) for a, b in zip(first["commands"], second["commands"])))

    def test_failure_preserves_actual_non_utf8_streams_without_writing_manifest(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory).resolve()
            self.experiment(base / "failed", base / "streams", failure=3)

    @unittest.skipUnless(os.name == "posix", "requires the hosted POSIX process-group boundary")
    def test_interrupted_producer_retains_running_child_streams(self):
        child = "import pathlib,sys,time; sys.stdout.buffer.write(b'actual output\\xff\\n'); sys.stdout.flush(); sys.stderr.buffer.write(b'actual error\\xfe\\n'); sys.stderr.flush(); pathlib.Path(sys.argv[1]).write_text('ready'); time.sleep(60)"
        driver = "import sys; from pathlib import Path; sys.path.insert(0,sys.argv[1]); import check_schema_registry as registry; registry.run([sys.executable,'-c',sys.argv[4],sys.argv[5]],Path(sys.argv[2]),[],Path(sys.argv[3]))"
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory).resolve()
            streams = base / "streams"
            streams.mkdir()
            ready = base / "ready"
            process = subprocess.Popen([sys.executable, "-c", driver, str(registry.ROOT / "scripts"), str(base), str(streams), child, str(ready)], stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
            try:
                deadline = time.monotonic() + 10
                while not ready.exists() and process.poll() is None and time.monotonic() < deadline:
                    time.sleep(0.02)
                self.assertTrue(ready.exists(), "child did not write actual diagnostics before interruption")
                os.killpg(process.pid, signal.SIGTERM)
                process.communicate(timeout=5)
                self.assertNotEqual(process.returncode, 0)
                self.assertEqual((streams / "00/stdout").read_bytes(), b"actual output\xff\n")
                self.assertEqual((streams / "00/stderr").read_bytes(), b"actual error\xfe\n")
                self.assertIsNone(json.loads((streams / "00/command.json").read_bytes())["exit_code"])
            finally:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.communicate(timeout=5)


if __name__ == "__main__":
    unittest.main()
