#!/usr/bin/env python3
"""Small public foreign/Python paths with a freshly invoked selected Lean gate.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import argparse
from dataclasses import replace
import hashlib
import importlib.util
import json
import os
from pathlib import Path
from current_source_fixtures import current_source_fixture
import subprocess
import sys
import tempfile
import tomllib
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "python"))
from qleisli import Client, QleisliError

FIXTURES = ROOT / "tests/fixtures/interop"
BINARY = ROOT / "target/debug/qleisli"
KERNEL = ROOT / "lean-kernel/.lake/build/bin/qleisli-kernel"
VERSION = tomllib.loads((ROOT / 'Cargo.toml').read_text())['package']['version']
ACTIONS = ("check", "run", "sample", "emit-ir", "emit-qasm", "emit-qir")
OBSERVATIONS = []
ENV = os.environ | {"PYTHONPATH": str(ROOT / "python")}


def process(command, data=None):
    command = list(map(str, command))
    result = subprocess.run(command, input=data, capture_output=True, timeout=70,
                            cwd=ROOT, env=ENV)
    OBSERVATIONS.append(dict(command=command, exit_code=result.returncode,
        input_sha256=hashlib.sha256(data).hexdigest() if data is not None else None,
        stdout=result.stdout.decode(errors="replace"), stderr=result.stderr.decode(errors="replace")))
    return result


class PublicNative(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="qleisli-interop-native-")
        cls.directory = Path(cls.temporary.name)
        cls.artifact = Client(BINARY, edition="2026").from_openqasm((FIXTURES / "bell.qasm").read_bytes()).artifact
        cls.artifact_path = cls.directory / "bell.qirf"
        cls.artifact_path.write_bytes(cls.artifact)
        cls.inputs = [("qasm", FIXTURES / "bell.qasm"),
                      ("qli", current_source_fixture(FIXTURES / "terminal")), ("qirf", cls.artifact_path)]

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def cli(self, action, format, path="-", *, kernel=None, data=None, extra=(), expected=0):
        args = [BINARY, "interop", action, path, f"--input={format}"]
        if format in ("qasm", "qirf"):
            args.append("--edition=2026")
        if kernel is not None:
            args.append(f"--lean-kernel={kernel}")
        if action == "sample":
            args.extend(["--shots=8", "--seed=7"])
        result = process([*args, *extra], data)
        self.assertEqual(result.returncode, expected, result.stderr)
        document = json.loads(result.stdout)
        self.assertEqual(document["format"], "qleisli.result")
        self.assertEqual(document["version"], 1)
        self.assertEqual(document["command"], f"interop {action}")
        self.assertEqual(document["outcome"], "error" if expected else "ok")
        if expected:
            self.assertIsNone(document["result"])
            self.assertTrue(document["diagnostics"])
        else:
            self.assertFalse(document["diagnostics"])
            if action == "check":
                actual_checker = Path(kernel or ENV["QLEISLI_KERNEL"]).resolve()
                self.assertEqual(document["result"], {
                    "checker_path": str(actual_checker),
                    "checker_identity": "unpinned",
                    "request_checked": False,
                    "ordinary_result_checked": False,
                    "source_preservation_verified": False,
                })
        return document

    def test_all_actions_formats_use_real_native_checker(self):
        for format, path in self.inputs:
            for action in ACTIONS:
                with self.subTest(format=format, action=action):
                    base = self.cli(action, format, path)
                    checked = self.cli(action, format, path, kernel=KERNEL)
                    self.assertEqual(base, checked)
        for name in ("bell", "gates"):
            source = (FIXTURES / f"{name}.qasm").read_bytes()
            self.assertEqual(self.cli("run", "qasm", data=source),
                             self.cli("run", "qasm", data=source, kernel=KERNEL))

    def test_qirf_emission_keeps_the_exact_checked_snapshot(self):
        for version in (1, 2):
            source = (ROOT / f"tests/fixtures/verification_v022/finite/t.v{version}.qirf").read_bytes()
            # Preserve framing/whitespace too; no second export of unchecked IR.
            source = b" \n" + source + b"\n "
            emitted = self.cli("emit-ir", "qirf", data=source, kernel=KERNEL)
            self.assertEqual(emitted["result"]["text"].encode(), source)

    def fake_kernel(self, name, response, status=0):
        path = self.directory / name
        path.write_text("#!/bin/sh\ncat >/dev/null\nprintf '%s' '" + response + f"'\nexit {status}\n")
        path.chmod(0o700)
        return path

    def test_missing_rejecting_and_failed_native_block_every_output(self):
        kernels = [self.directory / "absent",
                   self.fake_kernel("reject", "qleisli.native-result 3\nerror\ncontract\n", 1),
                   self.fake_kernel("capacity", "qleisli.native-result 3\nerror\nlimit\n", 1),
                   self.fake_kernel("failed", f"qleisli.native-result 3\naccepted\n2026\n{VERSION}\n--qirf-native\nexecution\n0\n0\n", 1),
                   self.fake_kernel("malformed", f"qleisli.native-result 3\naccepted\n2026\n{VERSION}\n--qirf-native\nexecution\n0\n0\ntrailing\n")]
        for kernel in kernels:
            for format, path in self.inputs:
                for action in ACTIONS:
                    with self.subTest(kernel=kernel.name, format=format, action=action):
                        self.cli(action, format, path, kernel=kernel, expected=1)

    def test_artifact_mutation_rejects_before_every_action(self):
        invalid = json.loads(self.artifact)
        invalid["root"] = 4294967295
        data = json.dumps(invalid).encode()
        for action in ACTIONS:
            with self.subTest(action=action):
                base = self.cli(action, "qirf", data=data, expected=1)
                selected = self.cli(action, "qirf", data=data, kernel=KERNEL, expected=1)
                # Both selection mechanisms must reject malformed input
                # before publishing any output.
                for document in (base, selected):
                    self.assertIn(document["diagnostics"][0]["code"], ("format", "invalid_ir"))

    def test_no_source_reload_after_native_acceptance(self):
        source = self.directory / "changing.qasm"
        original = (FIXTURES / "bell.qasm").read_bytes()
        replacement = 'OPENQASM 3.0; qubit q; bit c; reset q; c = measure q;'
        forwarder = self.directory / "mutating-kernel"
        forwarder.write_text(f"#!{sys.executable}\nimport pathlib, subprocess, sys\n"
            "packet = sys.stdin.buffer.read()\n"
            f"pathlib.Path({str(source)!r}).write_text({replacement!r})\n"
            f"result = subprocess.run([{str(KERNEL)!r}] + sys.argv[1:], input=packet, capture_output=True)\n"
            "sys.stdout.buffer.write(result.stdout)\nsys.exit(result.returncode)\n")
        forwarder.chmod(0o700)
        for action in ACTIONS:
            with self.subTest(action=action):
                source.write_bytes(original)
                before = self.cli(action, "qasm", source)
                selected = self.cli(action, "qasm", source, kernel=forwarder)
                if action == "check":
                    self.assertEqual(before["result"]["checker_path"], str(KERNEL.resolve()))
                    self.assertEqual(selected["result"]["checker_path"], str(forwarder.resolve()))
                    self.assertNotEqual(before["result"]["checker_path"], selected["result"]["checker_path"])
                    # The actual invoked checker is expected to differ. Keep
                    # every other scope/result field identical across source
                    # mutation rather than discarding the metadata wholesale.
                    selected = selected | {"result": selected["result"] | {
                        "checker_path": before["result"]["checker_path"],
                    }}
                self.assertEqual(before, selected)
                self.assertEqual(source.read_text(), replacement)

    def test_invalid_kernel_options_are_usage_failures(self):
        for flags in [("--lean-kernel=",), (f"--lean-kernel={KERNEL}", f"--lean-kernel={KERNEL}")]:
            self.cli("check", "qasm", data=b"OPENQASM 3.0;", extra=flags, expected=2)

    def test_source_edition_expectation_never_overrides_the_manifest(self):
        project = self.directory / 'edition-expectation'
        project.mkdir()
        (project / 'main.qli').write_text('use std::state::init0;\nobserve fn main() -> Bit { measure_z(init0()) }\n')
        manifest = project / 'Qargo.toml'
        manifest.write_text('schema-version = 2\n[qrate]\nedition = "2026"\n')
        for action in ACTIONS:
            with self.subTest(action=action):
                self.assertEqual(self.cli(action, 'qli', project),
                                 self.cli(action, 'qli', project, extra=['--expect-edition=2026']))
        for flags in (['--edition=2026'], ['--edition=2026', '--expect-edition=2026'],
                      ['--expect-edition=2026', '--expect-edition=2026']):
            self.cli('check', 'qli', project, extra=flags, expected=2)
        self.cli('check', 'qirf', self.artifact_path, extra=['--expect-edition=2026'], expected=2)
        for value in ('', 'latest', '2027'):
            document = self.cli('check', 'qli', project, extra=['--expect-edition=' + value], expected=1)
            self.assertEqual(document['diagnostics'][0]['code'], 'edition')
        manifest.write_text('schema-version = 2\n[qrate]\nedition = "2027"\n')
        marker = self.directory / 'unexpected-edition-checker'
        checker = self.directory / 'must-not-check-invalid-edition'
        checker.write_text(f'#!{sys.executable}\nfrom pathlib import Path\nPath({str(marker)!r}).touch()\nraise SystemExit(9)\n')
        checker.chmod(0o700)
        document = self.cli('check', 'qli', project, kernel=checker,
                            extra=['--expect-edition=2026'], expected=1)
        # Source declaration failures retain the existing project diagnostic,
        # distinct from an unsupported command-line edition parameter.
        diagnostic = document['diagnostics'][0]
        self.assertEqual(diagnostic['code'], 'project')
        self.assertIn('unsupported Qleisli edition "2027"', diagnostic['message'])
        self.assertEqual(diagnostic['primary']['path'], 'Qargo.toml')
        self.assertFalse(marker.exists())

    def test_python_source_program_keeps_captured_manifest_context(self):
        project = self.directory / 'captured-edition'
        project.mkdir()
        (project / 'main.qli').write_text('use std::state::init0;\nobserve fn main() -> Bit { measure_z(init0()) }\n')
        manifest = project / 'Qargo.toml'
        manifest.write_text('schema-version = 2\n[qrate]\nedition = "2026"\n')
        snapshot = self.cli('emit-ir', 'qli', project)['result']['text'].encode()
        forwarder = self.directory / 'manifest-mutating-checker'
        forwarder.write_text(f'#!{sys.executable}\nimport pathlib,subprocess,sys\n'
                             'packet = sys.stdin.buffer.read()\n'
                             f'pathlib.Path({str(manifest)!r}).write_text(\'schema-version = 2\\n[qrate]\\nedition = "2027"\\n\')\n'
                             f'result = subprocess.run([{str(KERNEL)!r}, *sys.argv[1:]], input=packet, capture_output=True)\n'
                             'sys.stdout.buffer.write(result.stdout)\nsys.stderr.buffer.write(result.stderr)\nsys.exit(result.returncode)\n')
        forwarder.chmod(0o700)
        program = Client(BINARY, edition='2026', lean_kernel=forwarder).compile_project(project)
        self.assertEqual(program.edition, '2026')
        self.assertEqual(program.artifact, snapshot)
        self.assertIn('"2027"', manifest.read_text())
        program.check()  # Fresh raw checking uses the retained explicit edition.
        with self.assertRaises(QleisliError) as failure:
            Client(BINARY, edition='2026', lean_kernel=KERNEL).compile_project(project)
        diagnostic = failure.exception.diagnostics[0]
        self.assertEqual(diagnostic['code'], 'project')
        self.assertIn('unsupported Qleisli edition "2027"', diagnostic['message'])
        self.assertEqual(diagnostic['primary']['path'], 'Qargo.toml')

    def test_python_imports_and_every_program_method_use_selected_kernel(self):
        base, selected = Client(BINARY, edition="2026"), Client(BINARY, lean_kernel=KERNEL, edition="2026")
        constructors = [lambda c: c.from_openqasm((FIXTURES / "bell.qasm").read_bytes()),
                        lambda c: c.compile_project(current_source_fixture(FIXTURES / "terminal")),
                        lambda c: c.from_ir(self.artifact)]
        for construct in constructors:
            a, b = construct(base), construct(selected)
            for method, kwargs in [("check", {}), ("run", {}), ("sample", dict(shots=8, seed=7)),
                                   ("to_openqasm", {}), ("to_qir", {})]:
                with self.subTest(method=method):
                    self.assertEqual(getattr(a, method)(**kwargs), getattr(b, method)(**kwargs))
                    blocked = replace(b, client=Client(BINARY, lean_kernel=self.directory / "absent", edition="2026"))
                    with self.assertRaises(QleisliError):
                        getattr(blocked, method)(**kwargs)
            with self.assertRaises(QleisliError):
                construct(Client(BINARY, lean_kernel=self.directory / "absent", edition="2026"))
        for value in ("", b"", "bad\0path"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                Client(BINARY, lean_kernel=value, edition="2026")

    def test_python_program_does_not_cache_prior_acceptance(self):
        forwarder = self.directory / "replaced-kernel"
        forwarder.write_text(f"#!{sys.executable}\nimport os, sys\n"
                            f"os.execv({str(KERNEL)!r}, [{str(KERNEL)!r}, *sys.argv[1:]])\n")
        forwarder.chmod(0o700)
        program = Client(BINARY, lean_kernel=forwarder, edition="2026").from_ir(self.artifact)
        self.fake_kernel("replaced-kernel", "qleisli.native-result 3\nerror\ninvalid_ir\n", 1)
        malformed = replace(program, client=Client(BINARY, lean_kernel=KERNEL, edition="2026"), artifact=b"{}")
        for current in (program, malformed):
            for method, kwargs in [("check", {}), ("run", {}), ("sample", dict(shots=8, seed=7)),
                                   ("to_openqasm", {}), ("to_qir", {})]:
                with self.subTest(method=method), self.assertRaises(QleisliError):
                    getattr(current, method)(**kwargs)

    @unittest.skipUnless(importlib.util.find_spec("pyqir"), "optional PyQIR is not installed")
    def test_qir_text_and_bitcode_keep_gate_after_translation(self):
        import pyqir
        source = (FIXTURES / "independent.ll").read_text()
        module = pyqir.Module.from_ir(pyqir.Context(), source)
        self.assertIsNone(module.verify())
        for data in (source, module.bitcode):
            with self.subTest(bitcode=isinstance(data, bytes)):
                self.assertEqual(Client(BINARY, edition="2026").from_qir(data).run(),
                                 Client(BINARY, lean_kernel=KERNEL, edition="2026").from_qir(data).run())
                with self.assertRaises(QleisliError):
                    Client(BINARY, lean_kernel=self.directory / "absent", edition="2026").from_qir(data)

    def test_python_cli_actions_preserve_failure_envelopes(self):
        inputs = list(self.inputs)
        if importlib.util.find_spec("pyqir"):
            inputs.append(("qir", FIXTURES / "independent.ll"))
        for format, path in inputs:
            for action in ACTIONS:
                args = [sys.executable, "-m", "qleisli", path, f"--input={format}",
                        "--edition=2026", f"--action={action}", f"--executable={BINARY}"]
                if action == "sample":
                    args.extend(["--shots=8", "--seed=7"])
                with self.subTest(format=format, action=action):
                    base = process(args)
                    selected = process([*args, f"--lean-kernel={KERNEL}"])
                    self.assertEqual(base.returncode, 0, base.stderr)
                    self.assertEqual(selected.returncode, 0, selected.stderr)
                    self.assertEqual(json.loads(base.stdout), json.loads(selected.stdout))
                    blocked = process([*args, f"--lean-kernel={self.directory / 'absent'}"])
                    self.assertEqual(blocked.returncode, 1, blocked.stderr)
                    doc = json.loads(blocked.stdout)
                    self.assertEqual(doc["command"], f"interop {action}")
                    self.assertEqual(doc["outcome"], "error")
                    self.assertTrue(doc["diagnostics"])
                    self.assertIsNone(doc["result"])


def main():
    global BINARY, KERNEL
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=BINARY)
    parser.add_argument("--kernel", type=Path, default=KERNEL)
    parser.add_argument("--record", type=Path)
    args = parser.parse_args()
    BINARY, KERNEL = args.binary.resolve(), args.kernel.resolve()
    # Compare environment and per-call selection using the same requested
    # checker, even when the invoking CI job has no kernel environment set.
    os.environ["QLEISLI_KERNEL"] = str(KERNEL)
    ENV["QLEISLI_KERNEL"] = str(KERNEL)
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(PublicNative))
    if args.record:
        args.record.parent.mkdir(parents=True, exist_ok=True)
        args.record.write_text(json.dumps(dict(status="passed" if result.wasSuccessful() else "failed",
            tests=result.testsRun, skipped=[reason for _, reason in result.skipped],
            scope="small foreign/Python selected checks; no source/backend preservation claim",
            binaries={str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in (BINARY, KERNEL)},
            sources={name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in
                ("scripts/test_interop_native.py", "src/bin/qleisli/interop.rs",
                 "python/qleisli/__init__.py", "python/qleisli/__main__.py")},
            observations=OBSERVATIONS), indent=2) + "\n")
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(main())
