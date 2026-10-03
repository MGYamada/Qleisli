#!/usr/bin/env python3
"""Small-system connection regressions; run against an installed Python package.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from dataclasses import replace

import pyqir
from qleisli import Client, Program, QleisliError

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "tests/fixtures/interop"
EXE = os.environ.get("QLEISLI_BIN", str(ROOT / "target/debug/qleisli"))


class Connections(unittest.TestCase):
    def setUp(self):
        self.client = Client(EXE)
        self.qir = (FIXTURES / "independent.ll").read_text()

    def test_qir_reader_cannot_be_replaced_by_current_directory_package(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            decoy = root / "qleisli"
            decoy.mkdir()
            (decoy / "__init__.py").write_text("")
            (decoy / "_qir.py").write_text("from pathlib import Path; Path('executed').touch(); raise SystemExit(91)")
            original = Path.cwd()
            try:
                os.chdir(root)
                # Importing Client above used the real installed package. A new
                # child must keep that identity even with a decoy beside input.
                result = self.client.from_qir(self.qir).run()
                self.assertEqual(result["distribution"][0]["bits"], [False, True])
                self.assertFalse((root / "executed").exists())
            finally:
                os.chdir(original)

    def test_host_cli_uses_closed_v1_codes_for_local_failures(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "source.qasm"
            source.write_text("OPENQASM 3.0;")
            for path, executable in [(source.with_name("missing.qasm"), EXE),
                                     (source, str(source.with_name("missing-executable")))]:
                result = subprocess.run([sys.executable, "-m", "qleisli", str(path),
                    "--input=qasm", "--executable", executable], capture_output=True)
                self.assertEqual(result.returncode, 1)
                self.assertEqual(json.loads(result.stdout)["diagnostics"][0]["code"], "project")

    def test_independent_qir_text_bitcode_order(self):
        expected = {"distribution": [{"bits": [False, True], "probability": 1.0}]}
        self.assertEqual(self.client.from_qir(self.qir).run(), expected)
        module = pyqir.Module.from_ir(pyqir.Context(), self.qir)
        self.assertIsNone(module.verify())
        self.assertEqual(self.client.from_qir(module.bitcode).run(), expected)
        # Resource ID order is not the output order.
        changed = self.qir.replace("ptr null, ptr @first", "ptr inttoptr (i64 1 to ptr), ptr @first").replace(
            "ptr inttoptr (i64 1 to ptr), ptr @second", "ptr null, ptr @second")
        self.assertEqual(self.client.from_qir(changed).run()["distribution"][0]["bits"], [True, False])

    def test_unnamed_and_mixed_block_identity_text_and_bitcode(self):
        expected = self.client.from_qir(self.qir).run()
        unnamed = self.qir.replace("start:", "0:").replace("readout:", "1:").replace("label %readout", "label %1")
        three = self.qir.replace("start:", "0:").replace("readout:", "2:").replace("label %readout", "label %1")
        three = three.replace("2:\n", "1:\n  br label %2\n2:\n")
        variants = [unnamed, three, self.qir.replace("start:", "0:"),
                    self.qir.replace("readout:", "0:").replace("label %readout", "label %0")]
        for source in variants:
            module = pyqir.Module.from_ir(pyqir.Context(), source)
            self.assertIsNone(module.verify())
            for encoded in [source, module.bitcode]:
                with self.subTest(source=source[:80], bitcode=isinstance(encoded, bytes)):
                    self.assertEqual(self.client.from_qir(encoded).run(), expected)
        for source, reason in [(three.replace("ret void", "br label %1"), "cyclic CFG"),
                               (unnamed.replace("ret void\n}", "ret void\n2:\n  ret void\n}"), "unvisited blocks")]:
            module = pyqir.Module.from_ir(pyqir.Context(), source)
            self.assertIsNone(module.verify())
            for encoded in [source, module.bitcode]:
                with self.subTest(reason=reason), self.assertRaises(QleisliError) as error:
                    self.client.from_qir(encoded)
                self.assertIn(reason, str(error.exception))

    def test_artifact_pointers_and_qasm_source_locations_are_preserved(self):
        artifact = json.loads(self.client.from_openqasm("OPENQASM 3.0;").artifact)
        artifact["root"] = None
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "bad.qirf"
            path.write_text(json.dumps(artifact))
            diagnostics = []
            for args in [["verify-ir", str(path), "--format=json"],
                         ["interop", "check", str(path), "--input=qirf"]]:
                result = subprocess.run([EXE, *args], capture_output=True)
                self.assertEqual(result.returncode, 1)
                diagnostics.append(json.loads(result.stdout)["diagnostics"])
            self.assertEqual(diagnostics[0], diagnostics[1])
            self.assertEqual(diagnostics[0][0]["related"], [{"message": "json_pointer: /root", "location": None}])
            source = '// λ🦀\r\nOPENQASM 3.0; include "stdgates.inc"; qubit q; bit c; reset q; mystery q; c = measure q;'
            qasm = Path(directory) / "bad.qasm"
            qasm.write_bytes(source.encode())
            result = subprocess.run([EXE, "interop", "check", str(qasm), "--input=qasm"], capture_output=True)
            direct = json.loads(result.stdout)["diagnostics"]
            location = direct[0]["primary"]
            start = source.encode().index(b"mystery")
            self.assertEqual(location, {"path": "bad.qasm", "start": start, "end": start + 7,
                                        "line": 2, "column": 64})
            # Python retains the complete structured envelope; no message parsing.
            result = subprocess.run([EXE, "interop", "emit-ir", "-", "--input=qasm"], input=source.encode(), capture_output=True)
            direct_stdin = json.loads(result.stdout)["diagnostics"]
            with self.assertRaises(QleisliError) as error:
                self.client.from_openqasm(source)
            self.assertEqual(error.exception.diagnostics, direct_stdin)
            self.assertEqual(direct_stdin[0]["primary"]["path"], "-")

    def test_bell_sampling_and_all_gates(self):
        for name in ["bell", "gates"]:
            program = self.client.from_openqasm((FIXTURES / f"{name}.qasm").read_text())
            imported = self.client.from_qir(program.to_qir())
            before, after = program.run()["distribution"], imported.run()["distribution"]
            self.assertEqual([row["bits"] for row in before], [row["bits"] for row in after])
            for a, b in zip(before, after):
                # Exact target rewrites can change floating evaluation order.
                self.assertAlmostEqual(a["probability"], b["probability"], delta=1e-12)
            original, emitted = [p.sample(shots=30, seed=17) for p in [program, imported]]
            self.assertEqual([shot["bits"] for shot in original["shots"]],
                             [shot["bits"] for shot in emitted["shots"]])
            # The shortened target has its own work count; each total must still
            # account for its actual shots rather than copying the source total.
            for sample in [original, emitted]:
                self.assertEqual(sample["execution_steps"], sum(s["execution_steps"] for s in sample["shots"]))
                self.assertTrue(all(s["execution_steps"] > 0 for s in sample["shots"]))
            if name == "gates":
                self.assertLess(emitted["execution_steps"], original["execution_steps"])
        shots = self.client.from_openqasm((FIXTURES / "bell.qasm").read_text()).sample(shots=30, seed=0)["shots"]
        self.assertEqual({tuple(s["bits"]) for s in shots}, {(False, False), (True, True)})

    def test_interference_and_hidden_results(self):
        source = 'OPENQASM 3.0; include "stdgates.inc"; qubit q; bit c; reset q; h q; t q; t q; t q; t q; h q; c = measure q;'
        p = self.client.from_qir(self.client.from_openqasm(source).to_qir())
        probabilities = {tuple(s["bits"]): s["probability"] for s in p.run()["distribution"]}
        self.assertAlmostEqual(probabilities[(True,)], 1.0)
        hidden = self.qir.replace("array_record_output(i64 2", "array_record_output(i64 1").replace(
            "  call void @__quantum__rt__result_record_output(ptr inttoptr (i64 1 to ptr), ptr @second)\n", "")
        self.assertEqual(self.client.from_qir(hidden).run()["distribution"][0]["bits"], [False])
        self.assertEqual(self.client.from_qir(self.client.from_openqasm("OPENQASM 3.0;").to_qir()).run(),
                         {"distribution": [{"bits": [], "probability": 1.0}]})

    def test_project_and_raw_ir_reverification(self):
        p = self.client.compile_project(FIXTURES / "terminal")
        self.assertEqual(self.client.from_ir(p.artifact).run(), p.run())
        self.assertTrue(p.check()["verified"])
        for mutated in [b"{}", p.artifact.rstrip()[:-1], p.artifact + b"garbage"]:
            with self.subTest(mutated=mutated[:50]), self.assertRaises(QleisliError):
                replace(p, artifact=mutated).run()
        with self.assertRaises(QleisliError):
            Program(self.client, b"{}").to_qir()

    def test_qir_rejects_profile_cfg_calls_and_resources(self):
        cases = {
            "malformed": b"not llvm", "bad-bitcode": b"BC\xc0\xde\0",
            "version": self.qir.replace('!"qir_major_version", i32 2', '!"qir_major_version", i32 1'),
            "dynamic": self.qir.replace('!"dynamic_qubit_management", i1 false', '!"dynamic_qubit_management", i1 true'),
            "profile": self.qir.replace('"base_profile"', '"adaptive_profile"'),
            "qis": self.qir.replace("x__body", "unknown__body"),
            "signature": self.qir.replace("declare void @__quantum__qis__x__body(ptr)", "declare i64 @__quantum__qis__x__body(ptr)"),
            "attribute": self.qir.replace('"irreversible"', '"readnone"'),
            "call-attribute": self.qir.replace("x__body(ptr null)", "x__body(ptr nonnull null)"),
            "entry-attribute": self.qir.replace('"entry_point"', '"entry_point" "noreturn"'),
            "no-init": self.qir.replace("  call void @__quantum__rt__initialize(ptr null)\n", ""),
            "duplicate-init": self.qir.replace("start:\n", "start:\n  call void @__quantum__rt__initialize(ptr null)\n"),
            "bounds": self.qir.replace("x__body(ptr null)", "x__body(ptr inttoptr (i64 2 to ptr))"),
            "global-as-wire": self.qir.replace("x__body(ptr null)", "x__body(ptr @root)"),
            "cycle": self.qir.replace("br label %readout", "br label %start"),
            "conditional": self.qir.replace("br label %readout", "br i1 true, label %readout, label %readout"),
            "unvisited": self.qir.replace("  ret void\n}", "  ret void\nunused:\n  ret void\n}"),
            "extra-definition": self.qir + "\ndefine void @other() { ret void }\n",
            "qis-definition": self.qir.replace("declare void @__quantum__qis__x__body(ptr)", "define void @__quantum__qis__x__body(ptr %q) { ret void }"),
            "late-gate": self.qir.replace("  ret void", "  call void @__quantum__qis__x__body(ptr null)\n  ret void"),
            "duplicate-measure": self.qir.replace("mz__body(ptr inttoptr (i64 1 to ptr), ptr null)", "mz__body(ptr null, ptr null)"),
            "result-overwrite": self.qir.replace("mz__body(ptr null, ptr inttoptr (i64 1 to ptr))", "mz__body(ptr null, ptr null)"),
            "duplicate-output": self.qir.replace("result_record_output(ptr inttoptr (i64 1 to ptr), ptr @second)", "result_record_output(ptr null, ptr @second)"),
            "missing-output": self.qir.replace("array_record_output(i64 2", "array_record_output(i64 3"),
            "label": self.qir.replace("ptr @second", "ptr @first"),
            "mutable": self.qir.replace("private constant", "private global"),
            "assembly": 'module asm "nop"\n' + self.qir,
            "alias": self.qir + "\n@alias = alias void (), ptr @external_entry\n",
            "oversize": b" " * ((1 << 20) + 1),
        }
        for name, source in cases.items():
            with self.subTest(name=name), self.assertRaises(QleisliError):
                self.client.from_qir(source)

    def test_rust_error_equivalence_and_atomic_failure(self):
        source = b"OPENQASM 3.0; qubit q;"
        result = subprocess.run([EXE, "interop", "emit-ir", "-", "--input=qasm"], input=source, capture_output=True)
        self.assertEqual(result.returncode, 1)
        doc = json.loads(result.stdout)
        self.assertIsNone(doc["result"])
        with self.assertRaises(QleisliError) as error:
            self.client.from_openqasm(source)
        self.assertEqual(error.exception.diagnostics, doc["diagnostics"])
        for flags in [["--input=qasm", "--input=qasm"], ["--input=qir"], ["--input=qasm", "--seed=0"]]:
            result = subprocess.run([EXE, "interop", "check", "-", *flags], input=b"", capture_output=True)
            self.assertEqual(result.returncode, 2)
            self.assertIsNone(json.loads(result.stdout)["result"])

    def test_python_limits_and_cli(self):
        p = self.client.from_qir(self.qir)
        for shots, seed in [(0, 0), (True, 0), (1, -1), (1, 2**64)]:
            with self.assertRaises(ValueError):
                p.sample(shots=shots, seed=seed)
        with self.assertRaises(QleisliError):
            self.client.from_openqasm(" " * ((1 << 20) + 1))
        result = subprocess.run([sys.executable, "-m", "qleisli", str(FIXTURES / "independent.ll"),
                                 "--input=qir", "--action=run", "--executable", EXE], capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["result"], p.run())

    def test_relative_project_diagnostic_keeps_source_location(self):
        with tempfile.TemporaryDirectory(dir=ROOT / "target") as directory:
            root = Path(directory)
            (root / "Qargo.toml").write_text('schema-version = 2\n[qrate]\nedition = "2026"\n')
            (root / "main.qli").write_text("observe fn main() -> CBit { missing() }\n")
            result = subprocess.run([EXE, "interop", "check", str(root.relative_to(ROOT)),
                                     "--input=qli"], cwd=ROOT, capture_output=True)
            self.assertEqual(result.returncode, 1)
            diagnostic = json.loads(result.stdout)["diagnostics"][0]
            self.assertNotEqual(diagnostic["code"], "project")
            self.assertEqual(diagnostic["primary"]["path"], "main.qli")


if __name__ == "__main__":
    unittest.main()
