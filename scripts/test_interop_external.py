#!/usr/bin/env python3
"""Independent syntax/profile smoke gates, not a translation correctness proof.

Install interop-validation-requirements.txt in a temporary virtual environment.
Pass the built interop example plus LLVM llvm-as and opt paths. No QIR execution
or external include lookup occurs. Missing validators fail, never silently skip.
"""
import argparse
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

import openqasm3
from openqasm3 import ast

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "tests/fixtures/interop"


def run(*args):
    return subprocess.run(args, check=True, capture_output=True, text=True).stdout


class ExternalFormats(unittest.TestCase):
    def emit(self, mode, path):
        return run(OPTIONS.example, mode, str(path))

    def check_qasm(self, text, expected_gates, measured_axes):
        program = openqasm3.parse(text)
        self.assertEqual(program.version, "3.0")
        gates = [s for s in program.statements if isinstance(s, ast.QuantumGate)]
        self.assertEqual([g.name.name for g in gates], expected_gates)
        resets = [s for s in program.statements if isinstance(s, ast.QuantumReset)]
        self.assertEqual(len(resets), 1)
        self.assertEqual(resets[0].qubits.name, "q")
        first_gate = min(program.statements.index(g) for g in gates)
        self.assertLess(program.statements.index(resets[0]), first_gate)
        measurements = [s for s in program.statements if isinstance(s, ast.QuantumMeasurementStatement)]
        self.assertEqual([s.measure.qubit.indices[0][0].value for s in measurements], measured_axes)
        self.assertEqual([s.target.indices[0][0].value for s in measurements], list(range(len(measured_axes))))

    def test_reference_openqasm_parser(self):
        for name in ["bell", "gates"]:
            # Parse independently authored inputs as well as the adapter output.
            openqasm3.parse((FIXTURES / f"{name}.qasm").read_text())
        self.check_qasm(self.emit("qasm-canonical", FIXTURES / "bell.qasm"), ["h", "cx"], [1, 0])
        self.check_qasm(self.emit("qasm-canonical", FIXTURES / "gates.qasm"),
                        ["h", "x", "y", "z", "s", "sdg", "t", "tdg", "cx", "cz", "swap", "ccx"], [0, 1, 2])
        self.check_qasm(self.emit("qli-to-qasm", FIXTURES / "terminal"), ["h", "cx"], [1, 0])

    def check_qir(self, text, qubits, results):
        with tempfile.TemporaryDirectory(prefix="qleisli-qir-") as directory:
            ll = Path(directory) / "module.ll"
            bc = Path(directory) / "module.bc"
            ll.write_text(text)
            run(OPTIONS.llvm_as, str(ll), "-o", str(bc))
            run(OPTIONS.opt, "-passes=verify", "-disable-output", str(bc))
        # Profile-specific checks in addition to generic LLVM validity.
        self.assertRegex(text, r"define i64 @main\(\) #0")
        self.assertEqual(re.findall(r"^(\w+):$", text, re.M), ["entry", "body", "measurements", "output"])
        self.assertEqual(re.findall(r"br label %(\w+)", text), ["body", "measurements", "output"])
        self.assertIn('"qir_profiles"="base_profile"', text)
        self.assertIn(f'"required_num_qubits"="{qubits}"', text)
        self.assertIn(f'"required_num_results"="{results}"', text)
        self.assertIn('!"qir_major_version", i32 2', text)
        self.assertIn('!"qir_minor_version", i32 0', text)
        for resource in ["qubit", "result"]:
            self.assertIn(f'!"dynamic_{resource}_management", i1 false', text)
        self.assertIn('declare void @__quantum__qis__mz__body(ptr, ptr writeonly) #1', text)
        self.assertIn('attributes #1 = { "irreversible" }', text)
        labels = re.findall(r'c"([^"\n]+)\\00"', text)
        self.assertEqual(len(labels), results + 1)
        self.assertEqual(len(set(labels)), len(labels))
        recorded = re.findall(r'call void @__quantum__rt__\w+_record_output\([^\n]+, ptr @label\.(\d+)\)', text)
        self.assertEqual(recorded, [str(i) for i in range(results + 1)])
        for block in ["entry", "body"]:
            block_text = text.split(f"{block}:\n", 1)[1].split("  br label", 1)[0]
            self.assertNotIn("mz__body", block_text)
        self.assertIn("ret i64 0", text)

    def test_standard_llvm_and_qir_structure(self):
        self.check_qir(self.emit("qasm-to-qir", FIXTURES / "bell.qasm"), 2, 2)
        self.check_qir(self.emit("qasm-to-qir", FIXTURES / "gates.qasm"), 3, 3)
        self.check_qir(self.emit("qli-to-qir", FIXTURES / "terminal"), 2, 2)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "empty.qasm"
            path.write_text("OPENQASM 3.0;")
            self.check_qir(self.emit("qasm-to-qir", path), 0, 0)

    def test_example_rejects_atomically(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "bad.qasm"
            path.write_text('OPENQASM 3.0; include "stdgates.inc"; qubit q; reset q; measure q; x q;')
            result = subprocess.run([OPTIONS.example, "qasm-to-qir", str(path)], capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, b"")
            self.assertIn(b"Unsupported", result.stderr)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("example")
    parser.add_argument("--llvm-as", default="llvm-as")
    parser.add_argument("--opt", default="opt")
    OPTIONS, remaining = parser.parse_known_args()
    unittest.main(argv=[__file__, *remaining])
