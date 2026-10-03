"""Host isolation/JSON regressions, including installations without optional LLVM.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "python"))
from qleisli import Client, QleisliError


class HostBoundary(unittest.TestCase):
    def test_reader_is_bound_to_imported_installation(self):
        client = Client(str(ROOT / "target/debug/qleisli"))
        with self.assertRaises(QleisliError) as original:
            client.from_qir(b"not LLVM")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "qleisli").mkdir()
            (root / "qleisli/__init__.py").write_text("")
            (root / "qleisli/_qir.py").write_text("from pathlib import Path; Path('executed').touch(); raise SystemExit(91)")
            previous = Path.cwd()
            try:
                os.chdir(root)
                with self.assertRaises(QleisliError) as actual:
                    client.from_qir(b"not LLVM")
                self.assertEqual(actual.exception.diagnostics, original.exception.diagnostics)
                self.assertFalse((root / "executed").exists())
            finally:
                os.chdir(previous)

    def test_host_cli_translates_transport_and_reader_errors_to_v1(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "input.qasm"
            source.write_text("OPENQASM 3.0;")
            for path, kind, code in [(root / "missing", "qasm", "project"),
                                     (source, "qasm", "project"), (source, "qir", "unsupported")]:
                process = subprocess.run([sys.executable, "-m", "qleisli", str(path),
                    "--input=" + kind, "--executable=" + str(root / "missing-executable")],
                    env=os.environ | {"PYTHONPATH": str(ROOT / "python")}, capture_output=True, timeout=30)
                self.assertEqual(process.returncode, 1, process.stderr)
                result = json.loads(process.stdout)
                self.assertEqual(result["diagnostics"][0]["code"], code)
                self.assertIsNone(result["result"])


if __name__ == "__main__":
    unittest.main()
