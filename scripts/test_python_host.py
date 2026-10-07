"""Host isolation/JSON regressions, including installations without optional LLVM.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "python"))
from qleisli import Client, QleisliError


class HostBoundary(unittest.TestCase):
    @unittest.skipUnless(os.name == 'posix', 'POSIX session containment')
    def test_process_completion_reclaims_descendants_in_separate_groups(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            child = ('import os,pathlib,sys,time; '
                     'pathlib.Path(sys.argv[1]).write_text(str(os.getpid())); time.sleep(10)')
            parent = ('import pathlib,subprocess,sys,time; '
                      'subprocess.Popen([sys.executable,"-c",sys.argv[1],sys.argv[2]], '
                      'process_group=0,stdin=subprocess.DEVNULL,stdout=None if sys.argv[3]=="pipes" else subprocess.DEVNULL,stderr=subprocess.DEVNULL); '
                      '\nwhile not pathlib.Path(sys.argv[2]).exists(): time.sleep(.005)\n'
                      'time.sleep(10) if sys.argv[3]=="wait" else None\n'
                      'sys.exit(7 if sys.argv[3]=="fail" else 0)')
            # An unrelated job must remain alive through every cleanup.
            with subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(10)']) as unrelated:
                try:
                    for case in ['ok', 'fail', 'wait', 'pipes']:
                        with self.subTest(case=case):
                            pidfile = root / case
                            started = time.monotonic()
                            try:
                                args = [sys.executable, '-c', parent, child, str(pidfile), case]
                                if case in ['wait', 'pipes']:
                                    with self.assertRaises(QleisliError) as failure:
                                        Client(timeout=1)._process(args, b'x' * 131072)
                                    self.assertEqual(failure.exception.diagnostics[0]['code'], 'limit')
                                else:
                                    result = Client(timeout=1)._process(args)
                                    self.assertEqual(result.returncode, 7 if case == 'fail' else 0)
                                self.assertLess(time.monotonic() - started, 4)
                                pid = int(pidfile.read_text())
                                deadline = time.monotonic() + 1
                                while True:
                                    state = subprocess.run(['ps', '-p', str(pid), '-o', 'stat='],
                                        capture_output=True, text=True, timeout=1)
                                    self.assertFalse(state.stderr, state.stderr)
                                    if not state.stdout.strip() or state.stdout.lstrip().startswith('Z'):
                                        break
                                    self.assertLess(time.monotonic(), deadline, state.stdout)
                                    time.sleep(.005)
                                self.assertIsNone(unrelated.poll())
                            finally:
                                if pidfile.exists():
                                    try:
                                        os.kill(int(pidfile.read_text()), 9)
                                    except ProcessLookupError:
                                        pass
                finally:
                    unrelated.kill()
                    unrelated.wait()

    def test_malformed_json_response_cannot_become_host_success(self):
        client = Client('unused')
        valid = dict(format='qleisli.result', version=1, command='interop check',
                     outcome='ok', diagnostics=[], result={'verified': True})
        def response(data):
            return patch.object(client, '_process', return_value=
                                subprocess.CompletedProcess([], 0, data.encode(), b''))
        with response(json.dumps(valid)):
            self.assertEqual(client._call('check', 'qirf'), {'verified': True})
        malformed = [json.dumps(valid | {'version': version}) for version in (True, 1.0, '1', 0, 2, None)]
        malformed += [json.dumps(valid).replace('"version": 1', '"version": 2, "version": 1'),
                      json.dumps(valid).replace('"verified": true', '"verified": false, "verified": true'),
                      json.dumps(valid).replace('"verified": true', '"probability": NaN'),
                      json.dumps(valid).replace('"verified": true', '"probability": 1e999'),
                      '[' * 3000 + '0' + ']' * 3000]
        for data in malformed:
            with self.subTest(data=data), response(data), self.assertRaises(QleisliError) as failure:
                client._call('check', 'qirf')
            self.assertEqual(failure.exception.diagnostics[0]['code'], 'connection')
        for data in ['{"qasm":"first","qasm":"second"}', '{"qasm":"text","bad":Infinity}']:
            with response(data), self.assertRaises(QleisliError) as failure:
                client.from_qir(b'not LLVM')
            self.assertEqual(failure.exception.diagnostics[0]['code'], 'qir')

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
