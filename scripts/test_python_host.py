"""Host isolation/JSON regressions, including installations without optional LLVM.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import io
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
from qleisli import Client, Program, QleisliError
from qleisli.__main__ import main as cli


class HostBoundary(unittest.TestCase):
    def test_edition_is_required_concrete_and_never_selected_by_process(self):
        with patch.object(Client, '_process') as invoke:
            with self.assertRaises(TypeError):
                Client('unused')
            for value in (None, '', 'latest', 'current', '*', '2027', 2026, True):
                with self.subTest(edition=value), self.assertRaises(ValueError):
                    Client('unused', edition=value)
            invoke.assert_not_called()

    def test_program_retains_edition_when_client_selection_is_changed(self):
        client = Client('unused', edition='2026')
        with self.assertRaises(AttributeError):
            client.edition = '2027'
        # An untrusted host object is not a native acceptance receipt.
        program = Program(client, b'{}', '2026')
        with self.assertRaises(AttributeError):
            program.edition = '2027'
        client._edition = '2027'
        with patch.object(client, '_process') as invoke, self.assertRaises(QleisliError) as failure:
            program.check()
        self.assertEqual(failure.exception.diagnostics[0]['code'], 'edition')
        invoke.assert_not_called()

    def test_source_expectation_and_raw_selection_are_distinct_arguments(self):
        client = Client('unused', edition='2026')
        calls = []

        def exchange(args, data=None):
            calls.append(args)
            document = dict(format='qleisli.result', version=1, command='interop ' + args[2],
                            outcome='ok', diagnostics=[], result=dict(text='{}'))
            return subprocess.CompletedProcess(args, 0, json.dumps(document).encode(), b'')

        # These fabricated replies test transport arguments, not acceptance.
        with patch.object(client, '_process', side_effect=exchange):
            raw = client.from_openqasm('untrusted text')
            source = client.compile_project(ROOT)
        self.assertIn('--edition=2026', calls[0])
        self.assertNotIn('--expect-edition=2026', calls[0])
        self.assertIn('--expect-edition=2026', calls[1])
        self.assertNotIn('--edition=2026', calls[1])
        self.assertEqual((raw.edition, source.edition), ('2026', '2026'))

    def test_host_cli_requires_an_explicit_supported_edition(self):
        for flags in ([], ['--edition=latest'], ['--edition=2027']):
            process = subprocess.run([sys.executable, '-m', 'qleisli', 'unused',
                                      '--input=qasm', *flags],
                                     env=os.environ | {'PYTHONPATH': str(ROOT / 'python')},
                                     capture_output=True, timeout=30)
            self.assertEqual(process.returncode, 2, process.stderr)
            self.assertIn(b'--edition', process.stderr)
            self.assertEqual(process.stdout, b'')

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
                                        Client(timeout=1, edition="2026")._process(args, b'x' * 131072)
                                    self.assertEqual(failure.exception.diagnostics[0]['code'], 'limit')
                                else:
                                    result = Client(timeout=1, edition="2026")._process(args)
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
        client = Client('unused', edition="2026")
        # Fabricated transport data tests envelope parsing only. It supplies
        # neither a native acceptance decision nor checker identity authority.
        scope = dict(checker_path='/test/selected-checker', checker_identity='unpinned',
                     ordinary_result_checked=False, runtime_result_checked=False,
                     request_checked=False, source_preservation_verified=False)
        valid = dict(format='qleisli.result', version=1, command='interop check',
                     outcome='ok', diagnostics=[], result=scope)
        def response(data):
            return patch.object(client, '_process', return_value=
                                subprocess.CompletedProcess([], 0, data.encode(), b''))
        with response(json.dumps(valid)):
            self.assertEqual(client._call('check', 'qirf', edition="2026"), scope)
        malformed = [json.dumps(valid | {'version': version}) for version in (True, 1.0, '1', 0, 2, None)]
        malformed += [json.dumps(valid).replace('"version": 1', '"version": 2, "version": 1'),
                      json.dumps(valid).replace('"request_checked": false', '"request_checked": true, "request_checked": false'),
                      json.dumps(valid).replace('"request_checked": false', '"request_checked": NaN'),
                      json.dumps(valid).replace('"request_checked": false', '"request_checked": 1e999'),
                      '[' * 3000 + '0' + ']' * 3000]
        for data in malformed:
            with self.subTest(data=data), response(data), self.assertRaises(QleisliError) as failure:
                client._call('check', 'qirf', edition="2026")
            self.assertEqual(failure.exception.diagnostics[0]['code'], 'connection')
        for data in ['{"qasm":"first","qasm":"second"}', '{"qasm":"text","bad":Infinity}']:
            with response(data), self.assertRaises(QleisliError) as failure:
                client.from_qir(b'not LLVM')
            self.assertEqual(failure.exception.diagnostics[0]['code'], 'qir')

    def test_malformed_action_results_fail_in_the_library_and_json_cli(self):
        client = Client('unused', edition='2026')
        program = Program(client, b'{}', '2026')
        cases = [
            ('check', {}, lambda: client.from_ir(b'{}')),
            ('emit-ir', {}, lambda: client.from_openqasm('OPENQASM 3.0;')),
            ('emit-ir', {'text': 2}, lambda: client.compile_project(ROOT)),
            ('run', {'distribution': [{'bits': [1], 'probability': 1}]}, program.run),
            ('sample', {'shots': []}, lambda: program.sample(shots=1, seed=0)),
        ]
        for action, payload, call in cases:
            document = dict(format='qleisli.result', version=1, command=f'interop {action}',
                            outcome='ok', diagnostics=[], result=payload)
            response = subprocess.CompletedProcess([], 0, json.dumps(document).encode(), b'')
            args = ['qleisli', '.', '--input=qli', '--edition=2026', '--action=' + action]
            if action == 'sample':
                args += ['--shots=1', '--seed=0']
            with self.subTest(action=action, payload=payload), patch.object(Client, '_process', return_value=response):
                with self.assertRaises(QleisliError) as failure:
                    call()
                self.assertEqual(failure.exception.diagnostics[0]['code'], 'connection')
                with patch.object(sys, 'argv', args), patch('sys.stdout', new_callable=io.StringIO) as output:
                    self.assertEqual(cli(), 1)
                    error = json.loads(output.getvalue())
                self.assertEqual((error['outcome'], error['result'], error['diagnostics'][0]['code']),
                                 ('error', None, 'project'))

    def test_reader_is_bound_to_imported_installation(self):
        client = Client(str(ROOT / "target/debug/qleisli"), edition="2026")
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
                    "--input=" + kind, "--edition=2026", "--executable=" + str(root / "missing-executable")],
                    env=os.environ | {"PYTHONPATH": str(ROOT / "python")}, capture_output=True, timeout=30)
                self.assertEqual(process.returncode, 1, process.stderr)
                result = json.loads(process.stdout)
                self.assertEqual(result["diagnostics"][0]["code"], code)
                self.assertIsNone(result["result"])


if __name__ == "__main__":
    unittest.main()
