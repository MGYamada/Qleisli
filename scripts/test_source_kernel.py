#!/usr/bin/env python3
"""Small public source/native coverage, including libraries and unused bodies.
Curated migration regressions, not an algorithm-authoring benchmark.
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
BINARY = Path(os.environ.get('QLEISLI_BIN', ROOT/'target/debug/qleisli')).resolve()
KERNEL = Path(os.environ.get('QLEISLI_KERNEL', ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel')).resolve()
FIXTURE = ROOT/'tests/fixtures/verification_v029'


class SourceKernel(unittest.TestCase):
    def run_cli(self, action, source, kernel=None, *flags):
        command = [str(BINARY), action, str(source), '--format=json', *flags]
        if kernel:
            command.append(f'--lean-kernel={kernel}')
        result = subprocess.run(command, capture_output=True, timeout=90, cwd=ROOT)
        document = json.loads(result.stdout)
        self.assertEqual(document['outcome'], 'ok' if result.returncode == 0 else 'error')
        return result.returncode, document

    def test_library_without_entry_checks_with_native_kernel(self):
        for source in ['library', 'project', 'generic']:
            legacy = self.run_cli('check', FIXTURE/source)
            selected = self.run_cli('check', FIXTURE/source, KERNEL)
            self.assertEqual(legacy, selected)
            self.assertEqual(selected[0], 0)

    def test_retained_evidence_examples_execute_with_native_handles(self):
        # Independent expected outcomes from the examples' authored contracts.
        # Keep the source-generated DAG and source table intact (#277).
        expected = {
            'function_contracts': [True, False, True],
            'operation_contracts': [True, True],
            'operation_algorithms': [True, False, False, True],
            'iterative_phase_estimation': [True, False, False, True],
        }
        with tempfile.TemporaryDirectory(prefix='qleisli-native-evidence-') as tmp:
            for name, bits in expected.items():
                with self.subTest(example=name):
                    source = ROOT/'examples'/name
                    artifact = Path(tmp)/f'{name}.qirf'
                    code, _ = self.run_cli('emit-ir', source, KERNEL, f'--output={artifact}')
                    self.assertEqual(code, 0)
                    data = json.loads(artifact.read_bytes())
                    self.assertGreater(len(data['programs']), 1)
                    self.assertTrue(data['evidence'])
                    self.assertTrue(data['sources'])
                    self.assertEqual(self.run_cli('verify-ir', artifact, KERNEL)[0], 0)
                    code, result = self.run_cli('run', source, KERNEL)
                    self.assertEqual(code, 0)
                    distribution = result['result']['distribution']
                    probability = sum(row['probability'] for row in distribution if row['bits'] == bits)
                    self.assertAlmostEqual(probability, 1.0, delta=1e-12)

    def test_unused_body_native_rejection_blocks_every_source_action(self):
        # Interpose a rejecting checker for the unused T body; all other bodies
        # go to the real kernel. A main-only gate would incorrectly succeed.
        with tempfile.TemporaryDirectory(prefix='qleisli-source-gate-') as tmp:
            tmp = Path(tmp)
            shim = tmp/'kernel'
            shim.write_text(f'#!{sys.executable}\n' + '''import json, subprocess, sys
data = sys.stdin.buffer.read()
size = int.from_bytes(data[4:8], 'little')
artifact = json.loads(data[12:12+size])
ops = artifact['programs'][artifact['root']]['operations']
if sum(op.get('gate') == 't' for op in ops) >= 2 or sum(
        any(s['action']['tag'] == 'contract' for s in op.get('steps', [])) for op in ops) >= 2:
    print('qleisli.qirf-native 1\\nerror\\ncontract')
    sys.exit(1)
result = subprocess.run(''' + repr([str(KERNEL)]) + ''' + sys.argv[1:], input=data, capture_output=True)
sys.stdout.buffer.write(result.stdout)
sys.exit(result.returncode)
''')
            shim.chmod(0o700)
            for source in ['project', 'generic']:
                for action, flags in [('check', []), ('run', []),
                                      ('sample', ['--shots=2', '--seed=5']),
                                      ('emit-ir', [f'--output={tmp / f"{source}-ordinary.qirf"}'])]:
                    with self.subTest(action=action):
                        self.assertEqual(self.run_cli(action, FIXTURE/source, None, *flags)[0], 0)
                        # The ordinary emit created its output; use another target.
                        selected_flags = [f'--output={tmp / f"{source}-blocked.qirf"}'] if action == 'emit-ir' else flags
                        code, document = self.run_cli(action, FIXTURE/source, shim, *selected_flags)
                        self.assertNotEqual(code, 0)
                        self.assertIsNone(document['result'])
                        self.assertIn('unused_phase', document['diagnostics'][0]['message'])
                self.assertFalse((tmp/f'{source}-blocked.qirf').exists())

    def test_qrate_library_and_missing_kernel_never_fall_back(self):
        with tempfile.TemporaryDirectory(prefix='qleisli-qrate-gate-') as tmp:
            tmp = Path(tmp)
            (tmp/'src').mkdir()
            (tmp/'Qargo.toml').write_text('schema-version = 2\n[qrate]\nedition = "2026"\n[source]\nroot = "src"\n')
            (tmp/'src/library.qli').write_bytes((FIXTURE/'library/library.qli').read_bytes())
            self.assertEqual(self.run_cli('check', tmp, KERNEL, '--qrate')[0], 0)
            code, document = self.run_cli('check', tmp, tmp/'missing', '--qrate')
            self.assertNotEqual(code, 0)
            self.assertIsNone(document['result'])


if __name__ == '__main__':
    unittest.main()
