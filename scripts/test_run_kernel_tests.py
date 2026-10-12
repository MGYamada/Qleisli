#!/usr/bin/env python3
"""Exercise native skip enforcement against subprocess test-harness output.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import os
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parent.parent


class NativeTestGateTests(unittest.TestCase):
    def test_original_launch_and_missing_kernel_diagnostics_are_retained(self):
        record = json.loads((ROOT / 'tests/fixtures/verification_v029/kernel-test-gating/baseline.json').read_text())
        original = record['first_observation']
        self.assertEqual(hashlib.sha256((ROOT / original['path']).read_bytes()).hexdigest(), original['sha256'])
        decoded = []
        for row in record['logs']:
            packed = (ROOT / row['path']).read_bytes()
            self.assertEqual(hashlib.sha256(packed).hexdigest(), row['sha256'])
            data = gzip.decompress(packed)
            self.assertEqual(len(data), row['raw_bytes'])
            self.assertEqual(hashlib.sha256(data).hexdigest(), row['raw_sha256'])
            decoded.append(data.decode())
        self.assertIn('no such command: `+1.98.1`', decoded[0])
        self.assertIn('select the matching Lean checker', decoded[1])
        self.assertIn('src/lib.rs - (line 17) ... FAILED', decoded[1])
        self.assertIn('1 passed; 0 failed; 0 ignored;', decoded[2])

    def invoke(self, output, status=0, kernel=sys.executable):
        # The child supplies harness observations, not a simulated checker decision.
        command = [sys.executable, str(ROOT / 'scripts/run_kernel_tests.py'), '--',
                   sys.executable, '-c', f'print({output!r}); raise SystemExit({status})']
        return subprocess.run(command, env=os.environ | {'QLEISLI_KERNEL': kernel},
                              capture_output=True, text=True)

    def test_native_tests_pass_and_separate_stress_ignore_is_allowed(self):
        result = self.invoke('test stress ... ignored, historical stress\n'
                             'test native ... ok\n'
                             'test result: ok. 1 passed; 0 failed; 1 ignored;')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('zero conditional native skips', result.stdout)

    def test_conditional_ignore_fails_even_with_a_successful_harness(self):
        result = self.invoke('test native ... ignored, native-kernel gate: requires QLEISLI_KERNEL\n'
                             'test result: ok. 1 passed; 0 failed; 1 ignored;')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('conditional native tests were skipped', result.stderr)

    def test_missing_or_invalid_selection_refuses_to_start_the_command(self):
        for kernel in ('', '/missing-explicit-native-checker'):
            with self.subTest(kernel=kernel):
                result = self.invoke('child must not run', kernel=kernel)
                self.assertNotEqual(result.returncode, 0)
                self.assertNotIn('child must not run', result.stdout)

    def test_native_failure_is_not_replaced_by_a_successful_other_target(self):
        result = self.invoke('test result: ok. 7 passed; 0 failed; 0 ignored;', status=101)
        self.assertEqual(result.returncode, 101)

    def test_zero_test_selection_cannot_supply_coverage(self):
        result = self.invoke('test result: ok. 0 passed; 0 failed; 0 ignored;')
        self.assertNotEqual(result.returncode, 0)

    def test_unrecognized_output_does_not_supply_a_passing_summary(self):
        result = self.invoke('all tests supposedly passed')
        self.assertNotEqual(result.returncode, 0)

    def test_shared_ci_commands_enforce_native_skip_checks(self):
        import ci_source_checks
        for group in ('rust-latest', 'rust-msrv'):
            commands = ci_source_checks.plan(group)
            tests = [argv for argv in commands if 'test' in argv]
            self.assertTrue(tests)
            for command in tests:
                self.assertEqual(command[:3], ['python3', 'scripts/run_kernel_tests.py', '--'])


if __name__ == '__main__':
    unittest.main()
