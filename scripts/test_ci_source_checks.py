#!/usr/bin/env python3
"""Check source-runner failures, input binding and shared command coverage.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import ci_source_checks as checks


class SourceChecksTests(unittest.TestCase):
    def test_linked_inventory_identities_precede_heavy_lane_scheduling(self):
        commands = checks.plan('source-integrity')
        self.assertEqual(commands[:2], [
            ['python3', 'scripts/check_verification_inventory.py'],
            ['python3', 'scripts/check_production_coverage.py'],
        ])
        self.assertEqual(commands[2:], [
            ['python3', 'scripts/check_input_corpus.py'],
            ['python3', 'scripts/test_current_source_fixtures.py'],
            ['python3', 'scripts/test_observation_sources.py'],
        ])
        later = checks.plan('repository-integrity')
        self.assertIn(['python3', 'scripts/test_check_production_coverage.py'], later)
        self.assertIn(['python3', 'scripts/check_production_coverage.py'], later)

    def test_preparation_precedes_consumers_and_binds_toolchains(self):
        for group in ('rust-latest', 'rust-msrv'):
            spec = checks.describe(group)
            commands = checks.plan(group)
            self.assertEqual(commands[:3], checks.plan('native-runtime'))
            self.assertEqual(spec['preparation_commands'], 3)
            self.assertIn('lean', spec['tools'])
            self.assertIn('QLEISLI_KERNEL', spec['environment'])
            self.assertIn('--all-targets', commands[spec['preparation_commands'] + (group == 'rust-latest')])
        with patch.object(checks, 'definition', return_value={'prepare': ['loop']}):
            with self.assertRaisesRegex(ValueError, 'cyclic'):
                checks.describe('loop')

    def test_tool_mismatch_refuses_commands_and_retains_unexecuted_plan(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'out'
            with (patch.object(checks, 'snapshot', return_value=dict(head='a')),
                  patch.dict(checks.os.environ, {'GITHUB_SHA': 'a'}),
                  patch.object(checks, 'toolchain', side_effect=ValueError('toolchain mismatch')),
                  patch.object(checks.run_native_ci, 'run_task') as run):
                self.assertEqual(checks.execute('source-integrity', None, output), 1)
                run.assert_not_called()
            report = json.loads((output / 'results.json').read_text())
            self.assertEqual(report['status'], 'failed')
            self.assertEqual(report['error'], 'toolchain mismatch')
            self.assertTrue(all(row['status'] == 'not-run' for row in report['commands']))

    def test_event_commit_mismatch_refuses_tool_probes_and_commands(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'out'
            with (patch.object(checks, 'snapshot', return_value=dict(head='a')),
                  patch.dict(checks.os.environ, {'GITHUB_SHA': 'b'}),
                  patch.object(checks, 'toolchain') as probe,
                  patch.object(checks.run_native_ci, 'run_task') as run):
                self.assertEqual(checks.execute('source-integrity', None, output), 1)
                probe.assert_not_called()
                run.assert_not_called()
            report = json.loads((output / 'results.json').read_text())
            self.assertEqual(report['error'], 'source checks differ from the exact event commit')
            self.assertTrue(all(row['status'] == 'not-run' for row in report['commands']))

    def test_tool_versions_are_checked_without_installing(self):
        spec = dict(tools={'python': dict(command=['python3', '--version'], pattern=r'Python 3\.11\.[0-9]+')})
        for version, code, accepted in [('Python 3.11.15', 0, True), ('Python 3.10.2', 0, False), ('Python 3.11.15', 1, False)]:
            with patch.object(checks.subprocess, 'run', return_value=subprocess.CompletedProcess([], code, version, '')):
                if accepted:
                    self.assertEqual(checks.toolchain(spec, {})['python']['version'], version)
                else:
                    with self.assertRaisesRegex(ValueError, 'toolchain mismatch'):
                        checks.toolchain(spec, {})

    def test_repository_checks_keep_prior_coverage_and_separate_continuity(self):
        commands = checks.plan('repository-integrity')
        # Bind the exact prior command coverage, independent of the manifest.
        import hashlib
        self.assertEqual(len(commands), 34)
        self.assertEqual(hashlib.sha256(json.dumps(commands).encode()).hexdigest(),
                         'ad1d29d1bdf9374234a3357e304041b4aaeae64a08a9138b326103079768e254')
        workflow = (checks.ROOT / '.github/workflows/ci.yml').read_text()
        self.assertIn('--checks repository-integrity --output', workflow)
        self.assertIn('scripts/check_constitution.py "${base_args[@]}"', workflow)

    def test_shared_contract_commands_preserve_both_existing_consumers(self):
        commands = checks.plan('source-contracts', Path('/selected/qleisli'))
        self.assertEqual(sum(argv[0] == '/selected/qleisli' for argv in commands), 3)
        self.assertEqual({argv[1] for argv in commands if argv[0] == 'python3'}, {
            'scripts/test_lean_phase_layout.py', 'scripts/test_lean_interference.py',
            'scripts/test_lean_qft.py', 'scripts/test_lean_qpe.py',
            'scripts/test_lean_controlled_power.py', 'scripts/test_cli_json.py'})
        workflow = (checks.ROOT / '.github/workflows/ci.yml').read_text()
        self.assertEqual(workflow.count('--checks source-contracts --compiler target/debug/qleisli'), 2)
        for group, compiler in [('absent', None), ('source-contracts', None)]:
            with self.assertRaises(ValueError): checks.plan(group, compiler)

    def test_input_binding_detects_unstaged_untracked_and_deleted_files(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def git(*args):
                subprocess.run(['git', '-c', 'user.name=Test', '-c', 'user.email=test@example.invalid',
                                '-c', 'commit.gpgsign=false', *args], cwd=root, check=True,
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            git('init'); (root / 'source').write_text('original'); git('add', 'source'); git('commit', '-m', 'baseline')
            initial = checks.snapshot(root)
            (root / 'source').write_text('changed')
            self.assertNotEqual(initial, checks.snapshot(root))
            (root / 'source').write_text('original')
            self.assertEqual(initial, checks.snapshot(root))
            (root / 'new').write_text('first source')
            added = checks.snapshot(root)
            self.assertNotEqual(initial, added)
            (root / 'new').write_text('modified first source')
            self.assertNotEqual(added, checks.snapshot(root))
            (root / 'source').unlink()
            self.assertNotEqual(initial, checks.snapshot(root))

    def test_failure_preserves_unexecuted_commands_and_never_overwrites_results(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); output = root / 'out'
            commands = [['python3', 'first.py'], ['python3', 'second.py']]
            log = root / 'failed.log'; log.write_text('actual failure')
            failed = dict(status='failed', log=str(log), error='exit 2', commands=[])
            with (patch.object(checks, 'snapshot', return_value=dict(head='a')),
                    patch.dict(checks.os.environ, {'GITHUB_SHA': 'a'}),
                    patch.object(checks, 'plan', return_value=commands),
                    patch.object(checks, 'toolchain', return_value={}),
                    patch.object(checks.run_native_ci, 'run_task', return_value=failed)):
                self.assertEqual(checks.execute('source-integrity', None, output), 1)
            report = json.loads((output / 'results.json').read_text())
            self.assertEqual([row['status'] for row in report['commands']], ['failed', 'not-run'])
            before = (output / 'results.json').read_bytes()
            with self.assertRaises(FileExistsError): checks.execute('source-integrity', None, output)
            self.assertEqual((output / 'results.json').read_bytes(), before)

    def test_preflight_failure_still_has_a_failed_report(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'out'
            self.assertEqual(checks.execute('missing', None, output), 1)
            report = json.loads((output / 'results.json').read_text())
            self.assertEqual(report['status'], 'failed')
            self.assertIn('unknown source-check group', report['error'])


if __name__ == '__main__':
    unittest.main()
