#!/usr/bin/env python3
"""Check source-runner failures, input binding and shared command coverage.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import contextlib
import base64
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import ci_source_checks as checks


class SourceChecksTests(unittest.TestCase):
    def test_rust_producer_first_sources_remain_inert_and_exact(self):
        stored = (checks.ROOT / 'tests/fixtures/authoring_sessions/ci-rust-parallel-v030/producer-first.json.gz').read_bytes()
        self.assertEqual(hashlib.sha256(stored).hexdigest(),
                         '21f0923fb5085bc4b2f078b4e854ab078568d475bbb1fd72d313caa88e5308f0')
        with gzip.GzipFile(fileobj=io.BytesIO(stored)) as archive:
            raw = archive.read(176612)
        self.assertEqual(len(raw), 176611)
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
                         '88ac50deea06e1ea1fd278dac3ff202c4b57adcac4aa16de985ec5d8ecd517cc')
        first = json.loads(raw)
        self.assertEqual((first['format'], first['version'], first['head']),
                         ('qleisli.inert-rust-producer-first', 1,
                          '11745e6884cc0775f47cfceb6bcfd2a8cdb4f9a3'))
        self.assertEqual(len(first['records']), 9)
        self.assertEqual({row['path'] for row in first['records']}, {
            '.github/workflows/ci.yml', '.github/actions/rust-suite/action.yml',
            '.github/actions/source-check/action.yml', '.github/actions/release-receipt/action.yml',
            '.github/ci/source-checks.json', 'scripts/check_rust_test_partition.py',
            'scripts/ci_source_checks.py', 'scripts/ci_profiles.py', 'scripts/check_release_ready.py'})
        for row in first['records']:
            data = base64.b64decode(row['base64'], validate=True)
            self.assertEqual((len(data), hashlib.sha256(data).hexdigest()), (row['bytes'], row['sha256']))
            self.assertIn(row['mode'], (0o644, 0o755))

    def test_partitioned_plans_keep_fresh_preparation_and_explicit_omissions(self):
        for group in ('rust-latest', 'rust-msrv'):
            full = checks.describe(group)
            selected = []
            for part in ('differential', 'remaining'):
                spec = checks.describe(group, partition=part)
                self.assertEqual(spec['preparation_commands'], 3)
                self.assertEqual(spec['commands'][:3], checks.plan('native-runtime'))
                self.assertEqual(spec['tools'], full['tools'])
                self.assertEqual(spec['environment'], full['environment'])
                self.assertEqual(spec['timeout_seconds'], 3600)
                info = spec['partition']
                self.assertEqual(info['name'], part)
                self.assertEqual(info['full_commands'], checks.definition(group)['commands'])
                self.assertEqual(sorted(info['selected_indices'] + info['omitted_indices']),
                                 list(range(len(info['full_commands']))))
                self.assertEqual(spec['commands'][3:],
                                 [info['full_commands'][i] for i in info['selected_indices']])
                selected.extend(info['selected_indices'])
            self.assertEqual(sorted(selected), list(range(len(full['commands']) - 3)))
        for group in ('source-integrity', 'source-contracts', 'native-runtime'):
            with self.assertRaisesRegex(ValueError, 'producer partition'):
                checks.plan(group, partition='remaining')

    def test_ci_preflight_keeps_hosted_checks_and_precedes_heavy_builds(self):
        commands = checks.plan('ci-preflight')
        self.assertEqual(commands, [['python3', 'scripts/' + name + '.py'] for name in (
            'check_whitespace', 'test_check_whitespace', 'test_check_pr_size',
            'test_check_fixture_budget', 'test_check_fixture_references',
            'test_ci_profiles', 'test_ci_source_checks', 'test_ci_rust_producers', 'test_ci_rust_artifacts', 'test_rust_test_partition',
            'test_run_rust_tests', 'test_native_verification_scheduler', 'test_ci_actions',
            'test_refresh_current_proof_records', 'test_check_release_ready',
            'test_measure_ci', 'test_run_native_ci', 'test_native_driver_bundle', 'test_package_lean_kernel',
            'test_archive_lean_kernel', 'test_run_kernel_tests')])
        workflow = (checks.ROOT / '.github/workflows/ci.yml').read_text()
        changes = workflow.split('  changes:\n')[1].split('  check-rust:\n')[0]
        self.assertIn('--checks ci-preflight --output', changes)
        self.assertIn('${{ runner.temp }}/ci-preflight/', changes)
        self.assertLess(changes.index('--checks ci-preflight'), changes.index('id: select'))
        # The complete-tree check is part of local plans, not a late inline job.
        self.assertNotIn('git diff --check', workflow)

    def test_partitioned_execution_reports_only_its_selected_commands(self):
        for part in ('differential', 'remaining'):
            with self.subTest(part=part), tempfile.TemporaryDirectory() as directory:
                output = Path(directory) / 'out'
                log = Path(directory) / 'command.log'; log.write_text('synthetic command result')
                def result(task, *_args):
                    return dict(status='passed', log=str(log), commands=[])
                with (patch.object(checks, 'snapshot', return_value=dict(head='bound-source')),
                      patch.dict(checks.os.environ, {'GITHUB_SHA': 'bound-source'}),
                      patch.object(checks, 'digest', return_value='bound-bytes'),
                      patch.object(checks, 'toolchain', return_value={}),
                      patch.object(checks.ci_runtime, 'run_task', side_effect=result) as run,
                      contextlib.redirect_stdout(io.StringIO())):
                    self.assertEqual(checks.execute('rust-latest', None, output, partition=part), 0)
                report = json.loads((output / 'results.json').read_text())
                expected = checks.plan('rust-latest', partition=part)
                self.assertEqual([row['argv'] for row in report['commands']], expected)
                self.assertEqual(run.call_count, len(expected))
                info = report['plan']['partition']
                self.assertEqual(info['name'], part)
                self.assertTrue(info['omitted_indices'])
                self.assertFalse(set(info['selected_indices']) & set(info['omitted_indices']))

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
            ['python3', 'scripts/test_execution_view_encoding.py'],
            ['python3', 'scripts/test_engineering_pure_tensor_native.py', '--baseline-only'],
            ['python3', 'scripts/test_engineering_openqasm_native.py', '--baseline-only'],
            ['python3', 'scripts/test_public_effects_first.py'],
            ['python3', 'scripts/test_stdlib_boundary_first.py'],
            ['python3', 'scripts/test_empty_basis_first.py'],
            ['python3', 'scripts/test_generic_dormant_first.py'],
            ['python3', 'scripts/test_native_edition_first.py'],
            ['python3', 'scripts/test_prelude_first.py'],
            ['python3', 'scripts/test_finite_adts_first.py'],
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
            start = spec['preparation_commands'] + (group == 'rust-latest')
            self.assertEqual(commands[start],
                             ['python3', 'scripts/check_rust_test_partition.py', '--group', group])
            import check_rust_test_partition as partition
            heavy, rest = partition.selection(group, checks.definition(group)['commands'])
            self.assertEqual(heavy, ['frontend_ownership_differential', 'source_ir_correspondence'])
            self.assertEqual(len(rest), 121)
            self.assertTrue(all(argv[:3] == ['python3', 'scripts/run_kernel_tests.py', '--']
                                for argv in (commands[start + 1], commands[start + 3])))
        with patch.object(checks, 'definition', return_value={'prepare': ['loop']}):
            with self.assertRaisesRegex(ValueError, 'cyclic'):
                checks.describe('loop')

    def test_tool_mismatch_refuses_commands_and_retains_unexecuted_plan(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'out'
            with (patch.object(checks, 'snapshot', return_value=dict(head='a')),
                  patch.dict(checks.os.environ, {'GITHUB_SHA': 'a'}),
                  patch.object(checks, 'toolchain', side_effect=ValueError('toolchain mismatch')),
                  patch.object(checks.ci_runtime, 'run_task') as run):
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
                  patch.object(checks.ci_runtime, 'run_task') as run):
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
        # Move exactly one policy regression earlier; keep every prior command.
        release = ['python3', 'scripts/test_check_release_ready.py']
        self.assertNotIn(release, commands)
        self.assertEqual(checks.plan('ci-preflight').count(release), 1)
        prior = commands[:8] + [release] + commands[8:]
        # Bind the exact prior coverage and order, independent of the manifest.
        import hashlib
        self.assertEqual(len(commands), 33)
        self.assertEqual(hashlib.sha256(json.dumps(prior).encode()).hexdigest(),
                         'ad1d29d1bdf9374234a3357e304041b4aaeae64a08a9138b326103079768e254')
        workflow = (checks.ROOT / '.github/workflows/ci.yml').read_text()
        self.assertIn('group: repository-integrity', workflow)
        self.assertIn('uses: ./.github/actions/source-check', workflow)
        self.assertIn('scripts/check_constitution.py "${base_args[@]}"', workflow)

    def test_shared_contract_commands_preserve_both_existing_consumers(self):
        commands = checks.plan('source-contracts', Path('/selected/qleisli'))
        self.assertEqual(sum(argv[0] == '/selected/qleisli' for argv in commands), 2)
        self.assertEqual(commands[2], ['python3', 'scripts/current_source_fixtures.py',
                                      '--check', '/selected/qleisli',
                                      'tests/fixtures/lean_phase_layout/first_source'])
        self.assertEqual({argv[1] for argv in commands if argv[0] == 'python3'}, {
            'scripts/current_source_fixtures.py',
            'scripts/test_lean_phase_layout.py', 'scripts/test_lean_interference.py',
            'scripts/test_lean_qft.py', 'scripts/test_lean_qpe.py',
            'scripts/test_lean_controlled_power.py', 'scripts/test_cli_json.py',
            'scripts/test_public_effects.py'})
        workflow = (checks.ROOT / '.github/workflows/ci.yml').read_text()
        self.assertEqual(workflow.count('uses: ./.github/actions/rust-producer'), 4)
        producer = (checks.ROOT / '.github/actions/rust-producer/action.yml').read_text()
        self.assertEqual(producer.count('uses: ./.github/actions/rust-suite'), 1)
        shared = (checks.ROOT / '.github/actions/rust-suite/action.yml').read_text()
        self.assertEqual(shared.count('group: source-contracts\n        compiler: target/debug/qleisli'), 1)
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
            failed = dict(status='timed-out', log=str(log), error='command exceeded 3600 seconds', commands=[])
            stderr = io.StringIO()
            with (patch.object(checks, 'snapshot', return_value=dict(head='a')),
                    patch.dict(checks.os.environ, {'GITHUB_SHA': 'a'}),
                    patch.object(checks, 'plan', return_value=commands),
                    patch.object(checks, 'toolchain', return_value={}),
                    patch.object(checks.ci_runtime, 'run_task', return_value=failed),
                    contextlib.redirect_stderr(stderr)):
                self.assertEqual(checks.execute('source-integrity', None, output), 1)
            self.assertIn('command exceeded 3600 seconds', stderr.getvalue())
            self.assertIn('actual failure', stderr.getvalue())
            report = json.loads((output / 'results.json').read_text())
            self.assertEqual([row['status'] for row in report['commands']], ['timed-out', 'not-run'])
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

    def test_failed_partition_or_guard_cannot_credit_later_rust_checks(self):
        commands = checks.plan('rust-latest')
        guard = ['python3', 'scripts/check_rust_test_partition.py', '--group', 'rust-latest']
        guard_indices = [index for index, command in enumerate(commands) if command == guard]
        self.assertEqual(len(guard_indices), 2)
        for failure_at in [*guard_indices, *(index + 1 for index in guard_indices)]:
            with self.subTest(failure_at=failure_at), tempfile.TemporaryDirectory() as directory:
                output = Path(directory) / 'out'
                log = Path(directory) / 'command.log'; log.write_text('actual retained failure')
                def result(task, *_args):
                    return dict(status='failed' if int(task['id']) == failure_at else 'passed',
                                error='partition or inventory failed' if int(task['id']) == failure_at else None,
                                log=str(log), commands=[])
                with (patch.object(checks, 'snapshot', return_value=dict(head='bound-source')),
                      patch.dict(checks.os.environ, {'GITHUB_SHA': 'bound-source'}),
                      patch.object(checks, 'digest', return_value='bound-bytes'),
                      patch.object(checks, 'toolchain', return_value={}),
                      patch.object(checks.ci_runtime, 'run_task', side_effect=result) as run,
                      contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO())):
                    self.assertEqual(checks.execute('rust-latest', None, output), 1)
                self.assertEqual(run.call_count, failure_at + 1)
                report = json.loads((output / 'results.json').read_text())
                self.assertEqual([row['argv'] for row in report['commands']], commands)
                self.assertEqual(report['status'], 'failed')
                self.assertTrue(all(row['status'] == 'not-run' for row in report['commands'][failure_at + 1:]))


if __name__ == '__main__':
    unittest.main()
