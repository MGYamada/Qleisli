#!/usr/bin/env python3
"""Check shared workflow wiring and execute its actual shell adapters locally.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import textwrap
import unittest

from ci_source_checks import describe

ROOT = Path(__file__).resolve().parents[1]


def action(name):
    return (ROOT / '.github/actions' / name / 'action.yml').read_text()


def job(name):
    workflow = (ROOT / '.github/workflows/ci.yml').read_text()
    return re.split(r'(?m)^  [a-z][a-z-]*:\n', workflow.split(f'  {name}:\n')[1])[0]


def action_step(block, name):
    steps = [step for step in re.split(r'(?m)^      - ', block)
             if f'uses: ./.github/actions/{name}\n' in step]
    if len(steps) != 1:
        raise AssertionError(f'expected one {name} caller, found {len(steps)}')
    return steps[0]


class CIActions(unittest.TestCase):
    def test_hosted_validation_covers_push_pr_completion_and_release(self):
        workflow = (ROOT / '.github/workflows/ci.yml').read_text()
        trigger = workflow.split('on:\n')[1].split('\nconcurrency:')[0]
        self.assertIn("  push:\n    branches: ['**']\n    tags: ['v*']\n", trigger)
        # Default PR events include opened, synchronize and reopened.
        self.assertIn('\n  pull_request:\n  workflow_dispatch:\n', trigger)
        self.assertIn('completion_issues:', trigger)
        self.assertIn('completion_pr:', trigger)
        self.assertIn('base: ${{ steps.select.outputs.base }}', job('changes'))
        self.assertIn('CONSTITUTION_BASE: ${{ needs.changes.outputs.base || inputs.release_base ||', job('check-docs'))
        self.assertIn('if: always()', job('required'))
        self.assertIn('group: ${{ github.workflow }}-${{ github.run_id }}', workflow)
        self.assertIn('cancel-in-progress: false', workflow)
        self.assertIn('--report "$RUNNER_TEMP/pr-size.json"', job('changes'))
        self.assertIn('--hosted --report "$RUNNER_TEMP/fixture-budget.json"', job('changes'))

    def shell(self, name, environment, code=0):
        # Execute the literal run block; GitHub inputs reach it only as env data.
        block = action(name).split('      run: |\n')[1].split('    - name:')[0]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fake = root / 'python3'
            fake.write_text(f'#!{sys.executable}\n' +
                            'import json,os,sys\n' +
                            'from pathlib import Path\n' +
                            "Path(os.environ['ARGV_RECORD']).write_text(json.dumps(sys.argv[1:]))\n" +
                            f'raise SystemExit({code})\n')
            fake.chmod(0o755)
            env = os.environ | dict(PATH=str(root) + os.pathsep + os.environ['PATH'],
                                   RUNNER_TEMP=str(root / 'temp with spaces'),
                                   ARGV_RECORD=str(root / 'argv')) | environment
            result = subprocess.run(['bash', '--noprofile', '--norc', '-eo', 'pipefail',
                                     '-c', textwrap.dedent(block)], cwd=root, env=env,
                                    capture_output=True, text=True)
            record = root / 'argv'
            return result, json.loads(record.read_text()) if record.exists() else None, env

    def traced_shell(self, name, tool, environment, fail_at=0, code=23):
        # Trace actual adapter calls, including per-child environment and the
        # shell's environment after success. A failed call must stop the block.
        block = action(name).split('      run: |\n')[1].split('    - name:')[0]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fake = root / tool
            fake.write_text(f'#!{sys.executable}\n' +
                            'import json,os,sys\n' +
                            'from pathlib import Path\n' +
                            "path=Path(os.environ['ARGV_RECORD'])\n" +
                            "rows=path.read_text().splitlines() if path.exists() else []\n" +
                            "row=dict(argv=sys.argv[1:],kernel=os.environ.get('QLEISLI_KERNEL'))\n" +
                            "with path.open('a') as stream: stream.write(json.dumps(row)+'\\n')\n" +
                            f'raise SystemExit({code} if len(rows)+1 == {fail_at} else 0)\n')
            fake.chmod(0o755)
            env = os.environ | dict(PATH=str(root) + os.pathsep + os.environ['PATH'],
                                   RUNNER_TEMP=str(root / 'temp with spaces'),
                                   ARGV_RECORD=str(root / 'argv'),
                                   PARENT_ENV_RECORD=str(root / 'parent-env')) | environment
            trailer = '\nprintf "%s" "${QLEISLI_KERNEL-}" > "$PARENT_ENV_RECORD"\n'
            result = subprocess.run(['bash', '--noprofile', '--norc', '-eo', 'pipefail',
                                     '-c', textwrap.dedent(block) + trailer], cwd=root, env=env,
                                    capture_output=True, text=True)
            record, parent = root / 'argv', root / 'parent-env'
            rows = [json.loads(line) for line in record.read_text().splitlines()] if record.exists() else []
            self.assertFalse((root / 'injected').exists(), 'input executed as shell code')
            return result, rows, parent.read_text() if parent.exists() else None

    def test_rust_toolchain_adapter_preserves_arguments_and_default_scope(self):
        cases = [
            ('1.98.1', 'rustfmt clippy', '', 'false'),
            ('1.85.0', 'clippy', '', 'false'),
            ('1.85.0', '', 'x86_64-apple-darwin', 'false'),
            ('1.98.1', '', '', 'false'),
            ('1.98.1', '', '', 'true'),
            ("compiler path/$(touch injected); 'quoted'", 'rustfmt clippy',
             "target path/$(touch injected); 'quoted'", 'true'),
        ]
        for version, components, target, default in cases:
            with self.subTest(version=version, components=components, target=target, default=default):
                result, rows, _ = self.traced_shell('rust-toolchain', 'rustup', dict(
                    TOOLCHAIN=version, COMPONENTS=components, TARGET=target, SET_DEFAULT=default))
                self.assertEqual(result.returncode, 0, result.stderr)
                command = ['toolchain', 'install', version, '--profile', 'minimal']
                for component in components.split():
                    command += ['--component', component]
                if target:
                    command += ['--target', target]
                expected = [command]
                if default == 'true':
                    expected.append(['default', version])
                self.assertEqual([row['argv'] for row in rows], expected)
        shared = action('rust-toolchain')
        for variable, key in [('TOOLCHAIN', 'toolchain'), ('COMPONENTS', 'components'),
                              ('TARGET', 'target'), ('SET_DEFAULT', 'set-default')]:
            self.assertIn(f'{variable}: ${{{{ inputs.{key} }}}}', shared)
        inputs = shared.split('inputs:\n')[1].split('runs:\n')[0]
        for key, declaration in [('toolchain', 'required: true'), ('components', "default: ''"),
                                 ('target', "default: ''"), ('set-default', "default: 'false'")]:
            declared = re.split(r'(?m)^  [a-z][a-z-]*:\n', inputs.split(f'  {key}:\n')[1])[0]
            self.assertIn(declaration, declared)
        self.assertNotIn('      if:', shared)
        self.assertNotIn('continue-on-error', shared)

    def test_rust_toolchain_adapter_rejects_bad_inputs_and_propagates_each_failure(self):
        valid = dict(TOOLCHAIN='1.98.1', COMPONENTS='', TARGET='', SET_DEFAULT='true')
        for change in (dict(TOOLCHAIN=''), dict(SET_DEFAULT=''), dict(SET_DEFAULT='unknown')):
            with self.subTest(change=change):
                result, rows, _ = self.traced_shell('rust-toolchain', 'rustup', valid | change)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(rows, [])
        for failed_call in (1, 2):
            with self.subTest(failed_call=failed_call):
                result, rows, _ = self.traced_shell('rust-toolchain', 'rustup', valid,
                                                     fail_at=failed_call, code=31)
                self.assertEqual(result.returncode, 31, result.stderr)
                self.assertEqual(len(rows), failed_call)
                self.assertEqual(rows[0]['argv'], ['toolchain', 'install', '1.98.1', '--profile', 'minimal'])
                if failed_call == 2:
                    self.assertEqual(rows[1]['argv'], ['default', '1.98.1'])

    def test_rust_toolchain_callers_preserve_configuration_and_preparation_order(self):
        expected = {
            'check-rust': ('1.98.1', 'rustfmt clippy', '', 'false'),
            'check-rust-msrv': ('1.85.0', 'clippy', '', 'false'),
            'check-macos-source': ('1.85.0', '', 'x86_64-apple-darwin', 'false'),
            'check-interop': ('1.98.1', '', '', 'false'),
            'check-lean-kernel': ('1.98.1', '', '', 'false'),
            'check-distribution': ('1.98.1', '', '', 'true'),
        }
        workflow = (ROOT / '.github/workflows/ci.yml').read_text()
        self.assertEqual(workflow.count('uses: ./.github/actions/rust-toolchain'), len(expected))
        for name, configuration in expected.items():
            with self.subTest(job=name):
                block = job(name)
                step = action_step(block, 'rust-toolchain')
                values = dict(re.findall(r'(?m)^          ([\w-]+): (.*?)\s*$', step))
                actual = tuple(values.get(key, default).strip("'\"") for key, default in (
                    ('toolchain', ''), ('components', ''), ('target', ''), ('set-default', 'false')))
                self.assertEqual(actual, configuration)
                self.assertNotIn('        if:', step)
                self.assertIn("if: needs.changes.outputs.profile == 'full'", block)
                self.assertLess(block.index('uses: ./.github/actions/cargo-archives'),
                                block.index('uses: ./.github/actions/rust-toolchain'))
                self.assertNotIn('        if:', action_step(block, 'native-runtime'))
                self.assertNotIn('rustup toolchain install', block)
                self.assertNotIn('rustup default', block)
                if name == 'check-lean-kernel':
                    self.assertLess(block.index('uses: ./.github/actions/rust-toolchain'),
                                    block.index('cargo +1.98.1 fetch'))
                    self.assertLess(block.index('cargo +1.98.1 fetch'),
                                    block.index('uses: ./.github/actions/native-runtime'))
                else:
                    self.assertLess(block.index('uses: ./.github/actions/native-runtime'),
                                    block.index('uses: ./.github/actions/cargo-archives'))
                if name == 'check-distribution':
                    self.assertLess(block.index('uses: ./.github/actions/rust-toolchain'),
                                    block.index('cargo +1.98.1 fetch'))
                    self.assertLess(block.index('cargo +1.98.1 fetch'),
                                    block.index('scripts/check_distribution.py'))
                if name in ('check-lean-kernel', 'check-distribution'):
                    fetch = [step for step in re.split(r'(?m)^      - ', block)
                             if 'cargo +1.98.1 fetch' in step]
                    self.assertEqual(len(fetch), 1)
                    self.assertNotIn('        if:', fetch[0])

    def test_native_bundle_adapter_binds_both_consumers_and_only_the_child_kernel(self):
        kernel = "/bundle path/$(touch injected); 'quoted'/qleisli-kernel"
        record = "/record path/$(touch injected); 'quoted'"
        environment = dict(BUNDLE_KERNEL=kernel, RECORD_PATH=record, QLEISLI_KERNEL='outer checker')
        result, rows, parent = self.traced_shell('native-bundle-smoke', 'python3', environment)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(rows, [
            dict(argv=['scripts/test_native_verification.py', '--kernel', kernel, '--record', record, '--workers', '2'],
                 kernel='outer checker'),
            dict(argv=['scripts/test_source_kernel.py'], kernel=kernel),
        ])
        self.assertEqual(parent, 'outer checker')
        shared = action('native-bundle-smoke')
        self.assertIn('BUNDLE_KERNEL: ${{ runner.temp }}/qleisli-native-bundle/bin/qleisli-kernel', shared)
        self.assertIn('RECORD_PATH: ${{ inputs.record }}', shared)
        self.assertIn('required: true', shared.split('  record:\n')[1].split('runs:\n')[0])
        self.assertNotIn('      if:', shared)
        self.assertNotIn('continue-on-error', shared)

    def test_native_bundle_adapter_refuses_missing_records_and_stops_after_either_failure(self):
        environment = dict(BUNDLE_KERNEL='/bundle/checker', RECORD_PATH='/records',
                           QLEISLI_KERNEL='outer checker')
        result, rows, _ = self.traced_shell('native-bundle-smoke', 'python3',
                                             environment | dict(RECORD_PATH=''))
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(rows, [])
        for failed_call in (1, 2):
            with self.subTest(failed_call=failed_call):
                result, rows, parent = self.traced_shell('native-bundle-smoke', 'python3',
                                                         environment, fail_at=failed_call, code=37)
                self.assertEqual(result.returncode, 37, result.stderr)
                self.assertEqual(len(rows), failed_call)
                self.assertIsNone(parent)
                self.assertEqual(rows[0]['argv'], ['scripts/test_native_verification.py',
                    '--kernel', '/bundle/checker', '--record', '/records', '--workers', '2'])
                if failed_call == 2:
                    self.assertEqual(rows[1], dict(argv=['scripts/test_source_kernel.py'],
                                                  kernel='/bundle/checker'))

    def test_source_adapter_preserves_literal_arguments_and_failures(self):
        compiler = "compiler path/$(touch injected); 'quoted'"
        for path, code in [('', 0), (compiler, 0), (compiler, 23)]:
            with self.subTest(compiler=path, exit_code=code):
                result, args, env = self.shell('source-check', dict(
                    CHECK_GROUP='source-contracts', CHECK_COMPILER=path), code)
                self.assertEqual(result.returncode, code, result.stderr)
                expected = ['scripts/ci_profiles.py', '--checks', 'source-contracts']
                if path:
                    expected += ['--compiler', path]
                self.assertEqual(args, expected + ['--output', env['RUNNER_TEMP'] + '/source-contracts'])
        shared = action('source-check')
        self.assertIn("if: always() && (steps.check.outcome == 'success' || steps.check.outcome == 'failure')", shared)
        self.assertIn('if-no-files-found: error', shared)
        self.assertNotIn('continue-on-error', shared)

    def test_receipt_adapter_keeps_job_identity_and_optional_evidence(self):
        for code in (0, 31):
            result, args, env = self.shell('release-receipt', dict(
                GITHUB_JOB='check-lean', NATIVE_EVIDENCE='native path',
                DISTRIBUTION_EVIDENCE='', CONSTITUTION_EVIDENCE="$(echo not executed)'path"), code)
            self.assertEqual(result.returncode, code, result.stderr)
            self.assertEqual(args, ['scripts/check_release_ready.py', '--record-job', 'check-lean',
                                   '--output', env['RUNNER_TEMP'] + '/release-receipt',
                                   '--native', 'native path', '--constitution', "$(echo not executed)'path"])
        text = action('release-receipt')
        self.assertIn('value: ${{ steps.record.outputs.release_receipt_sha256 }}', text)
        self.assertIn('release-receipt-${{ github.job }}-${{ github.sha }}-${{ github.run_attempt }}', text)
        self.assertNotIn('always()', text)  # Failed producers cannot publish success receipts.
        self.assertNotIn('continue-on-error', text)

    def test_source_group_inventory_and_preparation_ownership(self):
        expected = {
            'check-rust': ['rust-latest', 'source-contracts', 'source-semantics', 'rust-latest-lint-research'],
            'check-rust-msrv': ['rust-msrv', 'source-contracts', 'rust-msrv-lint-research'],
            'check-docs': ['book', 'repository-integrity'],
        }
        for name, groups in expected.items():
            block = job(name)
            if name in ('check-rust', 'check-rust-msrv'):
                profile = 'latest' if name == 'check-rust' else 'msrv'
                self.assertIn('profile: ' + profile, action_step(block, 'rust-suite'))
                self.assertNotIn('uses: ./.github/actions/source-check', block)
                shared = action('rust-suite').replace('${{ inputs.profile }}', profile)
                if profile == 'msrv':
                    shared = re.sub(r"    - name: Run source semantics\n.*?(?=    - name:)", '', shared, flags=re.S)
                self.assertEqual(re.findall(r'        group: ([\w-]+)', shared), groups)
            else:
                self.assertEqual(re.findall(r'          group: ([\w-]+)', block), groups)
                self.assertEqual(block.count('uses: ./.github/actions/source-check'), len(groups))
            for group in groups:
                self.assertIn(name, describe(group)['lanes'])
        for name in ('check-rust', 'check-rust-msrv', 'check-macos-source',
                     'check-interop', 'check-lean-kernel', 'check-distribution'):
            block = job(name)
            self.assertEqual(block.count('uses: ./.github/actions/native-runtime'), 1)
            if name in ('check-rust', 'check-rust-msrv'):
                self.assertIn("prepare: 'false'", block)
                group = 'rust-latest' if name == 'check-rust' else 'rust-msrv'
                self.assertEqual(describe(group)['prepare'], ['native-runtime'])
            else:
                self.assertNotIn('prepare:', block)
        native = action('native-runtime')
        self.assertIn("default: 'true'", native)
        self.assertIn('group: native-runtime', native)
        self.assertIn("build: 'false'", native)  # The shared plan owns the single build/audit.
        self.assertIn('native-runtime-${{ github.job }}-${{ github.sha }}-${{ github.run_attempt }}', native)

    def test_shared_rust_suite_keeps_optional_coverage_artifacts_and_refusal(self):
        shared = action('rust-suite')
        self.assertIn("if: inputs.profile == 'latest'", shared)
        self.assertIn('--quick --report "$RUNNER_TEMP/corpus.json"', shared)
        self.assertIn("steps.corpus.outcome == 'failure'", shared)
        self.assertIn('source-contracts-${{ github.job }}-${{ github.sha }}-${{ github.run_attempt }}', shared)
        self.assertNotIn('continue-on-error', shared)
        for profile in ('latest', 'msrv', 'unknown', 'latest; touch injected'):
            result, _, _ = self.shell('rust-suite', dict(RUST_SUITE_PROFILE=profile))
            self.assertEqual(result.returncode == 0, profile in ('latest', 'msrv'))

    def test_invalid_native_preparation_cannot_silently_skip_build(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'env'
            result, _, _ = self.shell('native-runtime', dict(
                PREPARE_NATIVE='unknown', GITHUB_ENV=str(output), GITHUB_WORKSPACE='/checkout'))
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(output.exists())

    def test_cache_keys_and_status_preserve_all_six_callers(self):
        versions = {'check-rust': '1.98.1', 'check-rust-msrv': '1.85.0',
                    'check-macos-source': '1.85.0', 'check-interop': '1.98.1',
                    'check-lean-kernel': '1.98.1', 'check-distribution': '1.98.1'}
        for name, version in versions.items():
            block = job(name)
            self.assertEqual(block.count('uses: ./.github/actions/cargo-archives'), 1)
            self.assertIn(f"toolchain: '{version}'", block)
            self.assertIn("enabled: ${{ github.event_name != 'workflow_dispatch' || inputs.cache != 'disabled' }}", block)
            self.assertIn('dependency-cache: ${{ steps.cargo-cache.outputs.status }}', block)
        text = action('cargo-archives')
        paths = text.split('        path: |\n')[1].split('        key:')[0].split()
        self.assertEqual(paths, ['~/.cargo/registry/index', '~/.cargo/registry/cache'])
        self.assertIn("if: inputs.enabled == 'true'", text)
        self.assertIn("steps.restore.outputs.cache-hit == 'true' && 'hit'", text)
        self.assertIn("steps.restore.outcome == 'success' && 'miss'", text)
        self.assertIn("steps.restore.outcome == 'skipped' && 'disabled' || 'unavailable'", text)
        self.assertIn("cargo-archives-v1-${{ runner.os }}-${{ runner.arch }}-${{ inputs.toolchain }}-${{ hashFiles('Cargo.toml', 'Cargo.lock', 'research/semantic-kernel/Cargo.toml', 'research/semantic-kernel/Cargo.lock') }}", text)


if __name__ == '__main__':
    unittest.main()
