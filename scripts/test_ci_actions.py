#!/usr/bin/env python3
"""Check shared workflow wiring and execute its actual shell adapters locally.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
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


class CIActions(unittest.TestCase):
    def test_hosted_validation_is_explicit_completion_or_release_only(self):
        workflow = (ROOT / '.github/workflows/ci.yml').read_text()
        trigger = workflow.split('on:\n')[1].split('\nconcurrency:')[0]
        self.assertNotIn('branches:', trigger)
        self.assertIn("tags: ['v*']", trigger)
        self.assertNotIn('pull_request:', trigger)
        self.assertNotIn('synchronize', trigger)
        self.assertIn('completion_issues:', trigger)
        self.assertIn('completion_pr:', trigger)
        self.assertIn('base: ${{ steps.select.outputs.base }}', job('changes'))
        self.assertIn('CONSTITUTION_BASE: ${{ needs.changes.outputs.base || inputs.release_base ||', job('check-docs'))
        self.assertIn('if: always()', job('required'))
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
            self.assertEqual(re.findall(r'          group: ([\w-]+)', block), groups)
            for group in groups:
                self.assertIn(name, describe(group)['lanes'])
            self.assertEqual(block.count('uses: ./.github/actions/source-check'), len(groups))
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
