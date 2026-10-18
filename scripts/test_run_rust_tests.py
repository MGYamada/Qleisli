#!/usr/bin/env python3
"""Check bounded Rust scheduling, exact build inventory and refusal propagation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import contextlib
import copy
import base64
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import patch

import run_rust_tests as runner
from test_rust_test_partition import metadata


class RustSchedulerTests(unittest.TestCase):
    def test_retained_first_sources_and_observations_are_inert_exact_bytes(self):
        root = runner.ROOT / 'tests/fixtures/authoring_sessions/ci-rust-parallel-v030'
        index = json.loads((root / 'index.json').read_text())
        self.assertIn('not a hosted full-CI benchmark', (root / 'README.md').read_text())
        coverage_bytes = (root / 'coverage-first.json.gz').read_bytes()
        self.assertEqual(hashlib.sha256(coverage_bytes).hexdigest(),
                         '100c8bc06a1eec06464374c231e427e1e1dab8cb4370a5f6752983b9071b8bc3')
        coverage = json.loads(gzip.decompress(coverage_bytes))
        self.assertEqual(coverage['first_head'], '8befdc78424c48b11e98917152ee7a7dd837261b')
        self.assertEqual([row['structuredContent']['job']['id'] for row in coverage['observations']],
                         [117622633631, 117622627615])
        workflow_bytes = (root / 'workflow-first.json.gz').read_bytes()
        self.assertEqual(hashlib.sha256(workflow_bytes).hexdigest(),
                         '9d9b9e75306c0347c0cadc347927d496d4c9116a3dc0a40a4dcdf81f7ff944cf')
        workflow = json.loads(gzip.decompress(workflow_bytes))
        self.assertEqual(workflow['first_head'], 'fd17cea85ef1761dba36b67cd0a00f6d227fa0dd')
        self.assertEqual(workflow['observation']['structuredContent']['job']['id'], 117625096694)
        native_bytes = (root / 'native-first.json.gz').read_bytes()
        self.assertEqual(hashlib.sha256(native_bytes).hexdigest(),
                         '1a887cd5c4fb77644fc84d8a032631332abacd53ffbf2dca47277d88e04f3bb3')
        native = json.loads(gzip.decompress(native_bytes))
        for row in native['records']:
            data = base64.b64decode(row['base64'], validate=True)
            self.assertEqual((len(data), hashlib.sha256(data).hexdigest()), (row['bytes'], row['sha256']))
        computed_bytes = (root / 'computed-timeout-first.json.gz').read_bytes()
        self.assertEqual(hashlib.sha256(computed_bytes).hexdigest(),
                         'da31b8a3d9b815653bf0b6441954c2b486d49e898fd0ed7e77d1114d47fa3c34')
        computed = json.loads(gzip.decompress(computed_bytes))
        self.assertEqual(computed['first_head'], '957f7f930ef9c55c1346eb8162030b89d657d7b6')
        self.assertEqual(len(computed['records']), 2344)
        self.assertEqual(len({row['name'] for row in computed['records']}), 2344)
        for row in computed['records']:
            data = base64.b64decode(row['base64'], validate=True)
            self.assertEqual((len(data), hashlib.sha256(data).hexdigest()), (row['bytes'], row['sha256']))
            self.assertIn(row['mode'], (0o600, 0o644, 0o755))
        archive = (root / index['archive']['path']).read_bytes()
        self.assertEqual(hashlib.sha256(archive).hexdigest(), index['archive']['sha256'])
        records = json.loads(gzip.decompress(archive))['records']
        self.assertEqual([{k:v for k,v in row.items() if k != 'base64'} for row in records], index['records'])
        self.assertEqual(len({row['name'] for row in records}), len(records))
        for row in records:
            data = base64.b64decode(row['base64'], validate=True)
            self.assertEqual((len(data), hashlib.sha256(data).hexdigest()), (row['bytes'], row['sha256']))

    def command(self, tail=None, msrv=False):
        return (runner.partition.MSRV if msrv else runner.partition.LATEST) + ['test'] + (
            tail if tail is not None else ['--test', 'alpha'])

    def test_positive_selection_for_both_pins_and_all_categories(self):
        value = metadata(runner.ROOT)
        for msrv in (False, True):
            _, selected = runner.selection(self.command(msrv=msrv), value)
            self.assertEqual(selected, {('test', 'alpha')})
        _, selected = runner.selection(self.command(runner.partition.CATEGORIES + ['--test', 'alpha']), value)
        self.assertEqual(len(selected), 8)
        self.assertNotIn(('custom-build', 'build-script-build'), selected)
        _, selected = runner.selection(self.command(['--all-targets']), value)
        self.assertEqual(len(selected), 10)

    def test_test_filters_features_unknown_targets_and_overrides_refuse(self):
        for tail in ([], ['--tests'], ['--all-targets', '--', '--skip', 'case'], ['--test', 'unknown'],
                     ['--test', 'alpha', '--', '--skip', 'case'],
                     ['--test', 'alpha', '--features', 'extra'], ['--test', 'alpha', '--no-run']):
            with self.assertRaises(ValueError):
                runner.selection(self.command(tail), metadata(runner.ROOT))
        with self.assertRaises(ValueError):
            runner.selection(['cargo', '+other', 'test', '--test', 'alpha'], metadata(runner.ROOT))

    def test_only_complete_same_package_same_target_build_artifacts_are_run(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'alpha'; path.write_text('artifact'); path.chmod(0o755)
            value = metadata(runner.ROOT); value['target_directory'] = directory
            target = next(t for t in value['packages'][0]['targets'] if t['name'] == 'alpha')
            message = dict(reason='compiler-artifact', package_id='root-id', target=target,
                           profile=dict(test=True), executable=str(path))
            expected = {('test', 'alpha')}
            self.assertEqual(runner.artifacts([message], value, expected)[0]['sha256'], runner.digest(path))
            for messages in ([], [message, message], [message | dict(package_id='dependency')],
                             [message | dict(profile=dict(test=False))],
                             [message | dict(target=target | dict(src_path='/other.rs'))],
                             [message | dict(executable='/missing')]):
                with self.assertRaises(ValueError): runner.artifacts(messages, value, expected)
            outside = Path(directory).parent / 'outside-executable'
            with self.assertRaises(ValueError):
                runner.artifacts([message | dict(executable=str(outside))], value, expected)

    def test_pool_is_bounded_and_runs_each_selected_target_once(self):
        active = 0; maximum = 0; seen = []; lock = threading.Lock()
        def run(row, directory):
            nonlocal active, maximum
            with lock:
                active += 1; maximum = max(maximum, active); seen.append(row['name'])
            time.sleep(0.02)
            with lock: active -= 1
            return row | dict(status='passed', seconds=0.02, log=str(directory / 'absent'))
        rows = [dict(kind='test', name=str(n), status='not-run') for n in range(7)]
        snapshots = []
        with tempfile.TemporaryDirectory() as directory, patch.object(runner, 'harness', side_effect=run), \
                contextlib.redirect_stdout(io.StringIO()):
            results = runner.schedule(rows, 2, Path(directory), lambda rows: snapshots.append(copy.deepcopy(rows)))
        self.assertEqual(maximum, 2)
        self.assertEqual(sorted(seen), [str(n) for n in range(7)])
        self.assertTrue(all(row['status'] == 'passed' for row in results))
        self.assertEqual(snapshots[-1], results)

    def test_failure_retains_unstarted_targets_and_stops_submission(self):
        rows = [dict(kind='test', name=str(n), status='not-run') for n in range(3)]
        output = io.StringIO()
        with tempfile.TemporaryDirectory() as directory, \
                patch.object(runner, 'harness', return_value=rows[0] | dict(status='failed', error='retained failure reason', seconds=0, log='/missing')) as run, \
                contextlib.redirect_stdout(output):
            results = runner.schedule(rows, 1, Path(directory), lambda rows: None)
        run.assert_called_once()
        self.assertIn('retained failure reason', output.getvalue())
        self.assertEqual([row['status'] for row in results], ['failed', 'not-run', 'not-run'])

    def test_complete_isolated_harness_finishes_before_any_pool_worker(self):
        rows = [dict(kind='test', name=name, status='not-run') for name in
                ('alpha', 'computed_derived_source', 'beta')]
        seen = []; active = []; lock = threading.Lock()
        def run(row, directory):
            with lock:
                if runner.isolated(row): self.assertEqual(active, [])
                else: self.assertNotIn('computed_derived_source', active)
                active.append(row['name']); seen.append(row['name'])
            time.sleep(0.02)
            with lock: active.remove(row['name'])
            return row | dict(status='passed', seconds=0.02, log=str(directory / 'absent'))
        with tempfile.TemporaryDirectory() as directory, patch.object(runner, 'harness', side_effect=run), \
                contextlib.redirect_stdout(io.StringIO()):
            results = runner.schedule(rows, 2, Path(directory), lambda rows: None)
        self.assertEqual(seen[0], 'computed_derived_source')
        self.assertCountEqual(seen, [row['name'] for row in rows])
        self.assertEqual([row['name'] for row in results], [row['name'] for row in rows])
        self.assertTrue(all(row['status'] == 'passed' for row in results))

    def test_isolated_failure_keeps_other_targets_unexecuted(self):
        rows = [dict(kind='test', name=name, status='not-run') for name in
                ('alpha', 'computed_derived_source', 'beta')]
        with tempfile.TemporaryDirectory() as directory, \
                patch.object(runner, 'harness', return_value=rows[1] | dict(
                    status='failed', error='native timeout', seconds=0, log='/missing')) as run, \
                patch.object(runner, 'ThreadPoolExecutor') as pool, contextlib.redirect_stdout(io.StringIO()):
            results = runner.schedule(rows, 2, Path(directory), lambda rows: None)
        run.assert_called_once()
        pool.assert_not_called()
        self.assertEqual([row['status'] for row in results], ['not-run', 'failed', 'not-run'])

    def test_failure_identity_survives_bounded_previews_after_large_worker_logs(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / 'failed.log'; log.write_text('large output\n' * 2000)
            row = dict(kind='lib', name='qleisli', status='failed', error='original failure', exit_code=101, log=str(log))
            output = io.StringIO()
            with contextlib.redirect_stderr(output):
                runner.failure_details([row, dict(kind='test', name='later-success', status='passed')])
            tail = output.getvalue()[-8192:]
            self.assertEqual(json.loads(tail.splitlines()[-1])['failed_harnesses'], [
                {key: row[key] for key in ('kind', 'name', 'error', 'exit_code', 'log')}])

    def test_actual_child_failure_native_skip_missing_summary_and_changed_binary_refuse(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            child = root / 'cargo-test.py'
            for mode in ('pass', 'isolated', 'exit', 'skip', 'missing', 'changed', 'wrong-artifact'):
                executable = root / 'artifact'; executable.write_text('bound executable')
                name = 'computed_derived_source' if mode == 'isolated' else mode
                artifact = dict(reason='compiler-artifact',package_id='root-id',target=dict(name=name),
                                profile=dict(test=True),executable=str(executable))
                if mode == 'wrong-artifact': artifact['executable'] = '/other-harness'
                body = f"print({json.dumps(artifact)!r})\n" + "print('test result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s')\n"
                if mode == 'exit': body += 'raise SystemExit(7)\n'
                if mode == 'skip': body += "print('test native ... ignored, native-kernel gate: requires QLEISLI_KERNEL')\n"
                if mode == 'missing': body = "print('not a test summary')\n"
                if mode == 'changed': body += f"from pathlib import Path\nPath({str(executable)!r}).write_text('replaced')\n"
                child.write_text(body)
                row = dict(kind='test', name=name, executable=str(executable), sha256=runner.digest(executable),
                           package_id='root-id',target=dict(name=name),profile=dict(test=True),
                           command=[sys.executable, str(child)], status='not-run')
                result = runner.harness(row, root)
                self.assertEqual(result['executed_command'], row['command'] +
                                 ['--message-format=json', '--', '--test-threads',
                                  '1' if mode == 'isolated' else '2'])
                self.assertEqual(result['test_threads'], 1 if mode == 'isolated' else 2)
                self.assertEqual(result['status'], 'passed' if mode in ('pass', 'isolated') else 'failed')
                if mode == 'exit': self.assertEqual(result['exit_code'], 7)

    def test_missing_kernel_refuses_before_metadata_or_build_and_retains_record(self):
        with tempfile.TemporaryDirectory() as directory, patch.dict(os.environ, QLEISLI_KERNEL='/missing'), \
                patch.object(runner.subprocess, 'run') as run, contextlib.redirect_stderr(io.StringIO()):
            record = Path(directory) / 'record.json'
            self.assertEqual(runner.execute(self.command(), 2, record), 1)
            run.assert_not_called()
            self.assertEqual(json.loads(record.read_text())['status'], 'failed')

    def test_outer_timeout_kills_worker_native_descendants(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            started, survived = root / 'started', root / 'survived'
            executable = root / 'artifact'; executable.write_text('bound executable')
            grandchild = f"from pathlib import Path; import time; Path({str(started)!r}).touch(); time.sleep(1.5); Path({str(survived)!r}).touch()"
            child = f"import subprocess,sys,time; subprocess.Popen([sys.executable,'-c',{grandchild!r}]); time.sleep(30)"
            row = dict(kind='test', name='timeout', executable=str(executable), sha256=runner.digest(executable),
                       command=[sys.executable, '-c', child])
            program = (f"import sys; from pathlib import Path; sys.path.insert(0,{str(runner.ROOT / 'scripts')!r}); "
                       f"import run_rust_tests; run_rust_tests.schedule([{row!r}],1,Path({str(root)!r}),lambda rows: None)")
            result = runner.ci_runtime.run_task(dict(id='timeout', commands=[[sys.executable, '-c', program]]),
                                                runner.ROOT, root / 'task', 0.8,
                                                runner.ci_runtime.execution_environment())
            self.assertEqual(result['commands'][0]['status'], 'timed-out')
            self.assertTrue(started.exists())
            time.sleep(1)
            self.assertFalse(survived.exists(), 'native descendant survived the outer deadline')


if __name__ == '__main__':
    unittest.main()
