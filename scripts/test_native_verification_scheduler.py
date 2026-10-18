"""Bounded pair scheduling and passive preservation; no historical execution.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import base64
import gzip
import hashlib
import io
import json
from pathlib import Path
import threading
import unittest
from unittest.mock import patch

import test_native_verification as native


class NativeClientScheduler(unittest.TestCase):
    def clients(self, count):
        return [(dict(id=str(i)), Path(str(i))) for i in range(count)]

    def test_two_workers_complete_every_pair_and_retain_input_order(self):
        active, maximum, finished = set(), [], []
        lock = threading.Lock()
        rendezvous, second_done = threading.Barrier(2), threading.Event()

        def compare(client, rows):
            name = client[0]['id']
            with lock:
                active.add(name)
                maximum.append(len(active))
            try:
                if name in ('0', '1'):
                    rendezvous.wait(timeout=3)
                if name == '0':
                    self.assertTrue(second_done.wait(3))
                for selection in ('environment', 'explicit'):
                    rows.append(dict(id=name, selection=selection))
                with lock:
                    finished.append(name)
                if name == '1':
                    second_done.set()
            finally:
                with lock:
                    active.remove(name)

        rows = []
        native.compare_clients(self.clients(5), 2, compare, rows)
        self.assertEqual(max(maximum), 2)
        self.assertEqual(finished[0], '1')
        self.assertEqual([row['id'] for row in rows], list(map(str, range(5))))
        self.assertEqual([row['status'] for row in rows], ['passed'] * 5)
        for row in rows:
            self.assertEqual(row['observations'], [dict(id=row['id'], selection=s)
                                                  for s in ('environment', 'explicit')])

    def test_failure_keeps_running_pair_and_marks_every_unstarted_case(self):
        second_started, release_second = threading.Event(), threading.Event()
        failure_observed = threading.Event()
        original_wait = native.wait

        def compare(client, rows):
            name = client[0]['id']
            rows.append(dict(id=name, selection='environment'))
            if name == '0':
                assert second_started.wait(3)
                raise ValueError('different result')
            second_started.set()
            assert release_second.wait(3)
            rows.append(dict(id=name, selection='explicit'))

        def observed_wait(*args, **kwargs):
            done, remaining = original_wait(*args, **kwargs)
            if any(f.result()['status'] == 'failed' for f in done):
                failure_observed.set()
            return done, remaining

        rows = []
        with patch.object(native, 'wait', side_effect=observed_wait):
            worker = threading.Thread(target=native.compare_clients,
                                      args=(self.clients(5), 2, compare, rows))
            worker.start()
            try:
                self.assertTrue(failure_observed.wait(3))
            finally:
                release_second.set()
                worker.join(3)
        self.assertFalse(worker.is_alive())
        self.assertEqual([r['status'] for r in rows], ['failed', 'passed'] + ['not-run'] * 3)
        self.assertEqual(rows[0]['error'], 'different result')
        self.assertEqual(len(rows[0]['observations']), 1)
        self.assertEqual(len(rows[1]['observations']), 2)
        self.assertTrue(all(not r['observations'] for r in rows[2:]))

    def test_one_worker_retains_serial_pair_order(self):
        calls, rows = [], []
        def compare(client, observations):
            for selection in ('environment', 'explicit'):
                call = (client[0]['id'], selection)
                calls.append(call)
                observations.append(call)
        native.compare_clients(self.clients(3), 1, compare, rows)
        self.assertEqual(calls, [(str(i), s) for i in range(3)
                                 for s in ('environment', 'explicit')])
        self.assertTrue(all(r['status'] == 'passed' for r in rows))

    def test_first_serial_sources_and_hosted_timing_are_inert_and_exact(self):
        path = native.ROOT / 'tests/fixtures/authoring_sessions/ci-rust-parallel-v030/bundle-smoke-first.json.gz'
        stored = path.read_bytes()
        self.assertEqual(hashlib.sha256(stored).hexdigest(),
                         '4d0f97e5af20a8aaf3755339ce79ce27ceba461bbfeb7db30a1c12132eb88f3a')
        with gzip.GzipFile(fileobj=io.BytesIO(stored)) as archive:
            decoded = archive.read(1_000_001)
        self.assertLessEqual(len(decoded), 1_000_000)
        payload = json.loads(decoded)
        self.assertEqual(payload['format'], 'qleisli.inert-ci-bundle-smoke-first')
        self.assertEqual(payload['source_head'], '80f73b090d72dfcf7b6be789ad2e384d3495c65b')
        self.assertEqual(len(payload['records']), 4)
        records = {}
        for row in payload['records']:
            self.assertNotIn(row['path'], records)
            data = base64.b64decode(row['base64'], validate=True)
            self.assertEqual((len(data), hashlib.sha256(data).hexdigest()), (row['bytes'], row['sha256']))
            self.assertIn(row['mode'], (0o600, 0o644, 0o755))
            records[row['path']] = data
        self.assertEqual(sum(map(len, records.values())), 102312)
        hosted = json.loads(records['hosted-macos-117644427199-first.json'])['structuredContent']
        self.assertFalse(hosted['logTruncated'])
        self.assertEqual(hosted['job']['conclusion'], 'success')
        self.assertIn('381 process checks, 84 small corpus clients', hosted['log'])
        self.assertIn('duration_ms=901684', hosted['log'])


if __name__ == '__main__':
    unittest.main()
