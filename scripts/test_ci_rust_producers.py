"""Synthetic pair-dependency mutation tests, never hosted success or a proof.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import copy
import base64
import gzip
import hashlib
import io
import json
from pathlib import Path
import unittest

import ci_rust_producers as gate


def fixture(profile='latest'):
    context = dict(repository='MGYamada/Qleisli', commit='1' * 40, tree='2' * 40,
                   run_id='17', attempt='2', event='pull_request')
    prefix = 'check-rust' if profile == 'latest' else 'check-rust-msrv'
    needs = {'changes': dict(result='success', outputs=dict(head='1' * 40, profile='full', proof_lane='full'))}
    for name, digest in [(prefix + '-differential', 'a' * 64), (prefix + '-remaining', 'b' * 64)]:
        needs[name] = dict(result='success', outputs=dict(source_head='1' * 40, source_tree='2' * 40,
                           source_run_id='17', source_attempt='2', rust_receipt_sha256=digest))
    return context, needs


class RustProducerDependencies(unittest.TestCase):
    def test_first_synthetic_obligations_are_preserved_without_execution(self):
        root = Path(__file__).resolve().parents[1]
        stored = (root / 'tests/fixtures/authoring_sessions/ci-rust-parallel-v030/producer-obligations-first.json.gz').read_bytes()
        self.assertEqual(hashlib.sha256(stored).hexdigest(),
                         '2a8dfa3cea1789ec8737da6fd5cdb8d88041276912c300f1dc2d32c658868b9a')
        with gzip.GzipFile(fileobj=io.BytesIO(stored)) as archive:
            raw = archive.read(23292)
        self.assertEqual(len(raw), 23291)
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
                         'a1de7d957372fe482e1de40599e23ba2cf30fbc87d62fc985082f9c8780f977a')
        first = json.loads(raw)
        self.assertEqual((first['format'], first['version']), ('qleisli.inert-rust-pair-first', 1))
        self.assertEqual(len(first['records']), 4)
        self.assertEqual({row['path'] for row in first['records']}, {
            'DESIGN-first.txt', 'pair-obligations-first.py',
            'pair-obligations-first.stdout.json', 'pair-obligations-first.stderr.txt'})
        records = {}
        for row in first['records']:
            data = base64.b64decode(row['base64'], validate=True)
            self.assertEqual((len(data), hashlib.sha256(data).hexdigest()), (row['bytes'], row['sha256']))
            self.assertIn(row['mode'], (0o600, 0o644))
            records[row['path']] = data
        observed = json.loads(records['pair-obligations-first.stdout.json'])['observations']
        self.assertEqual(len(observed), 40)
        self.assertEqual(sum(row['result'] == 'refused' for row in observed), 38)
        self.assertEqual(records['pair-obligations-first.stderr.txt'], b'')

    def test_both_profiles_return_expected_hashes_for_artifact_checking(self):
        for profile, prefix in [('latest', 'check-rust'), ('msrv', 'check-rust-msrv')]:
            context, needs = fixture(profile)
            self.assertEqual(gate.expected_producer_receipts(needs, profile, context), {
                'differential': dict(job=prefix + '-differential', sha256='a' * 64),
                'remaining': dict(job=prefix + '-remaining', sha256='b' * 64)})
            for event in ('push', 'workflow_dispatch'):
                gate.expected_producer_receipts(needs, profile, context | dict(event=event))

    def test_no_missing_extra_failed_skipped_or_cancelled_producer_can_supply_hashes(self):
        for profile in ('latest', 'msrv'):
            context, original = fixture(profile)
            for job in list(original)[1:]:
                changed = copy.deepcopy(original); del changed[job]
                with self.assertRaises(ValueError): gate.expected_producer_receipts(changed, profile, context)
                for status in ('failure', 'skipped', 'cancelled', 'timed_out', '', None, True):
                    changed = copy.deepcopy(original); changed[job]['result'] = status
                    with self.assertRaises(ValueError): gate.expected_producer_receipts(changed, profile, context)
            for changed in (original | {'other': {}}, {}, [], None):
                with self.assertRaises(ValueError): gate.expected_producer_receipts(changed, profile, context)

    def test_each_producer_binds_source_tree_run_attempt_and_receipt_digest(self):
        for profile in ('latest', 'msrv'):
            context, original = fixture(profile)
            for job in list(original)[1:]:
                for field in ('source_head', 'source_tree', 'source_run_id', 'source_attempt', 'rust_receipt_sha256'):
                    for value in ('wrong', None, False, ['wrong']):
                        changed = copy.deepcopy(original); changed[job]['outputs'][field] = value
                        with self.assertRaises(ValueError): gate.expected_producer_receipts(changed, profile, context)
                    changed = copy.deepcopy(original); del changed[job]['outputs'][field]
                    with self.assertRaises(ValueError): gate.expected_producer_receipts(changed, profile, context)
                for value in (None, [], True):
                    changed = copy.deepcopy(original); changed[job]['outputs'] = value
                    with self.assertRaises(ValueError): gate.expected_producer_receipts(changed, profile, context)

    def test_wrong_context_or_selection_refuses_instead_of_using_a_default(self):
        context, original = fixture()
        for field in context:
            changed = context.copy(); del changed[field]
            with self.assertRaises(ValueError): gate.expected_producer_receipts(original, 'latest', changed)
            changed = context | {field: False}
            with self.assertRaises(ValueError): gate.expected_producer_receipts(original, 'latest', changed)
        for changed in (context | dict(repository='other/repo'), context | dict(event='workflow_run'),
                        context | dict(commit='1' * 39), context | dict(tree='2' * 41),
                        context | dict(run_id='0'), context | dict(attempt='-1'), context | dict(extra='field')):
            with self.assertRaises(ValueError): gate.expected_producer_receipts(original, 'latest', changed)
        for field, values in [('head', ['3' * 40, None]), ('profile', ['docs', None]),
                              ('proof_lane', ['unknown', [], None])]:
            for value in values:
                changed = copy.deepcopy(original); changed['changes']['outputs'][field] = value
                with self.assertRaises(ValueError): gate.expected_producer_receipts(changed, 'latest', context)
        for profile in ('', 'unknown', None, []):
            with self.assertRaises(ValueError): gate.expected_producer_receipts(original, profile, context)


if __name__ == '__main__':
    unittest.main()
