"""Passive first-byte checks; historical source and observers are never run.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
# Packet scope notes: "tests/fixtures/authoring_sessions/prelude-v030/README.md".
import base64
import gzip
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import unittest

ROOT = Path(__file__).resolve().parents[1]


class FirstPrelude(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        stored = (ROOT / 'tests/fixtures/authoring_sessions/prelude-v030/first.json.gz').read_bytes()
        if hashlib.sha256(stored).hexdigest() != 'bb036f7a1117d17546257bbec76ff6e39270462c7cde9759103e5ca82358b82c':
            raise AssertionError('original stored first packet changed')
        with gzip.GzipFile(fileobj=io.BytesIO(stored)) as archive:
            raw = archive.read(215_918)
        if len(raw) != 215_917 or hashlib.sha256(raw).hexdigest() != 'd41be5487eb1609ed5d342a6bc20ab09b933bba7d1b6fc7cd462c5d4ae5ca6c9':
            raise AssertionError('original expanded first packet changed')
        cls.packet = json.loads(raw)
        cls.data = {}
        for name, row in cls.packet['records'].items():
            path = PurePosixPath(name)
            if path.is_absolute() or '..' in path.parts or str(path) != name or row['mode'] != 0o644:
                raise AssertionError('noncanonical record path/mode')
            data = base64.b64decode(row['base64'], validate=True)
            if (len(data), hashlib.sha256(data).hexdigest()) != (row['bytes'], row['sha256']):
                raise AssertionError('original record changed: ' + name)
            cls.data[name] = data

    def test_first_sources_and_observations_are_complete_and_unchanged(self):
        self.assertEqual((self.packet['format'], self.packet['version']),
                         ('qleisli.prelude-first-history', 1))
        self.assertEqual(len(self.data), 69)
        plan = json.loads(self.data['plan.json'])
        report = json.loads(self.data['report.json'])
        self.assertEqual(len(plan['plans']), 19)
        self.assertEqual(len(plan['source_records']), 41)
        for name, row in plan['source_records'].items():
            self.assertEqual(self.data[name], base64.b64decode(row['base64'], validate=True))
            self.assertEqual(hashlib.sha256(self.data[name]).hexdigest(), row['sha256'])
        self.assertEqual(len(report['commands']), 24)
        self.assertEqual(report['prediction_mismatches'], [])
        self.assertEqual(report['before'], report['after'])
        self.assertTrue(report['source_unchanged'])
        self.assertEqual(report['before']['head'], '6eb451647f599cb0f1589f5e75de1c91d3f7325e')
        self.assertEqual(report['before']['tree'], self.packet['source_tree'])
        for index, command in enumerate(report['commands'], 1):
            self.assertEqual(json.loads(self.data[f'observation-{index:02}.json']), command)
        artifact = self.data['explicit-bell-control.qirf']
        self.assertEqual((len(artifact), hashlib.sha256(artifact).hexdigest()),
                         (5338, 'fad9063dc1b00e9c513f1d8c95b5dfa2696053752b7941e0c2ec2fa85685e9f0'))

    def test_parser_refusals_are_not_relabelled_as_semantic_checks(self):
        report = json.loads(self.data['report.json'])
        checks = {row['case']: row for row in report['commands'] if row['operation'] == 'check'}
        expected = {
            'implicit-bell': 'unknown_name', 'implicit-static-id': 'unknown_name',
            'optout-explicit': 'parse', 'optout-missing': 'parse',
            'qualified-bell': 'parse', 'public-reexport': 'parse',
            'explicit-import-collision': 'project', 'missing-static-id': 'arity',
            'runtime-shadow': 'type_mismatch', 'explicit-prelude': 'project',
            'optout-primitives': 'parse', 'false-pure-explicit': 'effect',
            'false-pure-prelude': 'unknown_name', 'private-qualified': 'parse',
            'optout-explicit-prelude': 'parse',
        }
        for name, code in expected.items():
            self.assertEqual(checks[name]['exit_code'], 1)
            self.assertEqual(json.loads(checks[name]['stdout'])['diagnostics'][0]['code'], code)
        for name in ('explicit-bell', 'local-shadow', 'explicit-import-shadow', 'explicit-static-id'):
            self.assertEqual(checks[name]['exit_code'], 0)


if __name__ == '__main__':
    unittest.main()
