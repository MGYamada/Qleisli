"""Passive history preservation; never execute or extract saved sources.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
# Scope notes: "tests/fixtures/authoring_sessions/finite-adts-v030/README.md".
# Original bytes: "tests/fixtures/authoring_sessions/finite-adts-v030/first.tar.xz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/index.json".
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import tarfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'tests/fixtures/authoring_sessions/finite-adts-v030'


class FirstFiniteADTs(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        index_bytes = (FIXTURES / 'index.json').read_bytes()
        if hashlib.sha256(index_bytes).hexdigest() != '1c2f1e7dd7364157ecdf2f7b49068c11b872868b85104066353d64d1aa34fefc':
            raise AssertionError('first index changed')
        index = json.loads(index_bytes)
        stored = (FIXTURES / 'first.tar.xz').read_bytes()
        if (len(stored), hashlib.sha256(stored).hexdigest()) != (
                862696, 'f3857707618584c552821edc5b207bf461a94913815108c77b55306695385f72'):
            raise AssertionError('first archive changed')
        cls.data = {}
        total = 0
        with tarfile.open(fileobj=io.BytesIO(stored), mode='r:xz') as archive:
            for member in archive:
                path = PurePosixPath(member.name)
                if (not member.isfile() or member.mode != 0o644 or path.is_absolute()
                        or '..' in path.parts or str(path) != member.name
                        or member.name in cls.data or member.name not in index['records']):
                    raise AssertionError('noncanonical historical record')
                row = index['records'][member.name]
                if member.size != row['bytes'] or member.size > 8_000_000:
                    raise AssertionError('historical record exceeds declared bounds')
                total += member.size
                if total > 30_807_429:
                    raise AssertionError('historical expansion exceeds bounds')
                data = archive.extractfile(member).read(member.size + 1)
                if (len(data), hashlib.sha256(data).hexdigest()) != (row['bytes'], row['sha256']):
                    raise AssertionError('historical bytes changed')
                cls.data[member.name] = data
        if set(cls.data) != set(index['records']) or total != 30_807_429:
            raise AssertionError('first history is incomplete')

    def test_source_predictions_and_actual_refusals_remain_distinct(self):
        self.assertEqual(len(self.data), 60)
        plan = json.loads(self.data['source/plan.json'])
        report = json.loads(self.data['source/report.json'])
        self.assertEqual((len(plan['cases']), len(plan['sources'])), (10, 20))
        self.assertEqual(len(report['commands']), 12)
        self.assertEqual(report['prediction_mismatches'], [])
        self.assertTrue(report['source_unchanged'])
        self.assertTrue(report['first_source_unchanged'])
        self.assertEqual(report['before'], report['after'])
        self.assertEqual(sum(row['exit_code'] == 0 for row in report['commands']), 4)
        self.assertEqual(sum(row['exit_code'] == 1 for row in report['commands']), 8)
        for i, row in enumerate(report['commands'], 1):
            self.assertEqual(json.loads(self.data[f'source/observation-{i:02}.json']), row)
        refusals = [json.loads(row['stdout'])['diagnostics'][0]['code']
                    for row in report['commands'] if row['exit_code'] == 1]
        self.assertEqual(refusals.count('parse'), 7)
        self.assertEqual(refusals.count('type_mismatch'), 1)

    def test_failed_lean_attempt_is_not_promoted_to_a_proof(self):
        first = json.loads(self.data['encoding/observation-01/report.json'])
        self.assertEqual([row['exit_code'] for row in first['commands']], [0, 1])
        self.assertTrue(first['source_unchanged'])
        self.assertEqual(first['before'], first['after'])
        output = self.data['encoding/observation-01/proof.stdout']
        self.assertIn(b'failed to synthesize', output)
        self.assertIn(b'sorryAx', output)
        self.assertEqual(self.data['encoding/FiniteTagStudy.lean'],
                         self.data['encoding/observation-01/FiniteTagStudy.lean.txt'])

    def test_separate_repair_retains_the_actual_standard_axiom_scope(self):
        current = json.loads(self.data['encoding/observation-02/report.json'])
        self.assertEqual([row['exit_code'] for row in current['commands']], [0, 0])
        self.assertTrue(current['source_unchanged'])
        self.assertEqual(current['before'], current['after'])
        output = self.data['encoding/observation-02/proof.stdout'].decode()
        lines = output.splitlines()
        self.assertEqual(len(lines), 15)
        self.assertTrue(all(line.endswith('depends on axioms: [propext]') for line in lines))
        self.assertNotIn('sorryAx', output)
        self.assertEqual(self.data['encoding/observation-02/proof.stderr'], b'')
        self.assertEqual(self.data['encoding/FiniteTagStudy-v2.lean'],
                         self.data['encoding/observation-02/FiniteTagStudy-v2.lean.txt'])


if __name__ == '__main__':
    unittest.main()
