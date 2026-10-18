"""Passive first-byte retention only; never execute historical code or packets.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import base64
import gzip
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import unittest

ROOT = Path(__file__).resolve().parents[1]


class FirstNativeEdition(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        stored = (ROOT / 'tests/fixtures/authoring_sessions/native-edition-v030/first.json.gz').read_bytes()
        assert hashlib.sha256(stored).hexdigest() == '80df6cba3f022d8b2aafe4824c468d034309d100f61e5cbbc784b83f6e11483b'
        with gzip.GzipFile(fileobj=io.BytesIO(stored)) as archive:
            raw = archive.read(3_000_001)
        assert len(raw) == 2232842
        assert hashlib.sha256(raw).hexdigest() == '92fd570ef968726e17dce0633d8325912eef5da0f90f44d6abc3f8918d3cc199'
        payload = json.loads(raw)
        assert payload['format'] == 'qleisli.inert-first-edition-study' and payload['version'] == 1
        assert len(payload['records']) == 791
        cls.records = {}
        for row in payload['records']:
            name = row['path']
            path = PurePosixPath(name)
            assert not path.is_absolute() and '..' not in path.parts and str(path) == name
            assert '\\' not in name and '\x00' not in name and name not in cls.records
            data = base64.b64decode(row['base64'], validate=True)
            assert (len(data), hashlib.sha256(data).hexdigest()) == (row['bytes'], row['sha256'])
            assert type(row['mode']) is int and row['mode'] in (0o600, 0o644, 0o755)
            cls.records[name] = data
        assert sum(map(len, cls.records.values())) == 1566434

    def document(self, path):
        return json.loads(self.records[path])

    def test_original_index_and_every_first_member_remain_exact(self):
        raw = self.records['SESSION.pending.json']
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
                         '5cb5921743e33f978d72dc2ed8c0e6a3be06a9e4d1848a715ec26e98643c7498')
        index = json.loads(raw)
        self.assertEqual(len(index['files']), 757)
        for name, expected in index['files'].items():
            data = self.records[name]
            self.assertEqual((len(data), hashlib.sha256(data).hexdigest()),
                             (expected['bytes'], expected['sha256']))
        self.assertEqual(len(set(self.records) - set(index['files'])), 34)
        readme = (ROOT / 'tests/fixtures/authoring_sessions/native-edition-v030/README.md').read_text()
        self.assertIn(f'{len(self.records):,} original files, '
                      f'{sum(map(len, self.records.values())):,} expanded source/log bytes', readme)
        self.assertIn('80df6cba3f022d8b2aafe4824c468d034309d100f61e5cbbc784b83f6e11483b', readme)
        self.assertIn('(first.json.gz)', readme)

    def test_usage_entry_and_manifest_failures_are_not_reclassified(self):
        self.assertIn(b'unsupported --json', self.records['first-attempt-classification.txt'])
        before = self.document('attempt02/record.pending.json')['cases']
        self.assertEqual([(c['exit'], len(c['native_calls'])) for c in before],
                         [(1, 0)] * 7 + [(0, 76)])
        scalar = self.document('attempt02/cases/selected-scalar/stdout.json')
        self.assertEqual(scalar['diagnostics'][0]['code'], 'invalid_entry')
        self.assertNotIn('selected-scalar', [c['name'] for c in before])
        after = self.document('attempt03/record.json')['cases']
        self.assertEqual([(c['name'], c['exit'], len(c['native_calls'])) for c in after],
                         [('selected-scalar', 0, 76), ('nested-mismatch', 1, 0)])
        self.assertEqual(self.records['attempt02/cases/selected-scalar/main.qli'].replace(b'fn main(', b'fn scalar('),
                         self.records['attempt03/cases/selected-scalar/main.qli'])

    def test_before_native_context_gap_and_all_seven_queries_remain(self):
        record = self.document('native-contract-before/record.json')
        self.assertEqual(record['head'], 'c6a95e8488ad44bc398f9cfa97def807058436e5')
        self.assertEqual(len(record['mode_inventory']), 13)
        expected = ['current-QLV2', 'wrong-product', 'planned-QLV3-2026', 'planned-QLV3-2027',
                    'planned-QLV3-zero', 'inner-QLV1-is-not-external', 'trailing-QLV2']
        self.assertEqual([row['name'] for row in record['observations']], expected)
        self.assertEqual([row['exit'] for row in record['observations']], [0] + [1] * 6)
        for row in record['observations']:
            base = 'native-contract-before/' + row['name'] + '/'
            for name, key in [('request.bin', 'request_sha256'), ('stdout.txt', 'stdout_sha256'),
                              ('stderr.txt', 'stderr_sha256')]:
                self.assertEqual(hashlib.sha256(self.records[base + name]).hexdigest(), row[key])
        self.assertEqual(self.records['native-contract-before/current-QLV2/stdout.txt'],
                         b'qleisli.qirf-native 2\naccepted\ncaller\n21\n0\n')
        for label, edition in [('2026', 2026), ('2027', 2027), ('zero', 0)]:
            base = 'native-contract-before/planned-QLV3-' + label + '/'
            self.assertEqual(self.records[base + 'request.bin'][:8], b'QLV3' + edition.to_bytes(4, 'little'))
            self.assertEqual(self.records[base + 'stdout.txt'], b'qleisli.qirf-native 2\nerror\nformat\n')


if __name__ == '__main__':
    unittest.main()
