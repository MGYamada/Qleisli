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
    def test_first_migration_refusals_do_not_claim_a_completed_native_run(self):
        stored = (ROOT / 'tests/fixtures/authoring_sessions/native-edition-v030/context-migration-first.json.gz').read_bytes()
        self.assertEqual(hashlib.sha256(stored).hexdigest(),
                         '228aaa63263873bbdb101f56da047859595b0c5d0687bf364db94364687e8e85')
        with gzip.GzipFile(fileobj=io.BytesIO(stored)) as archive:
            raw = archive.read(1_039_732)
        self.assertEqual(len(raw), 1_039_731)
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
                         '754add7032d904257bcc3ecce72fdc96ba8f909456461edbfab1b10872769df2')
        record = json.loads(raw)
        self.assertEqual((record['format'], record['version']), ('qleisli.edition-context-first-migration', 1))
        self.assertEqual(len(record['records']), 13)
        data = {}
        for name, row in record['records'].items():
            data[name] = base64.b64decode(row['base64'], validate=True)
            self.assertEqual(hashlib.sha256(data[name]).hexdigest(), row['sha256'])
        attempt = json.loads(data['native-regressions-v1.json'])
        self.assertEqual([row['exit_code'] for row in attempt['commands']], [0, 0, 0, 101])
        self.assertIn(b'6 passed; 1 failed; 0 ignored', data['native-regressions-v1-3.stdout'])
        self.assertIn(b'project exceeds 10-byte aggregate source and manifest limit', data['native-regressions-v1-3.stdout'])
        self.assertIn(b'nonminimal_bool', data['compat-v2-3.stderr'])
        self.assertEqual(json.loads(data['source-integrity-v1.json'])['commands'][0]['status'], 'failed')
        self.assertEqual(json.loads(data['source-integrity-v2.json'])['commands'][1]['status'], 'failed')

    def test_first_lint_and_sandbox_diagnostics_keep_their_actual_scope(self):
        stored = (ROOT / 'tests/fixtures/authoring_sessions/native-edition-v030/context-validation-first.json.gz').read_bytes()
        self.assertEqual(hashlib.sha256(stored).hexdigest(),
                         'e9f8a889bd773390d4e86d7b3fc915374069aabf9a2c609134528f2aae5f6948')
        with gzip.GzipFile(fileobj=io.BytesIO(stored)) as archive:
            raw = archive.read(124_307)
        self.assertEqual(len(raw), 124_306)
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
                         '4c7322d5813e9610494e4cd4b24aa433489d04c067f0735e3d313396a52e2e92')
        record = json.loads(raw)
        self.assertEqual((record['format'], record['version']), ('qleisli.edition-context-first-validation', 1))
        self.assertEqual(set(record['records']), {'src/frontend/project/manifest.rs', 'src/interchange/process.rs',
                         'compat-v1.json', 'compat-v1-0.stdout', 'compat-v1-0.stderr',
                         'capture-tests-v2.json', 'capture-tests-v2-0.stdout', 'capture-tests-v2-0.stderr'})
        data = {}
        for name, row in record['records'].items():
            data[name] = base64.b64decode(row['base64'], validate=True)
            self.assertEqual(hashlib.sha256(data[name]).hexdigest(), row['sha256'])
        self.assertIn(b'4 previous errors', data['compat-v1-0.stderr'])
        self.assertIn(b'needless_borrow', data['compat-v1-0.stderr'])
        self.assertIn(b'278 passed; 1 failed; 167 ignored', data['capture-tests-v2-0.stdout'])
        self.assertIn(b'PermissionDenied', data['capture-tests-v2-0.stdout'])

    def test_first_capture_test_setup_failures_are_not_native_failures(self):
        stored = (ROOT / 'tests/fixtures/authoring_sessions/native-edition-v030/context-tests-first.json.gz').read_bytes()
        self.assertEqual(hashlib.sha256(stored).hexdigest(),
                         '1c619586c16e5732311717333591e5d7a2c7424be6dfa98565bd67feb685db61')
        with gzip.GzipFile(fileobj=io.BytesIO(stored)) as archive:
            raw = archive.read(37_250)
        self.assertEqual(len(raw), 37_249)
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
                         'fbdf78dfe8b85cf0f72a38523aaf54de0ff539bd8d39e5c534132024d2230f7d')
        record = json.loads(raw)
        self.assertEqual((record['format'], record['version']), ('qleisli.edition-context-first-test', 1))
        self.assertEqual(set(record['records']), {'tests/editions.rs', 'tests/common/mod.rs',
                         'capture-tests-v1.json', 'capture-tests-v1-1.stdout', 'capture-tests-v1-1.stderr'})
        data = {}
        for name, row in record['records'].items():
            data[name] = base64.b64decode(row['base64'], validate=True)
            self.assertEqual(hashlib.sha256(data[name]).hexdigest(), row['sha256'])
        self.assertIn(b'8 passed; 3 failed; 6 ignored', data['capture-tests-v1-1.stdout'])
        self.assertEqual(data['capture-tests-v1-1.stdout'].count(b'kind: NotFound'), 3)
        self.assertIn(b'fn write(&self, name: &str, source: &str)', data['tests/common/mod.rs'])
        self.assertIn('No nested/src files were written', record['classification'])

    def test_original_sources_before_context_capture_remain_inert_and_exact(self):
        stored = (ROOT / 'tests/fixtures/authoring_sessions/native-edition-v030/context-source-first.json.gz').read_bytes()
        self.assertEqual(hashlib.sha256(stored).hexdigest(),
                         '9393bc8b48d43ca3d45b6ed729ce5528593366004650a793b699a878cc208cfb')
        with gzip.GzipFile(fileobj=io.BytesIO(stored)) as archive:
            raw = archive.read(192_672)
        self.assertEqual(len(raw), 192_671)
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
                         '8638df9b724617a63e5f6d674ef87bf3d67626d3b950566c5165f10200310c7b')
        record = json.loads(raw)
        self.assertEqual((record['format'], record['version'], record['head']),
                         ('qleisli.edition-context-first', 1, '8dde351ce8c19d091bdae01c3e9ea49d5e34b368'))
        self.assertEqual(set(record['files']), {
            'src/frontend/mod.rs', 'src/lib.rs', 'src/frontend/project.rs',
            'src/frontend/project/edition.rs', 'src/frontend/project/manifest.rs',
            'src/frontend/compile/mod.rs', 'tests/editions.rs',
            'docs/src/reference/packages-and-artifacts.md',
        })
        for row in record['files'].values():
            data = base64.b64decode(row['base64'], validate=True)
            self.assertEqual(hashlib.sha256(data).hexdigest(), row['sha256'])
            self.assertIn(row['mode'], (0o644, 0o755))
        original = base64.b64decode(record['files']['src/frontend/project/manifest.rs']['base64'], validate=True)
        self.assertIn(b'let root = qrate_source_root(directory)?;', original)
        self.assertNotIn(b'manifest: Arc<', original)

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
