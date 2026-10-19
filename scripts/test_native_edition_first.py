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
    def test_capacity_history_keeps_the_first_oracle_and_actual_failures(self):
        stored = (ROOT / 'tests/fixtures/authoring_sessions/native-edition-v030/consumer-capacity-first.json.gz').read_bytes()
        self.assertEqual(hashlib.sha256(stored).hexdigest(),
                         'f838c733283878a32b1be03f16190f49748dce7bd8b3d46f9752a5d7d0ed8bd0')
        with gzip.GzipFile(fileobj=io.BytesIO(stored)) as archive:
            raw = archive.read(93_122)
        self.assertEqual(len(raw), 93_121)
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
                         '60ab92b384799800eebfc5eb1d0dd08b3d05a11b335afa1c7b6d4c49f3cf4eb9')
        record = json.loads(raw)
        self.assertEqual((record['format'], record['version']),
                         ('qleisli.capacity-consumer-first-observations', 1))
        self.assertEqual(record['source_head'], '4f3cff5c914ff83f2103102698a559d5648166d2')
        self.assertEqual(set(record['records']), {
            'original/tests/source_capacities.rs', 'original/tests/common/mod.rs',
            'original/tests/Qargo.toml', 'source-capacity-ci-first.json',
            'source-capacity-local-first.json', 'observe-capacity-before.py',
            'validate-capacity-after.py', 'source-capacity-validation.json',
        })
        data = {}
        for name, row in record['records'].items():
            data[name] = base64.b64decode(row['base64'], validate=True)
            self.assertEqual((len(data[name]), hashlib.sha256(data[name]).hexdigest()),
                             (row['bytes'], row['sha256']))
        self.assertIn(b'let total = loaded.modules.values().map(|m| m.source.len() as u64).sum();',
                      data['original/tests/source_capacities.rs'])
        hosted = json.loads(data['source-capacity-ci-first.json'])
        self.assertEqual(hosted['headRevision'], record['source_head'])
        self.assertEqual(hosted['job']['conclusion'], 'failure')
        self.assertFalse(hosted['logTruncated'])
        self.assertIn('policy(total)).is_ok()', hosted['log'])
        first = json.loads(data['source-capacity-local-first.json'])
        self.assertEqual(first['exit_code'], 101)
        self.assertTrue(first['source_unchanged'])
        repaired = json.loads(data['source-capacity-validation.json'])
        self.assertTrue(repaired['source_unchanged'])
        self.assertEqual([row['label'] for row in repaired['commands']],
                         ['normal-tests', 'normal-clippy', 'msrv-tests', 'msrv-clippy'])
        self.assertEqual([row['exit_code'] for row in repaired['commands']], [0, 0, 0, 0])
        self.assertEqual(record['separate_observer_attempt']['exit_code'], 130)

    def test_consumer_observer_failures_remain_separate_from_product_results(self):
        stored = (ROOT / 'tests/fixtures/authoring_sessions/native-edition-v030/consumer-observer-first.json.gz').read_bytes()
        self.assertEqual(hashlib.sha256(stored).hexdigest(),
                         '5a08506e3160bd169f55210b4fd7433dbdf0bd0f389eb4d398b2b446756414cc')
        with gzip.GzipFile(fileobj=io.BytesIO(stored)) as archive:
            raw = archive.read(39_942)
        self.assertEqual(len(raw), 39_941)
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
                         'ebf48db7df4c6dc3e759bc568885cc0242ca000475256d8afe33a8aa70d73c15')
        record = json.loads(raw)
        self.assertEqual((record['format'], record['version']),
                         ('qleisli.edition-consumer-observer-failures', 1))
        self.assertEqual(len(record['records']), 7)
        data = {}
        for name, row in record['records'].items():
            path = PurePosixPath(name)
            self.assertFalse(path.is_absolute())
            self.assertNotIn('..', path.parts)
            self.assertEqual(str(path), name)
            data[name] = base64.b64decode(row['base64'], validate=True)
            self.assertEqual((len(data[name]), hashlib.sha256(data[name]).hexdigest()),
                             (row['bytes'], row['sha256']))
        self.assertIn(b"No module named 'openqasm3'", data['interop-validator.stderr'])
        self.assertIn(b"KeyError: 'structuredContent'", data['passive-reader-first.stderr'])
        self.assertEqual(json.loads(data['interop-validator.json'])['command']['exit_code'], 1)
        self.assertEqual(json.loads(data['passive-reader-first.json'])['exit_code'], 1)

    def test_first_consumer_failures_preserve_sources_and_actual_diagnostics(self):
        stored = (ROOT / 'tests/fixtures/authoring_sessions/native-edition-v030/consumer-validation-first.json.gz').read_bytes()
        self.assertEqual(hashlib.sha256(stored).hexdigest(),
                         'cefe8d9c6a2637892c4899a3c28422a9154e5541bce51ecb8f06fb4167642734')
        with gzip.GzipFile(fileobj=io.BytesIO(stored)) as archive:
            raw = archive.read(532_294)
        self.assertEqual(len(raw), 532_293)
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
                         '4524d2f8189ff48530e13272827e156ee8d83742f6af60a7b22f135f637d9603')
        record = json.loads(raw)
        self.assertEqual((record['format'], record['version']),
                         ('qleisli.edition-consumer-first-observations', 1))
        self.assertEqual(len(record['records']), 26)
        data = {}
        for name, row in record['records'].items():
            path = PurePosixPath(name)
            self.assertFalse(path.is_absolute())
            self.assertNotIn('..', path.parts)
            self.assertEqual(str(path), name)
            data[name] = base64.b64decode(row['base64'], validate=True)
            self.assertEqual((len(data[name]), hashlib.sha256(data[name]).hexdigest()),
                             (row['bytes'], row['sha256']))
            self.assertIn(row['mode'], (0o600, 0o644))
        self.assertIn(b'error[E0061]', data['first-cargo.stderr'])
        self.assertIn(b'Kernel::selected()', data['first-adapter.rs'])
        self.assertIn(b'failed to select a version', data['normal-3.stderr'])
        self.assertEqual(json.loads(data['first-clippy-context.json'])['command']['exit_code'], 101)
        self.assertIn(b'import_openqasm3(r#', data['root-ci-before-0'])
        for name, contents in data.items():
            if name.startswith('pr423-ci-'):
                diagnostic = json.loads(contents)
                if 'structuredContent' in diagnostic:
                    self.assertEqual(set(diagnostic), {'content', 'structuredContent'})
                    diagnostic = diagnostic['structuredContent']
                self.assertEqual(diagnostic['headRevision'], record['source_revisions']['qleisli'])
                self.assertFalse(diagnostic['logTruncated'])

    def test_first_cli_context_failures_keep_invocation_and_consumer_errors_distinct(self):
        stored = (ROOT / 'tests/fixtures/authoring_sessions/native-edition-v030/cli-validation-first.json.gz').read_bytes()
        self.assertEqual(hashlib.sha256(stored).hexdigest(),
                         '7893c5d121deaa888819d7ba60d9322d964fa2794b0d886a4c132db2f1217252')
        with gzip.GzipFile(fileobj=io.BytesIO(stored)) as archive:
            raw = archive.read(13_129)
        self.assertEqual(len(raw), 13_128)
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
                         'e5627a9acb901a409fdf3bda3fc7814769d4c58330221dd3b9c8e1fe46ab70c1')
        record = json.loads(raw)
        self.assertEqual((record['format'], record['version']), ('qleisli.cli-edition-first-validation', 1))
        self.assertEqual(len(record['records']), 5)
        data = {}
        for name, row in record['records'].items():
            path = PurePosixPath(name)
            self.assertFalse(path.is_absolute())
            self.assertNotIn('..', path.parts)
            self.assertEqual(str(path), name)
            data[name] = base64.b64decode(row['base64'], validate=True)
            self.assertEqual((len(data[name]), hashlib.sha256(data[name]).hexdigest()),
                             (row['bytes'], row['sha256']))
            self.assertIn(row['mode'], (0o600, 0o644))
        self.assertIn(b"No such file or directory: 'target/debug/qleisli'", data['cli-json.stderr'])
        self.assertIn(b'raw verification requires --edition=2026', data['cli-json.stderr'])
        self.assertEqual([row['exit_code'] for row in json.loads(data['validation-first.json'])], [0, 0, 1])
        self.assertIn('omitted the documented positional absolute binary argument', record['classification'])

    def test_first_python_validation_keeps_the_original_diagnostic_oracle_error(self):
        stored = (ROOT / 'tests/fixtures/authoring_sessions/native-edition-v030/python-validation-first.json.gz').read_bytes()
        self.assertEqual(hashlib.sha256(stored).hexdigest(),
                         'a9a8c688af4a49b554a40cdb7ae56fe919c73fe2c0dd0d832c508121a9fff297')
        with gzip.GzipFile(fileobj=io.BytesIO(stored)) as archive:
            raw = archive.read(40_863)
        self.assertEqual(len(raw), 40_862)
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
                         'ebd3fcce00d0c63a354f572f0a2f10ce9e15b295909dadedb7b7677942648abc')
        record = json.loads(raw)
        self.assertEqual((record['format'], record['version']), ('qleisli.python-edition-first-validation', 1))
        self.assertEqual(len(record['records']), 9)
        data = {}
        for name, row in record['records'].items():
            path = PurePosixPath(name)
            self.assertFalse(path.is_absolute())
            self.assertNotIn('..', path.parts)
            self.assertEqual(str(path), name)
            data[name] = base64.b64decode(row['base64'], validate=True)
            self.assertEqual((len(data[name]), hashlib.sha256(data[name]).hexdigest()),
                             (row['bytes'], row['sha256']))
            self.assertIn(row['mode'], (0o600, 0o644))
        metadata = json.loads(data['interop-first-metadata.json'])
        self.assertEqual((metadata['status'], metadata['tests'], metadata['skipped']), ('failed', 12, []))
        self.assertIn(b'FAILED (failures=2)', data['interop-native.stderr'])
        actual = json.loads(json.loads(data['manifest-unsupported-first.json'])['stdout'])
        diagnostic = actual['diagnostics'][0]
        self.assertEqual(diagnostic['code'], 'project')
        self.assertEqual(diagnostic['primary']['path'], 'Qargo.toml')
        self.assertIn('unsupported Qleisli edition "2027"', diagnostic['message'])
        self.assertEqual(json.loads(data['source-after-build.json']), json.loads(data['source-after-tests.json']))
        self.assertIn('Transient test-project files were not captured separately', record['classification'])

    def test_first_python_context_sources_keep_sandbox_and_real_refusals_separate(self):
        stored = (ROOT / 'tests/fixtures/authoring_sessions/native-edition-v030/python-context-first.json.gz').read_bytes()
        self.assertEqual(hashlib.sha256(stored).hexdigest(),
                         '762f4872db96fb3c4380549402af59d63a90043c7d0375ab35833c02640a7616')
        with gzip.GzipFile(fileobj=io.BytesIO(stored)) as archive:
            raw = archive.read(47_994)
        self.assertEqual(len(raw), 47_993)
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
                         'e0e99516feed1b71f5697fef6bd3bb302c622702aa55892e3929069fb20f4a03')
        record = json.loads(raw)
        self.assertEqual((record['format'], record['version']), ('qleisli.python-edition-first', 1))
        self.assertEqual(len(record['records']), 32)
        data = {}
        for name, row in record['records'].items():
            path = PurePosixPath(name)
            self.assertFalse(path.is_absolute())
            self.assertNotIn('..', path.parts)
            self.assertEqual(str(path), name)
            data[name] = base64.b64decode(row['base64'], validate=True)
            self.assertEqual((len(data[name]), hashlib.sha256(data[name]).hexdigest()),
                             (row['bytes'], row['sha256']))
            self.assertIn(row['mode'], (0o600, 0o644))
        for environment in ('sandbox', 'unrestricted'):
            prefix = environment + '/'
            self.assertEqual(data[prefix + 'before.json'], data[prefix + 'after.json'])
            before = json.loads(data[prefix + 'before.json'])
            for path, digest in before['sources'].items():
                self.assertEqual(record['source_refs'][path], dict(commit=before['head'], sha256=digest))
            observed = json.loads(data[prefix + 'observations.json'])
            self.assertEqual(observed[0]['exception'], 'TypeError')
            self.assertIn("unexpected keyword argument 'edition'", observed[0]['message'])
            self.assertEqual([row['exit_code'] for row in observed[2:]], [0, 2, 1])
            self.assertIn(b'edition="2026"', data[prefix + 'desired.py'])
        sandbox = json.loads(data['sandbox/observations.json'])
        actual = json.loads(data['unrestricted/observations.json'])
        self.assertEqual(sandbox[1]['diagnostics'][0]['code'], 'connection')
        self.assertIn('ps', sandbox[1]['message'])
        self.assertEqual(actual[1]['diagnostics'][0]['code'], 'edition')
        self.assertIn('--edition=2026', actual[1]['message'])
        self.assertEqual(data['sandbox/project/main.qli'], data['unrestricted/project/main.qli'])
        self.assertIn('not fresh build attestation', record['classification'])

    def test_first_helper_refusals_retain_real_hierarchy_diagnostics(self):
        stored = (ROOT / 'tests/fixtures/authoring_sessions/native-edition-v030/native-helper-first.json.gz').read_bytes()
        self.assertEqual(hashlib.sha256(stored).hexdigest(),
                         'aea25ce49107d31122f240b72937bd96189e4d27ebaae5bf0d2a0ada631ba50b')
        with gzip.GzipFile(fileobj=io.BytesIO(stored)) as archive:
            raw = archive.read(19_230)
        self.assertEqual(len(raw), 19_229)
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
                         '21e9acde48e4d4d06728231730c6d3ff3f46274505d45920cebbe781a3819c89')
        record = json.loads(raw)
        self.assertEqual((record['format'], record['version']),
                         ('qleisli.native-edition-helper-first', 1))
        self.assertEqual(len(record['records']), 19)
        data = {}
        for name, row in record['records'].items():
            path = PurePosixPath(name)
            self.assertFalse(path.is_absolute())
            self.assertNotIn('..', path.parts)
            self.assertEqual(str(path), name)
            data[name] = base64.b64decode(row['base64'], validate=True)
            self.assertEqual((len(data[name]), hashlib.sha256(data[name]).hexdigest()),
                             (row['bytes'], row['sha256']))
            self.assertIn(row['mode'], (0o600, 0o644))
        first = json.loads(data['first.json'])
        self.assertEqual(first['exit_code'], 1)
        for path, digest in first['sources'].items():
            self.assertEqual(record['source_refs'][path], dict(commit=first['head'], sha256=digest))
        self.assertIn(b'qleisli.native-result 3\\nerror\\nformat\\n', data['first.stderr'])
        self.assertEqual(json.loads(data['pure-cli.json'])['exit_code'], 2)
        self.assertIn(b'unrecognized arguments: --kernel', data['pure-cli.stderr'])
        self.assertEqual(json.loads(data['source-kernel-v4.json'])['exit_code'], 1)
        self.assertIn(b'FAILED (failures=4)', data['source-kernel-v4.stderr'])
        self.assertEqual(json.loads(data['coverage-first.json'])['exit_code'], 1)
        self.assertIn(b'production source binding changed: src/bin/qleisli/source_plan.rs',
                      data['coverage-first.stderr'])
        observed = json.loads(data['hierarchy-error-first/observations.json'])
        self.assertEqual([row['name'] for row in observed], ['invalid-actual', 'invalid-required'])
        for row in observed:
            prefix = 'hierarchy-error-first/' + row['name']
            self.assertEqual((row['exit_code'], row['expected_retained_code']), (1, 'format'))
            self.assertEqual(data[prefix + '.stdout'], b'qleisli.native-result 3\nerror\ninvalid_ir\n')
            self.assertEqual(data[prefix + '.stderr'], b'')
            self.assertTrue(data[prefix + '.input'].startswith(b'QLV3'))
        self.assertIn('complete preimage and child CLI streams were not captured', record['classification'])

    def test_first_native_rust_integration_keeps_failures_and_separate_repairs(self):
        stored = (ROOT / 'tests/fixtures/authoring_sessions/native-edition-v030/native-context-integration-first.json.gz').read_bytes()
        self.assertEqual(hashlib.sha256(stored).hexdigest(),
                         'e5ac7bbfe3c03d951e57879ad668f29585e5233cb4a8b96bb22f1c56500b16fb')
        with gzip.GzipFile(fileobj=io.BytesIO(stored)) as archive:
            raw = archive.read(2_204_866)
        self.assertEqual(len(raw), 2_204_865)
        self.assertEqual(hashlib.sha256(raw).hexdigest(),
                         'b180a032ce33dc1c26fbcd77cd3240d0fe33c00dcbb8f6d2c5ee0df0f9910b98')
        record = json.loads(raw)
        self.assertEqual((record['format'], record['version']),
                         ('qleisli.native-edition-first-integration', 1))
        self.assertEqual(len(record['records']), 113)
        data = {}
        for name, row in record['records'].items():
            path = PurePosixPath(name)
            self.assertFalse(path.is_absolute())
            self.assertNotIn('..', path.parts)
            self.assertEqual(str(path), name)
            data[name] = base64.b64decode(row['base64'], validate=True)
            self.assertEqual((len(data[name]), hashlib.sha256(data[name]).hexdigest()),
                             (row['bytes'], row['sha256']))
            self.assertIn(row['mode'], (0o600, 0o644, 0o755))
        self.assertEqual(json.loads(data['rust/check-first.json'])['exit_code'], 101)
        self.assertIn(b'15 passed; 2 failed; 0 ignored', data['rust/runtime-tests.stdout'])
        cli = json.loads(data['cli-first/observations.json'])
        self.assertEqual(len(cli), 13)
        self.assertEqual([row['exit_code'] for row in cli],
                         [0] * 6 + [1] * 3 + [0, 1, 0, 2])
        self.assertEqual(data['cli-first/before.json'], data['cli-first/after.json'])
        first = json.loads(data['component-alias-first/observations.json'])
        self.assertEqual([row['exit_code'] for row in first], [0, 0])
        fixed = json.loads(data['component-followup/observations.json'])
        self.assertEqual([row['exit_code'] for row in fixed], [0, 1, 1, 1] * 2)
        for row in fixed:
            self.assertTrue(row['stdout'].startswith('qleisli.native-result 3\n'))
        self.assertIn('not captured as files', record['classification'])

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
