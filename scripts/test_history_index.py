"""Inert container compatibility and history retention; never execute saved code.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import gzip
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch
import zlib

import test_finite_adts_first as history


class HistoryIndexContainerTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        fixtures = patch.object(history, 'FIXTURES', self.root)
        fixtures.start()
        self.addCleanup(fixtures.stop)
        self.payload = b'unchanged first source\x00\xff\n'
        self.member = 'objects/first-source'
        self.index = (json.dumps({'format': 'synthetic-test-only', 'version': 1,
            'records': {self.member: {'bytes': len(self.payload),
                'sha256': self.sha(self.payload), 'original_mode': 0o644}}}, indent=2) + '\n').encode()
        (self.root / 'index.json').write_bytes(self.index)
        self.archive = self.make_archive(self.payload)
        (self.root / 'history.tar.xz').write_bytes(self.archive)

    @staticmethod
    def sha(raw):
        return hashlib.sha256(raw).hexdigest()

    def make_archive(self, payload):
        output = io.BytesIO()
        with tarfile.open(fileobj=output, mode='w:xz', format=tarfile.USTAR_FORMAT) as archive:
            member = tarfile.TarInfo(self.member)
            member.mode, member.size, member.mtime = 0o644, len(payload), 0
            archive.addfile(member, io.BytesIO(payload))
        return output.getvalue()

    def materialize(self, stored=None):
        stored = gzip.compress(self.index, mtime=0) if stored is None else stored
        (self.root / 'index.json.gz').write_bytes(stored)
        pins = {'bytes': len(stored), 'decoded_bytes': len(self.index),
                'decoded_sha256': self.sha(self.index)}
        return stored, pins

    def read(self, index_name, index_hash, **options):
        return history.read_history(index_name, 'history.tar.xz', index_hash,
            len(self.archive), self.sha(self.archive), len(self.payload), **options)

    def test_legacy_json_and_explicit_gzip_preserve_identical_json_and_member_bytes(self):
        expected = {self.member: self.payload}
        self.assertEqual(self.read('index.json', self.sha(self.index)), expected)
        stored, pins = self.materialize()
        self.assertEqual(history.read_history_index('index.json.gz', self.sha(stored), index_gzip=pins), self.index)
        self.assertEqual(self.read('index.json.gz', self.sha(stored), index_gzip=pins), expected)

    def test_gzip_is_opt_in_and_never_inferred_from_the_filename(self):
        (self.root / 'index.json.gz').write_bytes(self.index)
        self.assertEqual(self.read('index.json.gz', self.sha(self.index)), {self.member: self.payload})
        stored, _ = self.materialize()
        with self.assertRaises((UnicodeError, json.JSONDecodeError)):
            self.read('index.json.gz', self.sha(stored))

    def test_stored_size_and_hash_are_checked_before_the_decoder(self):
        stored, pins = self.materialize()
        for identity, metadata in ((self.sha(b'wrong'), pins),
                                   (self.sha(stored), pins | {'bytes': len(stored) - 1}),
                                   (self.sha(stored), pins | {'bytes': len(stored) + 1})):
            with self.subTest(identity=identity, size=metadata['bytes']), \
                 patch.object(history.zlib, 'decompressobj') as decoder, \
                 self.assertRaisesRegex(AssertionError, 'stored gzip index changed'):
                history.read_history_index('index.json.gz', identity, index_gzip=metadata)
            decoder.assert_not_called()

    def test_truncation_corruption_wrong_codec_extra_member_and_trailing_bytes_refuse(self):
        stored, _ = self.materialize()
        corrupt = bytearray(stored)
        corrupt[-8] ^= 1  # Break the gzip checksum while retaining exact stored pins.
        variants = (stored[:-1], bytes(corrupt), zlib.compress(self.index),
                    stored + gzip.compress(b'', mtime=0), stored + b'\0', stored + b'trailing')
        for raw in variants:
            with self.subTest(raw_hash=self.sha(raw)):
                _, pins = self.materialize(raw)
                with self.assertRaisesRegex(AssertionError, 'gzip index'):
                    self.read('index.json.gz', self.sha(raw), index_gzip=pins)

    def test_decoded_hash_and_exact_length_refuse_even_with_valid_stored_pins(self):
        stored, pins = self.materialize()
        for metadata in (pins | {'decoded_sha256': self.sha(b'wrong')},
                         pins | {'decoded_bytes': len(self.index) - 1},
                         pins | {'decoded_bytes': len(self.index) + 1}):
            with self.subTest(metadata=metadata), self.assertRaisesRegex(AssertionError, 'gzip index'):
                self.read('index.json.gz', self.sha(stored), index_gzip=metadata)

    def test_malformed_pins_and_fixed_capacity_refuse_before_any_file_read(self):
        stored, pins = self.materialize()
        self.assertEqual(history.MAX_GZIP_HISTORY_INDEX_BYTES, 4 * 1024 * 1024)
        self.assertEqual(history.MAX_DECODED_HISTORY_INDEX_BYTES, 4 * 1024 * 1024)
        variants = (False, {}, pins | {'codec': 'auto'}, pins | {'bytes': True},
                    pins | {'bytes': -1}, pins | {'decoded_bytes': True},
                    pins | {'decoded_bytes': 0}, pins | {'decoded_sha256': 'bad'},
                    pins | {'bytes': history.MAX_GZIP_HISTORY_INDEX_BYTES + 1},
                    pins | {'decoded_bytes': history.MAX_DECODED_HISTORY_INDEX_BYTES + 1})
        for metadata in variants:
            with self.subTest(metadata=metadata), patch.object(Path, 'open') as opened, \
                 self.assertRaisesRegex(AssertionError, 'gzip index'):
                history.read_history_index('index.json.gz', self.sha(stored), index_gzip=metadata)
            opened.assert_not_called()

    def test_compressed_index_still_enforces_existing_archive_member_hashes(self):
        stored, pins = self.materialize()
        # A freshly pinned archive cannot replace the original member identity.
        self.archive = self.make_archive(b'X' + self.payload[1:])
        (self.root / 'history.tar.xz').write_bytes(self.archive)
        with self.assertRaisesRegex(AssertionError, 'historical bytes changed'):
            self.read('index.json.gz', self.sha(stored), index_gzip=pins)


class QforReferenceFirstHistory(unittest.TestCase):
    # "tests/fixtures/authoring_sessions/qfor-boundary-v030/reference-first.tar.xz"
    # "tests/fixtures/authoring_sessions/qfor-boundary-v030/reference-first-index.json"
    # "tests/fixtures/authoring_sessions/qfor-boundary-v030/reference-first-validation.json"
    @classmethod
    def setUpClass(cls):
        cls.root = history.ROOT / 'tests/fixtures/authoring_sessions/qfor-boundary-v030'
        with patch.object(history, 'FIXTURES', cls.root):
            cls.data = history.read_history(
                'reference-first-index.json', 'reference-first.tar.xz',
                'abedabfc40d871ab0690b1ce462df38c9a1bd2e1a76517652ad453e768c52ea5',
                17852, 'e8c057b15ce7aa7939ef17e859b0924a93bc742bed0e684a0676bb30e81e66ce',
                177485)
        cls.index = json.loads((cls.root / 'reference-first-index.json').read_bytes())

    def raw(self, name):
        return self.data[self.index['original_records'][name]['record']]

    def record(self, name):
        return json.loads(self.raw(name))

    def test_first_sources_and_frozen_reference_contexts_remain_exact(self):
        self.assertEqual((len(self.index['original_records']), len(self.data)), (143, 62))
        for row in self.index['original_records'].values():
            blob = self.data[row['record']]
            self.assertEqual((len(blob), hashlib.sha256(blob).hexdigest(), row['original_mode']),
                             (row['bytes'], row['sha256'], 0o644))
        packet = self.record('packet.json')
        for name, row in packet['files'].items():
            self.assertEqual(hashlib.sha256(self.raw(name)).hexdigest(), row['sha256'])
        capture = self.record('first-capture.json')
        self.assertEqual(capture['parent_history'], 'none')
        self.assertEqual(capture['repairs_requested'], 0)
        for cohort in ('current', 'historical'):
            response = self.record(cohort + '-first-response.json')
            report = self.record(cohort + '-isolation-report.json')
            self.assertFalse(report['other_file_history_example_agent_or_compiler_output_consulted'])
            self.assertFalse(report['workspace_files_changed'])
            self.assertEqual(len(report['files_inspected']), 1)
            for task, source in response.items():
                name = cohort + '/' + task + '/main.qli'
                original = self.raw('first/' + name)
                self.assertEqual(original, source.encode())
                self.assertEqual(hashlib.sha256(original).hexdigest(), capture['sources'][name])

    def test_all_48_observations_and_independent_distributions_are_preserved(self):
        report = self.record('observed-first/report.json')
        self.assertEqual(report['status'], 'observed-stable')
        self.assertEqual(report['before'], report['after'])
        self.assertEqual(report['before']['head'], '66326f2f74eddd7be988cfb5f08921271f83359b')
        self.assertEqual(len(report['observations']), 48)
        expected = {'ghz': {'000': .5, '111': .5},
                    'arithmetic': {'00': .5, '11': .5}, 'qpe': {'11': 1.}}
        successful_runs = []
        for row in report['observations']:
            prefix = '-'.join(row[key] for key in ('variant', 'task', 'route', 'action'))
            for stream in ('stdout', 'stderr'):
                raw = self.raw('observed-first/' + prefix + '.' + stream)
                self.assertEqual(hashlib.sha256(raw).hexdigest(), row[stream + '_sha256'])
            document = json.loads(self.raw('observed-first/' + prefix + '.stdout'))
            self.assertEqual(document, row['document'])
            if row['action'] == 'run' and row['exit_code'] == 0:
                successful_runs.append(row)
                distribution = {}
                for outcome in document['result']['distribution']:
                    key = ''.join('1' if bit else '0' for bit in outcome['bits'])
                    distribution[key] = distribution.get(key, 0.) + outcome['probability']
                for key in distribution.keys() | expected[row['task']].keys():
                    self.assertAlmostEqual(distribution.get(key, 0.),
                                           expected[row['task']].get(key, 0.), places=10)
        self.assertEqual(len(successful_runs), 12)

    def test_observer_translations_are_separate_from_zero_author_repairs(self):
        plan = self.record('observed-first/plan.json')
        for name, identity in {**plan['originals'], **plan['derived_inputs']}.items():
            self.assertEqual(hashlib.sha256(self.raw(name)).hexdigest(), identity)
        self.assertEqual(plan['author_repairs'], 0)
        self.assertEqual(len(plan['translations']), 9)
        report = self.record('observed-first/report.json')
        private = [row for row in report['observations'] if row['exit_code'] != 0
                   and row['variant'] != 'historical-original']
        retired = [row for row in report['observations'] if row['variant'] == 'historical-original']
        self.assertEqual((len(private), len(retired)), (12, 12))
        self.assertTrue(all(row['route'] == 'selected-raw' for row in private))
        self.assertTrue(all(any(d['code'] == 'visibility' for d in row['document']['diagnostics'])
                            for row in private))
        self.assertTrue(all(row['exit_code'] != 0 for row in retired))
        summary = self.record('SUMMARY.json')
        self.assertEqual(summary['author_repairs'], {'current': 0, 'historical_surface': 0})
        self.assertEqual(summary['first_successes'],
                         {'current_project': 3, 'historical_surface_after_header_only_adapter': 3})
        self.assertIn('No observed repair-rate advantage', summary['finding'])
        self.assertIn('not historical compiler replay', summary['finding'])


class QforFixedFourierFirstHistory(unittest.TestCase):
    # "tests/fixtures/authoring_sessions/qfor-boundary-v030/fixed-fourier-first.tar.xz"
    # "tests/fixtures/authoring_sessions/qfor-boundary-v030/fixed-fourier-first-index.json"
    # "tests/fixtures/authoring_sessions/qfor-boundary-v030/fixed-fourier-first-validation.json"
    @classmethod
    def setUpClass(cls):
        cls.root = history.ROOT / 'tests/fixtures/authoring_sessions/qfor-boundary-v030'
        with patch.object(history, 'FIXTURES', cls.root):
            cls.data = history.read_history(
                'fixed-fourier-first-index.json', 'fixed-fourier-first.tar.xz',
                '7e1739b3848cc3ec3d1f6ea33662ba802d8a7093ad21077384c00f576fb7afe1',
                4920, 'faf3c30829b3d082862d14b03f063e1da241971d543e139520caa1ce55bfddad',
                16175)
        cls.index = json.loads((cls.root / 'fixed-fourier-first-index.json').read_bytes())

    def raw(self, name):
        return self.data[self.index['original_records'][name]['record']]

    def record(self, name):
        return json.loads(self.raw(name))

    def test_first_refusal_and_separate_repair_are_preserved(self):
        self.assertEqual((len(self.index['original_records']), len(self.data)), (15, 12))
        for row in self.index['original_records'].values():
            raw = self.data[row['record']]
            self.assertEqual((len(raw), hashlib.sha256(raw).hexdigest(), row['original_mode']),
                             (row['bytes'], row['sha256'], 0o644))
        first, repaired = self.raw('first/main.qli'), self.raw('attempt02/main.qli')
        self.assertEqual(repaired, first.replace(
            b'qif(a,b) { 0 => bit_identity, 1 => s }', b'controlled(s)(a,b)'))
        maintained = history.ROOT / 'tests/fixtures/frontend_v030/qfor/fixed-fourier/main.qli'
        self.assertEqual(maintained.read_bytes(), repaired)
        failure = self.record('first-observation-summary.json')
        self.assertEqual((failure['exit_code'], failure['code']), (101, 'unsupported'))
        source = first.decode()
        self.assertEqual(source[failure['span']['start']:failure['span']['end']],
                         failure['original_slice'])
        self.assertEqual(hashlib.sha256(first).hexdigest(), failure['source_sha256'])
        self.assertIn('not originally captured as separate streams', failure['scope'])

    def test_repaired_observation_retains_actual_exact_check_and_limits(self):
        report = self.record('attempt02-observation.json')
        self.assertEqual(report['exit_code'], 0)
        self.assertEqual(report['before'], report['after'])
        for suffix in ('attempt02/main.qli', 'driver02/src/main.rs'):
            identity = next(value for path, value in report['before'].items()
                            if path.endswith('/' + suffix))
            self.assertEqual(hashlib.sha256(self.raw(suffix)).hexdigest(), identity)
        self.assertIn(b'all16 exact coefficients and Gram checked', self.raw('attempt02.stdout'))
        self.assertIn(b'global phase counterexample refused', self.raw('attempt02.stdout'))
        plan = self.record('first-plan.json')
        self.assertEqual(plan['authored_qubits'], 2)
        self.assertIn('not a new isolated or zero-shot comparison', plan['kind'])


class OrdinaryReviewFirstHistory(unittest.TestCase):
    # "tests/fixtures/authoring_sessions/ordinary-execution-v030/review-first.tar.xz"
    # "tests/fixtures/authoring_sessions/ordinary-execution-v030/review-first-index.json"
    # "tests/fixtures/authoring_sessions/ordinary-execution-v030/review-first-validation.json"
    @classmethod
    def setUpClass(cls):
        cls.root = history.ROOT / 'tests/fixtures/authoring_sessions/ordinary-execution-v030'
        with patch.object(history, 'FIXTURES', cls.root):
            cls.data = history.read_history(
                'review-first-index.json', 'review-first.tar.xz',
                'ec958e42892c79ea70cec046b136a3b72241aa066798b1fc92d888555f4d4924',
                48124, 'b935e2df9ad637630d4d2da4bc422bd1423fdf00aafcef1a0549ff928f9a8859',
                285552)
        cls.index = json.loads((cls.root / 'review-first-index.json').read_bytes())

    def raw(self, name):
        return self.data[self.index['original_records'][name]['record']]

    def record(self, name):
        return json.loads(self.raw(name))

    def test_original_private_helper_failures_and_public_controls_remain_exact(self):
        self.assertEqual((len(self.index['original_records']), len(self.data)), (63, 35))
        for row in self.index['original_records'].values():
            raw = self.data[row['record']]
            self.assertEqual((len(raw), hashlib.sha256(raw).hexdigest(), row['original_mode']),
                             (row['bytes'], row['sha256'], 0o644))
        report = self.record('ordinary-private-helpers-first/report.json')
        self.assertEqual(report['before'], report['after'])
        self.assertEqual(len(report['observations']), 8)
        for row in report['observations']:
            expected = 0 if row['case'] == 'public-control' else 1
            self.assertEqual(row['exit_code'], expected)
            prefix = 'ordinary-private-helpers-first/' + row['case']
            document = json.loads(self.raw(prefix + '-' + row['action'] + '.stdout'))
            self.assertEqual(document, row['document'])
            source = self.raw(prefix + '/main.qli')
            path = next(path for path in report['before']
                        if path.endswith('/' + row['case'] + '/main.qli'))
            self.assertEqual(hashlib.sha256(source).hexdigest(), report['before'][path])
            self.assertEqual(b'pub fn helper' in source, row['case'] == 'public-control')
        self.assertIn(b'ordinary_result_checked', self.raw(
            'ordinary-python-consumers-first/hosted-check-interop.log'))

    def test_first_family_test_errors_and_separate_repair_are_not_production_claims(self):
        first = self.record('ordinary-family-cases-first-validation/report.json')
        self.assertEqual(first['status'], 'failed')
        self.assertIn(b'unexpected identifier', self.raw(
            'ordinary-family-cases-first-validation/FamilyCases.stdout'))
        repaired = self.record('ordinary-family-cases-repair-validation/report.json')
        self.assertEqual(repaired['status'], 'passed')
        self.assertEqual(repaired['before'], repaired['after'])
        self.assertEqual(len(repaired['commands']), 2)
        self.assertTrue(all(row['exit_code'] == 0 for row in repaired['commands']))
        self.assertIn(b'passed 12 complete input/all-history controls; at most one qubit', self.raw(
            'ordinary-family-cases-repair-validation/FamilyCases.stdout'))
        audit = json.loads(self.raw('ordinary-family-cases-repair-validation/FamilyAudit.stdout'))
        self.assertEqual(audit['checked'], 373)
        self.assertEqual(len(audit['required_theorems']), 9)
        self.assertTrue(all(set(row['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
                            for row in audit['declarations']))
        for module in ('OrdinaryFamily', 'OrdinarySignature', 'OrdinaryDomain', 'OrdinaryInputSemantics'):
            name = module + '.lean'
            self.assertEqual(self.raw('ordinary-family-first/' + name),
                             self.raw('ordinary-family-cases-syntax-repair/' + name))


class OrdinaryInputsFirstHistory(unittest.TestCase):
    # "tests/fixtures/authoring_sessions/ordinary-execution-v030/inputs-first.tar.xz"
    # "tests/fixtures/authoring_sessions/ordinary-execution-v030/inputs-first-index.json"
    # "tests/fixtures/authoring_sessions/ordinary-execution-v030/inputs-first-validation.json"
    @classmethod
    def setUpClass(cls):
        cls.root = history.ROOT / 'tests/fixtures/authoring_sessions/ordinary-execution-v030'
        with patch.object(history, 'FIXTURES', cls.root):
            cls.data = history.read_history(
                'inputs-first-index.json', 'inputs-first.tar.xz',
                '6be586116f429789e2e184fb39701b0eb69c15e9fc1eaae897110b840d7dbce4',
                142588, '2b0fb50363a50bb680eac51c79b0300f60011c5a8d4dec6b95dd634a6066faba',
                1887279)
        cls.index = json.loads((cls.root / 'inputs-first-index.json').read_bytes())

    def raw(self, name):
        return self.data[self.index['original_records'][name]['record']]

    def record(self, name):
        return json.loads(self.raw(name))

    def test_nine_original_input_programs_and_eighteen_actual_first_observations(self):
        self.assertEqual((len(self.index['original_records']), len(self.data)), (179, 111))
        for row in self.index['original_records'].values():
            raw = self.data[row['record']]
            self.assertEqual((len(raw), hashlib.sha256(raw).hexdigest(), row['original_mode']),
                             (row['bytes'], row['sha256'], 0o644))
        report = self.record('ordinary-input-v2-first/report.json')
        self.assertEqual(report['before'], report['after'])
        self.assertEqual(len(report['observations']), 18)
        for row in report['observations']:
            self.assertEqual(row['exit_code'], 0 if row['case'] == 'classical-inline-control' else 1)
            prefix = 'ordinary-input-v2-first/' + row['case']
            self.assertEqual(json.loads(self.raw(prefix + '-' + row['action'] + '.stdout')),
                             row['document'])
            source = self.raw(prefix + '/main.qli')
            path = next(path for path in report['before'] if path.endswith('/' + row['case'] + '/main.qli'))
            self.assertEqual(hashlib.sha256(source).hexdigest(), report['before'][path])

    def test_failed_proof_execution_and_policy_attempts_stay_separate_from_repairs(self):
        self.assertEqual(self.record('ordinary-v2-integration/native-first/report.json')['exit_code'], 101)
        self.assertIn(b'no method named', self.raw('ordinary-v2-integration/native-first/stdout'))
        self.assertIn(b'Lean exited with code 137', self.raw(
            'ordinary-v2-schema-repair-02-commands/01/stdout'))
        self.assertIn(b'summaries._unsafe_rec: partial project declaration', self.raw(
            'ordinary-v2-schema-repair-03-commands/02/stdout'))
        for name in ['native-repair-01', 'source-first', 'native-controls20']:
            report = self.record('ordinary-v2-integration/' + name + '/report.json')
            self.assertEqual(report['exit_code'], 0)
            self.assertTrue(report['stable_source'])
        self.assertIn(b'passed 20 complete input/all-history controls', self.raw(
            'ordinary-v2-integration/native-controls20/stdout'))
        report = self.record('ordinary-v2-schema-repair-04-report.json')
        self.assertEqual(report['status'], 'passed')
        self.assertEqual(len(report['commands']), 7)
        self.assertTrue(all(row['exit_code'] == 0 for row in report['commands']))


class OrdinaryTableIntermediatesHistory(unittest.TestCase):
    # "tests/fixtures/authoring_sessions/ordinary-execution-v030/tables-first.tar.xz"
    # "tests/fixtures/authoring_sessions/ordinary-execution-v030/tables-first-index.json"
    # "tests/fixtures/authoring_sessions/ordinary-execution-v030/tables-first-validation.json"
    @classmethod
    def setUpClass(cls):
        cls.root = history.ROOT / 'tests/fixtures/authoring_sessions/ordinary-execution-v030'
        with patch.object(history, 'FIXTURES', cls.root):
            cls.data = history.read_history(
                'tables-first-index.json', 'tables-first.tar.xz',
                'b1ae42f0a7007148c5800e619b52dcda6fe73c47442fc68e6898338788ded55d',
                22144, '241fafd33dc890fe63fe6ede94261df1843b3c97f595bb6a4cf8e36b8be03877',
                232157)
        cls.index = json.loads((cls.root / 'tables-first-index.json').read_bytes())

    def raw(self, name):
        return self.data[self.index['original_records'][name]['record']]

    def record(self, name):
        return json.loads(self.raw(name))

    def test_first_sources_and_all_before_after_streams_remain_distinct(self):
        self.assertEqual((len(self.index['original_records']), len(self.data)), (115, 58))
        for row in self.index['original_records'].values():
            raw = self.data[row['record']]
            self.assertEqual((len(raw), hashlib.sha256(raw).hexdigest(), row['original_mode']),
                             (row['bytes'], row['sha256'], 0o644))
        first = self.record('ordinary-table-intermediates-first/report.json')
        after = self.record('ordinary-table-intermediates-after/report.json')
        for folder, report, successes in [('first', first, 2), ('after', after, 10)]:
            self.assertEqual(report['before'], report['after'])
            self.assertEqual(report['source_repairs'], 0)
            self.assertEqual(len(report['observations']), 16)
            self.assertEqual(sum(row['exit_code'] == 0 for row in report['observations']), successes)
            for row in report['observations']:
                prefix = 'ordinary-table-intermediates-' + folder + '/'
                stdout = self.raw(prefix + row['stdout']['path'])
                self.assertEqual(json.loads(stdout), row['document'])
                for stream in ['stdout', 'stderr']:
                    self.assertEqual(hashlib.sha256(self.raw(prefix + row[stream]['path'])).hexdigest(),
                                     row[stream]['sha256'])
                source = 'ordinary-table-intermediates-first/' + row['case'] + '/main.qli'
                source_path = next(path for path in report['before']
                                   if path.endswith('/' + row['case'] + '/main.qli'))
                self.assertEqual(hashlib.sha256(self.raw(source)).hexdigest(), report['before'][source_path])
        outcomes = {row['case']: row['document']['result']['distribution']
                    for row in after['observations'] if row['action'] == 'run' and row['exit_code'] == 0}
        expected = {'direct-enum': {(True,): 1}, 'transitive-enum': {(False,): 1},
                    'zero-width-record': {(True,): 1}, 'builtin-control': {(True,): 1},
                    'measured-argument': {(False,): .5, (True,): .5}}
        self.assertEqual(set(outcomes), set(expected))
        for case, rows in outcomes.items():
            actual = {tuple(row['bits']): row['probability'] for row in rows}
            self.assertEqual(set(actual), set(expected[case]))
            for bits, value in expected[case].items():
                self.assertAlmostEqual(actual[bits], value, delta=1e-12)

    def test_old_refusal_expectation_failure_is_preserved_beside_the_repair(self):
        failed = self.record('ordinary-v2-integration/table-normal-source/report.json')
        self.assertEqual(failed['exit_code'], 101)
        self.assertTrue(failed['stable_source'])
        self.assertIn(b'cannot resolve Lean checker', self.raw(
            'ordinary-v2-integration/table-normal-source/stdout'))
        self.assertIn(b'ordinary_match_checks_all_arms_before_selected_refusal_and_project_native_check ... FAILED', self.raw(
            'ordinary-v2-integration/table-normal-source/stdout'))
        for name in ['table-normal-producer', 'table-normal-collection-repair',
                     'table-msrv-producer', 'table-msrv-source']:
            report = self.record('ordinary-v2-integration/' + name + '/report.json')
            self.assertEqual(report['exit_code'], 0)
            self.assertTrue(report['stable_source'])


class OrdinaryImportFirstHistory(unittest.TestCase):
    # "tests/fixtures/authoring_sessions/ordinary-execution-v030/imports-first.tar.xz"
    # "tests/fixtures/authoring_sessions/ordinary-execution-v030/imports-first-index.json.gz"
    # "tests/fixtures/authoring_sessions/ordinary-execution-v030/imports-first-validation.json"
    @classmethod
    def setUpClass(cls):
        cls.root = history.ROOT / 'tests/fixtures/authoring_sessions/ordinary-execution-v030'
        with patch.object(history, 'FIXTURES', cls.root):
            cls.data = history.read_history(
                'imports-first-index.json.gz', 'imports-first.tar.xz',
                '3eb208070d815ed9d40ed003b3bbcf79aa5195f5c5050f07723d0bdf6a1a9ac0',
                106484, '0884b386c4db8ed9d397bee71ae66659324c456603fbb67fb3b71fed3749c92a',
                3635688, index_gzip=dict(bytes=15364, decoded_bytes=119155,
                    decoded_sha256='1e61f1c05eec15b51cad79cbd30b9dece50264cb2938b252f3d5ee7d8297f4df'))
            decoded = history.read_history_index('imports-first-index.json.gz',
                '3eb208070d815ed9d40ed003b3bbcf79aa5195f5c5050f07723d0bdf6a1a9ac0',
                index_gzip=dict(bytes=15364, decoded_bytes=119155,
                    decoded_sha256='1e61f1c05eec15b51cad79cbd30b9dece50264cb2938b252f3d5ee7d8297f4df'))
        cls.index = json.loads(decoded)

    def raw(self, name):
        return self.data[self.index['original_records'][name]['record']]

    def record(self, name):
        return json.loads(self.raw(name))

    def test_originals_repairs_and_all_real_streams_remain_distinct(self):
        self.assertEqual((len(self.index['original_records']), len(self.data)), (286, 142))
        for row in self.index['original_records'].values():
            raw = self.data[row['record']]
            self.assertEqual((len(raw), hashlib.sha256(raw).hexdigest()), (row['bytes'], row['sha256']))
        for folder, count, successes in [('ordinary-import-closure-first', 18, 2),
                ('ordinary-import-closure-record-repair', 2, 0),
                ('ordinary-import-closure-after', 20, 10)]:
            report = self.record(folder + '/report.json')
            self.assertEqual(report['before'], report['after'])
            self.assertEqual(len(report['observations']), count)
            self.assertEqual(sum(row['exit_code'] == 0 for row in report['observations']), successes)
            for row in report['observations']:
                for stream in ['stdout', 'stderr']:
                    raw = self.raw(folder + '/' + row[stream]['path'])
                    self.assertEqual(hashlib.sha256(raw).hexdigest(), row[stream]['sha256'])
                self.assertEqual(json.loads(self.raw(folder + '/' + row['stdout']['path'])), row['document'])
        self.assertIn(b'{ tag: Tri, flag: Bit }', self.raw(
            'ordinary-import-closure-first/record-field-reexport/packet.qli'))
        self.assertIn(b'{ pub tag: Tri, pub flag: Bit }', self.raw(
            'ordinary-import-closure-record-repair/project/packet.qli'))
        after = self.record('ordinary-import-closure-after/report.json')
        expected = self.record('ordinary-import-closure-after/plan.json')['expected']
        for row in after['observations']:
            self.assertTrue(row['matches_expectation'])
            if row['action'] == 'run' and row['exit_code'] == 0:
                self.assertEqual(row['document']['result']['distribution'],
                    [dict(bits=expected[row['case']], probability=1)])

    def test_failed_and_interrupted_checks_are_not_reclassified_as_success(self):
        for name in ['signature-family-first', 'import-controls-first']:
            self.assertEqual(self.record('ordinary-import-lean-checks/' + name + '/report.json')['exit_code'], 1)
        self.assertEqual(self.record('ordinary-import-checks/schema-first/report.json')['exit_code'], 1)
        self.assertIn('exit 130', self.record('STOP-ordinary-imports-20261028.json')['local_checks'])
        self.assertNotIn('ordinary-import-checks/schema-work-accounting-repair/report.json',
                         self.index['original_records'])
        for name in ['normal-native', 'normal-collection', 'normal-source',
                     'msrv-native', 'msrv-collection', 'msrv-source']:
            report = self.record('ordinary-import-checks/' + name + '/report.json')
            self.assertEqual(report['exit_code'], 0)
            self.assertTrue(report['stable_source'])


if __name__ == '__main__':
    unittest.main()
