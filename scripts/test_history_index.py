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


if __name__ == '__main__':
    unittest.main()
