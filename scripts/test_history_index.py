"""Container compatibility/refusals only; never execute archived source.
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


if __name__ == '__main__':
    unittest.main()
