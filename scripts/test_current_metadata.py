"""Lossless current-view containers; no historical source or command execution.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import gzip
import json
import lzma
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import zlib

import current_metadata as metadata


class CurrentMetadataContainers(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.raw = '{\n  "z": [false, 0, null],\n  "a": "雪\\n\\\"quoted\\\""\n}\n'.encode()

    def store(self, relative, stored):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(stored)
        return path

    def test_both_explicit_current_paths_keep_exact_bytes_types_order_and_deterministic_crc64(self):
        self.assertEqual(metadata.MAX_BYTES, 16 * 1024 * 1024)
        self.assertEqual(metadata.DECODER_MEMORY_LIMIT, 64 * 1024 * 1024)
        self.assertEqual(metadata.DICTIONARY_BYTES, 4 * 1024 * 1024)
        self.assertEqual(metadata.CURRENT_PATHS, {
            'tests/fixtures/verification_v022/inventory.json.xz',
            'tests/fixtures/verification_v029/coverage.json.xz'})
        for relative in (metadata.INVENTORY, metadata.COVERAGE):
            with self.subTest(relative=relative):
                first = metadata.encode_bytes(relative, self.raw)
                self.assertEqual(first, metadata.encode_bytes(relative, self.raw))
                self.assertEqual(first[:6], b'\xfd7zXZ\x00')
                decoder = lzma.LZMADecompressor(format=lzma.FORMAT_XZ,
                                               memlimit=64 * 1024 * 1024)
                self.assertEqual(decoder.decompress(first), self.raw)
                self.assertTrue(decoder.eof)
                self.assertEqual(decoder.check, lzma.CHECK_CRC64)
                self.store(relative, first)
                self.assertEqual(metadata.read_bytes(self.root, relative), self.raw)
                self.assertEqual(metadata.read_json(self.root, relative), json.loads(self.raw))
                self.assertEqual(list(metadata.read_json(self.root, relative)), ['z', 'a'])
                self.assertIs(metadata.read_json(self.root, relative)['z'][0], False)

    def test_unknown_historical_plain_and_gzip_paths_are_not_auto_detected(self):
        stored = metadata.encode_bytes(metadata.INVENTORY, self.raw)
        for name in ('tests/fixtures/verification_v022/inventory.json',
                     'tests/fixtures/verification_v022/inventory.json.gz',
                     'tests/fixtures/verification_v029/coverage.json.gz',
                     'tests/fixtures/history/inventory.json.xz', metadata.INVENTORY + '.gz'):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'unsupported'):
                metadata.decode_bytes(name, stored)
        for value in (self.raw, gzip.compress(self.raw, mtime=0)):
            with self.subTest(value=value[:10]), self.assertRaisesRegex(ValueError, 'header'):
                metadata.decode_bytes(metadata.INVENTORY, value)

    def test_corruption_truncation_wrong_codec_extra_stream_padding_and_wrong_check_refuse(self):
        stored = metadata.encode_bytes(metadata.INVENTORY, self.raw)
        corrupt = bytearray(stored)
        corrupt[-8] ^= 1
        cases = [stored[:-1], bytes(corrupt), zlib.compress(self.raw),
                 lzma.compress(self.raw, format=lzma.FORMAT_ALONE,
                               filters=[{'id': lzma.FILTER_LZMA1, 'dict_size': 4 * 1024 * 1024}]),
                 stored + stored, stored + b'\0' * 4, stored + b'trailing']
        for raw in cases:
            with self.subTest(raw=raw[:12]), self.assertRaises(ValueError):
                metadata.decode_bytes(metadata.INVENTORY, raw)
        for check in (lzma.CHECK_NONE, lzma.CHECK_CRC32):
            stored = lzma.compress(self.raw, format=lzma.FORMAT_XZ, check=check,
                                   filters=[{'id': lzma.FILTER_LZMA2, 'dict_size': 4 * 1024 * 1024}])
            with self.subTest(check=check), self.assertRaisesRegex(ValueError, 'CRC64'):
                metadata.decode_bytes(metadata.INVENTORY, stored)

    def test_stored_output_and_real_decoder_memory_limits_refuse_without_large_inputs(self):
        small = metadata.encode_bytes(metadata.INVENTORY, b'{"s":"' + b'x' * 1000 + b'"}\n')
        with patch.object(metadata, 'MAX_BYTES', len(small)), \
             self.assertRaisesRegex(ValueError, 'oversized'):
            metadata.decode_bytes(metadata.INVENTORY, small)
        with patch.object(metadata, 'MAX_BYTES', 32), \
             patch.object(metadata.lzma, 'LZMADecompressor') as decoder, \
             self.assertRaisesRegex(ValueError, 'stored size'):
            metadata.decode_bytes(metadata.INVENTORY, metadata.HEADER + b'x' * 27)
        decoder.assert_not_called()
        with patch.object(metadata, 'MAX_BYTES', 8), \
             patch.object(metadata.lzma, 'compress') as compressor, \
             self.assertRaisesRegex(ValueError, 'decoded size'):
            metadata.encode_bytes(metadata.INVENTORY, self.raw)
        compressor.assert_not_called()
        # A normal 4 MiB-dictionary tiny stream exceeds a deliberately lowered
        # test decoder budget. No large dictionary or maximum-size case is made.
        with patch.object(metadata, 'DECODER_MEMORY_LIMIT', 1024 * 1024), \
             self.assertRaisesRegex(ValueError, 'over-memory') as error:
            metadata.decode_bytes(metadata.INVENTORY, small)
        self.assertIsInstance(error.exception.__cause__, lzma.LZMAError)
        self.assertEqual(metadata.decode_bytes(metadata.INVENTORY, small), b'{"s":"' + b'x' * 1000 + b'"}\n')

    def test_file_read_is_bounded_and_plain_gzip_duplicates_and_symlinks_refuse(self):
        stored = metadata.encode_bytes(metadata.INVENTORY, self.raw)
        path = self.store(metadata.INVENTORY, stored)
        with patch.object(metadata, 'decode_bytes', wraps=metadata.decode_bytes) as decoded:
            self.assertEqual(metadata.read_bytes(self.root, metadata.INVENTORY), self.raw)
        self.assertEqual(decoded.call_args.args, (metadata.INVENTORY, stored))
        path.write_bytes(metadata.HEADER + b'x' * 100)
        with patch.object(metadata, 'MAX_BYTES', 32), \
             patch.object(metadata, 'decode_bytes', side_effect=ValueError('sentinel')) as decoded, \
             self.assertRaisesRegex(ValueError, 'sentinel'):
            metadata.read_bytes(self.root, metadata.INVENTORY)
        self.assertEqual(len(decoded.call_args.args[1]), 33)
        path.write_bytes(stored)
        for name in metadata.obsolete_paths(metadata.INVENTORY):
            other = self.root / name
            for linked in (False, True):
                with self.subTest(name=name, linked=linked):
                    if linked:
                        other.symlink_to(self.root / 'missing-old-view')
                    else:
                        other.write_bytes(b'old current metadata')
                    with self.assertRaisesRegex(ValueError, 'duplicate'):
                        metadata.read_bytes(self.root, metadata.INVENTORY)
                    with self.assertRaisesRegex(ValueError, 'duplicate'):
                        metadata.write_bytes(self.root, metadata.INVENTORY, self.raw)
                    self.assertEqual(path.read_bytes(), stored)
                    other.unlink()
        path.unlink()
        target = self.root / 'other.xz'
        target.write_bytes(stored)
        path.symlink_to(target)
        with self.assertRaisesRegex(ValueError, 'linked'):
            metadata.read_bytes(self.root, metadata.INVENTORY)
        with self.assertRaisesRegex(ValueError, 'linked'):
            metadata.write_bytes(self.root, metadata.INVENTORY, self.raw)

    def test_invalid_json_and_duplicate_keys_refuse_before_write_and_after_decode(self):
        path = self.store(metadata.COVERAGE, b'original bytes')
        invalid = (b'\xff', b'{', b'[]', b'false',
                   b'{"same": 1, "same": 2}',
                   b'{"nested": {"same": 1, "same": 2}}')
        for raw in invalid:
            with self.subTest(raw=raw), self.assertRaises((ValueError, UnicodeError)):
                metadata.write_bytes(self.root, metadata.COVERAGE, raw)
            self.assertEqual(path.read_bytes(), b'original bytes')
        for raw in invalid:
            # Independent packing reaches the reader's JSON checks directly.
            stored = lzma.compress(raw, format=lzma.FORMAT_XZ, check=lzma.CHECK_CRC64,
                                   filters=[{'id': lzma.FILTER_LZMA2, 'dict_size': 4 * 1024 * 1024}])
            path.write_bytes(stored)
            with self.subTest(raw=raw), self.assertRaises((ValueError, UnicodeError)):
                metadata.read_json(self.root, metadata.COVERAGE)


if __name__ == '__main__':
    unittest.main()
