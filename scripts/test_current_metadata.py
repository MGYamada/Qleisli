"""Lossless current-view containers; no historical source or command execution.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import gzip
import json
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

    def test_both_explicit_current_paths_keep_exact_bytes_types_order_and_deterministic_header(self):
        self.assertEqual(metadata.MAX_BYTES, 16 * 1024 * 1024)
        for relative in (metadata.INVENTORY, metadata.COVERAGE):
            with self.subTest(relative=relative):
                first = metadata.encode_bytes(relative, self.raw)
                self.assertEqual(first, metadata.encode_bytes(relative, self.raw))
                self.assertEqual(first[:10], b'\x1f\x8b\x08\x00\x00\x00\x00\x00\x02\xff')
                self.store(relative, first)
                self.assertEqual(metadata.read_bytes(self.root, relative), self.raw)
                self.assertEqual(metadata.read_json(self.root, relative), json.loads(self.raw))
                self.assertEqual(list(metadata.read_json(self.root, relative)), ['z', 'a'])
                self.assertIs(metadata.read_json(self.root, relative)['z'][0], False)

    def test_unknown_historical_plain_and_other_codec_paths_are_not_auto_detected(self):
        stored = metadata.encode_bytes(metadata.INVENTORY, self.raw)
        for name in ('tests/fixtures/verification_v022/inventory.json',
                     'tests/fixtures/history/inventory.json.gz', metadata.INVENTORY + '.xz'):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'unsupported'):
                metadata.decode_bytes(name, stored)
        with self.assertRaisesRegex(ValueError, 'header'):
            metadata.decode_bytes(metadata.INVENTORY, self.raw)

    def test_corruption_truncation_wrong_codec_extra_member_padding_and_timestamp_refuse(self):
        stored = metadata.encode_bytes(metadata.INVENTORY, self.raw)
        corrupt = bytearray(stored)
        corrupt[-8] ^= 1
        dated = bytearray(stored)
        dated[4] = 1
        cases = [stored[:-1], bytes(corrupt), zlib.compress(self.raw),
                 stored + gzip.compress(b'', mtime=0), stored + b'\0', stored + b'trailing', bytes(dated)]
        for raw in cases:
            with self.subTest(raw=raw[:12]), self.assertRaises(ValueError):
                metadata.decode_bytes(metadata.INVENTORY, raw)

    def test_stored_limit_precedes_decoder_and_output_limit_refuses_expansion(self):
        small = metadata.encode_bytes(metadata.INVENTORY, b'{"s":"' + b'x' * 1000 + b'"}\n')
        with patch.object(metadata, 'MAX_BYTES', len(small)), \
             self.assertRaisesRegex(ValueError, 'oversized'):
            metadata.decode_bytes(metadata.INVENTORY, small)
        with patch.object(metadata, 'MAX_BYTES', 32), \
             patch.object(metadata.zlib, 'decompressobj') as decoder, \
             self.assertRaisesRegex(ValueError, 'stored size'):
            metadata.decode_bytes(metadata.INVENTORY, metadata.HEADER + b'x' * 23)
        decoder.assert_not_called()
        with patch.object(metadata, 'MAX_BYTES', 8), \
             patch.object(metadata.gzip, 'GzipFile') as compressor, \
             self.assertRaisesRegex(ValueError, 'decoded size'):
            metadata.encode_bytes(metadata.INVENTORY, self.raw)
        compressor.assert_not_called()

    def test_file_read_is_bounded_and_plain_duplicate_and_symlink_refuse(self):
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
        path.with_suffix('').write_bytes(self.raw)
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            metadata.read_bytes(self.root, metadata.INVENTORY)
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            metadata.write_bytes(self.root, metadata.INVENTORY, self.raw)
        path.with_suffix('').unlink()
        path.unlink()
        target = self.root / 'other.gz'
        target.write_bytes(stored)
        path.symlink_to(target)
        with self.assertRaisesRegex(ValueError, 'linked'):
            metadata.read_bytes(self.root, metadata.INVENTORY)

    def test_writer_rejects_invalid_utf8_json_and_nonobject_before_replacing_existing_bytes(self):
        path = self.store(metadata.COVERAGE, b'original bytes')
        for raw in (b'\xff', b'{', b'[]', b'false',
                    b'{"same": 1, "same": 2}',
                    b'{"nested": {"same": 1, "same": 2}}'):
            with self.subTest(raw=raw), self.assertRaises((ValueError, UnicodeError)):
                metadata.write_bytes(self.root, metadata.COVERAGE, raw)
            self.assertEqual(path.read_bytes(), b'original bytes')


if __name__ == '__main__':
    unittest.main()
