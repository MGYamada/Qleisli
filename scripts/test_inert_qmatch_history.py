"""Small passive reader controls; no real history decode or extraction.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import io
import json
import lzma
from pathlib import Path
import tarfile
import tempfile
import unittest

import inert_qmatch_history as reader


def regular_tar(entries, *, mode=0o644, kind=tarfile.REGTYPE):
    stream = io.BytesIO()
    with tarfile.open(fileobj=stream, mode='w', format=tarfile.USTAR_FORMAT) as archive:
        for name, data in entries:
            info = tarfile.TarInfo(name)
            info.size, info.mode, info.type = len(data), mode, kind
            archive.addfile(info, io.BytesIO(data))
    return stream.getvalue()


def sparse_tar(logical_size=1 << 40):
    # The stored data is empty. The old GNU sparse header claims a huge logical
    # hole; inspect this metadata only, and never call extractfile on it.
    info = tarfile.TarInfo('objects/' + reader.digest(b''))
    info.type = tarfile.GNUTYPE_SPARSE
    info.mode = 0o644
    header = bytearray(info.tobuf(format=tarfile.GNU_FORMAT))
    header[483:495] = tarfile.itn(logical_size, 12, tarfile.GNU_FORMAT)
    header[148:156] = b'        '
    header[148:156] = ('%06o\0 ' % sum(header)).encode('ascii')
    return bytes(header) + bytes(tarfile.RECORDSIZE - 512)


class BoundedPhysicalReader(unittest.TestCase):
    def setUp(self):
        self.payload = b'preserved first source\n'
        self.key = reader.digest(self.payload)
        self.expected = {self.key: len(self.payload)}
        self.raw = regular_tar([('objects/' + self.key, self.payload)])

    def test_canonical_whole_member_bytes(self):
        self.assertEqual(reader.physical_objects(self.raw, self.expected), {self.key: self.payload})

    def test_gnu_sparse_isfile_gap_and_physical_rejection(self):
        raw = sparse_tar()
        with tarfile.open(fileobj=io.BytesIO(raw), mode='r:') as archive:
            member = next(iter(archive))
            self.assertTrue(member.isfile())
            self.assertEqual(member.size, 1 << 40)
            self.assertIsNotNone(member.sparse)
        with self.assertRaisesRegex(ValueError, 'sparse physical'):
            reader.physical_objects(raw, {reader.digest(b''): 0})

    def test_original_sparse_rejected_before_any_logical_read(self):
        raw = sparse_tar()
        with tarfile.open(fileobj=io.BytesIO(raw), mode='r:') as archive:
            member = next(iter(archive))
            with self.assertRaisesRegex(ValueError, 'sparse or nonregular'):
                reader.regular_range(raw, member, 0)

    def test_aggregate_expected_bytes_refuse_before_tar_parser(self):
        expected = {'0' * 64: reader.TAR_MAX, '1' * 64: 1}
        with self.assertRaisesRegex(ValueError, 'aggregate shared object'):
            reader.physical_objects(b'not a TAR', expected)

    def test_declared_inventory_cannot_exceed_in_buffer_storage(self):
        with self.assertRaisesRegex(ValueError, 'inventory exceeds'):
            reader.physical_objects(self.raw, {self.key: len(self.raw)})

    def test_duplicate_member_rejected(self):
        raw = regular_tar([('objects/' + self.key, self.payload)] * 2)
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            reader.physical_objects(raw, self.expected)

    def test_missing_member_rejected(self):
        with self.assertRaisesRegex(ValueError, 'missing'):
            reader.physical_objects(regular_tar([]), self.expected)

    def test_unlisted_object_rejected(self):
        with self.assertRaisesRegex(ValueError, 'unlisted'):
            reader.physical_objects(self.raw, {})

    def test_wrong_whole_member_digest_rejected(self):
        raw = regular_tar([('objects/' + self.key, b'x' * len(self.payload))])
        with self.assertRaisesRegex(ValueError, 'identity differs'):
            reader.physical_objects(raw, self.expected)

    def test_noncanonical_mode_rejected(self):
        raw = regular_tar([('objects/' + self.key, self.payload)], mode=0o600)
        with self.assertRaisesRegex(ValueError, 'USTAR header'):
            reader.physical_objects(raw, self.expected)

    def test_v7_regular_type_not_physical_producer_type(self):
        raw = regular_tar([('objects/' + self.key, self.payload)], kind=tarfile.AREGTYPE)
        with self.assertRaisesRegex(ValueError, 'noncanonical'):
            reader.physical_objects(raw, self.expected)

    def test_nonzero_member_padding_rejected(self):
        raw = bytearray(self.raw)
        raw[512 + len(self.payload)] = 1
        with self.assertRaisesRegex(ValueError, 'padding'):
            reader.physical_objects(bytes(raw), self.expected)

    def test_nonzero_trailing_data_rejected(self):
        raw = bytearray(self.raw)
        raw[-1] = 1
        with self.assertRaisesRegex(ValueError, 'trailer'):
            reader.physical_objects(bytes(raw), self.expected)

    def test_extra_complete_zero_record_rejected(self):
        with self.assertRaisesRegex(ValueError, 'trailer'):
            reader.physical_objects(self.raw + bytes(tarfile.RECORDSIZE), self.expected)

    def test_original_offset_and_overlap_refused(self):
        member = tarfile.TarInfo('plain.txt')
        member.size, member.offset, member.offset_data = 1, 0, 512
        self.assertEqual(reader.regular_range(self.raw, member, 0), (512, 513, 1024))
        with self.assertRaisesRegex(ValueError, 'overlapping'):
            reader.regular_range(self.raw, member, 512)
        member.offset_data = len(self.raw)
        with self.assertRaisesRegex(ValueError, 'out-of-buffer'):
            reader.regular_range(self.raw, member, 0)

    def test_original_regular_with_sparse_metadata_refused(self):
        member = tarfile.TarInfo('plain.txt')
        member.size, member.offset, member.offset_data = 1, 0, 512
        member.sparse = []
        with self.assertRaisesRegex(ValueError, 'sparse'):
            reader.regular_range(self.raw, member, 0)

    def test_stored_one_mib_bound(self):
        with tempfile.TemporaryDirectory(prefix='qleisli-reader-small-') as folder:
            path = Path(folder) / 'oversized.xz'
            path.write_bytes(bytes(reader.STORED_MAX + 1))
            with self.assertRaisesRegex(ValueError, 'oversized stored'):
                reader.read_bounded(path, reader.STORED_MAX)


class SnapshotStructure(unittest.TestCase):
    """Small independent store inputs exercise namespace and manifest edges."""

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix='qleisli-history-map-')
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.folder = self.root / reader.PREFIX
        self.folder.mkdir(parents=True)
        self.data = b'first diagnostic\n'
        self.key = reader.digest(self.data)
        self.logical = reader.PREFIX + 'kept.txt'
        self.catalog = {
            'format': 'qleisli.inert-qmatch-shared-objects', 'version': 1,
            'source_commit': reader.SOURCE_COMMIT, 'archives': {},
            'files': {self.logical: {'kind': 'object', 'object': self.key,
                      'bytes': len(self.data), 'sha256': self.key, 'original_mode': 0o644}},
            'objects': {self.key: {'container': reader.PHYSICAL[0], 'bytes': len(self.data)}},
        }
        containers = []
        for index, name in enumerate(reader.PHYSICAL):
            entries = [('objects/' + self.key, self.data)] if index == 0 else []
            raw = regular_tar(entries)
            packed = lzma.compress(raw, check=lzma.CHECK_CRC64, preset=0)
            (self.folder / name).write_bytes(packed)
            containers.append({'path': name, 'bytes': len(packed), 'sha256': reader.digest(packed),
                               'decoded_bytes': len(raw), 'decoded_sha256': reader.digest(raw)})
        self.manifest = {'format': 'qleisli.inert-qmatch-shared-root', 'version': 1,
                         'containers': containers}
        self.save_catalog()

    def save_catalog(self):
        raw = json.dumps(self.catalog).encode()
        packed = lzma.compress(raw, check=lzma.CHECK_CRC64, preset=0)
        (self.folder / 'catalog.json.xz').write_bytes(packed)
        self.manifest['catalog'] = {'path': 'catalog.json.xz', 'bytes': len(packed),
                                    'sha256': reader.digest(packed), 'decoded_bytes': len(raw),
                                    'decoded_sha256': reader.digest(raw)}
        (self.folder / 'shared-history.json').write_text(json.dumps(self.manifest))

    def test_minimal_complete_store_reads_exact_original(self):
        snapshot = reader.Snapshot(self.root)
        self.assertEqual(snapshot.read(self.logical), self.data)
        self.assertEqual(snapshot.audit_originals(), (1, 0))
        snapshot.assert_inputs_unchanged()

    def test_missing_physical_container_refused(self):
        (self.folder / reader.PHYSICAL[-1]).unlink()
        with self.assertRaisesRegex(ValueError, 'nonregular'):
            reader.Snapshot(self.root)

    def test_duplicate_manifest_key_refused(self):
        path = self.folder / 'shared-history.json'
        path.write_text('{"version":1,"version":1}')
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            reader.Snapshot(self.root)

    def test_malformed_catalog_table_refused(self):
        self.catalog['files'] = []
        self.save_catalog()
        with self.assertRaisesRegex(ValueError, 'tables differ'):
            reader.Snapshot(self.root)

    def test_wrong_container_map_edge_refused(self):
        self.catalog['objects'][self.key]['container'] = reader.PHYSICAL[1]
        self.save_catalog()
        with self.assertRaisesRegex(ValueError, 'unlisted'):
            reader.Snapshot(self.root)

    def test_missing_logical_object_map_edge_refused(self):
        self.catalog['files'][self.logical]['object'] = '0' * 64
        self.save_catalog()
        with self.assertRaisesRegex(ValueError, 'missing referenced'):
            reader.Snapshot(self.root)

    def test_aggregate_bound_precedes_physical_decompression(self):
        self.catalog['objects'][self.key]['bytes'] = reader.TAR_MAX
        self.catalog['objects']['0' * 64] = {'container': reader.PHYSICAL[0], 'bytes': 1}
        self.save_catalog()
        (self.folder / reader.PHYSICAL[0]).write_bytes(b'not an XZ stream')
        with self.assertRaisesRegex(ValueError, 'aggregate shared object'):
            reader.Snapshot(self.root)

    def test_namespace_escape_refused(self):
        self.catalog['files']['outside/source.txt'] = self.catalog['files'].pop(self.logical)
        self.save_catalog()
        with self.assertRaisesRegex(ValueError, 'outside reviewed namespace'):
            reader.Snapshot(self.root)

    def test_missing_logical_path_does_not_use_physical_sibling(self):
        snapshot = reader.Snapshot(self.root)
        missing = reader.PREFIX + 'unregistered.txt'
        (self.root / missing).write_bytes(b'fallback must not be read')
        with self.assertRaisesRegex(ValueError, 'unregistered logical'):
            snapshot.read(missing)

    def test_physical_change_after_capture_refused(self):
        snapshot = reader.Snapshot(self.root)
        path = self.folder / reader.PHYSICAL[0]
        path.write_bytes(path.read_bytes() + b'changed')
        with self.assertRaisesRegex(ValueError, 'changed during'):
            snapshot.assert_inputs_unchanged()


if __name__ == '__main__':
    unittest.main(verbosity=2)
