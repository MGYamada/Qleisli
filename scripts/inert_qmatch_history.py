"""Passive reader for the reviewed, content-addressed qmatch history.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

Saved producer code is data only. The returned object represents one captured
input snapshot, not a cache of mutable paths or a previous validation result.
"""
import hashlib
import io
import json
import lzma
from pathlib import Path, PurePosixPath
import re
import tarfile


PREFIX = 'tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/'
MANIFEST = PREFIX + 'shared-history.json'
SOURCE_COMMIT = '8fcaaad3bac04adbc46a91c8a45d91a1d5353274'
INDEX_MAX = 4 * 1024 * 1024
STORED_MAX = 1024 * 1024
TAR_MAX = 32 * 1024 * 1024
MEM_MAX = 64 * 1024 * 1024
PROFILES = (6, 4 | lzma.PRESET_EXTREME)
PHYSICAL = ('objects-00.tar.xz', 'objects-01.tar.xz', 'objects-02.tar.xz')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def exact_keys(row, names):
    require(type(row) is dict and set(row) == set(names.split()), 'history keys differ')


def natural(value, cap):
    require(type(value) is int and 0 <= value <= cap, 'history size/profile differs')
    return value


def sha(value):
    require(type(value) is str and re.fullmatch('[0-9a-f]{64}', value), 'history digest differs')
    return value


def canonical_path(value):
    require(type(value) is str, 'history path is not text')
    path = PurePosixPath(value)
    require(value and not path.is_absolute() and str(path) == value
            and '..' not in path.parts and '\\' not in value and '\0' not in value,
            'history path is not canonical')
    return value


def json_object(data):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, 'duplicate history JSON key')
            result[key] = value
        return result
    require(len(data) <= INDEX_MAX, 'oversized history metadata')
    result = json.loads(data, object_pairs_hook=unique)
    require(type(result) is dict, 'history metadata is not an object')
    return result


def decode(data, maximum):
    decoder = lzma.LZMADecompressor(format=lzma.FORMAT_XZ, memlimit=MEM_MAX)
    raw = decoder.decompress(data, max_length=maximum + 1)
    require(len(raw) <= maximum and decoder.eof and not decoder.unused_data
            and decoder.check == lzma.CHECK_CRC64,
            'incomplete, trailing, non-CRC64 or oversized shared history')
    return raw


def identity(data, size, expected, cap):
    require(len(data) == natural(size, cap) and digest(data) == sha(expected),
            'shared history identity differs')


def read_bounded(path, cap):
    require(path.is_file() and not path.is_symlink(), 'nonregular shared history file')
    with path.open('rb') as stream:
        data = stream.read(cap + 1)
    require(len(data) <= cap, 'oversized stored shared history')
    return data


def regular_range(raw, member, cursor):
    """Bound stored regular bytes before slicing; sparse members never qualify."""
    require(member.type in (tarfile.REGTYPE, tarfile.AREGTYPE)
            and member.sparse is None
            and not any(key.startswith('GNU.sparse') for key in member.pax_headers),
            'sparse or nonregular original member')
    start = natural(member.offset_data, len(raw))
    size = natural(member.size, len(raw))
    offset = natural(member.offset, len(raw))
    end = start + size
    require(cursor <= offset and offset + 512 <= start and start % 512 == 0
            and end <= len(raw), 'overlapping or out-of-buffer original member')
    padded_end = ((end + 511) // 512) * 512
    require(padded_end <= len(raw), 'out-of-buffer original member padding')
    return start, end, padded_end


def physical_objects(raw, expected):
    """Read only the exact regular USTAR representation written by the producer."""
    require(len(raw) <= TAR_MAX, 'oversized physical object TAR')
    total = 0
    for key, size in expected.items():
        sha(key)
        total += natural(size, TAR_MAX)
        require(total <= TAR_MAX, 'aggregate shared object bytes exceed shard bound')
    require(total + 512 * len(expected) + 1024 <= len(raw),
            'shared object inventory exceeds stored TAR range')
    result, cursor = {}, 0
    with tarfile.open(fileobj=io.BytesIO(raw), mode='r:') as archive:
        for member in archive:
            require(member.type == tarfile.REGTYPE and member.sparse is None
                    and member.name.startswith('objects/') and not member.pax_headers,
                    'noncanonical or sparse physical member')
            key = member.name[8:]
            require(key in expected and key not in result, 'unlisted or duplicate shared object')
            require(member.size == expected[key], 'shared object length differs')
            start, end, padded_end = regular_range(raw, member, cursor)
            require(member.offset == cursor and start == cursor + 512,
                    'noncontiguous physical member range')
            header = tarfile.TarInfo('objects/' + key)
            header.size, header.mode, header.uid, header.gid, header.mtime = expected[key], 0o644, 0, 0, 0
            header.uname = header.gname = ''
            require(raw[cursor:start] == header.tobuf(format=tarfile.USTAR_FORMAT)
                    and not any(raw[end:padded_end]), 'noncanonical physical USTAR header/padding')
            data = raw[start:end]
            identity(data, expected[key], key, TAR_MAX)
            result[key] = data
            cursor = padded_end
    require(set(result) == set(expected), 'shared object missing')
    expected_end = ((cursor + 1024 + tarfile.RECORDSIZE - 1) // tarfile.RECORDSIZE) * tarfile.RECORDSIZE
    require(len(raw) == expected_end and not any(raw[cursor:]),
            'noncanonical physical TAR trailer')
    return result


class Snapshot:
    """One complete, validated immutable physical input snapshot.

    Construct explicitly once for a history-consumer suite. The suite should
    call assert_inputs_unchanged afterwards; no module-global lazy path cache
    or remembered successful test result is used.
    """

    def __init__(self, root):
        self.root = Path(root)
        self._physical = {}
        self._objects = {}
        manifest_raw = self._capture('shared-history.json', INDEX_MAX)
        manifest = json_object(manifest_raw)
        exact_keys(manifest, 'format version catalog containers')
        require(manifest['format'] == 'qleisli.inert-qmatch-shared-root'
                and type(manifest['version']) is int and manifest['version'] == 1,
                'unknown shared history manifest')
        catalog_row = manifest['catalog']
        exact_keys(catalog_row, 'path bytes sha256 decoded_bytes decoded_sha256')
        require(catalog_row['path'] == 'catalog.json.xz', 'shared catalog path differs')
        packed = self._capture('catalog.json.xz', INDEX_MAX)
        identity(packed, catalog_row['bytes'], catalog_row['sha256'], INDEX_MAX)
        catalog_raw = decode(packed, INDEX_MAX)
        identity(catalog_raw, catalog_row['decoded_bytes'], catalog_row['decoded_sha256'], INDEX_MAX)
        catalog = json_object(catalog_raw)
        exact_keys(catalog, 'format version source_commit files archives objects')
        require(catalog['format'] == 'qleisli.inert-qmatch-shared-objects'
                and type(catalog['version']) is int and catalog['version'] == 1
                and catalog['source_commit'] == SOURCE_COMMIT, 'shared catalog provenance differs')
        require(all(type(catalog[key]) is dict for key in ('files', 'archives', 'objects')),
                'shared catalog tables differ')
        self._files, self._archives = catalog['files'], catalog['archives']
        objects = catalog['objects']
        expected_by_container = {name: {} for name in PHYSICAL}
        expected_bytes = {name: 0 for name in PHYSICAL}
        for key, row in objects.items():
            sha(key)
            exact_keys(row, 'container bytes')
            require(row['container'] in expected_by_container, 'unknown object container')
            size = natural(row['bytes'], TAR_MAX)
            expected_by_container[row['container']][key] = size
            expected_bytes[row['container']] += size
            require(expected_bytes[row['container']] <= TAR_MAX,
                    'aggregate shared object bytes exceed shard bound')
        rows = manifest['containers']
        require(type(rows) is list and len(rows) == len(PHYSICAL), 'shared container count differs')
        for name, row in zip(PHYSICAL, rows):
            exact_keys(row, 'path bytes sha256 decoded_bytes decoded_sha256')
            require(row['path'] == name, 'shared container order/path differs')
            packed = self._capture(name, STORED_MAX)
            identity(packed, row['bytes'], row['sha256'], STORED_MAX)
            raw = decode(packed, TAR_MAX)
            identity(raw, row['decoded_bytes'], row['decoded_sha256'], TAR_MAX)
            recovered = physical_objects(raw, expected_by_container[name])
            require(not set(recovered).intersection(self._objects), 'duplicate physical object')
            self._objects.update(recovered)
        require(set(self._objects) == set(objects), 'shared object inventory differs')
        self._validate_catalog()

    def _capture(self, name, cap):
        require('/' not in name and name not in self._physical, 'repeated physical file')
        data = read_bounded(self.root / PREFIX / name, cap)
        self._physical[name] = (data, cap)
        return data

    def _object(self, key, size):
        require(sha(key) in self._objects, 'missing referenced history object')
        data = self._objects[key]
        identity(data, size, key, TAR_MAX)
        return data

    def _tar(self, recipe):
        size = natural(recipe['raw_bytes'], TAR_MAX)
        segments = recipe['segments']
        require(type(segments) is list, 'history segments are not a list')
        pieces, total = [], 0
        for pair in segments:
            require(type(pair) is list and len(pair) == 2, 'malformed history segment')
            total += natural(pair[1], TAR_MAX)
            require(total <= size, 'history segment total exceeds original bound')
            pieces.append(self._object(*pair))
        raw = b''.join(pieces)
        identity(raw, size, recipe['raw_sha256'], TAR_MAX)
        return raw

    def _validate_catalog(self):
        referenced, archive_names = set(), set()
        for logical, row in self._files.items():
            canonical_path(logical)
            require(logical.startswith(PREFIX), 'logical history outside reviewed namespace')
            require(type(row) is dict, 'invalid logical history row')
            natural(row.get('original_mode'), 0o7777)
            if row.get('kind') == 'object':
                exact_keys(row, 'kind object bytes sha256 original_mode')
                data = self._object(row['object'], row['bytes'])
                identity(data, row['bytes'], row['sha256'], TAR_MAX)
                referenced.add(row['object'])
            else:
                exact_keys(row, 'kind recipe bytes sha256 original_mode')
                require(row['kind'] == 'original-xz-tar' and row['recipe'] == logical
                        and logical in self._archives, 'invalid original archive recipe')
                recipe = self._archives[logical]
                exact_keys(recipe, 'segments members profile raw_bytes raw_sha256 stored_bytes stored_sha256')
                require(type(recipe['profile']) is int and recipe['profile'] in PROFILES,
                        'unreviewed original encoder profile')
                require(recipe['stored_bytes'] == row['bytes']
                        and recipe['stored_sha256'] == row['sha256'], 'original archive pins differ')
                natural(row['bytes'], STORED_MAX)
                sha(row['sha256'])
                raw = self._tar(recipe)
                referenced.update(pair[0] for pair in recipe['segments'])
                require(type(recipe['members']) is dict, 'original members not an object')
                member_total = 0
                for name, entry in recipe['members'].items():
                    canonical_path(name)
                    exact_keys(entry, 'object bytes sha256 original_mode')
                    member_total += natural(entry['bytes'], TAR_MAX)
                    require(member_total <= len(raw), 'aggregate original member bytes exceed TAR bound')
                seen, cursor = set(), 0
                with tarfile.open(fileobj=io.BytesIO(raw), mode='r:') as archive:
                    for member in archive:
                        canonical_path(member.name)
                        start, end, padded_end = regular_range(raw, member, cursor)
                        require(member.name not in seen
                                and member.name in recipe['members'], 'original member inventory differs')
                        entry = recipe['members'][member.name]
                        exact_keys(entry, 'object bytes sha256 original_mode')
                        require(member.mode == natural(entry['original_mode'], 0o7777)
                                and member.size == natural(entry['bytes'], TAR_MAX), 'original member mode/size differs')
                        expected = self._object(entry['object'], entry['bytes'])
                        data = raw[start:end]
                        require(data == expected, 'original member object differs')
                        identity(data, entry['bytes'], entry['sha256'], TAR_MAX)
                        referenced.add(entry['object'])
                        seen.add(member.name)
                        cursor = padded_end
                require(seen == set(recipe['members']), 'original member missing')
                archive_names.add(logical)
        require(archive_names == set(self._archives), 'unreferenced original archive recipe')
        require(referenced == set(self._objects), 'unreferenced shared history object')

    def read(self, logical):
        """Reconstruct exact original stored bytes, or reject; never fall back."""
        canonical_path(logical)
        require(logical in self._files, 'unregistered logical history path')
        row = self._files[logical]
        if row['kind'] == 'object':
            result = self._objects[row['object']]
            cap = TAR_MAX
        else:
            recipe = self._archives[logical]
            result = lzma.compress(self._tar(recipe), format=lzma.FORMAT_XZ,
                                   check=lzma.CHECK_CRC64, preset=recipe['profile'])
            cap = STORED_MAX
        identity(result, row['bytes'], row['sha256'], cap)
        return result

    def audit_originals(self):
        """Require full original stored-byte reconstruction for every row."""
        for logical in self._files:
            self.read(logical)
        return len(self._files), len(self._archives)

    def member_mode(self, logical, member):
        """Return mode metadata checked against the original bounded TAR bytes."""
        require(logical in self._archives and member in self._archives[logical]['members'],
                'unregistered original history member')
        return self._archives[logical]['members'][member]['original_mode']

    def assert_inputs_unchanged(self):
        for name, (expected, cap) in self._physical.items():
            require(read_bounded(self.root / PREFIX / name, cap) == expected,
                    'shared history changed during the observation')
