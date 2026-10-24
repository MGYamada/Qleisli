"""Explicit lossless containers for the two mutable current metadata views.

This codec grants no review, acceptance or historical-evidence authority. Schema,
source hashes, surface identity and all protected comparisons stay in consumers.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import json
import lzma
import os
from pathlib import Path
import stat

INVENTORY = 'tests/fixtures/verification_v022/inventory.json.xz'
COVERAGE = 'tests/fixtures/verification_v029/coverage.json.xz'
CURRENT_PATHS = frozenset((INVENTORY, COVERAGE))
OBSOLETE_GZIP_PATHS = frozenset(path[:-3] + '.gz' for path in CURRENT_PATHS)
MAX_BYTES = 16 * 1024 * 1024
DECODER_MEMORY_LIMIT = 64 * 1024 * 1024
DICTIONARY_BYTES = 4 * 1024 * 1024
HEADER = b'\xfd7zXZ\x00'


def current_path(root, relative):
    if relative not in CURRENT_PATHS:
        raise ValueError('unsupported current metadata path')
    return Path(root) / relative


def obsolete_paths(relative):
    current_path('.', relative)
    plain = relative[:-3]
    return plain, plain + '.gz'


def decode_bytes(relative, stored):
    """Exactly one CRC64 XZ stream; bounded bytes and decoder memory, no fallback."""
    current_path('.', relative)
    if type(stored) is not bytes or len(stored) > MAX_BYTES or not stored.startswith(HEADER):
        raise ValueError('invalid current metadata XZ header or stored size')
    try:
        decoder = lzma.LZMADecompressor(format=lzma.FORMAT_XZ, memlimit=DECODER_MEMORY_LIMIT)
        decoded = decoder.decompress(stored, max_length=MAX_BYTES + 1)
    except lzma.LZMAError as error:
        raise ValueError('invalid or over-memory current metadata XZ stream') from error
    if len(decoded) > MAX_BYTES or not decoder.eof or decoder.unused_data:
        raise ValueError('incomplete, trailing or oversized current metadata XZ')
    if decoder.check != lzma.CHECK_CRC64:
        raise ValueError('current metadata XZ requires CRC64')
    return decoded


def reject_duplicate_or_link(root, relative):
    path = current_path(root, relative)
    obsolete = [Path(root) / name for name in obsolete_paths(relative)]
    if path.is_symlink() or any(other.exists() or other.is_symlink() for other in obsolete):
        raise ValueError('linked current metadata or obsolete plain/gzip duplicate')
    return path


def read_bytes(root, relative):
    path = reject_duplicate_or_link(root, relative)
    if not path.is_file():
        raise ValueError('current metadata must be a regular file')
    with path.open('rb') as stream:
        if not stat.S_ISREG(os.fstat(stream.fileno()).st_mode):
            raise ValueError('current metadata must be a regular file')
        stored = stream.read(MAX_BYTES + 1)
    return decode_bytes(relative, stored)


def unique_object(pairs):
    value = {}
    for key, item in pairs:
        if key in value:
            raise ValueError('duplicate current metadata JSON key')
        value[key] = item
    return value


def json_object(decoded):
    value = json.loads(decoded.decode('utf-8'), object_pairs_hook=unique_object)
    if not isinstance(value, dict):
        raise ValueError('current metadata must contain a JSON object')
    return value


def read_json(root, relative):
    return json_object(read_bytes(root, relative))


def encode_bytes(relative, decoded):
    """Preserve all decoded bytes, including formatting, Unicode and newline."""
    current_path('.', relative)
    if type(decoded) is not bytes or len(decoded) > MAX_BYTES:
        raise ValueError('current metadata decoded size exceeds capacity')
    json_object(decoded)
    stored = lzma.compress(decoded, format=lzma.FORMAT_XZ, check=lzma.CHECK_CRC64,
                           filters=[{'id': lzma.FILTER_LZMA2, 'preset': 6,
                                     'dict_size': DICTIONARY_BYTES}])
    if len(stored) > MAX_BYTES or not stored.startswith(HEADER):
        raise ValueError('current metadata stored size or header differs')
    return stored


def write_bytes(root, relative, decoded):
    path = reject_duplicate_or_link(root, relative)
    stored = encode_bytes(relative, decoded)
    path.write_bytes(stored)
