"""Explicit lossless containers for the two mutable current metadata views.

This codec grants no review, acceptance or historical-evidence authority. Schema,
source hashes, surface identity and all protected comparisons stay in consumers.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import gzip
import io
import json
import os
from pathlib import Path
import stat
import zlib

INVENTORY = 'tests/fixtures/verification_v022/inventory.json.gz'
COVERAGE = 'tests/fixtures/verification_v029/coverage.json.gz'
CURRENT_PATHS = frozenset((INVENTORY, COVERAGE))
MAX_BYTES = 16 * 1024 * 1024
HEADER = b'\x1f\x8b\x08\x00\x00\x00\x00\x00\x02\xff'


def current_path(root, relative):
    if relative not in CURRENT_PATHS:
        raise ValueError('unsupported current metadata path')
    return Path(root) / relative


def decode_bytes(relative, stored):
    """Exactly one canonical-header gzip member; bounded output, no fallback."""
    current_path('.', relative)
    if type(stored) is not bytes or len(stored) > MAX_BYTES or stored[:10] != HEADER:
        raise ValueError('invalid current metadata gzip header or stored size')
    try:
        decoder = zlib.decompressobj(16 + zlib.MAX_WBITS)
        decoded = decoder.decompress(stored, MAX_BYTES + 1)
    except zlib.error as error:
        raise ValueError('invalid current metadata gzip stream') from error
    if (len(decoded) > MAX_BYTES or not decoder.eof or
            decoder.unconsumed_tail or decoder.unused_data):
        raise ValueError('incomplete, trailing or oversized current metadata gzip')
    return decoded


def read_bytes(root, relative):
    path = current_path(root, relative)
    plain = path.with_suffix('')
    if path.is_symlink() or plain.exists() or plain.is_symlink():
        raise ValueError('linked current metadata or obsolete plain duplicate')
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
    output = io.BytesIO()
    with gzip.GzipFile(filename='', mode='wb', fileobj=output, compresslevel=9, mtime=0) as stream:
        stream.write(decoded)
    stored = output.getvalue()
    if len(stored) > MAX_BYTES or stored[:10] != HEADER:
        raise ValueError('current metadata stored size or header differs')
    return stored


def write_bytes(root, relative, decoded):
    path = current_path(root, relative)
    plain = path.with_suffix('')
    if path.is_symlink() or plain.exists() or plain.is_symlink():
        raise ValueError('linked current metadata or obsolete plain duplicate')
    stored = encode_bytes(relative, decoded)
    path.write_bytes(stored)
