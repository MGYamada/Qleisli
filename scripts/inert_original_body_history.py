"""Inert original-body history validation; no extraction, imports or execution of saved code.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import hashlib
import json
from pathlib import PurePosixPath
import tarfile

CHUNKED_TAR_LIMIT = 16 * 1024 * 1024
CHUNKED_MEMBER_LIMIT = 8_000_000
CHUNKED_METADATA_LIMIT = 4 * 1024 * 1024
CHUNKED_INNER_MEMBERS = 1268
CHUNKED_ORIGINAL_FILES = 3405
CHUNKED_INNER_EXPANDED = 13_187_499
CHUNKED_METADATA_NAMES = {
    'transport.json', 'derived/validation.json', 'provenance/producers.json',
}


def _chunk_require(ok, message):
    if not ok:
        raise AssertionError(message)


def _chunk_name(name):
    _chunk_require(type(name) is str and name not in ('', '.', '..')
                   and '\x00' not in name and '\\' not in name,
                   'invalid inert original name')
    path = PurePosixPath(name)
    _chunk_require(not path.is_absolute() and '..' not in path.parts
                   and str(path) == name, 'noncanonical inert original name')
    return name


def _chunk_sha(value):
    _chunk_require(type(value) is str and len(value) == 64
                   and all(c in '0123456789abcdef' for c in value),
                   'invalid inert SHA256')
    return value


def _chunk_json(raw):
    _chunk_require(type(raw) is bytes and 0 < len(raw) <= CHUNKED_METADATA_LIMIT,
                   'inert metadata exceeds fixed bound')

    def unique(pairs):
        result = {}
        for key, value in pairs:
            _chunk_require(key not in result, 'duplicate inert JSON key')
            result[key] = value
        return result

    def constant(_):
        raise AssertionError('nonfinite inert JSON number')

    try:
        value = json.loads(raw.decode('utf-8'), object_pairs_hook=unique,
                           parse_constant=constant)
    except (UnicodeError, ValueError, RecursionError) as error:
        raise AssertionError('invalid inert JSON') from error
    _chunk_require(type(value) is dict, 'inert JSON must be an object')
    return value


def _chunk_identity(raw, row, limit, *, nonempty=True):
    _chunk_require(type(row) is dict and set(row) == {'bytes', 'sha256'},
                   'invalid inert identity fields')
    size = row['bytes']
    _chunk_require(type(size) is int and int(nonempty) <= size <= limit,
                   'inert byte count exceeds fixed bound')
    _chunk_sha(row['sha256'])
    _chunk_require(type(raw) is bytes and len(raw) == size
                   and hashlib.sha256(raw).hexdigest() == row['sha256'],
                   'inert bytes changed')


def _chunk_tar_size(sizes):
    # The exact canonical USTAR writer used by this inert profile pads to a
    # 10,240-byte record, after two 512-byte zero end blocks.
    used = sum(512 + ((size + 511) // 512) * 512 for size in sizes) + 1024
    return ((used + 10239) // 10240) * 10240


def validate_chunked_tar_history(outer):
    """Validate fixed inert history bytes, never extract or execute originals.

    The existing read_history verifies the pinned outer container. This adds
    strict validation of its exact reconstructed original USTAR byte stream.
    The caller must pin the outer index/archive through read_history first.
    """
    _chunk_require(type(outer) is dict and 'transport.json' in outer,
                   'missing explicit inert transport')
    transport = _chunk_json(outer['transport.json'])
    _chunk_require(set(transport) == {
        'format', 'version', 'chunks', 'inner_tar', 'member_count',
        'original_files', 'expanded_bytes',
    }, 'unexpected inert transport fields')
    _chunk_require(transport['format'] == 'qleisli.inert-chunked-tar-history'
                   and type(transport['version']) is int
                   and transport['version'] == 1, 'unknown inert transport')
    for key, expected in [('member_count', CHUNKED_INNER_MEMBERS),
                          ('original_files', CHUNKED_ORIGINAL_FILES),
                          ('expanded_bytes', CHUNKED_INNER_EXPANDED)]:
        _chunk_require(type(transport[key]) is int and transport[key] == expected,
                       'original history scope changed')
    chunks = transport['chunks']
    _chunk_require(type(chunks) is list and len(chunks) == 2,
                   'exactly two inert chunks required')
    names, parts = set(), []
    for row in chunks:
        _chunk_require(type(row) is dict
                       and set(row) == {'record', 'bytes', 'sha256'},
                       'invalid inert chunk fields')
        name = _chunk_name(row['record'])
        _chunk_require(name not in names and name not in CHUNKED_METADATA_NAMES
                       and name in outer, 'missing or repeated inert chunk')
        _chunk_identity(outer[name], {k: row[k] for k in ('bytes', 'sha256')},
                        CHUNKED_MEMBER_LIMIT)
        names.add(name)
        parts.append(outer[name])
    _chunk_require(set(outer) == names | CHUNKED_METADATA_NAMES,
                   'missing or extra outer inert member')
    _chunk_require(all(type(blob) is bytes and len(blob) <= CHUNKED_MEMBER_LIMIT
                       for blob in outer.values()), 'outer member bound')
    # Producer separately pins/checks the actual outer USTAR length. The
    # unchanged outer reader exposes payloads, so this checks the canonical
    # five-member envelope budget, not a new outer-header parser guarantee.
    _chunk_require(_chunk_tar_size(map(len, outer.values())) <= CHUNKED_TAR_LIMIT,
                   'canonical outer USTAR exceeds 16MiB')
    _chunk_require(sum(map(len, parts)) <= CHUNKED_TAR_LIMIT,
                   'reconstructed inner USTAR exceeds 16MiB')
    raw = b''.join(parts)
    _chunk_identity(raw, transport['inner_tar'], CHUNKED_TAR_LIMIT)
    _chunk_require(len(raw) % 10240 == 0, 'noncanonical USTAR record length')
    data, offset, total = {}, 0, 0
    zero = b'\x00' * 512
    while True:
        _chunk_require(offset + 512 <= len(raw), 'truncated USTAR header')
        header = raw[offset:offset + 512]
        if header == zero:
            _chunk_require(offset + 1024 <= len(raw)
                           and raw[offset + 512:offset + 1024] == zero,
                           'missing USTAR end block')
            _chunk_require(len(raw) == ((offset + 1024 + 10239) // 10240) * 10240
                           and not any(raw[offset:]),
                           'trailing or noncanonical USTAR padding')
            break
        try:
            name = header[:100].split(b'\x00', 1)[0].decode('ascii')
            size = int(header[124:136].rstrip(b'\x00 '), 8)
        except (UnicodeError, ValueError) as error:
            raise AssertionError('invalid USTAR header') from error
        _chunk_name(name)
        _chunk_require(name == 'original-records.json'
                       or (name.startswith('objects/') and len(name) == 72),
                       'unexpected original USTAR member')
        if name.startswith('objects/'):
            _chunk_sha(name[8:])
        _chunk_require(name not in data and len(data) < CHUNKED_INNER_MEMBERS,
                       'duplicate or extra original USTAR member')
        _chunk_require(0 <= size <= CHUNKED_MEMBER_LIMIT, 'inner member bound')
        canonical = tarfile.TarInfo(name)
        canonical.size = size
        canonical.mode = 0o644
        canonical.uid = canonical.gid = canonical.mtime = 0
        canonical.uname = canonical.gname = ''
        _chunk_require(header == canonical.tobuf(format=tarfile.USTAR_FORMAT),
                       'nonregular or changed canonical USTAR header')
        start, end = offset + 512, offset + 512 + size
        padded_end = start + ((size + 511) // 512) * 512
        _chunk_require(padded_end <= len(raw) and not any(raw[end:padded_end]),
                       'truncated member or nonzero USTAR alignment')
        total += size
        _chunk_require(total <= CHUNKED_INNER_EXPANDED,
                       'inner payload exceeds fixed expanded bound')
        blob = raw[start:end]
        if name.startswith('objects/'):
            _chunk_require(hashlib.sha256(blob).hexdigest() == name[8:],
                           'content-addressed object changed')
        data[name] = blob
        offset = padded_end
    _chunk_require(len(data) == CHUNKED_INNER_MEMBERS
                   and total == CHUNKED_INNER_EXPANDED
                   and 'original-records.json' in data,
                   'incomplete original USTAR')
    mapping = _chunk_json(data['original-records.json'])
    _chunk_require(set(mapping) == {'format', 'version', 'records'}
                   and mapping['format'] == 'qleisli.inert-original-records'
                   and type(mapping['version']) is int and mapping['version'] == 1,
                   'invalid original-file map')
    originals = mapping['records']
    _chunk_require(type(originals) is dict and len(originals) == CHUNKED_ORIGINAL_FILES,
                   'original path set changed')
    used = set()
    for name, row in originals.items():
        _chunk_name(name)
        _chunk_require(type(row) is dict
                       and set(row) == {'record', 'bytes', 'sha256', 'original_mode'},
                       'invalid original-file fields')
        _chunk_sha(row['sha256'])
        record = 'objects/' + row['sha256']
        _chunk_require(row['record'] == record and record in data,
                       'original-file object reference changed')
        mode = row['original_mode']
        _chunk_require(type(mode) is int and 0 <= mode <= 0o777,
                       'invalid original-file permission mode')
        _chunk_identity(data[record], {k: row[k] for k in ('bytes', 'sha256')},
                        CHUNKED_MEMBER_LIMIT, nonempty=False)
        used.add(record)
    _chunk_require(set(data) == used | {'original-records.json'},
                   'unreferenced or missing original object')
    metadata = {'transport': transport,
                'validation': _chunk_json(outer['derived/validation.json']),
                'provenance': _chunk_json(outer['provenance/producers.json'])}
    return data, originals, metadata



FORMAT = 'qleisli.original-body-reference-validation'
VERSION = 1
PREFIX = '/private/tmp/'
FILES = ('command.json', 'result.json', 'stdout', 'stderr', 'outputs.json')
PLAN_KEYS = ('argv', 'cwd', 'rss_group_limit_kib', 'host_memory_free_floor_percent', 'monitor_revision')


def check(ok, reason):
    if not ok:
        raise ValueError(reason)


def key(path):
    check(type(path) is str and path.startswith(PREFIX), 'expected historical tmp path')
    return path[len(PREFIX):]


def stage_records(root, originals):
    directories = set()
    prefix = root + '/'
    for name in originals:
        if not name.startswith(prefix):
            continue
        parts = name[len(prefix):].split('/')
        if (len(parts) == 2 and len(parts[0]) > 3 and parts[0][:2].isdigit()
                and parts[0][2] == '-' and parts[1] in FILES):
            directories.add(parts[0])
    stages = []
    for directory in sorted(directories):
        path = root + '/' + directory
        records = {name: path + '/' + name for name in FILES if path + '/' + name in originals}
        check({'command.json', 'stdout', 'stderr'} <= set(records), 'incomplete original stage streams')
        stage = {'directory': PREFIX + path, 'records': records}
        if 'result.json' not in records:
            stage['result'] = None
        stages.append(stage)
    return stages


def stage_counts(stages, original_json):
    counts = {'success': 0, 'failed': 0, 'unfinished': 0}
    for stage in stages:
        if PurePosixPath(stage['directory']).name.startswith('00-'):
            continue
        result = stage['records'].get('result.json')
        if result is None:
            counts['unfinished'] += 1
        elif original_json(result)['exit_code'] == 0:
            counts['success'] += 1
        else:
            counts['failed'] += 1
    return counts


def original_report(root, originals):
    return {'record': root + '/report.json'} if root + '/report.json' in originals else None


def observer_source(name, external):
    row = external[name]
    return {'path': row['source'], 'bytes': row['bytes'], 'mode': row['original_mode'], 'sha256': row['sha256']}


def expand_validation(compact, originals, original_json):
    """Recover the prior derived object exactly, without the external reports."""
    check(compact['format'] == FORMAT and compact['version'] == VERSION, 'unknown reference layout')
    external = {name: {'bytes': size, 'category': compact['external_record_categories'][category],
                       'original_mode': mode, 'sha256': sha, 'source': PREFIX + name}
                for name, size, mode, sha, category in compact['external_records']}
    roots = [{'path': PREFIX + root, 'selected_original_files': count, 'status': compact['source_packet_status']}
             for root, count in compact['source_packet_roots']]
    runs = []
    for old in compact['runs']:
        root, report_name = old['root'], old['external_observer_report']
        stages = stage_records(root, originals)
        observer_root = str(PurePosixPath(report_name).parent)
        plan = original_json(observer_root + '/plan.json')
        observer = dict(old['observer'])
        for field in old['observer_plan_fields']:
            observer[field] = plan[field]
        observer['source'] = observer_source(report_name, external)
        row = {k: v for k, v in old.items() if k not in
               ('root', 'observer', 'external_observer_report', 'observer_plan_fields')}
        row.update(validation_directory=PREFIX + root, stages=stages,
                   fresh_stage_results=stage_counts(stages, original_json),
                   inner_report=original_report(root, originals), observer_report=observer,
                   observer_directory=PREFIX + observer_root)
        if root + '/inputs.json' in originals:
            row['input_plan_record'] = root + '/inputs.json'
        runs.append(row)
    out = {k: v for k, v in compact.items() if k not in
           ('prior_schema', 'external_record_categories', 'source_packet_status', 'reference_layout')}
    out.update(format=compact['prior_schema'][0], version=compact['prior_schema'][1],
               runs=runs, external_records=external, source_packet_roots=roots)
    return out


ORIGINAL_TAR = {'bytes': 14141440, 'sha256': 'd030a38d7ebada21e1f0f3a93b87ea9eb23d8e9bcef65b076854e9397c790e47'}
RECOVERED_VALIDATION = (191309, '5d69b0cb95864a5f6c789363bfc900125b016cc699e70aad41f72326715e0a8f')


def recover_original_body_history(outer):
    """Recover this fixed history through live source, never archived producer code."""
    data, originals, metadata = validate_chunked_tar_history(outer)
    _chunk_require(metadata['transport']['inner_tar'] == ORIGINAL_TAR,
                   'fixed original USTAR identity changed')
    compact = dict(metadata['validation'])
    packaging = compact.pop('chunk_transport_retention')
    _chunk_require(packaging['metadata02_decoded_validation'] ==
                   dict(zip(('bytes', 'sha256'), RECOVERED_VALIDATION)),
                   'predecessor validation identity changed')
    def original_json(name):
        _chunk_require(name in originals, 'missing retained original reference')
        return _chunk_json(data[originals[name]['record']])
    recovered = expand_validation(compact, originals, original_json)
    raw = (json.dumps(recovered, sort_keys=True, separators=(',', ':')) + '\n').encode()
    _chunk_require((len(raw), hashlib.sha256(raw).hexdigest()) == RECOVERED_VALIDATION,
                   'reference recovery changed retained observations')
    return data, originals, metadata, recovered
