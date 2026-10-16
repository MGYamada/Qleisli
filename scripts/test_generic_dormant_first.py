#!/usr/bin/env python3
"""Validate generic/dormant first studies as bounded inert data, never replay them.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import collections
from datetime import datetime
import gzip
import hashlib
import io
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import tarfile
import tempfile
import tomllib

ROOT = Path(__file__).resolve().parents[1]
STUDY = ROOT / 'tests/fixtures/authoring_sessions/generic-dormant-v030'
MANIFEST_SHA = 'ab8408f90fd19c4908d4b7f8daa372abedf892ff48f15780241204106740b8cc'
SOURCE_FREEZE = 'd9a76a5c4a3951485f9f5c687172395c9d2b230fd20ecab243048400d088690a'
CAPTURE_FREEZE = '799ab6a3b87c75afdec7875a40d9c02715abfa829cd03102d58e22f01686eee8'
PLAN_SHA = 'dc964bb285afb103e175d950b3e9d34376881f738b91be50ec5b233c022ae518'
SUMMARY_SHA = '34ad5557ccfd2bd15a534d58ea22e340125e7b225b40cd35c3b977e3cef5a899'
DRIVER_SHA = 'd7c11811adcf78073cd10f7b7d5ef7baea24ec19f96fd7fe99762d9b90858b53'
INPUT_SHA = '02460b6b65f67015dbd1e81cdc59eefe6b6573b20630b643979ca57c24829a63'
HEAD = 'a70211706db3928bc0e172bd57458a1127c57cd1'
TREE = '77e66e7890d770ea9c1d37cc81d19c5c7fde6608'
CLI_SHA = 'd6d285819917aa3d1167c3efc73d7f81ec684b5ee89ce7ed37c8660997070e64'
KERNEL_SHA = '54c9d60b80f67217abd95c8fe6ec1c06aa262e142d5e6db30f46a20cb90faf07'
MAX_STORED = 2 * 1024 * 1024
MAX_CONTENT = 5 * 1024 * 1024
MAX_MEMBER = 4 * 1024 * 1024
MAX_MEMBERS = 80
MAX_CONTAINER = MAX_CONTENT + MAX_MEMBERS * 1024 + 10240
HEX = re.compile(r'[0-9a-f]{64}')
PACKET_TOTALS = {'first-sources': (20, 66507), 'first-observations': (50, 3978071)}


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def load_json(data):
    return json.loads(data, object_pairs_hook=unique_object)


def local_name(name):
    require(type(name) is str and name
            and not any(ord(c) < 32 or c in '\\:' for c in name), 'invalid member path')
    path = PurePosixPath(name)
    require(path.parts and not path.is_absolute() and '..' not in path.parts
            and str(path) == name and all(p not in {'.', ''} for p in path.parts),
            'nonlocal member path')
    return name


def integer(value, limit):
    return type(value) is int and 0 <= value <= limit


def read_file(path, limit, study=STUDY):
    require(path.is_file() and not path.is_symlink()
            and path.resolve().is_relative_to(study.resolve()), 'nonlocal retained file')
    require(path.stat().st_size <= limit, 'retained file exceeds read bound')
    with path.open('rb') as stream:
        content = stream.read(limit + 1)
    require(len(content) <= limit, 'retained file grew beyond read bound')
    return content


def header_text(field):
    value, separator, padding = field.partition(b'\0')
    require(not separator or not any(padding), 'noncanonical raw tar text')
    return value.decode('utf-8')


def check_ustar_container(raw, expected_count):
    """Scan original headers, including names, before tarfile can hide extensions."""
    require(type(raw) is bytes and len(raw) <= MAX_CONTAINER
            and len(raw) % 512 == 0 and integer(expected_count, MAX_MEMBERS),
            'invalid bounded tar container')
    offset = expanded = 0
    names = []
    seen = set()
    while True:
        header = raw[offset:offset + 512]
        require(len(header) == 512, 'missing tar terminator')
        if not any(header):
            require(len(raw) - offset >= 1024 and not any(raw[offset:]),
                    'invalid tar terminator or nonzero tail')
            require(len(names) == expected_count, 'raw tar member count differs')
            return names
        require(len(names) < expected_count and len(names) < MAX_MEMBERS,
                'raw tar member count exceeds bound')
        require(header[156:157] == tarfile.REGTYPE
                and header[257:263] == b'ustar\0' and header[263:265] == b'00',
                'nonregular or non-USTAR raw header')
        name, prefix = header_text(header[:100]), header_text(header[345:500])
        name = local_name(prefix + '/' + name if prefix else name)
        require(name not in seen, 'duplicate raw tar member')
        seen.add(name)
        size_field, checksum = header[124:136], header[148:156]
        require(re.fullmatch(rb'[0-7]{11}\x00', size_field) is not None,
                'noncanonical raw tar size')
        require(re.fullmatch(rb'[0-7]{6}\x00 ', checksum) is not None
                and int(checksum[:6], 8) == sum(header[:148]) + 8 * 32 + sum(header[156:]),
                'invalid raw tar checksum')
        size = int(size_field[:-1], 8)
        require(size <= MAX_MEMBER and size <= MAX_CONTENT - expanded,
                'raw tar member or content exceeds bound')
        data_end = offset + 512 + size
        next_offset = offset + 512 + ((size + 511) // 512) * 512
        require(next_offset <= len(raw) and not any(raw[data_end:next_offset]),
                'truncated tar member or nonzero padding')
        expanded += size
        names.append(name)
        offset = next_offset


def check_synthetic_containers():
    """New tiny malformed bytes exercise guards; retained commands stay inert."""
    def member(name, kind=tarfile.REGTYPE, content=b'x'):
        info = tarfile.TarInfo(name)
        info.type, info.size, info.mode = kind, len(content), 0o644
        return (info.tobuf(format=tarfile.USTAR_FORMAT) + content
                + bytes((-len(content)) % 512))

    regular, terminator = member('control'), bytes(1024)
    require(check_ustar_container(regular + terminator, 1) == ['control'],
            'synthetic regular control differs')
    rejected = [
        (member('extension', tarfile.XHDTYPE, b'') + regular + terminator, 1),
        (member('extension', tarfile.XGLTYPE, b'') + regular + terminator, 1),
        (member('extension', tarfile.GNUTYPE_LONGNAME, b'control\0') + regular + terminator, 1),
        (member('extension', tarfile.GNUTYPE_LONGLINK, b'control\0') + regular + terminator, 1),
        (member('fifo', tarfile.FIFOTYPE, b'') + terminator, 1),
        (member('link', tarfile.SYMTYPE, b'') + terminator, 1),
        (member('link', tarfile.LNKTYPE, b'') + terminator, 1),
        (member('directory/', tarfile.DIRTYPE, b'') + terminator, 1),
        (regular + regular + terminator, 2),
        (member('../escape') + terminator, 1),
        (member('/absolute') + terminator, 1),
        (member('C:/absolute') + terminator, 1),
        (member('parent\\escape') + terminator, 1),
        (member('parent//child') + terminator, 1),
        (regular + bytes(512), 1),
        (regular + terminator + bytes(511) + b'x', 1),
    ]
    for raw, count in rejected:
        try:
            check_ustar_container(raw, count)
        except ValueError:
            pass
        else:
            raise ValueError('malformed synthetic tar container accepted')
    # Declared sizes/counts must fail before payload allocation or tar parsing.
    oversized = tarfile.TarInfo('oversized')
    oversized.size = MAX_MEMBER + 1
    try:
        check_ustar_container(oversized.tobuf(format=tarfile.USTAR_FORMAT) + terminator, 1)
    except ValueError as error:
        require(str(error) == 'raw tar member or content exceeds bound',
                'oversized member did not fail at the size preflight')
    else:
        raise ValueError('oversized raw tar member accepted')
    try:
        check_ustar_container(regular + terminator, MAX_MEMBERS + 1)
    except ValueError as error:
        require(str(error) == 'invalid bounded tar container',
                'oversized member count did not fail at preflight')
    else:
        raise ValueError('oversized raw tar member count accepted')
    try:
        load_json(b'{"duplicate": 1, "duplicate": 2}')
    except ValueError as error:
        require(str(error) == 'duplicate JSON key', 'unexpected duplicate JSON rejection')
    else:
        raise ValueError('duplicate synthetic JSON key accepted')


def read_archive(row, study=STUDY):
    require(set(row) == {'id', 'original_directory', 'archive', 'archive_bytes',
                        'archive_sha256', 'tar_bytes', 'tar_sha256', 'file_count',
                        'expanded_bytes', 'files'}, 'unexpected archive fields')
    name = local_name(row['archive'])
    require('/' not in name and name == row['id'] + '.tar.gz', 'invalid archive name')
    for field, limit in [('archive_bytes', MAX_STORED), ('tar_bytes', MAX_CONTAINER),
                         ('file_count', MAX_MEMBERS), ('expanded_bytes', MAX_CONTENT)]:
        require(integer(row[field], limit), 'invalid bounded archive count')
    require(type(row['original_directory']) is str
            and row['original_directory'].startswith('/private/tmp/'),
            'missing original packet location')
    require(all(type(row[f]) is str and HEX.fullmatch(row[f])
                for f in ['archive_sha256', 'tar_sha256']), 'invalid archive digest')
    require(type(row['files']) is list and len(row['files']) == row['file_count'],
            'invalid complete member inventory')
    entries = {}
    for item in row['files']:
        require(type(item) is dict and set(item) == {'path', 'bytes', 'sha256', 'original_mode'},
                'invalid member record')
        member_name = local_name(item['path'])
        require(member_name not in entries and integer(item['bytes'], MAX_MEMBER)
                and type(item['sha256']) is str and HEX.fullmatch(item['sha256'])
                and item['original_mode'] == '0644', 'invalid original member identity')
        entries[member_name] = item
    require(list(entries) == sorted(entries, key=lambda path: PurePosixPath(path).parts),
            'member inventory is not canonical')
    require(sum(item['bytes'] for item in entries.values()) == row['expanded_bytes'],
            'expanded byte count differs')
    compressed = read_file(study / name, MAX_STORED, study)
    require(len(compressed) == row['archive_bytes'] and sha(compressed) == row['archive_sha256'],
            'archive identity differs')
    # Bound expansion before parsing original raw headers or member metadata.
    with gzip.GzipFile(fileobj=io.BytesIO(compressed), mode='rb') as stream:
        raw = stream.read(MAX_CONTAINER + 1)
    require(len(raw) <= MAX_CONTAINER and len(raw) == row['tar_bytes']
            and sha(raw) == row['tar_sha256'], 'tar container identity or bound differs')
    require(check_ustar_container(raw, row['file_count']) == list(entries),
            'raw tar inventory differs')
    files = {}
    with tarfile.open(fileobj=io.BytesIO(raw), mode='r:') as archive:
        for member in archive:
            member_name = local_name(member.name)
            require(member.type == tarfile.REGTYPE and not member.pax_headers
                    and member_name in entries and member_name not in files,
                    'unlisted, duplicate or nonregular tar member')
            expected = entries[member_name]
            require(member.size == expected['bytes'] and member.mode == 0o644
                    and member.uid == member.gid == member.mtime == 0
                    and member.uname == member.gname == '' and member.linkname == '',
                    'noncanonical member metadata')
            stream = archive.extractfile(member)
            require(stream is not None, 'missing tar member data')
            content = stream.read(member.size + 1)
            require(len(content) == member.size and sha(content) == expected['sha256'],
                    'original member bytes differ')
            files[member_name] = content
    require(list(files) == list(entries), 'missing or reordered archive members')
    return files


def check_inventory_freeze(files, name, digest, count, total):
    require(sha(files[name]) == digest, 'original freeze identity differs')
    frozen = load_json(files[name])
    entries = frozen['files']
    require(type(entries) is dict and len(entries) == frozen['file_count'] == count
            and frozen['total_bytes'] == total and set(entries) | {name} == set(files),
            'original freeze inventory differs')
    for path, row in entries.items():
        require(local_name(path) in files and set(row) == {'bytes', 'mode', 'sha256'}
                and row['mode'] == 0o644 and len(files[path]) == row['bytes']
                and sha(files[path]) == row['sha256'], 'historical frozen bytes or mode differ')
    require(sum(len(files[path]) for path in entries) == total, 'historical byte total differs')


def file_record(content):
    return {'bytes': len(content), 'mode': 0o644, 'sha256': sha(content)}


def check_sources(sources):
    check_inventory_freeze(sources, 'freeze.json', SOURCE_FREEZE, 19, 62872)
    require(sha(sources['plan.json']) == PLAN_SHA, 'first literal plan differs')
    manifests = [name for name in sources if name.endswith('/Qargo.toml')]
    require(len(manifests) == 6, 'complete project count differs')
    for name in manifests:
        manifest = tomllib.loads(sources[name].decode())
        require(manifest['schema-version'] == 2 and manifest['qrate']['edition'] == '2026'
                and name.removesuffix('Qargo.toml') + 'main.qli' in sources,
                'original complete project manifest differs')
    plan, cases, context = [load_json(sources[name]) for name in
                            ['plan.json', 'cases.json', 'context.json']]
    require(plan['format'] == 'qleisli.generic-dormant-frozen-first-plan'
            and plan['version'] == 1 and plan['case_count'] == 6
            and plan['planned_checks'] == len(plan['commands']) == 14
            and plan['planned_runs'] == plan['planned_emissions'] == 0
            and plan['max_authored_concrete_qubits'] == 2,
            'predeclared command count or physical scope differs')
    require(cases['case_count'] == len(cases['cases']) == 6
            and all(integer(c['max_authored_concrete_qubits'], 2) for c in cases['cases']),
            'bounded authored cases differ')
    require(context['observed_head'] == HEAD and context['observed_head_tree'] == TREE
            and context['observed_git_status_porcelain'] == ''
            and context['source_cli_native_cargo_build_invocations'] == 0
            and context['observations_created'] is False and context['goal_credit'] is False
            and 'prior runtime build' in context['cli']['provenance']
            and 'No clean a702117' in context['cli']['provenance'],
            'original informed/prior-build authoring context differs')
    require(plan['cli_sha256'] == context['cli']['sha256'] == CLI_SHA
            and plan['kernel_sha256'] == context['kernel']['sha256'] == KERNEL_SHA,
            'predeclared binary identities differ')
    # Historical executed=false denotes authoring time; observation data remains separate.
    require(load_json(sources['freeze.json'])['executed'] is False,
            'original authoring-time status was rewritten')
    return plan, context


def check_observations(sources, observed, plan, context):
    check_inventory_freeze(observed, 'capture-freeze.json', CAPTURE_FREEZE, 49, 3970271)
    require(sha(observed['summary.json']) == SUMMARY_SHA
            and sha(observed['observe.py']) == DRIVER_SHA, 'original capture bytes differ')
    summary, started, records, audit = [load_json(observed[name]) for name in
                                       ['summary.json', 'started.json', 'observations.json',
                                        'audit.json']]
    require(summary['complete'] is True and summary['observations'] == len(records) == 14
            and summary['accepted'] == 3 and summary['refused'] == 11
            and summary['all_windows_stable'] is True, 'actual outcome totals differ')
    require(started['driver'] == file_record(observed['observe.py'])
            and started['plan'] == PLAN_SHA and started['initial'] == summary['initial']
            and 'Prior runtime build' in started['cli_provenance'],
            'frozen original driver/plan/provenance differs')
    input_name = 'inputs-' + INPUT_SHA + '.json'
    inputs = load_json(observed[input_name])
    require(type(inputs) is dict and len(inputs) == 18993, 'complete input inventory differs')
    canonical = json.dumps(inputs, sort_keys=True, separators=(',', ':')).encode()
    require(sha(canonical) == INPUT_SHA and observed[input_name] == canonical + b'\n',
            'canonical observed input digest differs')
    require(collections.Counter(name.split('/', 1)[0] for name in inputs)
            == {'repository': 18971, 'first': 20, 'executable': 2},
            'observed input categories differ')
    for name, item in inputs.items():
        require(type(item) is dict and set(item) == {'bytes', 'mode', 'sha256'}
                and integer(item['bytes'], 150 * 1024 * 1024)
                and type(item['mode']) is int and item['mode'] in {0o644, 0o755}
                and type(item['sha256']) is str and HEX.fullmatch(item['sha256']),
                'invalid bounded observed file identity')
        if not name.startswith('executable/'):
            local_name(name)
    require({name.removeprefix('first/'): value for name, value in inputs.items()
             if name.startswith('first/')} ==
            {name: file_record(content) for name, content in sources.items()},
            'complete original source/input binding differs')
    for kind, digest in [('cli', CLI_SHA), ('kernel', KERNEL_SHA)]:
        path = plan[kind + '_path']
        require(context[kind]['path'] == path
                and inputs['executable/' + path]['sha256'] == digest,
                'original executable observation differs')
    require(len(context['production_sources']) == 173, 'production binding count differs')
    for name, item in context['production_sources'].items():
        original = inputs['repository/' + local_name(name)]
        require(item == {key: original[key] for key in ['bytes', 'sha256']},
                'original production source identity differs')

    def window(value):
        require(set(value) == {'utc', 'sha256', 'inventory', 'files', 'head', 'tree', 'status'}
                and value['sha256'] == INPUT_SHA and value['inventory'] == input_name
                and value['files'] == 18993 and value['head'] == HEAD
                and value['tree'] == TREE and value['status'] == '',
                'original before/after window differs')
        return datetime.fromisoformat(value['utc'])

    previous, final = window(summary['initial']), window(summary['final'])
    require(previous < final, 'invalid complete capture interval')
    expected_codes = ['unsupported', None, 'unsupported', None, 'unsupported', None,
                      'contract', 'contract', 'unsupported', 'limit', 'effect', 'effect',
                      'contract', 'contract']
    expected_files = {input_name, 'observe.py', 'started.json', 'summary.json',
                      'observations.json', 'audit.json', 'results.md', 'capture-freeze.json'}
    for ordinal, (row, command, code) in enumerate(zip(records, plan['commands'], expected_codes)):
        require(row == load_json(observed[f'{ordinal:02}.json'])
                and row['number'] == ordinal and row['id'] == command['id']
                and row['argv'] == command['argv'] and row['cwd'] == command['cwd']
                and row['prediction'] == command['prediction']
                and row['exit_code'] == command['prediction']['exit_code'] == (0 if code is None else 1)
                and row['prediction']['diagnostic_code'] == code and row['timeout'] is False
                and row['source_window_stable'] is True
                and type(row['seconds']) in {float, int} and math.isfinite(row['seconds'])
                and 0 < row['seconds'] < 120, 'original invocation/timing/prediction differs')
        require(row['argv'][:3] == [plan['cli_path'], '--format=json', 'check']
                and row['argv'][-1] == '--lean-kernel=' + plan['kernel_path'],
                'literal command kind or explicit kernel differs')
        before, after = window(row['before']), window(row['after'])
        require(previous <= before <= after <= final, 'unordered original observation windows')
        previous = after
        expected_files.add(f'{ordinal:02}.json')
        for stream in ['stdout', 'stderr']:
            name = f'{ordinal:02}.{stream}'
            expected_files.add(name)
            require(file_record(observed[name]) == row[stream], 'original raw stream differs')
        require(row['stderr']['bytes'] == 0, 'original stderr differs')
        parsed = load_json(observed[f'{ordinal:02}.stdout'])
        codes = [d['code'] for d in parsed['diagnostics']]
        require(parsed['format'] == 'qleisli.result' and parsed['version'] == 1
                and parsed['command'] == 'check' and codes == row['diagnostic_codes']
                == ([] if code is None else [code]), 'original JSON schema/diagnostic differs')
        if code is None:
            result = parsed['result']
            require(parsed['outcome'] == 'ok' and parsed['diagnostics'] == []
                    and result['status'] == 'checked' and result['checker_identity'] == 'unpinned'
                    and result['checker_path'] == plan['kernel_path']
                    and result['request_checked'] is False
                    and result['source_preservation_verified'] is False
                    and result['verification'] == {'scope': 'native-validity',
                        'request_origin': 'none', 'source_steps_checked': True,
                        'source_meaning_verified': False}
                    and result['execution_authority'] == 'checked-produced-ir'
                    and result['source_check_scope'] == 'all-supplied-module-declarations'
                    and result['native_check_scope'] == 'selected-specialization'
                    and result['ir_profile'] == 'raw', 'accepted scope differs')
            if ordinal == 5:
                require(result['entry'] == 'main::main'
                        and row['prediction']['uncertainty'],
                        'C harmless-main result was promoted to dormant discharge')
        else:
            require(parsed['outcome'] == 'error' and parsed['result'] is None,
                    'a refusal gained acceptance authority')
    require(set(observed) == expected_files, 'unlisted or missing original observation')
    require(audit['actual_checks'] == audit['predictions_matched'] == 14
            and audit['accepted'] == 3 and audit['refused'] == 11 and audit['timeouts'] == 0
            and audit['captured_input_inventory_sha256'] == INPUT_SHA
            and audit['summary_sha256'] == SUMMARY_SHA and audit['driver_sha256'] == DRIVER_SHA
            and audit['source_freeze_sha256'] == SOURCE_FREEZE
            and audit['unfinished_capture'] == []
            and len(audit['original_observation_files']) == 47,
            'original independent audit differs')
    original = audit['original_observation_files']
    require(set(original) == set(observed) - {'audit.json', 'results.md', 'capture-freeze.json'}
            and sum(item['bytes'] for item in original.values()) == 3939993,
            'pre-audit complete inventory differs')
    for name, item in original.items():
        require(file_record(observed[local_name(name)]) == item,
                'original pre-audit observation identity differs')


def main():
    check_synthetic_containers()
    require(STUDY.is_dir() and not STUDY.is_symlink()
            and STUDY.resolve().is_relative_to(ROOT.resolve()), 'nonlocal study directory')
    raw_manifest = read_file(STUDY / 'packets.json', 32 * 1024)
    require(sha(raw_manifest) == MANIFEST_SHA, 'reviewed retention manifest differs')
    manifest = load_json(raw_manifest)
    require(set(manifest) == {'format', 'version', 'scope', 'archives'}
            and manifest['format'] == 'qleisli.generic-dormant-retention'
            and type(manifest['version']) is int and manifest['version'] == 1,
            'unknown retention format')
    rows = manifest['archives']
    require(type(rows) is list and [row['id'] for row in rows] == list(PACKET_TOTALS)
            and all((row['file_count'], row['expanded_bytes']) == PACKET_TOTALS[row['id']]
                    for row in rows), 'complete original packet counts differ')
    require(sum(row['archive_bytes'] for row in rows) <= MAX_STORED
            and sum(row['expanded_bytes'] for row in rows) <= MAX_CONTENT
            and sum(row['file_count'] for row in rows) <= MAX_MEMBERS,
            'aggregate retention exceeds fixed reader bounds')
    packets = {row['id']: read_archive(row) for row in rows}
    require({path.name for path in STUDY.iterdir()} ==
            {row['archive'] for row in rows} | {'packets.json', 'README.md'},
            'unlisted retained study path')
    plan, context = check_sources(packets['first-sources'])
    check_observations(packets['first-sources'], packets['first-observations'], plan, context)
    note = ' '.join(read_file(STUDY / 'README.md', 16 * 1024).decode().split())
    for disclosure in ['informed study, not a blind benchmark',
                       'not dormant Meaning discharge', 'prior runtime build copy',
                       'not a clean commit-to-binary build attestation',
                       'not isolated CLI-only execution time',
                       'It never executes recorded commands.',
                       'No source-preservation, PR, quantitative RS or EXACT discharge']:
        require(disclosure in note, 'missing retention disclosure: ' + disclosure)
    print('Generic/dormant history: two packets / 70 unchanged original files / '
          '4,044,578 expanded bytes; 14 checks, 3 accepted / 11 refused. No command executed.')
    check_interface_naturals_first()
    check_closed_interface_naturals_first()
    check_operation_identity_first()
    check_dormant_contracts_first()
    check_dormant_partial_access_first()
    check_dormant_controls_first()


def check_signature_tree(packet, files):
    """Visit only manifest-derived children; reject extras before traversing them."""
    files = {PurePosixPath(local_name(name)) for name in files}
    directories = {PurePosixPath('.')}
    for path in files:
        directories.update(path.parents)
    require(not files & directories, 'signature file/directory collision')
    children = {directory: {} for directory in directories}
    for directory in directories - {PurePosixPath('.')}:
        children[directory.parent][directory.name] = True
    for path in files:
        children[path.parent][path.name] = False
    pending = [PurePosixPath('.')]
    while pending:
        relative = pending.pop()
        path = packet / relative
        require(not path.is_symlink() and path.is_dir(), 'nonlocal signature directory')
        expected, seen = children[relative], set()
        with os.scandir(path) as entries:
            for entry in entries:
                require(entry.name in expected and entry.name not in seen,
                        'unlisted signature packet entry')
                is_directory = expected[entry.name]
                require(not entry.is_symlink()
                        and (entry.is_dir(follow_symlinks=False) if is_directory
                             else entry.is_file(follow_symlinks=False)),
                        'nonregular signature packet path')
                seen.add(entry.name)
                if is_directory:
                    pending.append(relative / entry.name)
        require(seen == set(expected), 'missing signature packet entry')


def check_synthetic_signature_trees():
    """Tiny temporary inventories exercise traversal guards, never retained data."""
    with tempfile.TemporaryDirectory() as temporary:
        packet = Path(temporary) / 'packet'
        packet.mkdir()
        nested = packet / 'nested'
        nested.mkdir()
        (nested / 'kept.txt').write_bytes(b'x')
        files = {'nested/kept.txt'}
        check_signature_tree(packet, files)

        def refused(message):
            try:
                check_signature_tree(packet, files)
            except ValueError as error:
                require(str(error) == message, 'unexpected signature inventory rejection')
            else:
                raise ValueError('malformed synthetic signature inventory accepted')

        extra = packet / 'extra.txt'
        extra.write_bytes(b'')
        refused('unlisted signature packet entry')
        extra.unlink()
        extra = packet / 'empty'
        extra.mkdir()
        refused('unlisted signature packet entry')
        extra.rmdir()
        (nested / 'kept.txt').unlink()
        nested.rmdir()
        target = Path(temporary) / 'target'
        target.mkdir()
        (target / 'kept.txt').write_bytes(b'x')
        nested.symlink_to(target, target_is_directory=True)
        refused('nonregular signature packet path')


def read_signature_packet(packet, manifest_sha, file_count, total_bytes,
                          packet_format='qleisli.interface-naturals-first-retention'):
    """Read a fixed, reviewed signature inventory as bounded inert bytes."""
    require(packet.is_dir() and not packet.is_symlink()
            and packet.resolve().is_relative_to(ROOT.resolve()), 'nonlocal signature study')

    def bounded(name):
        path = packet / local_name(name)
        require(path.is_file() and not path.is_symlink()
                and path.resolve().is_relative_to(packet.resolve()), 'nonlocal signature member')
        current = packet
        for component in PurePosixPath(name).parts:
            current /= component
            require(not current.is_symlink(), 'signature member traverses symlink')
        require(path.stat().st_size <= 16384, 'signature member exceeds read bound')
        with path.open('rb') as stream:
            raw = stream.read(16385)
        require(len(raw) <= 16384, 'signature member grew beyond read bound')
        return raw

    raw = bounded('retention.json')
    require(sha(raw) == manifest_sha,
            'reviewed signature retention manifest differs')
    manifest = load_json(raw)
    require(set(manifest) == {'format', 'version', 'scope', 'files'}
            and manifest['format'] == packet_format
            and type(manifest['version']) is int and manifest['version'] == 1,
            'unknown signature retention format')
    rows = manifest['files']
    require(type(rows) is list and len(rows) == file_count, 'signature inventory count differs')
    retained = {}
    for row in rows:
        require(set(row) == {'path', 'bytes', 'mode', 'sha256'}, 'signature member fields differ')
        name = local_name(row['path'])
        require(name not in retained and integer(row['bytes'], 16384)
                and row['mode'] == 0o644 and HEX.fullmatch(row['sha256']),
                'invalid signature member record')
        content = bounded(name)
        require(len(content) == row['bytes'] and sha(content) == row['sha256']
                and (packet / name).stat().st_mode & 0o777 == row['mode'],
                'original signature member bytes or mode differ')
        retained[name] = content
    require(sum(map(len, retained.values())) == total_bytes, 'signature retained byte count differs')
    check_signature_tree(packet, set(retained) | {'retention.json'})
    return retained


def check_interface_naturals_first():
    """Read the small signature study as inert bytes, including first failures."""
    check_synthetic_signature_trees()
    retained = read_signature_packet(
        ROOT / 'tests/fixtures/authoring_sessions/interface-naturals-v030',
        '1bba39eed405f899afad6156a3d6889cb733f4f82caad22f370b28eb56f0bd4e', 20, 9018)
    for case in ('ordinary', 'helper'):
        original = retained[case + '/main.qli']
        translation = retained['translations/' + case + '/main.qli']
        require(translation == original.replace(b'classical fn keep', b'unitary fn keep'),
                'separate signature translation differs')
        for prefix in ('', 'translations/'):
            declaration = tomllib.loads(retained[prefix + case + '/Qargo.toml'].decode())
            require(declaration == {'schema-version': 2, 'qrate': {'edition': '2026'}},
                    'signature source edition differs')
    for name, expected in [('first-observations.json', 'parse: classical functions cannot have static operation parameters'),
                           ('translation-observations.json', 'unsupported: finite profile does not support static Nat parameters')]:
        observation = load_json(retained[name])
        require(observation['cli_sha256'] == 'c4ce6f86e6c452594f021be8abb0f20c333a78033e5754bf94060eda6deaa28c'
                and observation['kernel_sha256'] == KERNEL_SHA
                and observation['observed_head'] == '3b2df9b6f688251e66ca2df4286674d1e0b34f81'
                and observation['inputs_stable'] is True and observation['binary_stable'] is True
                and observation['kernel_stable'] is True
                and observation['inputs_before'] == observation['inputs_after'],
                'signature observation identity or stability differs')
        for path, digest in observation['inputs_before'].items():
            require(sha(retained[local_name(path)]) == digest, 'signature input window differs')
        require([row['case'] for row in observation['observations']] == ['ordinary', 'helper'],
                'signature observation order differs')
        for row in observation['observations']:
            require(type(row['exit_code']) is int and row['exit_code'] == 1
                    and retained[local_name(row['stdout'])] == b''
                    and expected in retained[local_name(row['stderr'])].decode(),
                    'first signature refusal changed or acquired acceptance authority')
    initial = load_json(retained['first-plan.json'])
    require(initial['execution'] == 'not run; current finite generic profile still refuses',
            'initial signature freeze was rewritten after observation')
    note = ' '.join(retained['README.md'].decode().split())
    for disclosure in ('not a blind benchmark', 'not a clean commit-to-binary build attestation',
                       'No source-preservation theorem', 'never executes recorded commands'):
        require(disclosure in note, 'missing signature retention disclosure: ' + disclosure)
    print('Interface Nat first history: 20 unchanged original files / 9,018 bytes; '
          'four actual refusals, zero admitted generic sources. No command executed.')


def check_closed_interface_naturals_first():
    """Preserve concrete capacity refusal and the separately native-checked control."""
    retained = read_signature_packet(
        ROOT / 'tests/fixtures/authoring_sessions/closed-interface-naturals-v030',
        '25340276d56c41c23b03671f512569c36cdd44d0cc75ac8cc8cf36f4418971cc', 11, 5467)
    cases = ('ordinary', 'helper')
    inputs = {case + '/' + name for case in cases for name in ('Qargo.toml', 'main.qli')}
    for case in cases:
        declaration = tomllib.loads(retained[case + '/Qargo.toml'].decode())
        require(declaration == {'schema-version': 2, 'qrate': {'edition': '2026'}},
                'closed signature source edition differs')
    initial = load_json(retained['first-plan.json'])
    require([row['case'] for row in initial['cases']] == list(cases),
            'closed signature prediction order differs')
    for row in initial['cases']:
        require(type(row['authored_qubits']) is int and row['authored_qubits'] == 0
                and row['execution'] == 'not run'
                and row['source_sha256'] == sha(retained[row['case'] + '/main.qli']),
                'closed signature initial source freeze differs')
    observation = load_json(retained['first-observations.json'])
    require(observation['cli_sha256'] ==
            'e47c22d58acc237880301f99315db871ef234cdeca8a9bf1f06824f14eff36d3'
            and observation['kernel_sha256'] == KERNEL_SHA
            and observation['observed_head'] == '3b2df9b6f688251e66ca2df4286674d1e0b34f81'
            and observation['inputs_stable'] is True and observation['binary_stable'] is True
            and observation['kernel_stable'] is True
            and observation['inputs_before'] == observation['inputs_after']
            and set(observation['inputs_before']) == inputs,
            'closed signature observation identity or stability differs')
    for name, digest in observation['inputs_before'].items():
        require(sha(retained[local_name(name)]) == digest, 'closed signature input window differs')
    rows = observation['observations']
    require([row['case'] for row in rows] == list(cases),
            'closed signature observation order differs')
    for row, expected_exit in zip(rows, (1, 0)):
        require(type(row['exit_code']) is int and row['exit_code'] == expected_exit
                and row['stdout'] == row['case'] + '.first.stdout.txt'
                and row['stderr'] == row['case'] + '.first.stderr.txt',
                'closed signature observation result or stream association differs')
    require(retained['ordinary.first.stdout.txt'] == b''
            and 'limit: concrete natural arithmetic exceeds u32 or has negative subtraction'
            in retained['ordinary.first.stderr.txt'].decode(),
            'ordinary signature capacity refusal differs')
    require(retained['helper.first.stderr.txt'] == b'', 'closed helper acquired a diagnostic')
    output = retained['helper.first.stdout.txt'].decode().splitlines()
    for line in ('native checks: IR structure, ownership, interface, classical scope and '
                 'decoded execution view; 2 concrete local roots, 9 bundled roots',
                 'checker identity: unpinned',
                 'native decisions: 20; independent requests checked: 0',
                 'entry request checked: false', 'source preservation: not proved'):
        require(line in output, 'closed helper native checking scope differs: ' + line)
    note = ' '.join(retained['README.md'].decode().split())
    for disclosure in ('non-generic runtime functions', 'representation-capacity failure',
                       'not wrapping arithmetic or a different mathematical Nat meaning',
                       'not a clean commit-to-binary build attestation', 'No generic admission',
                       'retention reader never executes the recorded commands or source'):
        require(disclosure in note, 'missing closed signature disclosure: ' + disclosure)
    print('Closed interface Nat first history: 11 unchanged retained files / 5,467 bytes; '
          'one u32 capacity refusal, one concrete helper control checked; '
          '20 native decisions / zero independent requests. '
          'No generic admission or source-preservation proof. No command executed.')


def check_operation_identity_first():
    """Preserve one existing Op-only control; never replay recorded commands."""
    retained = read_signature_packet(
        ROOT / 'tests/fixtures/authoring_sessions/operation-identity-v030',
        '2122f6574f045a7af04f8ee47babd10090bd892fc4ec50c166020a1fcc68d693',
        8, 4992, 'qleisli.operation-identity-first-retention')
    declaration = tomllib.loads(retained['Qargo.toml'].decode())
    require(declaration == {'schema-version': 2, 'qrate': {'edition': '2026'}},
            'operation identity source edition differs')
    initial = load_json(retained['first-plan.json'])
    require(initial['status'] == 'not-run' and initial['authored_qubits'] == 0,
            'operation identity initial prediction differs')
    observation = load_json(retained['first-observation.json'])
    require(observation['observed_head'] == 'c14c0cbbfb3527384f68a770191774b2b1b16603'
            and observation['build_attestation'] is False
            and observation['identities']['cli'] ==
            'e47c22d58acc237880301f99315db871ef234cdeca8a9bf1f06824f14eff36d3'
            and observation['identities']['kernel'] == KERNEL_SHA
            and observation['inputs_stable'] is True
            and observation['binary_stable'] is True and observation['kernel_stable'] is True
            and observation['exit_code'] == 0
            and observation['stdout'] == 'first.stdout.txt'
            and observation['stderr'] == 'first.stderr.txt',
            'operation identity observed inputs or checking scope differs')
    require(set(observation['input_sha256']) == {'main.qli', 'Qargo.toml', 'first-plan.json'},
            'operation identity original input window differs')
    for name, digest in observation['input_sha256'].items():
        require(sha(retained[local_name(name)]) == digest,
                'operation identity source or prediction differs')
    require(retained['first.stderr.txt'] == b'', 'operation identity acquired a diagnostic')
    lines = retained['first.stdout.txt'].decode().splitlines()
    for line in ('native checks: IR structure, ownership, interface, classical scope and '
                 'decoded execution view; 4 concrete local roots, 9 bundled roots',
                 'checker identity: unpinned',
                 'native decisions: 23; independent requests checked: 0',
                 'entry: absent; entry request checked: not applicable',
                 'source preservation: not proved'):
        require(line in lines, 'operation identity native observation differs: ' + line)
    print('Operation identity first history: 8 unchanged files / 4,992 bytes; '
          '23 native decisions / zero independent requests; '
          'no generic admission or source-preservation proof. No command executed.')


def check_dormant_contracts_first():
    """Read both complete pre-repair packets without executing their commands."""
    study = ROOT / 'tests/fixtures/authoring_sessions/dormant-contracts-v030'
    require(study.is_dir() and not study.is_symlink()
            and study.resolve().is_relative_to(ROOT.resolve()), 'nonlocal contract study')
    manifest_bytes = read_file(study / 'packets.json', 32 * 1024, study)
    require(sha(manifest_bytes) ==
            '43bc5db07379ac2d87fe2d9c5d95a58ae98eedd42c5ac0f1d3ed1f684ca8bd6c',
            'dormant contract retention manifest differs')
    manifest = load_json(manifest_bytes)
    require(set(manifest) == {'format', 'version', 'scope', 'archives'}
            and manifest['format'] == 'qleisli.dormant-contracts-retention'
            and type(manifest['version']) is int and manifest['version'] == 1,
            'unknown dormant contract retention format')
    rows = manifest['archives']
    require(type(rows) is list and
            [(r['id'], r['file_count'], r['expanded_bytes']) for r in rows] ==
            [('first-contracts', 34, 196087), ('followup-contracts', 38, 36583)],
            'complete dormant contract packet counts differ')
    require(sum(r['archive_bytes'] for r in rows) <= MAX_STORED
            and sum(r['expanded_bytes'] for r in rows) <= MAX_CONTENT
            and sum(r['file_count'] for r in rows) <= MAX_MEMBERS,
            'aggregate dormant contract retention exceeds fixed reader bounds')
    check_signature_tree(study, [r['archive'] for r in rows] + ['packets.json', 'README.md'])
    packets = [read_archive(row, study) for row in rows]
    first, followup = packets
    for index, (row, files) in enumerate(zip(rows, packets)):
        plan = load_json(files['first-plan.json'])
        observed = load_json(files['first-observations.json'])
        follow = index == 1
        require(plan['execution'] == 'not run' and 'not blind benchmark' in plan['kind']
                and observed['build_attestation'] is False
                and observed['binary_stable'] is True and observed['kernel_stable'] is True,
                'dormant contract prediction or provenance differs')
        head = 'c3b463072dad16b4f082dcc49cf34263b2543dfa'
        cli = 'c0bdb167737522fc13f8be5f392fbe40d332d7d152a1adc24bf21a25ed0f02b6'
        cli_path = '/Users/masa/git/Qleisli/target/debug/qleisli'
        kernel_path = '/Users/masa/git/Qleisli/lean-kernel/.lake/build/bin/qleisli-kernel'
        for suffix in ('_before', '_after') if follow else ('',):
            require(observed['observed_head' + suffix] == head
                    and observed['cli_sha256' + suffix] == cli
                    and observed['kernel_sha256' + suffix] == KERNEL_SHA,
                    'observed source and prior binary identities differ')
        cases = plan['cases']
        inputs = {name: sha(data) for name, data in files.items()
                  if name.endswith(('/main.qli', '/Qargo.toml'))}
        if follow:
            inputs['first-plan.json'] = sha(files['first-plan.json'])
        require(observed['inputs_before'] == observed['inputs_after'] == inputs,
                'dormant contract complete input window differs')
        observations = observed['observations']
        require(len(observations) == len(cases)
                and {o['case'] for o in observations} == set(cases),
                'dormant contract original observations differ')
        for case, prediction in cases.items():
            require(prediction['authored_qubits'] == 0
                    and prediction['source_sha256'] == sha(files[case + '/main.qli'])
                    and tomllib.loads(files[case + '/Qargo.toml'].decode()) ==
                    {'schema-version': 2, 'qrate': {'edition': '2026'}},
                    'dormant contract original source identity differs')
        failures = {} if follow else {
            'direct_bad_control': '8:55: contract: exact equation U E_in = E_out u does not hold',
            'deferred_left_bad_right': '8:90: parse: expected `)`, found identifier'}
        for observation in observations:
            case = observation['case']
            require(observation['argv'] == [cli_path, 'check', row['original_directory'] + '/' + case]
                    and type(observation['exit_code']) is int
                    and observation['exit_code'] == int(case in failures)
                    and type(observation['seconds']) in (int, float)
                    and math.isfinite(observation['seconds']) and observation['seconds'] >= 0,
                    'dormant contract recorded command or outcome differs')
            if follow:
                require(observation['observed_head'] == head
                        and observation['cli_sha256'] == cli
                        and observation['kernel_sha256'] == KERNEL_SHA
                        and observation['environment_override'] == {'QLEISLI_KERNEL': kernel_path}
                        and observation['build_attestation'] is False
                        and observation['cli_stable_during_case'] is True
                        and observation['kernel_stable_during_case'] is True,
                        'follow-up per-command provenance differs')
            require(observation['stdout'] == case + '.first.stdout.txt'
                    and observation['stderr'] == case + '.first.stderr.txt',
                    'dormant contract full stream association differs')
            stdout, stderr = (files[observation[key]].decode() for key in ('stdout', 'stderr'))
            if case in failures:
                require(stdout == '' and stderr == row['original_directory'] + '/' + case
                        + '/main.qli:' + failures[case] + '\n',
                        'original parser and contract diagnostics differ')
            else:
                direct = case == 'direct_closed_phase_good'
                require(stderr == '' and stdout.splitlines() == [
                    'checked source: ' + row['original_directory'] + '/' + case,
                    'native checks: IR structure, ownership, interface, classical scope and '
                    f'decoded execution view; {3 if direct else 2} concrete local roots, 9 bundled roots',
                    'checker: ' + kernel_path, 'checker identity: unpinned',
                    f'native decisions: {24 if direct else 22}; independent requests checked: 1',
                    'entry: absent; entry request checked: not applicable',
                    'source preservation: not proved'], 'recorded native checking scope differs')
    prior = {name: sha(data) for name, data in first.items()}
    observed_followup = load_json(followup['first-observations.json'])
    require(observed_followup['inputs_stable'] is True
            and observed_followup['prior_first_evidence_unchanged'] is True
            and observed_followup['prior_first_hashes_before'] ==
            observed_followup['prior_first_hashes_after'] == prior,
            'follow-up rewrote the complete initial evidence or Rust snapshot map')
    note = ' '.join(read_file(study / 'README.md', 16 * 1024, study).decode().split())
    for disclosure in ('informed studies, not blind benchmarks', 'partial closed-Op study',
                       'Expression obligations remain outside this study',
                       'prior build, not a clean commit-to-binary build attestation',
                       'It never executes recorded commands.',
                       'No source/native/runtime preservation proof', 'no issue completion'):
        require(disclosure in note, 'missing dormant contract disclosure: ' + disclosure)
    print('Dormant contract first history: 72 unchanged files / 232,670 bytes; '
          'initial 5 accepts / 1 contract refusal / 1 parser refusal, then 9 accepts. '
          'Partial closed-Op study only. No command executed.')


def check_dormant_partial_access_first():
    """Preserve failed invocations separately from the actual P1 reproducer."""
    study = ROOT / 'tests/fixtures/authoring_sessions/dormant-partial-access-v030'
    require(study.is_dir() and not study.is_symlink()
            and study.resolve().is_relative_to(ROOT.resolve()), 'nonlocal partial-access study')
    raw = read_file(study / 'packets.json', 32 * 1024, study)
    require(sha(raw) == 'bd057f05d0d74be3097c0b12abf8bb33a54f1806dd2b7bc340cead75a110f2fc',
            'partial-access retention manifest differs')
    manifest = load_json(raw)
    require(set(manifest) == {'format', 'version', 'scope', 'archives'}
            and manifest['format'] == 'qleisli.dormant-partial-access-retention'
            and type(manifest['version']) is int and manifest['version'] == 1,
            'unknown partial-access retention format')
    rows = manifest['archives']
    require(type(rows) is list and
            [(r['id'], r['file_count'], r['expanded_bytes']) for r in rows] ==
            [('first-attempts', 30, 80376), ('schema2-followup', 18, 11185)],
            'complete partial-access packet counts differ')
    require(sum(r['archive_bytes'] for r in rows) <= MAX_STORED
            and sum(r['expanded_bytes'] for r in rows) <= MAX_CONTENT
            and sum(r['file_count'] for r in rows) <= MAX_MEMBERS,
            'aggregate partial-access retention exceeds fixed reader bounds')
    check_signature_tree(study, [r['archive'] for r in rows] + ['packets.json', 'README.md'])
    first, corrected = [read_archive(row, study) for row in rows]
    cases = ['partial_then_right', 'partial_then_left', 'closed_power_control',
             'partial_then_instantiated']
    for files in (first, corrected):
        plan = load_json(files['first-plan.json'])
        require(plan['review_comment'] == 4289672012 and plan['qubits'] == 0
                and plan['cases'] == cases and plan['build_attestation'] is False,
                'partial-access first prediction or review scope differs')
    require(load_json(first['first-plan.json'])['expected'] ==
            load_json(corrected['first-plan.json'])['expected'],
            'schema correction changed the original prediction')
    for case in cases:
        require(first[case + '/main.qli'] == corrected[case + '/main.qli'],
                'schema follow-up changed first QLI bytes')
        require(tomllib.loads(first[case + '/Qargo.toml'].decode()) ==
                {'qrate': {'name': 'partial_access', 'version': '0.0.0', 'edition': '2026'}}
                and tomllib.loads(corrected[case + '/Qargo.toml'].decode()) ==
                {'schema-version': 2, 'qrate': {'edition': '2026'}},
                'original missing-schema and corrected manifest distinction differs')
    source_window = lambda files: {name: sha(data) for name, data in files.items()
                                  if name == 'first-plan.json'
                                  or name.endswith(('/main.qli', '/Qargo.toml'))}
    first_inputs = source_window(first)
    rust = {name: sha(data) for name, data in first.items() if name.startswith('first-rust/')}
    require(set(rust) == {'first-rust/src/frontend/compile/dormant.rs',
                         'first-rust/src/frontend/compile/operations.rs',
                         'first-rust/src/frontend/compile/operations/bindings.rs'},
            'complete initial Rust snapshot inventory differs')
    first_inputs.update(rust)
    directory_inputs = dict(first_inputs, **{'first-observations.json': sha(first['first-observations.json'])})
    directory_inputs.update({name: sha(data) for name, data in first.items()
                             if name.endswith(('.first.stdout.txt', '.first.stderr.txt'))})
    cli_path = '/Users/masa/git/Qleisli/target/debug/qleisli'
    kernel_path = '/Users/masa/git/Qleisli/lean-kernel/.lake/build/bin/qleisli-kernel'
    identity = dict(cli=cli_path, cli_sha256='fac790a0f1c2805d8f1e6d3f31a86bf15e9c83474bca425b983c167af0b7d6a3',
                    kernel=kernel_path, kernel_sha256=KERNEL_SHA,
                    head='61ef86c13c752fe8c6fbb43ac47b757deaf37be7', build_attestation=False)
    stages = [(first, rows[0], 'first-observations.json', first_inputs, 'first', 'file'),
              (first, rows[0], 'followup-observations.json', directory_inputs, 'directory', 'schema'),
              (corrected, rows[1], 'first-observations.json', source_window(corrected), 'first', 'actual')]
    require([len(stage[3]) for stage in stages] == [12, 21, 9],
            'complete partial-access input-window counts differ')
    for files, row, record, inputs, suffix, stage in stages:
        observed = load_json(files[record])
        require(observed['identity'] == identity and observed['inputs_stable'] is True
                and observed['executables_stable'] is True
                and observed['inputs_before'] == observed['inputs_after'] == inputs
                and [o['case'] for o in observed['observations']] == cases,
                'partial-access observation, input window or identity differs')
        for observation in observed['observations']:
            case = observation['case']
            location = row['original_directory'] + '/' + case
            accepted = stage == 'actual' and case in cases[:2]
            require(observation['argv'] == [cli_path, 'check',
                    location + ('/main.qli' if stage == 'file' else ''), '--lean-kernel=' + kernel_path]
                    and type(observation['exit_code']) is int
                    and observation['exit_code'] == int(not accepted),
                    'partial-access recorded invocation or outcome differs')
            stdout, stderr = (files[case + '.' + suffix + '.' + stream + '.txt']
                              for stream in ('stdout', 'stderr'))
            require(sha(stdout) == observation['stdout_sha256']
                    and sha(stderr) == observation['stderr_sha256'],
                    'partial-access complete stdout/stderr association differs')
            if accepted:
                require(stderr == b'' and stdout.decode().splitlines() == [
                    'checked source: ' + location,
                    'native checks: IR structure, ownership, interface, classical scope and '
                    'decoded execution view; 1 concrete local roots, 9 bundled roots',
                    'checker: ' + kernel_path, 'checker identity: unpinned',
                    'native decisions: 20; independent requests checked: 0',
                    'entry: absent; entry request checked: not applicable',
                    'source preservation: not proved'], 'partial-access native scope differs')
            else:
                diagnostic = {'file': '/main.qli:1:1: project: Not a directory (os error 20)',
                              'schema': '/Qargo.toml:1:1: project: Qargo.toml requires schema-version = 2',
                              'actual': '/main.qli:4:85: limit: static repetition exceeds 1024 steps'}[stage]
                require(stdout == b'' and stderr.decode() == location + diagnostic + '\n',
                        'invocation/configuration failures and actual capacity refusals differ')
    observed = load_json(corrected['first-observations.json'])
    require(observed['prior_evidence_unchanged'] is True
            and observed['prior_evidence_hashes'] == {name: sha(data) for name, data in first.items()},
            'schema follow-up changed complete prior evidence or Rust snapshots')
    note = ' '.join(read_file(study / 'README.md', 16 * 1024, study).decode().split())
    for disclosure in ('eight invocation/configuration failures', 'two accepts and two limit refusals',
                       'zero authored qubits', 'not a maximum quantum-system case',
                       'then-dirty control work', '49753079',
                       'not a clean commit-to-binary build attestation',
                       'It never executes recorded commands.',
                       'No source/native/runtime preservation proof', 'no issue completion'):
        require(disclosure in note, 'missing partial-access disclosure: ' + disclosure)
    print('Dormant partial-access first history: 48 unchanged files / 91,561 bytes; '
          '8 invocation/configuration failures, then 2 accepts / 2 capacity refusals. '
          'Zero authored qubits. No command executed.')


def check_dormant_controls_first():
    """Preserve the real pre-repair sector gap; never replay recorded commands."""
    study = ROOT / 'tests/fixtures/authoring_sessions/dormant-controls-v030'
    require(study.is_dir() and not study.is_symlink()
            and study.resolve().is_relative_to(ROOT.resolve()), 'nonlocal control study')
    raw = read_file(study / 'packets.json', 32 * 1024, study)
    require(sha(raw) == 'd20674e4ea35c5e67923a63fcbe5843f940a7276d0fe7c40a9fa06ce81b4c291',
            'dormant control manifest differs')
    manifest = load_json(raw)
    require(set(manifest) == {'format', 'version', 'scope', 'archives'}
            and manifest['format'] == 'qleisli.dormant-controls-retention'
            and type(manifest['version']) is int and manifest['version'] == 1,
            'unknown dormant control retention format')
    rows = manifest['archives']
    require(type(rows) is list and len(rows) == 1
            and rows[0]['id'] == 'first-controls'
            and rows[0]['file_count'] == 40 and rows[0]['expanded_bytes'] == 635383,
            'complete control packet count differs')
    check_signature_tree(study, ['first-controls.tar.gz', 'packets.json', 'README.md'])
    files = read_archive(rows[0], study)
    plan, observed = (load_json(files[name]) for name in ('first-plan.json', 'first-observations.json'))
    head = '739c24860698234c5489941f8c55447535d2b793'
    cli = 'a94f242cb191f31fd6b7fb35ec71c8e607d5f68d5fec89107d1edc8855389f45'
    cli_path = '/Users/masa/git/Qleisli/target/debug/qleisli'
    kernel_path = '/Users/masa/git/Qleisli/lean-kernel/.lake/build/bin/qleisli-kernel'
    require(plan['execution'] == 'not run' and plan['build_attestation'] is False
            and observed['build_attestation'] is False and 'no external model or blind benchmark' in plan['kind']
            and observed['all_planned_cases_observed'] is True,
            'control predictions or observed scope differ')
    for suffix in ('_before', '_after'):
        require(observed['observed_head' + suffix] == head
                and observed['cli_sha256' + suffix] == cli
                and observed['kernel_sha256' + suffix] == KERNEL_SHA,
                'control observed binary or HEAD identity differs')
    for flag in ('inputs_stable', 'scoped_rust_stable', 'scoped_rust_match_first_snapshots',
                 'prior_evidence_unchanged'):
        require(observed[flag] is True, 'control capture input window differs')
    scope = plan['scoped_rust_first_inputs']
    require(len(scope) == 17 and scope == observed['scoped_rust_before'] == observed['scoped_rust_after'],
            'control original Rust scope differs')
    for name, digest in scope.items():
        require(sha(files['first-rust/' + local_name(name)]) == digest,
                'control first Rust snapshot differs')
    inputs = {name: sha(data) for name, data in files.items()
              if name == 'first-plan.json' or name.startswith('first-rust/')
              or name.endswith(('/main.qli', '/Qargo.toml'))}
    require(inputs == observed['inputs_before'] == observed['inputs_after'],
            'complete original control input window differs')
    cases = {'zero_scalar_ctrl_then_unbound': (0, 19, 1),
             'zero_closed_hold_ctrl_then_unbound': (0, 21, 1),
             'zero_mixed_owner_forest': (0, 20, 2),
             'one_bit_unused_flip_ctrl': (1, 19, 1),
             'one_bit_direct_flip_ctrl': (1, None, None)}
    require(list(plan['cases']) == list(cases)
            and [o['case'] for o in observed['observations']] == list(cases),
            'control case order differs')
    for observation in observed['observations']:
        case = observation['case']
        qubits, decisions, roots = cases[case]
        prediction = plan['cases'][case]
        expected_identity = dict(head=head, cli=cli, kernel=KERNEL_SHA, scoped_rust=scope,
                                 source=sha(files[case + '/main.qli']),
                                 manifest=sha(files[case + '/Qargo.toml']))
        require(observation['identity_before'] == observation['identity_after'] == expected_identity
                and observation['argv'] == [cli_path, 'check', rows[0]['original_directory'] + '/' + case]
                and observation['environment_override'] == {'QLEISLI_KERNEL': kernel_path}
                and observation['build_attestation'] is False,
                'control per-command original association differs')
        for flag in ('head_stable_during_case', 'cli_stable_during_case', 'kernel_stable_during_case',
                     'source_stable_during_case', 'scoped_rust_stable_during_case'):
            require(observation[flag] is True, 'control per-command stability differs')
        require(type(prediction['qubits']) is int and prediction['qubits'] == qubits
                and prediction['source_sha256'] == expected_identity['source']
                and prediction['manifest_sha256'] == expected_identity['manifest']
                and tomllib.loads(files[case + '/Qargo.toml'].decode()) ==
                {'schema-version': 2, 'qrate': {'edition': '2026'}}, 'control source identity differs')
        refused = decisions is None
        require(type(observation['exit_code']) is int and observation['exit_code'] == int(refused),
                'original control outcome differs')
        for stream in ('stdout', 'stderr'):
            name = case + '.first.' + stream + '.txt'
            require(observation[stream] == name and observation[stream + '_sha256'] == sha(files[name]),
                    'control complete stream association differs')
        stdout, stderr = (files[observation[k]].decode() for k in ('stdout', 'stderr'))
        if refused:
            require(stdout == '' and ':3:37: contract:' in stderr
                    and 'ctrl requires computational-basis sector preservation' in stderr
                    and 'phase kickback is permitted' in stderr, 'original control refusal differs')
        else:
            require(stderr == '' and stdout.splitlines() == [
                'checked source: ' + rows[0]['original_directory'] + '/' + case,
                'native checks: IR structure, ownership, interface, classical scope and '
                f'decoded execution view; {roots} concrete local roots, 9 bundled roots',
                'checker: ' + kernel_path, 'checker identity: unpinned',
                f'native decisions: {decisions}; independent requests checked: 0',
                'entry: absent; entry request checked: not applicable',
                'source preservation: not proved'], 'original control native scope differs')
    prior_study = ROOT / 'tests/fixtures/authoring_sessions/dormant-contracts-v030'
    prior_manifest = read_file(prior_study / 'packets.json', 32 * 1024, prior_study)
    require(sha(prior_manifest) == '43bc5db07379ac2d87fe2d9c5d95a58ae98eedd42c5ac0f1d3ed1f684ca8bd6c',
            'prior Meaning manifest differs')
    prior_rows = load_json(prior_manifest)['archives']
    prior = {PurePosixPath(row['original_directory']).name:
             {name: sha(data) for name, data in read_archive(row, prior_study).items()}
             for row in prior_rows}
    require(prior == plan['prior_evidence_hashes_before'] == observed['prior_evidence_hashes_before']
            == observed['prior_evidence_hashes_after'], 'control study rewrote prior Meaning evidence')
    note = ' '.join(read_file(study / 'README.md', 16 * 1024, study).decode().split())
    for disclosure in ('informed study is not a blind benchmark',
                       'not a clean commit-to-binary build attestation',
                       'reader never executes recorded commands or source',
                       'not complete', '40 original files / 635,383'):
        require(disclosure in note, 'missing control study disclosure: ' + disclosure)
    print('Dormant control first history: 40 unchanged files / 635,383 bytes; '
          'four accepts (including the one-bit dormant gap), one direct sector refusal. '
          'Zero-width controls do not prove one-bit refusal. No command executed.')


if __name__ == '__main__':
    main()
