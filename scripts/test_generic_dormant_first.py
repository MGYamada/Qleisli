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
    check_dormant_control_owner_order_first()
    check_general_static_runtime_first()
    check_runtime_transforms_first()
    check_derived_phase_qft_first()
    check_computed_preparation_first()
    check_zero_basis_first()
    check_computed_long_leaf_first()


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


def check_dormant_control_owner_order_first():
    """Read complete mixed-owner history as inert data, including its observer."""
    study = ROOT / 'tests/fixtures/authoring_sessions/dormant-control-owner-order-v030'
    require(study.is_dir() and not study.is_symlink()
            and study.resolve().is_relative_to(ROOT.resolve()), 'nonlocal owner-order study')
    raw = read_file(study / 'packets.json', 32 * 1024, study)
    require(sha(raw) == '77f435e051719e69d5bdc0f6c6d6963492b678c9437e867179c265d57901b398',
            'owner-order manifest differs')
    manifest = load_json(raw)
    require(set(manifest) == {'format', 'version', 'scope', 'archives'}
            and manifest['format'] == 'qleisli.dormant-control-owner-order-retention'
            and type(manifest['version']) is int and manifest['version'] == 1,
            'unknown owner-order retention format')
    rows = manifest['archives']
    original = '/private/tmp/qleisli-generic-plan-validation-ji3399kg/controls-mixed-owner-baseline'
    require(type(rows) is list and len(rows) == 1
            and rows[0]['id'] == 'first-owner-order'
            and rows[0]['original_directory'] == original
            and rows[0]['file_count'] == 11 and rows[0]['expanded_bytes'] == 6758,
            'complete owner-order packet count differs')
    check_signature_tree(study, ['first-owner-order.tar.gz', 'packets.json', 'README.md'])
    files = read_archive(rows[0], study)
    cases = ('empty_ctrl', 'bit_ctrl')
    require(set(files) == {'capture.py', 'plan.json', 'observations.json'}
            | {case + '/' + name for case in cases for name in ('main.qli', 'Qargo.toml')}
            | {case + '.' + stream + '.txt' for case in cases for stream in ('stdout', 'stderr')},
            'complete owner-order file association differs')
    plan, observed = (load_json(files[name]) for name in ('plan.json', 'observations.json'))
    head = '410a50dc0ae2a4179279e75d3c4ea9aad0422ca2'
    cli_path = '/Users/masa/git/Qleisli/target/debug/qleisli'
    kernel_path = '/Users/masa/git/Qleisli/lean-kernel/.lake/build/bin/qleisli-kernel'
    executables = {cli_path: '5f08a1b8b8e3836954bfb267a94c66757055485cd1c653c881db1c6cae1ca88f',
                   kernel_path: KERNEL_SHA}
    require(set(plan) == {'kind', 'before_control_cli', 'predictions', 'limits',
                         'cli_build_attestation', 'provenance', 'head_before',
                         'executables_before', 'driver_sha256'}
            and plan['kind'] == 'informed one-bit whole-owner study'
            and plan['before_control_cli'] is True and plan['cli_build_attestation'] is False
            and plan['head_before'] == head and plan['executables_before'] == executables
            and plan['limits'] == 'one physical qubit; no maximum-size case; no run/sampling'
            and plan['provenance'] == 'Existing separately identified CLI; observed Git HEAD is '
            'not a binary build attestation. Concurrent checkout integration may change Git/source state.'
            and plan['driver_sha256'] == sha(files['capture.py'])
            == '6af3850e9f69aa492dcde9292556447715338193cc068df96fa333165652eb93',
            'owner-order first provenance or observer differs')
    require(plan['predictions'] == {
                'empty_ctrl': 'accept; exact zero-width owner remains present',
                'bit_ctrl': 'must refuse; X changes the sole physical Ctrl axis'}
            and list(plan['predictions']) == list(cases),
            'owner-order independent predictions differ')
    require(set(observed) == {'observations', 'head_after', 'executables_after', 'executables_stable'}
            and observed['head_after'] == head and observed['executables_after'] == executables
            and observed['executables_stable'] is True
            and type(observed['observations']) is list and len(observed['observations']) == 2
            and [item['case'] for item in observed['observations']] == list(cases),
            'owner-order observation identity or order differs')
    prefix = ('use std::quantum::x;\n'
              'unitary fn pair(a:Q<Unit>,b:Q<Bit>)->(Q<Unit>,Q<Bit>){(a,x(b))}\n'
              'unitary fn unused[const U:Op<Unit>](a:Q<Unit>,b:Q<Bit>)->(Q<Unit>,Q<Bit>)\n'
              'requires Applicable(U){')
    for observation in observed['observations']:
        case = observation['case']
        require(set(observation) == {'case', 'argv', 'exit_code', 'source_sha256',
                                    'stdout_sha256', 'stderr_sha256'}
                and observation['argv'] == [cli_path, 'check', original + '/' + case,
                                            '--lean-kernel=' + kernel_path]
                and type(observation['exit_code']) is int and observation['exit_code'] == 0,
                'owner-order original command or outcome differs')
        access = 'ctrl a,excl b' if case == 'empty_ctrl' else 'excl a,ctrl b'
        require(files[case + '/main.qli'].decode() == prefix + 'pair(' + access + ');(U(a),b)}\n'
                and observation['source_sha256'] == sha(files[case + '/main.qli'])
                and tomllib.loads(files[case + '/Qargo.toml'].decode()) ==
                {'schema-version': 2, 'qrate': {'edition': '2026'}},
                'owner-order original source or schema differs')
        for stream in ('stdout', 'stderr'):
            require(observation[stream + '_sha256'] == sha(files[case + '.' + stream + '.txt']),
                    'owner-order complete original stream association differs')
        require(files[case + '.stderr.txt'] == b''
                and files[case + '.stdout.txt'].decode().splitlines() == [
                    'checked source: ' + original + '/' + case,
                    'native checks: IR structure, ownership, interface, classical scope and '
                    'decoded execution view; 1 concrete local roots, 9 bundled roots',
                    'checker: ' + kernel_path, 'checker identity: unpinned',
                    'native decisions: 19; independent requests checked: 0',
                    'entry: absent; entry request checked: not applicable',
                    'source preservation: not proved'],
                'owner-order first actual native scope differs')
    note = ' '.join(read_file(study / 'README.md', 16 * 1024, study).decode().split())
    for disclosure in ('informed study is not a blind benchmark',
                       'Both first checks actually accepted',
                       'Predictions are requirements, not observed successes',
                       'Capture occurred during a dirty cherry-pick integration',
                       'not a clean commit-to-binary build attestation',
                       '11 original files / 6,758 bytes',
                       'reader never executes recorded commands or source',
                       'never extracts records to the filesystem',
                       'does not complete'):
        require(disclosure in note, 'missing owner-order disclosure: ' + disclosure)
    print('Dormant control owner-order history: 11 unchanged files / 6,758 bytes; '
          'two accepts, including the intended physical-axis-zero refusal. '
          'One physical qubit, two logical owners. No command executed.')


def check_general_static_runtime_first():
    """Read four complete bounded histories; archived observer code stays inert."""
    study = ROOT / 'tests/fixtures/authoring_sessions/general-static-runtime-v030'
    require(study.is_dir() and not study.is_symlink()
            and study.resolve().is_relative_to(ROOT.resolve()), 'nonlocal static study')
    raw = read_file(study / 'packets.json', 32 * 1024, study)
    require(sha(raw) == 'd08bf54b8d108ca8b812ec8a4d7f9c262319aa309fc4cddb682e9b1ab01f72fb',
            'general-static manifest differs')
    manifest = load_json(raw)
    require(set(manifest) == {'format', 'version', 'scope', 'archives'}
            and manifest['format'] == 'qleisli.general-static-runtime-retention'
            and type(manifest['version']) is int and manifest['version'] == 1,
            'unknown general-static retention format')
    rows = manifest['archives']
    require([(row['id'], row['file_count'], row['expanded_bytes']) for row in rows] == [
                ('general', 61, 172127), ('primitive-control', 19, 525886),
                ('derived-phase', 15, 10962), ('finite-primitives', 19, 13639)]
            and sum(row['file_count'] for row in rows) == 114
            and sum(row['expanded_bytes'] for row in rows) == 722614
            and sum(row['archive_bytes'] for row in rows) <= MAX_STORED,
            'complete general-static packet counts differ')
    check_signature_tree(study, [row['archive'] for row in rows] + ['packets.json', 'README.md'])
    packets = {row['id']: read_archive(row, study) for row in rows}
    originals = {row['id']: row['original_directory'] for row in rows}
    head = '460f72e019885bd859686b6f4a8b265b40ab36fd'
    cli_path = '/Users/masa/git/Qleisli/target/debug/qleisli'
    kernel_path = '/Users/masa/git/Qleisli/lean-kernel/.lake/build/bin/qleisli-kernel'
    old_cli = '0cc0017310561f75f95716603a293065797e370e2be901c26f03aad2f9ae2312'
    new_cli = 'd2ffe826ad0d219dda9e45858d0aa11598945b23c9752848e5dae52f037bfd1c'
    for files in packets.values():
        for name, data in files.items():
            if name.endswith('/Qargo.toml'):
                require(tomllib.loads(data.decode()) ==
                        {'schema-version': 2, 'qrate': {'edition': '2026'}},
                        'original static-study edition differs')

    files = packets['general']
    inventory = load_json(files['evidence-inventory.json'])
    expected = {name: dict(sha256=sha(data), bytes=len(data)) for name, data in files.items()
                if name != 'evidence-inventory.json'}
    require(inventory['files'] == expected and inventory['files_excluding_inventory'] == 60
            and inventory['bytes_excluding_inventory'] == 162436,
            'complete original general-study inventory differs')
    for group, count, driver, manifest_name in [
        ('first', 10, 'observe_first.py', 'first-manifest.json'),
        ('repairs', 2, 'observe_repairs.py', 'repair-manifest.json'),
    ]:
        plan = load_json(files[manifest_name])
        observed = load_json(files['observations-' + group + '/observations.json'])
        projects = plan['projects']
        require(len(projects) == count and len(observed['observations']) == count
                and observed['driver_sha256'] == sha(files[driver])
                and observed['first_manifest_sha256'] == sha(files[manifest_name])
                and [row['name'] for row in observed['observations']] ==
                [project['name'] for project in projects], 'general observation order differs')
        window = load_json(files['observations-' + group + '/before.json'])
        state = {key: value for key, value in window.items() if key != 'utc'}
        require(state['head'] == head and state['status'] == ''
                and state['cli_sha256'] == old_cli and state['kernel_sha256'] == KERNEL_SHA
                and len(state['source_sha256']) == 33
                and all(HEX.fullmatch(value) for value in state['source_sha256'].values())
                and datetime.fromisoformat(plan['created_utc']) <= datetime.fromisoformat(window['utc']),
                'general original snapshot or prediction ordering differs')
        after = load_json(files['observations-' + group + '/after.json'])
        require({key: value for key, value in after.items() if key != 'utc'} == state,
                'general complete source/executable window differs')
        for project, observation in zip(projects, observed['observations']):
            case = project['name']
            require(project['prediction'] and all(sha(files[name]) == digest
                    for name, digest in project['files'].items()), 'general first source differs')
            require(observation['argv'] == [cli_path, 'check', originals['general'] + '/' + group + '/' + case,
                                            '--format=json', '--lean-kernel=' + kernel_path]
                    and observation['cli_identity_stable'] is True
                    and observation['kernel_identity_stable'] is True
                    and observation['source_identity_stable'] is True,
                    'general original command or identity differs')
            for snapshot in (observation['before'], observation['after']):
                require({key: value for key, value in snapshot.items() if key != 'utc'} == state,
                        'general per-command source window differs')
            for stream in ('stdout', 'stderr'):
                record = observation[stream]
                data = files['observations-' + group + '/' + record['path']]
                require(record['sha256'] == sha(data) and record['bytes'] == len(data),
                        'general complete stream association differs')
            require(files['observations-' + group + '/' + case + '.stderr.txt'] == b'',
                    'general first stderr differs')
            result = load_json(files['observations-' + group + '/' + case + '.stdout.txt'])
            if case == 'closed_unit_control':
                require(observation['exit_code'] == 0 and result['diagnostics'] == []
                        and result['result']['native_decisions'] ==
                        {'count': 20, 'requests_checked': 0, 'complete': True}
                        and result['result']['source_preservation_verified'] is False,
                        'general control native scope differs')
            else:
                code = 'type_mismatch' if group == 'first' and case.startswith('basis_') else 'unsupported'
                require(observation['exit_code'] == 1 and result['result'] is None
                        and len(result['diagnostics']) == 1
                        and result['diagnostics'][0]['code'] == code,
                        'general first refusal category differs')
                if code == 'type_mismatch':
                    require('use type(T)' in result['diagnostics'][0]['message'],
                            'original Basis wrapper mistake was hidden')
    for case, basis in [('basis_unit_identity', 'Unit'), ('basis_bit_identity', 'Bit')]:
        require(files['repairs/' + case + '/main.qli'] ==
                files['first/' + case + '/main.qli'].replace(
                    ('identity[' + basis + ']').encode(), ('identity[type(' + basis + ')]').encode()),
                'Basis repair changed more than its original argument wrapper')

    files = packets['primitive-control']
    plan, observed = (load_json(files[name]) for name in ('predictions-and-inputs.json', 'observations.json'))
    before = plan['before']
    require(before['head'] == head and before['branch'] == 'codex/beta-dormant-runtime'
            and before['git_status_porcelain'] == '' and before['cli_sha256'] == old_cli
            and before['kernel_sha256'] == KERNEL_SHA and len(before['rust_source_sha256']) == 409
            and all(HEX.fullmatch(value) for value in before['rust_source_sha256'].values())
            and observed['after'] == before and observed['stable_total_window'] is True,
            'primitive-control complete original window differs')
    cases = [('phase-unused', 0, 18, 0), ('phase-direct', 0, 20, 1),
             ('x-unused', 0, 18, 0), ('x-direct', 1, None, None)]
    require([case['name'] for case in plan['cases']] == [case[0] for case in cases]
            and [row['name'] for row in observed['observations']] == [case[0] for case in cases],
            'primitive-control original order differs')
    for prediction, observation, (case, exit_code, decisions, requests) in zip(
            plan['cases'], observed['observations'], cases):
        require(prediction['prediction'] and prediction['main_sha256'] == sha(files[case + '/main.qli'])
                and prediction['manifest_sha256'] == sha(files[case + '/Qargo.toml'])
                and observation['before'] == observation['after'] == before
                and observation['stable_window'] is True and observation['exit'] == exit_code
                and observation['argv'] == [cli_path, 'check', originals['primitive-control'] + '/' + case,
                                           '--format=json', '--lean-kernel=' + kernel_path],
                'primitive-control original source/command binding differs')
        for stream in ('stdout', 'stderr'):
            require(observation[stream + '_sha256'] == sha(files[case + '.' + stream]),
                    'primitive-control full stream differs')
        require(files[case + '.stderr'] == b'', 'primitive-control stderr differs')
        result = load_json(files[case + '.stdout'])
        if decisions is None:
            require(result['diagnostics'][0]['code'] == 'contract' and result['result'] is None,
                    'direct X sector refusal differs')
        else:
            require(result['diagnostics'] == [] and result['result']['native_decisions'] ==
                    {'count': decisions, 'requests_checked': requests, 'complete': True}
                    and result['result']['source_preservation_verified'] is False,
                    'dormant primitive gap incorrectly gained a request or preservation claim')

    for packet_id, cli, cases in [
        ('derived-phase', old_cli, [('final_unqualified', 1, 'unknown_name: unresolved function global_phase_eighth'),
                                  ('legacy_exact_t', 0, ''),
                                  ('global_scalar_is_not_t', 1, 'contract: exact equation U E_in = E_out u does not hold')]),
        ('finite-primitives', new_cli, [(case, 1, 'unsupported: ') for case in
                                      ('one_axis_roundtrip', 'word_constructor', 'exact_phase', 'unsupported_phase')]),
    ]:
        files = packets[packet_id]
        plan, observed = (load_json(files[name]) for name in ('plan.json', 'observations.json'))
        identities = {cli_path: cli, kernel_path: KERNEL_SHA}
        require(plan['build_attestation'] is False and plan['execution'] == 'not run'
                and plan['head_before'] == observed['head_after'] == head
                and plan['dirty_before'] == observed['dirty_after'] and plan['dirty_before']
                and plan['executables_before'] == observed['executables_after'] == identities
                and observed['executables_stable'] is True and observed['source_bytes_stable'] is True
                and plan['driver_sha256'] == sha(files['capture.py'])
                and list(plan['cases']) == [case[0] for case in cases]
                and [row['case'] for row in observed['observations']] == [case[0] for case in cases],
                'derived/finite original executable or dirty-source identity differs')
        for observation, (case, exit_code, message) in zip(observed['observations'], cases):
            require(plan['predictions'][case] and observation['exit_code'] == exit_code
                    and plan['cases'][case]['source_sha256'] == observation['source_sha256_after']
                    == sha(files[case + '/main.qli'])
                    and plan['cases'][case]['manifest_sha256'] == sha(files[case + '/Qargo.toml'])
                    and observation['argv'] == [cli_path, 'check', originals[packet_id] + '/' + case,
                                                '--lean-kernel=' + kernel_path],
                    'derived/finite source/command binding differs')
            for stream in ('stdout', 'stderr'):
                require(observation[stream]['sha256'] == sha(files[observation[stream]['path']]),
                        'derived/finite full stream association differs')
            stdout, stderr = (files[observation[stream]['path']].decode() for stream in ('stdout', 'stderr'))
            if exit_code:
                require(stdout == '' and message in stderr, 'original derived/finite refusal differs')
                if packet_id == 'finite-primitives':
                    require('finite lowering profile' in stderr, 'profile refusal gained downstream evidence')
            else:
                require(stderr == '' and 'native decisions: 23; independent requests checked: 0' in stdout
                        and 'source preservation: not proved' in stdout, 'derived T first native scope differs')
    note = ' '.join(read_file(study / 'README.md', 16 * 1024, study).decode().split())
    for disclosure in ('informed studies are not blind benchmarks', '114 original files / 722,614 bytes',
                       'not a clean commit-to-binary build attestation', 'reader never executes',
                       'never extracts', 'does not complete', '409 Rust source hashes'):
        require(disclosure in note, 'missing general-static disclosure: ' + disclosure)
    print('General-static runtime history: four packets / 114 unchanged files / 722,614 bytes; '
          '23 original checks, 5 accepts / 18 refusals. Basis mistakes and dormant X gap retained. '
          'No recorded command, source or observer executed.')


def check_runtime_transforms_first():
    """Read complete first/translation histories without replaying anything."""
    study = ROOT / 'tests/fixtures/authoring_sessions/runtime-transforms-v030'
    require(study.is_dir() and not study.is_symlink()
            and study.resolve().is_relative_to(ROOT.resolve()), 'nonlocal transform study')
    raw = read_file(study / 'packets.json', 32 * 1024, study)
    require(sha(raw) == '136b45a0624d17074de276e29ffed3a4c901969178675a349ec796fe47b434d0',
            'runtime-transform manifest differs')
    manifest = load_json(raw)
    require(set(manifest) == {'format', 'version', 'scope', 'archives'}
            and manifest['format'] == 'qleisli.runtime-transforms-retention'
            and type(manifest['version']) is int and manifest['version'] == 1,
            'unknown runtime-transform retention format')
    rows = manifest['archives']
    require([(row['id'], row['file_count'], row['expanded_bytes']) for row in rows] ==
            [('first', 36, 36763), ('translations-01', 35, 26862)]
            and sum(row['file_count'] for row in rows) <= MAX_MEMBERS
            and sum(row['expanded_bytes'] for row in rows) <= MAX_CONTENT
            and sum(row['archive_bytes'] for row in rows) <= MAX_STORED,
            'complete transform packet counts or fixed bounds differ')
    check_signature_tree(study, [row['archive'] for row in rows] + ['packets.json', 'README.md'])
    packets = {row['id']: read_archive(row, study) for row in rows}
    originals = {row['id']: row['original_directory'] for row in rows}
    cases = ['generic_classical', 'inactive_self', 'specialized_group_control',
             'group_unit_inverse', 'symbolic_phase_inverse',
             'specialized_group_0', 'specialized_group_1', 'specialized_group_2']
    cli_path = '/Users/masa/git/Qleisli/target/debug/qleisli'
    kernel_path = '/Users/masa/git/Qleisli/lean-kernel/.lake/build/bin/qleisli-kernel'
    identities = {cli_path: 'ee67c0cb27748de6f7b13a4807eaf7ba8d96552816f5f0f23bc9cc1f0daf9c5b',
                  kernel_path: KERNEL_SHA}
    predictions = None
    for packet_id in ['first', 'translations-01']:
        files = packets[packet_id]
        plan, observed = (load_json(files[name]) for name in ['plan.json', 'observations.json'])
        expected = cases if packet_id == 'first' else cases[1:] + ['coherent_scalar_group']
        require(plan['head_before'] == observed['head_after'] ==
                '460f72e019885bd859686b6f4a8b265b40ab36fd'
                and type(plan['dirty_before']) is str and plan['dirty_before']
                and plan['dirty_before'] == observed['dirty_after']
                and plan['executables_before'] == observed['executables_after'] == identities
                and observed['executables_stable'] is True
                and observed['source_bytes_stable'] is True
                and plan['build_attestation'] is False and plan['execution'] == 'not run'
                and plan['driver_sha256'] == sha(files['capture.py'])
                and list(plan['cases']) == expected
                and [row['case'] for row in observed['observations']] == expected,
                'transform original source/observer/executable window differs')
        if predictions is None:
            predictions = plan['predictions']
            require(list(predictions) == cases and all(predictions.values()),
                    'first transform predictions differ')
            require('original-test-source.rs' in files
                    and not any(name.startswith('translations-01/') for name in files),
                    'first packet snapshot or disclosed subtree split differs')
        else:
            require(plan['predictions'] == predictions
                    and 'coherent_scalar_group' not in predictions,
                    'translation stale/missing predictions were rewritten')
        for row in observed['observations']:
            case = row['case']
            require(row['exit_code'] == 1
                    and row['argv'] == [cli_path, 'check', originals[packet_id] + '/' + case,
                                       '--lean-kernel=' + kernel_path]
                    and plan['cases'][case]['source_sha256'] == row['source_sha256_after']
                    == sha(files[case + '/main.qli'])
                    and plan['cases'][case]['manifest_sha256'] == sha(files[case + '/Qargo.toml'])
                    and tomllib.loads(files[case + '/Qargo.toml'].decode()) ==
                    {'schema-version': 2, 'qrate': {'edition': '2026'}},
                    'transform source/manifest/command association differs')
            for stream in ['stdout', 'stderr']:
                require(row[stream]['path'] == case + '.' + stream + '.txt'
                        and row[stream]['sha256'] == sha(files[row[stream]['path']]),
                        'transform complete stream association differs')
            require(files[row['stdout']['path']] == b'', 'refused transform gained output')
            code = ('parse' if case in ['generic_classical', 'group_unit_inverse',
                                       'specialized_group_0', 'specialized_group_1',
                                       'specialized_group_2'] else
                    'type_mismatch' if case == 'symbolic_phase_inverse' else 'unsupported')
            if packet_id == 'translations-01':
                code = 'unsupported'
            require((': ' + code + ': ') in files[row['stderr']['path']].decode(),
                    'original transform refusal category differs')
    note = ' '.join(read_file(study / 'README.md', 16 * 1024, study).decode().split())
    for disclosure in ['informed studies, not blind benchmarks', 'All 16 baseline invocations refused',
                       'stale generic-classical entry', 'no dedicated coherent-scalar prediction',
                       '71 unchanged files / 63,625 expanded bytes',
                       'not a clean commit-to-binary build attestation',
                       'never executes recorded commands', 'never extracts',
                       'does not establish current implementation correctness']:
        require(disclosure in note, 'missing runtime-transform disclosure: ' + disclosure)
    print('Runtime-transform history: two packets / 71 unchanged files / 63,625 bytes; '
          '16 refused checks, original mistakes and stale predictions retained. '
          'No recorded command, source or observer executed.')


def check_derived_phase_qft_first():
    """Inspect reported observations and retained bytes; execute no observer."""
    study = ROOT / 'tests/fixtures/authoring_sessions/derived-phase-qft-v030'
    require(study.is_dir() and not study.is_symlink()
            and study.resolve().is_relative_to(ROOT.resolve()), 'nonlocal derived-phase study')
    raw = read_file(study / 'packets.json', 32 * 1024, study)
    require(sha(raw) == '0a83cdde1de1b5ffe278d94f5532ad0500834b6560b149f9a29fa91853a1a63e',
            'derived-phase manifest differs')
    manifest = load_json(raw)
    require(set(manifest) == {'format', 'version', 'scope', 'archives'}
            and manifest['format'] == 'qleisli.derived-phase-qft-retention'
            and type(manifest['version']) is int and manifest['version'] == 1,
            'unknown derived-phase retention format')
    rows = manifest['archives']
    require([(row['id'], row['file_count'], row['expanded_bytes']) for row in rows] ==
            [('first', 21, 11509), ('translations-01', 15, 9726)]
            and sum(row['file_count'] for row in rows) <= MAX_MEMBERS
            and sum(row['expanded_bytes'] for row in rows) <= MAX_CONTENT
            and sum(row['archive_bytes'] for row in rows) <= MAX_STORED,
            'complete derived-phase packet counts or fixed bounds differ')
    check_signature_tree(study, [row['archive'] for row in rows] + ['packets.json', 'README.md'])
    packets = {row['id']: read_archive(row, study) for row in rows}
    original = '/private/tmp/qleisli-derived-phase-qft-first-9_2_729h'
    require([row['original_directory'] for row in rows] ==
            [original, original + '/translations-01'], 'derived-phase original locations differ')
    cli_path = '/Users/masa/git/Qleisli/target/debug/qleisli'
    kernel_path = '/Users/masa/git/Qleisli/lean-kernel/.lake/build/bin/qleisli-kernel'
    cli = 'd20fbb4505ed3c11997929b487404ea225395f993ea53bb30183361dcbda6ed9'
    first = load_json(packets['first']['capture.json'])
    translated = load_json(packets['translations-01']['capture.json'])
    require(set(first) == {'head', 'cli_sha256', 'kernel_sha256', 'scope', 'records',
                           'cli_stable', 'kernel_stable'}
            and first['head'] == '460f72e019885bd859686b6f4a8b265b40ab36fd'
            and first['scope'] == 'first desired source and actual diagnostics; dirty source, '
                                  'no clean build attestation; only 2/3-bit executions'
            and first['cli_stable'] is True and first['kernel_stable'] is True
            and set(translated) == {'records', 'cli_sha256', 'kernel_sha256'}
            and first['cli_sha256'] == translated['cli_sha256'] == cli
            and first['kernel_sha256'] == translated['kernel_sha256'] == KERNEL_SHA,
            'derived-phase recorded identity or capture limitations differ')
    for packet_id, capture, cases in [
        ('first', first, ['qft2', 'qft3', 'controlled_phase']),
        ('translations-01', translated, ['qft2', 'qft3']),
    ]:
        files = packets[packet_id]
        expected = {'capture.json'}
        for case in cases:
            expected.update(case + '/' + name for name in ['Qargo.toml', 'main.qli'])
            if case != 'controlled_phase':
                expected.add(case + '/kernel.qli')
            expected.update(case + '.' + command + '.' + stream
                            for command in ['check', 'run'] for stream in ['stdout', 'stderr'])
            require(tomllib.loads(files[case + '/Qargo.toml'].decode()) ==
                    {'schema-version': 2, 'qrate': {'edition': '2026'}},
                    'derived-phase source manifest differs')
        require(set(files) == expected, 'missing or extra derived-phase original file')
        require([(row['case'], row['argv'][1]) for row in capture['records']] ==
                [(case, command) for case in cases for command in ['check', 'run']],
                'derived-phase original observation order differs')
        for row in capture['records']:
            case, command = row['case'], row['argv'][1]
            fields = {'case', 'argv', 'exit_code', 'stdout', 'stderr'}
            if packet_id == 'translations-01':
                fields.add('command')
                require(row['command'] == command, 'translation command identity differs')
            directory = original + ('' if packet_id == 'first' else '/translations-01')
            require(set(row) == fields and row['argv'] ==
                    [cli_path, command, directory + '/' + case, '--format=json',
                     '--lean-kernel=' + kernel_path] and type(row['exit_code']) is int,
                    'derived-phase reported argv/source association differs')
            for stream in ['stdout', 'stderr']:
                require(type(row[stream]) is str and row[stream].encode() ==
                        files[case + '.' + command + '.' + stream],
                        'derived-phase full stream association differs')
            require(row['stderr'] == '', 'derived-phase stderr differs')
            result = load_json(row['stdout'])
            require(result['format'] == 'qleisli.result' and result['version'] == 1
                    and result['command'] == command, 'derived-phase result identity differs')
            refuses = packet_id == 'first' and case != 'controlled_phase'
            if refuses:
                diagnostic, = result['diagnostics']
                require(row['exit_code'] == 1 and result['outcome'] == 'error'
                        and result['result'] is None and diagnostic['code'] == 'type_mismatch'
                        and diagnostic['message'] ==
                        'expected a Basis argument; use type(T) for a concrete type'
                        and diagnostic['primary'] == {'path': 'kernel.qli', 'start': 436,
                            'end': 439, 'line': 11, 'column': 51}
                        and files[case + '/kernel.qli'][436:439] == b'Bit',
                        'first QFT Basis-wrapper refusal differs')
            else:
                require(row['exit_code'] == 0 and result['outcome'] == 'ok'
                        and result['diagnostics'] == [], 'derived-phase success observation differs')
                observed = result['result']
                if command == 'check':
                    decisions = {'controlled_phase': 171, 'qft2': 210, 'qft3': 224}[case]
                    require(observed['native_decisions'] == {'count': decisions,
                            'requests_checked': 0, 'complete': True}
                            and observed['checker_paths'] == [kernel_path]
                            and observed['checker_identity'] == 'unpinned'
                            and observed['entry'] == {'present': True, 'request_checked': False}
                            and observed['source_preservation_verified'] is False,
                            'derived-phase successful check scope differs')
                else:
                    distribution = observed['distribution']
                    width = 3 if case == 'qft3' else 2
                    outcomes = {tuple(item['bits']) for item in distribution}
                    require(len(distribution) == len(outcomes) == 2 ** width
                            and outcomes == {tuple(bool(n & (1 << k)) for k in range(width))
                                             for n in range(2 ** width)}
                            and all(all(type(bit) is bool for bit in item['bits'])
                                    and type(item['probability']) is float
                                    and math.isclose(item['probability'], 1 / 2 ** width,
                                                     rel_tol=0, abs_tol=1e-12)
                                    for item in distribution),
                            'derived-phase bounded numerical observation differs')
    for case in ['qft2', 'qft3']:
        for name in ['Qargo.toml', 'main.qli']:
            require(packets['first'][case + '/' + name] ==
                    packets['translations-01'][case + '/' + name],
                    'translation changed an unrelated source or manifest')
        source = packets['first'][case + '/kernel.qli']
        require(source.count(b'id[Bit]') == 1 and
                packets['translations-01'][case + '/kernel.qli'] ==
                source.replace(b'id[Bit]', b'id[type(Bit)]'),
                'separate original Basis-wrapper repair differs')
    note = ' '.join(read_file(study / 'README.md', 16 * 1024, study).decode().split())
    for disclosure in ['informed authoring study, not a blind benchmark',
                       '36 unchanged files / 21,235 expanded bytes',
                       'first driver was Python stdin; no pre-invocation script was saved',
                       'do not independently authenticate the invoking observer or the executed argv',
                       'no separate HEAD or stability window',
                       'Neither packet records a complete compiler-source freeze or pre/post source-byte hashes',
                       'not a clean commit-to-binary build attestation',
                       'never executes recorded commands', 'never extracts',
                       'does not establish current implementation correctness']:
        require(disclosure in note, 'missing derived-phase disclosure: ' + disclosure)
    print('Derived-phase/QFT history: two packets / 36 unchanged files / 21,235 bytes; '
          '10 invocations, 6 accepts / 4 original Basis-wrapper refusals; '
          'successful check reports have no independent requests. '
          'No recorded source, command or observer executed.')


def check_computed_preparation_first():
    """Read complete original histories without executing their saved observers."""
    study = ROOT / 'tests/fixtures/authoring_sessions/computed-preparation-v030'
    require(study.is_dir() and not study.is_symlink()
            and study.resolve().is_relative_to(ROOT.resolve()), 'nonlocal computed study')
    raw = read_file(study / 'packets.json', 32 * 1024, study)
    require(sha(raw) == '68b20824a886e67a2e5a1d298ac97f326a3dffe4af0850bdeae19b4c9ea140ad',
            'computed/preparation retention manifest differs')
    manifest = load_json(raw)
    require(set(manifest) == {'format', 'version', 'scope', 'archives'}
            and manifest['format'] == 'qleisli.computed-preparation-retention'
            and type(manifest['version']) is int and manifest['version'] == 1,
            'unknown computed/preparation retention format')
    rows = manifest['archives']
    require(type(rows) is list and
            [(row['id'], row['file_count'], row['expanded_bytes']) for row in rows] == [
                ('computed-body', 54, 126471), ('derived-preparation', 22, 9050),
                ('canonical-length', 7, 68353)]
            and sum(row['archive_bytes'] for row in rows) <= MAX_STORED
            and sum(row['expanded_bytes'] for row in rows) == 203874,
            'complete computed/preparation packet counts or archive order differ')
    # Bounds remain per archive, just as in the 114-file general-static study.
    check_signature_tree(study, [row['archive'] for row in rows] + ['packets.json', 'README.md'])
    packets = {row['id']: read_archive(row, study) for row in rows}
    originals = {row['id']: row['original_directory'] for row in rows}
    head = '460f72e019885bd859686b6f4a8b265b40ab36fd'
    cli_path = '/Users/masa/git/Qleisli/target/debug/qleisli'
    kernel_path = '/Users/masa/git/Qleisli/lean-kernel/.lake/build/bin/qleisli-kernel'
    identities = {cli_path: 'd20fbb4505ed3c11997929b487404ea225395f993ea53bb30183361dcbda6ed9',
                  kernel_path: KERNEL_SHA}
    for files in packets.values():
        for name, data in files.items():
            if name.endswith('/Qargo.toml'):
                require(tomllib.loads(data.decode()) ==
                        {'schema-version': 2, 'qrate': {'edition': '2026'}},
                        'computed/preparation source edition differs')

    def window(plan, observed, count):
        require(plan['head_before'] == observed['head_after'] == head
                and plan['build_attestation'] is False and observed['build_attestation'] is False
                and plan['dirty_before'] == observed['dirty_after'] and plan['dirty_before']
                and plan['executables_before'] == observed['executables_after'] == identities
                and observed['executables_stable'] is True
                and observed['wip_sources_stable'] is True
                and plan['sources_before'] == observed['sources_after']
                and type(plan['sources_before']) is dict and len(plan['sources_before']) == count
                and all(local_name(name) and HEX.fullmatch(digest)
                        for name, digest in plan['sources_before'].items()),
                'saved computed source/executable window or no-attestation scope differs')

    def streams(files, observation):
        result = []
        for stream in ('stdout', 'stderr'):
            item = observation[stream]
            require(set(item) == {'path', 'sha256'} and item['sha256'] == sha(files[local_name(item['path'])]),
                    'complete computed stream association differs')
            result.append(files[item['path']].decode())
        return result

    files = packets['computed-body']
    cases = ['derived_z', 'derived_t', 'unrelated_z_wrapper', 'non_diagonal',
             'wrong_scalar_meaning', 'hidden_reference']
    first = load_json(files['plan.json'])
    repair = load_json(files['repair-plan.json'])
    require(first['classification'] == 'informed checking study, at most two allocated quantum wires; no execution'
            and repair['kind'] == 'minimal first-source diagnostic repair'
            and repair['repair'] == 'rename parameterized quantum main declaration to subject; no body/contract change'
            and repair['first_plan_sha256'] == sha(files['plan.json'])
            and first['sources_before'] == repair['sources_before'],
            'computed first/repair lineage or classification differs')
    for prefix, plan_name, observed_name, driver in [
        ('', 'plan.json', 'observations.json', 'capture.py'),
        ('attempt-02/', 'repair-plan.json', 'repair-observations.json', 'capture-repair.py'),
    ]:
        plan, observed = load_json(files[plan_name]), load_json(files[observed_name])
        window(plan, observed, 201)
        require(plan['driver_sha256'] == sha(files[driver])
                and observed['original_sources_stable'] is True
                and list(plan['cases']) == cases
                and [item['case'] for item in observed['observations']] == cases,
                'computed original observer, case order or source stability differs')
        for observation in observed['observations']:
            case = observation['case']
            prediction = plan['cases'][case]
            source = files[prefix + case + '/main.qli']
            require(prediction['prediction'] == first['cases'][case]['prediction']
                    and prediction['source_sha256'] == observation['source_sha256_after'] == sha(source)
                    and prediction['manifest_sha256'] == sha(files[prefix + case + '/Qargo.toml'])
                    and type(observation['exit_code']) is int and observation['exit_code'] == 1
                    and observation['argv'] == [cli_path, 'check', originals['computed-body'] + '/' + prefix + case,
                                                '--lean-kernel=' + kernel_path],
                    'computed original source, prediction, argv or refusal differs')
            if prefix:
                original_source = files[case + '/main.qli']
                require(prediction['original_source_sha256'] == sha(original_source)
                        and source == original_source.replace(b'pub unitary fn main(', b'pub unitary fn subject(')
                        and files[prefix + case + '/Qargo.toml'] == files[case + '/Qargo.toml'],
                        'computed minimal repair changed a body, contract or original source')
            stdout, stderr = streams(files, observation)
            require(stdout == '' and stderr.startswith(originals['computed-body'] + '/' + prefix + case + '/main.qli:'),
                    'computed original refusal stream or source location differs')
            if case == 'hidden_reference':
                message = 'ownership: with_computed body cannot capture outer binding `r`'
            elif not prefix:
                message = 'invalid_entry: main must be an ordinary fn main() with a closed classical result'
            elif case == 'derived_t':
                message = 'ownership: with_computed must return its ancilla ownership'
            else:
                message = 'unsupported: with_computed currently accepts only identity and expanded Z/T gates'
            require(message in stderr, 'first entry mistake or repaired computed refusal was hidden')

    files = packets['derived-preparation']
    capture = load_json(files['capture.json'])
    require(set(capture) == {'cli_sha256', 'kernel_sha256', 'head', 'scope', 'records', 'cli_stable', 'kernel_stable'}
            and capture['cli_sha256'] == identities[cli_path] and capture['kernel_sha256'] == KERNEL_SHA
            and capture['head'] == head and capture['cli_stable'] is True and capture['kernel_stable'] is True
            and capture['scope'] == 'dirty source observation using existing executable; no full source freeze or clean build attestation; only zero/one/two-bit examples; Python stdin driver not saved',
            'preparation observed provenance or missing-driver disclosure differs')
    order = [(case, command) for case in ['reference_reset', 'empty_owner', 'false_pure_reset']
             for command in ['check', 'run']]
    require([(record['case'], record['argv'][1]) for record in capture['records']] == order
            and all(not name.endswith('.py') for name in files),
            'preparation command chronology or unsaved observer differs')
    kernel = files['reference_reset/kernel.qli']
    require(b'pub isometry fn init0()->Q<Bit>{basis unit(()) as () {0}}' in kernel
            and b'pub observe fn reset(q:Q<Bit>)->Q<Bit>{let outcome=measure_z(q);init0()}' in kernel
            and b'pub unitary fn empty()->Q<Bits<0>>' in kernel,
            'original derived preparation contracts differ')
    for record, (case, command) in zip(capture['records'], order):
        require(files[case + '/kernel.qli'] == kernel
                and record['argv'] == [cli_path, command, originals['derived-preparation'] + '/' + case,
                                       '--format=json', '--lean-kernel=' + kernel_path]
                and type(record['exit_code']) is int and record['exit_code'] == int(case == 'false_pure_reset')
                and record['stdout'].encode() == files[case + '.' + command + '.stdout']
                and record['stderr'].encode() == files[case + '.' + command + '.stderr'] == b'',
                'preparation original argv, complete streams or outcomes differ')
        response = load_json(record['stdout'])
        require(response['format'] == 'qleisli.result' and response['version'] == 1
                and response['command'] == command, 'preparation JSON report differs')
        if case == 'false_pure_reset':
            require(response['outcome'] == 'error' and response['result'] is None
                    and len(response['diagnostics']) == 1 and response['diagnostics'][0]['code'] == 'effect'
                    and 'body effect `Observe` exceeds asserted `Unitary` effect' in response['diagnostics'][0]['message'],
                    'false Unitary preparation refusal differs')
        elif command == 'check':
            result = response['result']
            require(response['outcome'] == 'ok' and response['diagnostics'] == []
                    and result['checker_paths'] == [kernel_path] and result['checker_identity'] == 'unpinned'
                    and result['native_decisions'] == {'count': 182 if case == 'reference_reset' else 168,
                                                     'requests_checked': 0, 'complete': True}
                    and result['entry'] == {'present': True, 'request_checked': False}
                    and result['concrete_ir_roots'] == {'local': 5, 'bundled': 19}
                    and result['source_preservation_verified'] is False,
                    'preparation successful native scope differs')
        else:
            distribution = response['result']['distribution']
            expected = {(False, False): 0.5, (True, False): 0.5} if case == 'reference_reset' else {(): 1.0}
            require(response['outcome'] == 'ok' and response['diagnostics'] == []
                    and len(distribution) == len(expected)
                    and {tuple(item['bits']) for item in distribution} == set(expected)
                    and all(all(type(bit) is bool for bit in item['bits'])
                            and type(item['probability']) in (int, float)
                            and math.isclose(item['probability'], expected[tuple(item['bits'])],
                                             rel_tol=0, abs_tol=1e-12) for item in distribution),
                    'preparation numerical observation differs')

    files = packets['canonical-length']
    plan, observed = load_json(files['plan.json']), load_json(files['observations.json'])
    window(plan, observed, 203)
    source = files['canonical-1025-t/main.qli']
    require(plan['driver_sha256'] == sha(files['capture.py'])
            and plan['source_sha256'] == observed['source_sha256_after'] == sha(source)
            and plan['manifest_sha256'] == sha(files['canonical-1025-t/Qargo.toml'])
            and source.count(b'let a=t(a);') == 1025 and b'use std::quantum::{t,init0}' in source
            and 'no independent request or new equation is claimed' in plan['prediction']
            and 'no execution' in plan['classification']
            and plan['argv'] == [cli_path, 'check', originals['canonical-length'] + '/canonical-1025-t',
                                  '--lean-kernel=' + kernel_path]
            and observed['exit_code'] == 0 and observed['original_source_stable'] is True,
            'canonical 1025-action original source, command or compatibility scope differs')
    stdout, stderr = streams(files, observed)
    require(stderr == '' and 'native decisions: 164; independent requests checked: 0' in stdout
            and 'entry request checked: false' in stdout and 'source preservation: not proved' in stdout,
            'canonical compatibility baseline gained an equation or preservation claim')
    note = ' '.join(read_file(study / 'README.md', 16 * 1024, study).decode().split())
    for disclosure in ('three separate informed studies, not blind benchmarks',
                       'all 54 original files', 'repairs never replace first bytes or predictions',
                       'Python stdin driver was not saved', 'source window',
                       'not a clean commit-to-binary build attestation',
                       '83 unchanged files / 203,874 expanded bytes',
                       'passive reader never executes', 'never extracts archive members',
                       'does not complete #369/#167'):
        require(disclosure in note, 'missing computed/preparation disclosure: ' + disclosure)
    print('Computed/preparation histories: three packets / 83 unchanged files / 203,874 bytes; '
          '19 invocations, 5 accepts / 14 refusals. Entry mistakes and repairs retained; '
          '1025-action acceptance is ordinary Raw checking only. No recorded code executed.')


def check_zero_basis_first():
    """Read first errors and separate wrappers as inert bytes, never replay."""
    study = ROOT / 'tests/fixtures/authoring_sessions/zero-basis-v030'
    require(study.is_dir() and not study.is_symlink()
            and study.resolve().is_relative_to(ROOT.resolve()), 'nonlocal zero-basis study')
    raw = read_file(study / 'packets.json', 32 * 1024, study)
    require(sha(raw) == '8375babb05f5c843cbbd8e2415dba3a7b499638e0edd649b47b0d7154f0d3114',
            'zero-basis manifest differs')
    manifest = load_json(raw)
    require(set(manifest) == {'format', 'version', 'scope', 'archives'}
            and manifest['format'] == 'qleisli.zero-basis-retention'
            and type(manifest['version']) is int and manifest['version'] == 1,
            'unknown zero-basis retention format')
    rows = manifest['archives']
    require([(row['id'], row['file_count'], row['expanded_bytes']) for row in rows] ==
            [('first', 37, 25685), ('translations-01', 19, 10666)]
            and sum(row['file_count'] for row in rows) <= MAX_MEMBERS
            and sum(row['expanded_bytes'] for row in rows) <= MAX_CONTENT
            and sum(row['archive_bytes'] for row in rows) <= MAX_STORED,
            'complete zero-basis counts or fixed reader bounds differ')
    check_signature_tree(study, [row['archive'] for row in rows] + ['packets.json', 'README.md'])
    packets = {row['id']: read_archive(row, study) for row in rows}
    original = '/private/tmp/qleisli-zero-basis-first-37g9fz7_'
    require([row['original_directory'] for row in rows] ==
            [original, original + '/translations-01'], 'zero-basis original locations differ')
    cases = ['prepare_zero', 'make_empty', 'consume_empty', 'phase_reference']
    cli = '/Users/masa/git/Qleisli/target/debug/qleisli'
    kernel = '/Users/masa/git/Qleisli/lean-kernel/.lake/build/bin/qleisli-kernel'
    identities = {cli: 'd20fbb4505ed3c11997929b487404ea225395f993ea53bb30183361dcbda6ed9',
                  kernel: KERNEL_SHA}
    for packet_id in ['first', 'translations-01']:
        files = packets[packet_id]
        plan, observed = (load_json(files[name]) for name in ['plan.json', 'observations.json'])
        require(plan['executables_before'] == observed['executables_after'] == identities
                and observed['executables_stable'] is True and plan['build_attestation'] is False
                and list(plan['cases']) == cases, 'zero-basis recorded source/executable identity differs')
        expected = {'plan.json', 'observations.json'}
        for case in cases:
            expected.update({case + '/main.qli', case + '/Qargo.toml'})
            require(plan['cases'][case]['source_sha256'] == sha(files[case + '/main.qli'])
                    and plan['cases'][case]['manifest_sha256'] == sha(files[case + '/Qargo.toml'])
                    and tomllib.loads(files[case + '/Qargo.toml'].decode()) ==
                    {'schema-version': 2, 'qrate': {'edition': '2026'}},
                    'zero-basis original source/edition association differs')
        if packet_id == 'first':
            expected.update({'design-review.md', 'design-review-update-01.md', 'summary.json'})
            require('capture.py' not in files and observed['first_sources_stable'] is True
                    and plan['full_build_source_binding'] is False
                    and plan['observed_head_before'] == observed['observed_head_after'] ==
                    {'head': '460f72e019885bd859686b6f4a8b265b40ab36fd',
                     'ref': 'refs/heads/codex/beta-dormant-runtime'}
                    and plan['source_window'] == observed['source_window_after']
                    and set(plan['source_window']) == {'src/frontend/specialize/lower.rs',
                                                     'src/frontend/specialize/lower/preservation.rs',
                                                     'src/frontend/specialize/raw.rs'}
                    and all(HEX.fullmatch(value) for value in plan['source_window'].values())
                    and list(plan['predictions']) == cases,
                    'first observer absence, limited source window or predictions were rewritten')
            order = [(case, profile) for case in cases for profile in ['ordinary', 'raw', 'hierarchy']]
            require([(row['case'], row['profile']) for row in observed['observations']] == order,
                    'zero-basis first command order differs')
        else:
            expected.add('capture.py')
            require(plan['driver_sha256'] == sha(files['capture.py'])
                    and observed['sources_stable'] is True and plan['prediction']
                    and not any(key in plan for key in ['source_window', 'observed_head_before', 'dirty_before'])
                    and [row['case'] for row in observed['observations']] == cases,
                    'wrapper driver or missing observer fields were reconstructed')
        for row in observed['observations']:
            case = row['case']
            require(row['source_sha256_after'] == plan['cases'][case]['source_sha256'],
                    'zero-basis original source bytes changed during observation')
            if packet_id == 'first':
                profile = row['profile']
                argv = ([cli, 'check', original + '/' + case, '--lean-kernel=' + kernel]
                        if profile == 'ordinary' else
                        [cli, 'check', '--entry=main::main',
                         '--module=main=' + original + '/' + case + '/main.qli',
                         '--ir-profile=' + profile, '--lean-kernel=' + kernel])
                prefix = case + '.' + profile
                expected_exit = 0 if profile == 'raw' else 1
            else:
                profile, prefix, expected_exit = 'wrapper', case, 0
                argv = [cli, 'check', original + '/translations-01/' + case,
                        '--lean-kernel=' + kernel]
            require(row['argv'] == argv and row['exit_code'] == expected_exit,
                    'zero-basis reported argv/outcome differs')
            for stream in ['stdout', 'stderr']:
                filename = prefix + '.' + stream + '.txt'
                expected.add(filename)
                require(row[stream]['path'] == filename
                        and row[stream]['sha256'] == sha(files[filename]),
                        'zero-basis full diagnostic stream association differs')
            stdout, stderr = (files[row[stream]['path']].decode() for stream in ['stdout', 'stderr'])
            if profile == 'raw':
                result = load_json(stdout)
                require(stderr == '' and result['status'] == 'checked'
                        and result['checker_path'] == kernel and result['checker_identity'] == 'unpinned'
                        and result['request_checked'] is False and result['source_preservation_verified'] is False
                        and result['verification'] == {'scope': 'native-validity', 'request_origin': 'none',
                                                       'source_steps_checked': True, 'source_meaning_verified': False}
                        and result['ir_profile'] == 'raw'
                        and result['source_check_scope'] == 'all-supplied-module-declarations'
                        and result['native_check_scope'] == 'selected-specialization',
                        'zero-basis selected Raw success scope differs')
            elif profile == 'hierarchy':
                require(stdout == '' and stderr.startswith('main:')
                        and ': unsupported: hierarchical transport does not support coherent basis tables; select the Raw profile\n' in stderr,
                        'zero-basis original hierarchy refusal was hidden')
            elif profile == 'ordinary':
                require(stdout == '' and stderr == original + '/' + case +
                        '/main.qli:2:1: invalid_entry: main must be an ordinary fn main() with a closed classical result\n',
                        'first ordinary entry mistake was rewritten')
            else:
                require(stderr == '' and stdout.startswith('checked source: ' + original + '/translations-01/' + case + '\n')
                        and '2 concrete local roots, 19 bundled roots\n' in stdout
                        and 'native decisions: 165; independent requests checked: 0\n' in stdout
                        and 'entry request checked: false\nsource preservation: not proved\n' in stdout,
                        'wrapper check success scope differs')
        require(set(files) == expected, 'missing or extra original zero-basis retained file')
    note = ' '.join(read_file(study / 'README.md', 16 * 1024, study).decode().split())
    for disclosure in ['informed study, not a blind benchmark', '54 original',
                       '56 files / 36,351 expanded bytes', 'two later notes',
                       'no pre-invocation driver file exists', 'no driver is reconstructed',
                       'no dirty-status snapshot was captured', 'not a complete source-closure freeze',
                       'not a clean commit-to-binary build attestation', 'never extracts',
                       'never executes recorded commands', 'No maximum-size case']:
        require(disclosure in note, 'missing zero-basis disclosure: ' + disclosure)
    print('Zero-basis history: two packets / 56 unchanged files / 36,351 bytes; '
          '12 first checks (4 Raw accepts, 4 hierarchy refusals, 4 entry mistakes) and '
          '4 separate wrapper accepts. Unsaved first observer retained as a limitation; '
          'no recorded source, observer or command executed.')


def check_computed_long_leaf_first():
    """Validate complete first refusals as inert bytes, never run an observer."""
    study = ROOT / 'tests/fixtures/authoring_sessions/computed-long-leaf-v030'
    require(study.is_dir() and not study.is_symlink()
            and study.resolve().is_relative_to(ROOT.resolve()), 'nonlocal long computed study')
    raw = read_file(study / 'packets.json', 32 * 1024, study)
    require(sha(raw) == 'bcb1d51e9f2132a5a518757c093cf6b3b7cf52c6fe3729242b41934db731e825',
            'long computed manifest differs')
    manifest = load_json(raw)
    require(set(manifest) == {'format', 'version', 'scope', 'archives'}
            and manifest['format'] == 'qleisli.computed-long-leaf-retention'
            and type(manifest['version']) is int and manifest['version'] == 1,
            'unknown long computed retention format')
    rows = manifest['archives']
    require(type(rows) is list
            and [(row['id'], row['file_count'], row['expanded_bytes']) for row in rows] ==
            [('first', 24, 266614)]
            and sum(row['file_count'] for row in rows) <= MAX_MEMBERS
            and sum(row['expanded_bytes'] for row in rows) <= MAX_CONTENT
            and sum(row['archive_bytes'] for row in rows) <= MAX_STORED,
            'complete long computed counts or unchanged reader bounds differ')
    check_signature_tree(study, ['first.tar.gz', 'packets.json', 'README.md'])
    files = read_archive(rows[0], study)
    original = '/private/tmp/qleisli-computed-long-leaf-first-h2o26w73'
    require(rows[0]['original_directory'] == original, 'long computed original location differs')
    cli = '/Users/masa/git/Qleisli/target/debug/qleisli'
    kernel = '/Users/masa/git/Qleisli/lean-kernel/.lake/build/bin/qleisli-kernel'
    scope = ('Dirty local executable identity and complete selected Rust/stdlib input window; '
             'build record separate. Not compiler/runtime/source preservation attestation, '
             'blind model benchmark, proof replay or issue completion.')
    cases = [
        ('attempt-01', 'first', 'capture.py', 1025,
         '817f6a9ea87d5a642d3861321710458fed6bca1bb4fba75e52ca3dd0f109bf23'),
        ('attempt-02', 'translation', 'capture_translation.py', 257,
         'dbb73d713dc1968957916ec09e5f19ce4ce21c544c0a8dd497ea0b64cc64e155'),
        ('attempt-03', 'compact', 'capture_compact.py', 0,
         'b7f23d2df7fc37eb2e74c7cc1d52d97541d42f67b427c866aa345d35d3176810'),
    ]
    expected = set()
    counts = collections.Counter()
    for attempt, prefix, driver, calls, digest in cases:
        source_name, edition_name = attempt + '/main.qli', attempt + '/Qargo.toml'
        note_name = prefix + '-source.json'
        stem = prefix + '-check'
        names = {source_name, edition_name, note_name, driver, stem + '.started.json',
                 stem + '.json', stem + '.stdout.txt', stem + '.stderr.txt'}
        expected.update(names)
        require(names <= files.keys(), 'incomplete long computed original attempt')
        source = files[source_name]
        note = load_json(files[note_name])
        require(sha(source) == digest and note['files'] ==
                {source_name: digest, edition_name: sha(files[edition_name])}
                and tomllib.loads(files[edition_name].decode()) ==
                {'schema-version': 2, 'qrate': {'edition': '2026'}}
                and source.count(b'let a=t(a);') == calls
                and b'use std::gate::t;' in source,
                'long computed original source, edition or before-run note differs')
        if prefix == 'first':
            require(note['format'] == 'qleisli.informed-first-source'
                    and note['model'] == 'GPT-6' and 'Not a blind authoring benchmark' in note['context']
                    and 'source-work exhaustion is also possible' in note['prediction'],
                    'long computed first model context or prediction was rewritten')
        else:
            require(note['format'] == 'qleisli.informed-source-translation'
                    and '1,000,000 source-work bound' in note['reason'],
                    'long computed translation lineage differs')
        require((b'qfor static i in 0..257 carry r=a { yield t(r); }' in source) ==
                (prefix == 'compact'), 'compact and expanded first sources were conflated')
        started = load_json(files[stem + '.started.json'])
        observed = load_json(files[stem + '.json'])
        start_fields = {'argv', 'cwd', 'observer_sha256', 'cli_sha256', 'kernel_sha256',
                        'head', 'dirty_status', 'inputs_before', 'scope'}
        finish_fields = {'exit_code', 'seconds', 'inputs_after', 'inputs_stable',
                         'cli_stable', 'kernel_stable', 'source_stable'}
        require(set(started) == start_fields and set(observed) == start_fields | finish_fields
                and all(observed[key] == value for key, value in started.items())
                and started['observer_sha256'] == sha(files[driver])
                and started['argv'] == [cli, 'check', original + '/' + attempt,
                                        '--format=json', '--lean-kernel=' + kernel]
                and started['cwd'] == '/Users/masa/git/Qleisli'
                and started['cli_sha256'] == 'b5b71be9a3f4ae0f134392f751390fb6fd88ed9b3329748a0b13fb9f3082e85e'
                and started['kernel_sha256'] == KERNEL_SHA
                and started['head'] == '460f72e019885bd859686b6f4a8b265b40ab36fd'
                and type(started['dirty_status']) is str and started['dirty_status']
                and started['scope'] == scope
                and type(observed['exit_code']) is int and observed['exit_code'] == 1
                and type(observed['seconds']) in (int, float)
                and math.isfinite(observed['seconds']) and observed['seconds'] >= 0
                and all(observed[key] is True for key in
                        ['inputs_stable', 'cli_stable', 'kernel_stable', 'source_stable']),
                'long computed saved observer, command, dirty provenance or outcome differs')
        inputs = started['inputs_before']
        require(type(inputs) is dict and len(inputs) == 206 and inputs == observed['inputs_after']
                and all(local_name(name) and type(value) is str and HEX.fullmatch(value)
                        for name, value in inputs.items())
                and sha(json.dumps(inputs, sort_keys=True, separators=(',', ':')).encode()) ==
                '8755eac5ee399459207541efb09d7cdb6e3b5de00551e95fd9e2565cd2e2a282',
                'long computed complete original input window differs')
        require(files[stem + '.stderr.txt'] == b'', 'long computed full stderr differs')
        response = load_json(files[stem + '.stdout.txt'])
        require(set(response) == {'format', 'version', 'command', 'outcome', 'diagnostics', 'result'}
                and response['format'] == 'qleisli.result' and type(response['version']) is int
                and response['version'] == 1 and response['command'] == 'check'
                and response['outcome'] == 'error' and response['result'] is None
                and len(response['diagnostics']) == 1,
                'long computed original full JSON error differs')
        diagnostic = response['diagnostics'][0]
        require(diagnostic['code'] == 'limit' and diagnostic['severity'] == 'error'
                and diagnostic['related'] == [], 'long computed first error category differs')
        if prefix == 'compact':
            counts['function-profile'] += 1
            require(diagnostic['message'] == 'with_computed phase normalization: function evidence exceeds its finite IR profile'
                    and diagnostic['primary'] == {'path': 'main.qli', 'start': 148, 'end': 248,
                                                  'line': 6, 'column': 11},
                    'compact finite FunctionEvidence refusal was hidden')
        else:
            counts['source-work'] += 1
            owner, used, requested = (('std::gate::t', 999695, 925) if prefix == 'first'
                                      else ('std::gate::scalar_eighth', 1000000, 1))
            require('source expansion exceeds the project-wide work limit of 1000000' in diagnostic['message']
                    and f'while checking {owner}; {used} units used, {requested} requested' in diagnostic['message']
                    and diagnostic['primary']['path'] == 'std://gate.qli'
                    and diagnostic['primary']['line'] == (25 if prefix == 'first' else 18),
                    'expanded source-work refusal was replaced by an equation result')
    require(set(files) == expected and counts == {'source-work': 2, 'function-profile': 1},
            'long computed complete inventory or diagnostic counters differ')
    note = ' '.join(read_file(study / 'README.md', 16 * 1024, study).decode().split())
    for disclosure in ['informed maintenance study, not a blind authoring benchmark',
                       '24 unchanged files / 266,614 expanded bytes', 'Every original regular-file mode',
                       'expanded-source work limits remain unrepaired', '206 hashes',
                       'not independently resampled afterward', 'not a reconstructed clean commit-to-binary build attestation',
                       'neither a source-success benchmark', 'M2 acceptance authority',
                       'never overwrite these first sources', 'never extracts', 'never executes archived']:
        require(disclosure in note, 'missing long computed disclosure: ' + disclosure)
    print('Long computed history: one packet / 24 unchanged files / 266,614 bytes; '
          'three first refusals, 2 source-work / 1 finite FunctionEvidence profile. '
          'Expanded work limits remain unrepaired; no recorded source, observer or command executed.')


if __name__ == '__main__':
    main()
