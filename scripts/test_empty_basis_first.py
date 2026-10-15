#!/usr/bin/env python3
"""Check retained empty-basis history as bounded inert data; never replay it.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import gzip
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import tarfile
import tomllib


ROOT = Path(__file__).resolve().parents[1]
STUDY = ROOT / 'tests/fixtures/authoring_sessions/empty-basis-v030'
MANIFEST_SHA = '0eb40cb998bd9c5be404ad49cec9fc9fa8731d47f1958c6dfa8ebfffc0acc421'
WRAPPER_FREEZE = '20561f43662a2c6e7aef9c837cf208878d561cb3cfc5311966da8cfca188feb7'
FINITE_FREEZE = '02e9f30765722f3301799c04a99fbace24eb99ed9767ddddc0e93cb56177d4a8'
CAPTURE_FREEZE = 'bb9e2fbeb22907606300fd929d62bd6729bff70ea0ee339e3b4e57c80814fc3e'
CLI_SHA = 'fb76379c81758517cc12e2b992e9855cdbbfa5c4c2768887f772d649a35b347c'
KERNEL_SHA = '54c9d60b80f67217abd95c8fe6ec1c06aa262e142d5e6db30f46a20cb90faf07'
FINITE_HEAD = '54edaa7717777ac35f86d7a4a9d013069ad676ac'
WORKING_SHA = '1c12213ae701e3150fd76872b90dc6e88259333b41b1adf122fd33399f4036dd'
# Local bounds stay below the unchanged repository fixture budget.
MAX_STORED = 2 * 1024 * 1024
MAX_CONTENT = 10 * 1024 * 1024
MAX_MEMBERS = 200
MAX_CONTAINER = MAX_CONTENT + MAX_MEMBERS * 1024 + 10240
HEX = re.compile(r'[0-9a-f]{64}')
PACKET_TOTALS = {
    'wrapper-first-sources': (18, 6935),
    'wrapper-first-observations': (22, 189935),
    'finite-first-sources': (38, 23171),
    'finite-first-observations': (95, 9482686),
}


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


def read_file(path, limit):
    require(path.is_file() and not path.is_symlink()
            and path.resolve().is_relative_to(STUDY.resolve()), 'nonlocal retained file')
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
        require(size <= MAX_CONTENT - expanded, 'raw tar content exceeds bound')
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
    try:
        load_json(b'{"duplicate": 1, "duplicate": 2}')
    except ValueError as error:
        require(str(error) == 'duplicate JSON key', 'unexpected duplicate JSON rejection')
    else:
        raise ValueError('duplicate synthetic JSON key accepted')


def read_archive(row):
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
        require(member_name not in entries and integer(item['bytes'], MAX_CONTENT)
                and type(item['sha256']) is str and HEX.fullmatch(item['sha256'])
                and item['original_mode'] == '0644', 'invalid original member identity')
        entries[member_name] = item
    require(list(entries) == sorted(entries, key=lambda path: PurePosixPath(path).parts),
            'member inventory is not canonical')
    require(sum(item['bytes'] for item in entries.values()) == row['expanded_bytes'],
            'expanded byte count differs')
    compressed = read_file(STUDY / name, MAX_STORED)
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


def check_project_manifests(files, count):
    manifests = [p for p in files if p.endswith('/Qargo.toml')]
    require(len(manifests) == count, 'complete project count differs')
    for path in manifests:
        manifest = tomllib.loads(files[path].decode())
        require(manifest['schema-version'] == 2 and manifest['qrate']['edition'] == '2026'
                and path.removesuffix('Qargo.toml') + 'main.qli' in files,
                'missing complete schema-2 edition-2026 project')


def check_result(parsed, producer_request=False):
    require(parsed['format'] == 'qleisli.result' and parsed['version'] == 1
            and parsed['command'] == 'check', 'unexpected recorded CLI schema')
    if parsed['outcome'] == 'ok':
        result = parsed['result']
        require(result['checker_identity'] == 'unpinned'
                and result['source_preservation_verified'] is False
                and result['verification']['source_meaning_verified'] is False,
                'recorded source/binary scope differs')
        if producer_request:
            require(result['request_checked'] is True
                    and result['verification']['scope'] == 'producer-consistency'
                    and result['verification']['request_origin'] == 'producer',
                    'hierarchy producer request scope differs')
        else:
            require(result['request_checked'] is False
                    and result['verification']['scope'] == 'native-validity'
                    and result['verification']['request_origin'] == 'none'
                    and result['verification']['source_steps_checked'] is True,
                    'Raw validity scope differs')


def check_wrapper(packets):
    sources, observed = packets['wrapper-first-sources'], packets['wrapper-first-observations']
    frozen = load_json(sources['freeze.json'])
    require(sha(sources['freeze.json']) == WRAPPER_FREEZE and frozen['schema'] == 1
            and frozen['kind'] == 'informed-first-source-conditional-minimization-study'
            and frozen['notes_sha256'] == sha(sources['README.md']), 'wrapper freeze differs')
    frozen_files = {}
    for case in frozen['cases']:
        for name, digest in case['files'].items():
            require(local_name(name) not in frozen_files and sha(sources[name]) == digest,
                    'wrapper first-source identity differs')
            frozen_files[name] = digest
    require(len(frozen_files) == 16
            and set(frozen_files) | {'freeze.json', 'README.md'} == set(sources),
            'wrapper complete inventory differs')
    check_project_manifests(sources, 8)
    summary = load_json(observed['summary.json'])
    require(summary['schema'] == 1 and summary['freeze_sha256'] == WRAPPER_FREEZE
            and summary['repairs'] == summary['retries'] == summary['fallbacks'] == 0
            and summary['desired_forms'] == 'retained separately and uncompiled',
            'wrapper scope or source repairs differ')
    expected = [('empty-wrapper-unused', 1, 'type'), ('empty-wrapper-selected', 1, 'type'),
                ('unit-wrapper-unused', 0, None), ('unit-wrapper-selected', 1, 'unsupported')]
    require([(r['case'], r['exit_code']) for r in summary['observations']]
            == [(name, code) for name, code, _ in expected], 'wrapper real outcomes differ')
    source_hashes = {name: sha(data) for name, data in sources.items()}
    for row, (name, _, diagnostic) in zip(summary['observations'], expected):
        require(row == load_json(observed[name + '/record.json']) and row['stable_inputs'] is True,
                'wrapper record or stable window differs')
        for stream in ['stdout', 'stderr']:
            require(sha(observed[name + '/' + stream]) == row[stream + '_sha256'],
                    'wrapper raw stream differs')
        before, after = [load_json(observed[name + '/' + which + '.json'])
                         for which in ['before', 'after']]
        require(set(before) == set(after)
                and all(before[k] == after[k] for k in before if k != 'recorded_utc')
                and before['working_inputs']['head'] == frozen['observed_head']
                and before['first_files'] == source_hashes
                and before['executables']['cli']['sha256'] == CLI_SHA
                and before['executables']['kernel']['sha256'] == KERNEL_SHA,
                'wrapper original context differs')
        parsed = load_json(observed[name + '/stdout'])
        check_result(parsed)
        require((parsed['outcome'] == 'ok') == (row['exit_code'] == 0)
                and [d['code'] for d in parsed['diagnostics']] ==
                ([] if diagnostic is None else [diagnostic]), 'wrapper diagnostic differs')


def check_finite(packets):
    sources, observed = packets['finite-first-sources'], packets['finite-first-observations']
    check_inventory_freeze(sources, 'freeze.json', FINITE_FREEZE, 37, 15003)
    check_inventory_freeze(observed, 'capture-freeze.json', CAPTURE_FREEZE, 94, 9464404)
    check_project_manifests(sources, 16)
    plan, summary = load_json(sources['study-plan.json']), load_json(observed['summary.json'])
    require(plan['format'] == 'qleisli.empty-bits-finite-first-study' and plan['version'] == 1
            and plan['case_count'] == len(plan['cases']) == 8 and plan['max_authored_qubits'] == 1
            and plan['desired_forms_executed'] is False and plan['planned_current_invocations'] == 17,
            'finite first-source study scope differs')
    require(summary['format'] == 'qleisli.empty-bits-finite-first-observations'
            and summary['version'] == 1 and summary['complete'] is True
            and summary['desired_forms_executed'] is False
            and (summary['invocations'], summary['accepted'], summary['refused'], summary['timeouts'])
            == (17, 4, 13, 0) and summary['source_freeze_sha256'] == FINITE_FREEZE
            and summary['cli_sha256'] == CLI_SHA and summary['kernel_sha256'] == KERNEL_SHA,
            'finite actual observation scope differs')
    require(all(summary[k] is True for k in ['all_per_invocation_windows_stable',
                'full_study_window_stable', 'whole_working_inputs_stable']),
            'finite changing observation window')
    first, last = [load_json(observed['context-' + which + '.json']) for which in ['before', 'after']]
    source_hashes = {name: {'bytes': len(data), 'sha256': sha(data)} for name, data in sources.items()}
    require(first == last and first['head'] == FINITE_HEAD
            and first['cli_sha256'] == CLI_SHA and first['kernel_sha256'] == KERNEL_SHA
            and len(first['runtime_files']) == summary['runtime_file_count'] == 87
            and first['first_source_files'] == source_hashes, 'finite original context differs')
    working = load_json(observed['working-inputs-before.json'])
    require(working == load_json(observed['working-inputs-after.json'])
            and working['head'] == FINITE_HEAD and working['working_inputs_sha256'] == WORKING_SHA
            and len(working['files']) == 18961, 'finite complete working-input map differs')
    runner = load_json(observed['first-runner-freeze.json'])
    require(runner['runner_sha256'] == sha(observed['run_new_literal_checks.py'])
            and runner['first_source_freeze_sha256'] == FINITE_FREEZE
            and runner['invocations_planned'] == 17 and runner['prior_recorded_argv_loaded'] is False,
            'original frozen runner differs')
    integrity = load_json(observed['postcheck-source-integrity.json'])
    require(integrity['all_original_files_match'] is True and integrity['original_listed_files'] == 37
            and integrity['original_bytes'] == 15003 and integrity['prediction_matches'] == 17
            and integrity['whole_working_inputs_sha256'] == WORKING_SHA
            and integrity['desired_invocations'] == 0, 'finite source-integrity record differs')
    records = summary['records']
    expected = {(c['id'], p): c['current_prediction'][p.replace('-', '_')]
                for c in plan['cases'] for p in ['finite'] + ['selected-' + p for p in c['selected_profiles']]}
    require(len(records) == len(expected) == 17
            and {(r['case'], r['profile']) for r in records} == set(expected)
            and sum(r['exit_code'] == 0 for r in records) == 4, 'finite invocation inventory differs')
    for row in records:
        directory = local_name(row['record_directory'])
        require(directory == 'checks/' + local_name(row['case']) + '/' + local_name(row['profile'])
                and row == load_json(observed[directory + '/record.json'])
                and row['timeout'] is False and row['window_stable'] is True
                and row['matches_initial_window'] is True, 'finite invocation record differs')
        for stream in ['stdout', 'stderr']:
            content = observed[directory + '/' + stream]
            require(sha(content) == row[stream + '_sha256']
                    and len(content) == row[stream + '_bytes'], 'finite raw stream differs')
        require(load_json(observed[directory + '/before.json']) ==
                load_json(observed[directory + '/after.json']) == first,
                'finite per-invocation context differs')
        parsed = load_json(observed[directory + '/stdout'])
        check_result(parsed, row['profile'] == 'selected-hierarchy')
        prediction = expected[(row['case'], row['profile'])]
        require(row['outcome'] == parsed['outcome'] and row['result'] == parsed['result']
                and row['diagnostics'] == parsed['diagnostics']
                and (row['exit_code'] == 0) == (parsed['outcome'] == 'ok')
                and (row['exit_code'] == 0 if prediction == 'accept' else
                     row['exit_code'] == 1 and [d['code'] for d in row['diagnostics']] == [prediction]),
                'finite predeclared outcome or diagnostic differs')


def main():
    check_synthetic_containers()
    require(STUDY.is_dir() and not STUDY.is_symlink()
            and STUDY.resolve().is_relative_to(ROOT.resolve()), 'nonlocal study directory')
    manifest_bytes = read_file(STUDY / 'packets.json', 64 * 1024)
    require(sha(manifest_bytes) == MANIFEST_SHA, 'reviewed retention manifest differs')
    manifest = load_json(manifest_bytes)
    require(set(manifest) == {'format', 'version', 'scope', 'archives'}
            and manifest['format'] == 'qleisli.empty-basis-retention'
            and type(manifest['version']) is int and manifest['version'] == 1,
            'unknown retention format')
    rows = manifest['archives']
    require(type(rows) is list and [r['id'] for r in rows] == list(PACKET_TOTALS),
            'missing or duplicate packet')
    require(sum(r['archive_bytes'] for r in rows) <= MAX_STORED
            and sum(r['expanded_bytes'] for r in rows) <= MAX_CONTENT
            and sum(r['file_count'] for r in rows) <= MAX_MEMBERS,
            'aggregate retention exceeds reader bounds')
    require(all((r['file_count'], r['expanded_bytes']) == PACKET_TOTALS[r['id']] for r in rows),
            'reviewed original packet totals differ')
    packets = {row['id']: read_archive(row) for row in rows}
    require({p.name for p in STUDY.iterdir()} ==
            {r['archive'] for r in rows} | {'packets.json', 'README.md'}, 'unlisted retained path')
    check_wrapper(packets)
    check_finite(packets)
    note = ' '.join(read_file(STUDY / 'README.md', 16 * 1024).decode().split())
    for disclosure in ['It never executes recorded commands.', 'not a blind benchmark',
                       'not a historical Git archive baseline', 'Desired drafts remain uncompiled.',
                       'Native JSON checker_identity is unpinned', 'producer-origin composition request',
                       'No source-preservation, PR, quantitative RS or EXACT discharge',
                       'The prior CLI was not built from the finite study\'s current dirty source.']:
        require(disclosure in note, 'missing study disclosure: ' + disclosure)
    print('Empty-basis history: four packets / 173 unchanged files / 9,702,727 expanded bytes; '
          '4 wrapper checks and 17 finite checks retained. No command executed.')


if __name__ == '__main__':
    main()
