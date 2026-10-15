#!/usr/bin/env python3
"""Check inert stdlib first studies with bounded decompression; execute nothing.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import gzip
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import tarfile


ROOT = Path(__file__).resolve().parents[1]
STUDY = ROOT / 'tests/fixtures/authoring_sessions/stdlib-boundary-v030'
MANIFEST = ROOT / 'tests/fixtures/authoring_sessions/stdlib-boundary-v030/packets.json'
README = ROOT / 'tests/fixtures/authoring_sessions/stdlib-boundary-v030/README.md'
MANIFEST_SHA = 'e5eda8da8b693f73abb6462afb185afc7b74bb9a9d443edf4a063d8fad2c2cd5'
# These local reader bounds are below the unchanged repository fixture budget.
MAX_STORED = 8 * 1024 * 1024
MAX_CONTENT = 26 * 1024 * 1024
MAX_MEMBERS = 1300
MAX_CONTAINER = MAX_CONTENT + MAX_MEMBERS * 1024 + 10240
HEX = re.compile(r'[0-9a-f]{64}')


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
    require(type(name) is str and name and not any(c in name for c in '\\\x00\r\n'),
            'invalid member path')
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


def check_ustar_container(raw, expected_count):
    """Reject extension records before tarfile can consume or reinterpret them."""
    require(type(raw) is bytes and len(raw) <= MAX_CONTAINER
            and len(raw) % 512 == 0 and integer(expected_count, MAX_MEMBERS),
            'invalid bounded tar container')
    offset = count = expanded = 0
    while True:
        header = raw[offset:offset + 512]
        require(len(header) == 512, 'missing tar terminator')
        if not any(header):
            require(len(raw) - offset >= 1024 and not any(raw[offset:]),
                    'invalid tar terminator or nonzero tail')
            require(count == expected_count, 'raw tar member count differs')
            return
        require(count < expected_count and count < MAX_MEMBERS,
                'raw tar member count exceeds bound')
        require(header[156:157] == tarfile.REGTYPE
                and header[257:263] == b'ustar\x00' and header[263:265] == b'00',
                'nonregular or non-USTAR raw header')
        size_field = header[124:136]
        require(re.fullmatch(rb'[0-7]{11}\x00', size_field) is not None,
                'noncanonical raw tar size')
        size = int(size_field[:-1], 8)
        require(size <= MAX_CONTENT - expanded, 'raw tar content exceeds bound')
        data_end = offset + 512 + size
        next_offset = offset + 512 + ((size + 511) // 512) * 512
        require(next_offset <= len(raw) and not any(raw[data_end:next_offset]),
                'truncated tar member or nonzero padding')
        expanded += size
        count += 1
        offset = next_offset


def check_synthetic_containers():
    """Exercise reader guards with new tiny bytes, never retained commands."""
    def member(name, kind, content):
        info = tarfile.TarInfo(name)
        info.type, info.size, info.mode = kind, len(content), 0o644
        return (info.tobuf(format=tarfile.USTAR_FORMAT) + content
                + bytes((-len(content)) % 512))

    regular = member('control', tarfile.REGTYPE, b'x')
    terminator = bytes(1024)
    check_ustar_container(regular + terminator, 1)
    # tarfile iteration hides an empty PAX or GNU longname header. Checking its
    # yielded TarInfo alone would accept both; this scan sees the original type.
    rejected = [
        (member('extension', tarfile.XHDTYPE, b'') + regular + terminator,
         'nonregular or non-USTAR raw header'),
        (member('extension', tarfile.GNUTYPE_LONGNAME, b'control\x00')
         + regular + terminator, 'nonregular or non-USTAR raw header'),
        (regular + bytes(512), 'invalid tar terminator or nonzero tail'),
        (regular + terminator + bytes(511) + b'x',
         'invalid tar terminator or nonzero tail'),
        (regular + regular + terminator, 'raw tar member count exceeds bound'),
    ]
    for raw, expected_message in rejected:
        try:
            check_ustar_container(raw, 1)
        except ValueError as error:
            require(str(error) == expected_message, 'unexpected synthetic rejection')
        else:
            raise ValueError('malformed synthetic tar container accepted')


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
                and item['original_mode'] in {'0644', '0755'}, 'invalid member identity')
        entries[member_name] = item
    require(list(entries) == sorted(entries, key=lambda path: PurePosixPath(path).parts),
            'member inventory is not canonical')
    require(sum(item['bytes'] for item in entries.values()) == row['expanded_bytes'],
            'expanded byte count differs')
    compressed = read_file(STUDY / name, MAX_STORED)
    require(len(compressed) == row['archive_bytes']
            and sha(compressed) == row['archive_sha256'], 'archive identity differs')
    # Bound the complete gzip expansion before tarfile can parse extended headers.
    # No archive member is extracted to disk and no retained program is imported.
    with gzip.GzipFile(fileobj=io.BytesIO(compressed), mode='rb') as stream:
        raw = stream.read(MAX_CONTAINER + 1)
    require(len(raw) <= MAX_CONTAINER and len(raw) == row['tar_bytes']
            and sha(raw) == row['tar_sha256'], 'tar container identity or bound differs')
    # The fixed manifest already binds the actual packets. This additional scan
    # makes the advertised format guard reject hidden PAX/GNU records too.
    check_ustar_container(raw, row['file_count'])
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


def check_freeze(files, name):
    frozen = load_json(files[name])
    seen = set()
    total = 0
    for row in frozen['files']:
        path = local_name(row['path'])
        require(path not in seen and path in files, 'invalid historical freeze member')
        seen.add(path)
        content = files[path]
        require(len(content) == row['bytes'] and sha(content) == row['sha256'],
                'historical frozen bytes differ')
        total += len(content)
    require(frozen.get('file_count', len(seen)) == len(seen)
            and frozen.get('bytes', total) == total, 'historical freeze count differs')


def check_observations(packets):
    first = packets['first-observations']
    summary = load_json(first['summary.json'])
    records = load_json(first['all-observations.json'])['records']
    require(len(records) == summary['source_observation_count'] == 128
            and sum(r['returncode'] == 0 for r in records) == summary['total_accepted'] == 40
            and summary['total_refused'] == 88, 'first observation counts differ')
    require(summary['source_repairs'] == 0 and summary['authored_max_program_qubits'] == 2
            and len(summary['first_prediction_corrections']) == 4,
            'first source defects or bounds disappeared')
    for row in records:
        directory = local_name(row['record_directory'])
        for stream in ['stdout', 'stderr']:
            require(sha(first[directory + '/' + stream]) == row[stream + '_sha256'],
                    'first raw stream differs')
        require(row['binary_stable_before_after'], 'first changing invocation window')
    v2 = load_json(packets['exact-v2-observations']['summary.json'])
    require((v2['invocation_count'], v2['emit_accepted'], v2['emit_refused'],
             v2['exact_request_accepted'], v2['exact_request_refused'],
             v2['exact_request_unperformed_after_emit_refusal']) == (38, 6, 10, 2, 4, 10)
            and v2['identity_stable'], 'v2 real failures disappeared')
    for packet, expected_count in [('exact-v2-observations', 38), ('exact-v3-observations', 48)]:
        files = packets[packet]
        records = [name for name in files if name.startswith('checks/') and name.endswith('/record.json')]
        require(len(records) == expected_count, 'missing raw invocation record')
        for name in records:
            directory = name.removesuffix('/record.json')
            row = load_json(files[name])
            for stream in ['stdout', 'stderr']:
                require(sha(files[directory + '/' + stream]) == row[stream + '_sha256'],
                        'exact-study raw stream differs')
            before = load_json(files[directory + '/context-before.json'])
            after = load_json(files[directory + '/context-after.json'])
            require(row['identity_stable'] and set(before) == set(after)
                    and all(before[key] == after[key] for key in before if key != 'utc'),
                    'exact-study changing invocation window')
    v3_files = packets['exact-v3-observations']
    v3 = load_json(v3_files['summary.json'])
    require((v3['actual_invocations'], v3['emitted_artifacts'], v3['exact_request_accepted'],
             v3['exact_request_refused'], v3['source_steps_accepted']) == (48, 16, 10, 6, 16)
            and v3['prediction_mismatches'] == v3['blocked'] == []
            and v3['all_per_invocation_windows_stable'] and v3['whole_window_stable']
            and v3['head_start'] == v3['head_finish'], 'v3 observation scope differs')
    records = load_json(v3_files['all-observations.json'])
    require(len(records) == 48, 'missing v3 invocation')
    for row in records:
        directory = 'checks/' + local_name(row['case']) + '/' + local_name(row['kind'])
        for stream in ['stdout', 'stderr']:
            require(sha(v3_files[directory + '/' + stream]) == row[stream + '_sha256'],
                    'v3 raw stream differs')
        require(row['identity_stable'] and row['cli_and_kernel_expected_hashes'],
                'v3 changing invocation window')
    inspections = load_json(v3_files['artifact-inspections.json'])
    require(len(inspections) == 16, 'missing descriptive artifact inspection')
    for row in inspections:
        require(sha(v3_files['artifacts/' + row['id'] + '.qirf.json']) == row['artifact_sha256']
                and row['observed_extra_physical_wires'] == 0
                and row['input_map_matches_predeclared'] and row['output_map_matches_predeclared']
                and row['source_preservation_verified'] is False and row['source_table_empty']
                and row['source_step_check_verification']['source_meaning_verified'] is False,
                'descriptive artifact binding or proof limit differs')


def main():
    check_synthetic_containers()
    require(STUDY.is_dir() and not STUDY.is_symlink()
            and STUDY.resolve().is_relative_to(ROOT.resolve()), 'nonlocal study directory')
    manifest_bytes = read_file(MANIFEST, 1024 * 1024)
    require(sha(manifest_bytes) == MANIFEST_SHA, 'reviewed retention manifest differs')
    manifest = load_json(manifest_bytes)
    require(set(manifest) == {'format', 'version', 'scope', 'archives'}
            and manifest['format'] == 'qleisli.stdlib-boundary-retention'
            and type(manifest['version']) is int and manifest['version'] == 1,
            'unknown retention format')
    rows = manifest['archives']
    require(type(rows) is list and [r['id'] for r in rows] == [
        'first-sources', 'first-observations', 'exact-v2-sources',
        'exact-v2-observations', 'exact-v3-sources', 'exact-v3-observations'],
        'missing or duplicate packet')
    require(sum(r['archive_bytes'] for r in rows) <= MAX_STORED
            and sum(r['expanded_bytes'] for r in rows) <= MAX_CONTENT
            and sum(r['file_count'] for r in rows) <= MAX_MEMBERS,
            'aggregate retention exceeds reader bounds')
    require(sum(r['file_count'] for r in rows) == 1227
            and sum(r['expanded_bytes'] for r in rows) == 25663271,
            'reviewed original packet totals differ')
    packets = {row['id']: read_archive(row) for row in rows}
    require({p.name for p in STUDY.iterdir()} ==
            {r['archive'] for r in rows} | {'packets.json', 'README.md'},
            'unlisted retained path')
    for files in packets.values():
        for name in ['freeze.json', 'freeze-addendum.json', 'v3-freeze.json', 'capture-freeze.json']:
            if name in files:
                check_freeze(files, name)
    # V3 is a new packet; the missing-manifest V2 and every first defect stay intact.
    v2, v3 = packets['exact-v2-sources'], packets['exact-v3-sources']
    require(all(v3.get(name) == data for name, data in v2.items())
            and set(v3) - set(v2) == {'common/Qargo.toml', 'V3-PLAN.md', 'v3-freeze.json'}
            and 'common/Qargo.toml' not in v2, 'v3 rewrote a predecessor')
    require(load_json(packets['first-sources']['freeze.json'])['max_program_qubits'] == 2
            and load_json(v3['v3-freeze.json'])['max_program_qubits'] == 2,
            'authored experiment bound differs')
    require(packets['first-sources']['independent-matrices.json'] ==
            v2['independent-matrices-v1-unchanged.json'] ==
            v3['independent-matrices-v1-unchanged.json'], 'independent first matrices changed')
    check_observations(packets)
    note = ' '.join(read_file(README, 32 * 1024).decode().split())
    for disclosure in ['It never executes recorded commands.', 'not a blind benchmark',
                       'missing `common/Qargo.toml`', 'source_meaning_verified=false',
                       'native JSON checker_identity is unpinned',
                       'No source-preservation, PR, quantitative RS or EXACT discharge',
                       'not a historical Git archive baseline']:
        require(disclosure in note, 'missing study disclosure: ' + disclosure)
    print('Stdlib history: six packets / 1,227 unchanged files / 25,663,271 expanded bytes; '
          '128 first checks, 38 v2 and 48 v3 invocations retained. No command executed.')


if __name__ == '__main__':
    main()
