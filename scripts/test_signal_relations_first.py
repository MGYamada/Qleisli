"""Read #30/#158/#198 first evidence without executing historical commands.

The source and raw streams are immutable data, not proof of exact operators,
source preservation, scalable synthesis, resources or executable build source.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
from datetime import datetime
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import tomllib


ROOT = Path(__file__).resolve().parents[1]
MEMBERS = (
    'tests/fixtures/authoring_sessions/classical-synthesis-v030/**/*',
    'tests/fixtures/authoring_sessions/signal-interface-v030/**/*',
    'tests/fixtures/authoring_sessions/quantum-relations-v030/**/*',
)
STUDIES = (
    ('classical-synthesis-30', 20, 43840, 6,
     '64e6968f6301ececcccd44c974d9faa7b19c3841788bc151e595ea4caaff2b4e',
     '5b25c289c9f0120feb7d7d3ab9728b0c488b6ae0e34e9eb5d672d688d7ca57f6',
     ('both-xor', 'increment2')),
    ('signal-158', 26, 43736, 9,
     'a3eeb3bfa5d7f7985dde56ac48f9cd2985fe2a3a4c49f15ab5ac89ff31a668b6',
     'cfaaa74af65c3d3e81be6bcc2f11614b535f8f42b5bebb0997b3e4f02919e531',
     ('returned-signal', 'lost-signal', 'explicit-discard')),
    ('quantum-relations-198', 60, 181686, 24,
     '6ba00b21c381bdfa050d133f991cf4ae3521a3a5da4b8df5b9e4c8edafaa4dfe',
     '9f7d7de89cb674cbedc114ed6fa7846fbf34c91653a2d1faae15a761c0e5ad58',
     ('eq-live', 'ne-nested', 'ord-zero', 'hash-live', 'hash-nested',
      'hash-zero', 'classical-static', 'explicit-coherent', 'declared-hash',
      'imported-qualified-hash')),
)
BINARY_HASHES = {
    'cli': 'ecf902d664448a5a07bca43d01cb1739f81ee07e4d3cd6d7a378b7eabed438d1',
    'kernel': 'abbce360dbb4dcf9425872c93e16456b576623f46bd9daeef25b7bdf841658ae',
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        assert key not in result, 'duplicate JSON key: ' + key
        result[key] = value
    return result


def read_json(data):
    return json.loads(data, object_pairs_hook=unique_object)


def safe_name(name):
    path = PurePosixPath(name)
    assert name and not path.is_absolute() and str(path) == name
    assert '..' not in path.parts and '\\' not in name
    return name


def read_files(pattern, count, byte_count, session_sha):
    study = ROOT / pattern.removesuffix('/**/*')
    assert study.is_dir() and not study.is_symlink()
    files = {}
    for path in ROOT.glob(pattern):
        assert not path.is_symlink() and path.resolve().is_relative_to(study.resolve())
        if path.is_dir():
            continue
        assert path.is_file() and path.stat().st_size <= 32 * 1024
        data = path.read_bytes()
        assert len(data) <= 32 * 1024
        files[path.relative_to(study).as_posix()] = data
    assert len(files) == count and sum(map(len, files.values())) == byte_count
    assert digest(files['session.json']) == session_sha
    session = read_json(files['session.json'])
    assert session['retained_sha256'] == {
        name: digest(data) for name, data in files.items() if name != 'session.json'}
    return files, session


def first_packet(files, session, count, sums_sha, cases):
    first = {name.removeprefix('first/'): data for name, data in files.items()
             if name.startswith('first/')}
    assert len(first) == count and digest(first['SHA256SUMS']) == sums_sha
    inventory = {}
    for line in first['SHA256SUMS'].decode().splitlines():
        match = re.fullmatch(r'([0-9a-f]{64})  (.+)', line)
        assert match
        sha, name = match.groups()
        safe_name(name)
        assert name not in inventory
        inventory[name] = sha
    hashes = {name: digest(data) for name, data in first.items()}
    assert inventory == {name: sha for name, sha in hashes.items() if name != 'SHA256SUMS'}
    assert session['status'] == 'first-observations-recorded'
    assert len(session['attempts']) == 1
    attempt = session['attempts'][0]
    assert attempt['id'] == 'attempt-01' and attempt['reports'] == []
    canonical = {name: data for name, data in files.items() if name.startswith('attempt-01/')}
    assert canonical == {name: data for name, data in first.items() if name.startswith('attempt-01/')}
    for field, suffix in [('sha256', '.qli'), ('manifest_sha256', '/Qargo.toml')]:
        assert attempt[field] == {name.removeprefix('attempt-01/'): digest(data)
                                  for name, data in canonical.items() if name.endswith(suffix)}
    assert set(attempt['manifest_sha256']) == {case + '/Qargo.toml' for case in cases}
    for case in cases:
        manifest = tomllib.loads(canonical['attempt-01/' + case + '/Qargo.toml'].decode())
        assert manifest['schema-version'] == 2 and manifest['qrate']['edition'] == '2026'
    if 'session.json' in first:
        original = read_json(first['session.json'])
        assert original['status'] == 'frozen-awaiting-first-observation'
        assert len(original['attempts']) == 1
        old = original['attempts'][0]
        assert old['observations'] == old['reports'] == []
        assert old['sha256'] == attempt['sha256']
        assert old['manifest_sha256'] == attempt['manifest_sha256']
    return first, hashes, attempt


def original_observations(files, session, events):
    """Recover every original observation byte in memory; never open its paths."""
    restored = {}
    for name, data in files.items():
        if not name.startswith('observations/'):
            continue
        relative = name.removeprefix('observations/')
        event = read_json(data)
        if name in events and 'original_files' in event:
            directory = event['original_directory']
            assert directory == Path(relative).stem
            assert set(event['original_files']) == {
                'command.json', 'result.json', 'stdout.txt', 'stderr.txt'}
            for leaf, record in event['original_files'].items():
                content = record['utf8'].encode()
                assert digest(content) == record['sha256']
                restored[safe_name(directory + '/' + leaf)] = content
        else:
            restored[safe_name(relative)] = data
    assert session['original_observation_sha256'] == {
        name: digest(data) for name, data in restored.items()}
    return restored


def event_data(event, stem):
    if stem == 'signal-158':
        return (event['before'], event['after'], event['started_utc'],
                event['recorded_utc'], event['elapsed_seconds'], event['exit_code'],
                event['stdout_raw'], event['stderr_raw'])
    raw = {name: value['utf8'] for name, value in event['original_files'].items()}
    command, result = read_json(raw['command.json']), read_json(raw['result.json'])
    assert event['command'] == command['argv'] and event['cwd'] == command['cwd']
    assert result['timed_out'] is False
    for stream in ('stdout', 'stderr'):
        assert digest(raw[stream + '.txt'].encode()) == result[stream + '_sha256']
    if stem == 'classical-synthesis-30':
        assert result['first_packet_unchanged'] is True and result['binaries_unchanged'] is True
        ended, elapsed, code = result['finished_at_utc'], result['duration_seconds'], result['returncode']
    else:
        assert all(result[key] == value for key, value in command.items())
        assert result['stdout_json'] == read_json(raw['stdout.txt'])
        ended, elapsed, code = result['ended_at_utc'], result['elapsed_seconds'], result['exit_code']
    assert event['exit_code'] == code and event['recorded_utc'] == ended
    return (command['before'], result['after'], command['started_at_utc'], ended,
            elapsed, code, raw['stdout.txt'], raw['stderr.txt'])


def check_outcome(parsed, case, action, exit_code):
    error = ('ownership' if case == 'lost-signal' else
             'parse' if case in ('eq-live', 'ne-nested', 'ord-zero') else
             'unknown_name' if case in ('hash-live', 'hash-nested', 'hash-zero') else None)
    assert parsed['format'] == 'qleisli.result' and parsed['version'] == 1
    assert parsed['command'] == action and exit_code == (1 if error else 0)
    assert parsed['outcome'] == ('error' if error else 'ok')
    if error:
        assert parsed['result'] is None
        assert [d['code'] for d in parsed['diagnostics']] == [error]
        diagnostic = parsed['diagnostics'][0]
        assert diagnostic['primary']['path'] == 'main.qli'
        if error == 'ownership':
            assert 'implicit quantum destruction is forbidden' in diagnostic['message']
        elif error == 'unknown_name':
            assert diagnostic['message'] == 'unresolved function hash'
        else:
            token = {'eq-live': '==', 'ne-nested': '!=', 'ord-zero': '<'}[case]
            assert diagnostic['message'] == 'expected `}`, found `' + token + '`'
    else:
        assert parsed['diagnostics'] == []
        if action == 'check':
            assert parsed['result']['source_preservation_verified'] is False
            assert parsed['result']['checker_identity'] == 'unpinned'
        else:
            # Recorded floating readout only, not an exact operator/phase proof.
            expected = {
                'both-xor': [([False, False, True, False], .2500000000000001),
                             ([False, True, True, False], .2500000000000001),
                             ([True, False, True, False], .2500000000000001),
                             ([True, True, False, True], .2500000000000001)],
                'increment2': [([False, True], .5000000000000001), ([True, False], .5000000000000001)],
                'returned-signal': [([False, False], .5000000000000001), ([True, True], .5000000000000002)],
                'explicit-discard': [([False], .5000000000000002), ([True], .5000000000000002)],
            }
            assert parsed['result']['distribution'] == [
                {'bits': bits, 'probability': probability} for bits, probability in expected[case]]


def main():
    for pattern, config in zip(MEMBERS, STUDIES, strict=True):
        stem, count, byte_count, first_count, session_sha, sums_sha, cases = config
        files, session = read_files(pattern, count, byte_count, session_sha)
        first, hashes, attempt = first_packet(files, session, first_count, sums_sha, cases)
        source_context = read_json(first['context.json'])
        frozen = datetime.fromisoformat(source_context[
            'created_at_utc' if stem == 'classical-synthesis-30' else
            'recorded_before_execution_utc' if stem == 'signal-158' else 'frozen_before_execution_utc'])
        context = read_json(files['observations/context.json'])
        identity = context['initial'] if stem == 'classical-synthesis-30' else context.get('identity', context)
        source_key = 'sources' if stem == 'signal-158' else 'source_hashes'
        assert identity[source_key] == hashes
        binaries = identity['binaries']
        assert {key: value['sha256'] for key, value in binaries.items()} == BINARY_HASHES
        collector_hash = context.get('collector_sha256', context.get('observer_sha256'))
        assert digest(files['collector.py.txt']) == session['collector_sha256'] == collector_hash
        actions = ('check',) if stem == 'quantum-relations-198' else ('check', 'run')
        expected = [(case, action) for case in cases for action in actions]
        names = [f'observations/{i:02d}-{case}-{action}.json'
                 for i, (case, action) in enumerate(expected, 1)]
        assert attempt['observations'] == names
        original_observations(files, session, names)
        previous = frozen
        for name, (case, action) in zip(names, expected, strict=True):
            event = read_json(files[name])
            before, after, started, ended, elapsed, code, stdout, stderr = event_data(event, stem)
            for snapshot in (before, after):
                assert snapshot[source_key] == hashes and snapshot['binaries'] == binaries
            started, ended = datetime.fromisoformat(started), datetime.fromisoformat(ended)
            assert previous < started <= ended and elapsed >= 0
            previous = ended
            argv = event['command']
            assert argv[:2] == [binaries['cli']['path'], action]
            assert argv[2].endswith('/stage7-' + stem + '-first/attempt-01/' + case)
            assert argv[3:] == ['--format=json', '--lean-kernel=' + binaries['kernel']['path']]
            assert stderr == '' and event['stdout'] == read_json(stdout)
            check_outcome(event['stdout'], case, action, code)
    print('First histories: 106 files, 16 unchanged sources, 20 observations; no history executed.')


if __name__ == '__main__':
    main()
