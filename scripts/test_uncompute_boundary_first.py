"""Validate #72/#352 first-source evidence as inert data, never replay it.

Numerical readout cannot establish the exact scalar distinction between Z and
-Z. This reader grants no source, CPTP, cleanup or resource proof authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
from datetime import datetime
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import tomllib


ROOT = Path(__file__).resolve().parents[1]
STUDY = ROOT / 'tests/fixtures/authoring_sessions/uncompute-boundary-v030'
MEMBERS = 'tests/fixtures/authoring_sessions/uncompute-boundary-v030/**/*'
SESSION_SHA = '30cd7f9521df15f96bd1380209e303f9fba4e92dc4889d770e3b7c3dcdba531d'
FIRST_SHA = '82cb64141cbab1cc04b3fd3c8db41ccff52de4e732081c9cf6cbe6f3c6c8a10e'
CASES = ('hxh', 'xzx', 'dirty-x')


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


def json_bytes(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()


def main():
    assert STUDY.is_dir() and not STUDY.is_symlink()
    files = {}
    for path in ROOT.glob(MEMBERS):
        assert not path.is_symlink() and path.resolve().is_relative_to(STUDY.resolve())
        if path.is_dir():
            continue
        assert path.is_file() and path.stat().st_size <= 16 * 1024
        data = path.read_bytes()
        assert len(data) <= 16 * 1024
        files[path.relative_to(STUDY).as_posix()] = data
    assert len(files) == 22 and sum(map(len, files.values())) == 45713
    assert digest(files['session.json']) == SESSION_SHA
    read = lambda name: read_json(files[name])
    session = read('session.json')
    assert session['retained_sha256'] == {
        name: digest(data) for name, data in files.items() if name != 'session.json'}
    first = {name.removeprefix('first/'): data for name, data in files.items()
             if name.startswith('first/')}
    assert len(first) == 9 and digest(first['SHA256SUMS']) == FIRST_SHA
    first_inventory = {}
    for line in first['SHA256SUMS'].decode().splitlines():
        match = re.fullmatch(r'([0-9a-f]{64})  (.+)', line)
        assert match
        sha, name = match.groups()
        path = PurePosixPath(name)
        assert not path.is_absolute() and str(path) == name and '..' not in path.parts
        assert name not in first_inventory and '\\' not in name
        first_inventory[name] = sha
    assert first_inventory == {name: digest(data) for name, data in first.items()
                               if name != 'SHA256SUMS'}
    original = read_json(first['session.json'])
    assert original['status'] == 'frozen-awaiting-first-observation'
    assert session['status'] == 'first-observations-recorded'
    assert len(original['attempts']) == len(session['attempts']) == 1
    attempt = session['attempts'][0]
    assert original['attempts'][0]['observations'] == original['attempts'][0]['reports'] == []
    for field, leaf in [('sha256', 'main.qli'), ('manifest_sha256', 'Qargo.toml')]:
        assert attempt[field] == original['attempts'][0][field]
        assert set(attempt[field]) == {case + '/' + leaf for case in CASES}
        for name, sha in attempt[field].items():
            assert files['attempt-01/' + name] == first['attempt-01/' + name]
            assert digest(files['attempt-01/' + name]) == sha
    for case in CASES:
        manifest = tomllib.loads(files['attempt-01/' + case + '/Qargo.toml'].decode())
        assert manifest['schema-version'] == 2 and manifest['qrate']['edition'] == '2026'

    predicted = read_json(first['context.json'])
    assert predicted['equations']['hxh']['exact_eighth_phases'] == [0, 4]
    assert predicted['equations']['xzx']['exact_eighth_phases'] == [4, 0]
    assert 'exactly |1>' in predicted['equations']['dirty-x']['all_input_failure']
    assert 'not Lean proof results' in predicted['scope']
    context = session['observation_context']
    assert context['worktree_head'] == session['baseline_commit']
    assert context['source_hashes'] == {name: digest(data) for name, data in first.items()}
    assert 'not an attestation' in context['build_attestation']
    frozen = datetime.fromisoformat(predicted['frozen_before_execution_utc'])
    recorded = datetime.fromisoformat(context['recorded_before_invocations_utc'])
    assert frozen < recorded
    identity = {key: context[key] for key in ('source_hashes', 'binaries')}
    binaries = context['binaries']
    assert set(binaries) == {'cli', 'kernel'}
    assert all(re.fullmatch(r'[0-9a-f]{64}', value['sha256']) for value in binaries.values())
    names = [f'observations/{i + 1:02}-{case}-{action}.json' for i, (case, action) in
             enumerate((case, action) for case in CASES for action in ('check', 'run'))]
    assert attempt['observations'] == names
    for name in names:
        event = read(name)
        case, action = Path(name).stem[3:].rsplit('-', 1)
        assert event['before'] == event['after'] == identity
        assert event['timed_out'] is False and event['elapsed_seconds'] >= 0
        started = datetime.fromisoformat(event['started_utc'])
        ended = datetime.fromisoformat(event['recorded_utc'])
        assert recorded < started <= ended
        recorded = ended
        argv = event['command']
        assert argv[0] == binaries['cli']['path'] and argv[1] == action
        assert argv[2].endswith('/stage7-uncompute-72-first/attempt-01/' + case)
        assert argv[3:] == ['--format=json', '--lean-kernel=' + binaries['kernel']['path']]
        for key, raw in [('stdout', event['stdout_raw']), ('stderr', event['stderr'])]:
            assert digest(raw.encode()) == event[key + '_sha256']
        assert event['stderr'] == '' and read_json(event['stdout_raw']) == event['stdout']
        # Reconstruct the original external metadata without opening its paths.
        command = {'argv': argv, 'cwd': event['cwd'], 'started_at_utc': event['started_utc'],
                   'before': event['before']}
        result = {**command, 'ended_at_utc': event['recorded_utc'],
                  'elapsed_seconds': event['elapsed_seconds'], 'exit_code': event['exit_code'],
                  'timed_out': event['timed_out'], 'after': event['after'],
                  'stdout_sha256': event['stdout_sha256'], 'stderr_sha256': event['stderr_sha256'],
                  'stdout_json': event['stdout']}
        assert event['original_record_sha256'] == {
            'command.json': digest(json_bytes(command)), 'result.json': digest(json_bytes(result))}
        parsed = event['stdout']
        assert parsed['format'] == 'qleisli.result' and parsed['version'] == 1
        assert parsed['command'] == action
        refused = case == 'dirty-x'
        assert event['exit_code'] == (1 if refused else 0)
        assert parsed['outcome'] == ('error' if refused else 'ok')
        if refused:
            assert parsed['result'] is None
            assert [d['code'] for d in parsed['diagnostics']] == ['unsupported']
            message = parsed['diagnostics'][0]['message']
            assert 'exact eighth-root diagonal ancilla action' in message
            assert 'does not bypass cleanup checking' in message
        else:
            assert parsed['diagnostics'] == []
            if action == 'check':
                assert parsed['result']['source_preservation_verified'] is False
                assert parsed['result']['checker_identity'] == 'unpinned'
            else:
                # Preserve this actual numerical readout; it cannot distinguish Z from -Z.
                assert parsed['result']['distribution'] == [{'bits': [True], 'probability': 1}]
    print('Uncompute first history: 22 files, 3 unchanged sources, 6 observations; no history executed.')


if __name__ == '__main__':
    main()
