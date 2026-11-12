"""Check the complete #157 first-source record as inert data, never replay it.

Recorded numerical outcomes are retention evidence, not exact cleanup, source,
CPTP or resource proofs. Historical command paths are compared, never opened.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
from datetime import datetime
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import tomllib


ROOT = Path(__file__).resolve().parents[1]
STUDY = ROOT / 'tests/fixtures/authoring_sessions/clean-marginal-v030'
MEMBERS = 'tests/fixtures/authoring_sessions/clean-marginal-v030/**/*'
INVENTORY_SHA = '9981a6134feb03b01da42a2c4f15b38d1da38e53fd409f24479b31f31a3eada5'
CASES = ('coherent-uncompute', 'explicit-reset', 'false-unitary-reset')


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


def inventory(data):
    result = {}
    for line in data.decode('utf-8').splitlines():
        match = re.fullmatch(r'([0-9a-f]{64})  (.+)', line)
        assert match, 'invalid SHA256SUMS line'
        sha, name = match.groups()
        path = PurePosixPath(name)
        assert not path.is_absolute() and str(path) == name and '..' not in path.parts
        assert '\\' not in name and not any(ord(c) < 32 for c in name)
        assert name not in result, 'duplicate inventory path'
        result[name] = sha
    return result


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
    assert len(files) == 53 and sum(map(len, files.values())) == 74753
    assert digest(files['SHA256SUMS']) == INVENTORY_SHA
    expected = inventory(files['SHA256SUMS'])
    assert set(expected) == files.keys() - {'SHA256SUMS'}
    assert all(digest(files[name]) == sha for name, sha in expected.items())
    first = {name.removeprefix('first/'): data for name, data in files.items()
             if name.startswith('first/')}
    first_hashes = {name: digest(data) for name, data in first.items()}
    assert len(first) == 11
    assert inventory(first['SHA256SUMS']) == {
        name: sha for name, sha in first_hashes.items() if name != 'SHA256SUMS'}

    read = lambda name: read_json(files[name])
    session, original = read('session.json'), read_json(first['session.json'])
    assert original['status'] == 'frozen-awaiting-first-observation'
    assert session['status'] == 'first-observations-recorded'
    assert original['attempts'][0]['observations'] == original['attempts'][0]['reports'] == []
    assert len(session['attempts']) == len(original['attempts']) == 1
    attempt = session['attempts'][0]
    assert attempt['id'] == original['attempts'][0]['id'] == 'attempt-01'
    for field, leaf in [('sha256', 'main.qli'), ('manifest_sha256', 'Qargo.toml')]:
        assert attempt[field] == original['attempts'][0][field]
        assert set(attempt[field]) == {case + '/' + leaf for case in CASES}
        for name, sha in attempt[field].items():
            assert files['attempt-01/' + name] == first['attempt-01/' + name]
            assert digest(files['attempt-01/' + name]) == sha
    for case in CASES:
        manifest = tomllib.loads(files['attempt-01/' + case + '/Qargo.toml'].decode())
        assert manifest['schema-version'] == 2 and manifest['qrate']['edition'] == '2026'

    context = read('observations/context.json')
    assert context['source_hashes'] == first_hashes
    assert context['worktree_head'] == session['baseline_commit']
    assert context['worktree_status'] == ''
    binaries = context['binaries']
    assert set(binaries) == {'cli', 'kernel'}
    assert all(re.fullmatch(r'[0-9a-f]{64}', value['sha256']) for value in binaries.values())
    frozen = datetime.fromisoformat(read_json(first['context.json'])['frozen_before_execution_utc'])
    recorded = datetime.fromisoformat(context['recorded_before_invocations_utc'])
    assert frozen < recorded
    names = [f'{i + 1:02}-{case}-{command}' for i, (case, command) in
             enumerate((case, command) for case in CASES for command in ('check', 'run'))]
    summary = read('observations/observations.json')
    assert [row['name'] for row in summary] == names
    assert attempt['observations'] == ['observations/' + name + '/event.json' for name in names]
    identity = {'source_hashes': first_hashes, 'binaries': binaries}
    results = {}
    for row, name in zip(summary, names):
        prefix = 'observations/' + name + '/'
        command, result, event = (read(prefix + leaf) for leaf in
                                  ('command.json', 'result.json', 'event.json'))
        assert all(result[key] == value for key, value in command.items())
        assert set(command) == {'argv', 'cwd', 'started_at_utc', 'before'}
        assert result['before'] == result['after'] == identity
        assert row['result'] == name + '/result.json'
        assert event['raw_observation'] == prefix + 'result.json'
        assert event['command'] == result['argv'] and event['cwd'] == result['cwd']
        assert event['exit_code'] == row['exit_code'] == result['exit_code']
        assert event['recorded_utc'] == result['ended_at_utc']
        assert row['timed_out'] is result['timed_out'] is False
        started = datetime.fromisoformat(result['started_at_utc'])
        ended = datetime.fromisoformat(result['ended_at_utc'])
        assert recorded < started <= ended and result['elapsed_seconds'] >= 0
        recorded = ended
        for stream in ('stdout', 'stderr'):
            raw = files[prefix + stream + '.txt']
            assert digest(raw) == result[stream + '_sha256']
            assert event[stream] == (read_json(raw) if stream == 'stdout' else raw.decode())
        assert event['stderr'] == ''
        case, action = name[3:].rsplit('-', 1)
        argv = result['argv']
        assert argv[0] == binaries['cli']['path'] and argv[1] == action
        assert argv[2].endswith('/stage7-clean-157-marginal-first/attempt-01/' + case)
        assert argv[3:] == ['--format=json', '--lean-kernel=' + binaries['kernel']['path']]
        parsed = event['stdout']
        assert parsed['format'] == 'qleisli.result' and parsed['version'] == 1
        assert parsed['command'] == action
        rejected = case == 'false-unitary-reset'
        assert result['exit_code'] == (1 if rejected else 0)
        assert parsed['outcome'] == ('error' if rejected else 'ok')
        if rejected:
            assert parsed['result'] is None
            assert [diagnostic['code'] for diagnostic in parsed['diagnostics']] == ['effect']
            assert 'body effect `Observe` exceeds asserted `Unitary`' in parsed['diagnostics'][0]['message']
        else:
            assert parsed['diagnostics'] == []
            if action == 'check':
                assert parsed['result']['source_preservation_verified'] is False
                assert parsed['result']['checker_identity'] == 'unpinned'
        results[case, action] = parsed['result']

    # Keep the actual numerical residuals; do not round them into exact evidence.
    for case, probabilities in [('coherent-uncompute', [1, 6.162975822039156e-33]),
                                 ('explicit-reset', [0.5000000000000002] * 2)]:
        distribution = results[case, 'run']['distribution']
        assert [item['bits'] for item in distribution] == [[False, False], [True, False]]
        assert [item['probability'] for item in distribution] == probabilities
    print('Clean-marginal history: 53 files, 3 unchanged sources, 6 observations; no history executed.')


if __name__ == '__main__':
    main()
