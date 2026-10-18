#!/usr/bin/env python3
"""Retain exact phase/instrument first evidence without executing its history.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import base64
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
INSTRUMENT = ROOT / 'tests/fixtures/authoring_sessions/engineering-instrument-v030/first-observations.json'
INSTRUMENT_NOTES = ROOT / 'tests/fixtures/authoring_sessions/engineering-instrument-v030/README.md'
PHASE = ROOT / 'tests/fixtures/authoring_sessions/exact-pi8-v030/first-observations.json'
PHASE_NOTES = ROOT / 'tests/fixtures/authoring_sessions/exact-pi8-v030/README.md'
PHASE_CURRENT = ROOT / 'tests/fixtures/authoring_sessions/exact-pi8-v030/current-language-primitives'


def capture(path, notes, expected_hash, expected_format, count, binaries):
    assert '`first-observations.json`' in notes.read_text()
    original = path.read_bytes()
    assert hashlib.sha256(original).hexdigest() == expected_hash
    data = json.loads(original)
    assert data['format'] == expected_format and data['version'] == 1
    assert data['kind'] == 'informed-study'
    assert len(data['files']) == count
    files = {}
    binary_count = 0
    for row in data['files']:
        name = row['path']
        assert not PurePosixPath(name).is_absolute()
        assert '..' not in PurePosixPath(name).parts and name not in files
        assert row['mode'] in (0o644, 0o755)
        assert ('utf8' in row) != ('base64' in row)
        if 'utf8' in row:
            content = row['utf8'].encode('utf-8')
        else:
            content = base64.b64decode(row['base64'], validate=True)
            binary_count += 1
        assert hashlib.sha256(content).hexdigest() == row['sha256']
        files[name] = content
    assert binary_count == binaries
    return files


def instrument():
    files = capture(INSTRUMENT, INSTRUMENT_NOTES,
        '9fc83442ac18bb49d53c65bf09a9d7650b8a0b9f528d021f6b118945d1bd1e0c',
        'qleisli.engineering-instrument-first-capture', 67, 8)
    first = json.loads(files['study.before.json'])
    assert hashlib.sha256(files['study.before.json']).hexdigest() == (
        '7eb96ac45616e94eeb88fd79e303afae830d8cdc41e6e1f0e02c44a06f86bac1')
    assert first['max_live_physical_quantum_bits'] == 2
    for case in first['cases']:
        prefix = 'attempt-01/' + case['name'] + '/'
        for field, name in [('source_sha256', 'main.qli'),
                            ('manifest_sha256', 'Qargo.toml'),
                            ('prediction_sha256', 'prediction.txt')]:
            assert hashlib.sha256(files[prefix + name]).hexdigest() == case[field]
        refused = json.loads(files['observations/' + case['name'] + '.check.json'])
        assert refused['exit_code'] == 1 and not refused['stderr']
        assert json.loads(refused['stdout'])['diagnostics'][0]['code'] == 'name'
    summary = json.loads(files['assessment.after.json'])
    for name, row in summary['files'].items():
        assert hashlib.sha256(files[name]).hexdigest() == row['sha256']
        assert len(files[name]) == row['bytes']
    before = json.loads(files['native-first/before.json'])
    observed = json.loads(files['native-first/observed.json'])
    assert len(before['tests']) == len(observed) == 8
    for prediction, actual in zip(before['tests'], observed):
        assert prediction['name'] == actual['name']
        assert actual['exit_code'] == (0 if prediction['accepted_prediction'] else 1)
        assert not actual['stderr']
        assert hashlib.sha256(files['native-first/' + actual['name'] + '.qlv2']).hexdigest() == actual['packet_sha256']
        for field in ['actual', 'expected']:
            assert hashlib.sha256(files['native-first/' + prediction[field] + '.qirf']).hexdigest() == prediction[field + '_sha256']
    unsupported = json.loads(files['native-first/unsupported.observed.json'])
    assert unsupported['exit_code'] == 1
    assert unsupported['stdout'] == 'qleisli.qirf-native 2\nerror\ninvalid_ir\n'
    host = json.loads(files['host-exact.observed.json'])
    for key, total, epsilon, sufficient in [
        ('unit_half', '1/2', '1/2', True), ('unit_tight', '1/2', '1/4', False),
        ('q_conservative', '2', '2', True), ('q_tighter', '2', '1', False),
    ]:
        assert host[key]['sum'] == total and host[key]['epsilon'] == epsilon
        assert host[key]['mathematical_sufficient_inequality'] is sufficient
    assert host['bell_residual']['probability_same_but_coherence_differs']
    assert host['bell_residual']['ideal_false'][0][3] == '1/2'
    assert host['bell_residual']['reset_false'][0][3] == '0'


def phase():
    files = capture(PHASE, PHASE_NOTES,
        '29dfe905de1b3594fb36d925419797aef7dda5302c3cd828bad8d280bcf16d9c',
        'qleisli.exact-pi8-first-capture', 25, 0)
    assert hashlib.sha256(files['study.before.json']).hexdigest() == (
        '5b757f7a5a97e39e0782f552fc7805600f9c5486f81f970bbfc7e3460d440bbb')
    summary = json.loads(files['assessment.after.json'])
    assert summary['first_sources_unchanged'] and summary['source_repairs'] == 0
    assert summary['maximum_physical_quantum_width'] == 1
    proposal = json.loads(files['pi8.proposal.json'])
    assert proposal['profile'] == 'qpe-dyadic8-v1'
    assert proposal['definitions'][0]['body'] == {
        'tag': 'dyadic_phase', 'j': 1, 'k': 4, 'target': 101}
    assert proposal['meanings'][0]['body'] == {'tag': 'phase', 'j': 1, 'k': 4}
    observations = json.loads(files['observations.json'])['observations']
    expected = {'ordinary-pi8': 1, 'raw-pi8': 1, 'hierarchy-pi8': 0,
                'proposal-pi8': 2, 'hierarchy-run-pi8': 0, 'hierarchy-outside': 1}
    assert len(observations) == len(expected)
    for observation in observations:
        label = observation['label']
        assert observation['exit_code'] == expected[label]
        for stream in ['stdout', 'stderr']:
            assert hashlib.sha256(files[label + '.' + stream + '.txt']).hexdigest() == observation[stream + '_sha256']
    repaired = json.loads(files['followup.observations.json'])
    original = next(row for row in observations if row['label'] == 'proposal-pi8')
    assert repaired['argv'] == [arg for arg in original['argv'] if not arg.startswith('--lean-kernel=')]
    assert repaired['exit_code'] == 0
    assert repaired['source_sha256'] == repaired['source_sha256_after']
    return files



def phase_current(files):
    """Read the two fixed current translations; history remains immutable."""
    index = json.loads((PHASE_CURRENT / 'translation-index.json').read_bytes())
    assert index['format'] == 'qleisli.exact-pi8-current-translations'
    assert index['version'] == 1
    assert index['history'] == PHASE.relative_to(ROOT).as_posix()
    assert index['history_sha256'] == hashlib.sha256(PHASE.read_bytes()).hexdigest()
    names = ['pi8', 'outside-profile']
    assert [row['name'] for row in index['sources']] == names
    expected = {name + '/' + leaf for name in names for leaf in ['main.qli', 'Qargo.toml']}
    assert {path.relative_to(PHASE_CURRENT).as_posix()
            for path in PHASE_CURRENT.rglob('*') if path.suffix in ['.qli', '.toml']} == expected
    current = {}
    for row, name in zip(index['sources'], names):
        assert row['original_source'] == row['current_source'] == name + '/main.qli'
        assert row['manifest'] == name + '/Qargo.toml'
        original = files[row['original_source']]
        assert hashlib.sha256(original).hexdigest() == row['original_source_sha256']
        for leaf, hash_field in [('main.qli', 'current_source_sha256'),
                                 ('Qargo.toml', 'manifest_sha256')]:
            path = PHASE_CURRENT / name / leaf
            assert path.resolve() == path and path.is_file()
            content = path.read_bytes()
            assert hashlib.sha256(content).hexdigest() == row[hash_field]
            current[name + '/' + leaf] = content
        source = current[name + '/main.qli']
        start, end = row['removed_import_span']
        assert type(start) is int and type(end) is int and 0 <= start < end <= len(original)
        assert original[start:end] == b'use std::quantum::phase;'
        assert source[:start] == original[:start] and source[start:] == original[end:]
        assert current[name + '/Qargo.toml'] == files[name + '/Qargo.toml']
    return current


def phase_live(cli, kernel):
    """Fresh commands authored here; no historical argv/path is consumed."""
    files = phase_current(phase())
    with tempfile.TemporaryDirectory(prefix='qleisli-exact-pi8-live-') as directory:
        directory = Path(directory)
        for name in ['pi8', 'outside-profile']:
            target = directory / name
            target.mkdir()
            for filename in ['main.qli', 'Qargo.toml']:
                (target / filename).write_bytes(files[name + '/' + filename])
        calls = 0

        def invoke(command, source, profile, expected, code=None):
            nonlocal calls
            args = [cli, command, '--entry=main::f',
                    '--module=main=' + str(directory / source / 'main.qli'),
                    '--ir-profile=' + profile, '--format=json']
            if command == 'emit-proposal':
                args.append('--output=' + str(directory / 'proposal.json'))
            else:
                args.append('--lean-kernel=' + kernel)
            result = subprocess.run(args, capture_output=True, timeout=60, check=False)
            calls += 1
            assert result.returncode == expected and not result.stderr, result
            document = json.loads(result.stdout)
            if code:
                assert document['outcome'] == 'error' and document['result'] is None
                assert document['diagnostics'][0]['code'] == code
            else:
                assert document['outcome'] == 'ok' and document['diagnostics'] == []
            return document

        report = invoke('check', 'pi8', 'hierarchy', 0)['result']
        assert report['verification']['scope'] == 'producer-consistency'
        assert report['request_checked'] is True
        assert report['source_preservation_verified'] is False
        assert report['verification']['source_meaning_verified'] is False
        invoke('emit-proposal', 'pi8', 'hierarchy', 0)
        proposal = json.loads((directory / 'proposal.json').read_bytes())
        assert proposal['profile'] == 'qpe-dyadic8-v1'
        assert proposal['definitions'][0]['body'] == {
            'tag': 'dyadic_phase', 'j': 1, 'k': 4, 'target': 101}
        assert proposal['meanings'][0]['body'] == {'tag': 'phase', 'j': 1, 'k': 4}
        invoke('check', 'pi8', 'raw', 1, 'unsupported')
        invoke('check', 'outside-profile', 'hierarchy', 1, 'limit')
        print(json.dumps({'fresh_symbolic_profile_cases': calls,
                          'maximum_physical_qubits': 1, 'status': 'passed'}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--pi8-live', action='store_true')
    parser.add_argument('--cli')
    args = parser.parse_args()
    instrument()
    phase()
    if args.pi8_live:
        assert args.cli and os.environ.get('QLEISLI_KERNEL')
        phase_live(str(Path(args.cli).resolve()),
                   str(Path(os.environ['QLEISLI_KERNEL']).resolve()))
    print('Instrument and pi/8 first sources, binary packets and actual diagnostics retained; history not executed.')
