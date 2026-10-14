#!/usr/bin/env python3
"""Static first-client retention and live small native engineering CLI checks.
Historical argv and paths are never executed or followed.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / 'tests/fixtures/authoring_sessions/engineering-pure-native-v030/first-observations.json'
NOTES = ROOT / 'tests/fixtures/authoring_sessions/engineering-pure-native-v030/README.md'


def baseline():
    notes = NOTES.read_text()
    assert '`first-observations.json`' in notes
    data = json.loads(CAPTURE.read_text())
    assert data['format'] == 'qleisli.engineering-pure-first-capture' and data['version'] == 1
    assert data['baseline_commit'] == '216ebf03d62f5f490ecd6e8097e037d1d5dfe98c'
    names = {'before.json', 'first-client.json', 'new-cli-original-request.json',
             'translation-before.json', 'translated-observation.json'}
    assert len(data['files']) == len(names)
    assert {row['path'] for row in data['files']} == names
    files = {}
    for row in data['files']:
        assert row['mode'] == 420
        assert hashlib.sha256(row['utf8'].encode()).hexdigest() == row['sha256']
        files[row['path']] = json.loads(row['utf8'])
    before = files['before.json']
    first = copy.deepcopy(files['first-client.json'])
    observation = first.pop('observation')
    assert first == before
    assert observation['returncode'] == 2 and not observation['stderr']
    assert json.loads(observation['stdout'])['diagnostics'][0]['code'] == 'usage'
    for value in before['inputs'].values():
        assert hashlib.sha256(value['utf8'].encode()).hexdigest() == value['sha256']
    original = json.loads(before['inputs']['request.json']['utf8'])
    assert original['domain'] == ['bit'] and original['codomain'] == ['bit']
    refusal = files['new-cli-original-request.json']
    assert refusal['exit_code'] == 1 and not refusal['stderr']
    assert json.loads(refusal['stdout'])['diagnostics'][0]['code'] == 'format'
    translation = files['translation-before.json']
    assert hashlib.sha256(translation['request_utf8'].encode()).hexdigest() == translation['request_sha256']
    repaired = copy.deepcopy(original)
    repaired['domain'] = repaired['codomain'] = {'tag': 'bit'}
    assert json.loads(translation['request_utf8']) == repaired
    success = files['translated-observation.json']
    assert success['exit_code'] == 0 and not success['stderr']
    report = json.loads(success['stdout'])['result']
    assert report['claim_kind'] == 'engineering'
    assert report['request_sha256'] == translation['request_sha256']
    actual = before['inputs']['actual.qirf']['utf8'].encode()
    assert report['actual_artifact_sha256'] == hashlib.sha256(actual).hexdigest()
    assert report['ideal_artifact_sha256'] == hashlib.sha256(repaired['expected_artifact'].encode()).hexdigest()
    assert not report['exact_source_correspondence_verified'] and not report['resource_bound_verified']
    return actual, repaired


def live(cli, kernel):
    actual, original = baseline()
    count = 0
    with tempfile.TemporaryDirectory(prefix='qleisli-engineering-cli-') as directory:
        directory = Path(directory)
        artifact = directory / 'actual.qirf'
        request_path = directory / 'request.json'
        artifact.write_bytes(actual)

        def invoke(request, *, success, text=False, checker=kernel, extra=()):
            nonlocal count
            request_bytes = (json.dumps(request, separators=(',', ':'), sort_keys=True) + '\n').encode()
            request_path.write_bytes(request_bytes)
            args = [cli, 'engineering', 'compare-pure', str(artifact),
                    '--against=' + str(request_path), '--lean-kernel=' + checker]
            if not text:
                args.append('--format=json')
            result = subprocess.run(args + list(extra), capture_output=True, timeout=60, check=False)
            count += 1
            assert result.returncode == (0 if success else 1), (args, result)
            if text:
                assert not result.stderr
                output = result.stdout.decode()
                assert 'engineering bound checked:' in output
                assert 'source correspondence, instrument bound and target resource bound: not established' in output
                assert hashlib.sha256(actual).hexdigest() in output
                return output
            assert not result.stderr, result
            document = json.loads(result.stdout)
            assert document['command'] == 'engineering compare-pure'
            assert document['outcome'] == ('ok' if success else 'error')
            if not success:
                assert document['result'] is None and len(document['diagnostics']) == 1
                return document
            report = document['result']
            assert document['diagnostics'] == []
            assert report['claim_kind'] == 'engineering'
            assert report['metric'] == 'pure-euclidean-operator-norm-v1'
            assert report['target_profile'] == 'qirf-r8-pure-v1'
            assert report['composition'] == 'single-component-v1'
            assert report['epsilon'] == request['epsilon']
            assert report['actual_artifact_sha256'] == hashlib.sha256(actual).hexdigest()
            assert report['ideal_artifact_sha256'] == hashlib.sha256(request['expected_artifact'].encode()).hexdigest()
            assert report['request_sha256'] == hashlib.sha256(request_bytes).hexdigest()
            assert report['checker_path'] == str(Path(checker).resolve())
            assert report['checker_identity'] == 'unpinned' and 0 < report['native_exact_work'] <= 10_000_000
            for name in ['source_preservation_verified', 'exact_source_correspondence_verified',
                         'resource_bound_verified', 'instrument_bound_verified']:
                assert report[name] is False
            assert report['error_categories'] == {
                'implementation_distance': 'checked-declared-bound', 'sampling': 'not-claimed',
                'algorithmic_resolution': 'not-claimed', 'numerical_runtime': 'not-claimed'}
            assert 'verified' not in report
            return document

        invoke(original, success=True)
        invoke(original, success=True, text=True)
        tight = copy.deepcopy(original)
        tight['epsilon'] = {'numerator': '1', 'denominator_bits': 1}
        assert invoke(tight, success=False)['diagnostics'][0]['code'] == 'contract'
        zero = copy.deepcopy(original)
        zero['ideal'] = copy.deepcopy(zero['actual'])
        zero['expected_artifact'] = actual.decode()
        zero['epsilon'] = {'numerator': '0', 'denominator_bits': 0}
        invoke(zero, success=True)
        for field in original:
            missing = copy.deepcopy(original)
            del missing[field]
            invoke(missing, success=False)
        for field in ['claim_kind', 'metric', 'checker_profile', 'target_profile', 'composition', 'error_category']:
            changed = copy.deepcopy(original)
            changed[field] = 'unrecognized-profile'
            invoke(changed, success=False)
        wrong_tree = copy.deepcopy(original)
        wrong_tree['domain'] = {'tag': 'bits', 'width': 1}
        assert invoke(wrong_tree, success=False)['diagnostics'][0]['code'] == 'contract'
        stale = copy.deepcopy(original)
        stale['actual']['matrix'] = copy.deepcopy(stale['ideal']['matrix'])
        assert invoke(stale, success=False)['diagnostics'][0]['code'] == 'contract'
        for bound in [
            {'numerator': '-1', 'denominator_bits': 0},
            {'numerator': '0', 'denominator_bits': 1},
            {'numerator': '2', 'denominator_bits': 1},
            {'numerator': '01', 'denominator_bits': 0},
            {'numerator': '1', 'denominator_bits': 127},
        ]:
            invalid = copy.deepcopy(original)
            invalid['epsilon'] = bound
            invoke(invalid, success=False)
        invoke(original, success=False, checker=str(directory / 'missing-kernel'))
        # Flags never select a fallback, source execution or artifact emission.
        for extra in [('--against=duplicate',), ('--format=json',), ('--output=out',), ('extra',)]:
            request_path.write_text(json.dumps(original))
            result = subprocess.run([cli, 'engineering', 'compare-pure', str(artifact),
                '--against=' + str(request_path), '--format=json', '--lean-kernel=' + kernel,
                *extra], capture_output=True, timeout=60, check=False)
            count += 1
            assert result.returncode == 2 and not result.stderr
            assert json.loads(result.stdout)['diagnostics'][0]['code'] == 'usage'
        assert not (directory / 'out').exists()
    print(json.dumps({'native_cli_cases': count, 'max_physical_qubits': 1, 'status': 'passed'}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--baseline-only', action='store_true')
    parser.add_argument('--cli')
    args = parser.parse_args()
    baseline()
    if args.baseline_only:
        print('Original first CLI inputs, diagnostics and separate Basis repair retained; history not executed.')
    else:
        assert args.cli, '--cli is required for live checks'
        kernel = os.environ.get('QLEISLI_KERNEL')
        assert kernel, 'select the separately built/audited native kernel'
        live(str(Path(args.cli).resolve()), str(Path(kernel).resolve()))
