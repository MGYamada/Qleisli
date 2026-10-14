#!/usr/bin/env python3
"""Fresh small instrument CLI comparisons using immutable original input data.
Historical commands, paths and host drivers are never executed.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import copy
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

from test_engineering_boundary_baseline import capture, INSTRUMENT, INSTRUMENT_NOTES, ROOT

CAPTURE = ROOT / 'tests/fixtures/authoring_sessions/engineering-instrument-native-v030/first-observations.json'
NOTES = ROOT / 'tests/fixtures/authoring_sessions/engineering-instrument-native-v030/README.md'


def baseline():
    files = capture(CAPTURE, NOTES,
        '1a23bf83513679132b13df4ea7506ed72cae4bd26bc6ec50ed73f524f53342ef',
        'qleisli.engineering-instrument-native-first-capture', 38, 0)
    observed = json.loads(files['api/observed.before.json'])
    assert observed['baseline'] == 'b754d211277c8b3b893cd3675ed834c5aded7f91'
    assert hashlib.sha256(files['api/main.qli']).hexdigest() == observed['source_sha256']
    assert [row['exit_code'] for row in observed['records']] == [0, 2]
    assert not any(row['stderr'] for row in observed['records'])
    checked = json.loads(observed['records'][0]['stdout'])
    assert checked['outcome'] == 'ok'
    assert checked['result']['source_preservation_verified'] is False
    native = json.loads(files['native/before.json'])
    assert native['base_commit'] == observed['baseline']
    for name, digest in native['files'].items():
        assert hashlib.sha256(files['native/' + name]).hexdigest() == digest
    before = next(row for row in native['commands'] if row['name'] == 'native-before')
    assert before['exit_code'] == 1
    assert json.loads(before['stdout'])['code'] == 'io'
    cli = json.loads(files['cli/before.json'])
    assert cli['exit_code'] == 2
    assert hashlib.sha256(files['cli/engineering.before.rs.txt']).hexdigest() == cli['source_sha256']
    assert not files['cli/first.stderr.txt']
    document = json.loads(files['cli/first.stdout.txt'])
    assert document['command'] == 'engineering compare-pure'
    assert document['diagnostics'][0]['code'] == 'usage'
    for prefix, source in [('pure', 'PureConjugation.lean'),
                           ('contraction', 'ContractionV1.lean'),
                           ('composition', 'CompositionV1.lean'), ('tensor', 'TensorV1.lean')]:
        record = json.loads(files['composition/' + prefix + '-attempt01.validation.json'])
        assert record['exit_code'] == (0 if prefix == 'composition' else 1)
        assert hashlib.sha256(files['composition/' + source]).hexdigest() == record['source_sha256']
        for stream in ['stdout', 'stderr']:
            if stream + '_sha256' in record:
                assert hashlib.sha256(files['composition/' + prefix + '-attempt01.' + stream + '.txt']).hexdigest() == record[stream + '_sha256']
    return files


def retained_inputs():
    return capture(INSTRUMENT, INSTRUMENT_NOTES,
        '9fc83442ac18bb49d53c65bf09a9d7650b8a0b9f528d021f6b118945d1bd1e0c',
        'qleisli.engineering-instrument-first-capture', 67, 8)


def dyadic(value):
    value = Fraction(value)
    denominator = value.denominator
    assert denominator > 0 and denominator & (denominator - 1) == 0
    return {'numerator': str(value.numerator),
            'denominator_bits': denominator.bit_length() - 1}


def request(files, name, epsilon, majorants):
    # Select fixed original DATA, not recorded commands or filesystem locations.
    original = json.loads(files['native-first/' + name + '.request.json'])
    return {
        'format': 'qleisli.engineering-instrument-request', 'version': 1,
        'claim_kind': 'engineering-instrument-bound',
        'metric': 'complete-adjoint-euclidean-operator-norm-v1',
        'checker_profile': 'choi-l1-r8-instrument-v1',
        'target_profile': 'qirf-r8-instrument-v1',
        'composition': 'single-component-v1', 'error_category': 'implementation-distance',
        'actual_signature': original['actual_signature'],
        'expected_signature': original['expected_signature'],
        'identity': original['identity'], 'epsilon': dyadic(epsilon),
        'majorants': [dyadic(value) for value in majorants],
        'expected_artifact': original['expected_artifact'],
    }


def live(cli, kernel):
    baseline()
    files = retained_inputs()
    calls = 0
    with tempfile.TemporaryDirectory(prefix='qleisli-instrument-cli-') as directory:
        directory = Path(directory)
        artifact = directory / 'actual.qirf'
        request_path = directory / 'request.json'

        def invoke(actual_name, data, *, success, text=False, checker=kernel,
                   extra=(), flags_first=False):
            nonlocal calls
            actual = files['native-first/' + actual_name + '.qirf']
            artifact.write_bytes(actual)
            request_bytes = (json.dumps(data, separators=(',', ':'), sort_keys=True) + '\n').encode()
            request_path.write_bytes(request_bytes)
            args = [cli, 'engineering', 'compare-instrument', str(artifact),
                    '--against=' + str(request_path), '--lean-kernel=' + checker]
            if not text:
                args.insert(2 if flags_first else len(args), '--format=json')
            result = subprocess.run(args + list(extra), capture_output=True, timeout=60, check=False)
            calls += 1
            assert result.returncode == (0 if success else 1), (args, result)
            if text:
                assert not result.stderr
                output = result.stdout.decode()
                assert 'instrument engineering bound checked:' in output
                assert 'pure phase agreement, coherent control, inverse, clean release and target resource bounds: not established' in output
                assert 'sampling, algorithmic resolution and numerical runtime error: not claimed' in output
                assert hashlib.sha256(actual).hexdigest() in output
                return output
            assert not result.stderr, result
            document = json.loads(result.stdout)
            assert document['command'] == 'engineering compare-instrument'
            assert document['outcome'] == ('ok' if success else 'error')
            if not success:
                assert document['result'] is None and len(document['diagnostics']) == 1
                return document
            report = document['result']
            assert document['diagnostics'] == []
            for field in ['claim_kind', 'metric', 'checker_profile', 'target_profile',
                          'composition', 'error_category', 'epsilon']:
                assert report[field] == data[field]
            assert report['native_check_scope'] == 'both-original-instruments-and-complete-adjoint-bound'
            assert report['instrument_bound_verified'] is True
            for field in ['pure_phase_bound_verified', 'source_preservation_verified',
                          'exact_source_correspondence_verified', 'coherent_control_verified',
                          'inverse_capability_verified', 'cleanup_verified', 'resource_bound_verified',
                          'constitutional_pr_verified', 'constitutional_rs_verified']:
                assert report[field] is False
            assert report['actual_artifact_sha256'] == hashlib.sha256(actual).hexdigest()
            assert report['ideal_artifact_sha256'] == hashlib.sha256(data['expected_artifact'].encode()).hexdigest()
            assert report['request_sha256'] == hashlib.sha256(request_bytes).hexdigest()
            assert report['checker_path'] == str(Path(checker).resolve())
            assert report['checker_identity'] == 'unpinned'
            assert 0 < report['native_exact_work'] <= 10_000_000
            assert report['error_categories'] == {
                'implementation_distance': 'checked-declared-bound', 'sampling': 'not-claimed',
                'algorithmic_resolution': 'not-claimed', 'numerical_runtime': 'not-claimed'}
            assert 'verified' not in report
            return document

        unit = request(files, 'unit-random-vs-false', '1/2', ['1/4', '1/4'])
        invoke('unit-random', unit, success=True)
        invoke('unit-random', unit, success=True, text=True)
        invoke('unit-random', unit, success=True, flags_first=True)
        tight = copy.deepcopy(unit)
        tight['epsilon'] = dyadic('1/4')
        assert invoke('unit-random', tight, success=False)['diagnostics'][0]['code'] == 'contract'
        zero = request(files, 'unit-false-self', 0, [0, 0])
        invoke('unit-false', zero, success=True)
        host = json.loads(files['host-exact.observed.json'])
        residual = request(files, 'q-random-vs-false', 2, host['q_conservative']['majorants'])
        invoke('q-random', residual, success=True)
        residual['epsilon'] = dyadic(1)
        invoke('q-random', residual, success=False)
        # Same public probabilities cannot hide the changed residual/reference map.
        reset = request(files, 'q-reset-vs-false', 0, [0] * 32)
        invoke('q-reset', reset, success=False)
        for majorants in [[], unit['majorants'][:-1], unit['majorants'] + [dyadic(0)]]:
            malformed = copy.deepcopy(unit)
            malformed['majorants'] = majorants
            invoke('unit-random', malformed, success=False)
        malformed = copy.deepcopy(unit)
        malformed['majorants'][0] = dyadic('-1/4')
        invoke('unit-random', malformed, success=False)
        invoke('unit-random', unit, success=False, checker=str(directory / 'missing-kernel'))
        for extra in [('--against=duplicate',), ('--format=json',), ('--output=out',), ('extra',)]:
            result = subprocess.run([cli, 'engineering', 'compare-instrument', str(artifact),
                '--against=' + str(request_path), '--format=json', '--lean-kernel=' + kernel,
                *extra], capture_output=True, timeout=60, check=False)
            calls += 1
            assert result.returncode == 2 and not result.stderr, result
            document = json.loads(result.stdout)
            assert document['command'] == 'engineering compare-instrument'
            assert document['diagnostics'][0]['code'] == 'usage'
        assert not (directory / 'out').exists()
    print(json.dumps({'native_instrument_cli_cases': calls,
                      'max_physical_qubits': 2, 'status': 'passed'}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--baseline-only', action='store_true')
    parser.add_argument('--cli')
    args = parser.parse_args()
    baseline()
    if args.baseline_only:
        print('First API/native/CLI sources and real diagnostics retained; history not executed.')
    else:
        kernel = os.environ.get('QLEISLI_KERNEL')
        assert args.cli and kernel, 'select the CLI and separately built/audited native checker'
        live(str(Path(args.cli).resolve()), str(Path(kernel).resolve()))
