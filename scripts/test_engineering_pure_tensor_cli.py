#!/usr/bin/env python3
"""Fresh small tensor CLI comparisons; preserved commands remain inert history.
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

from test_engineering_pure_tensor_native import (
    FIXED, dependency_ideal, dyadic, encoded, independent_discriminator,
    parent, request, retained)


def baseline():
    retained()
    independent_discriminator()


def live(cli, kernel):
    baseline()
    calls = 0
    identities = [hashlib.sha256(Path(path).read_bytes()).hexdigest() for path in (cli, kernel)]
    with tempfile.TemporaryDirectory(prefix='qleisli-pure-tensor-cli-') as directory:
        directory = Path(directory)
        artifact_path, request_path = directory / 'actual.qirf', directory / 'request.json'

        def invoke(actual, data, success=False, text=False, checker=kernel, flags_first=False):
            nonlocal calls
            artifact, request_bytes = encoded(actual), encoded(data)
            artifact_path.write_bytes(artifact)
            request_path.write_bytes(request_bytes)
            args = [cli, 'engineering', 'compare-pure-tensor', '--edition=2026', str(artifact_path),
                    '--against=' + str(request_path), '--lean-kernel=' + checker]
            if not text:
                args.insert(2 if flags_first else len(args), '--format=json')
            result = subprocess.run(args, capture_output=True, timeout=60, check=False)
            calls += 1
            assert result.returncode == (0 if success else 1) and not result.stderr, (args, result)
            if text:
                output = result.stdout.decode()
                assert 'engineering tensor bound checked:' in output
                assert 'component budgets:' in output
                assert 'six original pure artifacts, both ordered tensor equations and additive component bounds' in output
                assert 'source correspondence, exact phase agreement, control/inverse access, cleanup, instrument bound, target realization/resource bound and constitutional PR/RS: not established' in output
                assert 'sampling, algorithmic resolution and numerical runtime error: not claimed' in output
                assert hashlib.sha256(artifact).hexdigest() in output
                assert hashlib.sha256(request_bytes).hexdigest() in output
                return output
            document = json.loads(result.stdout)
            assert document['format'] == 'qleisli.result' and document['version'] == 1
            assert document['command'] == 'engineering compare-pure-tensor'
            assert document['outcome'] == ('ok' if success else 'error')
            if not success:
                assert document['result'] is None and len(document['diagnostics']) == 1
                return document
            report = document['result']
            assert not document['diagnostics']
            for field in ['claim_kind', 'metric', 'checker_profile', 'target_profile',
                          'composition', 'error_category', 'epsilon']:
                assert report[field] == data[field]
            assert report['component_epsilons'] == [data[s]['epsilon'] for s in ('left', 'right')]
            assert report['native_check_scope'] == 'six-original-pure-artifacts-ordered-tensor-equations-and-additive-component-bounds'
            assert report['identity_algorithm'] == 'sha256'
            assert report['actual_artifact_sha256'] == hashlib.sha256(artifact).hexdigest()
            assert report['ideal_artifact_sha256'] == hashlib.sha256(data['expected_artifact'].encode()).hexdigest()
            assert report['request_sha256'] == hashlib.sha256(request_bytes).hexdigest()
            assert report['component_artifact_sha256'] == [dict(
                actual=hashlib.sha256(data[s]['actual_artifact'].encode()).hexdigest(),
                ideal=hashlib.sha256(data[s]['expected_artifact'].encode()).hexdigest()) for s in ('left', 'right')]
            assert report['checker_path'] == str(Path(checker).resolve())
            assert report['checker_identity'] == 'unpinned' and 0 < report['native_exact_work'] <= 10_000_000
            for field in ['source_preservation_verified', 'exact_source_correspondence_verified',
                          'phase_agreement_verified', 'control_access_verified', 'inverse_access_verified',
                          'clean_workspace_verified', 'dirty_workspace_verified', 'resource_bound_verified',
                          'target_realization_verified', 'constitutional_pr_verified', 'constitutional_rs_verified',
                          'instrument_bound_verified']:
                assert report[field] is False
            assert report['error_categories'] == dict(implementation_distance='checked-declared-bound',
                sampling='not-claimed', algorithmic_resolution='not-claimed', numerical_runtime='not-claimed')
            assert 'verified' not in report
            return document

        actual, base = request()
        invoke(actual, base, True)
        invoke(actual, base, True, text=True)
        invoke(actual, base, True, flags_first=True)
        for options in [dict(left_phase=0, left_epsilon=0),
                        dict(left_kind='prepare', right_phase=1, right_epsilon=Fraction(7, 8)),
                        dict(left_kind='unit', right_kind='unit', left_phase=0, left_epsilon=0)]:
            a, data = request(**options)
            invoke(a, data, True)
        invoke(actual, dependency_ideal(base), True)
        for field in base:
            data = copy.deepcopy(base)
            del data[field]
            invoke(actual, data)
        for field in FIXED:
            data = copy.deepcopy(base)
            data[field] = 2 if field == 'version' else 'unrecognized'
            invoke(actual, data)
        for side in ('left', 'right'):
            for field in base[side]:
                data = copy.deepcopy(base)
                del data[side][field]
                invoke(actual, data)
        for epsilon in [0, 1, Fraction(7, 16)]:
            data = copy.deepcopy(base)
            data['epsilon'] = dyadic(epsilon)
            assert invoke(actual, data)['diagnostics'][0]['code'] in ('format', 'contract')
        for side in ('left', 'right'):
            data = copy.deepcopy(base)
            # A valid replacement child and fresh requested matrix still cannot retain an old parent.
            replacement = request(left_phase=7 if side == 'left' else 1,
                                  right_phase=7 if side == 'right' else 0,
                                  left_epsilon=2, right_epsilon=2)[1]
            data[side] = replacement[side]
            data['epsilon'] = dyadic(Fraction(int(data['left']['epsilon']['numerator']),
                2**data['left']['epsilon']['denominator_bits']) + Fraction(int(data['right']['epsilon']['numerator']),
                2**data['right']['epsilon']['denominator_bits']))
            assert invoke(actual, data)['diagnostics'][0]['code'] == 'contract'
        data = copy.deepcopy(base)
        changed = parent('bit', 'bit', 0, 1)
        data['ideal'], data['expected_artifact'] = changed['leaf'], encoded(changed['artifact']).decode()
        assert invoke(actual, data)['diagnostics'][0]['code'] == 'contract'
        for bound in [dict(numerator='-1', denominator_bits=0), dict(numerator='0', denominator_bits=1),
                      dict(numerator='2', denominator_bits=1), dict(numerator='01', denominator_bits=0),
                      dict(numerator='1', denominator_bits=127)]:
            data = copy.deepcopy(base)
            data['left']['epsilon'] = bound
            invoke(actual, data)
        invoke(actual, base, checker=str(directory / 'missing-kernel'))
        # No flag can select source execution, artifact emission or a fallback.
        artifact_path.write_bytes(encoded(actual))
        request_path.write_bytes(encoded(base))
        for extra in [('--against=duplicate',), ('--format=json',), ('--output=out',), ('extra',)]:
            args = [cli, 'engineering', 'compare-pure-tensor', '--edition=2026', str(artifact_path),
                    '--against=' + str(request_path), '--lean-kernel=' + kernel, '--format=json', *extra]
            result = subprocess.run(args, capture_output=True, timeout=60, check=False)
            calls += 1
            assert result.returncode == 2 and not result.stderr
            assert json.loads(result.stdout)['diagnostics'][0]['code'] == 'usage'
        assert not (directory / 'out').exists()
    assert identities == [hashlib.sha256(Path(path).read_bytes()).hexdigest() for path in (cli, kernel)]
    print(json.dumps(dict(status='passed', native_cli_cases=calls, maximum_physical_qubits=2,
                         checker_sha256=identities[1], cli_sha256=identities[0])))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-only', action='store_true')
    parser.add_argument('--cli')
    args = parser.parse_args()
    baseline()
    if args.baseline_only:
        print('Original tensor sources, first diagnostics and supplemental shape/budget captures retained; history not executed.')
    else:
        assert args.cli, '--cli is required for live checks'
        kernel = os.environ.get('QLEISLI_KERNEL')
        assert kernel, 'select the separately rebuilt/audited native checker'
        live(str(Path(args.cli).resolve()), str(Path(kernel).resolve()))
