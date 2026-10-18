#!/usr/bin/env python3
"""Compare literal canonical emitted targets with independently authored ideals.
Historical commands, paths and drivers remain inert archive data.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import copy
from fractions import Fraction
import json
import os
from pathlib import Path
import subprocess
import tempfile

from test_engineering_openqasm_native import (
    FIXED, GATES, dependency_ideal, digest, dyadic, encoded,
    hostile_targets, independent_oracle, request, retained, target, word_from_target)

COMMAND = 'engineering compare-openqasm3'
UNESTABLISHED = ('pure_phase_bound_verified', 'source_preservation_verified',
    'exact_source_correspondence_verified', 'export_preservation_verified',
    'coherent_control_verified', 'inverse_capability_verified', 'cleanup_verified',
    'resource_bound_verified', 'constitutional_pr_verified', 'constitutional_rs_verified')


def baseline():
    retained()
    independent_oracle()


def live(cli, kernel):
    baseline()
    identities = [digest(Path(p).read_bytes()) for p in (cli, kernel)]
    calls = 0
    with tempfile.TemporaryDirectory(prefix='qleisli-openqasm-cli-') as temporary:
        directory = Path(temporary)
        target_path, request_path = directory / 'actual.qasm', directory / 'request.json'

        def invoke(actual, data, success=False, text=False, checker=kernel, flags_first=False,
                   request_bytes=None):
            nonlocal calls
            target_path.write_bytes(actual)
            request_bytes = encoded(data) if request_bytes is None else request_bytes
            request_path.write_bytes(request_bytes)
            args = [cli, 'engineering', 'compare-openqasm3', str(target_path),
                    '--against=' + str(request_path), '--lean-kernel=' + checker]
            if not text:
                args.insert(2 if flags_first else len(args), '--format=json')
            result = subprocess.run(args, capture_output=True, timeout=60, check=False)
            calls += 1
            assert result.returncode == (0 if success else 1) and not result.stderr, (args, result)
            if text:
                output = result.stdout.decode()
                assert 'OpenQASM target engineering bound checked:' in output
                assert 'canonical one-qubit terminal target bytes and original ideal; Unit -> classical Bit' in output
                assert 'capacity: 1024 target bytes; 8 gate lines' in output
                assert 'source/export correspondence, pure phase agreement, coherent control, inverse, cleanup, resource bounds and constitutional PR/RS: not established' in output
                assert 'sampling, algorithmic resolution and numerical runtime error: not claimed' in output
                assert digest(actual) in output and digest(request_bytes) in output
                return output
            document = json.loads(result.stdout)
            assert document['format'] == 'qleisli.result' and document['version'] == 1
            assert document['command'] == COMMAND
            assert document['outcome'] == ('ok' if success else 'error')
            if not success:
                assert document['result'] is None and len(document['diagnostics']) == 1
                return document
            report = document['result']
            assert not document['diagnostics']
            for field in ('claim_kind', 'metric', 'checker_profile', 'target_profile',
                          'composition', 'error_category', 'epsilon', 'majorants'):
                assert report[field] == data[field]
            assert report['gate_word'] == list(word_from_target(actual))
            assert report['identity_algorithm'] == 'sha256'
            assert report['target_artifact_sha256'] == digest(actual)
            assert report['ideal_artifact_sha256'] == digest(data['expected_artifact'].encode())
            assert report['request_sha256'] == digest(request_bytes)
            assert report['checker_path'] == str(Path(checker).resolve())
            assert report['checker_identity'] == 'unpinned' and 0 < report['native_exact_work'] <= 10_000_000
            assert report['native_check_scope'] == 'canonical-target-bytes-generated-unit-instrument-original-ideal-and-complete-adjoint-bound'
            assert report['target_capacity'] == dict(max_target_bytes=1024, max_gate_count=8)
            assert report['instrument_bound_verified'] is True and report['target_artifact_bound_verified'] is True
            for field in UNESTABLISHED:
                assert report[field] is False
            assert report['error_categories'] == dict(implementation_distance='checked-declared-bound',
                sampling='not-claimed', algorithmic_resolution='not-claimed', numerical_runtime='not-claimed')
            assert 'verified' not in report
            return document

        actual, base = target(), request()
        invoke(actual, base, True)
        invoke(actual, base, True, text=True)
        invoke(actual, base, True, flags_first=True)
        invoke(target(('h',)), request(epsilon=0, majorants=(0, 0)), True)
        for name in GATES:
            invoke(target((name,)), request((name,), 0, (0, 0)), True)
        invoke(target(('h',) * 8), request((), 0, (0, 0)), True)
        invoke(actual, dependency_ideal(base), True)
        spaced = copy.deepcopy(base)
        spaced['expected_artifact'] = '\n' + spaced['expected_artifact'] + '\n'
        invoke(actual, spaced, True, request_bytes=b' ' + encoded(spaced) + b'\n')
        for _, value in hostile_targets():
            invoke(value, base)
        for field in base:
            changed = copy.deepcopy(base)
            del changed[field]
            invoke(actual, changed)
        for field in FIXED:
            changed = copy.deepcopy(base)
            changed[field] = 2 if field == 'version' else 'unsupported'
            invoke(actual, changed)
        for side in ('actual_signature', 'expected_signature'):
            for part, replacement in [('input', dict(tag='bits', width=0)),
                                      ('result', dict(tag='bits', width=1))]:
                changed = copy.deepcopy(base)
                changed[side][part] = replacement
                invoke(actual, changed)
        for epsilon in (0, Fraction(1, 2)):
            changed = copy.deepcopy(base)
            changed['epsilon'] = dyadic(epsilon)
            assert invoke(actual, changed)['diagnostics'][0]['code'] == 'contract'
        for values in ((), (Fraction(1, 4),) * 2, (Fraction(1, 2),) * 3):
            changed = copy.deepcopy(base)
            changed['majorants'] = [dyadic(v) for v in values]
            invoke(actual, changed)
        for field in ('metric', 'target_profile', 'composition'):
            changed = copy.deepcopy(base)
            del changed[field]
            invoke(actual, changed)
        for value in (dict(numerator='runtime', denominator_bits=0), dict(numerator='-1', denominator_bits=0),
                      dict(numerator='0', denominator_bits=1), dict(numerator='1', denominator_bits=127)):
            changed = copy.deepcopy(base)
            changed['epsilon'] = value
            invoke(actual, changed)
        # Valid changed target or ideal bytes cannot reuse an old zero-bound comparison.
        zero = request((), 0, (0, 0))
        invoke(target(('x',)), zero)
        changed = request(('x',), 0, (0, 0))
        invoke(actual, changed)
        invoke(actual, base, checker=str(directory / 'missing-kernel'))
        for field, value in (('accepted', True), ('resource_bound', 0), ('gate_word', [])):
            invoke(actual, dict(base, **{field: value}))
        # Exercise the real existing exporter with freshly authored source and explicit Unit entry.
        for name, expression, word, budget, majorants in [
            ('actual', 'init0()', (), 1, (Fraction(1, 2), Fraction(1, 2))),
            ('ideal', 'h(init0())', ('h',), 0, (0, 0))]:
            project = directory / name
            project.mkdir()
            (project / 'Qargo.toml').write_text('schema-version = 2\n\n[qrate]\nedition = "2026"\n')
            (project / 'main.qli').write_text(
                '// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0\n'
                'use std::state::init0;\n\n'
                'observe fn operation(u: Q<Unit>) -> Bit { finish(u); measure_z(' + expression + ') }\n'
                'observe fn main() -> Bit { operation(unit(())) }\n')
            result = subprocess.run([cli, 'interop', 'emit-qasm', str(project), '--input=qli',
                '--lean-kernel=' + kernel, '--format=json'], capture_output=True, timeout=60, check=False)
            calls += 1
            assert result.returncode == 0 and not result.stderr, result
            document = json.loads(result.stdout)
            assert document['outcome'] == 'ok' and not document['diagnostics']
            emitted = document['result']['text'].encode()
            assert emitted == target(word)
            invoke(emitted, request(epsilon=budget, majorants=majorants), True)
        target_path.write_bytes(actual)
        request_path.write_bytes(encoded(base))
        for extra in (('--against=duplicate',), ('--format=json',), ('--output=out',), ('extra',)):
            result = subprocess.run([cli, 'engineering', 'compare-openqasm3', str(target_path),
                '--against=' + str(request_path), '--lean-kernel=' + kernel, '--format=json', *extra],
                capture_output=True, timeout=60, check=False)
            calls += 1
            assert result.returncode == 2 and not result.stderr
            assert json.loads(result.stdout)['diagnostics'][0]['code'] == 'usage'
        assert not (directory / 'out').exists()
    assert identities == [digest(Path(p).read_bytes()) for p in (cli, kernel)]
    print(json.dumps(dict(status='passed', native_cli_cases=calls, maximum_physical_qubits=1,
        cli_sha256=identities[0], kernel_sha256=identities[1],
        comparison_script_sha256=digest(Path(__file__).read_bytes()))))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-only', action='store_true')
    parser.add_argument('--cli')
    parser.add_argument('--kernel', default=os.environ.get('QLEISLI_KERNEL'))
    args = parser.parse_args()
    if args.baseline_only:
        baseline()
        print('Original target sources, first failures and literal export bytes retained; history not executed.')
    else:
        assert args.cli and args.kernel, 'select the CLI and separately rebuilt/audited checker'
        live(str(Path(args.cli).resolve()), str(Path(args.kernel).resolve()))
