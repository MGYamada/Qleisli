#!/usr/bin/env python3
"""Bounded #46 design experiment, never a production acceptance authority.

Compare outcome-indexed CP maps after summing hidden Kraus histories. Optional
fresh VM-26 reconstruction is checked against the existing independent oracle.
No source parser, accepted handle, new protocol or guarantee is supplied here.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import datetime
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import native_harness
import test_lean_exact as exact
import test_lean_finite as finite
import test_lean_observation as observation
import test_lean_raw as raw


def conjugate(value):
    return value[:2] + [-x for x in value[2:]]


def choi(histories):
    """J_y[(out,in),(out',in')] = sum_h K_yh[out,in] conj(K_yh[out',in']).

    Public results are ordered tuples. Hidden labels/order are not public
    observations. Entries retain all off-diagonal input/output coefficients.
    """
    result = {}
    shapes = {(len(h['operator']), len(h['operator'][0])) for h in histories}
    if len(shapes) != 1:
        raise ValueError('a complete history family must have one rectangular interface')
    for history in histories:
        values = tuple(history['results'])
        vector = [value for row in history['operator'] for value in row]
        term = [[exact.oracle_mul(x, conjugate(y)) for y in vector] for x in vector]
        if values not in result:
            result[values] = term
        else:
            result[values] = [[[x + y for x, y in zip(a, b)] for a, b in zip(left, right)]
                              for left, right in zip(result[values], term)]
    # An impossible outcome denotes zero, irrespective of whether a particular
    # Kraus decomposition retains explicit zero histories for that outcome.
    return (next(iter(shapes)), {label: matrix for label, matrix in result.items()
                                if any(any(value) for row in matrix for value in row)})


def probabilities(histories):
    """POVM effects; equal probabilities alone omit the residual channel."""
    result = {}
    for history in histories:
        label = tuple(history['results'])
        matrix = history['operator']
        gram = exact.oracle_compose(exact.oracle_adjoint(matrix), matrix)
        if label not in result:
            result[label] = gram
        else:
            result[label] = [[[x + y for x, y in zip(a, b)] for a, b in zip(left, right)]
                             for left, right in zip(result[label], gram)]
    return result


def programs():
    p, op, port = observation.p, raw.op, raw.port
    z = p([port(0, [0])], operations=[op('measure_z', input=0, output=0)], results=[0])
    hh = p([port(0, [0])], operations=[op('gate', gate='h', input=0, output=1),
        op('gate', gate='h', input=1, output=2), op('measure_z', input=2, output=0)], results=[0])
    tz = p([port(0, [0])], operations=[op('gate', gate='t', input=0, output=1),
        op('measure_z', input=1, output=0)], results=[0])
    flipped = p([port(0, [0])], operations=[op('measure_z', input=0, output=0),
        op('classical_not', input=0, output=1)], results=[1])
    discard = p([port(0, [0])], operations=[op('discard', input=0)])
    discard_h = p([port(0, [0])], operations=[op('gate', gate='h', input=0, output=1),
        op('discard', input=1)])
    nondestructive = p([port(0, [0])], operations=[op('init0', output=1, wire=1),
        op('cnot', control=0, target=1, control_out=2, target_out=3),
        op('measure_z', input=3, output=0)], outputs=[2], results=[0])
    replacement = p([port(0, [0])], operations=[op('measure_z', input=0, output=0),
        op('init0', output=1, wire=1)], outputs=[1], results=[0])
    identity = p([port(0, [0])], outputs=[0], effect='unitary')
    negative_identity = p([port(0, [0])], operations=[
        op('gate', gate=gate, input=index, output=index + 1)
        for index, gate in enumerate(['z', 'x', 'z', 'x'])], outputs=[4], effect='unitary')
    phase = p([port(0, [0])], operations=[op('gate', gate='z', input=0, output=1)],
        outputs=[1], effect='unitary')
    ordered = p([port(0, [0])], operations=[op('measure_z', input=0, output=0),
        op('classical_not', input=0, output=1)], results=[0, 1])
    reversed_results = dict(ordered, classical_outputs=[1, 0])
    return dict(z=z, hh=hh, tz=tz, flipped=flipped, discard=discard,
                discard_h=discard_h, nondestructive=nondestructive, replacement=replacement,
                identity=identity, negative_identity=negative_identity, phase=phase,
                ordered=ordered, reversed_results=reversed_results)


def comparisons(histories):
    pairs = [('redundant_HH_readout', 'z', 'hh', True),
             ('unobservable_branch_phase', 'z', 'tz', True),
             ('public_result_relabeling', 'z', 'flipped', False),
             ('different_hidden_Kraus_basis', 'discard', 'discard_h', True),
             ('same_probabilities_wrong_residual', 'nondestructive', 'replacement', False),
             ('global_phase_in_CP_family_only', 'identity', 'negative_identity', True),
             ('same_branch_probability_wrong_channel', 'identity', 'phase', False),
             ('ordered_public_results', 'ordered', 'reversed_results', False)]
    result = []
    for name, left, right, expected in pairs:
        equal = choi(histories[left]) == choi(histories[right])
        if equal != expected:
            raise AssertionError((name, equal, expected))
        result.append(dict(name=name, left=left, right=right, equal=equal, expected=expected))
    # These equalities intentionally cannot be established by literal Kraus-list
    # equality; the negative residual example cannot be rejected by probability.
    assert histories['discard'] != histories['discard_h']
    assert histories['identity'] != histories['negative_identity']
    assert histories['nondestructive'] != histories['replacement']
    assert probabilities(histories['nondestructive']) == probabilities(histories['replacement'])
    assert probabilities(histories['identity']) == probabilities(histories['phase'])
    assert choi(histories['discard']) == choi(list(reversed(histories['discard'])))
    scaled = [[exact.oracle_mul(value, [0, Fraction(1, 2), 0, 0]) for value in row]
              for row in histories['identity'][0]['operator']]
    split = [dict(results=[], hidden=[index], operator=scaled) for index in [0, 1]]
    assert choi(histories['identity']) == choi(split), 'Kraus count is not a semantic label'
    zero = dict(results=[False], hidden=[], operator=[[[0, 0, 0, 0], [0, 0, 0, 0]]])
    assert choi(histories['discard']) == choi(histories['discard'] + [zero])
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native', action='store_true')
    parser.add_argument('--record', type=Path, required=True)
    args = parser.parse_args()
    cases = programs()
    histories = {name: observation.oracle(program) for name, program in cases.items()}
    results = comparisons(histories)
    log, binding = [], None
    if args.native:
        kernel_before = native_harness.source_identity()
        with tempfile.TemporaryDirectory(prefix='qleisli-instrument-meaning-') as directory:
            project = Path(directory)
            (project / 'Main.lean').write_text(observation.LEAN)
            binary = native_harness.build(project, log)
            inputs = [dict(artifact=dict(format='qleisli.raw-observing-component', version=1,
                program=program, dependencies=[], bindings=[]), classical=[], budget=10000000,
                mode='instrument') for program in cases.values()]
            payload = '\n'.join(finite.dumps(case) for case in inputs) + '\n'
            started = time.monotonic()
            run = subprocess.run([str(binary)], input=payload, text=True, capture_output=True,
                                 timeout=60, check=True)
            log.append(dict(command=[str(binary)], cwd=str(Path.cwd()), exit=run.returncode,
                            seconds=time.monotonic() - started, stderr=run.stderr))
            observed = [json.loads(line) for line in run.stdout.splitlines()]
            assert len(observed) == len(cases)
            actual = {}
            for name, row in zip(cases, observed):
                assert row['accepted'], (name, row)
                actual[name] = [dict(hidden=h['hidden'], results=h['results'], operator=[
                    [exact.decoded(value) for value in h['matrix']['entries'][offset:offset+h['matrix']['cols']]]
                    for offset in range(0, len(h['matrix']['entries']), h['matrix']['cols'])])
                    for h in row['result']['histories']]
                assert actual[name] == histories[name], name
            assert comparisons(actual) == results
            assert native_harness.source_identity() == kernel_before, 'kernel source changed'
            binding = dict(driver_sha256=hashlib.sha256(observation.LEAN.encode()).hexdigest(),
                binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                input_sha256=hashlib.sha256(payload.encode()).hexdigest(),
                stdout_sha256=hashlib.sha256(run.stdout.encode()).hexdigest(),
                stderr=run.stderr, programs=len(cases), exact_history_matches=len(actual),
                kernel_source_sha256=hashlib.sha256(json.dumps(kernel_before, sort_keys=True).encode()).hexdigest(),
                kernel_library_sha256=native_harness.digest(native_harness.LIBRARY),
                lean_toolchain=subprocess.check_output(['lake', 'env', 'lean', '--version'],
                    cwd=native_harness.PACKAGE, text=True).strip())
    report = dict(format=1, kind='untrusted-instrument-meaning-design-experiment',
        baseline_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        command=[sys.executable, *sys.argv],
        recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), max_live_qubits=2,
        comparisons=results, native=binding, commands=log,
        programs=cases, histories=histories,
        source_sha256={str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [Path(__file__), Path(observation.__file__), Path(exact.__file__),
                         Path(finite.__file__), Path(raw.__file__), Path(native_harness.__file__)]},
        limits=['not a production requested-instrument gate',
                'no source preservation or full QS/PR/RS proof',
                'no signature/type-tree/effect admission is inferred from CP equality',
                'pure operation Meaning remains phase-sensitive and Unitary-only'])
    args.record.parent.mkdir(parents=True, exist_ok=True)
    args.record.write_text(json.dumps(report, indent=2, default=str) + '\n')
    print(f'{len(results)} exact CP comparisons; native original-history matches: '
          f'{binding["exact_history_matches"] if binding else "not run"}; max 2 live qubits')


if __name__ == '__main__':
    main()
