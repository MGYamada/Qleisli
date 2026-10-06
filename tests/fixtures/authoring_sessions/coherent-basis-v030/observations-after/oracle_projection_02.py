"""Append public-entry observations and finish the ordered-join oracle.

The initial capture/analysis/driver are immutable, including their oracle
failure and private-entry visibility refusals. Commands below are authored.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import time

BASE = Path(__file__).resolve().parent.parent
ROOT = BASE.parents[3]
CLI = Path('/private/tmp/qleisli-bounded-validation-target/debug/qleisli')
NATIVE = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
EXPECTED_CLI = '4c58a0b51360b99433ea75259967875c40d0caf872e2dc2981616c08d9c7db50'
EXPECTED_NATIVE = '39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85'
TOLERANCE = 1e-12


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, data):
    assert not path.exists(), 'Refusing to overwrite a supplemental record'
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')


def stamp():
    return datetime.now(timezone.utc).isoformat()


def permutation_oracle(path):
    """Literal two-axis H/+1-map/measurement reference with ordered join.

    Joining owners concatenates their ordered axis lists and changes no
    amplitude. The permutation is independently derived from (a,a xor b),
    using a as the low bit, rather than treating the emitted table as truth.
    """
    data = json.loads(path.read_text())
    assert data['format'] == 'qleisli.finite-ir' and data['version'] == 2
    program = data['programs'][data['root']]
    assert not program['quantum_inputs'] and not program['quantum_outputs']
    state, width = [1 + 0j], 0
    owners, issued, measurements = {}, set(), []
    snapshot, observed_table, joins = None, None, []

    def owner(token, axes):
        assert token not in issued
        issued.add(token)
        owners[token] = tuple(axes)

    for operation in program['operations']:
        tag = operation['tag']
        assert not measurements or tag == 'measure_z'
        if tag == 'init0':
            assert operation['wire'] == width
            state += [0j] * len(state)
            owner(operation['output'], (width,))
            width += 1
        elif tag == 'gate':
            axes = owners.pop(operation['input'])
            assert len(axes) == 1 and operation['gate'] == 'h'
            axis = axes[0]
            output = [0j] * len(state)
            for label, amplitude in enumerate(state):
                output[label & ~(1 << axis)] += amplitude / math.sqrt(2)
                output[label | (1 << axis)] += amplitude * (-1 if label >> axis & 1 else 1) / math.sqrt(2)
            state = output
            owner(operation['output'], axes)
        elif tag == 'join':
            left = owners.pop(operation['left'])
            right = owners.pop(operation['right'])
            assert not set(left) & set(right)
            owner(operation['output'], left + right)
            joins.append({'left_axes': left, 'right_axes': right, 'output_axes': left + right,
                          'amplitude_action': 'identity; ordered owner concatenation only'})
        elif tag == 'lift_basis':
            axes = owners.pop(operation['input'])
            assert axes == (0, 1) and operation['output_wires'] == [0, 1]
            expected = [a | ((a ^ b) << 1) for a, b in
                        [(label & 1, label >> 1) for label in range(4)]]
            observed_table = operation['table']
            assert observed_table == expected
            output = [0j] * len(state)
            for label, amplitude in enumerate(state):
                output[expected[label]] += amplitude
            state = output
            owner(operation['output'], axes)
            snapshot = {''.join(str(label >> axis & 1) for axis in axes):
                        {'real': amplitude.real, 'imaginary': amplitude.imag}
                        for label, amplitude in enumerate(state)}
        elif tag == 'split':
            axes = owners.pop(operation['input'])
            left_width = operation['left_bits']
            owner(operation['left'], axes[:left_width])
            owner(operation['right'], axes[left_width:])
        elif tag == 'measure_z':
            axes = owners.pop(operation['input'])
            assert len(axes) == 1
            measurements.append((operation['output'], axes[0]))
        else:
            raise ValueError('unsupported permutation-oracle operation: ' + tag)
        assert width <= 2
    assert not owners and snapshot is not None
    measured_axes = dict(measurements)
    distribution = {}
    for label, amplitude in enumerate(state):
        bits = ''.join(str(label >> measured_axes[token] & 1) for token in program['classical_outputs'])
        distribution[bits] = distribution.get(bits, 0) + abs(amplitude) ** 2
    return {'distribution': distribution, 'after_lift': snapshot, 'table': observed_table,
            'ordered_joins': joins, 'coefficient_contract': '+1', 'source_qubits': width}


def main():
    output = BASE / 'observations-after'
    capture = json.loads((output / 'capture.json').read_text())
    first = json.loads((BASE / 'first-files.json').read_text())
    protected = dict(capture['historical_inputs_sha256'])
    protected.update({'observations-after/capture.json': digest(output / 'capture.json'),
                      'analysis-after-01.json': digest(BASE / 'analysis-after-01.json'),
                      'capture_after.py': digest(BASE / 'capture_after.py')})

    def identity():
        assert digest(CLI) == EXPECTED_CLI and digest(NATIVE) == EXPECTED_NATIVE
        for name, sha in first['files'].items():
            assert digest(BASE / 'attempt-01' / name) == sha
        for name, sha in protected.items():
            assert digest(BASE / name) == sha
    identity()
    cases = [('entangle-desired', 'entangle'), ('phase-reference-desired', 'entangle'),
             ('permutation-desired', 'map'), ('unit-owner-desired', 'identity')]
    prediction = {'format': 'qleisli.coherent-basis-public-entry-predictions', 'version': 1,
                  'recorded_before_commands_utc': stamp(), 'driver_sha256': digest(Path(__file__)),
                  'cli_sha256': EXPECTED_CLI, 'native_sha256': EXPECTED_NATIVE,
                  'cases': [{'case': case, 'entry': 'main::' + entry,
                             'source_sha256': digest(BASE / 'attempt-01' / case / 'main.qli'),
                             'predicted_exit': 1, 'predicted_code': 'unsupported',
                             'predicted_message': 'sized preparation profile: unsupported runtime expression'}
                            for case, entry in cases],
                  'reason': 'The frozen original main entries are private, which preempts projection. Selecting existing public helpers should expose the unchanged CoherentLift projection restriction; no source change is authorized.'}
    write(output / 'public-entry-predictions-02.json', prediction)
    environment = os.environ.copy()
    environment['QLEISLI_KERNEL'] = str(NATIVE)
    observations, assertions = [], []
    for case, entry in cases:
        source = BASE / 'attempt-01' / case / 'main.qli'
        command = [str(CLI), 'check', '--entry=main::' + entry,
                   '--module=main=' + str(source), '--format=json', '--lean-kernel=' + str(NATIVE)]
        identity()
        began = time.monotonic()
        result = subprocess.run(command, cwd=ROOT, env=environment, capture_output=True, timeout=60)
        elapsed = time.monotonic() - began
        identity()
        stem = case + '-public-selected-check-02'
        stdout, stderr = output / (stem + '.stdout.txt'), output / (stem + '.stderr.txt')
        stdout.write_bytes(result.stdout)
        stderr.write_bytes(result.stderr)
        event = {'command': command, 'case': case, 'entry': 'main::' + entry,
                 'exit_code': result.returncode, 'recorded_utc': stamp(), 'elapsed_seconds': elapsed,
                 'cwd': str(ROOT), 'source_sha256': digest(source),
                 'cli': {'path': str(CLI), 'sha256': EXPECTED_CLI},
                 'native_selection': {'path': str(NATIVE), 'sha256': EXPECTED_NATIVE},
                 'raw_stdout': {'path': str(stdout.relative_to(BASE)), 'sha256': digest(stdout)},
                 'raw_stderr': {'path': str(stderr.relative_to(BASE)), 'sha256': digest(stderr)},
                 'identity_checked_before_and_after': True}
        try:
            event['stdout'] = json.loads(result.stdout)
        except ValueError as error:
            event['decode_error'] = str(error)
        write(output / (stem + '.json'), event)
        observations.append(str((output / (stem + '.json')).relative_to(BASE)))
        ds = event.get('stdout', {}).get('diagnostics', [])
        assertions.append({'name': case + '-public-CoherentLift-projection-refusal',
                           'passed': result.returncode == 1 and len(ds) == 1 and
                           ds[0]['code'] == 'unsupported' and
                           ds[0]['message'] == 'sized preparation profile: unsupported runtime expression',
                           'details': {'entry': 'main::' + entry, 'source_sha256': digest(source),
                                       'actual_diagnostics': ds}})
    path = output / 'artifacts/permutation-desired.qirf'
    oracle = permutation_oracle(path)
    expected = next(case['oracle']['distribution'] for case in first['cases']
                    if case['id'] == 'permutation-desired')
    actual_event = json.loads((output / 'permutation-desired-finite-run.json').read_text())
    actual = {''.join('1' if bit else '0' for bit in row['bits']): row['probability']
              for row in actual_event['stdout']['result']['distribution']}
    keys = set(expected) | set(actual) | set(oracle['distribution'])
    assertions.append({'name': 'permutation-independent-final-distribution-with-ordered-join',
                       'passed': all(abs(actual.get(key, 0) - expected.get(key, 0)) <= TOLERANCE and
                                     abs(oracle['distribution'].get(key, 0) - expected.get(key, 0)) <= TOLERANCE
                                     for key in keys),
                       'details': {'specified_exact_distribution': expected,
                                   'actual_numeric_distribution': actual,
                                   'independent_numeric_distribution': oracle['distribution'],
                                   'tolerance': TOLERANCE, 'normalization_or_pruning': False}})
    expected_amplitudes = {'00': complex(1 / math.sqrt(2), 0), '11': complex(1 / math.sqrt(2), 0)}
    snapshot = {key: complex(value['real'], value['imaginary']) for key, value in oracle['after_lift'].items()}
    assertions.append({'name': 'permutation-independent-complex-lift-amplitudes-with-ordered-join',
                       'passed': all(abs(snapshot.get(key, 0j) - expected_amplitudes.get(key, 0j)) <= TOLERANCE
                                     for key in set(snapshot) | set(expected_amplitudes)),
                       'details': {'specified_amplitudes': {key: {'real': value.real, 'imaginary': value.imag}
                                                           for key, value in expected_amplitudes.items()},
                                   'actual_ir_reference_amplitudes': oracle['after_lift'], 'tolerance': TOLERANCE}})
    expected_labels = [a | ((a ^ b) << 1) for a, b in [(label & 1, label >> 1) for label in range(4)]]
    assertions.append({'name': 'permutation-all-four-ordered-basis-labels-with-ordered-join',
                       'passed': oracle['table'] == expected_labels,
                       'details': {'input_axis_order': ['a', 'b'], 'derived_labels': expected_labels,
                                   'actual_table': oracle['table'], 'ordered_joins': oracle['ordered_joins']}})
    identity()
    analysis = {'format': 'qleisli.coherent-basis-after-supplement', 'version': 1,
                'recorded_utc': stamp(), 'driver': {'path': str(Path(__file__).relative_to(BASE)),
                                                 'sha256': digest(Path(__file__))},
                'original_capture_sha256': protected['observations-after/capture.json'],
                'original_analysis_sha256': protected['analysis-after-01.json'],
                'original_driver_sha256': protected['capture_after.py'],
                'first_sources_sha256': digest(BASE / 'first-files.json'),
                'cli_sha256': EXPECTED_CLI, 'native_sha256': EXPECTED_NATIVE,
                'predictions': {'path': 'observations-after/public-entry-predictions-02.json',
                                'sha256': digest(output / 'public-entry-predictions-02.json')},
                'observations': observations, 'assertions': assertions,
                'passed_assertions': sum(item['passed'] for item in assertions),
                'failed_assertions': [item for item in assertions if not item['passed']],
                'permutation_oracle': oracle, 'artifact_sha256': digest(path),
                'historical_and_first_source_identities_preserved': True,
                'corrigenda': [
                    'The initial AFTER analysis has 64 passed assertions and one oracle omission: join was unsupported by that authored oracle. The failure and original driver remain unchanged; the ordered-join oracle here completes the missing permutation comparison using the actual captured artifact.',
                    'The initial README overstates selected CoherentLift refusals. Its frozen selected commands target private main::main; the actual original and first AFTER positive selected observations return visibility, not projection. These additional commands select existing public helpers with unchanged source and explicitly recorded before-command predictions.'
                ],
                'scope': 'Four additional public-entry CLI observations and a literal two-qubit permutation oracle; no original source/command-record rewriting, command replay, compiler/Lean rebuild, fresh replay, independent parser review, new admission, mathematical certification or release validation.'}
    write(BASE / 'analysis-after-02.json', analysis)
    print(json.dumps({'additional_observations': len(observations),
                      'passed_assertions': analysis['passed_assertions'],
                      'failed_assertions': analysis['failed_assertions'],
                      'analysis_sha256': digest(BASE / 'analysis-after-02.json')}, indent=2))


if __name__ == '__main__':
    main()
