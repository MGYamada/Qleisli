"""Capture the fixed post-migration CLI on unchanged informed #81 sources.

Commands are authored below, never executed from an observation record.
The small complex-vector oracle uses literal mathematics, not compiler code.
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

ROOT = Path(__file__).resolve().parents[4]
BASE = Path(__file__).resolve().parent
CLI = Path('/private/tmp/qleisli-bounded-validation-target/debug/qleisli')
NATIVE = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
EXPECTED_CLI = '4c58a0b51360b99433ea75259967875c40d0caf872e2dc2981616c08d9c7db50'
EXPECTED_NATIVE = '39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85'
TOLERANCE = 1e-12


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, data):
    assert not path.exists(), 'Refusing to overwrite an AFTER record: ' + str(path)
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')


def stamp():
    return datetime.now(timezone.utc).isoformat()


def identity(first, protected):
    assert digest(CLI) == EXPECTED_CLI, 'CLI identity changed'
    assert digest(NATIVE) == EXPECTED_NATIVE, 'native identity changed'
    for name, sha in first['files'].items():
        assert digest(BASE / 'attempt-01' / name) == sha, 'source identity changed: ' + name
    for name, sha in protected.items():
        assert digest(BASE / name) == sha, 'historical record identity changed: ' + name


def complex_json(value):
    return {'real': value.real, 'imaginary': value.imag}


def literal_ir_oracle(artifact, expected_table, logical_order):
    """Interpret only the literal gates/owners in these three tiny artifacts.

    Labels encode the first ordered axis as bit zero. Lift coefficients are
    exactly +1 by its independent contract. Finite floating point is used here
    for regression comparison, never as an exact proof or acceptance decision.
    """
    data = json.loads(artifact.read_text())
    assert data['format'] == 'qleisli.finite-ir' and data['version'] == 2
    program = data['programs'][data['root']]
    assert not program['quantum_inputs'] and not program['quantum_outputs']
    state, width = [1 + 0j], 0
    owners, issued, measurements, snapshots = {}, set(), [], []
    gates, cnots, lift_tables = [], [], []

    def owner(token, axes):
        assert token not in issued, 'duplicate logical owner in oracle input'
        issued.add(token)
        owners[token] = tuple(axes)

    def take(token):
        return owners.pop(token)

    def permutation(mapping):
        output = [0j] * len(state)
        for label, amplitude in enumerate(state):
            output[mapping(label)] += amplitude
        return output

    for operation in program['operations']:
        tag = operation['tag']
        assert not measurements or tag == 'measure_z', 'oracle expects a final measurement tail'
        if tag == 'init0':
            assert operation['wire'] == width
            state += [0j] * len(state)
            owner(operation['output'], (width,))
            width += 1
        elif tag == 'gate':
            axes = take(operation['input'])
            assert len(axes) == 1
            axis, gate = axes[0], operation['gate']
            output = [0j] * len(state)
            for label, amplitude in enumerate(state):
                if gate == 'h':
                    output[label & ~(1 << axis)] += amplitude / math.sqrt(2)
                    output[label | (1 << axis)] += amplitude * (-1 if label >> axis & 1 else 1) / math.sqrt(2)
                elif gate == 't':
                    omega = complex(math.sqrt(0.5), math.sqrt(0.5))
                    output[label] += amplitude * (omega if label >> axis & 1 else 1)
                else:
                    raise ValueError('unsupported literal oracle gate: ' + gate)
            state = output
            owner(operation['output'], axes)
            gates.append({'gate': gate, 'axis': axis})
        elif tag == 'cnot':
            control, target = take(operation['control']), take(operation['target'])
            assert len(control) == len(target) == 1 and control != target
            state = permutation(lambda label: label ^ ((1 << target[0]) if label >> control[0] & 1 else 0))
            owner(operation['control_out'], control)
            owner(operation['target_out'], target)
            cnots.append({'control_axis': control[0], 'target_axis': target[0]})
        elif tag == 'lift_basis':
            before = take(operation['input'])
            after = tuple(operation['output_wires'])
            table = operation['table']
            assert table == expected_table, 'emitted lift differs from the independently specified ordered +1 map'
            assert len(table) == 1 << len(before) and len(set(table)) == len(table)
            assert after[:len(before)] == before
            for axis in after[len(before):]:
                assert axis == width
                state += [0j] * len(state)
                width += 1
            mask = sum(1 << axis for axis in after)
            def mapping(label):
                value = sum(((label >> axis) & 1) << bit for bit, axis in enumerate(before))
                output = label & ~mask
                for bit, axis in enumerate(after):
                    output |= ((table[value] >> bit) & 1) << axis
                return output
            state = permutation(mapping)
            owner(operation['output'], after)
            snapshot = {}
            assert len(logical_order) == width
            for label, amplitude in enumerate(state):
                bits = ''.join(str(label >> axis & 1) for axis in logical_order)
                snapshot[bits] = complex_json(amplitude)
            snapshots.append(snapshot)
            lift_tables.append(table)
        elif tag == 'split':
            axes = take(operation['input'])
            left_width = operation['left_bits']
            owner(operation['left'], axes[:left_width])
            owner(operation['right'], axes[left_width:])
        elif tag == 'measure_z':
            axes = take(operation['input'])
            assert len(axes) == 1
            measurements.append((operation['output'], axes[0]))
        else:
            raise ValueError('unsupported literal oracle operation: ' + tag)
        assert width <= 3, 'oracle is restricted to the three frozen small controls'
    assert not owners
    assert len(snapshots) == 1
    measured_axes = dict(measurements)
    distribution = {}
    for label, amplitude in enumerate(state):
        bits = ''.join(str(label >> measured_axes[token] & 1) for token in program['classical_outputs'])
        distribution[bits] = distribution.get(bits, 0.0) + abs(amplitude) ** 2
    return {'distribution': distribution, 'after_lift': snapshots[0],
            'lift_tables': lift_tables, 'gates': gates, 'cnots': cnots,
            'maximum_source_qubits': width, 'coefficient_contract': '+1',
            'logical_snapshot_axes': logical_order}


def main():
    output = BASE / 'observations-after'
    assert not output.exists(), 'Refusing to overwrite AFTER observations'
    first = json.loads((BASE / 'first-files.json').read_text())
    protected_paths = [BASE / name for name in (
        'README.md', 'context.md', 'first-files.json', 'session.json',
        'session.pending.json', 'capture_before.py', 'results-before.json')]
    protected_paths += sorted((BASE / 'observations-before').rglob('*'))
    protected = {str(path.relative_to(BASE)): digest(path) for path in protected_paths if path.is_file()}
    identity(first, protected)
    output.mkdir()
    artifacts = output / 'artifacts'
    artifacts.mkdir()
    started = stamp()
    environment = os.environ.copy()
    environment['QLEISLI_KERNEL'] = str(NATIVE)
    observations, events = [], {}
    for case in first['cases']:
        case_id = case['id']
        project = BASE / 'attempt-01' / case_id
        commands = [
            ('finite-check', [str(CLI), 'check', str(project), '--format=json', '--lean-kernel=' + str(NATIVE)]),
            ('selected-check', [str(CLI), 'check', '--entry=main::main', '--module=main=' + str(project / 'main.qli'), '--format=json', '--lean-kernel=' + str(NATIVE)]),
        ]
        if case['spelling'] == 'desired' and case['oracle'] is not None:
            commands += [
                ('finite-run', [str(CLI), 'run', str(project), '--format=json', '--lean-kernel=' + str(NATIVE)]),
                ('finite-emit-ir', [str(CLI), 'emit-ir', str(project), '--output=' + str(artifacts / (case_id + '.qirf')), '--format=json', '--lean-kernel=' + str(NATIVE)]),
            ]
        if case['spelling'] == 'legacy':
            commands.append(('finite-check-text', [str(CLI), 'check', str(project), '--lean-kernel=' + str(NATIVE)]))
        for action, command in commands:
            identity(first, protected)
            began = time.monotonic()
            completed = subprocess.run(command, cwd=ROOT, env=environment, capture_output=True, timeout=60)
            elapsed = time.monotonic() - began
            identity(first, protected)
            name = case_id + '-' + action
            stdout_file = output / (name + '.stdout.txt')
            stderr_file = output / (name + '.stderr.txt')
            stdout_file.write_bytes(completed.stdout)
            stderr_file.write_bytes(completed.stderr)
            event = {
                'command': command, 'exit_code': completed.returncode, 'recorded_utc': stamp(),
                'elapsed_seconds': elapsed, 'case': case_id, 'action': action, 'cwd': str(ROOT),
                'cli': {'path': str(CLI), 'sha256': EXPECTED_CLI},
                'native_selection': {'path': str(NATIVE), 'sha256': EXPECTED_NATIVE},
                'source_sha256': digest(project / 'main.qli'),
                'raw_stdout': {'path': str(stdout_file.relative_to(BASE)), 'sha256': digest(stdout_file)},
                'raw_stderr': {'path': str(stderr_file.relative_to(BASE)), 'sha256': digest(stderr_file)},
                'identity_checked_before_and_after': True,
                'native_attestation_limit': 'Explicit selected bytes are checked; native child start/exit counts and compiled-HEAD correspondence are not independently attested.'
            }
            if action.endswith('-text'):
                event['text_stdout'] = completed.stdout.decode('utf-8')
                event['text_stderr'] = completed.stderr.decode('utf-8')
            else:
                try:
                    parsed = json.loads(completed.stdout.decode('utf-8'))
                    if parsed.get('format') != 'qleisli.result' or parsed.get('version') != 1:
                        raise ValueError('unexpected result format')
                    event['stdout'] = parsed
                except (UnicodeDecodeError, ValueError, AttributeError) as error:
                    event['decode_error'] = str(error)
            write(output / (name + '.json'), event)
            observations.append(str((output / (name + '.json')).relative_to(BASE)))
            events[(case_id, action)] = event
    identity(first, protected)
    captured_artifacts = {str(path.relative_to(BASE)): {'sha256': digest(path), 'bytes': path.stat().st_size}
                          for path in sorted(artifacts.iterdir())}
    assert all(info['bytes'] < 1048576 for info in captured_artifacts.values())
    capture = {'format': 'qleisli.coherent-basis-after-capture', 'version': 1,
               'baseline_checkout': first['baseline_commit'], 'started_utc': started, 'ended_utc': stamp(),
               'cli_sha256': EXPECTED_CLI, 'native_sha256': EXPECTED_NATIVE,
               'first_sources_sha256': digest(BASE / 'first-files.json'),
               'driver_sha256': digest(Path(__file__)), 'historical_inputs_sha256': protected,
               'source_and_executable_identities_unchanged': True,
               'observations': observations, 'artifacts': captured_artifacts,
               'scope': 'Actual unchanged-source CLI observations. No source repair, compiler/Lean rebuild, fresh replay, independent parser review, guarantee admission or completion claim.'}
    write(output / 'capture.json', capture)

    assertions = []
    def check(name, condition, details):
        assertions.append({'name': name, 'passed': bool(condition), 'details': details})

    def before(case, action):
        return json.loads((BASE / 'observations-before' / (case + '-' + action + '.json')).read_text())

    def diagnostics(event):
        return event.get('stdout', {}).get('diagnostics', [])

    def diagnostic_contract(event):
        return [(item['code'], item['severity'], item['message']) for item in diagnostics(event)]

    for case in first['cases']:
        case_id = case['id']
        if case['spelling'] == 'legacy':
            for action in ('finite-check', 'selected-check'):
                event = events[(case_id, action)]
                ds = diagnostics(event)
                source = (BASE / 'attempt-01' / case_id / 'main.qli').read_bytes()
                start = source.index(b'do ')
                spans = [item['primary'] for item in ds]
                condition = (event['exit_code'] == 1 and len(ds) == 1 and
                             ds[0]['code'] in ('project', 'parse') and
                             'removed in Qleisli 0.3.0' in ds[0]['message'] and
                             'basis q as p { e }' in ds[0]['message'] and
                             'not monadic bind or measurement' in ds[0]['message'] and
                             ds[0]['primary']['start'] == start and ds[0]['primary']['end'] == start + 2)
                check(case_id + '-' + action + '-targeted-removal', condition,
                      {'diagnostics': ds, 'expected_byte_span': [start, start + 2], 'actual_spans': spans})
            text = events[(case_id, 'finite-check-text')]
            json_event = events[(case_id, 'finite-check')]
            ds = diagnostics(json_event)
            location = ds[0]['primary'] if ds else {}
            rendered = text['text_stdout'] + text['text_stderr']
            location_text = ':' + str(location.get('line')) + ':' + str(location.get('column'))
            check(case_id + '-text-diagnostic',
                  text['exit_code'] == 1 and 'removed in Qleisli 0.3.0' in rendered and
                  'basis q as p { e }' in rendered and location_text in rendered,
                  {'json_byte_location': location, 'rendered_line_column': location_text})
        else:
            legacy = case['pair'] + '-legacy'
            for action in ('finite-check', 'selected-check'):
                old, new = before(legacy, action), events[(case_id, action)]
                check(case_id + '-' + action + '-legacy-contract',
                      old['exit_code'] == new['exit_code'] and old['stdout']['outcome'] == new.get('stdout', {}).get('outcome') and
                      diagnostic_contract(old) == diagnostic_contract(new),
                      {'before_diagnostics': diagnostics(old), 'after_diagnostics': diagnostics(new),
                       'comparison': 'exit/outcome and exact code/severity/message; source byte spans are separately recorded and may move'})
            if case['oracle'] is not None:
                for action in ('finite-run', 'finite-emit-ir'):
                    old, new = before(legacy, action), events[(case_id, action)]
                    check(case_id + '-' + action + '-legacy-contract',
                          old['exit_code'] == new['exit_code'] and old['stdout']['outcome'] == new.get('stdout', {}).get('outcome') and
                          diagnostic_contract(old) == diagnostic_contract(new),
                          {'before_diagnostics': diagnostics(old), 'after_diagnostics': diagnostics(new)})

    oracle_records = {}
    for pair, table, order, expected_amplitudes in (
            ('entangle', [0, 3], [0, 1], {'00': 1 / math.sqrt(2), '11': 1 / math.sqrt(2)}),
            ('phase-reference', [0, 3], [0, 2, 1], {'000': 1 / math.sqrt(2), '111': complex(0.5, 0.5)}),
            ('permutation', [0, 3, 2, 1], [0, 1], {'00': 1 / math.sqrt(2), '11': 1 / math.sqrt(2)})):
        desired = pair + '-desired'
        current = artifacts / (desired + '.qirf')
        historical = BASE / 'observations-before' / 'artifacts' / (pair + '-legacy.qirf')
        check(pair + '-exact-qirf-bytes', current.is_file() and current.read_bytes() == historical.read_bytes(),
              {'historical_sha256': digest(historical), 'current_sha256': digest(current) if current.is_file() else None})
        old = before(pair + '-legacy', 'finite-run')['stdout']['result']['distribution']
        new_event = events[(desired, 'finite-run')]
        new = new_event.get('stdout', {}).get('result')
        new = new.get('distribution') if isinstance(new, dict) else None
        check(pair + '-literal-run-distribution-identity', old == new, {'before': old, 'after': new})
        if not current.is_file() or new is None:
            check(pair + '-independent-oracle', False, {'error': 'required actual artifact/distribution missing'})
            continue
        try:
            oracle = literal_ir_oracle(current, table, order)
        except (AssertionError, KeyError, ValueError) as error:
            check(pair + '-independent-oracle', False, {'error': str(error)})
            continue
        oracle_records[pair] = oracle
        expected = next(case['oracle']['distribution'] for case in first['cases'] if case['id'] == desired)
        actual = {''.join('1' if bit else '0' for bit in row['bits']): row['probability'] for row in new}
        keys = set(expected) | set(actual) | set(oracle['distribution'])
        check(pair + '-independent-final-distribution',
              all(abs(actual.get(key, 0.0) - expected.get(key, 0.0)) <= TOLERANCE and
                  abs(oracle['distribution'].get(key, 0.0) - expected.get(key, 0.0)) <= TOLERANCE for key in keys),
              {'specified_exact_distribution': expected, 'actual_numeric_distribution': actual,
               'independent_numeric_distribution': oracle['distribution'], 'tolerance': TOLERANCE,
               'comparison': 'union of outcomes, no normalization or probability pruning; tolerance is regression evidence, not exact semantic identity'})
        snapshot = {key: complex(value['real'], value['imaginary']) for key, value in oracle['after_lift'].items()}
        keys = set(snapshot) | set(expected_amplitudes)
        check(pair + '-independent-complex-lift-amplitudes',
              all(abs(snapshot.get(key, 0j) - expected_amplitudes.get(key, 0j)) <= TOLERANCE for key in keys),
              {'specified_exact_amplitudes': {key: complex_json(value) for key, value in expected_amplitudes.items()},
               'independent_actual_ir_amplitudes': oracle['after_lift'], 'ordered_axes': order,
               'tolerance': TOLERANCE})
        if pair == 'permutation':
            ordered_pairs = [((label & 1), (label >> 1)) for label in range(4)]
            expected_labels = [a | ((a ^ b) << 1) for a, b in ordered_pairs]
            check('permutation-all-four-ordered-basis-labels', oracle['lift_tables'] == [expected_labels],
                  {'input_axis_order': ['a', 'b'], 'input_pairs': ordered_pairs,
                   'independently_derived_labels': expected_labels, 'actual_tables': oracle['lift_tables']})

    # A lost/reference-dephased or conjugated T phase has the same 000/111
    # probabilities before interference, but would fail this final control.
    wrong_phase_zero = abs((1 + complex(0, -1)) / 2) ** 2
    check('phase-reference-control-distinguishes-conjugated-phase',
          abs(wrong_phase_zero - 0.5) <= TOLERANCE and wrong_phase_zero < 1 - TOLERANCE,
          {'correct_exact_final_000_probability': 1, 'conjugated_T_phase_final_000_probability': wrong_phase_zero,
           'reference_dephasing_final_000_probability': 0.5,
           'reason': 'For the conjugated phase, undoing with Tdag leaves relative phase -i; reference dephasing removes the off-diagonal interference.'})
    identity(first, protected)
    summary = {'format': 'qleisli.coherent-basis-after-analysis', 'version': 1,
               'capture': {'path': 'observations-after/capture.json', 'sha256': digest(output / 'capture.json')},
               'driver_sha256': digest(Path(__file__)), 'cli_sha256': EXPECTED_CLI, 'native_sha256': EXPECTED_NATIVE,
               'first_sources_sha256': digest(BASE / 'first-files.json'),
               'historical_and_first_source_identities_preserved': True,
               'observations': len(observations), 'assertions': assertions,
               'passed_assertions': sum(item['passed'] for item in assertions),
               'failed_assertions': [item for item in assertions if not item['passed']],
               'independent_literal_oracles': oracle_records,
               'review_independence_limit': 'The author implemented the parser. This is actual command capture and a separately authored literal numerical oracle, not an independent parser implementation review.',
               'scope': 'Frozen 0–3-qubit migration/isolation controls; unchanged native choice. Numeric regression and exact three-artifact byte comparisons are not a general source/runtime preservation proof, Lean replay, full QS/PR/RS discharge, Issue completion or release validation.'}
    write(BASE / 'analysis-after-01.json', summary)
    print(json.dumps({'observations': len(observations), 'passed_assertions': summary['passed_assertions'],
                      'failed_assertions': summary['failed_assertions'], 'artifacts': captured_artifacts,
                      'analysis_sha256': digest(BASE / 'analysis-after-01.json'),
                      'capture_sha256': digest(output / 'capture.json')}, indent=2))


if __name__ == '__main__':
    main()
