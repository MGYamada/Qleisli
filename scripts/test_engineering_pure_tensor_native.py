#!/usr/bin/env python3
"""Independent small exact tensor comparisons; retained history is never run.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import copy
from fractions import Fraction
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import struct
import subprocess
import tarfile
import tomllib

from native_packet import envelope, parse_reply
from test_native_execution_protocol import qdv

ROOT = Path(__file__).resolve().parents[1]
SESSION = ROOT / 'tests/fixtures/authoring_sessions/engineering-pure-composition-v030'
VERSION = tomllib.loads((ROOT / 'Cargo.toml').read_text())['package']['version']
MODE = '--engineering-pure-tensor-check'
FIXED = dict(format='qleisli.engineering-pure-tensor-request', version=1,
    claim_kind='engineering-pure-tensor-bound', metric='pure-euclidean-operator-norm-v1',
    checker_profile='tensor-additive-r8-pure-leaf-v1', target_profile='qirf-r8-pure-v1',
    composition='ordered-tensor-two-v1', error_category='implementation-distance')
ARCHIVES = [
    ('tensor-prototype.tar.gz', '5fbbff9fd4218f12188cde5b61b8ee99914b197cb2d9664171c01a6cd4cb3e84', 85),
    ('shape-budget-supplement.tar.gz', '1b0690083fce798ad05ab66309f9385b1bba1a23a103440fb359856e0976bcf9', 44)]


def digest(value):
    return hashlib.sha256(value).hexdigest()


def retained():
    """Read only fixed local members in memory: no extraction or historical argv."""
    provenance = json.loads((SESSION / 'provenance.json').read_text())
    assert provenance['format'] == 'qleisli.engineering-pure-composition-first-capture'
    assert provenance['version'] == 1 and provenance['kind'] == 'informed-study'
    assert provenance['maximum_physical_qubits'] == 2
    assert provenance['recorded_commands_executed'] is False
    assert provenance['source_to_manual_qirf_preservation_established'] is False
    assert provenance['issue_completion_credit'] is False
    assert '`provenance.json`' in (SESSION / 'README.md').read_text()
    captures = []
    for (name, sha, count), record in zip(ARCHIVES, provenance['preserved_archives'], strict=True):
        raw = (SESSION / name).read_bytes()
        assert digest(raw) == sha == record['sha256'] and record['path'] == name
        assert len(raw) == record['bytes']
        files = {}
        with tarfile.open(fileobj=io.BytesIO(raw), mode='r:gz') as archive:
            for member in archive.getmembers():
                path = PurePosixPath(member.name)
                assert member.isfile() and member.mode in (0o644, 0o755)
                assert not path.is_absolute() and '..' not in path.parts
                assert member.name not in files and member.size <= 1 << 20
                files[member.name] = archive.extractfile(member).read()
        freeze = json.loads(files['freeze.json'])
        assert digest(files['freeze.json']) == record['freeze_sha256']
        assert len(freeze['files']) == count == record['frozen_files']
        assert len(files) == count + 1 == record['members']
        assert set(files) == set(freeze['files']) | {'freeze.json'}
        for path, sha in freeze['files'].items():
            assert digest(files[path]) == sha
        captures.append(files)
    original, supplement = captures
    first = json.loads(original['first-sources.json'])
    for path, sha in first['first_sources'].items():
        assert digest(original[path]) == sha
    before = json.loads(original['cli-before.json'])
    assert digest(original['desired/main.qli']) == before['source_sha256']
    for call in before['calls']:
        event = json.loads(original[call['name'] + '.json'])
        assert event['argv'] == call['argv']  # Identity only; never execute it.
        assert event['cli_sha256_after'] == before['identity']['cli']['sha256']
        assert event['kernel_sha256_after'] == before['identity']['kernel']['sha256']
        assert not event['stderr']
        result = json.loads(event['stdout'])
        if call['name'] == 'emit-project':
            assert event['exit_code'] == 1 and result['diagnostics'][0]['code'] == 'invalid_entry'
        else:
            assert event['exit_code'] == 0 and result['outcome'] == 'ok'
            assert result['result']['source_preservation_verified'] is False
    for source, log in [('PureComposedMath.first.lean', 'math-attempt-01.log'),
                        ('PureComposedBounded.first.lean', 'bounded-attempt-01.log')]:
        assert original[source] and b'error:' in original[log]
    assert original['PureComposedKernel.first.lean'] and original['kernel-attempt-01/stdout.log']
    desired = json.loads(supplement['desired-first.json'])
    assert 'unexecuted' in desired['kind']
    for path, sha in desired['files'].items():
        assert digest(supplement[path]) == sha
    assert supplement['PureComposedShapes.first.lean'] and b'error:' in supplement['shapes-attempt-01.log']
    assert supplement['PureComposedBudgets.first.lean'] and supplement['budgets-attempt-01.stdout.txt']
    assert json.loads(supplement['start.json'])['predecessor_bundle_sha256'] == ARCHIVES[0][1]
    failures = (SESSION / 'observer-failures.json').read_bytes()
    assert digest(failures) == '31c0e36a0f52ea64a1ef03af2ff2946fa836b5029d39de50ccf21613f5d16129'
    assert provenance['observer_failures'] == dict(path='observer-failures.json', sha256=digest(failures),
                                                  bytes=len(failures), files=7)
    observer = json.loads(failures)
    assert observer['format'] == 'qleisli.engineering-pure-tensor-observer-failures'
    assert observer['recorded_commands_executed'] is False
    for row in observer['files']:
        assert digest(row['utf8'].encode()) == row['sha256']
    assert observer['files'][0]['sha256'] == 'f2ca791733699376f4ee2c547b609c7721945ba279378aa0d753bcbab8516311'
    return {'preserved_frozen_files': 129, 'preserved_freeze_records': 2,
            'retained_observer_failure_files': len(observer['files']), 'historical_commands_executed': 0}


def encoded(value):
    return json.dumps(value, separators=(',', ':'), ensure_ascii=False).encode()


def dyadic(value):
    value = Fraction(value)
    assert value.denominator & (value.denominator - 1) == 0
    return dict(numerator=str(value.numerator), denominator_bits=value.denominator.bit_length() - 1)


ZERO = (Fraction(0),) * 4
ONE = (Fraction(1), *ZERO[1:])


def phase(exponent):
    values = list(ZERO)
    values[exponent % 4] = Fraction(1 if exponent % 8 < 4 else -1)
    return tuple(values)


def add(a, b):
    return tuple(x + y for x, y in zip(a, b, strict=True))


def multiply(a, b):
    out = list(ZERO)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[(i + j) % 4] += x * y * (1 if i + j < 4 else -1)
    return tuple(out)


def conjugate(a):
    return a[0], -a[3], -a[2], -a[1]


def matrix(rows, cols, entries):
    assert len(entries) == rows * cols
    # The independent oracle uses 1,zeta,zeta²,zeta³. The existing wire format
    # uses 1,sqrt(2),i,i*sqrt(2); convert exactly, including global phases.
    converted = [(a, (b - d) / 2, c, (b + d) / 2) for a, b, c, d in entries]
    return dict(format='qleisli.finite-matrix', version=1, domain='zeta8-dyadic-v1',
                rows=rows, cols=cols, entries=[[dyadic(c) for c in x] for x in converted])


def entries(m):
    values = [tuple(Fraction(int(c['numerator']), 2 ** c['denominator_bits']) for c in row)
              for row in m['entries']]
    return [(a, b + d, c, d - b) for a, b, c, d in values]


def tensor(a, b):
    """Independent low-first tensor coordinates: low + dimension * high."""
    ae, be = entries(a), entries(b)
    rows, cols = a['rows'] * b['rows'], a['cols'] * b['cols']
    return matrix(rows, cols, [multiply(ae[(r % a['rows']) * a['cols'] + c % a['cols']],
        be[(r // a['rows']) * b['cols'] + c // a['cols']])
        for r in range(rows) for c in range(cols)])


def independently_isometric(m):
    values = entries(m)
    for a in range(m['cols']):
        for b in range(m['cols']):
            total = ZERO
            for row in range(m['rows']):
                total = add(total, multiply(conjugate(values[row * m['cols'] + a]),
                                            values[row * m['cols'] + b]))
            assert total == (ONE if a == b else ZERO)


def positive_real(a):
    """Decide a + b sqrt(2) exactly; no floating-point tolerance."""
    rational, radical, imaginary, negative_radical = a
    assert imaginary == 0 and radical == -negative_radical
    if rational >= 0 and radical >= 0:
        return rational > 0 or radical > 0
    if rational <= 0 and radical <= 0:
        return False
    return rational * rational > 2 * radical * radical if rational > 0 else 2 * radical * radical > rational * rational


def independent_discriminator():
    delta = add(ONE, tuple(-x for x in phase(1)))
    squared = multiply(conjugate(delta), delta)
    assert squared == (Fraction(2), Fraction(-1), Fraction(0), Fraction(1))
    budget_squared = (Fraction(49, 64), *ZERO[1:])
    assert positive_real(add(budget_squared, tuple(-x for x in squared)))
    assert positive_real(add(add(squared, squared), tuple(-x for x in budget_squared)))
    return {'leaf_squared_distance': '2-sqrt(2)', 'whole_tensor_frobenius_squared': '4-2*sqrt(2)',
            'declared_budget_squared': '49/64', 'leaf_sufficient': True, 'whole_sufficient': False}


def basis(kind):
    return dict(tag='unit' if kind in ('unit', 'prepare') else 'bit')


def pair(a, b):
    return dict(tag='pair', left=a, right=b)


def port(token, wires):
    return dict(token=token, wires=wires, shape=dict(bits=len(wires)))


def phase_steps(exponent, unit=False):
    return [dict(controls=[], action=dict(tag='monomial', indices=[] if unit else [0],
        permutation=[0] if unit else [0, 1], phases=[exponent] if unit else [0, exponent]))]


def literal(domain, codomain, input_port, output_port, operations, meaning, effect='unitary'):
    program = dict(quantum_inputs=[input_port], classical_inputs=[], operations=operations,
                   quantum_outputs=[output_port['token']], classical_outputs=[], declared_effect=effect)
    artifact = dict(format='qleisli.finite-ir', version=2, profile='finite-meaning-v1',
        programs=[program], evidence=[], sources=[], root=0, root_interface=dict(input=domain, output=codomain))
    return dict(artifact=artifact, leaf=dict(input=input_port, output=output_port, matrix=meaning))


def simple(kind, exponent):
    if kind == 'prepare':
        operations = [dict(tag='unpack_unit', input=0), dict(tag='init0', output=1, wire=0),
            dict(tag='gate', gate='x', input=1, output=2),
            dict(tag='apply_unitary', input=2, output=3, steps=phase_steps(exponent))]
        return literal(basis(kind), basis('bit'), port(0, []), port(3, [0]), operations,
                       matrix(2, 1, [ZERO, phase(exponent)]), 'iso')
    unit = kind == 'unit'
    meaning = matrix(1, 1, [phase(exponent)]) if unit else matrix(2, 2, [ONE, ZERO, ZERO, phase(exponent)])
    return literal(basis(kind), basis(kind), port(0, [] if unit else [0]), port(1, [] if unit else [0]),
        [dict(tag='apply_unitary', input=0, output=1, steps=phase_steps(exponent, unit))], meaning)


def parent(left_kind, right_kind, left_phase, right_phase, swapped=False):
    children = [simple(left_kind, left_phase), simple(right_kind, right_phase)]
    widths = [len(child['leaf']['input']['wires']) for child in children]
    operations = [dict(tag='split', input=0, left=1, right=2, left_bits=widths[0])]
    token, fresh_wire = 3, sum(widths)
    outputs = []
    for side, child in enumerate(children):
        tokens = {0: side + 1}
        offset = 0 if side == 0 else widths[0]
        wires = {wire: wire + offset for wire in child['leaf']['input']['wires']}
        for operation in child['artifact']['programs'][0]['operations']:
            op = copy.deepcopy(operation)
            if 'input' in op:
                op['input'] = tokens[op['input']]
            if 'output' in op:
                original = op['output']
                tokens[original] = token
                op['output'] = token
                token += 1
            if 'wire' in op:
                wires[op['wire']] = fresh_wire
                op['wire'] = fresh_wire
                fresh_wire += 1
            operations.append(op)
        outputs.append(port(tokens[child['leaf']['output']['token']],
                            [wires[w] for w in child['leaf']['output']['wires']]))
    low, high = outputs[::-1] if swapped else outputs
    operations.append(dict(tag='join', left=low['token'], right=high['token'], output=token))
    a, b = [child['artifact']['root_interface'] for child in children]
    return literal(pair(a['input'], b['input']), pair(a['output'], b['output']),
        port(0, list(range(sum(widths)))), port(token, low['wires'] + high['wires']), operations,
        tensor(children[1]['leaf']['matrix'], children[0]['leaf']['matrix']) if swapped else
        tensor(children[0]['leaf']['matrix'], children[1]['leaf']['matrix']),
        'iso' if 'prepare' in (left_kind, right_kind) else 'unitary')


def comparison(kind, phase_value, epsilon):
    actual, ideal = simple(kind, 0), simple(kind, phase_value)
    interface = actual['artifact']['root_interface']
    return dict(domain=interface['input'], codomain=interface['output'], actual=actual['leaf'],
        ideal=ideal['leaf'], epsilon=dyadic(epsilon), actual_artifact=encoded(actual['artifact']).decode(),
        expected_artifact=encoded(ideal['artifact']).decode())


def request(left_kind='bit', right_kind='bit', left_phase=1, right_phase=0,
            left_epsilon=Fraction(7, 8), right_epsilon=0):
    actual, ideal = parent(left_kind, right_kind, 0, 0), parent(left_kind, right_kind, left_phase, right_phase)
    return actual['artifact'], dict(FIXED, actual=actual['leaf'], ideal=ideal['leaf'],
        epsilon=dyadic(Fraction(left_epsilon) + right_epsilon),
        left=comparison(left_kind, left_phase, left_epsilon), right=comparison(right_kind, right_phase, right_epsilon),
        expected_artifact=encoded(ideal['artifact']).decode())


def basis_view(value):
    tag = value['tag']
    if tag == 'pair':
        return [['pair'], *basis_view(value['left']), *basis_view(value['right'])]
    if tag == 'tuple':
        return [['tuple', len(value['fields'])], *[a for f in value['fields'] for a in basis_view(f)]]
    return [[tag, value['width']]] if tag == 'bits' else [[tag]]


def port_view(value):
    return ['port', value['token'], value['wires'], value['shape']['bits']]


def matrix_view(value):
    return ['matrix', value['rows'], value['cols'],
            [[['dyadic', c['numerator'], c['denominator_bits']] for c in row] for row in value['entries']]]


def leaf_view(value):
    return ['leaf', port_view(value['input']), port_view(value['output']), matrix_view(value['matrix'])]


def dyadic_view(value):
    return ['dyadic', value['numerator'], value['denominator_bits']]


def step_view(value):
    action = value['action']
    fields = ['indices', 'permutation', 'phases'] if action['tag'] == 'monomial' else ['indices', 'evidence', 'adjoint']
    return ['step', [['control', c['index'], c['when_one']] for c in value['controls']],
            [action['tag'], *[action[key] for key in fields]]]


def program_view(value):
    fields = {'unpack_unit': ['input'], 'init0': ['output', 'wire'], 'gate': ['gate', 'input', 'output'],
              'split': ['input', 'left', 'right', 'left_bits'], 'join': ['left', 'right', 'output'],
              'apply_unitary': ['input', 'output', 'steps'], 'measure_z': ['input', 'output']}
    operations = []
    for op in value['operations']:
        values = []
        for field in fields[op['tag']]:
            item = op[field]
            values.append(['h', 'x', 'z', 't'].index(item) if field == 'gate' else
                          [step_view(s) for s in item] if field == 'steps' else item)
        operations.append([op['tag'].replace('_', '-').replace('measure-z', 'measure'), *values])
    return ['program', [port_view(p) for p in value['quantum_inputs']], value['classical_inputs'],
            operations, value['quantum_outputs'], value['classical_outputs'],
            ['unitary', 'iso', 'observe'].index(value['declared_effect'])]


def graph_view(artifact, leaf):
    interface = artifact['root_interface']
    root = artifact['programs'][artifact['root']]
    receipts = []
    for evidence in artifact['evidence']:
        implementation = artifact['programs'][evidence['implementation']]
        specification = artifact['programs'][evidence['specification']]
        identity = evidence['identity']
        receipts.append(['function-evidence', basis_view(evidence['signature']),
            program_view(implementation), program_view(specification),
            ['identity', identity['implementation'], identity['specification'],
             [['source', artifact['sources'][i]['path'], artifact['sources'][i]['text']] for i in identity['sources']]],
            ['circuit', basis_view(evidence['signature']), [step_view(s) for s in implementation['operations'][0]['steps']]],
            matrix_view(simple('bit', 1)['leaf']['matrix']), 1, 1])
    return ['finite-graph', artifact['root'],
        ['root-interface', basis_view(interface['input']), basis_view(interface['output'])],
        [['source', s['path'], s['text']] for s in artifact['sources']],
        [program_view(p) for p in artifact['programs']], receipts, program_view(root),
        ['unitary', 'iso', 'observe'].index(root['declared_effect']), [port_view(leaf['output'])]]


def dependency_ideal(data):
    data = copy.deepcopy(data)
    artifact = json.loads(data['left']['expected_artifact'])
    original = copy.deepcopy(artifact['programs'][0])
    root = copy.deepcopy(original)
    root['operations'][0]['steps'] = [dict(controls=[],
        action=dict(tag='contract', indices=[0], evidence=0, adjoint=False))]
    artifact['programs'] = [original, copy.deepcopy(original), root]
    artifact['root'] = 2
    artifact['sources'] = [dict(path='tensor-𝄞.qli', text='Identity data; no source-preservation assertion.')]
    artifact['evidence'] = [dict(tag='circuit', signature=basis('bit'), implementation=0,
        specification=1, identity=dict(implementation='original-t', specification='independent-t', sources=[0]))]
    data['left']['expected_artifact'] = encoded(artifact).decode()
    return data


def complete_view(actual, data):
    def component(value):
        return ['engineering-pure-component', basis_view(value['domain']), basis_view(value['codomain']),
                leaf_view(value['actual']), leaf_view(value['ideal']), dyadic_view(value['epsilon']),
                value['actual_artifact'], value['expected_artifact']]
    left, right = data['left'], data['right']
    context = ['engineering-pure-tensor-request', *[data[k] for k in FIXED],
        basis_view(pair(left['domain'], right['domain'])), basis_view(pair(left['codomain'], right['codomain'])),
        leaf_view(data['actual']), leaf_view(data['ideal']), dyadic_view(data['epsilon']),
        component(left), component(right), data['expected_artifact']]
    pairs = [(actual, data['actual']), (json.loads(data['expected_artifact']), data['ideal'])]
    for child in (left, right):
        pairs.extend((json.loads(child[key + '_artifact']), child[leaf])
                     for key, leaf in [('actual', 'actual'), ('expected', 'ideal')])
    return ['engineering-pure-tensor', context, *[graph_view(a, leaf) for a, leaf in pairs]]


def pure_comparison(actual, leaf, ideal_artifact, ideal_leaf, domain, codomain, epsilon):
    data = dict(format='qleisli.engineering-pure-request', version=1, claim_kind='engineering',
        metric=FIXED['metric'], checker_profile='frobenius-r8-pure-leaf-v1', target_profile=FIXED['target_profile'],
        composition='single-component-v1', error_category=FIXED['error_category'], domain=domain, codomain=codomain,
        actual=leaf, ideal=ideal_leaf, epsilon=dyadic(epsilon), expected_artifact=encoded(ideal_artifact).decode())
    context = ['engineering-pure-request', *[data[k] for k in list(FIXED)[:8]], basis_view(domain),
               basis_view(codomain), leaf_view(leaf), leaf_view(ideal_leaf), dyadic_view(data['epsilon']), data['expected_artifact']]
    view = ['engineering-pure', context, graph_view(actual, leaf), graph_view(ideal_artifact, ideal_leaf)]
    return data, envelope('2026', inner(actual, data), qdv(view))


def inner(actual, data, whitespace=False):
    a, r = encoded(actual), encoded(data)
    if whitespace:
        a, r = b'\n' + a + b'\n', b' ' + r + b'\n'
    return b'QLV1' + struct.pack('<II', len(a), len(r)) + a + r


def live(kernel, record=None):
    retention, oracle = retained(), independent_discriminator()
    rows = []
    kernel_sha = digest(kernel.read_bytes())
    script_sha = digest(Path(__file__).read_bytes())
    if record:
        record.mkdir(parents=True, exist_ok=True)

    def invoke(name, actual, data, success=False, view=None, packet=None, mode=MODE, error=None):
        if packet is None:
            packet = envelope('2026', inner(actual, data), qdv(complete_view(actual, data) if view is None else view))
        result = subprocess.run([str(kernel), mode, VERSION], input=packet,
                                capture_output=True, timeout=60, check=False)
        row = dict(name=name, exit_code=result.returncode, stdout=result.stdout.decode(), stderr=result.stderr.decode(),
                   packet_sha256=digest(packet), packet_bytes=len(packet))
        rows.append(row)
        if record:
            (record / 'observations.json').write_text(json.dumps(dict(kernel_sha256=kernel_sha, records=rows), indent=2) + '\n')
        reply = parse_reply(result.stdout, edition='2026', product=VERSION, mode=mode, scope='execution')
        assert not result.stderr, (name, result)
        if success:
            assert result.returncode == 0 and reply.claim == 'engineering-checked', (name, result)
            assert len(reply.payload) == 1 and 0 < int(reply.payload[0]) <= 10_000_000, (name, reply)
            leaves = [data['actual'], data['ideal']]
            if mode == MODE:
                leaves += [data[s][l] for s in ('left', 'right') for l in ('actual', 'ideal')]
            for leaf in leaves:
                independently_isometric(leaf['matrix'])
        else:
            assert result.returncode == 1 and reply.error is not None, (name, result)
            if error:
                assert reply.error == error, (name, reply)
        return reply

    actual, base = request()
    good_view = complete_view(actual, base)
    invoke('tensor-discriminator-seven-eighths', actual, base, True)
    for name, options in [
        ('two-nonzero-budgets', dict(right_phase=1, right_epsilon=Fraction(7, 8))),
        ('rectangular-left', dict(left_kind='prepare')),
        ('rectangular-both-budgets', dict(left_kind='prepare', right_phase=1, right_epsilon=Fraction(7, 8))),
        ('rectangular-right', dict(right_kind='prepare', right_phase=1, right_epsilon=Fraction(7, 8))),
        ('unit-left', dict(left_kind='unit', right_phase=1, right_epsilon=Fraction(7, 8))),
        ('unit-right', dict(right_kind='unit', right_phase=1, right_epsilon=Fraction(7, 8))),
        ('unit-pair', dict(left_kind='unit', right_kind='unit', right_phase=1, right_epsilon=Fraction(7, 8))),
        ('unit-pair-zero', dict(left_kind='unit', right_kind='unit', left_phase=0, left_epsilon=0)),
        ('canonical-half-plus-half', dict(left_phase=0, left_epsilon=Fraction(1, 2), right_epsilon=Fraction(1, 2))),
        ('mixed-exponents', dict(left_phase=0, left_epsilon=Fraction(3, 8), right_epsilon=Fraction(1, 2))),
        ('max-square-admissible-budget', dict(left_phase=0, left_epsilon=2**63 - 1, right_epsilon=2**63 - 1))]:
        a, data = request(**options)
        invoke(name, a, data, True)
    invoke('whitespace-original-body-request', actual, base, True,
           packet=envelope('2026', inner(actual, base, True), qdv(good_view)))
    dependency = dependency_ideal(base)
    invoke('original-dependency-and-source-identity', actual, dependency, True)
    for index in (0, 1):
        data = copy.deepcopy(dependency)
        artifact = json.loads(data['left']['expected_artifact'])
        artifact['programs'][index]['operations'][0]['steps'] = phase_steps(7)
        data['left']['expected_artifact'] = encoded(artifact).decode()
        invoke('stale-original-dependency-' + str(index), actual, data)
    data = copy.deepcopy(dependency)
    artifact = json.loads(data['left']['expected_artifact'])
    artifact['programs'][2]['operations'][0]['steps'][0]['action']['evidence'] = 1
    data['left']['expected_artifact'] = encoded(artifact).decode()
    invoke('invalid-original-dependency-index', actual, data)
    # This same parent passes exact self-comparison, yet its requested tensor equation is wrong.
    changed = parent('prepare', 'bit', 1, 0, swapped=True)
    interface = changed['artifact']['root_interface']
    self_request, self_packet = pure_comparison(changed['artifact'], changed['leaf'], changed['artifact'],
        changed['leaf'], interface['input'], interface['output'], 0)
    invoke('swapped-parent-independently-valid-self-equation', changed['artifact'], self_request, True,
           packet=self_packet, mode='--engineering-pure-check')
    a, data = request(left_kind='prepare')
    data['ideal'], data['expected_artifact'] = changed['leaf'], encoded(changed['artifact']).decode()
    invoke('typed-consistent-swapped-parent', a, data)
    for field in FIXED:
        data = copy.deepcopy(base)
        data[field] = 2 if field == 'version' else 'unrecognized'
        invoke('unsupported-' + field, actual, data, view=good_view)
    for field in base:
        data = copy.deepcopy(base)
        del data[field]
        invoke('missing-' + field, actual, data, view=good_view)
    for side in ('left', 'right'):
        for field in base[side]:
            data = copy.deepcopy(base)
            del data[side][field]
            invoke('missing-' + side + '-' + field, actual, data, view=good_view)
    for side in ('left', 'right'):
        for field in ('actual', 'ideal'):
            data = copy.deepcopy(base)
            data[side][field]['matrix'] = matrix(2, 2, [ONE, ZERO, ZERO, phase(4)])
            invoke('stale-' + side + '-' + field + '-matrix', actual, data)
    for exponent, label in [(7, 'parent-phase'), (4, 'changed-parent')]:
        data = copy.deepcopy(base)
        changed = parent('bit', 'bit', exponent, 0)
        data['ideal'], data['expected_artifact'] = changed['leaf'], encoded(changed['artifact']).decode()
        invoke(label, actual, data)
    changed = parent('bit', 'bit', 0, 1)
    data = copy.deepcopy(base)
    data['ideal'], data['expected_artifact'] = changed['leaf'], encoded(changed['artifact']).decode()
    invoke('parent-axis', actual, data)
    for field in ('actual', 'ideal'):
        data = copy.deepcopy(base)
        data[field]['output']['wires'].reverse()
        invoke('ordered-parent-' + field + '-wires', actual, data)
    for which in ('input', 'output'):
        data = copy.deepcopy(base)
        changed = json.loads(data['expected_artifact'])
        changed['root_interface'][which] = dict(tag='bits', width=2)
        data['expected_artifact'] = encoded(changed).decode()
        invoke('equal-width-parent-' + which + '-tree', actual, data, view=good_view)
    data = copy.deepcopy(base)
    data['left']['domain'] = dict(tag='bits', width=1)
    invoke('equal-width-component-tree', actual, data)
    for value in [dict(numerator='-1', denominator_bits=0), dict(numerator='0', denominator_bits=1),
                  dict(numerator='2', denominator_bits=1), dict(numerator='01', denominator_bits=0),
                  dict(numerator='1', denominator_bits=127), dict(numerator=str(2**127), denominator_bits=0)]:
        data = copy.deepcopy(base)
        data['left']['epsilon'] = value
        invoke('invalid-component-epsilon-' + str(len(rows)), actual, data, view=good_view)
    for value in [0, 1, Fraction(7, 16)]:
        data = copy.deepcopy(base)
        data['epsilon'] = dyadic(value)
        invoke('stale-total-' + str(value), actual, data)
    for field, value in [('accepted', True), ('resource_bound', 0), ('domain', dict(tag='bit'))]:
        data = dict(base, **{field: value})
        invoke('unknown-' + field, actual, data, view=good_view)
    for name, operations in [
        ('observation', [dict(tag='measure_z', input=0, output=0), dict(tag='init0', output=1, wire=1)]),
        ('reset', [dict(tag='reset', input=0, output=1, fresh_wire=1)]),
        ('discard', [dict(tag='discard', input=0), dict(tag='init0', output=1, wire=1)])]:
        for label in ('unitary', 'iso', 'observe'):
            data = copy.deepcopy(base)
            artifact = json.loads(data['left']['actual_artifact'])
            artifact['programs'][0]['operations'] = operations
            artifact['programs'][0]['declared_effect'] = label
            data['left']['actual']['output'] = port(1, [1])
            data['left']['actual_artifact'] = encoded(artifact).decode()
            invoke('hidden-' + name + '-label-' + label, actual, data, view=good_view)
    for epsilon in (2**64, Fraction(1, 2**64)):
        data = copy.deepcopy(base)
        data['left']['epsilon'] = data['epsilon'] = dyadic(epsilon)
        invoke('component-arithmetic-capacity-' + str(len(rows)), actual, data)
    # All typed request context fields and every original graph field are independently bound.
    for i in range(1, len(good_view[1])):
        view = copy.deepcopy(good_view)
        view[1][i] = ['substituted-context']
        invoke('qdv-context-' + str(i), actual, base, view=view, error='decoded_view')
    for graph in range(2, 8):
        for field in range(1, 9):
            view = copy.deepcopy(good_view)
            view[graph][field] = ['substituted-graph-field']
            invoke('qdv-graph-' + str(graph) + '-field-' + str(field), actual, base, view=view, error='decoded_view')
    original, graph = inner(actual, base), qdv(good_view)
    for name, packet in [('old-frame', original), ('inspection', envelope('2026', original)),
                         ('caller', envelope('2026', original, graph, qdv(['caller-origin']))),
                         ('trailing-byte', envelope('2026', original, graph) + b'x'),
                         ('truncated', envelope('2026', original, graph)[:-1])]:
        invoke(name, actual, base, packet=packet)
    oversized_header = b'QLV3' + struct.pack('<6I', 2026, 1, (64 << 20) + 1, len(graph), 0, 0) + original + graph
    invoke('oversized-envelope-declaration', actual, base, packet=oversized_header)
    for name, a, r in [('oversized-original-file', b' ' * ((16 << 20) + 1), encoded(base)),
                       ('oversized-request-file', encoded(actual), b' ' * ((16 << 20) + 1))]:
        packet = b'QLV1' + struct.pack('<II', len(a), len(r)) + a + r
        invoke(name, actual, base, packet=envelope('2026', packet, graph))
    pure, pure_packet = pure_comparison(actual, base['actual'], json.loads(base['expected_artifact']),
        base['ideal'], pair(basis('bit'), basis('bit')), pair(basis('bit'), basis('bit')), Fraction(7, 8))
    invoke('whole-parent-frobenius-refuses-same-budget', actual, pure,
           packet=pure_packet, mode='--engineering-pure-check', error='contract')
    assert digest(kernel.read_bytes()) == kernel_sha, 'native checker changed during comparisons'
    assert digest(Path(__file__).read_bytes()) == script_sha, 'comparison source changed during validation'
    summary = dict(status='passed', kernel_sha256=kernel_sha, comparison_script_sha256=script_sha, native_cases=len(rows),
        max_physical_qubits=2, retention=retention, independent_exact_oracle=oracle, records=rows,
        source_preservation_verified=False, target_resources_verified=False, issue_completion_credit=False)
    if record:
        (record / 'validation.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({key: value for key, value in summary.items() if key != 'records'}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-only', action='store_true')
    parser.add_argument('--kernel', type=Path, default=os.environ.get('QLEISLI_KERNEL'))
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    if args.baseline_only:
        print(json.dumps(dict(status='passed', **retained())))
    else:
        assert args.kernel, 'select the separately rebuilt/audited native checker'
        live(Path(args.kernel).resolve(), args.record)
