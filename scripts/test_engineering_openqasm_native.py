#!/usr/bin/env python3
"""Check fresh small emitted-target claims; preserved history remains inert.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import base64
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

from native_packet import envelope
from test_native_execution_protocol import qdv

ROOT = Path(__file__).resolve().parents[1]
SESSION = ROOT / 'tests/fixtures/authoring_sessions/engineering-openqasm-v030'
VERSION = tomllib.loads((ROOT / 'Cargo.toml').read_text())['package']['version']
MODE = '--engineering-openqasm-check'
HEADER = 'qleisli.engineering-openqasm-native 1'
FIXED = dict(format='qleisli.engineering-openqasm-request', version=1,
    claim_kind='engineering-target-instrument-bound',
    metric='complete-adjoint-euclidean-operator-norm-v1',
    checker_profile='canonical-target-choi-l1-r8-v1',
    target_profile='openqasm3-canonical-one-qubit-terminal-r8-v1',
    composition='single-component-v1', error_category='implementation-distance')
GATES = ('h', 'x', 'y', 'z', 's', 'sdg', 't', 'tdg')
PREFIX = b'OPENQASM 3.0;\ninclude "stdgates.inc";\nqubit[1] q;\nbit[1] c;\nreset q;\n'
SUFFIX = b'c[0] = measure q[0];\n'
SIGNATURE = dict(input=dict(tag='unit'), result=dict(tag='bit'))


def digest(value):
    return hashlib.sha256(value).hexdigest()


def encoded(value):
    return json.dumps(value, separators=(',', ':'), ensure_ascii=False).encode()


def retained():
    """Read fixed local archive data only, never an archived driver or argv."""
    p = json.loads((SESSION / 'provenance.json').read_text())
    assert p['format'] == 'qleisli.engineering-openqasm-first-capture' and p['version'] == 1
    assert p['kind'] == 'informed-study' and p['maximum_physical_qubits'] == 1
    for key in ('recorded_commands_executed', 'source_export_preservation_established',
                'target_reference_adopted', 'issue_completion_credit'):
        assert p[key] is False
    for name, sha in (
        ('reader-first-observation.json', '50e40c0a4cea0b43cc019ee71bd47338ea2cc8f59818e87c672de2d4ac5137a5'),
        ('native-first-observation.json', '5c1a56714a072ae995206efc335784147a6f5171e77a73228e1c2ea3dd57c55b'),
        ('native-observer-first.json', '952e5278d30884aa54dd120ef486fa46c5e8e8ebfb3391e0c60b23ef6fa93884')):
        assert digest((SESSION / name).read_bytes()) == sha
    assert '`provenance.json`' in (SESSION / 'README.md').read_text()
    a = p['preserved_archive']
    assert a['path'] == 'target-prototype.tar.gz' and a['freeze_path'] == 'prototype-freeze.json'
    raw = (SESSION / a['path']).read_bytes()
    assert len(raw) == a['bytes'] == 26329
    assert digest(raw) == a['sha256'] == '88d18091827a76662ef32665fb465067b443616aa05cdfdedaf88f40f7c2b40a'
    freeze_bytes = (SESSION / a['freeze_path']).read_bytes()
    assert digest(freeze_bytes) == a['freeze_sha256'] == 'cad0fce4a2fd8fda0e127259b3be26fa22ea9367ffbbe8e41bbd4bc2e6af3fd1'
    freeze = json.loads(freeze_bytes)
    assert freeze['temporary_id'] == 'TP-31-TARGET-QASM-01' and freeze['priority'] == 'P1'
    assert freeze['archive']['sha256'] == digest(raw)
    files = {}
    with tarfile.open(fileobj=io.BytesIO(raw), mode='r:gz') as archive:
        for member in archive.getmembers():
            path = PurePosixPath(member.name)
            assert member.isfile() and member.mode in (0o644, 0o755)
            assert not path.is_absolute() and '..' not in path.parts and member.name not in files
            assert member.size <= 1 << 20
            files[member.name] = archive.extractfile(member).read()
    assert len(files) == a['members'] == 114 and set(files) == set(freeze['files'])
    for path, sha in freeze['files'].items():
        assert digest(files[path]) == sha
    for path, sha in json.loads(files['first-sources.json']).items():
        assert digest(files[path]) == sha
    assert len(freeze['cli_records']) == 14
    for name in freeze['cli_records']:
        event = json.loads(files[name])
        assert not event['stderr']
        result = json.loads(event['stdout'])
        assert result['outcome'] == ('ok' if event['exit_code'] == 0 else 'error')
        if name.endswith('-first.json') or name == 'open-functions-export.json':
            assert event['exit_code'] == 1 and result['diagnostics'][0]['code'] == 'invalid_entry'
    for source, call in [('CanonicalTarget.first.lean', 'decoder-attempt01'),
                         ('CanonicalTargetExamples.first.lean', 'examples-attempt01'),
                         ('CanonicalTargetMeaning.first.lean', 'meaning-attempt01'),
                         ('CanonicalGatePhases.first.lean', 'gate-phases-attempt01')]:
        assert files[source] and json.loads(files[call + '.json'])['exit_code'] == 1
        assert b'error:' in files[call + '.stdout.txt']
    assert json.loads(files['decoder-attempt03.json'])['exit_code'] == 1
    assert b'String.fromUTF8' in files['CanonicalTarget.attempt02.lean']
    assert b'did not reduce' in files['examples-attempt01.stdout.txt']
    reader = json.loads((SESSION / 'reader-first-observation.json').read_text())
    assert reader['exit_code'] == 1 and reader['historical_commands_executed'] is False
    assert digest(reader['source_utf8'].encode()) == reader['source_sha256']
    assert "assert b'String.fromUTF8' in files['decoder-attempt03.stdout.txt']" in reader['source_utf8']
    assert 'AssertionError' in reader['stderr']
    native = json.loads((SESSION / 'native-first-observation.json').read_text())
    assert native['historical_commands_executed'] is False
    assert digest(native['source_utf8'].encode()) == native['source_sha256']
    observed = native['observation']['records'][0]
    assert observed['exit_code'] == 1 and observed['stdout'] == HEADER + '\nerror\ninvalid_ir\n'
    assert digest(base64.b64decode(native['packet_base64'], validate=True)) == observed['packet_sha256']
    assert 'root_interface' not in json.loads(json.loads(native['request_utf8'])['expected_artifact'])
    observer = json.loads((SESSION / 'native-observer-first.json').read_text())
    assert observer['kind'] == 'test-observer-no-op-mutation' and observer['historical_commands_executed'] is False
    assert digest(observer['source_utf8'].encode()) == observer['source_sha256']
    assert observer['observation']['exit_code'] == 0
    assert digest(base64.b64decode(observer['packet_base64'], validate=True)) == observer['observation']['packet_sha256']
    assert files['actual.qasm'] == target()
    assert files['ideal.qasm'] == target(('h',))
    oracle = json.loads(files['host-exact-oracle.json'])
    assert oracle['ordered_public_choi_differences'] == ['1/2', '-1/2']
    assert oracle['conservative_l1_bound'] == '1'
    production = json.loads((SESSION / 'production-first.json').read_text())
    assert production['format'] == 'qleisli.engineering-openqasm-production-first-capture'
    assert production['recorded_commands_executed'] is False and production['issue_completion_credit'] is False
    a = production['archive']
    assert a['path'] == 'production-first.tar.gz'
    raw = (SESSION / a['path']).read_bytes()
    assert digest(raw) == a['sha256'] == '34d8dd2047d303a6f4ef090d5ccb12b5ef33f490b2bcfeb4ab517f2c2e93f0e2'
    assert len(raw) == a['bytes'] == 22743
    current = {}
    with tarfile.open(fileobj=io.BytesIO(raw), mode='r:gz') as archive:
        for member in archive.getmembers():
            path = PurePosixPath(member.name)
            assert member.isfile() and member.mode == 0o644 and member.size <= 1 << 20
            assert not path.is_absolute() and '..' not in path.parts and member.name not in current
            current[member.name] = archive.extractfile(member).read()
    assert len(current) == a['members'] == 26 and set(current) == set(production['files'])
    for path, sha in production['files'].items():
        assert digest(current[path]) == sha
    for path, sha in json.loads(current['native/first-sources.json']).items():
        assert digest(current['native/first/' + path]) == sha
    prefix = 'native/QleisliKernel_Qirf_EngineeringOpenQasm.lean.'
    for attempt, status in [('attempt01', 1), ('attempt02', 0)]:
        event = json.loads(current[prefix + attempt + '.json'])
        assert event['exit_code'] == status and digest(current[prefix + attempt + '.lean']) == event['sha256']
    assert b'QleisliKernel.QleisliKernel.Target' in current[prefix + 'attempt01.stdout.txt']
    for row in json.loads(current['rust/source.json']):
        assert digest(current['rust/first/' + row['path']]) == row['sha256']
    compilation = json.loads(current['rust/compile.json'])
    for i, event in enumerate(compilation['commands'], 1):
        assert event['exit_code'] == 0
        assert digest(current[f'rust/compile-{i:02}-attempt01.log']) == event['sha256']
    assert production['observer_failure']['semantic_counterexample'] is False
    assert production['clippy_failure']['production_semantic_change'] is False
    assert b'native_binds_literal_target_gate_word_typed_context_and_both_original_graphs' in current['rust/observer-failure.log']
    assert b'byte_char_slices' in current['rust/clippy-failure.log']
    compiled = json.loads((SESSION / 'compiled-audit-first.json').read_text())
    assert compiled['format'] == 'qleisli.engineering-openqasm-compiled-audit-first-capture'
    assert compiled['recorded_commands_executed'] is False and compiled['issue_completion_credit'] is False
    assert digest(current[compiled['source_in_production_first_archive']]) == compiled['source_sha256']
    assert compiled['named_axiom_audit_was_insufficient'] is True
    a = compiled['archive']
    assert a['path'] == 'compiled-audit-first.tar.gz'
    raw = (SESSION / a['path']).read_bytes()
    assert digest(raw) == a['sha256'] == 'f6cf7762e58afbf07ca77f19f58a770b0a876325e635bf56d8912f709f054870'
    assert len(raw) == a['bytes'] and a['members'] == 2
    audit_files = {}
    with tarfile.open(fileobj=io.BytesIO(raw), mode='r:gz') as archive:
        for member in archive.getmembers():
            assert member.isfile() and member.mode == 0o644 and member.name in ('attribution.json', 'schema.json')
            assert member.name not in audit_files and member.size <= 1 << 20
            audit_files[member.name] = archive.extractfile(member).read()
    assert set(audit_files) == set(compiled['files']) and len(audit_files) == 2
    for name, sha in compiled['files'].items():
        assert digest(audit_files[name]) == sha
    attribution, schema = (json.loads(audit_files[n]) for n in ('attribution.json', 'schema.json'))
    assert attribution['source_sha256'] == compiled['source_sha256']
    assert attribution['schema_sha256'] == digest(audit_files['schema.json'])
    assert schema['status'] == 'error' and schema['commands'][-1]['exit_code'] == 1
    assert 'word._unsafe_rec: partial project declaration' in schema['error']
    return dict(preserved_frozen_files=114, preserved_freeze_records=1,
                preserved_production_files=28, retained_current_harness_failures=3,
                retained_compiled_audit_failures=1, historical_commands_executed=0)


def dyadic(value):
    value = Fraction(value)
    assert value.denominator & (value.denominator - 1) == 0
    return dict(numerator=str(value.numerator), denominator_bits=value.denominator.bit_length() - 1)


ZERO = (Fraction(0),) * 4
ONE = (Fraction(1), *ZERO[1:])
I = (Fraction(0), Fraction(0), Fraction(1), Fraction(0))
ROOT_HALF = (Fraction(0), Fraction(1, 2), Fraction(0), Fraction(0))


def add(a, b):
    return tuple(x + y for x, y in zip(a, b, strict=True))


def neg(a):
    return tuple(-x for x in a)


def multiply(a, b):
    """Exact independent arithmetic in 1,sqrt(2),i,i*sqrt(2)."""
    w, x, y, z = a
    p, q, r, s = b
    return (w*p + 2*x*q - y*r - 2*z*s, w*q + x*p - y*s - z*r,
            w*r + 2*x*s + y*p + 2*z*q, w*s + x*r + y*q + z*p)


def conjugate(a):
    return a[0], a[1], -a[2], -a[3]


def gate_matrix(name):
    return {'h': (ROOT_HALF, ROOT_HALF, ROOT_HALF, neg(ROOT_HALF)),
        'x': (ZERO, ONE, ONE, ZERO), 'y': (ZERO, neg(I), I, ZERO),
        'z': (ONE, ZERO, ZERO, neg(ONE)), 's': (ONE, ZERO, ZERO, I),
        'sdg': (ONE, ZERO, ZERO, neg(I)),
        't': (ONE, ZERO, ZERO, add(ROOT_HALF, multiply(I, ROOT_HALF))),
        'tdg': (ONE, ZERO, ZERO, add(ROOT_HALF, neg(multiply(I, ROOT_HALF))))}[name]


def probabilities(word):
    vector = (ONE, ZERO)
    for name in word:
        a, b, c, d = gate_matrix(name)
        vector = (add(multiply(a, vector[0]), multiply(b, vector[1])),
                  add(multiply(c, vector[0]), multiply(d, vector[1])))
    values = [multiply(conjugate(v), v) for v in vector]
    assert add(*values) == ONE
    return values


def independent_oracle():
    assert gate_matrix('y') != tuple(neg(v) for v in gate_matrix('y'))
    assert gate_matrix('s') != gate_matrix('sdg') and gate_matrix('t') != gate_matrix('tdg')
    assert probabilities(()) == [ONE, ZERO]
    half = (Fraction(1, 2), *ZERO[1:])
    assert probabilities(('h',)) == [half, half]
    gaps = [add(a, neg(b)) for a, b in zip(probabilities(()), probabilities(('h',)), strict=True)]
    assert gaps == [half, neg(half)]
    return dict(ordered_choi_differences=['1/2', '-1/2'], conservative_l1_bound='1',
                arithmetic='exact-Q-sqrt2-complex', pre_observation_phase_sensitive=True)


def target(word=()):
    return PREFIX + b''.join((name + ' q[0];\n').encode() for name in word) + SUFFIX


def word_from_target(value):
    assert value.startswith(PREFIX) and value.endswith(SUFFIX)
    body = value[len(PREFIX):-len(SUFFIX)]
    return tuple(line.removesuffix(' q[0];') for line in body.decode('ascii').splitlines())


def step(name):
    if name == 'h':
        return dict(controls=[], action=dict(tag='hadamard', target=0))
    permutation, phases = ([1, 0], [2, 6]) if name == 'y' else ([0, 1], [0, {'s': 2, 'sdg': 6, 'tdg': 7}[name]])
    return dict(controls=[], action=dict(tag='monomial', indices=[0], permutation=permutation, phases=phases))


def gate_op(name, before, after):
    if name in ('h', 'x', 'z', 't'):
        return dict(tag='gate', gate=name, input=before, output=after)
    return dict(tag='apply_unitary', input=before, output=after, steps=[step(name)])


def port(token, wires):
    return dict(token=token, wires=wires, shape=dict(bits=len(wires)))


def program(word):
    operations = [dict(tag='unpack_unit', input=0), dict(tag='init0', output=1, wire=0)]
    operations += [gate_op(name, i + 1, i + 2) for i, name in enumerate(word)]
    operations.append(dict(tag='measure_z', input=len(word) + 1, output=0))
    return dict(quantum_inputs=[port(0, [])], classical_inputs=[], operations=operations,
                quantum_outputs=[], classical_outputs=[0], declared_effect='observe')


def ideal(word=('h',)):
    return dict(format='qleisli.finite-ir', version=2, profile='finite-meaning-v1',
                programs=[program(word)], evidence=[], sources=[], root=0, root_interface=None)


def request(word=('h',), epsilon=1, majorants=(Fraction(1, 2), Fraction(1, 2))):
    return dict(FIXED, actual_signature=copy.deepcopy(SIGNATURE), expected_signature=copy.deepcopy(SIGNATURE),
        identity=dict(implementation='emitted-canonical-target', specification='independent-original-ideal',
            sources=[dict(path='target-study-𝄞.qli', text='Identity data only; no source/export preservation claim.')]),
        epsilon=dyadic(epsilon), majorants=[dyadic(v) for v in majorants], expected_artifact=encoded(ideal(word)).decode())


def dependency_ideal(data):
    data = copy.deepcopy(data)
    pure = dict(quantum_inputs=[port(0, [0])], classical_inputs=[],
        operations=[dict(tag='apply_unitary', input=0, output=1, steps=[step('h')])],
        quantum_outputs=[1], classical_outputs=[], declared_effect='unitary')
    root = program(())
    root['operations'].insert(2, dict(tag='apply_unitary', input=1, output=2,
        steps=[dict(controls=[], action=dict(tag='contract', indices=[0], evidence=0, adjoint=False))]))
    root['operations'][-1]['input'] = 2
    artifact = ideal(())
    artifact.update(programs=[pure, copy.deepcopy(pure), root], root=2,
        sources=[dict(path='original-H-𝄞.qli', text='Original source identity; not a lowering proof.')],
        evidence=[dict(tag='circuit', signature=dict(tag='bit'), implementation=0, specification=1,
            identity=dict(implementation='H-body', specification='H-independent', sources=[0]))])
    data['expected_artifact'] = encoded(artifact).decode()
    return data


def basis_view(value):
    tag = value['tag']
    if tag == 'pair':
        return [['pair'], *basis_view(value['left']), *basis_view(value['right'])]
    return [[tag, value['width']]] if tag == 'bits' else [[tag]]


def signature_view(value):
    def result(value):
        tag = value['tag']
        if tag == 'pair':
            return [['pair'], *result(value['left']), *result(value['right'])]
        if tag == 'quantum':
            return [['quantum', basis_view(value['basis'])]]
        return [[tag, value['width']]] if tag == 'bits' else [[tag]]
    return ['instrument-signature', basis_view(value['input']), result(value['result'])]


def identity_view(value):
    return ['identity', value['implementation'], value['specification'],
            [['source', s['path'], s['text']] for s in value['sources']]]


def dyadic_view(value):
    return ['dyadic', value['numerator'], value['denominator_bits']]


def step_view(value):
    a = value['action']
    keys = {'hadamard': ['target'], 'monomial': ['indices', 'permutation', 'phases'],
            'contract': ['indices', 'evidence', 'adjoint']}[a['tag']]
    return ['step', [['control', c['index'], c['when_one']] for c in value['controls']],
            [a['tag'], *[a[k] for k in keys]]]


def program_view(value):
    keys = {'unpack_unit': ['input'], 'init0': ['output', 'wire'], 'gate': ['gate', 'input', 'output'],
            'apply_unitary': ['input', 'output', 'steps'], 'measure_z': ['input', 'output']}
    operations = []
    for op in value['operations']:
        fields = [(['h', 'x', 'z', 't'].index(op[k]) if k == 'gate' else
                   [step_view(s) for s in op[k]] if k == 'steps' else op[k]) for k in keys[op['tag']]]
        operations.append([op['tag'].replace('_', '-').replace('measure-z', 'measure'), *fields])
    return ['program', [['port', p['token'], p['wires'], p['shape']['bits']] for p in value['quantum_inputs']],
            value['classical_inputs'], operations, value['quantum_outputs'], value['classical_outputs'],
            ['unitary', 'iso', 'observe'].index(value['declared_effect'])]


def graph_view(value):
    receipts = []
    for evidence in value['evidence']:
        implementation, specification = (value['programs'][evidence[k]] for k in ('implementation', 'specification'))
        identity = evidence['identity']
        matrix = ['matrix', 2, 2, [[dyadic_view(dyadic(c)) for c in v] for v in gate_matrix('h')]]
        receipts.append(['function-evidence', basis_view(evidence['signature']), program_view(implementation),
            program_view(specification), ['identity', identity['implementation'], identity['specification'],
            [['source', value['sources'][i]['path'], value['sources'][i]['text']] for i in identity['sources']]],
            ['circuit', basis_view(evidence['signature']), [step_view(s) for s in implementation['operations'][0]['steps']]],
            matrix, 1, 1])
    root = value['programs'][value['root']]
    return ['finite-graph', value['root'], None, [['source', s['path'], s['text']] for s in value['sources']],
            [program_view(p) for p in value['programs']], receipts, program_view(root), 2, []]


def complete_view(target_bytes, data):
    word = word_from_target(target_bytes)
    context = ['engineering-openqasm-request', *[data[k] for k in FIXED],
        signature_view(data['actual_signature']), signature_view(data['expected_signature']),
        identity_view(data['identity']), dyadic_view(data['epsilon']),
        [dyadic_view(v) for v in data['majorants']], data['expected_artifact']]
    return ['engineering-openqasm', context, list(target_bytes), list(word),
            graph_view(ideal(word)), graph_view(json.loads(data['expected_artifact']))]


def inner(target_bytes, data=None, request_bytes=None):
    r = encoded(data) if request_bytes is None and data is not None else request_bytes or b''
    return b'QLV1' + struct.pack('<II', len(target_bytes), len(r)) + target_bytes + r


def hostile_targets():
    base = target()
    cases = [(name, base.replace(a, b)) for name, a, b in [
        ('header', b'3.0', b'3.1'), ('include', b'stdgates.inc', b'other.inc'),
        ('qubits', b'qubit[1]', b'qubit[2]'), ('bits', b'bit[1] c', b'bit[2] c'),
        ('missing-reset', b'reset q;\n', b''), ('reset-element', b'reset q;', b'reset q[0];'),
        ('readout-wire', b'measure q[0]', b'measure q[1]'), ('result-slot', b'c[0] =', b'c[1] ='),
        ('comment', b'reset q;', b'reset q; // comment'), ('line-ending', b'\n', b'\r\n'),
        ('rotation', SUFFIX, b'rx(0.1) q[0];\n' + SUFFIX),
        ('unknown-gate', SUFFIX, b'sx q[0];\n' + SUFFIX),
        ('wrong-gate-operand', SUFFIX, b'h q[1];\n' + SUFFIX),
        ('two-qubit-gate', SUFFIX, b'cx q[0], q[0];\n' + SUFFIX)]]
    return cases + [('missing-newline', base[:-1]), ('extra-newline', base + b'\n'),
        ('after-measurement', base + b'h q[0];\n'), ('duplicate-measurement', base + SUFFIX),
        ('empty', b''), ('non-ascii', base + b'\xff'), ('nul', base.replace(b'reset', b'\0reset')),
        ('nine-gates', target(('h',) * 9)), ('byte-capacity', b'a' * 1025)]


def live(kernel, record=None):
    retention, oracle = retained(), independent_oracle()
    rows, kernel_sha = [], digest(kernel.read_bytes())
    if record:
        record.mkdir(parents=True, exist_ok=True)

    def invoke(name, target_bytes, data, success=False, view=None, packet=None, error=None, version=VERSION):
        if packet is None:
            packet = envelope(inner(target_bytes, data), qdv(complete_view(target_bytes, data) if view is None else view))
        result = subprocess.run([str(kernel), MODE, version], input=packet, capture_output=True, timeout=60, check=False)
        rows.append(dict(name=name, exit_code=result.returncode, stdout=result.stdout.decode(),
            stderr=result.stderr.decode(), packet_sha256=digest(packet), packet_bytes=len(packet)))
        if record:
            (record / 'observations.json').write_text(json.dumps(dict(kernel_sha256=kernel_sha, records=rows), indent=2) + '\n')
        fields = result.stdout.decode().splitlines()
        assert not result.stderr and fields and fields[0] == HEADER, (name, result)
        if success:
            assert result.returncode == 0 and len(fields) == 4 and fields[1:3] == ['engineering-checked', 'execution'], (name, result)
            assert 0 < int(fields[3]) <= 10_000_000, (name, fields)
        else:
            assert result.returncode == 1 and len(fields) == 3 and fields[1] == 'error', (name, result)
            if error:
                assert fields[2] == error, (name, fields)

    actual, base = target(), request()
    good = complete_view(actual, base)
    invoke('emitted-zero-versus-original-H-epsilon-one', actual, base, True)
    invoke('H-original-exactzero-engineering', target(('h',)), request(epsilon=0, majorants=(0, 0)), True)
    for name in GATES:
        invoke('single-gate-' + name, target((name,)), request((name,), 0, (0, 0)), True)
    invoke('eight-gates', target(('h',) * 8), request((), 0, (0, 0)), True)
    invoke('deterministic-zero-versus-one', actual, request(('x',), 2, (1, 1)), True)
    dependency = dependency_ideal(base)
    invoke('original-H-dependencies-and-source-identity', actual, dependency, True)
    spaced = copy.deepcopy(base)
    spaced['expected_artifact'] = '\n ' + spaced['expected_artifact'] + ' \n'
    invoke('original-ideal-and-request-whitespace', actual, spaced, True,
           packet=envelope(inner(actual, request_bytes=b' ' + encoded(spaced) + b'\n'), qdv(complete_view(actual, spaced))))
    for name, value in hostile_targets():
        invoke('target-' + name, value, base, view=good)
    for field in base:
        changed = copy.deepcopy(base)
        del changed[field]
        invoke('missing-' + field, actual, changed, view=good)
    for field in FIXED:
        changed = copy.deepcopy(base)
        changed[field] = 2 if field == 'version' else 'unsupported'
        invoke('unsupported-' + field, actual, changed, view=good)
    for field, value in [('accepted', True), ('resource_bound', 0), ('gate_word', ['h'])]:
        invoke('extra-' + field, actual, dict(base, **{field: value}), view=good)
    for field in ('actual_signature', 'expected_signature'):
        for part, replacement in [('input', dict(tag='bits', width=0)),
                                  ('input', dict(tag='pair', left=dict(tag='unit'), right=dict(tag='unit'))),
                                  ('result', dict(tag='bits', width=1)),
                                  ('result', dict(tag='pair', left=dict(tag='bit'), right=dict(tag='unit')))]:
            changed = copy.deepcopy(base)
            changed[field][part] = replacement
            invoke('full-tree-' + field + '-' + part + '-' + str(len(rows)), actual, changed, view=good)
    for epsilon in [Fraction(1, 2), 0]:
        changed = copy.deepcopy(base)
        changed['epsilon'] = dyadic(epsilon)
        invoke('tight-epsilon-' + str(epsilon), actual, changed, error='contract')
    for majorants in [[], (Fraction(1, 2),), (Fraction(1, 2),) * 3, (Fraction(1, 4),) * 2]:
        changed = copy.deepcopy(base)
        changed['majorants'] = [dyadic(v) for v in majorants]
        invoke('false-majorants-' + str(len(rows)), actual, changed)
    for slot in ('epsilon', 'majorants'):
        for bound in [dict(numerator='-1', denominator_bits=0), dict(numerator='0', denominator_bits=1),
                      dict(numerator='2', denominator_bits=1), dict(numerator='01', denominator_bits=0),
                      dict(numerator='1', denominator_bits=127), dict(numerator=str(2**127), denominator_bits=0),
                      dict(numerator='runtime', denominator_bits=0)]:
            changed = copy.deepcopy(base)
            if slot == 'majorants':
                changed[slot][0] = bound
            else:
                changed[slot] = bound
            invoke('invalid-' + slot + '-' + str(len(rows)), actual, changed, view=good)
    for field in ('implementation', 'specification', 'sources'):
        changed = copy.deepcopy(base)
        del changed['identity'][field]
        invoke('missing-identity-' + field, actual, changed, view=good)
    for field in ('implementation', 'specification'):
        changed = copy.deepcopy(base)
        changed['identity'][field] = ''
        invoke('empty-identity-' + field, actual, changed, view=good)
    for index in (0, 1):
        changed = copy.deepcopy(dependency)
        artifact = json.loads(changed['expected_artifact'])
        artifact['programs'][index]['operations'][0]['steps'] = [step('s')]
        changed['expected_artifact'] = encoded(artifact).decode()
        invoke('stale-original-H-dependency-' + str(index), actual, changed)
    changed = copy.deepcopy(base)
    artifact = json.loads(changed['expected_artifact'])
    artifact['programs'][0]['quantum_inputs'] = []
    del artifact['programs'][0]['operations'][0]
    changed['expected_artifact'] = encoded(artifact).decode()
    invoke('closed-ideal-cannot-replace-explicit-Unit-owner', actual, changed)
    for slot, fields in [(1, range(15)), (4, range(9)), (5, range(9))]:
        for field in fields:
            view = copy.deepcopy(good)
            view[slot][field] = True
            invoke('qdv-' + str(slot) + '-field-' + str(field), actual, base, view=view, error='decoded_view')
    for slot, replacement in [(0, 'other-claim'), (2, []), (3, ['h'])]:
        view = copy.deepcopy(good)
        view[slot] = replacement
        invoke('qdv-target-data-' + str(slot), actual, base, view=view, error='decoded_view')
    original, graph = inner(actual, base), qdv(good)
    duplicate = b'{"epsilon":' + encoded(base['epsilon']) + b',' + encoded(base)[1:]
    invoke('duplicate-request-field', actual, base, packet=envelope(inner(actual, request_bytes=duplicate), graph))
    for name, packet in [('old-frame', original), ('inspection', envelope(original)),
                         ('caller', envelope(original, graph, qdv(['caller-origin']))),
                         ('trailing-byte', envelope(original, graph) + b'x'),
                         ('truncated', envelope(original, graph)[:-1]),
                         ('missing-request', envelope(inner(actual), graph)),
                         ('oversized-request', envelope(inner(actual, request_bytes=b' ' * ((16 << 20) + 1)), graph))]:
        invoke(name, actual, base, packet=packet)
    invoke('product-version', actual, base, version='0.0.0', error='version')
    assert digest(kernel.read_bytes()) == kernel_sha
    summary = dict(status='passed', kernel_sha256=kernel_sha, comparison_script_sha256=digest(Path(__file__).read_bytes()),
        native_cases=len(rows), maximum_physical_qubits=1, retention=retention, independent_exact_oracle=oracle,
        source_export_preservation_verified=False, target_resources_verified=False, issue_completion_credit=False, records=rows)
    if record:
        (record / 'validation.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'records'}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-only', action='store_true')
    parser.add_argument('--kernel', type=Path, default=os.environ.get('QLEISLI_KERNEL'))
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    if args.baseline_only:
        print(json.dumps(dict(status='passed', **retained(), independent_exact_oracle=independent_oracle())))
    else:
        assert args.kernel, 'select the separately rebuilt/audited native checker'
        live(Path(args.kernel).resolve(), args.record)
