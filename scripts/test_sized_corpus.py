#!/usr/bin/env python3
"""Actual sized Xor/GHZ source, native reconstruction and independent oracles.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import cmath
from collections import defaultdict
import copy
import hashlib
import json
import math
import os
from pathlib import Path
import re
import subprocess
import tempfile

from compile_sized_corpus import SourceError, compile_source, text, wires

ROOT = Path(__file__).resolve().parent.parent
CASES = {
    'xor': ('corpus/sized/qualtran_xor/bitwise.qli', 'xor_into', [0, 1, 2, 4, 8]),
    'ghz': ('corpus/sized/katas_ghz/prepare.qli', 'ghz', [1, 2, 3, 8]),
}


def circuit_action(artifact):
    """Independent diagnostic interpreter of the actual accepted IR.

    Propagate coordinate maps; expand only the small diagnostic gate schedule.
    There is no algorithm-name recognition or matrix from the producer.
    """
    gates = []

    def walk(index, positions, inverse=False, controls=()):
        definition = artifact['definitions'][index]
        body, header = definition['body'], definition['interface']
        tag = body['tag']
        if tag == 'inverse':
            return walk(body['definition'], positions, not inverse, controls)
        if tag == 'sequence':
            children = list(body['children'])
            for child in reversed(children) if inverse else children:
                positions = walk(child, positions, inverse, controls)
            return positions
        if tag == 'tensor':
            child = artifact['definitions'][body['left']]
            width = len(wires(child['interface']['outputs' if inverse else 'inputs']['quantum']))
            return (walk(body['left'], positions[:width], inverse, controls) +
                    walk(body['right'], positions[width:], inverse, controls))
        if tag == 'control':
            active = controls+((positions[0], int(body['polarity'])),)
            after = walk(body['definition'], positions[1:], inverse, active)
            if after != positions[1:]:
                # A provider's final coordinate permutation acts only in its
                # active control sector; it is not a global relabelling.
                gates.append(('permute', tuple(positions[1:]), active, tuple(after)))
            return positions
        if tag == 'repeat':
            for _ in range(body['count']):
                positions = walk(body['definition'], positions, inverse, controls)
            return positions
        if tag == 'dyadic_phase':
            assert len(positions) == 1
            angle = 2*math.pi*body['j']/(1 << body['k']) * (-1 if inverse else 1)
            gates.append(('phase', positions[0], controls, cmath.exp(1j*angle)))
            return positions
        if tag in ('structural', 'rewire'):
            before = wires(header['inputs']['quantum'])
            after = wires(header['outputs']['quantum'])
            permutation = (body['permutation']['axes'] if tag == 'rewire'
                           else [before.index(a) for a in after])
            if inverse:
                permutation = [permutation.index(i) for i in range(len(permutation))]
            return [positions[i] for i in permutation]
        if tag == 'leaf':
            program = json.loads(body['program'])
            ops = program['programs'][program['root']]['operations']
            assert len(positions) == len(ops) == 1
            assert ops[0]['tag'] == 'gate' and ops[0]['gate'] in ('h', 'x')
            gates.append((ops[0]['gate'], positions[0], controls, 1))
            return positions  # H and X are their own inverses.
        raise AssertionError(f'unsupported diagnostic node {tag}')

    root = artifact['entry']['implementation']
    width = len(wires(artifact['definitions'][root]['interface']['inputs']['quantum']))
    outputs = walk(root, list(range(width)))

    def apply(column):
        state = dict(column)
        for gate, target, controls, phase in gates:
            result = defaultdict(complex)
            for label, amplitude in state.items():
                if not all((label >> axis)&1 == polarity for axis, polarity in controls):
                    result[label] += amplitude
                elif gate == 'x':
                    result[label ^ (1 << target)] += amplitude
                elif gate == 'phase':
                    result[label] += amplitude * (phase if (label >> target)&1 else 1)
                elif gate == 'permute':
                    mapped = label
                    for dst, src in zip(target, phase):
                        mapped = (mapped & ~(1 << dst)) | (((label >> src)&1) << dst)
                    result[mapped] += amplitude
                else:
                    low = label & ~(1 << target)
                    result[low] += amplitude/math.sqrt(2)
                    result[low | (1 << target)] += amplitude/math.sqrt(2) * (-1 if (label >> target)&1 else 1)
            state = result
        result = defaultdict(complex)
        for label, amplitude in state.items():
            mapped = sum(((label >> axis)&1) << i for i, axis in enumerate(outputs))
            result[mapped] += amplitude
        return dict(result)
    return apply, len(gates)


def expected(name, width, column):
    """Direct formulas, independent of source and its generated circuit."""
    out = defaultdict(complex)
    for label, amplitude in column.items():
        if name == 'xor':
            mask = (1 << width)-1
            x, y = label & mask, label >> width
            out[x | ((y ^ x) << width)] += amplitude
        else:
            low = label & 1
            tail = label & ~1
            out[tail] += amplitude/math.sqrt(2)
            out[(tail ^ ((1 << width)-2)) | 1] += amplitude/math.sqrt(2) * (-1 if low else 1)
    return dict(out)


def difference(first, second):
    return max((abs(first.get(i, 0)-second.get(i, 0)) for i in first.keys() | second.keys()), default=0)


def semantic(name, width, artifact, exhaustive=True):
    apply, gate_count = circuit_action(artifact)
    size = 1 << (2*width if name == 'xor' else width)
    labels = range(size) if exhaustive else sorted({0, 1, size//2, size-1})
    errors = [difference(apply({label: 1}), expected(name, width, {label: 1})) for label in labels]
    # Two coherent columns of a joint state with an untouched reference bit.
    # Keep complex amplitudes: output probabilities cannot detect a sign fault.
    for r in range(2):
        column = {i: complex((i+2*r)%7-3, (3*i+r)%5-2)
                  for i in sorted({0, 1 % size, size//3, size//2, size-1})}
        norm = math.sqrt(sum(abs(a)**2 for a in column.values()))
        column = {i: a/(norm*math.sqrt(2)) for i, a in column.items()}
        errors.append(difference(apply(column), expected(name, width, column)))
    return dict(basis_columns=len(labels), reference_columns=2,
                maximum_error=max(errors), executed_gates=gate_count)


def rejected_sources(sources):
    xor, ghz = sources['xor'], sources['ghz']
    cases = [
        ('alias', xor.replace('(x,y) {', '(x,x) {'), 'xor_into', 2),
        ('empty-alias', xor.replace('(x,y) {', '(x,x) {'), 'xor_into', 0),
        ('dropped-zero-owner', '''pub unitary fn drop[static n: Nat]
            (x: Q<Bits<n>>, y: Q<Bits<n>>) -> Q<Bits<n>> { x }''', 'drop', 0),
        ('empty-body-alias', xor.replace('cnot(a,b)', 'cnot(a,a)'), 'xor_into', 0),
        ('out-of-range', xor.replace('take_bit[n,k](x)', 'take_bit[n,n](x)'), 'xor_into', 2),
        ('wrong-width', xor.replace('take_bit[n,k](x)', 'take_bit[n+1,k](x)'), 'xor_into', 2),
        ('wrong-reinsert-width', xor.replace('put_bit[n,k](a,x)', 'put_bit[n-1,k](a,x)'), 'xor_into', 2),
        ('owner-shadow', xor.replace('let (a,x)', 'let (y,x)'), 'xor_into', 2),
        ('tuple-shape', xor.replace('let (x,y) = pair', 'let ((x,y),z) = pair'), 'xor_into', 2),
        ('unknown-import', xor.replace('std::quantum::cnot', 'other::quantum::cnot'), 'xor_into', 2),
        ('nonlinear-size', xor.replace('0..n', '0..n*n'), 'xor_into', 2),
        ('underflow', xor.replace('0..n', '0..n-1'), 'xor_into', 0),
        ('zero-ghz', ghz, 'ghz', 0),
        ('register-capacity', xor, 'xor_into', 9),
        ('implicit-bit-view', '''use std::quantum::h;
            pub unitary fn bad[static n: Nat](q: Q<Bits<n>>) -> Q<Bits<n>> { h(q) }''', 'bad', 1),
    ]
    results = []
    for name, source, entry, width in cases:
        try:
            compile_source(source, entry, {'n': width})
        except SourceError as error:
            results.append(dict(case=name, diagnostic=str(error)))
        else:
            raise AssertionError(f'accepted invalid source {name}')
    # The 16-wire total is independent of the maximum width of each register.
    # Check a complete owner-preserving three-register return to reach capacity.
    overflow = '''pub unitary fn wide[static n: Nat](x: Q<Bits<n>>, y: Q<Bits<n>>, z: Q<Bit>)
        -> (Q<Bits<n>>, Q<Bits<n>>, Q<Bit>) { (x,y,z) }'''
    try:
        compile_source(overflow, 'wide', {'n': 8})
    except SourceError as error:
        assert '16-wire' in str(error)
        results.append(dict(case='total-capacity', diagnostic=str(error)))
    else:
        raise AssertionError('accepted 17 wires')
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    parser.add_argument('--small', action='store_true', help='use only positive widths through three; retain source rejection checks')
    args = parser.parse_args()
    cases = {name: (path, entry, [w for w in widths if not args.small or w <= 3])
             for name, (path, entry, widths) in CASES.items()}
    sources = {name: (ROOT/path).read_text() for name, (path, _, _) in CASES.items()}
    for name, (_, entry, _) in CASES.items():
        original = compile_source(sources[name], entry, {'n': 2})
        renamed = compile_source(sources[name].replace('fn '+entry, 'fn arbitrary_name'),
                                 'arbitrary_name', {'n': 2})
        assert original == renamed, 'a function name must not select an algorithm'
        direct = compile_source(sources[name], entry, {'n': 2}, compact=False)
        a, _ = circuit_action(original)
        b, _ = circuit_action(direct)
        for label in range(16 if name == 'xor' else 4):
            assert difference(a({label: 1}), b({label: 1})) < 1e-12
    artifacts, expected_native = {}, {}
    for name, (_, entry, widths) in cases.items():
        for width in widths:
            key = f'{name}-{width}'
            artifacts[key] = compile_source(sources[name], entry, {'n': width})
            expected_native[key] = 'ok'

    negatives = rejected_sources(sources)
    fault_sources = {
        'xor-wrong-axis': ('xor', sources['xor'].replace('take_bit[n,k](y)', 'take_bit[n,n-1-k](y)').replace(
            'put_bit[n,k](b,y)', 'put_bit[n,n-1-k](b,y)')),
        # Keep the injected X gate unshadowed by the source's x register.
        'xor-phase': ('xor', re.sub(r'\bx\b', 'left', sources['xor']).replace('use std::quantum::cnot;',
            'use std::quantum::cnot;\nuse std::quantum::h;\nuse std::quantum::x;').replace(
            'yield (put_bit', 'let a = h(x(h(a)));\n        yield (put_bit')),
        'ghz-no-superposition': ('ghz', sources['ghz'].replace('std::quantum::h', 'std::quantum::x').replace('h(head)', 'x(head)')),
        'ghz-missing-fanout': ('ghz', sources['ghz'].replace('0..n-1', '0..0')),
    }
    for key, (name, source) in fault_sources.items():
        artifacts[key] = compile_source(source, CASES[name][1], {'n': 2})
        expected_native[key] = 'ok'  # Valid circuits, deliberately wrong algorithms.
    for key, tag, error in [('ir-empty-owner', 'structural', 'invalid_ir'),
                            ('ir-wrong-leaf', 'leaf', 'contract')]:
        bad = copy.deepcopy(artifacts['xor-2'])
        for definition in bad['definitions']:
            if definition['body']['tag'] != tag:
                continue
            if tag == 'structural':
                definition['interface']['outputs']['quantum'][1]['owner'] = definition['interface']['outputs']['quantum'][0]['owner']
            else:
                program = json.loads(definition['body']['program'])
                program['programs'][0]['operations'][0]['gate'] = 'h'
                definition['body']['program'] = text(program)
            break
        artifacts[key], expected_native[key] = bad, error
    kernel = ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel'
    with tempfile.TemporaryDirectory(prefix='qleisli-sized-corpus-') as tmp:
        directory = Path(tmp)
        for key, artifact in artifacts.items():
            (directory/f'{key}.json').write_text(text(artifact))
        (directory/'cases.txt').write_text(''.join(f'{k}|{v}\n' for k, v in expected_native.items()))
        result = subprocess.run(['cargo', 'test', '--test', 'sized_corpus', 'inspect_source_produced_corpus', '--', '--ignored', '--nocapture'],
            cwd=ROOT, env=os.environ | dict(QLEISLI_HIERARCHY_KERNEL=str(kernel), QLEISLI_SIZED_CORPUS=tmp),
            capture_output=True, text=True, timeout=120)
    rows = [line.split('|')[1:] for line in result.stdout.splitlines() if line.startswith('CORPUS|')]
    report = dict(format='qleisli.sized-corpus-experiment', version=1, status='error',
        scope='small-system' if args.small else 'historical-full-width-selection',
        native=rows, source_rejections=negatives,
        source_sha256={name: hashlib.sha256(source.encode()).hexdigest() for name, source in sources.items()},
        kernel_sha256=hashlib.sha256(kernel.read_bytes()).hexdigest(),
        artifacts={key: dict(sha256=hashlib.sha256(text(a).encode()).hexdigest(),
                   bytes=len(text(a).encode()), definitions=len(a['definitions'])) for key, a in artifacts.items()},
        stdout=result.stdout, stderr=result.stderr)
    if result.returncode == 0:
        assert [row[0] for row in rows] == list(artifacts)
        semantics = {}
        for name, (_, _, widths) in cases.items():
            for width in widths:
                key = f'{name}-{width}'
                check = semantic(name, width, artifacts[key])
                assert check['maximum_error'] < 1e-12, (key, check)
                semantics[key] = check
        report['semantics'] = semantics
        faults = {}
        for key, (name, _) in fault_sources.items():
            check = semantic(name, 2, artifacts[key])
            assert check['maximum_error'] > 0.1, (key, check)
            faults[key] = check
        report['semantic_faults'] = faults
        report['status'] = 'passed-experimental-source-path'
    if args.record:
        args.record.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ('stdout', 'stderr', 'artifacts')}))
    if result.returncode:
        print(result.stdout+result.stderr)
    return result.returncode


if __name__ == '__main__':
    raise SystemExit(main())
