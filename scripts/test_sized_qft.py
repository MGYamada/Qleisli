#!/usr/bin/env python3
"""Shared QFT source, independently requested Fourier meaning and inverse.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import cmath
import copy
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import tempfile

from compile_sized_corpus import Circuit, SourceError, adjoint_artifact, compile_source, port, text
from test_hierarchical_qft import side
from test_sized_corpus import circuit_action, difference

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT/'corpus/sized/qualtran_qft/fourier.qli'
INVERSE_SOURCE = ROOT/'corpus/sized/qualtran_qft/inverse.qli'
WIDTHS = [1, 2, 3, 4, 8]


def canonical_boundary(artifact):
    """Explicitly rename only boundary labels, retaining ordered coordinates."""
    c = Circuit()
    c.definitions = copy.deepcopy(artifact['definitions'])
    c.meanings = copy.deepcopy(artifact['meanings'])
    c.encodings = copy.deepcopy(artifact['encodings'])
    c.proofs = copy.deepcopy(artifact['proofs'])
    entry = artifact['entry']['implementation']
    assert entry == artifact['entry']['proof']
    before, after = c.ends(entry)
    assert len(before) == len(after) == 1 and before[0]['basis'] == after[0]['basis']
    width = len(before[0]['axes'])
    canonical = [port(0, range(width))]
    if before != canonical or after != canonical:
        entry = c.sequence([c.rewire(canonical, before), entry, c.rewire(after, canonical)])
    return dict(format='qleisli.hierarchical-ir', version=1, profile='qpe-dyadic8-v1',
        definitions=c.definitions, meanings=c.meanings, encodings=c.encodings,
        proofs=c.proofs, entry=dict(implementation=entry, proof=entry))


def request(width):
    interface = dict(inputs=side([port(0, range(width))]), outputs=side([port(0, range(width))]))
    return dict(format='qleisli.hierarchy-request', version=1, profile='qpe-dyadic8-v1',
        kind='equation', effect='unitary', interface=interface, entry=0,
        meanings=[dict(interface=interface, body=dict(tag='qft', width=width))])


def expected(width, column, inverse=False):
    size = 1 << width
    sign = -1 if inverse else 1
    return {y: sum(a*cmath.exp(sign*2j*math.pi*x*y/size) for x, a in column.items())/math.sqrt(size)
            for y in range(size)}


def probes(artifact, width, inverse=False):
    apply, gate_count = circuit_action(artifact)
    size = 1 << width
    worst = 0
    for label in range(size):
        column = {label: 1}
        worst = max(worst, difference(apply(column), expected(width, column, inverse)))
    for r in range(2):
        column = {i: complex((i+2*r)%7-3, (3*i+r)%5-2) for i in range(size)}
        norm = math.sqrt(2*sum(abs(a)**2 for a in column.values()))
        column = {i: a/norm for i, a in column.items()}
        worst = max(worst, difference(apply(column), expected(width, column, inverse)))
    return dict(basis_columns=size, reference_columns=2, maximum_error=worst, executed_gates=gate_count)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    parser.add_argument('--small', action='store_true', help='use widths one through three and only a small shared/frame case')
    args = parser.parse_args()
    widths = [w for w in WIDTHS if not args.small or w <= 3]
    source = SOURCE.read_text()
    inverse_source = INVERSE_SOURCE.read_text()
    modules = {'fourier': source, 'inverse': inverse_source}
    artifacts, bindings = {}, {}
    for width in widths:
        key = f'qft-{width}'
        artifacts[key] = compile_source(source, 'fourier', {'n': width})
        artifacts[f'inverse-{width}'] = compile_source(inverse_source, 'inverse_fourier', {'n': width}, modules=modules)
        bindings[key] = (width, 'ok')
        renamed = compile_source(source.replace('fn fourier', 'fn unrelated'), 'unrelated', {'n': width})
        assert renamed == artifacts[key], 'an algorithm name must not determine compilation'

    # Equivalent literal angle spellings normalize exactly, without float tests.
    equivalent = source.replace('controlled_phase[1,n-stage-k]', 'controlled_phase[2,n-stage-k+1]')
    artifacts['equivalent-angle'] = compile_source(equivalent, 'fourier', {'n': 3})
    assert artifacts['equivalent-angle'] == artifacts['qft-3']
    bindings['equivalent-angle'] = (3, 'ok')
    artifacts['wrapped-inverse-3'] = adjoint_artifact(artifacts['qft-3'])
    double_source = '''use fourier::fourier;
        pub unitary fn twice[static n: Nat](q: Q<Bits<n>>) -> Q<Bits<n>> {
            let q = fourier[n](q); fourier[n](q)
        }'''
    shared_width = 3 if args.small else 8
    shared_key = f'shared-twice-{shared_width}'
    artifacts[shared_key] = compile_source(double_source, 'twice', {'n': shared_width}, modules=modules)
    assert sum(d['body']['tag'] == 'leaf' for d in artifacts[shared_key]['definitions']) == shared_width
    framed_source = '''use fourier::fourier;
        pub unitary fn framed[static n: Nat](reference: Q<Bits<n>>, q: Q<Bits<n>>)
            -> (Q<Bits<n>>, Q<Bits<n>>) { (reference, fourier[n](q)) }'''
    artifacts['framed-call-2'] = compile_source(framed_source, 'framed', {'n': 2}, modules=modules)
    if not args.small:
        artifacts['framed-call-8'] = compile_source(framed_source, 'framed', {'n': 8}, modules=modules)

    fault_sources = {
        'missing-reversal': source.replace('k+k+2 <= n', 'k+k+2 <= 0'),
        'missing-phase': source.replace('0..n-1-stage carry pair', '0..0 carry pair'),
        'wrong-phase': source.replace('controlled_phase[1,n-stage-k]', 'controlled_phase[2,n-stage-k]'),
        'wrong-h': source.replace('std::quantum::h', 'std::quantum::x').replace('h(target)', 'x(target)'),
    }
    for key, changed in fault_sources.items():
        artifacts[key] = canonical_boundary(compile_source(changed, 'fourier', {'n': 2}))
        bindings[key] = (2, 'contract')
    artifacts['inverse-changed-dependency'] = compile_source(inverse_source, 'inverse_fourier', {'n': 2},
        modules={'fourier': fault_sources['wrong-phase'], 'inverse': inverse_source})

    rejects = [
        ('zero-width', source, 0), ('oversized-register', source, 9),
        ('false-premise', source.replace('n >= 1', 'n <= 0'), 2),
        ('angle-denominator', source.replace('controlled_phase[1,n-stage-k]', 'controlled_phase[1,9]'), 2),
        ('unnormalized-angle', source.replace('controlled_phase[1,n-stage-k]', 'controlled_phase[4,2]'), 2),
        ('alias-control', source.replace('(control,target)', '(control,control)'), 2),
        ('unselected-branch-alias', source.replace('put_bit[n,k](high,put_bit[n-1,n-2-k](low,rest))',
                                               'put_bit[n,k](high,put_bit[n-1,n-2-k](high,rest))'), 1),
        ('unselected-static-name', source.replace('take_bit[n,k](register)', 'take_bit[n,unknown](register)'), 1),
    ]
    source_rejections = []
    for key, changed, width in rejects:
        try:
            compile_source(changed, 'fourier', {'n': width})
        except SourceError as error:
            source_rejections.append(dict(case=key, diagnostic=str(error)))
        else:
            raise AssertionError(f'invalid source accepted: {key}')
    def reject_call(key, changed, entry, library):
        try:
            compile_source(changed, entry, {'n': 2}, modules=library)
        except SourceError as error:
            source_rejections.append(dict(case=key, diagnostic=str(error)))
        else:
            raise AssertionError(f'invalid operation call accepted: {key}')
    reject_call('unknown-module', inverse_source, 'inverse_fourier', {})
    reject_call('unknown-imported-declaration', inverse_source, 'inverse_fourier',
                {'fourier': source.replace('fn fourier', 'fn different')})
    reject_call('missing-static-argument', inverse_source.replace('fourier[n]', 'fourier[n,1]'),
                'inverse_fourier', modules)
    reject_call('operation-type-mismatch', inverse_source.replace('fourier[n]', 'fourier[n+1]'),
                'inverse_fourier', modules)
    cycle = '''use cycle::looping;
        pub unitary fn looping[static n: Nat](q: Q<Bits<n>>) -> Q<Bits<n>> { looping[n](q) }'''
    reject_call('operation-cycle', cycle, 'looping', {'cycle': cycle})
    helper = '''pub unitary fn idle[static n: Nat, static tag: Nat](q: Q<Bits<n>>) -> Q<Bits<n>> {
        for static i in 0..600 carry state = q { yield state; }
    }'''
    consumer = '''use helper::idle;
        pub unitary fn over[static n: Nat](q: Q<Bits<n>>) -> Q<Bits<n>> {
            let q = idle[n,0](q); idle[n,1](q)
        }'''
    reject_call('aggregate-source-work', consumer, 'over', {'helper': helper})

    kernel = ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel'
    command = ['cargo', 'test', '--test', 'sized_corpus', 'check_source_fourier_contracts', '--', '--ignored', '--nocapture']
    with tempfile.TemporaryDirectory(prefix='qleisli-sized-qft-') as tmp:
        directory = Path(tmp)
        for key, artifact in artifacts.items():
            (directory/f'{key}.json').write_text(text(artifact))
        for width in widths:
            (directory/f'request-{width}.json').write_text(text(request(width)))
        (directory/'cases.txt').write_text(''.join(
            f'{key}|request-{bindings[key][0]}.json|{bindings[key][1]}\n' if key in bindings else f'{key}||\n'
            for key in artifacts))
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=120,
            env=os.environ | dict(QLEISLI_HIERARCHY_KERNEL=str(kernel), QLEISLI_SIZED_QFT=tmp))
    report = dict(format='qleisli.sized-qft-experiment', version=1, status='error', command=command,
        scope='small-system' if args.small else 'historical-full-width-selection',
        kernel_sha256=hashlib.sha256(kernel.read_bytes()).hexdigest(),
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        inverse_source_sha256=hashlib.sha256(inverse_source.encode()).hexdigest(),
        source_rejections=source_rejections,
        artifacts={key: dict(sha256=hashlib.sha256(text(a).encode()).hexdigest(),
            bytes=len(text(a).encode()), definitions=len(a['definitions'])) for key, a in artifacts.items()},
        native=[line.split('|')[1:] for line in result.stdout.splitlines() if line.startswith('SIZED-FOURIER|')],
        stdout=result.stdout, stderr=result.stderr)
    if args.record:
        args.record.write_text(json.dumps(report, indent=2)+'\n')
    if result.returncode:
        print(result.stdout+result.stderr)
        return result.returncode
    assert len(report['native']) == len(artifacts)+len(bindings)
    print('Fresh native and named Fourier checks passed.', flush=True)

    semantic, inverses, roundtrips = {}, {}, {}
    for width in widths:
        forward = artifacts[f'qft-{width}']
        inverse = artifacts[f'inverse-{width}']
        semantic[str(width)] = probes(forward, width)
        inverses[str(width)] = probes(inverse, width, True)
        assert semantic[str(width)]['maximum_error'] < 1e-10, semantic[str(width)]
        assert inverses[str(width)]['maximum_error'] < 1e-10, inverses[str(width)]
        apply, _ = circuit_action(forward)
        undo, _ = circuit_action(inverse)
        column = {i: complex(i%7-3, i%5-2) for i in range(1 << width)}
        norm = math.sqrt(sum(abs(a)**2 for a in column.values()))
        column = {i: a/norm for i, a in column.items()}
        roundtrips[str(width)] = max(difference(undo(apply(column)), column),
                                    difference(apply(undo(column)), column))
        assert roundtrips[str(width)] < 1e-10
        if width <= 3:
            direct = compile_source(source, 'fourier', {'n': width}, compact=False)
            evaluate, _ = circuit_action(direct)
            assert difference(evaluate(column), apply(column)) < 1e-10
        print(f'Width {width}: all forward/inverse columns and reference probes passed.', flush=True)
    faults = {key: probes(artifacts[key], 2) for key in fault_sources}
    faults['inverse-changed-dependency'] = probes(artifacts['inverse-changed-dependency'], 2, True)
    assert all(row['maximum_error'] > 0.1 for row in faults.values()), faults
    twice, repeated_gates = circuit_action(artifacts[shared_key])
    for label in range(1 << shared_width):
        assert difference(twice({label: 1}), {(-label) % (1 << shared_width): 1}) < 1e-10
    assert probes(artifacts['wrapped-inverse-3'], 3, True)['maximum_error'] < 1e-10
    framed, _ = circuit_action(artifacts['framed-call-2'])
    frame_error = 0
    for label in range(16):
        reference, target = label & 3, label >> 2
        target_column = expected(2, {target: 1})
        wanted = {reference | (y << 2): a for y, a in target_column.items()}
        frame_error = max(frame_error, difference(framed({label: 1}), wanted))
    entangled = {0: 1/math.sqrt(2), 15: 1j/math.sqrt(2)}
    wanted = {r | (y << 2): a*scale for r, target, scale in [(0, 0, 1/math.sqrt(2)), (3, 3, 1j/math.sqrt(2))]
              for y, a in expected(2, {target: 1}).items()}
    frame_error = max(frame_error, difference(framed(entangled), wanted))
    assert frame_error < 1e-10
    report.update(status='passed-experimental-source-path', forward=semantic, inverse=inverses,
                  roundtrip_errors=roundtrips, semantic_faults=faults,
                  shared_call=dict(basis_columns=1 << shared_width, finite_leaves=shared_width, executed_gates=repeated_gates),
                  framed_call=dict(basis_columns=16, entangled_vectors=1, maximum_error=frame_error))
    if args.record:
        args.record.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ('stdout', 'stderr', 'artifacts')}))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
