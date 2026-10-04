#!/usr/bin/env python3
"""Shared coherent QPE source and independent full-column/reference diagnostics.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Remaining validation uses small qubit systems by the 2026-09-30 user decision.
The measured Bits API remains open.
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
import subprocess
import tempfile

from compile_sized_corpus import Operation, SourceError, compile_source, text
from test_sized_corpus import circuit_action, difference

ROOT = Path(__file__).resolve().parent.parent
DIRECTORY = ROOT/'corpus/sized/qualtran_qpe'


def modules():
    result = {p.stem: p.read_text() for p in DIRECTORY.glob('*.qli')}
    result['fourier'] = (ROOT/'corpus/sized/qualtran_qft/fourier.qli').read_text()
    return result


def compile_case(sources, n, m, j=1, d=3):
    return compile_source(sources['estimation'], 'estimate', dict(n=n, m=m), modules=sources,
                          operations={'U': Operation('evolution::evolve', (n, j, d))})


def expected(n, m, column, j=1, d=3, provider='phase'):
    """Direct Walsh/DFT sum with analytically specified powers of the provider.

    Read no proposed meaning, graph or trace. Also covers arbitrary phase input,
    non-basis eigenvectors and an actual target coordinate permutation.
    """
    size = 1 << m
    result = defaultdict(complex)
    for label, amplitude in column.items():
        a, b = label & (size-1), label >> m
        for s in range(size):
            if provider == 'rotate':
                target = b
                for _ in range(s % n):
                    target = (target >> 1) | ((target & 1) << (n-1))
                powers = {target: 1}
            elif provider == 'global':
                powers = {b: cmath.exp(2j*math.pi*j*s/(1 << d))}
            elif provider == 'conjugated':
                phase = cmath.exp(2j*math.pi*j*s/(1 << d))
                powers = {b: (1+phase)/2, b ^ 1: (1-phase)/2}
            else:
                powers = {b: cmath.exp(2j*math.pi*j*s*(b & 1)/(1 << d))}
            sign = (-1) ** ((a & s).bit_count())
            for y in range(size):
                factor = amplitude * sign * cmath.exp(-2j*math.pi*s*y/size)/size
                for target, weight in powers.items():
                    result[y | (target << m)] += factor*weight
    return dict(result)


def probes(artifact, n, m, j=1, d=3, provider='phase'):
    evaluate, gates = circuit_action(artifact)
    maximum = 0
    for label in range(1 << (n+m)):
        column = {label: 1}
        maximum = max(maximum, difference(evaluate(column), expected(n, m, column, j, d, provider)))
    # The two columns are unnormalized branches of one state entangled with a
    # reference qubit. Compare complex amplitudes without phase alignment.
    dimension = 1 << (n+m)
    refs = [{0: 1/math.sqrt(3), dimension-1: 1j/math.sqrt(6)},
            {1: (1+1j)/math.sqrt(12), dimension-2: -1/math.sqrt(3)}]
    for column in refs:
        maximum = max(maximum, difference(evaluate(column), expected(n, m, column, j, d, provider)))
    # Read the final quantum phase register diagnostically, retaining target
    # vectors per branch; this is not a production Bits measurement implementation.
    initial = {0: 1/math.sqrt(2), 1 << m: 1j/math.sqrt(2)}
    actual, wanted = evaluate(initial), expected(n, m, initial, j, d, provider)
    branch_error = max(difference({x >> m: z for x, z in actual.items() if x % (1 << m) == y},
                                 {x >> m: z for x, z in wanted.items() if x % (1 << m) == y})
                       for y in range(1 << m))
    maximum = max(maximum, branch_error)
    return dict(basis_columns=dimension, reference_columns=2, diagnostic_phase_branches=1 << m,
                maximum_error=maximum, executed_instructions=gates)


def source_rejections(source):
    cases = [
        ('missing-controlled-access', source['estimation'].replace(', Controlled(U)', '')),
        ('apply-is-not-controlled', source['estimation'].replace('Controlled(U)', 'Apply(U)')),
        ('adjoint-is-not-controlled', source['estimation'].replace('Controlled(U)', 'Adjoint(U)')),
        ('missing-access-empty-loop', source['estimation'].replace(', Controlled(U)', '').replace('0..m carry', '0..0 carry')),
        ('missing-access-zero-repeat', source['estimation'].replace(', Controlled(U)', '').replace('2^k,U', '0,U')),
        ('unknown-access-parameter', source['estimation'].replace('Controlled(U)', 'Controlled(V)')),
        ('duplicate-access', source['estimation'].replace('Controlled(U)', 'Controlled(U), Controlled(U)')),
        ('duplicate-operation-parameter', source['estimation'].replace('static U: Op<Bits<n>>', 'static U: Op<Bits<n>>, static U: Op<Bits<n>>')),
        ('alias-control', source['estimation'].replace('(control,target);', '(control,control);')),
        ('capture-outside-carry', source['estimation'].replace('carry pair = (phase,target)', 'carry pair = phase')),
        ('unbound-count', source['estimation'].replace('2^k,U', '2^missing,U')),
        ('count-exponent-limit', source['estimation'].replace('2^k,U', '2^9,U')),
        ('count-limit', source['estimation'].replace('2^k,U', '257,U')),
        ('composed-count-limit', source['estimation'].replace('repeat_op(2^k,U)', 'repeat_op(256,repeat_op(2,U))')),
        ('non-two-power-base', source['estimation'].replace('2^k,U', '3^k,U')),
        ('ambiguous-power-suffix', source['estimation'].replace('2^k,U', '2^k+1,U')),
        ('nonlinear-size', source['estimation'].replace('Q<Bits<m>>', 'Q<Bits<2^m>>')),
        ('operation-shadow', source['estimation'].replace('let phase = hadamard_bits', 'let U = hadamard_bits')),
        ('wrong-provider-type', source['estimation'].replace('Op<Bits<n>>', 'Op<Bits<n+1>>')),
    ]
    result = []
    for name, text_source in cases:
        changed = source | {'estimation': text_source}
        try:
            compile_case(changed, 1, 3)
        except SourceError as e:
            result.append(dict(case=name, diagnostic=str(e)))
        else:
            raise AssertionError('invalid source accepted: '+name)
    for name, n, m in [('zero-target', 0, 3), ('zero-phase', 1, 0), ('wide-target', 9, 3)]:
        try:
            compile_case(source, n, m)
        except SourceError as e:
            result.append(dict(case=name, diagnostic=str(e)))
        else:
            raise AssertionError(name)
    for name, source_change, providers in [
        ('missing-provider', source, {}),
        ('unknown-provider', source, {'U': Operation('missing::evolve', (1, 1, 3))}),
        ('wrong-provider-arity', source, {'U': Operation('evolution::evolve', (1,))}),
        ('false-provider-premise-at-zero', source | {
            'evolution': source['evolution'].replace('n >= 1', 'n >= 2'),
            'estimation': source['estimation'].replace('2^k,U', '0,U')}, {'U': Operation('evolution::evolve', (1, 1, 3))}),
        ('invalid-unused-provider', source | {
            'evolution': source['evolution'].replace('phase[j,d](bit)', 'phase[j,d](rest)'),
            'estimation': source['estimation'].replace('0..m carry', '0..0 carry')}, {'U': Operation('evolution::evolve', (1, 1, 3))}),
    ]:
        try:
            compile_source(source_change['estimation'], 'estimate', dict(n=1, m=3), modules=source_change, operations=providers)
        except SourceError as e:
            result.append(dict(case=name, diagnostic=str(e)))
        else:
            raise AssertionError(name)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    source = modules()
    artifacts = {f'qpe-{n}-{m}': compile_case(source, n, m) for n, m in [(1, 3), (2, 4)]}
    params = {'qpe-1-3': (1, 3, 1, 3, 'phase'), 'qpe-2-4': (2, 4, 1, 3, 'phase')}
    artifacts['off-grid'] = compile_case(source, 1, 3, 1, 5)
    params['off-grid'] = (1, 3, 1, 5, 'phase')
    for name, expression, kind in [
        ('non-basis', 'h(phase[j,d](h(bit)))', 'conjugated'),
        ('global-phase', 'x(phase[j,d](x(phase[j,d](bit))))', 'global'),
    ]:
        changed = source | {'evolution': source['evolution'].replace('use std::quantum::phase;',
            'use std::quantum::phase;\nuse std::quantum::h;\nuse std::quantum::x;').replace('phase[j,d](bit)', expression)}
        artifacts[name] = compile_case(changed, 1, 3)
        params[name] = (1, 3, 1, 3, kind)
    swap = source['evolution'].replace('put_bit[n,0](bit,rest)', 'put_bit[n,n-1](bit,rest)').replace('phase[j,d](bit)', 'bit')
    for name, n, m in [('permuted-target', 2, 3), ('cyclic-target', 3, 2)]:
        artifacts[name] = compile_case(source | {'evolution': swap}, n, m)
        params[name] = (n, m, 1, 3, 'rotate')
    mutations = {
        'wrong-power-order': source['estimation'].replace('2^k,U', '2^(m-1-k),U'),
        'missing-high-power': source['estimation'].replace('0..m carry', '0..m-1 carry'),
        'wrong-fourier-sign': source['estimation'].replace('adjoint(fourier[m],phase)', 'fourier[m](phase)'),
        'missing-hadamards': source['estimation'].replace('hadamard_bits[m](phase)', 'phase'),
    }
    for name, changed in mutations.items():
        artifacts[name] = compile_case(source | {'estimation': changed}, 1, 3)
    artifacts['wrong-provider-phase'] = compile_case(source, 1, 3, 3, 3)
    # Zero repeat retains a checked real provider, but changes the algorithm.
    artifacts['zero-repeat'] = compile_case(source | {'estimation': source['estimation'].replace('2^k,U', '0,U')}, 1, 3)
    mutations['wrong-provider-phase'] = ''
    mutations['zero-repeat'] = ''
    malformed = {}
    for name in ('false-finite-equation', 'false-repeat-equation'):
        candidate = copy.deepcopy(artifacts['qpe-1-3'])
        for definition in candidate['definitions']:
            body = definition['body']
            if name == 'false-finite-equation' and body['tag'] == 'leaf':
                packet = json.loads(body['program'])
                packet['programs'][packet['root']]['operations'][0]['gate'] = 'x'
                body['program'] = text(packet)
                break
            if name == 'false-repeat-equation' and body['tag'] == 'repeat':
                body['count'] += 1
                break
        artifacts[name] = candidate
        malformed[name] = 'contract'
    report = dict(format='qleisli.sized-qpe-experiment', version=1,
                  status='passed-small-coherent-source-path',
                  scope='Unitary coherent core only; measured Bits API, named QPE contract and production execution remain open.',
                  validation_selection='Small qubit systems only, as requested on 2026-09-30; no new maximum-size generation or check. Earlier (8,8) limit is retained in the authoring history.',
                  source_sha256={key: hashlib.sha256(value.encode()).hexdigest() for key, value in source.items()},
                  producer_sha256=hashlib.sha256((ROOT/'scripts/compile_sized_corpus.py').read_bytes()).hexdigest(),
                  diagnostic_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  source_rejections=source_rejections(source))
    kernel = ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel'
    report['kernel_sha256'] = hashlib.sha256(kernel.read_bytes()).hexdigest()
    with tempfile.TemporaryDirectory(prefix='qleisli-sized-qpe-') as directory:
        directory = Path(directory)
        for name, artifact in artifacts.items():
            (directory/f'{name}.json').write_text(text(artifact))
        (directory/'cases.txt').write_text(''.join(name+'|'+malformed.get(name, 'ok')+'\n' for name in artifacts))
        command = ['cargo', 'test', '--test', 'sized_corpus', 'inspect_source_produced_corpus', '--', '--ignored', '--nocapture']
        run = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, env=os.environ | {
            'QLEISLI_HIERARCHY_KERNEL': str(kernel), 'QLEISLI_SIZED_CORPUS': str(directory)})
        report.update(command=command, stdout=run.stdout, stderr=run.stderr, exit_code=run.returncode)
        report['native'] = [line.split('|')[1:] for line in run.stdout.splitlines() if line.startswith('CORPUS|')]
    if run.returncode:
        if args.record:
            args.record.write_text(json.dumps(report, indent=2)+'\n')
        print(run.stdout+run.stderr)
        return 1
    print('Small-system native coherent source checks completed; maximum-size checks omitted by user decision.', flush=True)
    semantic = {name: probes(artifacts[name], *param) for name, param in params.items()}
    assert all(row['maximum_error'] < 1e-10 for row in semantic.values()), semantic
    faults = {name: probes(artifacts[name], 1, 3) for name in mutations}
    assert all(row['maximum_error'] > 0.1 for row in faults.values()), faults
    # H P H must not silently behave as P, and global phase cannot be quotiented
    # away before coherent control. Check these are distinguishing tests.
    assert probes(artifacts['non-basis'], 1, 3)['maximum_error'] > 0.1
    assert probes(artifacts['global-phase'], 1, 3)['maximum_error'] > 0.1
    report.update(semantics=semantic, semantic_faults=faults,
                  generated_artifacts={name: dict(definitions=len(a['definitions']), bytes=len(text(a).encode())) for name,a in artifacts.items()})
    if args.record:
        args.record.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('stdout', 'stderr', 'source_rejections')}))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
