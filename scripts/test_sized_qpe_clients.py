#!/usr/bin/env python3
"""Small coherent order/amplitude clients of the same shared QPE source.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Local integration material, not a fourth external corpus or measured Bits API.
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


def sources():
    result = {p.stem: p.read_text() for directory in ('tests/fixtures/frontend_v030/ordinary-type-cutover/current/sized_clients',
              'corpus/sized/qualtran_qpe') for p in (ROOT/directory).glob('*.qli')}
    result['fourier'] = (ROOT/'corpus/sized/qualtran_qft/fourier.qli').read_text()
    return result


def build(modules, kind, n, m, j=1, d=3):
    if kind == 'order':
        return compile_source(modules['order'], 'order_phase', dict(n=n,m=m), modules=modules,
                              operations={'U': Operation('modular::mul_two', (n,))})
    return compile_source(modules['amplitude'], 'amplitude_phase', dict(n=n,m=m,j=j,d=d), modules=modules)


def expected(kind, n, m, column, j=1, d=3):
    """Direct complete-input coefficients, reading no graph/meaning/trace.

    Order uses modular powers with the explicitly fixed unused label. Amplitude
    uses G^s A = exp(i alpha) exp(-i (2s+1) alpha X) on the low bit.
    """
    size, modulus = 1 << m, (1 << n)-1
    alpha = math.pi*j/(1 << d)
    result = defaultdict(complex)
    for label, coefficient in column.items():
        a, b = label % size, label >> m
        for s in range(size):
            if kind == 'order':
                powers = {modulus if b == modulus else pow(2,s,modulus)*b % modulus: 1}
            else:
                powers = {b: cmath.exp(1j*alpha)*math.cos((2*s+1)*alpha),
                          b ^ 1: -1j*cmath.exp(1j*alpha)*math.sin((2*s+1)*alpha)}
            sign = (-1)**((a&s).bit_count())
            for y in range(size):
                scalar = coefficient*sign*cmath.exp(-2j*math.pi*s*y/size)/size
                for target, weight in powers.items():
                    result[y | (target << m)] += scalar*weight
    return dict(result)


def phase_kernel(theta, m, y):
    size = 1 << m
    return abs(sum(cmath.exp(2j*math.pi*s*(theta-y/size)) for s in range(size))/size)**2


def probes(artifact, kind, n, m, j=1, d=3):
    evaluate, gates = circuit_action(artifact)
    dimension, size = 1 << (n+m), 1 << m
    maximum = 0
    for label in range(dimension):
        maximum = max(maximum, difference(evaluate({label:1}), expected(kind,n,m,{label:1},j,d)))
    columns = [{x: complex((x+shift)%5-2, (2*x+shift)%7-3) for x in range(dimension)}
               for shift in (1,3)]
    norm = math.sqrt(sum(abs(a)**2 for c in columns for a in c.values()))
    for column in columns:
        column = {x:a/norm for x,a in column.items()}
        maximum = max(maximum, difference(evaluate(column),expected(kind,n,m,column,j,d)))
    # Diagnostic branch vectors from the actual hierarchy, not a measurement API.
    prepared_input = {1 << m:1} if kind == 'order' else {0:1}
    actual = evaluate(prepared_input)
    wanted = expected(kind,n,m,prepared_input,j,d)
    branches = [{x >> m:z for x,z in actual.items() if x % size == y} for y in range(size)]
    branch_error = max(difference(branch,{x >> m:z for x,z in wanted.items() if x % size == y})
                       for y,branch in enumerate(branches))
    probabilities = [sum(abs(z)**2 for z in branch.values()) for branch in branches]
    analytic = ([sum(phase_kernel(k/n,m,y) for k in range(n))/n for y in range(size)]
                if kind == 'order' else
                [(phase_kernel(j/(1 << d),m,y)+phase_kernel(-j/(1 << d),m,y))/2
                 for y in range(size)])
    maximum = max(maximum,branch_error,max(abs(a-b) for a,b in zip(probabilities,analytic)))
    result = dict(basis_columns=dimension,reference_columns=2,maximum_error=maximum,
                  executed_instructions=gates,diagnostic_probabilities=probabilities,
                  diagnostic_branch_error=branch_error)
    if kind == 'amplitude':
        result['target_probability'] = math.sin(math.pi*j/(1 << d))**2
        result['diagnostic_grid_estimates'] = [math.sin(math.pi*y/size)**2 for y in range(size)]
    else:
        result['orbit'] = [pow(2,s,(1 << n)-1) for s in range(n)]
    return result


def source_rejections(base):
    cases = []
    order = base['order']
    for name, changed in [
        ('forward-missing-controlled', order.replace(', Controlled(U)','')),
        ('forward-apply-is-not-control', order.replace('Controlled(U)','Apply(U)')),
        ('forward-adjoint-is-not-control', order.replace('Controlled(U)','Adjoint(U)')),
        ('forward-natural-for-operation', order.replace('estimate[n,m,U]','estimate[n,m,1]')),
        ('forward-operation-for-natural', order.replace('estimate[n,m,U]','estimate[U,m,U]')),
        ('forward-static-arity', order.replace('estimate[n,m,U]','estimate[n,U]')),
        ('forward-target-type', order.replace('Op<Bits<n>>','Op<Bits<n+1>>')),
        ('forward-alias', order.replace('(phase,target)\n}', '(target,target)\n}')),
        ('forward-access-empty-fold', order.replace(', Controlled(U)','').replace(
            'estimate[n,m,U](phase,target)',
            'qfor static k in 0..0 carry pair = (phase,target) { let (p,t) = pair; yield estimate[n,m,U](p,t); }')),
        ('forward-access-unselected-branch', order.replace(', Controlled(U)','').replace(
            'estimate[n,m,U](phase,target)',
            'if static n == 2 { (phase,target) } else { estimate[n,m,U](phase,target) }')),
    ]:
        cases.append((name,base|{'order':changed},'order'))
    cases.append(('callee-extra-access',base|{'estimation':base['estimation'].replace(
        'Controlled(U)','Controlled(U), Adjoint(U)')},'order'))
    for name,changed in [
        ('transparent-static-arity',base['amplitude'].replace('grover[n,j,d]','grover[n]')),
        ('transparent-wrong-target',base['amplitude'].replace('grover[n,j,d]','grover[n+1,j,d]')),
        ('hidden-transparent-provider',base['amplitude'].replace('let target = prepare',
            'let grover = target; let target = prepare').replace('(target);','(grover);')),
    ]:
        cases.append((name,base|{'amplitude':changed},'amplitude'))
    cases.append(('transparent-false-premise',base|{'amplification':base['amplification'].replace(
        'requires n >= 1','requires n >= 3')},'amplitude'))
    result = []
    for name, modules, kind in cases:
        try:
            build(modules,kind,2,2)
        except SourceError as error:
            result.append(dict(case=name,diagnostic=str(error)))
        else:
            raise AssertionError('invalid source accepted: '+name)
    nested = Operation('evolution::evolve',(1,1,3),(('unused',Operation('modular::mul_two',(2,))),))
    deep = Operation('modular::mul_two',(2,))
    for _ in range(33):
        deep = Operation('modular::mul_two',(2,),(('U',deep),))
    for name, provider in [('unexpected-nested-provider',nested),('provider-depth',deep),
        ('duplicate-provider',Operation('modular::mul_two',(2,),(('U',nested),('U',nested))))]:
        try:
            compile_source(order,'order_phase',dict(n=2,m=2),modules=base,operations={'U':provider})
        except SourceError as error:
            result.append(dict(case=name,diagnostic=str(error)))
        else:
            raise AssertionError(name)
    return result


def cache_case(base):
    # Different nested providers at the same natural sizes must not share a
    # stale instantiation. Their phases add to pi on the all-one three-bit input.
    modules = base | {
      'box': 'use std::registers::take_bit; use std::registers::put_bit; pub unitary fn box[static n: Nat, static V: Op<Bits<n-1>>](q: Q<Bits<n>>) -> Q<Bits<n>> requires n >= 2, Controlled(V) { let (c,t)=take_bit[n,0](q); let (c,t)=controlled(V)(c,t); put_bit[n,0](c,t) }',
      'route': 'pub unitary fn route[static n: Nat, static U: Op<Bits<n>>](c: Q<Bit>,q: Q<Bits<n>>) -> (Q<Bit>,Q<Bits<n>>) requires Controlled(U) { controlled(U)(c,q) }',
      'client': 'use route::route; use box::box; use evolution::evolve; pub unitary fn twice[static n: Nat](c: Q<Bit>,q: Q<Bits<n>>) -> (Q<Bit>,Q<Bits<n>>) { let (c,q)=route[n,box[n,evolve[n-1,1,3]]](c,q); route[n,box[n,evolve[n-1,3,3]]](c,q) }'}
    artifact = compile_source(modules['client'],'twice',dict(n=2),modules=modules)
    evaluate,_ = circuit_action(artifact)
    oracle = lambda column: {x:(-a if x == 7 else a) for x,a in column.items()}
    inputs = [{x:1} for x in range(8)] + [{x:complex(x-3,2-x)/10 for x in range(8)}]
    error = max(difference(evaluate(c),oracle(c)) for c in inputs)
    assert error < 1e-10, error
    return artifact,dict(maximum_error=error,basis_columns=8,reference_columns=1)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record',type=Path)
    args=parser.parse_args()
    base=sources()
    artifacts,parameters={},{}
    for n,m in [(2,2),(2,3),(3,2),(3,3),(4,3)]:
        name=f'order-{n}-{m}'; parameters[name]=('order',n,m,1,3)
    for name,n,m,j,d in [('zero',1,3,0,3),('one',1,3,4,3),('half',1,3,2,3),
        ('small',1,2,1,3),('exact',1,3,1,3),('complement',1,3,3,3),
        ('off-grid',1,3,1,5),('spectator',2,2,1,3)]:
        parameters['amplitude-'+name]=('amplitude',n,m,j,d)
    for name,p in parameters.items():
        artifacts[name]=build(base,*p)
    # An additional transparent forwarding level still calls the same QPE body.
    bridge=base['order'].replace('order_phase','forward_phase')
    indirect=base|{'bridge':bridge,'order':base['order'].replace('use estimation::estimate;',
        'use bridge::forward_phase;').replace('estimate[n,m,U]','forward_phase[n,m,U]')}
    artifacts['indirect-forward']=build(indirect,'order',2,2)
    parameters['indirect-forward']=('order',2,2,1,3)
    reordered=base|{'estimation':base['estimation'].replace(
        'static n: Nat, static m: Nat, static U: Op<Bits<n>>',
        'static U: Op<Bits<n>>, static n: Nat, static m: Nat'),
        'order':base['order'].replace('estimate[n,m,U]','estimate[U,n,m]')}
    artifacts['declaration-order']=build(reordered,'order',2,2)
    parameters['declaration-order']=('order',2,2,1,3)
    negative_sign=base['amplification'].replace('use rotation::prepare;',
        'use rotation::prepare; use std::registers::take_bit; use std::registers::put_bit; use std::quantum::phase; use std::quantum::x;').replace(
        'prepare[n,j,d](q)\n}', 'let q=prepare[n,j,d](q); let (bit,rest)=take_bit[n,0](q); put_bit[n,0](x(phase[1,1](x(phase[1,1](bit)))),rest)\n}')
    faults={
      'wrong-modular-direction': (base|{'modular':base['modular'].replace('take_bit[n,n-1]','take_bit[n,0]').replace('put_bit[n,0]','put_bit[n,n-1]')},('order',3,2,1,3)),
      'missing-preparation': (base|{'amplitude':base['amplitude'].replace('prepare[n,j,d](target)','target')},('amplitude',1,3,1,3)),
      'wrong-reflection-sign': (base|{'amplification':negative_sign},('amplitude',1,3,1,3)),
      'wrong-conjugation': (base|{'amplification':base['amplification'].replace('adjoint(prepare[n,j,d],q)','prepare[n,j,d](q)')},('amplitude',1,3,1,3)),
      'shared-qpe-fault-order': (base|{'estimation':base['estimation'].replace('2^k,U','0,U')},('order',3,2,1,3)),
      'shared-qpe-fault-amplitude': (base|{'estimation':base['estimation'].replace('2^k,U','0,U')},('amplitude',1,3,1,3)),
    }
    for name,(modules,p) in faults.items():
        artifacts[name]=build(modules,*p)
    artifacts['nested-provider-cache'],cache=cache_case(base)
    malformed=copy.deepcopy(artifacts['amplitude-exact'])
    for definition in malformed['definitions']:
        if definition['body']['tag']=='leaf':
            packet=json.loads(definition['body']['program'])
            packet['programs'][packet['root']]['operations'][0]['gate']='x'
            definition['body']['program']=text(packet)
            break
    artifacts['false-forwarded-leaf']=malformed
    report=dict(format='qleisli.sized-qpe-clients',version=1,status='pending',
        scope='Small coherent local integration clients; no maximum-size validation, measured Bits API, certified decoder or production integration claim.',
        source_sha256={k:hashlib.sha256(v.encode()).hexdigest() for k,v in base.items()},
        producer_sha256=hashlib.sha256((ROOT/'scripts/compile_sized_corpus.py').read_bytes()).hexdigest(),
        source_rejections=source_rejections(base))
    kernel=ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel'
    report['kernel_sha256']=hashlib.sha256(kernel.read_bytes()).hexdigest()
    with tempfile.TemporaryDirectory(prefix='qleisli-qpe-clients-') as directory:
        directory=Path(directory)
        for name,a in artifacts.items():
            (directory/(name+'.json')).write_text(text(a))
        (directory/'cases.txt').write_text(''.join(name+'|'+('contract' if name=='false-forwarded-leaf' else 'ok')+'\n' for name in artifacts))
        command=['cargo','test','--test','sized_corpus','inspect_source_produced_corpus','--','--ignored','--nocapture']
        run=subprocess.run(command,cwd=ROOT,text=True,capture_output=True,env=os.environ|{
            'QLEISLI_SIZED_CORPUS':str(directory),'QLEISLI_HIERARCHY_KERNEL':str(kernel)})
        report.update(command=command,exit_code=run.returncode,stdout=run.stdout,stderr=run.stderr,
                      native=[line.split('|')[1:] for line in run.stdout.splitlines() if line.startswith('CORPUS|')])
    if run.returncode:
        if args.record: args.record.write_text(json.dumps(report,indent=2)+'\n')
        print(run.stdout+run.stderr)
        return 1
    semantic={name:probes(artifacts[name],*p) for name,p in parameters.items()}
    bad={name:probes(artifacts[name],*p) for name,(_,p) in faults.items()}
    assert all(row['maximum_error'] < 1e-10 for row in semantic.values()),semantic
    assert all(row['maximum_error'] > 0.1 for row in bad.values()),bad
    for name in ('amplitude-zero','amplitude-one','amplitude-half','amplitude-exact','amplitude-complement'):
        row=semantic[name]
        assert sum(p*abs(v-row['target_probability']) for p,v in zip(
            row['diagnostic_probabilities'],row['diagnostic_grid_estimates'])) < 1e-10
    probabilities=semantic['order-4-3']['diagnostic_probabilities']
    assert max(abs(p-(0.25 if y%2==0 else 0)) for y,p in enumerate(probabilities)) < 1e-10
    report.update(status='passed-small-coherent-clients',semantics=semantic,semantic_faults=bad,
        provider_cache=cache,totals=dict(basis_columns=sum(r['basis_columns'] for r in semantic.values())+8,
                                       reference_columns=2*len(semantic)+1),
        artifacts={name:dict(definitions=len(a['definitions']),bytes=len(text(a).encode()),
                            sha256=hashlib.sha256(text(a).encode()).hexdigest()) for name,a in artifacts.items()})
    if args.record: args.record.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('status','totals','provider_cache')}))
    print(f"Native outcomes: {len(report['native'])}; source rejections: {len(report['source_rejections'])}; semantic faults: {len(bad)}")
    return 0


if __name__=='__main__':
    raise SystemExit(main())
