#!/usr/bin/env python3
"""Small-system shared AddK/Equals sources and phase-fixed arithmetic oracles.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
No maximum-size checks. Native inspection is separate from algorithm tests.
"""
import argparse
import copy
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import tempfile

from current_source_fixtures import current_source_file
from compile_sized_corpus import SourceError, compile_source, text
from test_sized_corpus import circuit_action, difference

ROOT = Path(__file__).resolve().parent.parent
DIRECTORY = ROOT/'corpus/sized/qualtran_arithmetic'
WIDTHS = range(4)


def sources():
    result = {p.stem: current_source_file(p).read_text() for p in DIRECTORY.glob('*.qli')}
    result['bitwise'] = current_source_file(ROOT/'corpus/sized/qualtran_xor/bitwise.qli').read_text()
    return result


def compile_case(modules, module, entry, **sizes):
    return compile_source(modules[module], entry, sizes, modules=modules)


def permutation(kind, n, amount=0):
    dimension = 1 << n
    if kind == 'add':
        return n, lambda x: (x+amount) % dimension
    if kind == 'invert':
        return n, lambda x: x ^ (dimension-1)
    if kind == 'controls':
        return n+1, lambda x: x ^ (dimension if x % dimension == dimension-1 else 0)
    if kind == 'controlled-add':
        return n+1, lambda x: (x & 1) | ((((x >> 1)+amount*(x & 1)) % dimension) << 1)
    if kind == 'identity':
        return n, lambda x: x
    assert kind == 'equals'
    return 2*n+1, lambda x: x ^ ((1 << (2*n)) if x % dimension == (x >> n) % dimension else 0)


def probes(artifact, kind, n, amount=0):
    width, mapping = permutation(kind, n, amount)
    evaluate, gates = circuit_action(artifact)
    maximum = 0
    for x in range(1 << width):
        maximum = max(maximum, difference(evaluate({x: 1}), {mapping(x): 1}))
    # Two distinct reference columns of a normalized entangled vector. At zero
    # data width the columns naturally have one coefficient each.
    columns = [{x: complex((x+shift)%5-2, (2*x+shift)%7-3) for x in range(1 << width)}
               for shift in (1, 3)]
    norm = math.sqrt(sum(abs(a)**2 for c in columns for a in c.values()))
    for column in columns:
        column = {x: a/norm for x, a in column.items()}
        maximum = max(maximum, difference(evaluate(column), {mapping(x): a for x,a in column.items()}))
    return dict(basis_columns=1 << width, reference_columns=2,
                maximum_error=maximum, executed_instructions=gates)


def rejected_sources(modules):
    examples = []
    base = modules['comparison']
    for name, changed in [
        ('alias-empty-owners', base.replace('xor_into[n](left,y)', 'xor_into[n](left,left)')),
        ('ordinary-argument-count', base.replace('xor_into[n](left,y)', 'xor_into[n](left)')),
        ('ordinary-argument-grouping', base.replace('xor_into[n](left,y)', 'xor_into[n]((left,y))')),
        ('ordinary-static-count', base.replace('xor_into[n]', 'xor_into[n,n]')),
        ('missing-returned-target', base.replace('(left,y,target)\n}', '(left,y)\n}')),
        ('different-result-nesting', base.replace('-> (Q<Bits<n>>, Q<Bits<n>>, Q<Bit>)', '-> (Q<Bits<n>>, (Q<Bits<n>>, Q<Bit>))')),
        ('control-target-type', base.replace('all_ones[n](y,target)', 'all_ones[n](target,y)')),
    ]:
        examples.append((name, modules | {'comparison': changed}, 'comparison', 'equals', dict(n=0)))
    base = modules['controls']
    for name, changed, width in [
        ('aliased-controlled-group', base.replace('(head,(rest,target));', '(head,(rest,head));'), 1),
        ('controlled-group-nesting', base.replace('(head,(rest,target));', '(head,((rest,target),target));'), 1),
        ('wrong-control-kind', base.replace('(head,(rest,target));', '(rest,(head,target));'), 1),
        ('unknown-static-target', base.replace('all_ones[n-1]', 'missing[n-1]'), 1),
        ('same-size-recursion', base.replace('(controls,x(target))', 'all_ones[n](controls,target)'), 0),
        ('invalid-empty-branch', base.replace('(controls,x(target))', '(controls,x(controls))'), 1),
        ('controlled-static-arity', base.replace('all_ones[n-1]', 'all_ones[n-1,n]'), 0),
    ]:
        examples.append((name, modules | {'controls': changed}, 'controls', 'all_ones', dict(n=width)))
    examples.append(('empty-loop-call-arity', modules | {'addition': modules['addition'].replace('increment[n](register)', 'increment[n](register,register)')}, 'addition', 'add_k', dict(n=0, K=0)))
    examples.append(('aggregate-fold-limit', modules, 'addition', 'add_k', dict(n=1, K=1025)))
    bad = 'use increment::increment; pub unitary fn bad[const n: Nat](increment: Q<Bits<n>>) -> Q<Bits<n>> { increment[n](increment) }'
    examples.append(('live-name-hides-function', modules | {'client': bad}, 'client', 'bad', dict(n=1)))
    bad = 'use increment::increment; pub unitary fn bad[const n: Nat](q: Q<Bits<n>>) -> Q<Bits<n>> { let increment = q; let q = increment; increment[n](q) }'
    examples.append(('spent-name-hides-function', modules | {'client': bad}, 'client', 'bad', dict(n=1)))
    bad = 'use growing::grow; pub unitary fn grow[const n: Nat](q: Q<Bit>) -> Q<Bit> { grow[n+1](q) }'
    examples.append(('instantiation-depth', modules | {'growing': bad}, 'growing', 'grow', dict(n=0)))
    bad = 'use controls::all_ones; pub unitary fn bad[const n: Nat](c: Q<Bit>, q: Q<Bits<n>>, t: Q<Bit>) -> (Q<Bit>,(Q<Bits<n>>,Q<Bit>)) { controlled(power(all_ones[n],0))(c,(q,t)) }'
    faulty = modules | {'client': bad, 'controls': base.replace('(controls,x(target))', '(x(controls),target)')}
    examples.append(('invalid-zero-repeat-body', faulty, 'client', 'bad', dict(n=0)))
    results = []
    for name, changed, module, entry, sizes in examples:
        try:
            compile_case(changed, module, entry, **sizes)
        except SourceError as error:
            results.append(dict(case=name, diagnostic=str(error)))
        else:
            raise AssertionError('invalid source accepted: '+name)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    modules = sources()
    artifacts, params = {}, {}
    for n in WIDTHS:
        for module, entry, kind, amount in [('controls','all_ones','controls',0),
                ('increment','increment','add',1), ('negation','invert_bits','invert',0),
                ('comparison','equals','equals',0)]:
            name = f'{module}-{n}'
            artifacts[name] = compile_case(modules, module, entry, n=n)
            params[name] = kind, n, amount
        for amount in sorted({0, 1, 3, (1 << n)-1, 1 << n, (1 << n)+1}):
            name = f'add-{n}-{amount}'
            artifacts[name] = compile_case(modules, 'addition', 'add_k', n=n, K=amount)
            params[name] = 'add', n, amount
    inverse_add = 'use addition::add_k; pub unitary fn undo[const n: Nat, const K: Nat](q: Q<Bits<n>>) -> Q<Bits<n>> { inverse(add_k[n,K])(q) }'
    inverse_eq = 'use comparison::equals; pub unitary fn undo[const n: Nat](a: Q<Bits<n>>, b: Q<Bits<n>>, t: Q<Bit>) -> (Q<Bits<n>>,Q<Bits<n>>,Q<Bit>) { inverse(equals[n])((a,b,t)) }'
    control_add = 'use addition::add_k; pub unitary fn use_add[const n: Nat, const K: Nat](c: Q<Bit>, q: Q<Bits<n>>) -> (Q<Bit>,Q<Bits<n>>) { controlled(add_k[n,K])(c,q) }'
    for n in WIDTHS:
        artifacts[f'inverse-add-{n}'] = compile_case(modules | {'client': inverse_add}, 'client', 'undo', n=n, K=3)
        params[f'inverse-add-{n}'] = 'add', n, -3
        artifacts[f'inverse-equals-{n}'] = compile_case(modules | {'client': inverse_eq}, 'client', 'undo', n=n)
        params[f'inverse-equals-{n}'] = 'equals', n, 0
        artifacts[f'controlled-add-{n}'] = compile_case(modules | {'client': control_add}, 'client', 'use_add', n=n, K=3)
        params[f'controlled-add-{n}'] = 'controlled-add', n, 3
    double_eq = 'use comparison::equals; pub unitary fn twice[const n: Nat](a: Q<Bits<n>>, b: Q<Bits<n>>, t: Q<Bit>) -> (Q<Bits<n>>,Q<Bits<n>>,Q<Bit>) { let (a,b,t) = equals[n](a,b,t); equals[n](a,b,t) }'
    artifacts['shared-equals-twice'] = compile_case(modules | {'client': double_eq}, 'client', 'twice', n=2)
    params['shared-equals-twice'] = 'identity', 5, 0
    original = modules['increment']
    reordered = original.replace('let (low,high) = all_ones[n-1](low,high);\n        let low = increment[n-1](low);', 'let low = increment[n-1](low);\n        let (low,high) = all_ones[n-1](low,high);')
    faults = {
        'wrong-carry-order': (modules | {'increment': reordered}, 'addition', 'add_k', dict(n=2,K=3), ('add',2,3)),
        'missing-carry': (modules | {'increment': original.replace('all_ones[n-1](low,high)', '(low,high)')}, 'addition', 'add_k', dict(n=2,K=3), ('add',2,3)),
        'reversed-bit-order': (modules | {'increment': original.replace('[n,n-1]', '[n,0]')}, 'addition', 'add_k', dict(n=2,K=3), ('add',2,3)),
        'wrong-count': (modules | {'addition': modules['addition'].replace('0..K carry', '0..K-1 carry')}, 'addition', 'add_k', dict(n=2,K=3), ('add',2,3)),
        'missing-restore': (modules | {'comparison': modules['comparison'].rsplit('let (left,y) = xor_into[n](left,y);',1)[0]+'(left,y,target)\n}\n'}, 'comparison', 'equals', dict(n=2), ('equals',2,0)),
        'wrong-predicate': (modules | {'comparison': modules['comparison'].replace('let y = invert_bits[n](y);', 'let y = y;',1)}, 'comparison', 'equals', dict(n=2), ('equals',2,0)),
        'extra-target-phase': (modules | {'comparison': modules['comparison'].replace('use bitwise::xor_into;', 'use bitwise::xor_into;\nuse std::quantum::phase;').replace('(left,y,target)\n}', '(left,y,phase[1,1](target))\n}')}, 'comparison', 'equals', dict(n=2), ('equals',2,0)),
    }
    for name,(changed,module,entry,sizes,_) in faults.items():
        artifacts[name] = compile_case(changed, module, entry, **sizes)
    malformed = copy.deepcopy(artifacts['controls-2'])
    for definition in malformed['definitions']:
        if definition['body']['tag'] == 'leaf':
            packet = json.loads(definition['body']['program'])
            packet['programs'][packet['root']]['operations'][0]['gate'] = 'h'
            definition['body']['program'] = text(packet)
            break
    artifacts['false-finite-x'] = malformed
    report = dict(format='qleisli.sized-arithmetic-experiment', version=1, status='pending',
        scope='Small-system source path; no maximum-size checks, named arithmetic contract proof or production integration claim.',
        source_sha256={k:hashlib.sha256(v.encode()).hexdigest() for k,v in modules.items()},
        producer_sha256=hashlib.sha256((ROOT/'scripts/compile_sized_corpus.py').read_bytes()).hexdigest(),
        source_rejections=rejected_sources(modules))
    kernel = ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel'
    report['kernel_sha256'] = hashlib.sha256(kernel.read_bytes()).hexdigest()
    with tempfile.TemporaryDirectory(prefix='qleisli-small-arithmetic-') as directory:
        directory = Path(directory)
        for name,artifact in artifacts.items():
            (directory/f'{name}.json').write_text(text(artifact))
        (directory/'cases.txt').write_text(''.join(name+'|'+('contract' if name == 'false-finite-x' else 'ok')+'\n' for name in artifacts))
        command = ['cargo','test','--test','sized_corpus','inspect_source_produced_corpus','--','--ignored','--nocapture']
        run = subprocess.run(command,cwd=ROOT,text=True,capture_output=True,env=os.environ | {
            'QLEISLI_SIZED_CORPUS':str(directory),'QLEISLI_HIERARCHY_KERNEL':str(kernel)})
        report.update(command=command,exit_code=run.returncode,stdout=run.stdout,stderr=run.stderr)
        report['native'] = [line.split('|')[1:] for line in run.stdout.splitlines() if line.startswith('CORPUS|')]
    if run.returncode:
        if args.record: args.record.write_text(json.dumps(report,indent=2)+'\n')
        print(run.stdout+run.stderr)
        return 1
    print('Fresh small-system native arithmetic checks passed.',flush=True)
    semantic = {name:probes(artifacts[name],*p) for name,p in params.items()}
    assert all(row['maximum_error'] < 1e-10 for row in semantic.values()), semantic
    bad = {name:probes(artifacts[name],*f[-1]) for name,f in faults.items()}
    assert all(row['maximum_error'] > 0.1 for row in bad.values()), bad
    # Function spelling cannot select an arithmetic circuit.
    renamed = modules | {'comparison': modules['comparison'].replace('fn equals[', 'fn renamed[')}
    assert compile_case(renamed,'comparison','renamed',n=2) == artifacts['comparison-2']
    report.update(status='passed-small-source-path',semantics=semantic,semantic_faults=bad,
        totals=dict(basis_columns=sum(r['basis_columns'] for r in semantic.values()),reference_columns=2*len(semantic)),
        artifacts={name:dict(definitions=len(a['definitions']),bytes=len(text(a).encode())) for name,a in artifacts.items()})
    if args.record: args.record.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('stdout','stderr','semantics','artifacts','source_rejections')}))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
