#!/usr/bin/env python3
"""Native derivation closure, independent recursive rules and exact monomial oracle.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
This does not claim full quantum soundness or external artifact acceptance.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import random
from test_hierarchical_power import PRELUDE
from test_hierarchical_artifact import ROOT, build_and_run

PRELUDE = PRELUDE.replace('import QleisliKernel.Hierarchical.Power',
                         'import QleisliKernel.Hierarchical.Derivation') + r'''
def reportDerivation (name : String) (a : Artifact) (order : Array Nat) : IO Unit :=
  match Derivation.checkAll a order with
  | .error e => IO.println s!"{name}|{code e}"
  | .ok checked => IO.println s!"{name}|derived|{checked.state.visits}|{checked.state.proofs}"
def reportPowerDerivation (name : String) (a : Artifact) (order : Array Nat) (k provider : Nat) : IO Unit :=
  match Derivation.powerEntry a order k provider with
  | .error e => IO.println s!"{name}|{code e}"
  | .ok checked => IO.println s!"{name}|derived|{checked.visits}|{checked.derivation.state.proofs}"
def reportLocalRule (name : String) (a : Artifact) (index budget : Nat) : IO Unit :=
  match Rule.check a index budget with
  | .error e => IO.println s!"{name}|{code ⟨e,none⟩}"
  | .ok checked => IO.println s!"{name}|matched|{checked.visits}"
def structuralEquation : Artifact :=
  let a := bside 0 7
  let b : Side := ⟨#[⟨1,#[.bits 1],#[7]⟩],#[]⟩
  {definitions := #[⟨⟨a,b⟩,.unitary,.structural .bitToBits⟩]
   meanings := #[⟨⟨a,b⟩,.structural .bitToBits⟩]
   encodings := #[identityE a,identityE b]
   proofs := #[{proof with rule := .structural,outputEncoding := 1}]
   entry := ⟨0,0⟩}
def phasePower (j angle exponent : Nat) : Artifact :=
  let a := powerArtifact (bside 0 0) (2^exponent)
  let a := alterDefinition a 0 (fun d => {d with body := .dyadicPhase 0 j angle})
  let a := alterMeaning a 0 (fun m => {m with body := .phase j angle})
  let a := alterPremise a (fun p => {p with rule := .phase})
  alterRoot a (fun p => {p with witness := ⟨1,#[exponent,0],#[]⟩})
'''


def refs(body):
    tag, *args = body
    if tag in ('phase', 'rewire', 'identity'):
        return []
    if tag in ('inverse', 'repeat', 'control'):
        return [args[0]]
    return list(args)


def oracle(nodes, root):
    """Recursive proof validation from actual nodes, independent of proposed order/cache."""
    active, done = set(), set()
    def visit(i):
        if not 0 <= i < len(nodes) or i in active:
            return False
        if i in done:
            return True
        n = nodes[i]
        active.add(i)
        d, m, ps = n['d'], n['m'], n['p']
        valid = all(visit(p) for p in ps)
        valid &= d[0] == m[0] and n['rule'] == d[0]
        valid &= refs(d) == ps and refs(m) == ps
        if d[0] in ('phase', 'rewire'):
            valid &= d == m
        if d[0] in ('control', 'repeat'):
            valid &= d[2] == m[2]
        active.remove(i)
        if valid:
            done.add(i)
        return valid
    return visit(root) and len(done) == len(nodes)


def monomial(nodes, index, field, cache=None):
    """Exact basis permutation and 256th-root exponents; no quantum float tolerances."""
    cache = {} if cache is None else cache
    if index in cache:
        return cache[index]
    node = nodes[index]
    tag, *args = node[field]
    size = 1 << len(node['side'])
    identity = [(i, 0) for i in range(size)]
    def compose(first, second):
        return [(second[y][0], (phase+second[y][1]) % 256) for y, phase in first]
    if tag == 'phase':
        j, k = args
        answer = [(0, 0), (1, j*(256//(2**k)) % 256)]
    elif tag == 'identity':
        answer = identity
    elif tag == 'rewire':
        answer = [(sum(((x >> src) & 1) << dst for dst, src in enumerate(args[0])), 0) for x in range(size)]
    elif tag == 'sequence':
        answer = identity
        for child in args:
            answer = compose(answer, monomial(nodes, child, field, cache))
    elif tag == 'repeat':
        child, count = args
        power = monomial(nodes, child, field, cache)
        answer = identity
        while count:
            if count & 1:
                answer = compose(answer, power)
            power = compose(power, power)
            count //= 2
    elif tag == 'inverse':
        answer = [None]*size
        for x, (y, phase) in enumerate(monomial(nodes, args[0], field, cache)):
            answer[y] = (x, -phase % 256)
    elif tag == 'control':
        child, polarity = args
        target = monomial(nodes, child, field, cache)
        answer = [((target[x >> 1][0] << 1) | (x & 1), target[x >> 1][1])
                  if (x & 1) == polarity else (x, 0) for x in range(size)]
    elif tag == 'tensor':
        low, high = args
        a, b = monomial(nodes, low, field, cache), monomial(nodes, high, field, cache)
        width = len(nodes[low]['side'])
        answer = [(a[x % len(a)][0] | (b[x >> width][0] << width),
                   (a[x % len(a)][1]+b[x >> width][1]) % 256) for x in range(size)]
    else:
        raise AssertionError(tag)
    cache[index] = answer
    return answer


def node(nodes, side, body):
    nodes.append(dict(side=side, d=body, m=body, rule=body[0], p=refs(body)))
    return len(nodes)-1


def array(items):
    return '#[' + ','.join(map(str, items)) + ']'


def side_text(owners):
    return '⟨' + array(f'⟨{i},#[.bit],#[{100+i}]⟩' for i in owners) + ',#[]⟩'


def body_text(body, logical=False):
    tag, *args = body
    if tag == 'phase':
        return f'.phase {args[0]} {args[1]}'  # Physical target is added by render().
    if tag == 'rewire':
        return f'.rewire ⟨{array(args[0])},{array(args[0])},#[]⟩'
    if tag == 'repeat':
        return f'.power {args[0]} {args[1]}' if logical else f'.repeatOp {args[1]} {args[0]}'
    if tag == 'sequence':
        return f'.sequence {array(args)}'
    if tag == 'control':
        return f'.control {args[0]} {str(bool(args[1])).lower()}'
    return '.' + tag + (' ' + ' '.join(map(str, args)) if args else '')


def render(nodes):
    definitions, meanings, encodings, proofs = [], [], [], []
    for i, n in enumerate(nodes):
        s = side_text(n['side'])
        d = body_text(n['d'])
        if n['d'][0] == 'phase':
            d = f'.dyadicPhase {n["side"][0]} {n["d"][1]} {n["d"][2]}'
        definitions.append(f'⟨⟨{s},{s}⟩,.unitary,{d}⟩')
        meanings.append(f'⟨⟨{s},{s}⟩,{body_text(n["m"],True)}⟩')
        encodings.append(f'⟨{s},{s},.identity⟩')
        rule = 'repeatOp' if n['rule'] == 'repeat' else n['rule']
        proofs.append(f'⟨.equation,.{rule},{array(n["p"])},{i},{i},{i},{i},⟨1,#[],#[]⟩⟩')
    return '⟨' + ','.join(array(xs) for xs in (definitions, meanings, encodings, proofs)) + f',⟨{len(nodes)-1},{len(nodes)-1}⟩⟩'


def cases():
    rows, models = [], {}
    def add(name, artifact, expected, whole=True, k=0, provider=0, order='Array.range 10'):
        call = (f'reportPowerDerivation "{name}" ({artifact}) ({order}) {k} {provider}' if whole
                else f'reportDerivation "{name}" ({artifact}) ({order})')
        rows.append((name, call, expected))
    for n in range(1,9):
        for k in range(13):
            add(f'power-{n}-{k}',f'powerSample {n} {k}','derived',k=k)
    for k in [0,3,12]:
        add(f'permuted-{k}',f'permutedPower {k}','derived',k=k,provider=2,order='#[2,0,1,4,5,3,6,7,8,9]')
    for angle in [3,4,8]:
        for exponent in range(13):
            add(f'phase-power-{angle}-{exponent}',f'phasePower 1 {angle} {exponent}','derived',k=exponent)
    add('phase-power-false-provider', 'alterMeaning (phasePower 1 8 12) 0 (fun m => {m with body := .phase 2 8})','contract',k=12)
    add('opaque-provider', 'alterDefinition (powerSample 1 0) 0 (fun d => {d with body := .leaf (bytes 1)})','contract')
    add('false-provider', 'alterMeaning (powerArtifact (bside 0 0) 1) 0 (fun m => {m with body := .phase 1 3})','contract')
    add('forged-finite-rule', 'alterPremise (powerSample 1 0) (fun p => {p with rule := .finite})','contract')
    add('wrong-request', 'powerSample 1 0','contract',k=1)
    add('wrong-provider-request', 'powerSample 1 0','contract',provider=1)
    add('zero-invalid-body', 'wrongZeroBody','invalid_ir')
    add('cycle', 'alterPremise (powerSample 1 0) (fun p => {p with premises := #[1]})','invalid_ir')
    add('duplicate-order', 'powerSample 1 0','invalid_ir',order='#[0,1,2,3,4,5,6,7,8,8]')
    add('zero-owner','powerArtifact zeroTarget 1','derived')
    add('empty-owner','powerSample 0 0','derived')
    add('nested-owner','powerArtifact (tupleSide nested) 1','derived')
    add('flat-owner','powerArtifact (tupleSide flat) 1','derived')
    add('explicit-conversion','structuralEquation','derived',whole=False,order='Array.range 5')
    add('wrong-conversion-rule','alterPremise structuralEquation (fun p => {p with rule := .rewire})','contract',whole=False,order='Array.range 5')
    for label, budget, expected in [('exact-local-budget',5398,'matched'),('under-local-budget',5397,'limit'),
                                     ('zero-local-budget',0,'limit'),('outside-local-budget',2000001,'limit')]:
        rows.append((label,f'reportLocalRule "{label}" (base 1) 0 {budget}',expected))
    rows.append(('unbound-huge-child','reportLocalRule "unbound-huge-child" (alterDefinition (powerSample 1 0) 0 (fun d => {d with interface := ⟨hugeAxes,hugeAxes⟩})) 1 2000000','limit'))
    # Random DAGs remain small for the independent monomial model, while large
    # repeat counts would make literal expansion infeasible.
    for seed in range(32):
        rng = random.Random(seed)
        nodes = []
        root = node(nodes,[0],('phase',rng.randrange(1,8),3))
        for _ in range(6):
            tag = rng.choice(['sequence','repeat','inverse'])
            body = (tag,root,0) if tag=='sequence' else ((tag,root,rng.choice([0,1,3,4096])) if tag=='repeat' else (tag,root))
            root = node(nodes,[0],body)
        if seed % 2:
            second = node(nodes,[2],('phase',rng.randrange(1,256),8))
            root = node(nodes,[0,2],('tensor',root,second))
        else:
            root = node(nodes,[1,0],('control',root,seed % 4 == 0))
        swap = node(nodes,nodes[root]['side'],('rewire',[1,0]))
        root = node(nodes,nodes[root]['side'],('sequence',root,swap))
        for suffix, model in [('valid',nodes),('false-leaf',copy.deepcopy(nodes))]:
            if suffix == 'false-leaf':
                model[0]['m'] = ('phase',(model[0]['m'][1]+1)%8,3)
            name = f'dag-{seed}-{suffix}'
            valid = oracle(model,root)
            models[name] = model
            add(name,render(model),'derived' if valid else 'contract',whole=False,order=f'Array.range {4*len(model)}')
    # Independent noncommuting phase/swap example exposes wrong execution order.
    nodes=[]
    a=node(nodes,[0],('phase',1,3)); b=node(nodes,[2],('phase',1,8))
    t=node(nodes,[0,2],('tensor',a,b)); s=node(nodes,[0,2],('rewire',[1,0]))
    node(nodes,[0,2],('sequence',t,s))
    for name, change in [('ordered',None),('meaning-order','meaning'),('premise-order','premise'),('missing-premise','missing')]:
        model=copy.deepcopy(nodes)
        if change=='meaning': model[-1]['m']=('sequence',s,t)
        if change=='premise': model[-1]['p']=[s,t]
        if change=='missing': model[-1]['p']=[t]
        models[name]=model
        # Removing the premise also makes its proof unreachable, so preparation
        # rejects before rule matching. Retain that more precise diagnostic.
        expected='derived' if oracle(model,len(model)-1) else ('invalid_ir' if change=='missing' else 'contract')
        add(name,render(model),expected,whole=False,order='Array.range 20')
    # Even a zero repeat checks the actual false leaf premise.
    nodes=[]; a=node(nodes,[0],('phase',1,8)); node(nodes,[0],('repeat',a,0)); nodes[0]['m']=('phase',2,8)
    models['zero-false-leaf']=nodes
    add('zero-false-leaf',render(nodes),'contract',whole=False,order='Array.range 8')
    return rows, models


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record',type=Path)
    args=parser.parse_args()
    rows,models=cases()
    source=PRELUDE+'\n'+'\n'.join(f'def case{i} : IO Unit := {call}' for i,(_,call,_) in enumerate(rows))+'\n'
    groups=list(range(0,len(rows),16))
    for first in groups:
        source+=f'def group{first} : IO Unit := do\n'+'\n'.join(f'  case{i}' for i in range(first,min(first+16,len(rows))))+'\n'
    source+='def main : IO Unit := do\n'+'\n'.join(f'  group{i}' for i in groups)+'\n'
    commands,binary=build_and_run(source,args.record)
    results={}
    for line in commands[-1]['stdout'].splitlines():
        name,*fields=line.split('|'); assert name not in results; results[name]=fields
    if args.record:
        args.record.write_text(json.dumps(dict(status='observed-not-yet-compared',results=results,commands=commands),indent=2)+'\n')
    assert len(results)==len(rows)
    semantic_counterexamples=coefficients=0
    for name,_,expected in rows:
        assert results[name][0]==expected,(name,results[name],expected)
        if name not in models: continue
        model=models[name]
        assert (expected=='derived')==oracle(model,len(model)-1)
        actual=monomial(model,len(model)-1,'d'); logical=monomial(model,len(model)-1,'m')
        if expected=='derived':
            assert actual==logical,(name,actual,logical)
            assert sorted(x for x,_ in actual)==list(range(len(actual)))
            assert int(results[name][2])==len(model)  # Shared premises are checked once.
            coefficients+=len(actual)
        elif actual!=logical:
            semantic_counterexamples+=1
    assert semantic_counterexamples>0
    for n in range(1,9):
        assert len({results[f'power-{n}-{k}'][1] for k in range(13)})==1
    report=dict(format='qleisli.hierarchical-derivation-validation',version=1,status='passed',cases=len(rows),
                derived=sum(status=='derived' for _,_,status in rows),recursive_oracle_cases=len(models),
                local_matches=sum(status=='matched' for _,_,status in rows),
                rejected=sum(status not in ('derived','matched') for _,_,status in rows),
                exact_coefficients=coefficients,semantic_counterexamples=semantic_counterexamples,
                maximum_oracle_dimension=4,maximum_checker_dense_dimension=0,repeated_bodies_expanded=0,
                external_semantic_evidence=False,binary_sha256=binary,harness_sha256=hashlib.sha256(source.encode()).hexdigest(),
                results=results,commands=commands,source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in [*sorted((ROOT/'lean-kernel/QleisliKernel/Hierarchical').glob('*.lean')),
                              *(ROOT/'scripts'/f'test_hierarchical_{name}.py' for name in ['artifact','typing','contract_typing','power']),Path(__file__).resolve()]})
    if args.record: args.record.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in {'results','commands'}}))


if __name__=='__main__':main()
