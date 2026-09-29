#!/usr/bin/env python3
"""Call expansion through existing rules, checked against an independent oracle.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
The fixture caller is typed separately; no external call receipt is issued.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import random

from test_hierarchical_artifact import ROOT, build_and_run

PRELUDE = r'''import QleisliKernel.Hierarchical.CallLowering
import QleisliKernel.Hierarchical.Derivation
open QleisliKernel.Hierarchical
open Artifact
def sample (first rest callerIn callerOut : Side) (input output logicalIn logicalOut : PortMap)
    (bit : Bool) (count logicalCount j logicalJ : Nat) : Artifact :=
  let callee := NodeTyping.append first rest
  let idMap : PortMap := ⟨Array.range rest.quantum.size,Array.range (wires rest).size,#[]⟩
  let firstBody := if bit then Body.dyadicPhase 0 j 8 else .rewire ⟨#[0],#[],#[]⟩
  let firstMeaning := if bit then MeaningBody.phase logicalJ 8 else .identity
  let firstRule := if bit then Rule.phase else .rewire
  let enc (s : Side) : Encoding := ⟨s,s,.identity⟩
  let p (rule : Rule) (ps : Array Nat) (d m i o : Nat) : Proof :=
    ⟨.equation,rule,ps,d,m,i,o,⟨1,#[],#[]⟩⟩
  {definitions := #[⟨⟨first,first⟩,.unitary,firstBody⟩,
                    ⟨⟨rest,rest⟩,.unitary,.rewire idMap⟩,
                    ⟨⟨callee,callee⟩,.unitary,.tensor 0 1⟩,
                    ⟨⟨callee,callee⟩,.unitary,.repeatOp count 2⟩,
                    ⟨⟨callerIn,callerOut⟩,.unitary,.call 3 input output⟩]
   meanings := #[⟨⟨first,first⟩,firstMeaning⟩,⟨⟨rest,rest⟩,.identity⟩,
                 ⟨⟨callee,callee⟩,.tensor 0 1⟩,⟨⟨callee,callee⟩,.power 2 logicalCount⟩,
                 ⟨⟨callerIn,callee⟩,.rewire logicalIn⟩,
                 ⟨⟨callee,callerOut⟩,.rewire logicalOut⟩,
                 ⟨⟨callerIn,callerOut⟩,.sequence #[4,3,5]⟩]
   encodings := #[enc first,enc rest,enc callee,enc callerIn,enc callerOut]
   proofs := #[p firstRule #[] 0 0 0 0,p .rewire #[] 1 1 1 1,
               p .tensor #[0,1] 2 2 2 2,p .repeatOp #[2] 3 3 2 2,
               p .rewire #[] 5 4 3 2,p .rewire #[] 6 5 2 4,
               p .sequence #[4,3,5] 4 6 3 4]
   entry := ⟨4,6⟩}
def failure (e : Error) : String := match e with
  | .limit => "limit" | .contract => "contract" | .invalidIr => "invalid_ir"
def report (name : String) (a : Artifact) (budget : Nat := 2000000) : IO Unit := do
  match NodeTyping.check a 4 budget with
  | .error e => IO.println s!"{name}|{failure e}|call-typing"
  | .ok typed =>
    let some expansion := CallLowering.plan a 4 | IO.println s!"{name}|no-plan"
    let lowered := CallLowering.install a 4 expansion
    let order := #[0,1,2,3,5,6,4] ++ (Array.range 19).map (·+7)
    match Derivation.checkAll lowered order with
    | .error e => IO.println s!"{name}|{failure e.kind}|derivation"
    | .ok checked =>
      let .rewire before := expansion.before.body | IO.println s!"{name}|bad-before"
      let .rewire after := expansion.after.body | IO.println s!"{name}|bad-after"
      let .sequence children := expansion.replacement.body | IO.println s!"{name}|bad-sequence"
      IO.println s!"{name}|derived|{typed.visits}|{checked.state.visits}|{lowered.definitions.size}|{checked.state.proofs}|{before.axes.toList}|{after.axes.toList}|{children.toList}"
'''


def array(values):
    return '#[' + ','.join(map(str, values)) + ']'


def side(ports):
    return '⟨' + array(f'⟨{p["owner"]},{p["basis"]},{array(p["axes"])}⟩' for p in ports) + ',#[]⟩'


def mapping(owners, axes):
    return f'⟨{array(owners)},{array(axes)},#[]⟩'


def make(width, seed, count, dense_ports=False):
    rng = random.Random(seed)
    callee = [dict(owner=i, basis='#[.bit]', axes=[7+i]) for i in range(width)]
    if not width:
        callee = [dict(owner=0, basis='#[.bits 0]', axes=[])]
    elif not dense_ports:
        callee = [callee[0],dict(owner=1,basis=f'#[.bits {width-1}]',axes=list(range(8,7+width)))]
    # This owner has no axis but must still be returned with its distinct type.
    callee.append(dict(owner=30, basis='#[.unit]', axes=[]))
    size = len(callee)
    ip, op = list(range(size)), list(range(size))
    rng.shuffle(ip)
    rng.shuffle(op)
    renamed = [dict(owner=100+p['owner'], basis=p['basis'], axes=[1000+x for x in p['axes']]) for p in callee]
    caller_in = [None]*size
    for i, target in enumerate(ip):
        caller_in[target] = renamed[i]
    caller_out = [renamed[i] for i in op]
    in_axes = [a for p in caller_in for a in p['axes']]
    source_axes = [a for p in callee for a in p['axes']]
    im = [in_axes.index(1000+a) for a in source_axes]
    om = [source_axes.index(a-1000) for p in caller_out for a in p['axes']]
    return dict(width=width, first=callee[:1], rest=callee[1:], caller_in=caller_in,
                caller_out=caller_out, ip=ip, op=op, im=im, om=om, lim=im[:], lom=om[:],
                lip=ip[:], lop=op[:], count=count, logical_count=count, j=13, logical_j=13)


def render(m):
    return 'sample ' + ' '.join('('+side(m[key])+')' for key in ['first','rest','caller_in','caller_out']) + ' ' + ' '.join([
        '('+mapping(m['ip'],m['im'])+')', '('+mapping(m['op'],m['om'])+')',
        '('+mapping(m['lip'],m['lim'])+')', '('+mapping(m['lop'],m['lom'])+')',
        str(bool(m['width'])).lower(),str(m['count']),str(m['logical_count']),str(m['j']),str(m['logical_j'])])


def monomial(width, im, om, j, count):
    answer=[]
    for x in range(1 << width):
        inner = sum(((x >> src) & 1) << dst for dst,src in enumerate(im))
        y = sum(((inner >> src) & 1) << dst for dst,src in enumerate(om))
        answer.append((y, (j*count*(inner & 1)) % 256))
    return answer


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record',type=Path)
    args=parser.parse_args()
    rows=[]
    for n in range(9):
        for seed in range(3):
            for count in [0,3,4096]:
                rows.append((f'call-{n}-{seed}-{count}',make(n,seed,count),'derived',2000000))
    base=make(3,11,3,dense_ports=True)
    # Retain the measured aggregate limit of a distinct, more fragmented header.
    rows.append(('nine-owner-capacity',make(8,0,0,dense_ports=True),'limit',2000000))
    for label,key,value,status in [
            ('phase','j',14,'contract'),('count','count',4,'contract'),
            ('zero-false-provider','count',0,'contract'),
            ('duplicate-owner','ip',[0,0,2,3],'invalid_ir'),
            ('missing-empty-owner','ip',[0,1,2],'invalid_ir'),
            ('duplicate-axis','im',[0,0,2],'invalid_ir'),
            ('missing-axis','im',[0,1],'invalid_ir'),
            ('count-limit','count',4097,'invalid_ir')]:
        m=copy.deepcopy(base);m[key]=value
        rows.append((label,m,status,2000000))
    zero=make(3,11,0);zero['j']=14
    rows.append(('zero-still-checks-provider',zero,'contract',2000000))
    changed_contract=copy.deepcopy(base)
    changed_contract['lip'][0],changed_contract['lip'][1]=changed_contract['lip'][1],changed_contract['lip'][0]
    changed_contract['lim'][0],changed_contract['lim'][1]=changed_contract['lim'][1],changed_contract['lim'][0]
    rows.append(('well-typed-logical-axis-change',changed_contract,'contract',2000000))
    bad=copy.deepcopy(base)
    # Both maps are locally valid permutations, but their identity renamings conflict.
    bad['op'][0],bad['op'][1]=bad['op'][1],bad['op'][0]
    rows.append(('cross-endpoint-renaming',bad,'invalid_ir',2000000))
    rows.extend([('no-budget',base,'limit',0),('invalid-budget',base,'limit',2000001)])
    calls=[f'report {json.dumps(name)} ({render(m)}) {budget}' for name,m,_,budget in rows]
    source=PRELUDE+'\n'+ '\n'.join(f'def case{i} : IO Unit := {c}' for i,c in enumerate(calls))
    source+='\ndef main : IO Unit := do\n'+'\n'.join(f'  case{i}' for i in range(len(calls)))+'\n'
    commands,binary=build_and_run(source,args.record)
    results={line.split('|')[0]:line.split('|')[1:] for line in commands[-1]['stdout'].splitlines()}
    if args.record:
        args.record.write_text(json.dumps(dict(status='validation-in-progress',results=results,commands=commands),indent=2)+'\n')
    assert len(results)==len(rows)
    coefficients=counterexamples=0
    for name,m,expected,_ in rows:
        actual=results[name]
        assert actual[0]==expected,(name,actual,expected)
        logical=monomial(m['width'],m['lim'],m['lom'],m['logical_j'],m['logical_count'])
        if expected=='derived':
            assert actual[3:5]==['7','7'],(name,actual)  # Two adapters; seven shared proofs once each.
            im,om,children=map(json.loads,actual[5:8])
            assert children==[5,3,6]
            evaluated=monomial(m['width'],im,om,m['j'],m['count'])
            assert evaluated==logical,(name,evaluated,logical)
            assert sorted(y for y,_ in evaluated)==list(range(1<<m['width']))
            coefficients+=len(evaluated)
        elif expected=='contract':
            evaluated=monomial(m['width'],m['im'],m['om'],m['j'],m['count'])
            counterexamples+=evaluated!=logical
    for n in range(9):
        for seed in range(3):
            assert len({results[f'call-{n}-{seed}-{k}'][1] for k in [0,3,4096]})==1
            assert len({results[f'call-{n}-{seed}-{k}'][2] for k in [0,3,4096]})==1
    report=dict(format='qleisli.hierarchical-call-validation',version=1,status='passed',cases=len(rows),
                accepted=sum(e=='derived' for _,_,e,_ in rows),exact_coefficients=coefficients,
                semantic_counterexamples=counterexamples,maximum_oracle_dimension=256,
                generated_adapter_nodes=2,repeated_bodies_expanded=0,external_semantic_evidence=False,
                binary_sha256=binary,harness_sha256=hashlib.sha256(source.encode()).hexdigest(),
                results=results,commands=commands,source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in [*sorted((ROOT/'lean-kernel/QleisliKernel/Hierarchical').glob('*.lean')),Path(__file__).resolve()]})
    if args.record:args.record.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in {'results','commands','source_sha256'}}))


if __name__=='__main__':main()
