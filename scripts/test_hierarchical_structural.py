#!/usr/bin/env python3
"""Explicit hierarchical ownership conversions and independent basis routing.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
This is an internal conversion test, not external artifact semantic acceptance.
"""
import argparse
import hashlib
import json
from pathlib import Path
from test_hierarchical_contract_typing import PRELUDE
from test_hierarchical_artifact import ROOT, build_and_run

PRELUDE += r'''
def register (n : Nat) : Side := ⟨#[⟨10,#[.bits n],(Array.range n).map (fun i => 100 + 3*i)⟩],#[]⟩
def splitRegister (n k : Nat) : Interface :=
  let axes := (Array.range n).map (fun i => 100 + 3*i)
  ⟨register n,⟨#[⟨11,#[.bit],#[100+3*k]⟩,
    ⟨12,#[.bits (n-1)],(axes.toList.take k ++ axes.toList.drop (k+1)).toArray⟩],#[]⟩⟩
def unaryConversion (input output : Basis) (axes : Array Nat) : Interface :=
  ⟨⟨#[⟨1,input,axes⟩],#[]⟩,⟨#[⟨2,output,axes⟩],#[]⟩⟩
def tupleConversion (fields : Array QuantumPort) : Interface :=
  let tree := fields.foldl (fun a p => a ++ p.basis) #[.tuple fields.size]
  ⟨⟨#[⟨90,tree,fields.foldl (fun a p => a ++ p.axes) #[]⟩],#[]⟩,⟨fields,#[]⟩⟩
def flatFields : Array QuantumPort := #[⟨1,#[.bit],#[7]⟩,⟨2,#[.unit],#[]⟩,⟨3,#[.bits 0],#[]⟩,⟨4,#[.bits 2],#[9,2]⟩]
def nestedFields : Array QuantumPort := #[⟨1,#[.tuple 2,.bit,.unit],#[7]⟩,⟨2,#[.bits 2],#[9,2]⟩]
def emptyConversion (basis : Basis) : Interface := ⟨noPorts,⟨#[⟨9,basis,#[]⟩],#[]⟩⟩
def modifyOutput (i : Interface) (f : Array QuantumPort → Array QuantumPort) : Interface :=
  {i with outputs := {i.outputs with quantum := f i.outputs.quantum}}
def convertArtifact (operation : StructuralOp) (i : Interface) : Artifact :=
  {definitions := #[⟨i,.unitary,.structural operation⟩], meanings := #[⟨i,.structural operation⟩],
   encodings := #[identityE i.inputs,identityE i.outputs],
   proofs := #[{proof with rule := .structural,outputEncoding := 1}], entry := ⟨0,0⟩}
def natJson (values : List Nat) : String := "[" ++ String.intercalate "," (values.map toString) ++ "]"
def reportStructural (name : String) (operation : StructuralOp) (i : Interface) (budget : Nat) : IO Unit :=
  match accepted : Structural.check operation i budget with
  | .error e => IO.println s!"{name}|{code ⟨e,none⟩}"
  | .ok checked =>
    let map := Structural.axisMap i
    let back := Structural.inverseAxes i
    let n := (wires i.inputs).size
    let h := Structural.check_axes operation i budget checked accepted
    let routed := (List.range (2^n)).map fun value =>
      let bits : Fin n → Bool := fun bit => (value / 2^bit.val) % 2 == 1
      let actual := QleisliKernel.Layout.reindex map h.forwardBound bits
      (List.finRange n).foldl (fun acc bit => acc + (if actual bit then 2^bit.val else 0)) 0
    IO.println s!"{name}|typed|{checked.visits}|{natJson map}|{natJson back}|{natJson routed}"
'''


def cases():
    rows = []
    routes = {}
    def add(name,op,interface,status='typed',route=None,budget=2000000):
        rows.append((name,f'reportStructural {json.dumps(name)} ({op}) ({interface}) {budget}',status))
        if route is not None: routes[name] = route
    for n in range(1,9):
        for k in range(n):
            forward=[k]+[i for i in range(n) if i!=k]
            backward=[forward.index(i) for i in range(n)]
            add(f'take-{n}-{k}',f'.takeBit {n} {k}',f'splitRegister {n} {k}',route=forward)
            add(f'put-{n}-{k}',f'.putBit {n} {k}',f'Structural.swapped (splitRegister {n} {k})',route=backward)
    for label,fields,n in [('flat','flatFields',3),('nested','nestedFields',3),
                             ('all-zero','#[⟨1,#[.unit],#[]⟩,⟨2,#[.bits 0],#[]⟩]',0)]:
        add(f'tuple-split-{label}','.splitTuple',f'tupleConversion {fields}',route=list(range(n)))
        add(f'tuple-join-{label}','.joinTuple',f'Structural.swapped (tupleConversion {fields})',route=list(range(n)))
    add('bit-to-bits','.bitToBits','unaryConversion #[.bit] #[.bits 1] #[57]',route=[0])
    add('bits-to-bit','.bitsToBit','unaryConversion #[.bits 1] #[.bit] #[57]',route=[0])
    for kind,basis in [('Unit','.unit'),('EmptyBits','.bits 0')]:
        add(f'pack-{kind}',f'.pack{kind}',f'emptyConversion #[{basis}]',route=[])
        add(f'unpack-{kind}',f'.unpack{kind}',f'Structural.swapped (emptyConversion #[{basis}])',route=[])
    for n,k in [(0,0),(9,0),(1,1),(8,8),(100000000,0),(8,4294967296)]:
        add(f'bad-static-{n}-{k}',f'.takeBit {n} {k}','splitRegister 1 0','invalid_ir')
    negatives=[
      ('wrong-selected-axis','.takeBit 8 4','splitRegister 8 3'),
      ('remainder-reversed','.takeBit 8 3','modifyOutput (splitRegister 8 3) (fun ps => ps.mapIdx (fun j p => if j==1 then {p with axes := p.axes.reverse} else p))'),
      ('missing-zero-remainder','.takeBit 1 0','modifyOutput (splitRegister 1 0) (fun ps => ps.extract 0 1)'),
      ('unit-is-not-zero-bits','.takeBit 1 0','modifyOutput (splitRegister 1 0) (fun ps => ps.mapIdx (fun j p => if j==1 then {p with basis := #[.unit]} else p))'),
      ('selected-bits1-is-not-bit','.takeBit 1 0','modifyOutput (splitRegister 1 0) (fun ps => ps.mapIdx (fun j p => if j==0 then {p with basis := #[.bits 1]} else p))'),
      ('old-owner-reused','.takeBit 1 0','modifyOutput (splitRegister 1 0) (fun ps => ps.mapIdx (fun j p => if j==0 then {p with owner := 10} else p))'),
      ('duplicate-zero-owner','.takeBit 1 0','modifyOutput (splitRegister 1 0) (fun ps => ps.map (fun p => {p with owner := 11}))'),
      ('duplicated-remainder','.takeBit 1 0','modifyOutput (splitRegister 1 0) (fun ps => ps ++ ps.extract 1 2)'),
      ('wire-duplicate','.takeBit 2 0','modifyOutput (splitRegister 2 0) (fun ps => ps.map (fun p => {p with axes := #[100]}))'),
      ('extra-frame','.takeBit 2 0','modifyOutput (splitRegister 2 0) (fun ps => ps.push ⟨99,#[.unit],#[]⟩)'),
      ('classical-output','.takeBit 1 0','{splitRegister 1 0 with outputs := {(splitRegister 1 0).outputs with classical := #[⟨1,#[.bit]⟩]}}'),
      ('tuple-unary','.splitTuple','tupleConversion #[⟨1,#[.bit],#[0]⟩]'),
      ('tuple-empty','.splitTuple','tupleConversion #[]'),
      ('tuple-arity-change','.splitTuple','{tupleConversion flatFields with inputs := ⟨#[⟨90,#[.tuple 3,.bit,.unit,.bits 2],#[7,9,2]⟩],#[]⟩}'),
      ('nested-flattened','.splitTuple','{tupleConversion nestedFields with inputs := ⟨#[⟨90,#[.tuple 3,.bit,.unit,.bits 2],#[7,9,2]⟩],#[]⟩}'),
      ('tuple-axis-order','.splitTuple','modifyOutput (tupleConversion nestedFields) (fun ps => ps.reverse)'),
      ('tuple-zero-owner-lost','.splitTuple','modifyOutput (tupleConversion flatFields) (fun ps => ps.filter (fun p => p.owner != 3))'),
      ('bit-conversion-identity','.bitToBits','unaryConversion #[.bit] #[.bit] #[57]'),
      ('bit-conversion-wire-change','.bitToBits','modifyOutput (unaryConversion #[.bit] #[.bits 1] #[57]) (fun ps => ps.map (fun p => {p with axes := #[58]}))'),
      ('empty-wrong-type','.packEmptyBits','emptyConversion #[.unit]'),
      ('empty-duplicate-owner','.packUnit','modifyOutput (emptyConversion #[.unit]) (fun ps => ps ++ ps)'),
      ('empty-implicit-consume','.packUnit','Structural.swapped (emptyConversion #[.unit])'),
    ]
    for name,op,i in negatives: add(name,op,i,'invalid_ir')
    add('budget-zero','.takeBit 8 4','splitRegister 8 4','limit',budget=0)
    add('budget-profile-excess','.takeBit 1 0','splitRegister 1 0','limit',budget=2000001)
    add('oversized-header','.splitTuple','tupleConversion (Array.replicate 100000 ⟨1,#[.unit],#[]⟩)','limit')
    # Exact remaining-budget boundary, independent arithmetic from the published charge.
    # For take(1,0): scan=3; side charges 1+4+4+4 and 1+16+8+4; two wires total.
    boundary=8*4**2+16*(1+13+29)+8*3**2
    add('exact-budget','.takeBit 1 0','splitRegister 1 0',budget=boundary,route=[0])
    add('one-under-budget','.takeBit 1 0','splitRegister 1 0','limit',budget=boundary-1)
    for name,op,i in [('whole-eight','.takeBit 8 7','splitRegister 8 7'),
                       ('whole-zero','.takeBit 1 0','splitRegister 1 0'),
                       ('whole-tuple','.splitTuple','tupleConversion nestedFields')]:
        rows.append((name,f'reportComplete "{name}" (convertArtifact ({op}) ({i})) #[0,1,2,3,4]','typed'))
    rows.append(('whole-invalid','reportComplete "whole-invalid" (convertArtifact (.takeBit 1 0) (modifyOutput (splitRegister 1 0) (fun ps => ps.extract 0 1))) #[0,1,2,3,4]','invalid_ir'))
    rows.append(('rewire-still-rejects-split','reportNode "rewire-still-rejects-split" (localArtifact #[⟨splitRegister 8 7,.unitary,.rewire ⟨#[0,0],#[7,0,1,2,3,4,5,6],#[]⟩⟩]) 0 2000000','invalid_ir'))
    rows.append(('nonunitary-annotation','reportNode "nonunitary-annotation" (localArtifact #[⟨splitRegister 1 0,.iso,.structural (.takeBit 1 0)⟩]) 0 2000000','invalid_ir'))
    return rows,routes


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record',type=Path)
    args=parser.parse_args()
    rows,routes=cases()
    source=PRELUDE+'\n'+'\n'.join(f'def case{i} : IO Unit := {call}' for i,(_,call,_) in enumerate(rows))+'\n'
    groups=list(range(0,len(rows),16))
    for first in groups:
        source+=f'def group{first} : IO Unit := do\n'+'\n'.join(f'  case{i}' for i in range(first,min(first+16,len(rows))))+'\n'
    source+='def main : IO Unit := do\n'+'\n'.join(f'  group{i}' for i in groups)+'\n'
    commands,binary=build_and_run(source,args.record)
    results={}
    for line in commands[-1]['stdout'].splitlines():
        name,*fields=line.split('|')
        assert name not in results
        results[name]=fields
    if args.record: args.record.write_text(json.dumps(dict(status='observed-not-yet-compared',results=results,commands=commands),indent=2)+'\n')
    assert len(results)==len(rows)
    basis_checks=0
    for name,_,expected in rows:
        assert results[name][0]==expected,(name,results[name],expected)
        if name not in routes: continue
        forward=routes[name]
        actual=json.loads(results[name][2])
        backward=json.loads(results[name][3])
        routed=json.loads(results[name][4])
        assert actual==forward,(name,actual,forward)
        assert backward==[forward.index(i) for i in range(len(forward))]
        for x,y in enumerate(routed):
            # Independent weighted-bit formula; no Lean layout helper reused.
            expected_y=sum(((x>>source)&1)<<dest for dest,source in enumerate(forward))
            assert y==expected_y,(name,x,y,expected_y)
            restored=sum(((y>>source)&1)<<dest for dest,source in enumerate(backward))
            assert restored==x
            basis_checks+=1
    report=dict(format='qleisli.hierarchical-structural-validation',version=1,status='passed',cases=len(rows),
                typed=sum(status=='typed' for _,_,status in rows),basis_checks=basis_checks,
                maximum_dense_dimension=0,reference_scope="actual Lean coefficient round-trip theorem",
                external_semantic_evidence=False,binary_sha256=binary,harness_sha256=hashlib.sha256(source.encode()).hexdigest(),
                results=results,commands=commands,source_sha256={str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest()
                 for path in [*sorted((ROOT/'lean-kernel/QleisliKernel/Hierarchical').glob('*.lean')),Path(__file__).resolve()]})
    if args.record: args.record.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in {'results','commands'}}))

if __name__=='__main__': main()
