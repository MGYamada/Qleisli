#!/usr/bin/env python3
"""Actual hierarchical node typing, ownership/effects and whole-table checking.

This suite never treats structural typing as semantic proof or finite verification.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import hashlib
import json
from pathlib import Path
from test_hierarchical_artifact import PRELUDE, ROOT, build_and_run

PRELUDE = PRELUDE.replace('import QleisliKernel.Hierarchical.Ports',
                          'import QleisliKernel.Hierarchical.NodeTyping') + r'''
open QleisliKernel.Hierarchical
def bside (owner axis : Nat) : Side := ⟨#[⟨owner,#[.bit],#[axis]⟩],#[]⟩
def leaf (s : Side) : Definition := ⟨⟨s,s⟩,.unitary,.leaf (bytes 1)⟩
def localArtifact (definitions : Array Definition) : Artifact :=
  {base 1 with definitions := definitions}
def single (body : Body) (effect : Effect := .unitary) : Artifact :=
  localArtifact #[⟨⟨bside 0 0,bside 0 0⟩,effect,body⟩]
def wrap (body : Body) (effect : Effect := .unitary) : Artifact :=
  localArtifact #[leaf (bside 0 0),⟨⟨bside 0 0,bside 0 0⟩,effect,body⟩]
def initialized : Definition := ⟨⟨noPorts,bside 0 0⟩,.iso,.init0 0⟩
def observed : Definition := ⟨⟨bside 0 0,⟨#[],#[⟨1,#[.bit]⟩]⟩⟩,.observe,.observeZ 0 1⟩
def trial (order : Array Nat) (effect : Effect) : Artifact :=
  localArtifact #[initialized,observed,⟨⟨noPorts,⟨#[],#[⟨1,#[.bit]⟩]⟩⟩,effect,.sequence order⟩]
def parentCall (outOwner outAxis : Nat) : Definition :=
  ⟨⟨bside 10 10,bside outOwner outAxis⟩,.unitary,.call 0 (identityMap 1) (identityMap 1)⟩
def called (outOwner outAxis : Nat) : Artifact :=
  localArtifact #[leaf (bside 7 3),parentCall outOwner outAxis]
def newCalled (outOwner : Nat) : Artifact :=
  localArtifact #[⟨⟨bside 7 3,bside 8 3⟩,.unitary,.rewire (identityMap 1)⟩,parentCall outOwner 10]
def controller (owner axis : Nat) (basis : Basis := #[.bit]) : Artifact :=
  let c : Side := ⟨#[⟨owner,basis,#[axis]⟩],#[]⟩
  let s := NodeTyping.append c (bside 0 0)
  localArtifact #[leaf (bside 0 0),⟨⟨s,s⟩,.unitary,.control 0 true⟩]
def parallel (owner axis : Nat) : Artifact :=
  let a := leaf (bside 0 0)
  let b := leaf (bside owner axis)
  let s := NodeTyping.append a.interface.inputs b.interface.inputs
  localArtifact #[a,b,⟨⟨s,s⟩,.unitary,.tensor 0 1⟩]
def measuredFrame : Definition :=
  ⟨⟨⟨#[⟨0,#[.bit],#[0]⟩,⟨2,#[.bits 0],#[]⟩],#[⟨4,#[.bit]⟩]⟩,
    ⟨#[⟨2,#[.bits 0],#[]⟩],#[⟨4,#[.bit]⟩,⟨5,#[.bit]⟩]⟩⟩,.observe,.observeZ 0 5⟩
def preparedFrame : Definition :=
  ⟨⟨⟨#[⟨2,#[.bits 0],#[]⟩],#[⟨4,#[.bit]⟩]⟩,
    ⟨#[⟨2,#[.bits 0],#[]⟩,⟨0,#[.bit],#[0]⟩],#[⟨4,#[.bit]⟩]⟩⟩,.iso,.init0 0⟩
def computeRegion : Artifact :=
  let logical := bside 0 0
  let physical := NodeTyping.append logical (bside 1 1)
  {base 1 with definitions := #[leaf physical,leaf physical,
      ⟨⟨logical,logical⟩,.unitary,.computed 0 1 0 0⟩],
               meanings := #[⟨⟨logical,logical⟩,.identity⟩], encodings := #[⟨logical,physical,.zeroScratch 1 0⟩]}
def invalidZeroTyped : Artifact :=
  {repeated 0 with definitions := #[⟨signature 1,.unitary,.dyadicPhase 0 1 3⟩,
    ⟨signature 1,.unitary,.repeatOp 0 0⟩]}
def lifetimeTensor : Artifact :=
  localArtifact #[observed,initialized,
    ⟨⟨observed.interface.inputs,NodeTyping.append observed.interface.outputs initialized.interface.outputs⟩,
      .observe,.tensor 0 1⟩]
def classicalCall (output : Nat) : Artifact :=
  let callee : Definition := ⟨⟨⟨#[],#[⟨3,#[.bit]⟩]⟩,⟨#[],#[⟨4,#[.bit]⟩]⟩⟩,.observe,.leaf (bytes 1)⟩
  let caller : Definition := ⟨⟨⟨#[],#[⟨10,#[.bit]⟩]⟩,⟨#[],#[⟨output,#[.bit]⟩]⟩⟩,.observe,
    .call 0 ⟨#[],#[],#[0]⟩ ⟨#[],#[],#[0]⟩⟩
  localArtifact #[callee,caller]
def renamedUnitary (swap : Bool) (isRepeat : Bool) : Artifact :=
  let a := bside 0 0
  let b := bside 1 0
  let interface : Interface := if swap then ⟨b,a⟩ else ⟨a,b⟩
  localArtifact #[⟨⟨a,b⟩,.unitary,.rewire (identityMap 1)⟩,
    ⟨interface,.unitary,if isRepeat then .repeatOp 0 0 else .inverse 0⟩]
def reportNode (name : String) (a : Artifact) (index budget : Nat) : IO Unit :=
  match NodeTyping.check a index budget with
  | .error e => IO.println s!"{name}|{code ⟨e,none⟩}"
  | .ok checked => IO.println s!"{name}|typed|{checked.visits}"
def reportAll (name : String) (a : Artifact) (order : Array Nat) : IO Unit :=
  match NodeTyping.checkAll a order with
  | .error e => IO.println s!"{name}|{code e}"
  | .ok checked => IO.println s!"{name}|typed|{checked.totalVisits}"
'''


def cases():
    rows = []
    def add(name, expression, status, index=0, budget=2000000):
        rows.append((name,f'reportNode {json.dumps(name)} ({expression}) {index} {budget}',status))
    add('finite-leaf-remains-obligation','single (.leaf (bytes 1))','typed')
    add('empty-finite-rejected','single (.leaf (bytes 0))','invalid_ir')
    for j,k in [(0,0),(1,1),(1,3),(31,5),(255,8)]:
        add(f'phase-{j}-{k}',f'single (.dyadicPhase 0 {j} {k})','typed')
    add('phase-needs-Bit-not-Bits1','changeDef (base 1) (fun d => {d with body := .dyadicPhase 0 1 3})','invalid_ir')
    add('phase-owner-outside','single (.dyadicPhase 7 1 3)','invalid_ir')
    add('phase-invalid-angle','single (.dyadicPhase 0 256 8)','invalid_ir')
    add('phase-wrong-effect','single (.dyadicPhase 0 1 3) .iso','invalid_ir')
    add('rewire','single (.rewire (identityMap 1))','typed')
    add('rewire-missing-owner','single (.rewire ⟨#[],#[0],#[]⟩)','invalid_ir')
    for count in [0,1,4096]:
        add(f'repeat-{count}',f'wrap (.repeatOp {count} 0)','typed',1)
    add('repeat-excess','wrap (.repeatOp 4097 0)','invalid_ir',1)
    add('repeat-missing-child','wrap (.repeatOp 1 2)','invalid_ir',1)
    add('repeat-wrong-effect','wrap (.repeatOp 1 0) .iso','invalid_ir',1)
    add('repeat-nonunitary','{wrap (.repeatOp 0 0) with definitions := #[{leaf (bside 0 0) with effect := .observe},⟨⟨bside 0 0,bside 0 0⟩,.unitary,.repeatOp 0 0⟩]}','invalid_ir',1)
    add('inverse','wrap (.inverse 0)','typed',1)
    add('inverse-nonunitary','localArtifact #[initialized,⟨⟨bside 0 0,noPorts⟩,.unitary,.inverse 0⟩]','invalid_ir',1)
    add('sequence-pure','wrap (.sequence #[0,0])','typed',1)
    add('sequence-empty','wrap (.sequence #[])','invalid_ir',1)
    add('sequence-effect-join','trial #[0,1] .observe','typed',2)
    add('sequence-wrong-order','trial #[1,0] .observe','invalid_ir',2)
    add('sequence-underreported-effect','trial #[0,1] .unitary','invalid_ir',2)
    add('tensor-cross-lifetime-capture','lifetimeTensor','invalid_ir',2)
    add('classical-call-fresh','classicalCall 11','typed',1)
    add('classical-call-capture','classicalCall 10','invalid_ir',1)
    add('inverse-swaps-endpoints','renamedUnitary true false','typed',1)
    add('inverse-keeps-wrong-endpoints','renamedUnitary false false','invalid_ir',1)
    add('zero-repeat-needs-closed-identity','renamedUnitary false true','invalid_ir',1)
    add('tensor-disjoint','parallel 1 1','typed',2)
    add('tensor-owner-alias','parallel 0 1','invalid_ir',2)
    add('tensor-axis-alias','parallel 1 0','invalid_ir',2)
    add('call-consistent','called 10 10','typed',1)
    add('call-owner-changes-between-maps','called 11 10','invalid_ir',1)
    add('call-axis-changes-between-maps','called 10 11','invalid_ir',1)
    add('call-new-owner-fresh','newCalled 11','typed',1)
    add('call-new-owner-captures-input','newCalled 10','invalid_ir',1)
    add('controlled','controller 1 1','typed',1)
    add('control-owner-alias','controller 0 1','invalid_ir',1)
    add('control-axis-alias','controller 1 0','invalid_ir',1)
    add('control-needs-Bit','controller 1 1 #[.bits 1]','invalid_ir',1)
    add('init','localArtifact #[initialized]','typed')
    add('observe','localArtifact #[observed]','typed')
    add('measure-preserves-zero-and-classical-frame','localArtifact #[measuredFrame]','typed')
    add('measure-drops-zero-frame','localArtifact #[{measuredFrame with interface := {measuredFrame.interface with outputs := ⟨#[],measuredFrame.interface.outputs.classical⟩}}]','invalid_ir')
    add('measure-overwrites-classical','localArtifact #[{measuredFrame with body := .observeZ 0 4}]','invalid_ir')
    add('measure-wrong-owner','localArtifact #[{measuredFrame with body := .observeZ 2 5}]','invalid_ir')
    add('init-preserves-zero-and-classical-frame','localArtifact #[preparedFrame]','typed')
    add('init-wrong-effect','localArtifact #[{initialized with effect := .unitary}]','invalid_ir')
    add('init-reuses-owner','localArtifact #[{preparedFrame with body := .init0 2}]','invalid_ir')
    add('init-mutates-classical-frame','localArtifact #[{preparedFrame with interface := {preparedFrame.interface with outputs := {preparedFrame.interface.outputs with classical := #[]}}}]','invalid_ir')
    add('computed-equation-remains-obligation','computeRegion','typed',2)
    add('computed-wrong-compute-reference','changeEncoding computeRegion (fun e => {e with body := .zeroScratch 1 1})','invalid_ir',2)
    add('computed-wrong-encoding-kind','changeEncoding computeRegion (fun e => {e with body := .identity})','invalid_ir',2)
    add('budget-zero','single (.rewire (identityMap 1))','limit',budget=0)
    add('budget-profile-overflow','single (.rewire (identityMap 1))','limit',budget=2000001)
    add('oversized-node','oversizedPorts','limit')
    add('oversized-children','oversizedReferences','limit')
    add('zero-repeat-parent-alone-insufficient','invalidZeroTyped','typed',1)
    whole = [
        ('whole-budget-shared','proofStar 4986','Array.range 4989','limit'),
        ('whole-base','base 1','order','typed'),
        ('whole-zero-repeat','repeated 0','#[0,1,2,3,4]','typed'),
        ('whole-zero-repeat-invalid-body','invalidZeroTyped','#[0,1,2,3,4]','invalid_ir'),
        ('whole-cycle','zeroCycle','order','invalid_ir'),
        ('whole-phase-fault-still-needs-semantics','changeDef (typed #[.bit] 1) (fun d => {d with body := .dyadicPhase 0 1 3})','order','typed'),
    ]
    rows += [(name,f'reportAll {json.dumps(name)} ({a}) ({order})',status) for name,a,order,status in whole]
    return rows


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record',type=Path)
    args=parser.parse_args()
    rows=cases()
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
    for name,_,expected in rows: assert results[name][0]==expected,(name,results[name],expected)
    report=dict(format='qleisli.hierarchical-typing-validation',version=1,status='passed',cases=len(rows),
                typed=sum(status=='typed' for _,_,status in rows),semantic_evidence_issued=False,
                binary_sha256=binary,harness_sha256=hashlib.sha256(source.encode()).hexdigest(),results=results,commands=commands,
                source_sha256={str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in [
                    *sorted((ROOT/'lean-kernel/QleisliKernel/Hierarchical').glob('*.lean')),
                    ROOT/'scripts/test_hierarchical_artifact.py',Path(__file__).resolve()]})
    if args.record: args.record.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in {'results','commands'}}))


if __name__=='__main__': main()
