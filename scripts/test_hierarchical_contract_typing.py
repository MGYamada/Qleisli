#!/usr/bin/env python3
"""Meaning/encoding headers, QPE provider binding and explicit zero-scratch shapes.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Success is structural typing, never a finite equation or semantic receipt.
"""
import argparse
import hashlib
import json
from pathlib import Path
from test_hierarchical_typing import PRELUDE
from test_hierarchical_artifact import ROOT, build_and_run

PRELUDE = PRELUDE.replace('import QleisliKernel.Hierarchical.NodeTyping',
                         'import QleisliKernel.Hierarchical.ContractTyping') + r'''
def withMeanings (meanings : Array Meaning) : Artifact := {base 1 with meanings := meanings}
def pureM (s : Side) (body : MeaningBody) : Meaning := ⟨⟨s,s⟩,body⟩
def mone (s : Side) (body : MeaningBody) : Artifact := withMeanings #[pureM s body]
def phaseM : Meaning := pureM (bside 0 0) (.phase 1 3)
def meaningPair (body : MeaningBody) : Artifact := withMeanings #[phaseM,pureM (bside 0 0) body]
def qpeM (n m : Nat) : Artifact :=
  let s := side n
  withMeanings #[pureM s .identity,⟨⟨s,⟨s.quantum,#[⟨9,#[.bits m]⟩]⟩⟩,.qpeInstrument n m 0⟩]
def qpeChanged (n m : Nat) (f : Meaning → Meaning) : Artifact :=
  {qpeM n m with meanings := (qpeM n m).meanings.mapIdx (fun i value => if i==1 then f value else value)}
def tensorMeaning (owner axis : Nat) : Artifact :=
  let a := pureM (bside 0 0) .identity
  let b := pureM (bside owner axis) .identity
  withMeanings #[a,b,pureM (NodeTyping.append a.interface.inputs b.interface.inputs) (.tensor 0 1)]
def controlMeaning (converted : Bool) : Artifact :=
  let a := bside 0 0
  let b : Side := if converted then ⟨#[⟨1,#[.bits 1],#[0]⟩],#[]⟩ else bside 1 0
  let c := bside 2 1
  withMeanings #[⟨⟨a,b⟩,.finite (bytes 1)⟩,
    ⟨⟨NodeTyping.append c a,NodeTyping.append c b⟩,.control 0 true⟩]
def controlDefinition : Artifact :=
  let a := bside 0 0
  let b : Side := ⟨#[⟨1,#[.bits 1],#[0]⟩],#[]⟩
  let c := bside 2 1
  localArtifact #[⟨⟨a,b⟩,.unitary,.leaf (bytes 1)⟩,
    ⟨⟨NodeTyping.append c a,NodeTyping.append c b⟩,.unitary,.control 0 true⟩]
def withEncodings (encodings : Array Encoding) : Artifact := {base 1 with encodings := encodings}
def identityE (s : Side) : Encoding := ⟨s,s,.identity⟩
def eone (s : Side) : Artifact := withEncodings #[identityE s]
def zeroE (privateBasis : Basis) (axes : Array Nat) (count : Nat) : Artifact :=
  let logical := bside 0 0
  let physical := NodeTyping.append logical ⟨#[⟨1,privateBasis,axes⟩],#[]⟩
  {base 1 with definitions := #[leaf physical],
               encodings := #[⟨logical,physical,.zeroScratch count 0⟩]}
def tensorEncoding (owner axis : Nat) : Artifact :=
  let a := identityE (bside 0 0)
  let b := identityE (bside owner axis)
  let s := NodeTyping.append a.logical b.logical
  withEncodings #[a,b,⟨s,s,.tensor 0 1⟩]
def rewireEncoding (changedLogical : Bool) : Artifact :=
  let a := identityE bitPair
  let logical := if changedLogical then renamedPair else bitPair
  withEncodings #[a,⟨logical,renamedPair,.rewire 0 ⟨#[1,0],#[1,0],#[]⟩⟩]
def hiddenMeaning : Artifact :=
  {repeated 0 with meanings := #[pureM (side 1) (.phase 1 3),pureM (side 1) (.power 0 0)], proofs := #[{proof with implementation := 1,meaning := 1}]}
def falseScratch : Artifact :=
  {base 1 with encodings := #[⟨side 1,side 1,.zeroScratch 1 0⟩]}
def reportContract (name : String) (a : Artifact) (ref : Ref) (budget : Nat) : IO Unit :=
  match ContractTyping.check a ref budget with
  | .error e => IO.println s!"{name}|{code ⟨e,none⟩}"
  | .ok checked => IO.println s!"{name}|typed|{checked.visits}"
def reportComplete (name : String) (a : Artifact) (order : Array Nat) : IO Unit :=
  match ContractTyping.checkAll a order with
  | .error e => IO.println s!"{name}|{code e}"
  | .ok checked => IO.println s!"{name}|typed|{checked.totalVisits}"
'''


def cases():
    rows=[]
    def add(name,expression,status='typed',index=0,table='meaning',budget=2000000):
        rows.append((name,f'reportContract {json.dumps(name)} ({expression}) ⟨.{table},{index}⟩ {budget}',status))
    for n in range(9):
        add(f'identity-{n}',f'mone (side {n}) .identity')
        add(f'finite-{n}',f'mone (side {n}) (.finite (bytes 1))','typed' if n<=6 else 'limit')
        add(f'qft-{n}',f'mone (side {n}) (.qft {n})','typed' if n else 'invalid_ir')
    add('finite-empty','mone (side 1) (.finite (bytes 0))','invalid_ir')
    add('pure-no-classical','mone classicalSide .identity','invalid_ir')
    add('identity-exact-owners','withMeanings #[⟨⟨bside 0 0,bside 1 0⟩,.identity⟩]','invalid_ir')
    add('qft-no-product-substitution','mone (tupleSide flat) (.qft 3)','invalid_ir')
    add('qft-no-Bit-substitution','mone (bside 0 0) (.qft 1)','invalid_ir')
    add('qft-axis-order','withMeanings #[⟨⟨side 2,⟨#[⟨0,#[.bits 2],#[1,0]⟩],#[]⟩⟩,.qft 2⟩]','invalid_ir')
    add('phase-Bit','mone (bside 0 0) (.phase 1 8)')
    add('phase-not-Bits1','mone (side 1) (.phase 1 3)','invalid_ir')
    add('phase-not-multiple-owners','mone bitPair (.phase 1 3)','invalid_ir')
    add('phase-outside-domain','mone (bside 0 0) (.phase 256 8)','invalid_ir')
    add('sequence','meaningPair (.sequence #[0,0])',index=1)
    add('sequence-empty','meaningPair (.sequence #[])','invalid_ir',index=1)
    add('sequence-dangling','meaningPair (.sequence #[2])','invalid_ir',index=1)
    add('tensor','tensorMeaning 1 1',index=2)
    add('tensor-owner-alias','tensorMeaning 0 1','invalid_ir',index=2)
    add('tensor-axis-alias','tensorMeaning 1 0','invalid_ir',index=2)
    add('inverse','meaningPair (.inverse 0)',index=1)
    add('inverse-rectangular','withMeanings #[⟨⟨side 1,side 2⟩,.finite (bytes 1)⟩,⟨⟨side 2,side 1⟩,.inverse 0⟩]','invalid_ir',index=1)
    add('control-renamed-same-type','controlMeaning false',index=1)
    add('control-forbids-implicit-conversion','controlMeaning true','invalid_ir',index=1)
    for count in [0,1,4096]: add(f'power-{count}',f'meaningPair (.power 0 {count})',index=1)
    add('power-outside-domain','meaningPair (.power 0 4097)','invalid_ir',index=1)
    add('power-not-closed','withMeanings #[⟨⟨bside 0 0,bside 1 0⟩,.finite (bytes 1)⟩,⟨⟨bside 0 0,bside 1 0⟩,.power 0 0⟩]','invalid_ir',index=1)
    add('rewire','mone bitPair (.rewire ⟨#[1,0],#[1,0],#[]⟩)')
    add('rewire-missing-owner','mone bitPair (.rewire ⟨#[0],#[0,1],#[]⟩)','invalid_ir')
    for n in range(1,9):
        for m in range(1,9): add(f'qpe-header-{n}-{m}',f'qpeM {n} {m}',index=1)
    add('qpe-target-zero','qpeM 0 1','invalid_ir',index=1)
    add('qpe-precision-zero','qpeM 1 0','invalid_ir',index=1)
    add('qpe-wrong-provider-type','{qpeM 1 3 with meanings := (qpeM 1 3).meanings.mapIdx (fun i m => if i==0 then pureM (bside 0 0) .identity else m)}','invalid_ir',index=1)
    add('qpe-wrong-precision-type','qpeChanged 1 3 (fun m => {m with interface := {m.interface with outputs := ⟨(side 1).quantum,#[⟨9,#[.bits 2]⟩]⟩}})','invalid_ir',index=1)
    add('qpe-cannot-drop-target','qpeChanged 1 3 (fun m => {m with interface := {m.interface with outputs := ⟨#[],#[⟨9,#[.bits 3]⟩]⟩}})','invalid_ir',index=1)
    add('qpe-cannot-measure-target','qpeChanged 1 3 (fun m => {m with interface := {m.interface with outputs := ⟨#[],#[⟨9,#[.bits 4]⟩]⟩}})','invalid_ir',index=1)
    for op in ['.inverse 1','.power 1 0','.sequence #[1]']:
        add('instrument-not-pure-'+op.split()[0][1:],f'{{qpeM 1 1 with meanings := (qpeM 1 1).meanings.push (pureM (side 1) ({op}))}}','invalid_ir',index=2)
    for n in range(9): add(f'encoding-identity-{n}',f'eone (side {n})',table='encoding')
    add('encoding-classical-identity','eone classicalSide',table='encoding')
    add('encoding-identity-wrong-name','withEncodings #[⟨bside 0 0,bside 1 0,.identity⟩]','invalid_ir',table='encoding')
    add('encoding-identity-wrong-type','withEncodings #[⟨side 1,bside 0 0,.identity⟩]','invalid_ir',table='encoding')
    add('encoding-tensor','tensorEncoding 1 1',index=2,table='encoding')
    add('encoding-tensor-alias','tensorEncoding 0 1','invalid_ir',index=2,table='encoding')
    add('encoding-rewire','rewireEncoding false',index=1,table='encoding')
    add('encoding-rewire-changes-logical','rewireEncoding true','invalid_ir',index=1,table='encoding')
    add('scratch-one','zeroE #[.bit] #[1] 1',table='encoding')
    add('scratch-zero-owner','zeroE #[.bits 0] #[] 0',table='encoding')
    add('scratch-unit-owner','zeroE #[.unit] #[] 0',table='encoding')
    add('scratch-count-understated','zeroE #[.bit] #[1] 0','invalid_ir',table='encoding')
    add('scratch-count-overstated','zeroE #[.bits 0] #[] 1','invalid_ir',table='encoding')
    add('scratch-axis-capture','zeroE #[.bit] #[0] 1','invalid_ir',table='encoding')
    add('scratch-compute-not-unitary','changeDef (zeroE #[.bit] #[1] 1) (fun d => {d with effect := .iso})','invalid_ir',table='encoding')
    add('scratch-prefix-not-dimension','changeEncoding (zeroE #[.bit] #[1] 1) (fun e => {e with logical := bside 1 1})','invalid_ir',table='encoding')
    add('scratch-logical-type-change','changeEncoding (zeroE #[.bit] #[1] 1) (fun e => {e with logical := side 1})','invalid_ir',table='encoding')
    add('wrong-reference-table','base 1','invalid_ir',table='definition')
    add('missing-reference','base 1','invalid_ir',index=1)
    add('zero-budget','base 1','limit',budget=0)
    add('too-large-budget','base 1','limit',budget=2000001)
    add('oversized-meaning','changeMeaning (base 1) (fun m => {m with body := .sequence (Array.replicate 1000001 0)})','limit')
    rows.append(('control-definition-conversion', 'reportNode "control-definition-conversion" controlDefinition 1 2000000','invalid_ir'))
    whole=[('whole-base','base 8','order','typed'),('whole-zero','repeated 0','#[0,1,2,3,4]','typed'),
           ('whole-hidden-meaning','hiddenMeaning','#[0,1,2,3,4,5]','invalid_ir'),
           ('whole-false-scratch','falseScratch','order','invalid_ir'),
           ('whole-budget','proofStar 4986','Array.range 4989','limit'),
           ('whole-phase-still-needs-proof','changeDef (typed #[.bit] 1) (fun d => {d with body := .dyadicPhase 0 1 3})','order','typed')]
    rows += [(name,f'reportComplete {json.dumps(name)} ({artifact}) ({order})',status) for name,artifact,order,status in whole]
    return rows


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record',type=Path)
    args=parser.parse_args();rows=cases()
    source=PRELUDE+'\n'+'\n'.join(f'def case{i} : IO Unit := {call}' for i,(_,call,_) in enumerate(rows))+'\n'
    groups=list(range(0,len(rows),16))
    for first in groups:
        source+=f'def group{first} : IO Unit := do\n'+'\n'.join(f'  case{i}' for i in range(first,min(first+16,len(rows))))+'\n'
    source+='def main : IO Unit := do\n'+'\n'.join(f'  group{i}' for i in groups)+'\n'
    commands,binary=build_and_run(source,args.record);results={}
    for line in commands[-1]['stdout'].splitlines():
        name,*fields=line.split('|');assert name not in results;results[name]=fields
    if args.record: args.record.write_text(json.dumps(dict(status='observed-not-yet-compared',results=results,commands=commands),indent=2)+'\n')
    assert len(results)==len(rows)
    for name,_,expected in rows: assert results[name][0]==expected,(name,results[name],expected)
    report=dict(format='qleisli.hierarchical-contract-typing-validation',version=1,status='passed',cases=len(rows),
                typed=sum(status=='typed' for _,_,status in rows),qpe_header_cases=64,dense_dimension=0,
                semantic_evidence_issued=False,binary_sha256=binary,harness_sha256=hashlib.sha256(source.encode()).hexdigest(),
                results=results,commands=commands,source_sha256={str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest()
                for path in [*sorted((ROOT/'lean-kernel/QleisliKernel/Hierarchical').glob('*.lean')),
                             ROOT/'scripts/test_hierarchical_artifact.py',ROOT/'scripts/test_hierarchical_typing.py',Path(__file__).resolve()]})
    if args.record:args.record.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in {'results','commands'}}))


if __name__=='__main__':main()
