#!/usr/bin/env python3
"""Fresh composed checks: independent pure request, initialization and readout.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
The native pending result retains finite obligations and is not production API.
"""
import argparse
import json
from pathlib import Path

from test_hierarchical_artifact import build_and_run


PRELUDE = r'''import QleisliKernel.Hierarchical.Instrument
open QleisliKernel.Hierarchical
open Artifact

def target : QuantumPort := ⟨7,#[.bit],#[3]⟩
def fresh : QuantumPort := ⟨11,#[.bit],#[8]⟩
def before : Side := ⟨#[target],#[]⟩
def initialized : Side := ⟨#[target,fresh],#[]⟩
def freshSide : Side := ⟨#[fresh],#[]⟩
def output : Side := ⟨#[target],#[⟨200,#[.bits 1]⟩]⟩
def temporary : Side := ⟨#[target],#[⟨100,#[.bit]⟩]⟩
def init : Definition := ⟨⟨before,initialized⟩,.iso,.init0 11⟩
def measurement : Definition := ⟨⟨initialized,temporary⟩,.observe,.observeZ 11 100⟩
def identityMap : PortMap := ⟨#[0],#[0],#[]⟩
def meanings (phase : Nat) : Array Meaning := #[
  ⟨⟨before,before⟩,.phase phase 3⟩,
  ⟨⟨freshSide,freshSide⟩,.rewire identityMap⟩,
  ⟨⟨initialized,initialized⟩,.tensor 0 1⟩]
def equation (i : Nat) (rule : Rule) (premises : Array Nat) : Proof :=
  ⟨.equation,rule,premises,i,i,i,i,⟨1,#[],#[]⟩⟩
def graph (phase : Nat) : Artifact :=
  ⟨#[⟨⟨before,before⟩,.unitary,.dyadicPhase 7 phase 3⟩,
      ⟨⟨freshSide,freshSide⟩,.unitary,.rewire identityMap⟩,
      ⟨⟨initialized,initialized⟩,.unitary,.tensor 0 1⟩],
    meanings phase,
    #[⟨before,before,.identity⟩,⟨freshSide,freshSide,.identity⟩,
      ⟨initialized,initialized,.identity⟩],
    #[equation 0 .phase #[],equation 1 .rewire #[],equation 2 .tensor #[0,1]],⟨2,2⟩⟩
def request : Instrument.Request :=
  ⟨⟨before,#[fresh]⟩,⟨.equation,.unitary,⟨initialized,initialized⟩,meanings 1,2⟩,
    ⟨initialized,#[11],200⟩,output⟩
def packet : Instrument.Packet :=
  ⟨⟨#[init],initialized⟩,graph 1,Array.range 12,
    #[⟨2,2,#[1,2]⟩,⟨0,0,#[]⟩,⟨1,1,#[]⟩],#[1,2,0],
    ⟨#[measurement],#[100],output⟩⟩
def finiteGraph : Artifact :=
  let a := graph 1
  let d : Definition := ⟨⟨before,before⟩,.unitary,.leaf "untrusted finite program".toUTF8⟩
  let m : Meaning := ⟨⟨before,before⟩,.finite "untrusted matrix".toUTF8⟩
  { a with
    definitions := a.definitions.set! 0 d
    meanings := a.meanings.set! 0 m
    proofs := a.proofs.set! 0 (equation 0 .finite #[]) }
def finiteRequest : Instrument.Request :=
  let m : Meaning := ⟨⟨before,before⟩,.finite "independently required matrix".toUTF8⟩
  {request with circuit := {request.circuit with meanings := (meanings 1).set! 0 m}}
def report (name : String) (r : Instrument.Request) (p : Instrument.Packet) : IO Unit :=
  match Instrument.checkAll r p with
  | .error e => IO.println s!"{name}|{repr e.kind}"
  | .ok result => IO.println s!"{name}|pending|{result.visits}|{result.circuit.artifact.state.requests.size}|{result.circuit.binding.requests.length}"
'''


def cases():
    return [
        ('independent-request','request','packet','pending'),
        ('finite-obligations-remain','finiteRequest','{packet with artifact := finiteGraph}','pending-finite'),
        ('wrong-pure-phase','request','{packet with artifact := graph 3}','contract'),
        ('changed-root-request','{request with circuit := {request.circuit with meanings := meanings 3}}','packet','contract'),
        ('forged-initialization','request','{packet with preparation := {packet.preparation with initializations := #[]}}','contract'),
        ('init-changes-target','request','{packet with preparation := {packet.preparation with initializations := #[{init with body := .init0 7}]}}','contract'),
        ('wrong-preparation-boundary','request','{packet with preparation := {packet.preparation with outputs := before}}','contract'),
        ('wrong-readout-boundary','{request with readout := {request.readout with inputs := freshSide}}','packet','contract'),
        ('wrong-readout-owner','{request with readout := {request.readout with owners := #[7]}}','packet','contract'),
        ('lost-target','request','{packet with readout := {packet.readout with outputs := ⟨#[],output.classical⟩}}','contract'),
        ('wrong-pack','request','{packet with readout := {packet.readout with pack := #[101]}}','contract'),
        ('changed-public-result','{request with outputs := ⟨#[target],#[⟨201,#[.bits 1]⟩]⟩}','packet','contract'),
        ('forged-readout-effect','request','{packet with readout := {packet.readout with measurements := #[{measurement with effect := .unitary}]}}','contract'),
        ('oversized-boundary','{request with outputs := ⟨Array.replicate 100000 target,#[]⟩}','packet','limit'),
    ]


def test_composed_boundaries(output):
    expected = {name:status for name,_,_,status in cases()}
    seen = {}
    for line in output.splitlines():
        fields = line.split('|')
        name = fields[0]
        assert name in expected and name not in seen,line
        if fields[1] == 'pending':
            assert expected[name] in ('pending','pending-finite') and len(fields) == 5,line
            count = 1 if expected[name] == 'pending-finite' else 0
            assert 0 < int(fields[2]) <= 2000000 and fields[3:] == [str(count),str(count)],line
            seen[name] = dict(status='pending',work=int(fields[2]),finite_implementation_obligations=count,
                              finite_meaning_obligations=count)
        else:
            assert fields[1].rsplit('.',1)[-1] == expected[name],line
            seen[name] = dict(status=expected[name])
    assert seen.keys() == expected.keys()
    return seen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record',type=Path)
    args = parser.parse_args()
    source = PRELUDE+'\ndef main : IO Unit := do\n'+''.join(
        f'  report {json.dumps(name)} ({request}) ({packet})\n' for name,request,packet,_ in cases())
    commands,binary_hash = build_and_run(source,args.record)
    report = dict(format='qleisli.composed-instrument-validation',version=1,status='passed',
        cases=len(cases()),results=test_composed_boundaries(commands[-1]['stdout']),
        binary_sha256=binary_hash,commands=commands,production_integration=False,
        named_qpe_binding=False,source_preservation_proved=False)
    if args.record:
        args.record.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'commands'}))


if __name__ == '__main__':
    main()
