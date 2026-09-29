#!/usr/bin/env python3
"""Bind coherent powers to actual artifact bodies and pending provider equations.

This is not semantic acceptance: a projected provider equation must subsequently
be independently checked. No external schema is enabled by these tests.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import hashlib
import json
from pathlib import Path
from test_hierarchical_contract_typing import PRELUDE
from test_hierarchical_artifact import ROOT, build_and_run

PRELUDE = PRELUDE.replace('import QleisliKernel.Hierarchical.ContractTyping',
                         'import QleisliKernel.Hierarchical.Power') + r'''
def powerArtifact (s : Side) (count : Nat) : Artifact :=
  let full := NodeTyping.append (bside 500 1000) s
  let map : PortMap := ⟨Array.range s.quantum.size,Array.range (wires s).size,#[]⟩
  {definitions := #[⟨⟨s,s⟩,.unitary,.rewire map⟩,
                    ⟨⟨s,s⟩,.unitary,.repeatOp count 0⟩,
                    ⟨⟨full,full⟩,.unitary,.control 1 true⟩],
   meanings := #[pureM s .identity,pureM s (.power 0 count),pureM full (.control 1 true)],
   encodings := #[identityE s,identityE full],
   proofs := #[proof,{proof with rule := .schema "controlled-power/1",premises := #[0],implementation := 2,meaning := 2,inputEncoding := 1,outputEncoding := 1,witness := ⟨1,#[0,0],#[]⟩}],entry := ⟨2,1⟩}
def zeroTarget : Side := ⟨#[⟨0,#[.bit],#[0]⟩,⟨1,#[.bits 0],#[]⟩],#[]⟩
def alterRoot (a : Artifact) (f : Proof → Proof) : Artifact :=
  {a with proofs := a.proofs.mapIdx (fun i p => if i==1 then f p else p)}
def alterPremise (a : Artifact) (f : Proof → Proof) : Artifact :=
  {a with proofs := a.proofs.mapIdx (fun i p => if i==0 then f p else p)}
def alterDefinition (a : Artifact) (index : Nat) (f : Definition → Definition) : Artifact :=
  {a with definitions := a.definitions.mapIdx (fun i d => if i==index then f d else d)}
def alterMeaning (a : Artifact) (index : Nat) (f : Meaning → Meaning) : Artifact :=
  {a with meanings := a.meanings.mapIdx (fun i m => if i==index then f m else m)}
def powerSample (n k : Nat) : Artifact :=
  alterRoot (powerArtifact (side n) (2^k)) fun p => {p with witness := ⟨1,#[k,0],#[]⟩}
def permutedPower (k : Nat) : Artifact :=
  let s := side 2
  let full := NodeTyping.append (bside 500 1000) s
  {powerSample 2 k with
    definitions := #[⟨⟨s,s⟩,.unitary,.repeatOp (2^k) 2⟩,⟨⟨full,full⟩,.unitary,.control 0 true⟩,⟨⟨s,s⟩,.unitary,.rewire (identityMap 2)⟩]
    meanings := #[pureM full (.control 2 true),pureM s .identity,pureM s (.power 1 (2^k))]
    proofs := #[{proof with implementation := 2,meaning := 1},{proof with rule := .schema "controlled-power/1",premises := #[0],implementation := 1,meaning := 0,inputEncoding := 1,outputEncoding := 1,witness := ⟨1,#[k,2],#[]⟩}]
    entry := ⟨1,1⟩}
def projectText (p : Power.Pending) : String :=
  s!"{p.actual.control}|{p.actual.targetDefinition}|{p.actual.count}|{p.actual.whenOne}|{p.logical.provider}|{p.logical.count}|{p.logical.polarity}|{p.providerProofIndex}|{p.providerProof.implementation}|{p.providerProof.meaning}"
def reportPower (name : String) (a : Artifact) (k provider budget : Nat) : IO Unit :=
  match Power.inspect a a.entry.proof k provider budget with
  | .error e => IO.println s!"{name}|{code ⟨e,none⟩}"
  | .ok p => IO.println s!"{name}|pending|{p.visits}|{projectText p}"
def reportPowerEntry (name : String) (a : Artifact) (order : Array Nat) (k provider : Nat) : IO Unit :=
  match Power.inspectEntry a order k provider with
  | .error e => IO.println s!"{name}|{code e}"
  | .ok p => IO.println s!"{name}|pending|{p.totalVisits}|{projectText p.pending}"
def wrongZeroBody : Artifact :=
  alterDefinition (powerArtifact (side 1) 0) 0 (fun d => {d with body := .dyadicPhase 0 1 3})
def widePower : Artifact := powerArtifact ⟨Array.replicate 100000 ⟨0,#[.bits 0],#[]⟩,#[]⟩ 1
'''


def cases():
    rows = []

    def add(name, artifact='powerSample 1 0', status='pending', k=0, provider=0,
            budget=2000000, whole=False, order='Array.range 10', stage=None):
        call = (f'reportPowerEntry {json.dumps(name)} ({artifact}) ({order}) {k} {provider}' if whole
                else f'reportPower {json.dumps(name)} ({artifact}) {k} {provider} {budget}')
        if status == 'pending' and stage is None:
            stage = ['0', str(provider), str(2**k), 'true', '0', str(2**k), 'true', '0', str(provider), '0']
        rows.append((name, call, status, stage))

    for n in range(1, 9):
        for k in range(13):
            add(f'whole-{n}-{k}', f'powerSample {n} {k}', k=k, whole=True)
    for k in [0, 12]:
        add(f'local-{k}', f'powerSample 8 {k}', k=k)
    for k in range(13):
        add(f'permuted-{k}', f'permutedPower {k}', k=k, provider=2, whole=True,
            order='#[2,0,1,4,5,3,6,7,8,9]',
            stage=['0','2',str(2**k),'true','1',str(2**k),'true','0','2','1'])
    for name, side in [('empty-bits', 'side 0'), ('unit', '⟨#[⟨0,#[.unit],#[]⟩],#[]⟩'),
                       ('zero-owner', 'zeroTarget'),
                       ('flat', 'tupleSide flat'), ('nested', 'tupleSide nested')]:
        add(f'whole-{name}', f'powerArtifact ({side}) 1', whole=True)
    # These are honest *pending* obligations, including well-typed but false semantics.
    add('opaque-provider-needs-reconstruction',
        'alterDefinition (powerSample 1 0) 0 (fun d => {d with body := .leaf (bytes 1)})', whole=True)
    add('wrong-provider-meaning-needs-derivation',
        'alterMeaning (powerArtifact (bside 0 0) 1) 0 (fun m => {m with body := .phase 1 3})', whole=True)
    mutations = [
        ('physical-count', 'alterDefinition (powerSample 1 0) 1 (fun d => {d with body := .repeatOp 2 0})'),
        ('logical-count', 'alterMeaning (powerSample 1 0) 1 (fun m => {m with body := .power 0 2})'),
        ('both-counts', 'powerArtifact (side 1) 2'),
        ('zero-count', 'powerArtifact (side 1) 0'),
        ('physical-polarity', 'alterDefinition (powerSample 1 0) 2 (fun d => {d with body := .control 1 false})'),
        ('logical-polarity', 'alterMeaning (powerSample 1 0) 2 (fun m => {m with body := .control 1 false})'),
        ('both-polarities', 'alterMeaning (alterDefinition (powerSample 1 0) 2 (fun d => {d with body := .control 1 false})) 2 (fun m => {m with body := .control 1 false})'),
        ('physical-provider', 'alterDefinition (powerSample 1 0) 1 (fun d => {d with body := .repeatOp 1 1})'),
        ('logical-provider', 'alterMeaning (powerSample 1 0) 1 (fun m => {m with body := .power 1 1})'),
        ('premise-implementation', 'alterPremise (powerSample 1 0) (fun p => {p with implementation := 1})'),
        ('premise-meaning', 'alterPremise (powerSample 1 0) (fun p => {p with meaning := 1})'),
        ('premise-encoding', 'alterPremise (powerSample 1 0) (fun p => {p with inputEncoding := 1})'),
        ('missing-premise', 'alterRoot (powerSample 1 0) (fun p => {p with premises := #[]})'),
        ('extra-premise', 'alterRoot (powerSample 1 0) (fun p => {p with premises := #[0,0]})'),
        ('self-premise', 'alterRoot (powerSample 1 0) (fun p => {p with premises := #[1]})'),
        ('missing-premise-reference', 'alterRoot (powerSample 1 0) (fun p => {p with premises := #[2]})'),
        ('extra-witness-reference', 'alterRoot (powerSample 1 0) (fun p => {p with witness := ⟨1,#[0,0],#[⟨.definition,0⟩]⟩})'),
        ('extra-parameter', 'alterRoot (powerSample 1 0) (fun p => {p with witness := ⟨1,#[0,0,0],#[]⟩})'),
        ('missing-parameter', 'alterRoot (powerSample 1 0) (fun p => {p with witness := ⟨1,#[0],#[]⟩})'),
        ('wrong-version', 'alterRoot (powerSample 1 0) (fun p => {p with witness := ⟨2,#[0,0],#[]⟩})'),
        ('wrong-schema', 'alterRoot (powerSample 1 0) (fun p => {p with rule := .schema "qft-dyadic8/1"})'),
        ('declaration-is-not-schema', 'alterRoot (powerSample 1 0) (fun p => {p with rule := .schema "Qleisli.Schema.power_coherent_sound"})'),
        ('ordinary-rule', 'alterRoot (powerSample 1 0) (fun p => {p with rule := .control})'),
        ('instrument-kind', 'alterRoot (powerSample 1 0) (fun p => {p with kind := .instrument})'),
        ('root-input-encoding', 'alterRoot (powerSample 1 0) (fun p => {p with inputEncoding := 0})'),
        ('root-output-encoding', 'alterRoot (powerSample 1 0) (fun p => {p with outputEncoding := 0})'),
        ('range-encoding-not-whole-space', 'changeEncoding (powerSample 1 0) (fun e => {e with body := .zeroScratch 0 0})'),
        ('not-repeat', 'alterDefinition (powerSample 1 0) 1 (fun d => {d with body := .inverse 0})'),
        ('not-control', 'alterDefinition (powerSample 1 0) 2 (fun d => {d with body := .sequence #[1]})'),
        ('not-logical-power', 'alterMeaning (powerSample 1 0) 1 (fun m => {m with body := .inverse 0})'),
        ('wrong-axis-header', 'alterDefinition (powerSample 1 0) 1 (fun d => {d with interface := ⟨bside 0 9,bside 0 9⟩})'),
        ('same-width-different-type', 'alterDefinition (powerSample 1 0) 1 (fun d => {d with interface := ⟨bside 0 0,bside 0 0⟩})'),
        ('lost-zero-owner', 'alterDefinition (powerArtifact zeroTarget 1) 1 (fun d => {d with interface := ⟨bside 0 0,bside 0 0⟩})'),
        ('flattened-nested-type', 'alterDefinition (powerArtifact (tupleSide nested) 1) 1 (fun d => {d with interface := ⟨tupleSide flat,tupleSide flat⟩})'),
    ]
    for name, artifact in mutations:
        add(name, artifact, 'contract')
    add('wrong-independent-provider', status='contract', provider=1)
    add('wrong-independent-exponent', status='contract', k=1)
    add('outside-exponent', status='limit', k=13)
    add('outside-provider', status='limit', provider=4294967296)
    add('outside-budget', status='limit', budget=2000001)
    add('empty-budget', status='limit', budget=0)
    add('huge-header', 'widePower', 'limit')
    add('huge-witness', 'alterRoot (powerSample 1 0) (fun p => {p with witness := ⟨1,Array.replicate 2000000 0,#[]⟩})', 'limit')
    # Independent arithmetic for the published local charge: 12 header refs,
    # eight full-control sides and sixteen target sides, including the premise.
    header_scan = 12 + 8*2 + 16
    full_side = 1 + 4*2**2 + 2*(4+4)
    target_side = 1 + 4 + 4 + 4
    boundary = 64+4+1+header_scan + 32*(1+12+8*full_side+16*target_side)
    assert boundary == 15633
    add('exact-remaining-budget', budget=boundary)
    add('one-under-remaining-budget', status='limit', budget=boundary-1)
    # The local fixed-shape pass has no permission to skip the whole graph pass.
    add('whole-zero-invalid-provider', 'wrongZeroBody', 'invalid_ir', whole=True)
    add('whole-cycle', 'alterDefinition (powerSample 1 0) 0 (fun d => {d with body := .repeatOp 0 0})', 'invalid_ir', whole=True)
    add('whole-wrong-entry', '{powerSample 1 0 with entry := ⟨1,1⟩}', 'contract', whole=True)
    add('whole-duplicate-order', status='invalid_ir', whole=True, order='#[0,1,2,3,4,5,6,7,8,8]')
    add('whole-wrong-order', status='invalid_ir', whole=True, order='(Array.range 10).reverse')
    # Types and endpoints still pass for these semantic schema mutations.
    for name, artifact in mutations[:7]:
        rows.append(('typed-'+name, f'reportComplete "typed-{name}" ({artifact}) (Array.range 10)', 'typed', None))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    rows = cases()
    source = PRELUDE + '\n' + '\n'.join(f'def case{i} : IO Unit := {call}' for i, (_, call, _, _) in enumerate(rows)) + '\n'
    groups = list(range(0, len(rows), 16))
    for first in groups:
        source += f'def group{first} : IO Unit := do\n' + '\n'.join(f'  case{i}' for i in range(first, min(first+16, len(rows)))) + '\n'
    source += 'def main : IO Unit := do\n' + '\n'.join(f'  group{i}' for i in groups) + '\n'
    commands, binary = build_and_run(source, args.record)
    results = {}
    for line in commands[-1]['stdout'].splitlines():
        name, *fields = line.split('|')
        assert name not in results
        results[name] = fields
    if args.record:
        args.record.write_text(json.dumps(dict(status='observed-not-yet-compared', results=results, commands=commands), indent=2)+'\n')
    assert len(results) == len(rows)
    for name, _, status, stage in rows:
        assert results[name][0] == status, (name, results[name], status)
        if stage is not None:
            assert results[name][2:] == stage, (name, results[name], stage)
            assert 0 < int(results[name][1]) <= 2000000
    # Verification work depends on the shared graph, not the number of repetitions.
    assert results['local-0'][1] == results['local-12'][1]
    for n in range(1, 9):
        assert len({results[f'whole-{n}-{k}'][1] for k in range(13)}) == 1
    report = dict(format='qleisli.hierarchical-power-validation', version=1, status='passed',
                  cases=len(rows), pending=sum(s=='pending' for _, _, s, _ in rows),
                  typed_counterexamples=7, maximum_dense_dimension=0, repeated_bodies_expanded=0,
                  semantic_evidence_issued=False, external_schema_enabled=False,
                  binary_sha256=binary, harness_sha256=hashlib.sha256(source.encode()).hexdigest(),
                  results=results, commands=commands,
                  source_sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in [*sorted((ROOT/'lean-kernel/QleisliKernel/Hierarchical').glob('*.lean')),
                                ROOT/'lean-kernel/QleisliKernel/Schema.lean',
                                ROOT/'scripts/test_hierarchical_artifact.py',
                                ROOT/'scripts/test_hierarchical_typing.py',
                                ROOT/'scripts/test_hierarchical_contract_typing.py', Path(__file__).resolve()]})
    if args.record:
        args.record.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: v for k, v in report.items() if k not in {'results', 'commands'}}))


if __name__ == '__main__':
    main()
