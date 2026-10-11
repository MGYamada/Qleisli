#!/usr/bin/env python3
"""Native actual-byte finite requests; pending is not semantic acceptance.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import hashlib
import json
from pathlib import Path
import random

from test_hierarchical_artifact import ROOT, build_and_run

PRELUDE = r'''import QleisliKernel.Hierarchical.Finite
open QleisliKernel.Hierarchical
open Artifact
def sample (input output : QuantumPort) (program description : String) : Artifact :=
  let i : Side := ⟨#[input],#[]⟩
  let o : Side := ⟨#[output],#[]⟩
  {definitions := #[⟨⟨i,o⟩,.unitary,.leaf program.toUTF8⟩]
   meanings := #[⟨⟨i,o⟩,.finite description.toUTF8⟩]
   encodings := #[⟨i,i,.identity⟩,⟨o,o,.identity⟩]
   proofs := #[⟨.equation,.finite,#[],0,0,0,1,⟨1,#[],#[]⟩⟩]
   entry := ⟨0,0⟩}
def changedProof (a : Artifact) (f : Proof → Proof) : Artifact :=
  {a with proofs := a.proofs.map f}
def changedDefinition (a : Artifact) (f : Definition → Definition) : Artifact :=
  {a with definitions := a.definitions.map f}
def changedMeaning (a : Artifact) (f : Meaning → Meaning) : Artifact :=
  {a with meanings := a.meanings.map f}
def changedEncoding (a : Artifact) (f : Encoding → Encoding) : Artifact :=
  {a with encodings := a.encodings.map f}
-- These local projection cases deliberately use unrelated unused placeholders.
-- A whole-artifact preparation pass must independently check reachability.
def reindexed (a : Artifact) : Artifact :=
  {a with definitions := #[⟨⟨⟨#[],#[]⟩,⟨#[],#[]⟩⟩,.observe,.init0 99⟩] ++ a.definitions
          meanings := #[⟨⟨⟨#[],#[]⟩,⟨#[],#[]⟩⟩,.identity⟩] ++ a.meanings
          encodings := a.encodings.reverse
          proofs := a.proofs ++ a.proofs.map (fun p =>
            {p with implementation := 1,meaning := 1,inputEncoding := 1,outputEncoding := 0})}
def code (error : Error) : String := match error with
  | .limit => "limit" | .invalidIr => "invalid_ir" | .contract => "contract"
def basisCodes (basis : Basis) : List Nat := basis.toList.map fun atom => match atom with
  | .unit => 0 | .bit => 1 | .tuple n => 2+n | .bits n => 100+n
def report (name : String) (a : Artifact) (index : Nat := 0) (budget : Nat := 2000000) : IO Unit := do
  match Finite.inspect a index budget with
  | .error e => IO.println s!"{name}|{code e}"
  | .ok p =>
    let r := p.request
    let some input := r.physical.interface.inputs.quantum[0]? | IO.println s!"{name}|missing-input"
    let some output := r.physical.interface.outputs.quantum[0]? | IO.println s!"{name}|missing-output"
    let semantic := match Rule.check a index budget with
      | .error e => code e | .ok _ => "accepted"
    IO.println s!"{name}|pending|{p.visits}|{r.index}|{r.proof.implementation}|{r.proof.meaning}|{r.proof.inputEncoding}|{r.proof.outputEncoding}|{input.owner}|{output.owner}|{input.axes.toList}|{output.axes.toList}|{basisCodes input.basis}|{basisCodes output.basis}|{r.program.data.toList}|{r.description.data.toList}|{semantic}"
def boundaries (a : Artifact) : IO Unit := do
  match Finite.inspect a 0 2000000 with
  | .error e => IO.println s!"boundary-start|{code e}"
  | .ok p =>
    report "budget-exact" a 0 p.visits
    report "budget-short" a 0 (p.visits-1)
    report "budget-zero" a 0 0
    report "budget-over" a 0 2000001
'''


def array(values):
    return '#[' + ','.join(map(str, values)) + ']'


def basis(width, units=False, nested=False):
    if not width:
        atoms = ['.unit']
        codes = [0]
    elif width == 1:
        atoms = ['.bit']
        codes = [1]
    elif nested:
        atoms = ['.tuple 2', '.bit'] * (width-1) + ['.bit']
        codes = [4, 1] * (width-1) + [1]
    else:
        atoms = [f'.tuple {width}'] + ['.bit'] * width
        codes = [width+2] + [1] * width
    if units:
        atoms = ['.tuple 2', '.unit'] + atoms
        codes = [4, 0] + codes
    return array(atoms), codes


def model(width, seed, units=False, nested=False):
    b, codes = basis(width, units, nested)
    rng = random.Random(seed)
    ia = [20+x for x in range(width)]
    oa = [70+x for x in range(width)]
    rng.shuffle(ia)
    rng.shuffle(oa)
    return dict(basis=b, codes=codes, ia=ia, oa=oa, io=7, oo=19,
                program=f'opaque-program-{width}-{seed}', description=f'independent-matrix-{width}-{seed}')


def render(m):
    return 'sample ' + ' '.join([
        f'⟨{m["io"]},{m["basis"]},{array(m["ia"])}⟩',
        f'⟨{m["oo"]},{m["basis"]},{array(m["oa"])}⟩',
        json.dumps(m['program']), json.dumps(m['description'])])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    rows = []
    def add(name, expression, status='contract', expected=None, index=0, budget=2000000):
        rows.append(dict(name=name, expression=expression, status=status, expected=expected,
                         index=index, budget=budget))
    for width in range(7):
        for seed in range(3):
            m = model(width, seed, units=seed == 1, nested=seed == 2)
            add(f'legacy-{width}-{seed}', render(m), 'pending', m)
    m = model(2, 0)
    base = render(m)
    add('reindexed', f'reindexed ({base})', 'pending', m, index=1)
    for key, value in [('program', 'phase-mutated-program'), ('description', 'wrong-independent-matrix'),
                       ('io', 1007), ('oo', 1019), ('ia', list(reversed(m['ia']))), ('oa', list(reversed(m['oa'])))]:
        mutation = dict(m, **{key: value})
        add(f'bound-{key}-mutation', render(mutation), 'pending', mutation)
    for key in ('program', 'description'):
        mutation = dict(m, **{key: ''})
        add(f'empty-{key}', render(mutation))
    for width in (7, 8):
        add(f'width-{width}', render(model(width, 0)))
    # Explicit atomic Bits now survive projection; opaque bodies still cannot
    # authorize acceptance. Retain their tags, including the zero-width atom.
    for width in (0, 1, 2, 6):
        atomic = dict(model(width, 0), basis=f'#[.bits {width}]', codes=[100+width])
        add(f'atomic-bits-{width}', render(atomic), 'pending', atomic)
    add('atomic-bits-7', render(dict(model(7, 0), basis='#[.bits 7]')))
    # Same bit width is insufficient: the actual meaning's tree must match.
    for width in (0, 1, 2):
        atomic = render(dict(model(width, 0), basis=f'#[.bits {width}]'))
        legacy_basis, _ = basis(width)
        add(f'bits-{width}-not-legacy-tree', f'changedMeaning ({atomic}) '
            '(fun d => {d with interface := {d.interface with inputs := '
            '{d.interface.inputs with quantum := d.interface.inputs.quantum.map '
            f'(fun p => {{p with basis := {legacy_basis}}})}}}}}})')
    add('duplicate-axis', render(dict(m, ia=[20, 20])))
    add('missing-axis', render(dict(m, oa=[70])))
    add('owner-overflow', render(dict(m, oo=4294967296)))
    add('bad-arity', render(dict(m, basis='#[.tuple 3,.bit,.bit]')))
    proof_mutations = {
        'wrong-rule': 'rule := .phase', 'premise': 'premises := #[0]',
        'template': 'witness := ⟨2,#[],#[]⟩', 'parameters': 'witness := ⟨1,#[0],#[]⟩',
        'witness-reference': 'witness := ⟨1,#[],#[⟨.definition,0⟩]⟩',
        'instrument-kind': 'kind := .instrument', 'missing-definition': 'implementation := 1',
        'missing-meaning': 'meaning := 1', 'missing-input-encoding': 'inputEncoding := 2',
        'missing-output-encoding': 'outputEncoding := 2', 'swapped-encodings': 'inputEncoding := 1,outputEncoding := 0',
    }
    for name, fields in proof_mutations.items():
        add(name, f'changedProof ({base}) (fun p => {{p with {fields}}})')
    add('missing-proof', base, 'invalid_ir', index=1)
    add('non-leaf', f'changedDefinition ({base}) (fun d => {{d with body := .inverse 0}})')
    add('non-finite-meaning', f'changedMeaning ({base}) (fun d => {{d with body := .identity}})')
    for effect in ('iso', 'observe'):
        add(effect, f'changedDefinition ({base}) (fun d => {{d with effect := .{effect}}})')
    add('nonidentity-encoding', f'changedEncoding ({base}) (fun e => {{e with body := .tensor 0 0}})')
    add('changed-encoding-owner', f'changedEncoding ({base}) (fun e => {{e with physical := '
        '{e.physical with quantum := e.physical.quantum.map (fun p => {p with owner := p.owner+1})}})')
    add('changed-meaning-output-order', f'changedMeaning ({base}) (fun d => {{d with interface := '
        '{d.interface with outputs := {d.interface.outputs with quantum := '
        'd.interface.outputs.quantum.map (fun p => {p with axes := p.axes.reverse})}}})')
    add('changed-meaning-type', f'changedMeaning ({base}) (fun d => {{d with interface := '
        '{d.interface with inputs := {d.interface.inputs with quantum := '
        'd.interface.inputs.quantum.map (fun p => {p with basis := #[.bits 2]})}}})')
    add('drop-unit-owner', f'changedDefinition ({render(model(0,0))}) (fun d => {{d with interface := '
        '{d.interface with outputs := ⟨#[],#[]⟩}})')
    add('extra-zero-owner', f'changedDefinition ({base}) (fun d => {{d with interface := '
        '{d.interface with inputs := {d.interface.inputs with quantum := '
        'd.interface.inputs.quantum.push ⟨99,#[.unit],#[]⟩}}})')
    add('classical-port', f'changedDefinition ({base}) (fun d => {{d with interface := '
        '{d.interface with inputs := {d.interface.inputs with classical := #[⟨3,#[.bit]⟩]}}})')
    add('oversized-header', f'changedDefinition ({base}) (fun d => {{d with interface := '
        '{d.interface with inputs := ⟨Array.replicate 100000 ⟨1,#[.unit],#[]⟩,#[]⟩}})', 'limit')
    add('payload-over-cap', f'changedDefinition ({base}) (fun d => {{d with body := '
        '.leaf ⟨Array.replicate 16777217 0⟩})', 'limit')
    calls = [f'report {json.dumps(r["name"])} ({r["expression"]}) {r["index"]} {r["budget"]}' for r in rows]
    calls.append(f'boundaries ({base})')
    source = PRELUDE + '\n'.join(f'def case{i} : IO Unit := {call}' for i, call in enumerate(calls)) + '\n'
    groups = list(range(0, len(calls), 12))
    for first in groups:
        source += f'def group{first} : IO Unit := do\n' + '\n'.join(
            f'  case{i}' for i in range(first, min(first+12, len(calls)))) + '\n'
    source += 'def main : IO Unit := do\n' + '\n'.join(f'  group{i}' for i in groups) + '\n'
    commands, binary_hash = build_and_run(source, args.record)
    results = {}
    for line in commands[-1]['stdout'].splitlines():
        name, *fields = line.split('|')
        assert name not in results, name
        results[name] = fields
    if args.record:
        args.record.write_text(json.dumps(dict(status='observed-not-yet-compared', results=results,
                                              commands=commands), indent=2)+'\n')
    assert len(results) == len(rows)+4, results
    probes = 0
    for row in rows:
        fields = results[row['name']]
        assert fields[0] == row['status'], (row['name'], fields, row['status'])
        if row['expected'] is None:
            continue
        m = row['expected']
        assert int(fields[1]) <= row['budget']
        expected_indices = [1, 1, 1, 1, 0] if row['name'] == 'reindexed' else [0, 0, 0, 0, 1]
        assert list(map(int, fields[2:7])) == expected_indices, (row['name'], fields)
        assert list(map(int, fields[7:9])) == [m['io'], m['oo']], (row['name'], fields)
        actual = [json.loads(field) for field in fields[9:15]]
        expected = [m['ia'], m['oa'], m['codes'], m['codes'],
                    list(m['program'].encode()), list(m['description'].encode())]
        assert actual == expected, (row['name'], actual, expected)
        assert fields[15] == 'contract', (row['name'], fields)
        probes += sum(map(len, expected)) + 7
    assert results['budget-exact'][0] == 'pending'
    assert results['budget-short'] == ['limit']
    assert results['budget-zero'] == ['limit']
    assert results['budget-over'] == ['limit']
    report = dict(format='qleisli.hierarchical-finite-binding-validation', version=1, status='passed',
                  cases=len(results), pending=sum(r[0] == 'pending' for r in results.values()),
                  field_and_byte_probes=probes, semantic_acceptances=0,
                  source_sha256=hashlib.sha256(source.encode()).hexdigest(), binary_sha256=binary_hash,
                  results=results, commands=commands)
    if args.record:
        args.record.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({key: value for key, value in report.items() if key not in ('results', 'commands')}, sort_keys=True))


if __name__ == '__main__':
    main()
