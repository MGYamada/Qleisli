#!/usr/bin/env python3
"""Native complete outer Fourier request binding and independent complex action.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Finite H requests remain explicit; no production semantic seal is issued here.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

from probe_hierarchical_qft_cost import artifact as lean_artifact, array
from test_hierarchical_artifact import build_and_run
from test_hierarchical_fourier_base import fixtures, reconstruct
from test_hierarchical_gradient import PRELUDE as GRADIENT_PRELUDE
from test_hierarchical_qft import semantic_probes, text
from test_hierarchical_wiring import closure

PRELUDE = 'import QleisliKernel.Hierarchical.FourierRoot\n' + GRADIENT_PRELUDE + '''
def requested (n : Nat) (a : Artifact) : FourierRoot.Request :=
  match a.definitions[a.entry.implementation]? with
  | some d => ⟨n,d.interface⟩
  | none => ⟨n,⟨⟨#[],#[]⟩,⟨#[],#[]⟩⟩⟩
def rootStatus (a : Artifact) (r : FourierRoot.Request) (order : Array Nat) (remaining : Nat) : String :=
  match FourierRoot.inspect a r order remaining with
  | .ok p => s!"pending:{p.visits}:{p.body.requests.length}"
  | .error .limit => "limit"
  | .error .invalidIr => "invalid_ir"
  | .error .contract => "contract"
def rootReport (name : String) (a : Artifact) (r : FourierRoot.Request) (order : Array Nat) (remaining : Nat) : IO Unit :=
  IO.println s!"{name}|{rootStatus a r order remaining}"
def emitBound (name : String) (n : Nat) (r : Hadamard.Request) (expected : String) : IO Unit := do
  let some input := r.leaf.interface.inputs.quantum[0]? | throw <| IO.userError "missing input"
  let some output := r.leaf.interface.outputs.quantum[0]? | throw <| IO.userError "missing output"
  let bytes := String.intercalate "," (r.program.data.toList.map (fun b => toString b.toNat))
  IO.println s!"LEAF|{name}|{n}|{r.leafIndex}|{input.owner}|{output.owner}|{input.axes[0]!}|{output.axes[0]!}|{expected}|{bytes}"
def rootBaseline (n : Nat) (a : Artifact) (order : Array Nat) : IO Unit := do
  let checked ← match Conditional.checkAll a (Array.range (totalNodes a)) with
    | .error e => throw <| IO.userError s!"typing {n}: {repr e}"
    | .ok p => pure p
  let r := requested n a
  let remaining := 2000000-checked.state.visits
  let p ← match FourierRoot.inspect a r order remaining with
    | .error e => throw <| IO.userError s!"root {n}: {repr e}"
    | .ok p => pure p
  rootReport s!"baseline-{n}" a r order remaining
  rootReport s!"exact-{n}" a r order p.visits
  rootReport s!"short-{n}" a r order (p.visits-1)
  rootReport s!"renamed-{n}" (renamed a) (requested n (renamed a)) order remaining
  rootReport s!"stale-interface-{n}" (renamed a) r order remaining
  IO.println s!"budget-{n}|{checked.state.visits}|{checked.state.visits+p.visits}"
  for (h,i) in p.body.requests.zipIdx do
    emitBound s!"h-{n}-{i}" n h "ok"
def changedLeaf (name : String) (a : Artifact) (order : Array Nat) (index : Nat) (expected : String) : IO Unit := do
  let p ← match FourierRoot.inspect a (requested 8 a) order 2000000 with
    | .error e => throw <| IO.userError s!"changed finite leaf {name}: {repr e}"
    | .ok p => pure p
  let some h := p.body.requests.find? (fun h => h.leafIndex == index)
    | throw <| IO.userError "missing actual finite obligation"
  emitBound name 8 h expected
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    parser.add_argument('--save-source', type=Path)
    args = parser.parse_args()
    cases, _ = fixtures()
    schedules = {}
    source = PRELUDE
    for width, (a, _, _, _, _) in cases.items():
        children = a['definitions'][a['entry']['implementation']]['body']['children']
        schedules[width] = closure(a, [children[0], *children[2:]])
        source += f'def qft{width} : Artifact := {lean_artifact(a)}\n'
    a, gradients, stages, hs, _ = cases[8]
    root = a['entry']['implementation']
    children = a['definitions'][root]['body']['children']
    enter, body, leave, *swaps = children
    control = a['definitions'][body]['body']['children'][2]
    provider = a['definitions'][control]['body']['definition']
    phase = next(i for i, d in enumerate(a['definitions']) if d['body']['tag'] == 'dyadic_phase')
    phase_body = a['definitions'][phase]['body']
    order = schedules[8]
    leaf = a['definitions'][hs[-1]]['body']['children'][0]
    faults = {
        'missing-reversal': f'changed qft8 {root} (fun d => {{d with body := .sequence {array(children[:3])}}})',
        'missing-swap': f'changed qft8 {root} (fun d => {{d with body := .sequence {array(children[:-1])}}})',
        'duplicate-swap': f'changed qft8 {root} (fun d => {{d with body := .sequence {array([*children, swaps[-1]])}}})',
        'nonidentity-enter': f'changed qft8 {enter} (fun d => {{d with body := .rewire ⟨#[0],#[1,0,2,3,4,5,6,7],#[]⟩}})',
        'duplicate-axis': f'changed qft8 {enter} (fun d => {{d with body := .rewire ⟨#[0],#[0,0,2,3,4,5,6,7],#[]⟩}})',
        'missing-enter': f'changed qft8 {root} (fun d => {{d with body := .sequence {array(children[1:])}}})',
        'wrong-body-width': f'changed qft8 {root} (fun d => {{d with body := .sequence {array([enter, stages[-2], *children[2:]])}}})',
        'wrong-effect': f'changed qft8 {root} (fun d => {{d with effect := .observe}})',
        'wrong-control': f'changed qft8 {control} (fun d => {{d with body := .control {provider} false}})',
        'wrong-phase': f'changed qft8 {phase} (fun d => {{d with body := .dyadicPhase {phase_body["target"]} 2 {phase_body["k"]}}})',
        'wrong-input-shape': f'changed qft8 {root} (fun d => {{d with interface := {{d.interface with inputs := {{d.interface.inputs with quantum := d.interface.inputs.quantum.map fun p => {{p with basis := #[.bit]}}}}}}}})',
    }
    source += 'def main : IO Unit := do\n'
    for n in cases:
        source += f'  rootBaseline {n} qft{n} {array(schedules[n])}\n'
    for name, fault in faults.items():
        source += f'  rootReport {json.dumps(name)} ({fault}) (requested 8 qft8) {array(order)} 2000000\n'
    # All required outer roots must be inspected; a partial cache is not enough.
    for name, schedule in {
        'missing-enter-cache': [i for i in order if i != enter],
        'missing-leave-cache': [i for i in order if i != leave],
        'missing-swap-cache': [i for i in order if i != swaps[-1]],
        'empty-cache': [], 'reversed-order': list(reversed(order)),
    }.items():
        source += f'  rootReport "{name}" qft8 (requested 8 qft8) {array(schedule)} 2000000\n'
    source += f'''  rootReport "different-width" qft8 (requested 7 qft8) {array(order)} 2000000
  rootReport "zero-width" qft8 (requested 0 qft8) {array(order)} 2000000
  rootReport "oversized-width" qft8 (requested 9 qft8) {array(order)} 2000000
  rootReport "zero-budget" qft8 (requested 8 qft8) {array(order)} 0
  rootReport "reset-budget" qft8 (requested 8 qft8) {array(order)} 2000001
  rootReport "oversized-root" (changed qft8 {root} (fun d => {{d with body := .sequence (Array.replicate 1000000 0)}})) (requested 8 qft8) {array(order)} 2000000
  rootReport "different-interface" qft8 (requested 8 (renamed qft8)) {array(order)} 2000000
  rootReport "commuting-swaps" (changed qft8 {root} (fun d => {{d with body := .sequence {array([enter, body, leave, *reversed(swaps)])}}})) (requested 8 qft8) {array(order)} 2000000
  rootReport "missing-definition" {{qft8 with entry := ⟨999999,0⟩}} (requested 8 qft8) {array(order)} 2000000
  rootReport "duplicate-order" qft8 (requested 8 qft8) {array([*order, order[0]])} 2000000
'''
    program = json.loads(a['definitions'][leaf]['body']['program'])
    wrong_x = copy.deepcopy(program)
    wrong_x['programs'][0]['operations'][0]['gate'] = 'x'
    negative = copy.deepcopy(program)
    raw = negative['programs'][0]
    tokens = [raw['quantum_inputs'][0]['token'], 1000, 1001, 1002, 1003, raw['quantum_outputs'][0]]
    raw['operations'] = [dict(tag='gate', gate=gate, input=tokens[i], output=tokens[i+1])
                         for i, gate in enumerate(['h', 'x', 'z', 'x', 'z'])]
    for name, payload, expected in [('wrong-x', text(wrong_x), 'contract'), ('negative-h', text(negative), 'contract'), ('empty-h', '', 'limit')]:
        source += f'  changedLeaf "{name}" (changed qft8 {leaf} (fun d => {{d with body := .leaf ({json.dumps(payload)}).toUTF8}})) {array(order)} {leaf} "{expected}"\n'
    source += f'  changedLeaf "stale-renamed-h" (renamed qft8) {array(order)} {leaf} "contract"\n'
    if args.save_source:
        args.save_source.write_text(source)
    commands, binary = build_and_run(source, args.record)
    lines = [line.split('|') for line in commands[-1]['stdout'].splitlines()]
    rows = {f[0]: f[1:] for f in lines if f[0] != 'LEAF'}
    leaf_rows = [f[1:] for f in lines if f[0] == 'LEAF']
    if args.record:
        args.record.write_text(json.dumps(dict(status='observed-not-yet-compared', results=rows, commands=commands), indent=2)+'\n')
    for n in cases:
        expected = rows[f'baseline-{n}']
        assert expected[0].startswith('pending:') and expected[0].endswith(f':{n}')
        assert rows[f'exact-{n}'] == rows[f'renamed-{n}'] == expected
        assert rows[f'short-{n}'] == ['limit']
        assert rows[f'stale-interface-{n}'] == ['contract']
        before, after = map(int, rows[f'budget-{n}'])
        assert before < after <= 2000000
    for name in [*faults, 'missing-enter-cache', 'missing-leave-cache', 'missing-swap-cache', 'empty-cache',
                 'reversed-order', 'different-width', 'different-interface']:
        assert rows[name] == ['contract'], (name, rows[name])
    for name in ['zero-width', 'oversized-width', 'zero-budget', 'reset-budget', 'oversized-root']:
        assert rows[name] == ['limit'], (name, rows[name])
    assert rows['commuting-swaps'] == rows['baseline-8']
    assert rows['missing-definition'] == rows['duplicate-order'] == ['invalid_ir']
    assert len(leaf_rows) == 40
    semantics = semantic_probes({n: c[0] for n, c in cases.items()})
    result = reconstruct(cases, leaf_rows, commands)
    report = dict(format='qleisli.fourier-root-binding', version=1,
                  status='passed' if result.returncode == 0 else 'failed',
                  native_cases=len(rows), finite_requests=len(leaf_rows), results=rows,
                  semantic_probes=semantics, source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                  binary_sha256=binary, commands=commands, semantic_evidence_issued=False,
                  scope='Actual whole Fourier entry at widths 1–8, independently requested full interface/width, computed identity/reversal routing, complete complex amplitudes and returned exact-H obligations under one remaining budget. Production request transport/seals and correspondence gates remain open.')
    if args.record:
        args.record.write_text(json.dumps(report, indent=2)+'\n')
    if result.returncode:
        print(result.stdout+result.stderr)
        raise SystemExit(result.returncode)
    print(text({k: v for k, v in report.items() if k not in ('commands', 'results', 'semantic_probes')}))


if __name__ == '__main__':
    main()
