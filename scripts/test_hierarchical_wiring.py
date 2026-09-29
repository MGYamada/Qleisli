#!/usr/bin/env python3
"""Native actual-wiring inspection, shared budgets and independent basis action.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
A route summary is conditional on complete artifact typing, not a Fourier seal.
"""
import argparse
import hashlib
import json
from pathlib import Path

from probe_hierarchical_qft_cost import artifact as lean_artifact, array
from test_hierarchical_artifact import build_and_run
from test_hierarchical_gradient import PRELUDE as GRADIENT_PRELUDE
from test_hierarchical_qft import SharedGradientCircuit, execute, text

PRELUDE = '''import QleisliKernel.Hierarchical.Wiring
import QleisliKernel.Hierarchical.FourierBody
''' + GRADIENT_PRELUDE + '''
def wiringStatus (a : Artifact) (order : Array Nat) (remaining : Nat) : String :=
  match Wiring.inspect a order remaining with
  | .ok p => s!"ok:{p.visits}"
  | .error .limit => "limit"
  | .error .invalidIr => "invalid_ir"
  | .error .contract => "contract"
def wiringReport (name : String) (a : Artifact) (order : Array Nat) (remaining : Nat) : IO Unit :=
  IO.println s!"{name}|{wiringStatus a order remaining}"
def wiringBaseline (width body : Nat) (a : Artifact) (order roots : Array Nat) : IO Unit := do
  let checked ← match Conditional.checkAll a (Array.range (totalNodes a)) with
    | .error e => throw <| IO.userError s!"typing {width}: {repr e}"
    | .ok p => pure p
  let recursive ← match FourierBody.inspect a width width body (2000000-checked.state.visits) with
    | .error e => throw <| IO.userError s!"body {width}: {repr e}"
    | .ok p => pure p
  let remaining := 2000000-checked.state.visits-recursive.visits
  let inspected ← match Wiring.inspect a order remaining with
    | .error e => throw <| IO.userError s!"wiring {width}: {repr e}"
    | .ok p => pure p
  wiringReport s!"baseline-{width}" a order remaining
  wiringReport s!"renamed-{width}" (renamed a) order remaining
  wiringReport s!"exact-{width}" a order inspected.visits
  wiringReport s!"short-{width}" a order (inspected.visits-1)
  IO.println s!"budget-{width}|{checked.state.visits+recursive.visits}|{checked.state.visits+recursive.visits+inspected.visits}"
  for root in roots do
    let some axes := (inspected.cache[root]?).bind id | throw <| IO.userError "missing inspected root"
    IO.println s!"route-{width}-{root}|{repr axes}"
def nodeTypingReport (name : String) (a : Artifact) (index : Nat) : IO Unit :=
  let result := (a.definitions[index]?).map (NodeTyping.conditions a)
  IO.println s!"{name}|{repr result}"
def emptyWiring : Artifact :=
  let s : Side := ⟨#[⟨0,#[.bits 0],#[]⟩],#[]⟩
  ⟨#[⟨⟨s,s⟩,.unitary,.rewire ⟨#[0],#[],#[]⟩⟩],#[],#[],#[],⟨0,0⟩⟩
'''


def closure(artifact, roots):
    seen = set()
    order = []
    def visit(index):
        if index in seen:
            return
        body = artifact['definitions'][index]['body']
        assert body['tag'] in ('rewire', 'structural', 'tensor', 'sequence')
        children = (body['children'] if body['tag'] == 'sequence' else
                    [body['left'], body['right']] if body['tag'] == 'tensor' else [])
        for child in children:
            visit(child)
        seen.add(index)
        order.append(index)
    for root in roots:
        visit(root)
    return order


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    parser.add_argument('--save-source', type=Path)
    args = parser.parse_args()
    cases = {}
    source = PRELUDE
    for width in range(1, 9):
        artifact = SharedGradientCircuit().qft(width)
        children = artifact['definitions'][artifact['entry']['implementation']]['body']['children']
        roots = [children[0], *children[2:]]
        order = closure(artifact, roots)
        cases[width] = (artifact, children[1], roots, order)
        source += f'def qft{width} : Artifact := {lean_artifact(artifact)}\n'
    a, body, roots, order = cases[8]
    rename = roots[0]
    faults = {
        'hidden-phase': f'changed qft8 {rename} (fun d => {{d with body := .dyadicPhase 0 0 1}})',
        'hidden-leaf': f'changed qft8 {rename} (fun d => {{d with body := .leaf ByteArray.empty}})',
        'hidden-repeat': f'changed qft8 {rename} (fun d => {{d with body := .repeatOp 0 {body}}})',
        'axis-outside': f'changed qft8 {rename} (fun d => {{d with body := .rewire ⟨#[0],#[0,1,2,3,4,5,6,8],#[]⟩}})',
        'axis-missing': f'changed qft8 {rename} (fun d => {{d with body := .rewire ⟨#[0],#[0,1,2,3,4,5,6],#[]⟩}})',
        'wrong-effect': f'changed qft8 {rename} (fun d => {{d with effect := .observe}})',
        'mismatched-width': f'changed qft8 {rename} (fun d => {{d with interface := {{d.interface with outputs := ⟨#[],#[]⟩}}}})',
        'self-cycle': f'changed qft8 {rename} (fun d => {{d with body := .sequence #[{rename}]}})',
    }
    source += 'def main : IO Unit := do\n'
    for width, (_, recursive, selected, schedule) in cases.items():
        source += f'  wiringBaseline {width} {recursive} qft{width} {array(schedule)} {array(selected)}\n'
    for name, fault in faults.items():
        source += f'  wiringReport {json.dumps(name)} ({fault}) {array(order)} 2000000\n'
    tensor = next(a['definitions'][i]['body'] for i in order
                  if a['definitions'][i]['body']['tag'] == 'tensor')
    missing = tensor['left']
    schedules = {'missing-dependency': [i for i in order if i != missing], 'reversed-order': list(reversed(order)),
                 'duplicate-node': [*order, order[0]], 'missing-definition': [999999],
                 'unsupported-body': [body]}
    for name, schedule in schedules.items():
        source += f'  wiringReport {json.dumps(name)} qft8 {array(schedule)} 2000000\n'
    source += f'''  wiringReport "duplicate-axis-summary" (changed qft8 {rename} (fun d => {{d with body := .rewire ⟨#[0],#[0,0,2,3,4,5,6,7],#[]⟩}})) {array(order)} 2000000
  nodeTypingReport "duplicate-axis-typing" (changed qft8 {rename} (fun d => {{d with body := .rewire ⟨#[0],#[0,0,2,3,4,5,6,7],#[]⟩}})) {rename}
  wiringReport "lost-empty-owner-summary" (changed emptyWiring 0 (fun d => {{d with interface := {{d.interface with outputs := ⟨#[],#[]⟩}}}})) #[0] 2000000
  nodeTypingReport "lost-empty-owner-typing" (changed emptyWiring 0 (fun d => {{d with interface := {{d.interface with outputs := ⟨#[],#[]⟩}}}})) 0
  wiringReport "oversized-body" (changed qft8 {rename} (fun d => {{d with body := .sequence (Array.replicate 1000000 0)}})) {array(order)} 2000000
  wiringReport "empty-owner" emptyWiring #[0] 2000000
  wiringReport "zero-budget" qft8 {array(order)} 0
  wiringReport "reset-budget" qft8 {array(order)} 2000001
'''
    if args.save_source:
        args.save_source.write_text(source)
    commands, binary = build_and_run(source, args.record)
    rows = dict((r[0],r[1:]) for r in (line.split('|') for line in commands[-1]['stdout'].splitlines()))
    if args.record:
        args.record.write_text(json.dumps(dict(status='observed-not-yet-compared',results=rows,
            commands=commands),indent=2)+'\n')
    vectors = 0
    for width, (artifact, _, selected, _) in cases.items():
        expected = rows[f'baseline-{width}']
        assert expected[0].startswith('ok:')
        assert rows[f'renamed-{width}'] == rows[f'exact-{width}'] == expected
        assert rows[f'short-{width}'] == ['limit']
        before, after = map(int, rows[f'budget-{width}'])
        assert before < after <= 2000000
        size = 1 << width
        for position, root in enumerate(selected):
            axes = json.loads(rows[f'route-{width}-{root}'][0])
            expected_axes = list(range(width))
            if position >= 2:
                low, high = position-2, width-1-(position-2)
                expected_axes[low], expected_axes[high] = expected_axes[high], expected_axes[low]
            assert axes == expected_axes, (width, root, axes, expected_axes)
            for input_index in range(size):
                vector = [complex(i == input_index) for i in range(size)]
                output = execute(artifact, root, vector)
                routed = sum(((input_index >> axis) & 1) << i for i, axis in enumerate(axes))
                assert output == [complex(i == routed) for i in range(size)]
                vectors += 1
        # The suffix after the recursive body is exactly bit reversal, including
        # its actual owner rename. Check complete complex amplitudes, not probabilities.
        vector = [complex(i+1, size-i)/(size+1) for i in range(size)]
        actual = vector
        for root in selected[1:]:
            actual = execute(artifact, root, actual)
        target = [vector[int(f'{i:0{width}b}'[::-1], 2)] for i in range(size)]
        assert actual == target
        vectors += 1
    for name in [*faults, 'missing-dependency','reversed-order','unsupported-body']:
        assert rows[name] == ['contract'], (name, rows[name])
    for name in ['duplicate-node','missing-definition']:
        assert rows[name] == ['invalid_ir'], (name, rows[name])
    for name in ['zero-budget','reset-budget','oversized-body']:
        assert rows[name] == ['limit']
    for name in ['empty-owner','duplicate-axis-summary','lost-empty-owner-summary']:
        assert rows[name][0].startswith('ok:')
    for name in ['duplicate-axis-typing','lost-empty-owner-typing']:
        assert rows[name] == ['some false']

    report = dict(format='qleisli.hierarchical-wiring',version=1,status='passed',
                  native_cases=len(rows),basis_and_complex_vectors=vectors,results=rows,
                  source_sha256=hashlib.sha256(source.encode()).hexdigest(),binary_sha256=binary,
                  commands=commands,semantic_evidence_issued=False,
                  scope='Actual outer QFT renames and lifted SWAPs at widths 1–8; fresh routing cache, full-artifact/body/wiring aggregate budget and phase-sensitive diagnostic action. Complete outer Fourier/root composition remains separate.')
    if args.record:
        args.record.write_text(json.dumps(report,indent=2)+'\n')
    print(text({k:v for k,v in report.items() if k not in ('commands','results')}))


if __name__ == '__main__':
    main()
