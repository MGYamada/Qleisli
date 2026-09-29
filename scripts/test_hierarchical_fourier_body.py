#!/usr/bin/env python3
"""Complete recursive Fourier-body inspection and bound exact-H obligations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Outer reversal/request integration and finite-reader correspondence remain explicit.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

from probe_hierarchical_qft_cost import artifact as lean_artifact, array
from test_hierarchical_artifact import build_and_run
from test_hierarchical_fourier_base import PRELUDE as BASE_PRELUDE, fixtures, reconstruct
from test_hierarchical_fourier_stage import probes
from test_hierarchical_qft import text

PRELUDE = 'import QleisliKernel.Hierarchical.FourierBody\n' + BASE_PRELUDE + '''
def bodyStatus (a : Artifact) (precision width index remaining : Nat) : String :=
  match FourierBody.inspect a precision width index remaining with
  | .ok p => s!"pending:{p.visits}:{p.requests.length}"
  | .error .limit => "limit"
  | .error _ => "contract"
def bodyReport (name : String) (a : Artifact) (precision width index remaining : Nat) : IO Unit :=
  IO.println s!"{name}|{bodyStatus a precision width index remaining}"
def emitRequest (name : String) (precision : Nat) (r : Hadamard.Request) : IO Unit := do
  let some input := r.leaf.interface.inputs.quantum[0]? | throw <| IO.userError "missing input"
  let some output := r.leaf.interface.outputs.quantum[0]? | throw <| IO.userError "missing output"
  let bytes := String.intercalate "," (r.program.data.toList.map (fun b => toString b.toNat))
  IO.println s!"LEAF|{name}|{precision}|{r.leafIndex}|{input.owner}|{output.owner}|{input.axes[0]!}|{output.axes[0]!}|ok|{bytes}"
def bodyBaseline (precision : Nat) (a : Artifact) (indices : Array Nat) : IO Unit := do
  let checked ← match Conditional.checkAll a (Array.range (totalNodes a)) with
    | .error e => throw <| IO.userError s!"typing {precision}: {repr e}"
    | .ok p => pure p
  for offset in [:indices.size] do
    let width := offset+1
    let index := indices[offset]!
    let remaining := 2000000-checked.state.visits
    let p ← match FourierBody.inspect a precision width index remaining with
      | .error e => throw <| IO.userError s!"body {precision}/{width}: {repr e}"
      | .ok p => pure p
    bodyReport s!"body-{precision}-{width}" a precision width index remaining
    bodyReport s!"renamed-{precision}-{width}" (renamed a) precision width index remaining
    bodyReport s!"exact-{precision}-{width}" a precision width index p.visits
    bodyReport s!"short-{precision}-{width}" a precision width index (p.visits-1)
    if width = precision then
      IO.println s!"budget-{precision}|{checked.state.visits}|{checked.state.visits+p.visits}"
      for (request, i) in p.requests.zipIdx do
        emitRequest s!"h-{precision}-{i}" precision request
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    parser.add_argument('--save-source', type=Path)
    args = parser.parse_args()
    cases, base_vectors = fixtures()
    artifacts = {p: c[0] for p, c in cases.items()}
    stages = {p: c[2] for p, c in cases.items()}
    stage_vectors, _ = probes(artifacts, stages)
    source = PRELUDE
    for p, a in artifacts.items():
        source += f'def qft{p} : Artifact := {lean_artifact(a)}\n'
    a, gradients, stage_indices, hs, base = cases[8]
    root = stage_indices[-1]
    enter, first, controlled, last, leave = a['definitions'][root]['body']['children']
    child = a['definitions'][last]['body']['right']
    lower_control = a['definitions'][child]['body']['children'][2]
    repeated = a['definitions'][lower_control]['body']['definition']
    repeated_child = a['definitions'][repeated]['body']['definition']
    gchild = a['definitions'][controlled]['body']['definition']
    phase = a['definitions'][a['definitions'][gradients[-1]]['body']['children'][1]]['body']['left']
    phase_body = a['definitions'][phase]['body']
    leaf = a['definitions'][hs[-1]]['body']['children'][0]
    faults = {
        'negative-control': f'changed qft8 {controlled} (fun d => {{d with body := .control {gchild} false}})',
        'wrong-repeat': f'changed qft8 {repeated} (fun d => {{d with body := .repeatOp 3 {repeated_child}}})',
        'zero-repeat': f'changed qft8 {repeated} (fun d => {{d with body := .repeatOp 0 {repeated_child}}})',
        'omitted-repeat': f'changed qft8 {lower_control} (fun d => {{d with body := .control {repeated_child} true}})',
        'wrong-gradient': f'changed qft8 {controlled} (fun d => {{d with body := .control {gradients[-2]} true}})',
        'phase-numerator': f'changed qft8 {phase} (fun d => {{d with body := .dyadicPhase {phase_body["target"]} 2 {phase_body["k"]}}})',
        'phase-exponent': f'changed qft8 {phase} (fun d => {{d with body := .dyadicPhase {phase_body["target"]} 1 {phase_body["k"]+1}}})',
        'phase-owner': f'changed qft8 {phase} (fun d => {{d with body := .dyadicPhase 909090 1 {phase_body["k"]}}})',
        'recursive-cycle': f'changed qft8 {last} (fun d => {{d with body := .tensor {a["definitions"][last]["body"]["left"]} {root}}})',
        'stage-order': f'changed qft8 {root} (fun d => {{d with body := .sequence #[{enter},{last},{controlled},{first},{leave}]}})',
        'base-body': f'changed qft8 {base} (fun d => {{d with body := .repeatOp 1 {base}}})',
        'h-missing-leaf': f'changed qft8 {hs[-1]} (fun d => {{d with body := .sequence #[]}})',
    }
    source += 'def main : IO Unit := do\n'
    for p, (_, _, st, _, b) in cases.items():
        source += f'  bodyBaseline {p} qft{p} {array([b, *st])}\n'
    source += ''.join(f'  bodyReport {json.dumps(name)} ({fault}) 8 8 {root} 2000000\n' for name, fault in faults.items())
    source += f'''  bodyReport "missing-root" qft8 8 8 999999 2000000
  bodyReport "wrong-precision" qft8 7 7 {child} 2000000
  bodyReport "zero-width" qft8 8 0 {root} 2000000
  bodyReport "oversized-profile" qft8 9 8 {root} 2000000
  bodyReport "width-over-precision" qft8 7 8 {root} 2000000
  bodyReport "zero-budget" qft8 8 8 {root} 0
  bodyReport "reset-budget" qft8 8 8 {root} 2000001
  bodyReport "opaque-h-pending" (changed qft8 {leaf} (fun d => {{d with body := .leaf ByteArray.empty}})) 8 8 {root} 2000000
'''
    program = json.loads(a['definitions'][leaf]['body']['program'])
    wrong_x = copy.deepcopy(program)
    wrong_x['programs'][0]['operations'][0]['gate'] = 'x'
    negative = copy.deepcopy(program)
    raw = negative['programs'][0]
    tokens = [raw['quantum_inputs'][0]['token'], 1000, 1001, 1002, 1003, raw['quantum_outputs'][0]]
    raw['operations'] = [dict(tag='gate', gate=gate, input=tokens[i], output=tokens[i+1])
                         for i, gate in enumerate(['h', 'x', 'z', 'x', 'z'])]
    for name, payload, expected in [('wrong-x', text(wrong_x), 'contract'), ('negative-h', text(negative), 'contract'), ('empty-h', '', 'format')]:
        source += f'  emitH {json.dumps(name)} 8 (changed qft8 {leaf} (fun d => {{d with body := .leaf ({json.dumps(payload)}).toUTF8}})) {hs[-1]} {json.dumps(expected)}\n'
    source += f'  emitH "stale-renamed-h" 8 (renamed qft8) {hs[-1]} "contract"\n'
    if args.save_source:
        args.save_source.write_text(source)
    commands, binary = build_and_run(source, args.record)
    lines = [line.split('|') for line in commands[-1]['stdout'].splitlines()]
    rows = {f[0]: f[1:] for f in lines if f[0] != 'LEAF'}
    leaf_rows = [f[1:] for f in lines if f[0] == 'LEAF']
    for p in range(1, 9):
        before, after = map(int, rows[f'budget-{p}'])
        assert before < after <= 2000000
        for width in range(1, p+1):
            expected = rows[f'body-{p}-{width}']
            assert expected[0].startswith('pending:') and expected[0].endswith(f':{width}')
            assert rows[f'renamed-{p}-{width}'] == rows[f'exact-{p}-{width}'] == expected
            assert rows[f'short-{p}-{width}'] == ['limit']
    for name in [*faults, 'missing-root', 'wrong-precision']:
        assert rows[name] == ['contract'], (name, rows[name])
    for name in ['zero-width', 'oversized-profile', 'width-over-precision', 'zero-budget', 'reset-budget']:
        assert rows[name] == ['limit']
    assert rows['opaque-h-pending'] == rows['body-8-8']
    assert len(leaf_rows) == 40
    result = reconstruct(cases, leaf_rows, commands)
    report = dict(format='qleisli.fourier-body-binding', version=1,
                  status='passed' if result.returncode == 0 else 'failed',
                  native_cases=len(rows), finite_requests=len(leaf_rows), results=rows,
                  base_vectors=base_vectors, stage_vectors=stage_vectors,
                  source_sha256=hashlib.sha256(source.encode()).hexdigest(), binary_sha256=binary,
                  commands=commands, semantic_evidence_issued=False,
                  scope='Every actual recursive body at precision 1–8, exact bound H requests, full phases/reference vectors and one shared remaining budget per independent root request. Complete actual outer reversal, named request, native/finite-reader correspondence and production/corpus gates remain open.')
    if args.record:
        args.record.write_text(json.dumps(report, indent=2)+'\n')
    if result.returncode:
        print(result.stdout+result.stderr)
        raise SystemExit(result.returncode)
    print(text({k: v for k, v in report.items() if k not in ('commands', 'results', 'base_vectors', 'stage_vectors')}))


if __name__ == '__main__':
    main()
