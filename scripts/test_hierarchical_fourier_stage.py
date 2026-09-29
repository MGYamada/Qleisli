#!/usr/bin/env python3
"""Actual Fourier-stage binding and independent complex/reference diagnostics.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Pending stage inspection does not discharge H, gradient or recursive equations.
"""
import argparse
import cmath
import copy
import hashlib
import json
import math
from pathlib import Path

from probe_hierarchical_qft_cost import artifact as lean_artifact, array
from test_hierarchical_artifact import build_and_run
from test_hierarchical_gradient import PRELUDE as GRADIENT_PRELUDE
from test_hierarchical_qft import SharedGradientCircuit, execute, text

PRELUDE = 'import QleisliKernel.Hierarchical.FourierStage\n' + GRADIENT_PRELUDE
PRELUDE += '''
def stageStatus (a : Artifact) (n index remaining : Nat) : String :=
  match FourierStage.inspect a n index remaining with
  | .ok p => s!"pending:{p.visits}"
  | .error .limit => "limit"
  | .error .invalidIr => "invalid_ir"
  | .error .contract => "contract"
def stageReport (name : String) (a : Artifact) (n index remaining : Nat) : IO Unit :=
  IO.println s!"{name}|{stageStatus a n index remaining}"
def stageBaseline (precision : Nat) (a : Artifact) (gradients stages : Array Nat) : IO Unit := do
  let pending ← match Conditional.checkAll a (Array.range (totalNodes a)) with
    | .error e => throw <| IO.userError s!"whole typing {precision}: {repr e}"
    | .ok pending => pure pending
  let mut used := pending.state.visits
  for width in [:gradients.size] do
    let p ← match Gradient.inspect a precision width gradients[width]! (2000000-used) with
      | .error e => throw <| IO.userError s!"gradient {precision}/{width}: {repr e}"
      | .ok p => pure p
    used := used+p.visits
  let gradientUsed := used
  for offset in [:stages.size] do
    let n := offset+1
    let index := stages[offset]!
    let p ← match FourierStage.inspect a n index (2000000-used) with
      | .error e => throw <| IO.userError s!"stage {precision}/{n}: {repr e}"
      | .ok p => pure p
    stageReport s!"pending-{precision}-{n}" a n index (2000000-used)
    stageReport s!"renamed-{precision}-{n}" (renamed a) n index (2000000-used)
    stageReport s!"exact-{precision}-{n}" a n index p.visits
    stageReport s!"short-{precision}-{n}" a n index (p.visits-1)
    used := used+p.visits
  IO.println s!"budget-{precision}|{pending.state.visits}|{gradientUsed}|{used}"
'''


def fixtures():
    artifacts, gradients, stages, bases = {}, {}, {}, {}
    for precision in range(1, 9):
        builder = SharedGradientCircuit()
        artifacts[precision] = builder.qft(precision)
        gradients[precision] = [builder.gradient(n) for n in range(precision)]
        stages[precision] = [builder.recursive(n) for n in range(2, precision+1)]
        bases[precision] = builder.recursive(1)
    return artifacts, gradients, stages, bases


def reversed_fourier(vector):
    size = len(vector)
    width = size.bit_length()-1
    return [sum(v*cmath.exp(2j*math.pi*x*int(f'{y:0{width}b}'[::-1], 2)/size)
                for x, v in enumerate(vector))/math.sqrt(size) for y in range(size)]


def probes(artifacts, stages):
    rows = []
    for precision, indices in stages.items():
        for width, index in enumerate(indices, 2):
            size = 1 << width
            selected = sorted({0, 1, size//2, size-1})
            vectors = [[complex(i == x) for i in range(size)] for x in selected]
            columns = [[complex(((i+2*r) % 7)-3, ((3*i+r) % 5)-2)
                        for i in range(size)] for r in range(2)]
            norm = math.sqrt(sum(abs(z)**2 for col in columns for z in col))
            vectors += [[z/norm for z in col] for col in columns]
            errors = [max(abs(a-b) for a, b in zip(execute(artifacts[precision], index, v),
                                                   reversed_fourier(v))) for v in vectors]
            assert max(errors) < 1e-12, (precision, width, errors)
            rows.append(dict(precision=precision, width=width, vectors=len(vectors),
                             maximum_error=max(errors)))
    # H is more specific than a unitary. An X leaf keeps all structural headers
    # valid but must fail the eventual exact-H obligation and the Fourier oracle.
    wrong = copy.deepcopy(artifacts[8])
    root = stages[8][-1]
    first = wrong['definitions'][root]['body']['children'][1]
    h = wrong['definitions'][first]['body']['left']
    leaf = wrong['definitions'][h]['body']['children'][0]
    payload = json.loads(wrong['definitions'][leaf]['body']['program'])
    payload['programs'][payload['root']]['operations'][0]['gate'] = 'x'
    wrong['definitions'][leaf]['body']['program'] = text(payload)
    vector = [1]+[0]*255
    assert max(abs(a-b) for a, b in zip(execute(wrong, root, vector), reversed_fourier(vector))) > 0.01
    return rows, leaf


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    parser.add_argument('--save-source', type=Path)
    args = parser.parse_args()
    artifacts, gradients, stages, bases = fixtures()
    semantic, leaf = probes(artifacts, stages)
    source = PRELUDE
    for precision, a in artifacts.items():
        source += f'def qft{precision} : Artifact := {lean_artifact(a)}\n'
    root = stages[8][-1]
    enter, first, gradient, last, leave = artifacts[8]['definitions'][root]['body']['children']
    h = artifacts[8]['definitions'][first]['body']['left']
    low = artifacts[8]['definitions'][first]['body']['right']
    high = artifacts[8]['definitions'][last]['body']['left']
    child = artifacts[8]['definitions'][last]['body']['right']
    faults = {
        'tensor-order': f'changed qft8 {first} (fun d => {{d with body := .tensor {low} {h}}})',
        'tensor-alias': f'changed qft8 {first} (fun d => {{d with body := .tensor {h} {h}}})',
        'recursive-order': f'changed qft8 {last} (fun d => {{d with body := .tensor {child} {high}}})',
        'dangling-child': f'changed qft8 {last} (fun d => {{d with body := .tensor {high} 999999}})',
        'sequence-order': f'changed qft8 {root} (fun d => {{d with body := .sequence #[{enter},{last},{gradient},{first},{leave}]}})',
        'missing-gradient': f'changed qft8 {root} (fun d => {{d with body := .sequence #[{enter},{first},{last},{leave}]}})',
        'oversized-sequence': f'changed qft8 {root} (fun d => {{d with body := .sequence (Array.replicate 1000000 {enter})}})',
        'take-position': f'changed qft8 {enter} (fun d => {{d with body := .structural (.takeBit 8 0)}})',
        'put-width': f'changed qft8 {leave} (fun d => {{d with body := .structural (.putBit 7 6)}})',
        'low-permutation': f'changed qft8 {low} (fun d => {{d with body := .rewire ⟨#[0],#[6,5,4,3,2,1,0],#[]⟩}})',
        'high-nonidentity': f'changed qft8 {high} (fun d => {{d with body := .dyadicPhase 107 1 1}})',
        'routing': f'changed qft8 {enter} (fun d => {{d with interface := {{d.interface with inputs := {{d.interface.inputs with quantum := d.interface.inputs.quantum.map fun p => {{p with axes := p.axes.reverse}}}}}}}})',
        'bits-vs-tuple': f'changed qft8 {child} (fun d => {{d with interface := {{d.interface with inputs := {{d.interface.inputs with quantum := d.interface.inputs.quantum.map fun p => {{p with basis := #[.tuple 7,.bit,.bit,.bit,.bit,.bit,.bit,.bit]}}}}}}}})',
        'observe-child': f'changed qft8 {child} (fun d => {{d with effect := .observe}})',
        'gradient-interface': f'changed qft8 {gradient} (fun d => {{d with interface := {{d.interface with inputs := {{d.interface.inputs with quantum := d.interface.inputs.quantum.reverse}}}}}})',
        'aliased-recursion': f'changed qft8 {last} (fun d => {{d with body := .tensor {high} {root}}})',
    }
    source += 'def main : IO Unit := do\n'
    source += ''.join(f'  stageBaseline {p} qft{p} {array(gradients[p])} {array(stages[p])}\n' for p in range(1, 9))
    source += ''.join(f'  stageReport {json.dumps(name)} ({a}) 7 {root} 2000000\n' for name, a in faults.items())
    source += f'''  stageReport "missing-root" qft8 7 999999 2000000
  stageReport "zero-budget" qft8 7 {root} 0
  stageReport "reset-budget" qft8 7 {root} 2000001
  stageReport "zero-width" qft1 0 {bases[1]} 2000000
  stageReport "excess-width" qft8 8 {root} 2000000
  stageReport "wrong-width" qft8 6 {root} 2000000
  stageReport "leaf-obligation-remains" (changed qft8 {leaf} (fun d => {{d with body := .leaf ByteArray.empty}})) 7 {root} 2000000
  stageReport "gradient-obligation-remains" (changed qft8 {gradient} (fun d => {{d with body := .control {child} false}})) 7 {root} 2000000
'''
    if args.save_source:
        args.save_source.write_text(source)
    commands, binary = build_and_run(source, args.record)
    rows = {line.split('|')[0]: line.split('|')[1:] for line in commands[-1]['stdout'].splitlines()}
    for precision in range(1, 9):
        before, after_gradient, after_stage = map(int, rows[f'budget-{precision}'])
        assert before < after_gradient <= after_stage <= 2000000
        for n in range(1, precision):
            ok = rows[f'pending-{precision}-{n}']
            assert ok[0].startswith('pending:')
            assert rows[f'renamed-{precision}-{n}'] == ok
            assert rows[f'exact-{precision}-{n}'] == ok
            assert rows[f'short-{precision}-{n}'] == ['limit']
    for fault in (*faults, 'missing-root', 'wrong-width'):
        assert rows[fault] == ['contract'], (fault, rows[fault])
    for name in ['zero-budget', 'reset-budget', 'zero-width', 'excess-width']:
        assert rows[name] == ['limit']
    for name in ['leaf-obligation-remains', 'gradient-obligation-remains']:
        assert rows[name] == rows['pending-8-7']
    report = dict(format='qleisli.hierarchical-fourier-stage-binding', version=1, status='passed',
                  native_cases=len(rows), results=rows, semantic_probes=semantic,
                  wrong_h_oracle_rejected=True, semantic_evidence_issued=False,
                  source_sha256=hashlib.sha256(source.encode()).hexdigest(), binary_sha256=binary,
                  commands=commands,
                  scope='Actual five-node stage geometry and cumulative Conditional/Gradient/FourierStage budget. The one-bit base, exact H, controlled-gradient/recursive obligations, complete reversal and requested-root binding remain; external schemas stay disabled.')
    if args.record:
        args.record.write_text(json.dumps(report, indent=2)+'\n')
    print(text({k: v for k, v in report.items() if k not in ('commands', 'results', 'semantic_probes')}))


if __name__ == '__main__':
    main()
