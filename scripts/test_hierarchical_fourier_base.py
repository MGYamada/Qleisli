#!/usr/bin/env python3
"""Actual one-bit Fourier bases and native-bound fresh finite H reconstruction.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
All requests remain conditional components, not production Fourier evidence.
"""
import argparse
import copy
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import tempfile

from probe_hierarchical_qft_cost import artifact as lean_artifact, array
from test_hierarchical_artifact import build_and_run
from test_hierarchical_gradient import PRELUDE as GRADIENT_PRELUDE
from test_hierarchical_qft import SharedGradientCircuit, execute, text

ROOT = Path(__file__).resolve().parent.parent
PRELUDE = '''import QleisliKernel.Hierarchical.FourierBase
import QleisliKernel.Hierarchical.Hadamard
''' + GRADIENT_PRELUDE + '''
def baseStatus (a : Artifact) (index remaining : Nat) : String :=
  match FourierBase.inspect a index remaining with
  | .ok p => s!"pending:{p.visits}"
  | .error .limit => "limit"
  | .error _ => "contract"
def hStatus (a : Artifact) (index remaining : Nat) : String :=
  match Hadamard.inspect a index remaining with
  | .ok p => s!"pending:{p.visits}"
  | .error .limit => "limit"
  | .error _ => "contract"
def baseReport (name : String) (a : Artifact) (index remaining : Nat) : IO Unit :=
  IO.println s!"{name}|{baseStatus a index remaining}"
def hReport (name : String) (a : Artifact) (index remaining : Nat) : IO Unit :=
  IO.println s!"{name}|{hStatus a index remaining}"
def emitH (name : String) (precision : Nat) (a : Artifact) (index : Nat) (expected : String) : IO Unit := do
  let p ← match Hadamard.inspect a index 2000000 with
    | .error e => throw <| IO.userError s!"request {name}: {repr e}"
    | .ok p => pure p
  let r := p.request
  let some input := r.leaf.interface.inputs.quantum[0]? | throw <| IO.userError "missing input"
  let some output := r.leaf.interface.outputs.quantum[0]? | throw <| IO.userError "missing output"
  let bytes := String.intercalate "," (r.program.data.toList.map (fun b => toString b.toNat))
  IO.println s!"LEAF|{name}|{precision}|{r.leafIndex}|{input.owner}|{output.owner}|{input.axes[0]!}|{output.axes[0]!}|{expected}|{bytes}"
def fullBaseline (precision : Nat) (a : Artifact) (gradients stages hs : Array Nat) (base : Nat) : IO Unit := do
  let checked ← match Conditional.checkAll a (Array.range (totalNodes a)) with
    | .error e => throw <| IO.userError s!"typing {precision}: {repr e}"
    | .ok p => pure p
  let mut used := checked.state.visits
  for width in [:gradients.size] do
    let p ← match Gradient.inspect a precision width gradients[width]! (2000000-used) with
      | .error e => throw <| IO.userError s!"gradient {precision}/{width}: {repr e}"
      | .ok p => pure p
    used := used+p.visits
  for offset in [:stages.size] do
    let p ← match FourierStage.inspect a (offset+1) stages[offset]! (2000000-used) with
      | .error e => throw <| IO.userError s!"stage {precision}/{offset}: {repr e}"
      | .ok p => pure p
    used := used+p.visits
  let before := used
  let b ← match FourierBase.inspect a base (2000000-used) with
    | .error e => throw <| IO.userError s!"base {precision}: {repr e}"
    | .ok p => pure p
  baseReport s!"base-{precision}" a base (2000000-used)
  baseReport s!"base-renamed-{precision}" (renamed a) base (2000000-used)
  baseReport s!"base-exact-{precision}" a base b.visits
  baseReport s!"base-short-{precision}" a base (b.visits-1)
  used := used+b.visits
  for offset in [:hs.size] do
    let index := hs[offset]!
    let p ← match Hadamard.inspect a index (2000000-used) with
      | .error e => throw <| IO.userError s!"H {precision}/{offset}: {repr e}"
      | .ok p => pure p
    hReport s!"h-{precision}-{offset}" a index (2000000-used)
    hReport s!"h-renamed-{precision}-{offset}" (renamed a) index (2000000-used)
    hReport s!"h-exact-{precision}-{offset}" a index p.visits
    hReport s!"h-short-{precision}-{offset}" a index (p.visits-1)
    emitH s!"h-{precision}-{offset}" precision a index "ok"
    used := used+p.visits
  IO.println s!"budget-{precision}|{checked.state.visits}|{before}|{used}"
'''


def fixtures():
    cases = {}
    semantic = []
    for precision in range(1, 9):
        b = SharedGradientCircuit()
        a = b.qft(precision)
        bodies = [b.recursive(n) for n in range(1, precision+1)]
        hs = [a['definitions'][a['definitions'][r]['body']['children'][1]]['body']['left'] for r in bodies]
        cases[precision] = (a, [b.gradient(n) for n in range(precision)], bodies[1:], hs, bodies[0])
        vectors = [[1, 0], [0, 1], [1/math.sqrt(3), 1j/math.sqrt(3)], [1/math.sqrt(3), 0]]
        for v in vectors:
            expected = [(v[0]+v[1])/math.sqrt(2), (v[0]-v[1])/math.sqrt(2)]
            error = max(abs(x-y) for x, y in zip(execute(a, bodies[0], v), expected))
            assert error < 1e-12
            semantic.append(dict(precision=precision, maximum_error=error))
    return cases, semantic


def reconstruct(cases, leaf_rows, commands):
    with tempfile.TemporaryDirectory(prefix='qleisli-hadamard-binding-') as temporary:
        directory = Path(temporary)
        for p, (a, _, _, _, _) in cases.items():
            (directory/f'qft-{p}.json').write_text(text(a))
        manifest = []
        for fields in leaf_rows:
            name, p, leaf_index, owner, output, axis, out_axis, expected, values = fields
            data = bytes(map(int, values.split(','))) if values else b''
            if name.startswith('h-'):
                actual = cases[int(p)][0]['definitions'][int(leaf_index)]['body']['program'].encode()
                assert data == actual  # Native request carries complete actual bytes.
            filename = f'{name}.qirf'
            (directory/filename).write_bytes(data)
            manifest.append('|'.join([name, p, owner, output, axis, out_axis, expected, filename]))
        (directory/'requests.txt').write_text('\n'.join(manifest)+'\n')
        env = os.environ.copy()
        env['QLEISLI_HADAMARD_FIXTURES'] = str(directory)
        env['QLEISLI_HIERARCHY_KERNEL'] = str(ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel')
        command = ['cargo', 'test', '--test', 'qft_hierarchy', 'reconstruct_bound_hadamard_requests', '--', '--ignored', '--nocapture']
        result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True, timeout=120)
        commands.append(dict(argv=command, exit_code=result.returncode, stdout=result.stdout, stderr=result.stderr))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    parser.add_argument('--save-source', type=Path)
    args = parser.parse_args()
    cases, semantic = fixtures()
    source = PRELUDE
    for p, (a, _, _, _, _) in cases.items():
        source += f'def qft{p} : Artifact := {lean_artifact(a)}\n'
    a, _, _, hs, base = cases[8]
    enter, first, last, leave = a['definitions'][base]['body']['children']
    low = a['definitions'][first]['body']['right']
    high = a['definitions'][last]['body']['left']
    h = hs[-1]
    leaf, rename = a['definitions'][h]['body']['children']
    base_faults = {
        'base-empty-owner': f'changed qft8 {low} (fun d => {{d with interface := ⟨⟨#[],#[]⟩,⟨#[],#[]⟩⟩}})',
        'base-empty-as-unit': f'changed qft8 {low} (fun d => {{d with interface := {{d.interface with inputs := {{d.interface.inputs with quantum := d.interface.inputs.quantum.map fun p => {{p with basis := #[.unit]}}}}}}}})',
        'base-invent-empty-axis': f'changed qft8 {low} (fun d => {{d with body := .rewire ⟨#[0],#[0],#[]⟩}})',
        'base-nonidentity': f'changed qft8 {high} (fun d => {{d with body := .dyadicPhase 100 1 1}})',
        'base-order': f'changed qft8 {base} (fun d => {{d with body := .sequence #[{enter},{last},{first},{leave}]}})',
        'base-take-width': f'changed qft8 {enter} (fun d => {{d with body := .structural (.takeBit 2 0)}})',
        'base-put-position': f'changed qft8 {leave} (fun d => {{d with body := .structural (.putBit 1 1)}})',
        'base-extra-child': f'changed qft8 {base} (fun d => {{d with body := .sequence #[{enter},{first},{first},{last},{leave}]}})',
    }
    h_faults = {
        'h-order': f'changed qft8 {h} (fun d => {{d with body := .sequence #[{rename},{leaf}]}})',
        'h-extra-child': f'changed qft8 {h} (fun d => {{d with body := .sequence #[{leaf},{rename},{rename}]}})',
        'h-dangling-leaf': f'changed qft8 {h} (fun d => {{d with body := .sequence #[999999,{rename}]}})',
        'h-wrong-axis': f'changed qft8 {rename} (fun d => {{d with body := .rewire ⟨#[0],#[1],#[]⟩}})',
        'h-drop-owner': f'changed qft8 {rename} (fun d => {{d with body := .rewire ⟨#[],#[0],#[]⟩}})',
        'h-classical-map': f'changed qft8 {rename} (fun d => {{d with body := .rewire ⟨#[0],#[0],#[0]⟩}})',
        'h-observe-leaf': f'changed qft8 {leaf} (fun d => {{d with effect := .observe}})',
        'h-owner-interface': f'changed qft8 {rename} (fun d => {{d with interface := {{d.interface with outputs := {{d.interface.outputs with quantum := d.interface.outputs.quantum.map fun p => {{p with owner := 90000}}}}}}}})',
        'h-bit-as-bits': f'changed qft8 {h} (fun d => {{d with interface := {{d.interface with inputs := {{d.interface.inputs with quantum := d.interface.inputs.quantum.map fun p => {{p with basis := #[.bits 1]}}}}}}}})',
    }
    program = json.loads(a['definitions'][leaf]['body']['program'])
    wrong_x = copy.deepcopy(program)
    wrong_x['programs'][0]['operations'][0]['gate'] = 'x'
    negative = copy.deepcopy(program)
    raw = negative['programs'][0]
    owner = raw['quantum_inputs'][0]['token']
    output = raw['quantum_outputs'][0]
    tokens = [owner, 1000, 1001, 1002, 1003, output]
    raw['operations'] = [dict(tag='gate', gate=gate, input=tokens[i], output=tokens[i+1])
                         for i, gate in enumerate(['h', 'x', 'z', 'x', 'z'])]
    # Independent sequential gate calculation: global -H has H probabilities.
    for vector in ([1, 0], [0, 1], [1/math.sqrt(2), 1j/math.sqrt(2)]):
        wanted = [(vector[0]+vector[1])/math.sqrt(2), (vector[0]-vector[1])/math.sqrt(2)]
        actual = wanted[:]
        for gate in ['x', 'z', 'x', 'z']:
            actual = actual[::-1] if gate == 'x' else [actual[0], -actual[1]]
        assert max(abs(x+y) for x, y in zip(actual, wanted)) < 1e-12
        assert max(abs(abs(x)**2-abs(y)**2) for x, y in zip(actual, wanted)) < 1e-12
    source += 'def main : IO Unit := do\n'
    for p, (_, gradients, stages, hindices, baseindex) in cases.items():
        source += f'  fullBaseline {p} qft{p} {array(gradients)} {array(stages)} {array(hindices)} {baseindex}\n'
    source += ''.join(f'  baseReport {json.dumps(name)} ({fault}) {base} 2000000\n' for name, fault in base_faults.items())
    source += ''.join(f'  hReport {json.dumps(name)} ({fault}) {h} 2000000\n' for name, fault in h_faults.items())
    source += f'''  baseReport "base-zero-budget" qft8 {base} 0
  baseReport "base-budget-reset" qft8 {base} 2000001
  hReport "h-zero-budget" qft8 {h} 0
  hReport "h-budget-reset" qft8 {h} 2000001
  hReport "h-oversized-payload" (changed qft8 {leaf} (fun d => {{d with body := .leaf ⟨Array.replicate 16777217 0⟩}})) {h} 2000000
'''
    for name, payload, expected in [('wrong-x', text(wrong_x), 'contract'), ('negative-h', text(negative), 'contract'), ('empty-h', '', 'limit')]:
        source += f'  emitH {json.dumps(name)} 8 (changed qft8 {leaf} (fun d => {{d with body := .leaf ({json.dumps(payload)}).toUTF8}})) {h} {json.dumps(expected)}\n'
    source += f'  emitH "stale-renamed-h" 8 (renamed qft8) {h} "contract"\n'
    if args.save_source:
        args.save_source.write_text(source)
    commands, binary = build_and_run(source, args.record)
    lines = [line.split('|') for line in commands[-1]['stdout'].splitlines()]
    rows = {fields[0]: fields[1:] for fields in lines if fields[0] != 'LEAF'}
    leaf_rows = [fields[1:] for fields in lines if fields[0] == 'LEAF']
    for p in range(1, 9):
        _, before, after = map(int, rows[f'budget-{p}'])
        assert before < after <= 2000000
        assert rows[f'base-{p}'][0].startswith('pending:')
        assert rows[f'base-renamed-{p}'] == rows[f'base-exact-{p}'] == rows[f'base-{p}']
        assert rows[f'base-short-{p}'] == ['limit']
        for offset in range(p):
            name = f'h-{p}-{offset}'
            assert rows[name][0].startswith('pending:')
            assert rows[f'h-renamed-{p}-{offset}'] == rows[f'h-exact-{p}-{offset}'] == rows[name]
            assert rows[f'h-short-{p}-{offset}'] == ['limit']
    for name in (*base_faults, *h_faults):
        assert rows[name] == ['contract'], (name, rows[name])
    for name in ['base-zero-budget', 'base-budget-reset', 'h-zero-budget', 'h-budget-reset', 'h-oversized-payload']:
        assert rows[name] == ['limit']
    assert len(leaf_rows) == 40
    result = reconstruct(cases, leaf_rows, commands)
    report = dict(format='qleisli.fourier-base-hadamard-binding', version=1,
                  status='passed' if result.returncode == 0 else 'failed',
                  native_cases=len(rows), finite_requests=len(leaf_rows), results=rows,
                  semantic_probes=semantic, global_phase_fault=True, semantic_evidence_issued=False,
                  source_sha256=hashlib.sha256(source.encode()).hexdigest(), binary_sha256=binary,
                  commands=commands,
                  scope='Actual base/H component binding, complete finite bytes, independent exact H and cumulative existing budgets. Recursive controlled-gradient discharge and full requested-root/reversal integration remain pending; all external schemas disabled.')
    if args.record:
        args.record.write_text(json.dumps(report, indent=2)+'\n')
    if result.returncode:
        print(result.stdout+result.stderr)
        raise SystemExit(result.returncode)
    print(text({k: v for k, v in report.items() if k not in ('commands', 'results', 'semantic_probes')}))


if __name__ == '__main__':
    main()
