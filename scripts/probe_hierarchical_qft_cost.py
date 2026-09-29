#!/usr/bin/env python3
"""Measure existing QFT checker costs without raising any acceptance limit.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Per-node diagnostic checks are not a whole-artifact acceptance result.
"""
import argparse
import json
from pathlib import Path

from test_hierarchical_artifact import build_and_run
from test_hierarchical_qft import Circuit, SharedGradientCircuit, text


def array(values):
    return '#['+','.join(str(x) for x in values)+']'


def side(s):
    assert not s['classical']
    ports = []
    for p in s['quantum']:
        basis = array('.bit' if a['tag'] == 'bit' else f'.bits {a["width"]}' for a in p['basis'])
        ports.append(f'⟨{p["owner"]},{basis},{array(p["axes"])}⟩')
    return '⟨'+array(ports)+',#[]⟩'


def interface(h):
    return f'⟨{side(h["inputs"])},{side(h["outputs"])}⟩'


def body(b):
    tag = b['tag']
    if tag in ('leaf', 'finite'):
        value = b['program' if tag == 'leaf' else 'description']
        return f'.{tag} ({json.dumps(value)}).toUTF8'
    if tag == 'sequence':
        return f'.sequence {array(b["children"])}'
    if tag == 'tensor':
        return f'.tensor {b["left"]} {b["right"]}'
    if tag == 'rewire':
        p = b['permutation']
        return f'.rewire ⟨{array(p["owners"])},{array(p["axes"])},#[]⟩'
    if tag == 'structural':
        op = b['operation']
        name = dict(take_bit='takeBit', put_bit='putBit')[op['tag']]
        return f'.structural (.{name} {op["width"]} {op["position"]})'
    if tag in ('phase', 'dyadic_phase'):
        prefix = '.phase' if tag == 'phase' else f'.dyadicPhase {b["target"]}'
        return f'{prefix} {b["j"]} {b["k"]}'
    if tag == 'control':
        return f'.control {b.get("definition",b.get("child"))} {str(b["polarity"]).lower()}'
    if tag == 'repeat':
        return f'.repeatOp {b["count"]} {b["definition"]}'
    if tag == 'power':
        return f'.power {b["child"]} {b["count"]}'
    raise AssertionError(tag)


def artifact(a):
    definitions = array(f'⟨{interface(d["interface"])},.unitary,{body(d["body"])}⟩' for d in a['definitions'])
    meanings = array(f'⟨{interface(m["interface"])},{body(m["body"])}⟩' for m in a['meanings'])
    encodings = array(f'⟨{side(e["logical"])},{side(e["physical"])},.identity⟩' for e in a['encodings'])
    proofs = array(f'⟨.equation,.{("repeatOp" if p["rule"]["tag"] == "repeat" else p["rule"]["tag"])},{array(p["premises"])},{p["implementation"]},'
                   f'{p["meaning"]},{p["input_encoding"]},{p["output_encoding"]},⟨1,#[],#[]⟩⟩'
                   for p in a['proofs'])
    entry = a['entry']
    return f'⟨{definitions},{meanings},{encodings},{proofs},⟨{entry["implementation"]},{entry["proof"]}⟩⟩'


PRELUDE = '''import QleisliKernel.Hierarchical.Conditional
open QleisliKernel.Hierarchical Artifact
set_option maxRecDepth 10000
def report (width : Nat) (a : Artifact) : IO Unit := do
  let order := Array.range (totalNodes a)
  let prepared ← match prepare a order with
    | .error e => throw <| IO.userError s!"prepare {width}: {repr e}"
    | .ok p => pure p.totalVisits
  let mut nodes := 0
  let mut contracts := 0
  let mut rules := 0
  let mut typedRules := 0
  for i in [:a.definitions.size] do
    match NodeTyping.check a i 2000000 with
    | .error e => throw <| IO.userError s!"node {width}/{i}: {repr e}"
    | .ok v => nodes := nodes + v.visits
  for ref in ContractTyping.subjects a do
    match ContractTyping.check a ref 2000000 with
    | .error e => throw <| IO.userError s!"contract {width}/{repr ref}: {repr e}"
    | .ok v => contracts := contracts + v.visits
  for i in [:a.proofs.size] do
    match Conditional.localCheck a i 2000000 with
    | .error e => throw <| IO.userError s!"rule {width}/{i}: {repr e}"
    | .ok v => rules := rules + v.visits
    if (a.proofs[i]?.map (fun p => p.rule == .finite)).getD false then
      match Finite.inspect a i 2000000 with
      | .error e => throw <| IO.userError s!"finite {width}/{i}: {repr e}"
      | .ok v => typedRules := typedRules + v.visits
    else
      match TypedRule.check a i 2000000 with
      | .error e => throw <| IO.userError s!"typed rule {width}/{i}: {repr e}"
      | .ok v => typedRules := typedRules + v.visits
  IO.println s!"{width}|{prepared}|{nodes}|{contracts}|{rules}|{typedRules}"
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path, required=True)
    parser.add_argument('--construction', choices=['lifted','shared-gradient'], default='lifted')
    args = parser.parse_args()
    builder = SharedGradientCircuit if args.construction == 'shared-gradient' else Circuit
    widths = range(1,9) if args.construction == 'shared-gradient' else [1,2,3,4,8]
    source = PRELUDE
    for n in widths:
        source += f'def qft{n} : Artifact := {artifact(builder().qft(n))}\n'
    source += 'def main : IO Unit := do\n'+''.join(f'  report {n} qft{n}\n' for n in widths)
    commands, binary = build_and_run(source, args.record)
    rows = [[int(x) for x in line.split('|')] for line in commands[-1]['stdout'].splitlines()]
    report = dict(format='qleisli.hierarchy-qft-cost-probe', version=1, status='diagnostic',
                  construction=args.construction,
                  columns=['width','preparation','definition_typing','contract_typing','legacy_local_rules','typed_local_rules'],
                  rows=rows, binary_sha256=binary, commands=commands,
                  scope='Local checks each use the unchanged 2000000 ceiling. Their separate totals are diagnostics, not acceptance of the complete artifact.')
    args.record.write_text(json.dumps(report,indent=2)+'\n')
    print(text({k:v for k,v in report.items() if k != 'commands'}))


if __name__ == '__main__':
    main()
