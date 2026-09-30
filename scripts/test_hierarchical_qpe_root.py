#!/usr/bin/env python3
"""One fresh pure-artifact check, provider binding and actual QPE schedule.

Frozen provider graphs below are mutation fixtures, not independent QPE proof.
The theorem's independent provider/finite-reader premises remain explicit.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import hashlib
import json
from pathlib import Path

from compact_sized_graph import remap
from compile_sized_corpus import Operation
from compile_sized_instrument import compile_instrument
from probe_hierarchical_qft_cost import array, interface, side
from test_hierarchical_artifact import ROOT, build_and_run
from test_hierarchical_qpe_schedule import fixture
from test_hierarchical_routed_power import body
from test_sized_instrument import sources


def artifact(graph):
    definitions = array(f'⟨{interface(d["interface"])},.unitary,{body(d["body"])}⟩' for d in graph['definitions'])
    meanings = array(f'⟨{interface(m["interface"])},{body(m["body"])}⟩' for m in graph['meanings'])
    encodings = array(f'⟨{side(e["logical"])},{side(e["physical"])},.identity⟩' for e in graph['encodings'])
    proofs = array(f'⟨.equation,.{("repeatOp" if p["rule"]["tag"] == "repeat" else p["rule"]["tag"])},{array(p["premises"])},{p["implementation"]},'
                   f'{p["meaning"]},{p["input_encoding"]},{p["output_encoding"]},⟨1,#[],#[]⟩⟩' for p in graph['proofs'])
    entry = graph['entry']
    return f'⟨{definitions},{meanings},{encodings},{proofs},⟨{entry["implementation"]},{entry["proof"]}⟩⟩'


def children(value):
    tag = value['tag']
    if tag == 'sequence':
        return value['children']
    if tag == 'tensor':
        return [value['left'], value['right']]
    if tag in ('inverse', 'control', 'power'):
        return [value['child']]
    return []


def provider_fixture(graph, provider):
    proof, = [i for i, p in enumerate(graph['proofs']) if p['implementation'] == provider]
    root = graph['proofs'][proof]['meaning']
    preorder, postorder, seen = [], [], set()
    def walk(index):
        if index in seen:
            return
        seen.add(index)
        preorder.append(index)
        for child in children(graph['meanings'][index]['body']):
            walk(child)
        postorder.append(index)
    walk(root)
    indices = {old: new for new, old in enumerate(preorder)}
    meanings = array(f'⟨{interface(graph["meanings"][i]["interface"])},{body(remap(graph["meanings"][i]["body"],indices))}⟩' for i in preorder)
    header = interface(graph['definitions'][provider]['interface'])
    request = f'⟨.equation,.unitary,{header},{meanings},0⟩'
    pairs = array(f'⟨{i},{indices[i]},{array(indices[j] for j in children(graph["meanings"][i]["body"]))}⟩' for i in preorder)
    return proof, request, pairs, array(indices[i] for i in postorder)


PRELUDE = '''import QleisliKernel.Hierarchical.QpeRoot
open QleisliKernel.Hierarchical Artifact
set_option maxRecDepth 20000
def report (name : String) (r : QpeRoot.Request) (p : QpeRoot.Packet) : IO Unit := do
  match QpeRoot.checkAll r p with
  | .error e => IO.println s!"{name}|{repr e.kind}"
  | .ok checked => IO.println s!"{name}|pending|{checked.visits}|{checked.artifact.state.visits}|{checked.provider.visits}|{checked.schedule.visits}|{checked.artifact.state.requests.size}"
def changePhase (a : Artifact) (index : Nat) : Artifact :=
  {a with
    definitions := a.definitions.mapIdx (fun i d => if i==index then match d.body with
      | .dyadicPhase target _ k => {d with body:=.dyadicPhase target 2 k} | _ => d else d)
    meanings := a.meanings.mapIdx (fun i m => if i==index then match m.body with
      | .phase _ k => {m with body:=.phase 2 k} | _ => m else m)}
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    code, calls, expected, graphs = PRELUDE, [], {}, {}
    for name, n, m in [('small', 1, 2), ('target2', 2, 2), ('precision3', 1, 3), ('target2precision4', 2, 4)]:
        proposal = compile_instrument(sources(), 'measurement::qpe', dict(n=n, m=m),
                                      {'U': Operation('evolution::evolve', (n, 1, 3))})
        graphs[name] = graph = proposal['graph']
        schedule, candidate, metadata = fixture(graph, n, m)
        proof, provider, pairs, order = provider_fixture(graph, metadata['stages'][0]['provider'])
        code += f'def graph_{name} : Artifact := {artifact(graph)}\n'
        code += f'def request_{name} : QpeRoot.Request := ⟨{schedule},{provider}⟩\n'
        code += f'def packet_{name} : QpeRoot.Packet := ⟨graph_{name},Array.range (totalNodes graph_{name}),{proof},{pairs},{order},{candidate}⟩\n'
        calls.append(f'report "{name}" request_{name} packet_{name}')
        expected[name] = 'capacity' if name == 'target2precision4' else 'pending'
    phase = next(i for i, d in enumerate(graphs['small']['definitions']) if d['body']['tag'] == 'dyadic_phase')
    def add(name, request='request_small', packet='packet_small', status='contract'):
        calls.append(f'report "{name}" ({request}) ({packet})')
        expected[name] = status
    add('changed-provider', packet=f'{{packet_small with artifact:=changePhase graph_small {phase}}}')
    add('wrong-provider-proof', packet='{packet_small with providerProof:=packet_small.artifact.entry.proof}')
    add('missing-provider-proof', packet='{packet_small with providerProof:=4294967295}')
    add('missing-provider-pair', packet='{packet_small with pairs:=#[]}', status='limit')
    add('wrong-phase-order', request='{request_small with circuit:={request_small.circuit with phase:=#[1,2]}}')
    add('wrong-provider-effect', request='{request_small with provider:={request_small.provider with effect:=.iso}}')
    add('wrong-provider-kind', request='{request_small with provider:={request_small.provider with kind:=.instrument}}')
    add('incomplete-artifact', packet='{packet_small with order:=#[]}', status='invalidIr')
    code += 'def main : IO Unit := do\n' + ''.join('  '+call+'\n' for call in calls)
    commands, binary = build_and_run(code, args.record)
    rows = {}
    for line in commands[-1]['stdout'].splitlines():
        name, *fields = line.split('|')
        assert name not in rows
        rows[name] = fields
    assert rows.keys() == expected.keys(), (rows.keys(), expected.keys())
    for name, status in expected.items():
        actual = rows[name][0].rsplit('.', 1)[-1]
        assert actual in (('pending', 'limit') if status == 'capacity' else (status,)), (name, rows[name], status)
    report = dict(format='qleisli.qpe-root-validation', version=1, status='passed',
                  native_cases=len(rows), results=rows,
                  source_sha256=hashlib.sha256(code.encode()).hexdigest(), binary_sha256=binary,
                  kernel_source_sha256=hashlib.sha256((ROOT/'lean-kernel/QleisliKernel/Hierarchical/QpeRoot.lean').read_bytes()).hexdigest(),
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), commands=commands,
                  provider_request_origin='frozen baseline mutation fixture',
                  finite_equations_discharged=False, named_qpe_instrument=False, production_integration=False)
    if args.record:
        args.record.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('commands',)}))


if __name__ == '__main__':
    main()
