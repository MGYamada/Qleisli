#!/usr/bin/env python3
"""Native actual QPE schedule and component binding on small source programs.

Finite H equations and independent provider equations remain explicit. This
component does not perform whole-artifact checking or issue a named receipt.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import hashlib
import json
from pathlib import Path

from compile_sized_corpus import Operation
from compile_sized_instrument import compile_instrument
from probe_hierarchical_qft_cost import array, interface
from test_hierarchical_artifact import ROOT, build_and_run
from test_hierarchical_circuit_trace import source_atoms
from test_hierarchical_routed_power import definitions_only, source_stages
from test_hierarchical_wiring import closure
from test_sized_instrument import sources

PRELUDE = '''import QleisliKernel.Hierarchical.QpeSchedule
open QleisliKernel.Hierarchical Artifact
set_option maxRecDepth 20000
def change (a : Artifact) (index : Nat) (body : Body) : Artifact :=
  {a with definitions := a.definitions.mapIdx (fun i d => if i==index then {d with body:=body} else d)}
def report (name : String) (a : Artifact) (r : QpeSchedule.Request)
    (c : QpeSchedule.Candidate) (remaining : Nat) : IO Unit := do
  match QpeSchedule.inspect a r c remaining with
  | .error e => IO.println s!"{name}|{repr e}"
  | .ok p => IO.println s!"{name}|pending|{p.visits}|{p.parts.values.length}|{p.inverse.fourier.body.requests.length}"
def budgets (a : Artifact) (r : QpeSchedule.Request) (c : QpeSchedule.Candidate) : IO Unit := do
  let .ok p := QpeSchedule.inspect a r c 2000000 |
    throw <| IO.userError "baseline failed"
  report "exact-budget" a r c p.visits
  report "short-budget" a r c (p.visits-1)
'''


def fixture(graph, n, m):
    selected, order = source_atoms(graph)
    definitions = graph['definitions']
    hs = [i for i in selected if definitions[i]['body']['tag'] == 'leaf']
    stages = source_stages(graph)
    inverse, = [i for i in selected if definitions[i]['body']['tag'] == 'inverse']
    forward = definitions[inverse]['body']['definition']
    children = definitions[forward]['body']['children']
    fourier_order = closure(graph, [children[0], *children[2:]])
    assert len(hs) == len(stages) == m
    phase = list(range(n+m-1, n-1, -1))
    target = list(range(n))
    request = ('⟨' + interface(definitions[graph['entry']['implementation']]['interface']) +
               f',{array(phase)},{array(target)},{array(phase+target)},{stages[0]["provider"]}⟩')
    def atom(i):
        return f'⟨{i},{interface(definitions[i]["interface"])}⟩'
    candidate = ('⟨' + array(atom(i) for i in hs) + ',' +
                 array(atom(s['index']) for s in stages) + ',' + atom(inverse) + ',' +
                 array(order) + ',' + array(array(s['routes']) for s in stages) + ',' +
                 array(fourier_order) + '⟩')
    return request, candidate, dict(hs=hs, stages=stages, inverse=inverse, forward=forward)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    code, calls, expected, metadata, graphs = PRELUDE, [], {}, {}, {}
    for name, n, m in [('small', 1, 2), ('target2', 2, 2), ('precision3', 1, 3), ('target2precision4', 2, 4)]:
        proposal = compile_instrument(sources(), 'measurement::qpe', dict(n=n, m=m),
                                      {'U': Operation('evolution::evolve', (n, 1, 3))})
        graphs[name] = graph = proposal['graph']
        r, c, metadata[name] = fixture(graph, n, m)
        code += f'def {name} : Artifact := {definitions_only(graph)}\n'
        code += f'def request_{name} : QpeSchedule.Request := {r}\n'
        code += f'def candidate_{name} : QpeSchedule.Candidate := {c}\n'
        calls.append(f'report "{name}" {name} request_{name} candidate_{name} 2000000')
        expected[name] = 'pending'

    def add(name, artifact='small', request='request_small', candidate='candidate_small', remaining=2000000, status='contract'):
        calls.append(f'report "{name}" ({artifact}) ({request}) ({candidate}) {remaining}')
        expected[name] = status

    info = metadata['small']
    add('wrong-phase-order', request='{request_small with phase:=#[1,2]}')
    add('wrong-result-route', request='{request_small with route:=#[0,1,2]}')
    add('duplicate-coordinate', request='{request_small with phase:=#[2,2]}')
    add('wrong-provider', request=f'{{request_small with provider:={info["hs"][0]}}}')
    add('wrong-power-order', candidate='{candidate_small with powers:=candidate_small.powers.reverse}')
    add('wrong-h-order', candidate='{candidate_small with hadamards:=candidate_small.hadamards.reverse}')
    add('missing-h', candidate='{candidate_small with hadamards:=#[]}')
    add('missing-power-route', candidate='{candidate_small with powerOrders:=#[#[],#[]]}')
    add('missing-fourier-route', candidate='{candidate_small with fourierOrder:=#[]}')
    add('missing-trace', candidate='{candidate_small with traceOrder:=#[]}')
    stage = info['stages'][1]
    add('wrong-power-count', artifact=f'change small {stage["core"]} (.repeatOp 3 {stage["provider"]})')
    add('wrong-control-polarity', artifact=f'change small {stage["index"]} (.control {stage["child"]} false)')
    add('forward-for-inverse', artifact=f'change small {info["inverse"]} (.repeatOp 1 {info["forward"]})')
    add('hidden-phase', artifact=f'change small {stage["routes"][0]} (.dyadicPhase 0 1 3)')
    add('wrong-target-order', artifact='target2', request='{request_target2 with target:=#[1,0]}', candidate='candidate_target2')
    add('zero-budget', remaining=0, status='limit')
    add('reset-budget', remaining=2000001, status='limit')
    # Finite bytes are retained, not accepted by this component. Exact H checking
    # must reject this request before a result could ever become evidence.
    add('unresolved-finite-bytes', artifact=f'change small {info["hs"][0]} (.leaf "not-an-H-packet".toUTF8)', status='pending')
    calls.append('budgets small request_small candidate_small')
    expected.update({'exact-budget': 'pending', 'short-budget': 'limit'})
    code += 'def main : IO Unit := do\n' + ''.join('  '+c+'\n' for c in calls)
    commands, binary = build_and_run(code, args.record)
    results = {}
    for line in commands[-1]['stdout'].splitlines():
        name, *fields = line.split('|')
        assert name not in results
        results[name] = fields
    assert results.keys() == expected.keys(), (results.keys(), expected.keys())
    for name, status in expected.items():
        assert results[name][0].rsplit('.', 1)[-1] == status, (name, results[name], status)
    report = dict(format='qleisli.qpe-schedule-validation', version=1, status='passed',
                  native_cases=len(results), results=results,
                  source_sha256=hashlib.sha256(code.encode()).hexdigest(), binary_sha256=binary,
                  kernel_source_sha256=hashlib.sha256((ROOT/'lean-kernel/QleisliKernel/Hierarchical/QpeSchedule.lean').read_bytes()).hexdigest(),
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), commands=commands,
                  finite_h_equations_discharged=False, independent_provider_bound=False,
                  named_qpe_instrument=False, production_integration=False)
    if args.record:
        args.record.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ('results', 'commands')}))


if __name__ == '__main__':
    main()
