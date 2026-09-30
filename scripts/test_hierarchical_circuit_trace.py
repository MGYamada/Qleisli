#!/usr/bin/env python3
"""Actual shared-circuit routing/events and phase-sensitive reconstruction.

Atoms retain independent semantic obligations. A successful trace does not
certify Hadamard, provider powers, inverse Fourier or a named QPE instrument.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import copy
import hashlib
import json
import math
from pathlib import Path

from compile_sized_corpus import Operation
from compile_sized_instrument import compile_instrument
from probe_hierarchical_qft_cost import array, interface
from test_hierarchical_artifact import ROOT, build_and_run
from test_hierarchical_routed_power import definitions_only
from test_sized_corpus import circuit_action, difference
from test_sized_instrument import sources


def source_atoms(graph):
    """Untrusted fixture selection: stop at requested leaf/control/inverse nodes."""
    definitions, seen, atoms, order = graph['definitions'], set(), [], []

    def walk(index):
        if index in seen:
            return
        seen.add(index)
        body = definitions[index]['body']
        if body['tag'] in ('leaf', 'control', 'inverse'):
            atoms.append(index)
        elif body['tag'] == 'sequence':
            for child in body['children']:
                walk(child)
        elif body['tag'] == 'tensor':
            walk(body['left'])
            walk(body['right'])
        else:
            assert body['tag'] in ('structural', 'rewire'), body
        order.append(index)
    walk(graph['entry']['implementation'])
    return atoms, order


def reconstruct(graph, route, events):
    """Global coordinate-local operators; no graph routing is reused here."""
    width = len(route)
    atoms = {}
    for index, positions in events:
        action, _ = circuit_action(dict(graph, entry=dict(implementation=index, proof=0)))
        atoms[index] = [action({column: 1}) for column in range(1 << len(positions))]

    def action(state):
        for index, positions in events:
            next_state = {}
            clear = sum(1 << position for position in positions)
            for value, amplitude in state.items():
                local = sum(((value >> position) & 1) << j for j, position in enumerate(positions))
                for output, coefficient in atoms[index][local].items():
                    result = value & ~clear
                    result |= sum(((output >> j) & 1) << position for j, position in enumerate(positions))
                    next_state[result] = next_state.get(result, 0) + coefficient * amplitude
            state = next_state
        return {sum(((value >> position) & 1) << j for j, position in enumerate(route)): amplitude
                for value, amplitude in state.items()}
    return width, action


PRELUDE = '''import QleisliKernel.Hierarchical.CircuitTrace
open QleisliKernel.Hierarchical Artifact
set_option maxRecDepth 20000
def change (a : Artifact) (index : Nat) (body : Body) : Artifact :=
  {a with definitions := a.definitions.mapIdx (fun i d => if i==index then {d with body:=body} else d)}
def report (name : String) (a : Artifact) (atoms : Array CircuitTrace.Atom)
    (order : Array Nat) (remaining : Nat) : IO Unit := do
  match CircuitTrace.inspect a atoms order remaining with
  | .error e => IO.println s!"{name}|{repr e}"
  | .ok p =>
    let some trace := (p.cache[a.entry.implementation]?).bind id |
      throw <| IO.userError "entry trace absent"
    let route := String.intercalate "," (trace.route.map toString)
    let events := String.intercalate ";" (trace.events.toList.map fun event =>
      s!"{event.atom}:" ++ String.intercalate "," (event.positions.map toString))
    IO.println s!"{name}|pending|{p.visits}|{trace.width}|{route}|{events}"
def budgets (a : Artifact) (atoms : Array CircuitTrace.Atom) (order : Array Nat) : IO Unit := do
  let .ok p := CircuitTrace.inspect a atoms order 2000000 |
    throw <| IO.userError "baseline did not inspect"
  report "budget-exact" a atoms order p.visits
  report "budget-short" a atoms order (p.visits-1)
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    source, calls, expected, graphs, metadata = PRELUDE, [], {}, {}, {}
    for name, n, m in [('small', 1, 2), ('target2', 2, 2), ('precision3', 1, 3), ('target2precision4', 2, 4)]:
        proposal = compile_instrument(sources(), 'measurement::qpe', dict(n=n, m=m),
                                      {'U': Operation('evolution::evolve', (n, 1, 3))})
        graph = graphs[name] = proposal['graph']
        atoms, order = metadata[name] = source_atoms(graph)
        source += f'def {name} : Artifact := {definitions_only(graph)}\n'
        source += f'def atoms_{name} : Array CircuitTrace.Atom := ' + array(
            f'⟨{index},{interface(graph["definitions"][index]["interface"])}⟩' for index in atoms) + '\n'
        source += f'def order_{name} : Array Nat := {array(order)}\n'
        calls.append(f'report "{name}" {name} atoms_{name} order_{name} 2000000')
        expected[name] = 'pending'

    atoms, order = metadata['small']
    graph = graphs['small']
    root = graph['entry']['implementation']
    route = graph['definitions'][root]['body']['children'][0]

    def add(name, artifact='small', atom_expr='atoms_small', order_expr='order_small',
            remaining=2000000, status='contract'):
        calls.append(f'report "{name}" ({artifact}) ({atom_expr}) ({order_expr}) {remaining}')
        expected[name] = status

    add('hidden-phase', f'change small {route} (.dyadicPhase 0 1 3)')
    add('duplicate-route-axis', f'change small {route} (.rewire ⟨#[1,2,0],#[0,0,2],#[]⟩)')
    add('atom-signature', atom_expr='atoms_small.map fun atom => {atom with interface := ⟨⟨#[],#[]⟩,⟨#[],#[]⟩⟩}')
    add('duplicate-atom', atom_expr='atoms_small++atoms_small')
    add('missing-atom', atom_expr='atoms_small.extract 1 atoms_small.size')
    add('missing-child', order_expr=array(order[1:]))
    add('reversed-order', order_expr=array(list(reversed(order))))
    add('duplicate-definition', order_expr='order_small++order_small', status='invalidIr')
    add('zero-budget', remaining=0, status='limit')
    add('excess-budget', remaining=2000001, status='limit')
    # Atom internals remain obligations. Opaque repetition is not expanded.
    add('opaque-large-repeat', f'change small {atoms[-1]} (.repeatOp 4294967295 {atoms[0]})', status='pending')
    changed = copy.deepcopy(graph)
    changed['definitions'][route]['body']['permutation']['axes'] = [2, 1, 0]
    graphs['permuted-route'] = changed
    source += f'def permuted : Artifact := {definitions_only(changed)}\n'
    add('permuted-route', 'permuted', status='pending')
    # A small shared DAG describes exponential event duplication. Precharge
    # must reject growth before materializing the next event array.
    header = interface(graph['definitions'][atoms[0]]['interface'])
    source += f'def growthHeader : Interface := {header}\n'
    source += 'def growth : Artifact := ⟨#[⟨growthHeader,.unitary,.leaf ByteArray.empty⟩] ++ '
    source += '(Array.range 60).map (fun i => ⟨growthHeader,.unitary,.sequence #[i,i]⟩),'
    source += '#[],#[],#[],⟨60,0⟩⟩\n'
    add('event-growth-precharge', 'growth', atom_expr='#[⟨0,growthHeader⟩]',
        order_expr='Array.range 61', status='limit')
    calls.append('budgets small atoms_small order_small')
    expected.update({'budget-exact': 'pending', 'budget-short': 'limit'})
    source += 'def main : IO Unit := do\n' + ''.join('  '+call+'\n' for call in calls)
    commands, binary_hash = build_and_run(source, args.record)
    results = {}
    for line in commands[-1]['stdout'].splitlines():
        name, *fields = line.split('|')
        assert name not in results
        results[name] = fields
    assert results.keys() == expected.keys(), (results.keys(), expected.keys())
    for name, status in expected.items():
        assert results[name][0].rsplit('.', 1)[-1] == status, (name, results[name], status)
    probes = {}
    for name, graph in graphs.items():
        row = results[name]
        route = list(map(int, row[3].split(',')))
        events = [(int(event.split(':')[0]), list(map(int, event.split(':')[1].split(','))))
                  for event in row[4].split(';')]
        width, reconstructed = reconstruct(graph, route, events)
        actual, _ = circuit_action(graph)
        inputs = [{i: 1} for i in range(1 << width)] + [
            {i: complex(i % 3-1, (i+1) % 4-2)/math.sqrt(10*(1 << width)) for i in range(1 << width)}]
        maximum = max(difference(actual(state), reconstructed(state)) for state in inputs)
        assert maximum < 1e-12, (name, maximum)
        probes[name] = dict(coefficients=len(inputs)*(1 << width), maximum_error=maximum,
                            route=route, events=events)
    report = dict(format='qleisli.circuit-trace-validation', version=1, status='passed',
                  native_cases=len(results), results=results, coefficient_probes=probes,
                  phase_sensitive_coefficients=sum(p['coefficients'] for p in probes.values()),
                  maximum_error=max(p['maximum_error'] for p in probes.values()),
                  source_sha256=hashlib.sha256(source.encode()).hexdigest(), binary_sha256=binary_hash,
                  kernel_source_sha256=hashlib.sha256((ROOT/'lean-kernel/QleisliKernel/Hierarchical/CircuitTrace.lean').read_bytes()).hexdigest(),
                  mathlib_source_sha256=hashlib.sha256((ROOT/'lean/Qleisli/HierarchicalCircuitTrace.lean').read_bytes()).hexdigest(),
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), commands=commands,
                  atom_equations_discharged=False, named_qpe_binding=False, production_integration=False)
    if args.record:
        args.record.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ('commands', 'results', 'coefficient_probes')}))


if __name__ == '__main__':
    main()
