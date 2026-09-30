#!/usr/bin/env python3
"""Actual source controlled-power components, fresh routes and complex oracles.

The native result is a component obligation, not provider evidence or named QPE
acceptance. Provider matrices below are independent diagnostic formulas only.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import cmath
import copy
import hashlib
import json
import math
from pathlib import Path

from compile_sized_corpus import Operation
from compile_sized_instrument import compile_instrument
from probe_hierarchical_qft_cost import array, body as original_body, interface
from test_hierarchical_artifact import ROOT, build_and_run
from test_sized_corpus import circuit_action, difference
from test_sized_instrument import sources


def body(value):
    if value['tag'] == 'inverse':
        return f'.inverse {value.get("definition", value.get("child"))}'
    if value['tag'] == 'structural':
        operation = value['operation']
        if operation['tag'] in ('bit_to_bits', 'bits_to_bit'):
            return '.structural .' + {'bit_to_bits': 'bitToBits', 'bits_to_bit': 'bitsToBit'}[operation['tag']]
    return original_body(value)


def definitions_only(graph):
    # The local inspector reads only definitions. It cannot use empty proof or
    # meaning tables to issue whole-artifact evidence.
    definitions = array(f'⟨{interface(d["interface"])},.unitary,{body(d["body"])}⟩'
                        for d in graph['definitions'])
    return f'⟨{definitions},#[],#[],#[],⟨{graph["entry"]["implementation"]},0⟩⟩'


def source_stages(graph):
    """Fixture discovery only; neither this selector nor its indices are trusted."""
    definitions = graph['definitions']
    found = []

    def walk(index):
        value = definitions[index]['body']
        if value['tag'] == 'inverse':
            return
        if value['tag'] == 'control':
            child = value['definition']
            shell = definitions[child]['body']
            enter, core, leave = shell['children']
            inner = definitions[core]['body']
            provider, count = ((inner['definition'], inner['count'])
                               if inner['tag'] == 'repeat' else (core, 1))
            found.append(dict(index=index, child=child, core=core, provider=provider,
                              count=count, routes=[enter, leave]))
        elif value['tag'] == 'sequence':
            for child in value['children']:
                walk(child)
        elif value['tag'] == 'tensor':
            walk(value['left'])
            walk(value['right'])
    walk(graph['entry']['implementation'])
    assert [s['count'] for s in found] == [2**i for i in range(len(found))]
    assert len({s['provider'] for s in found}) == 1
    return found


def coefficients(graph, stage, width, exponent, global_sign=False, changed=False):
    local = dict(graph, entry=dict(implementation=stage['index'], proof=0))
    actual, _ = circuit_action(local)
    size = 1 << (width+1)
    columns = [{i: 1} for i in range(size)] + [
        {i: complex(i % 3-1, (i+1) % 4-2)/math.sqrt(10*size) for i in range(size)}]
    maximum = 0.0
    for column in columns:
        expected = {i: amplitude*(
            ((-1)**(2**exponent) if global_sign else
             cmath.exp(2j*math.pi*((i >> 1) & 1)*(2**exponent)/8)) if i & 1 else 1)
            for i, amplitude in column.items()}
        maximum = max(maximum, difference(actual(column), expected))
    assert (maximum > 0.1 if changed else maximum < 1e-12), maximum
    return dict(coefficients=len(columns)*size, maximum_error=maximum,
                expected='different' if changed else 'equal')


PRELUDE = '''import QleisliKernel.Hierarchical.RoutedPower
open QleisliKernel.Hierarchical Artifact
set_option maxRecDepth 20000
def change (a : Artifact) (index : Nat) (body : Body) : Artifact :=
  {a with definitions := a.definitions.mapIdx (fun i d => if i==index then {d with body:=body} else d)}
def report (name : String) (a : Artifact) (index : Nat) (request : RoutedPower.Request)
    (order : Array Nat) (remaining : Nat) : IO Unit := do
  match RoutedPower.inspect a index request order remaining with
  | .error e => IO.println s!"{name}|{repr e}"
  | .ok p => IO.println s!"{name}|pending|{p.visits}"
def budgets (name : String) (a : Artifact) (index : Nat) (request : RoutedPower.Request)
    (order : Array Nat) : IO Unit := do
  let .ok p := RoutedPower.inspect a index request order 2000000 |
    throw <| IO.userError "baseline did not inspect"
  report (name++"-exact") a index request order p.visits
  report (name++"-short") a index request order (p.visits-1)
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    modules = sources()
    signed = modules | {'evolution': modules['evolution'].replace(
        'use std::quantum::phase;', 'use std::quantum::phase;\nuse std::quantum::x;').replace(
        'phase[j,d](bit)', 'phase[1,1](x(phase[1,1](x(bit))))')}
    graphs, stages, probes = {}, {}, {}
    source = PRELUDE
    calls, expected = [], {}
    for key, n, m, module_set in [('small', 1, 2, modules), ('wide', 2, 2, modules),
                                   ('precision3', 1, 3, modules), ('signed', 1, 2, signed)]:
        proposal = compile_instrument(module_set, 'measurement::qpe', dict(n=n, m=m),
                                      {'U': Operation('evolution::evolve', (n, 1, 3))})
        graph = proposal['graph']
        graphs[key], stages[key] = graph, source_stages(graph)
        source += f'def {key} : Artifact := {definitions_only(graph)}\n'
        for exponent, stage in enumerate(stages[key]):
            name = f'{key}-{exponent}'
            header = interface(graph['definitions'][stage['index']]['interface'])
            source += f'def request_{key}_{exponent} : RoutedPower.Request := ⟨{n},{exponent},{stage["provider"]},{header}⟩\n'
            calls.append(f'report "{name}" {key} {stage["index"]} request_{key}_{exponent} {array(stage["routes"])} 2000000')
            expected[name] = 'pending'
            probes[name] = coefficients(graph, stage, n, exponent, global_sign=key == 'signed')

    first, second = stages['small']
    wide = stages['wide'][0]
    def add(name, artifact='small', index=None, request='request_small_0', order=None,
            remaining=2000000, status='contract'):
        if index is None:
            index = first['index']
        if order is None:
            order = array(first['routes'])
        calls.append(f'report "{name}" ({artifact}) {index} ({request}) ({order}) {remaining}')
        expected[name] = status

    add('direct-one-sequence-provider', f'change small {first["index"]} (.control {first["provider"]} true)',
        order='#[]', status='pending')
    add('direct-one-wrong-request', f'change small {first["index"]} (.control {first["provider"]} true)',
        request='{request_small_0 with exponent:=1}', order='#[]')
    add('wrong-exponent', request='{request_small_0 with exponent:=1}')
    add('wrong-provider', request=f'{{request_small_0 with provider:={first["routes"][0]}}}')
    add('wrong-polarity', f'change small {first["index"]} (.control {first["child"]} false)')
    add('wrong-count', f'change small {second["core"]} (.repeatOp 3 {second["provider"]})',
        second['index'], 'request_small_1', array(second['routes']))
    add('wrong-count-provider', f'change small {second["core"]} (.repeatOp 2 {first["routes"][0]})',
        second['index'], 'request_small_1', array(second['routes']))
    add('hidden-shell-phase', f'change small {first["routes"][0]} (.dyadicPhase 0 1 3)')
    add('shell-permutation', f'change wide {wide["routes"][0]} (.rewire ⟨#[0],#[1,0],#[]⟩)',
        wide['index'], 'request_wide_0', array(wide['routes']))
    add('missing-route', order='#[]')
    add('duplicate-route', order=array(first['routes']*2), status='invalidIr')
    add('missing-root', index=999999)
    add('wrong-full-interface', request='{request_small_0 with interface:=request_wide_0.interface}')
    add('outside-budget', remaining=2000001, status='limit')
    add('zero-budget', remaining=0, status='limit')
    add('outside-exponent', request='{request_small_0 with exponent:=13}', status='limit')
    add('outside-provider', request='{request_small_0 with provider:=4294967296}', status='limit')
    # Provider contents are deliberately *not* certified here. Mutation remains
    # pending and changes the independently computed operator, demonstrating why
    # its actual-byte/request equation must be discharged before sealing evidence.
    changed = copy.deepcopy(graphs['small'])
    phase = next(i for i, d in enumerate(changed['definitions'])
                 if d['body']['tag'] == 'dyadic_phase')
    changed['definitions'][phase]['body']['j'] = 2
    source += f'def changedProvider : Artifact := {definitions_only(changed)}\n'
    add('provider-phase-obligation', 'changedProvider', status='pending')
    probes['provider-phase-obligation'] = coefficients(changed, first, 1, 0, changed=True)
    calls.append(f'budgets "shared-budget" small {first["index"]} request_small_0 {array(first["routes"])}')
    expected['shared-budget-exact'] = 'pending'
    expected['shared-budget-short'] = 'limit'
    source += 'def main : IO Unit := do\n' + ''.join('  '+call+'\n' for call in calls)
    commands, binary_hash = build_and_run(source, args.record)
    results = {}
    for line in commands[-1]['stdout'].splitlines():
        name, *fields = line.split('|')
        assert name not in results
        results[name] = fields
    assert set(results) == set(expected)
    for name, status in expected.items():
        observed = results[name][0].rsplit('.', 1)[-1]
        assert observed == status, (name, results[name], status)
        if status == 'pending':
            assert 0 < int(results[name][1]) <= 2000000
    report = dict(format='qleisli.routed-power-validation', version=1, status='passed',
                  native_cases=len(results), results=results, coefficient_probes=probes,
                  phase_sensitive_coefficients=sum(p['coefficients'] for p in probes.values()),
                  maximum_accepted_error=max(p['maximum_error'] for p in probes.values()
                                             if p['expected'] == 'equal'),
                  source_sha256=hashlib.sha256(source.encode()).hexdigest(), binary_sha256=binary_hash,
                  kernel_source_sha256=hashlib.sha256((ROOT/'lean-kernel/QleisliKernel/Hierarchical/RoutedPower.lean').read_bytes()).hexdigest(),
                  mathlib_source_sha256=hashlib.sha256((ROOT/'lean/Qleisli/HierarchicalRoutedPower.lean').read_bytes()).hexdigest(),
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  commands=commands, provider_equation_discharged=False,
                  named_qpe_binding=False, production_integration=False)
    if args.record:
        args.record.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ('commands', 'results', 'coefficient_probes')}))


if __name__ == '__main__':
    main()
