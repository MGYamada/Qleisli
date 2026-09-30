#!/usr/bin/env python3
"""Actual fresh-zero nodes versus an independent coefficient/reference oracle.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import struct

from test_hierarchical_artifact import ROOT, build_and_run
from test_hierarchical_readout import PRELUDE, side
from instrument_transport import encode_preparation, inspect


def simple_side(value):
    value = copy.deepcopy(value)
    for port in value['quantum']+value['classical']:
        atom, = port['basis']
        port['basis'] = atom['tag']+(f' {atom["width"]}' if atom['tag'] == 'bits' else '')
    return value


def base(width):
    inputs = dict(quantum=[dict(owner=10, basis=[dict(tag='bit')], axes=[41]),
                          dict(owner=11, basis=[dict(tag='unit')], axes=[]),
                          dict(owner=12, basis=[dict(tag='bits', width=0)], axes=[])],
                  classical=[dict(value=60, basis=[dict(tag='bits', width=2)])])
    fresh = [dict(owner=30+i, basis=[dict(tag='bit')], axes=[7+3*i]) for i in range(width)]
    request = dict(inputs=inputs, fresh=fresh)
    current, definitions = copy.deepcopy(inputs), []
    for port in fresh:
        after = dict(quantum=current['quantum']+[port], classical=current['classical'])
        definitions.append(dict(interface=dict(inputs=current, outputs=after),
                                effect='iso', body=dict(tag='init0', output=port['owner'])))
        current = after
    packet = dict(initializations=definitions, outputs=current)
    return json.loads(json.dumps(request)), json.loads(json.dumps(packet))


def cases():
    rows = [dict(name=f'fresh-{width}', request=r, packet=p, status='checked', budget=2000000)
            for width in range(4) for r, p in [base(width)]]
    request, packet = base(2)

    def mutate(name, change):
        r, p = copy.deepcopy((request, packet))
        change(r, p)
        rows.append(dict(name=name, request=r, packet=p, status='contract', budget=2000000))

    mutate('wrong-required-axis', lambda r, p: r['fresh'][0].__setitem__('axes', [6]))
    mutate('wrong-required-owner', lambda r, p: r['fresh'][0].__setitem__('owner', 200))
    mutate('implicit-bits1', lambda r, p: r['fresh'][0].__setitem__('basis', [dict(tag='bits', width=1)]))
    mutate('reordered-request', lambda r, p: r['fresh'].reverse())
    mutate('missing-node', lambda r, p: p['initializations'].pop())
    mutate('reordered-nodes', lambda r, p: p['initializations'].reverse())
    mutate('wrong-body', lambda r, p: p['initializations'][0].__setitem__('body', dict(tag='observe_z', input=10, output=55)))
    mutate('wrong-effect', lambda r, p: p['initializations'][0].__setitem__('effect', 'unitary'))
    mutate('aliased-input-axis', lambda r, p: r['inputs']['quantum'][1].__setitem__('axes', [41]))
    mutate('aliased-new-owner', lambda r, p: p['initializations'][0]['body'].__setitem__('output', 10))
    mutate('alter-existing-classical', lambda r, p: p['outputs']['classical'][0].__setitem__('value', 61))
    mutate('drop-empty-owner', lambda r, p: p['outputs']['quantum'].pop(2))
    mutate('drop-existing-target', lambda r, p: p['outputs']['quantum'].pop(0))
    mutate('alter-input-frame', lambda r, p: p['initializations'][0]['interface']['inputs']['quantum'][0].__setitem__('axes', [40]))
    mutate('broken-chain', lambda r, p: p['initializations'][1]['interface']['inputs']['quantum'].pop())
    mutate('wrong-intermediate-output', lambda r, p: p['initializations'][0]['interface']['outputs']['quantum'][-1].__setitem__('axes', [8]))
    for name, budget in [('zero-budget', 0), ('budget-excess', 2000001)]:
        rows.append(dict(name=name, request=request, packet=packet, status='limit', budget=budget))
    return rows


def lean_request(request):
    fresh = side(simple_side(dict(quantum=request['fresh'], classical=[])))
    return f'⟨{side(simple_side(request["inputs"]))},({fresh} : Side).quantum⟩'


def lean_packet(packet):
    nodes = []
    for d in packet['initializations']:
        b = d['body']
        body = f'.init0 {b["output"]}' if b['tag'] == 'init0' else f'.observeZ {b["input"]} {b["output"]}'
        h = d['interface']
        nodes.append(f'⟨⟨{side(simple_side(h["inputs"]))},{side(simple_side(h["outputs"]))}⟩,.{d["effect"]},{body}⟩')
    return f'⟨#[{",".join(nodes)}],{side(simple_side(packet["outputs"]))}⟩'


REPORT = r'''
def prepareReport (name : String) (request : Preparation.Request) (packet : Preparation.Packet)
    (budget : Nat) : IO Unit := do
  match Preparation.check request packet budget with
  | .error e => IO.println s!"{name}|{match e with | .limit => "limit" | .invalidIr => "invalid_ir" | .contract => "contract"}"
  | .ok checked =>
    let original := Preparation.headerCharge request packet + 64 * (1 + request.fresh.size) *
      (1 + sideCharge request.inputs + sideCharge packet.outputs +
        request.fresh.foldl (fun n p => n + p.basis.size + p.axes.size) 0 +
        packet.initializations.foldl (fun n d => n + d.interface.charge) 0)
    let atOriginal := match Preparation.check request packet original with
      | .ok same => same.visits == checked.visits | _ => false
    let atExact := match Preparation.check request packet checked.visits with
      | .ok same => same.visits == checked.visits | _ => false
    let below := match Preparation.check request packet (checked.visits-1) with
      | .error .limit => true | _ => false
    unless checked.visits ≤ original && atOriginal && atExact && below do
      throw (IO.userError s!"preparation accounting boundary: {name}")
    let actual := (packet.initializations.mapM Preparation.project).getD #[]
    let axes := (wires ⟨actual,#[]⟩).toList
    let inputs := (wires request.inputs).toList
    let outputs := (wires packet.outputs).toList
    let mut values : Array String := #[]
    for label in List.range (2^outputs.length) do
      for reference in List.range 2 do
        let coordinate := fun axis => bit label (outputs.idxOf axis)
        let oldLabel := fun (state : Nat → Bool) => (inputs.zipIdx).foldl
          (fun n (axis,i) => n + if state axis then 2^i else 0) 0
        let real := Semantics.Preparation.sequential axes (fun state ref => (coefficient (oldLabel state) ref).1) coordinate reference
        let imag := Semantics.Preparation.sequential axes (fun state ref => (coefficient (oldLabel state) ref).2) coordinate reference
        values := values.push s!"[{label},{reference},{real},{imag}]"
    IO.println s!"{name}|checked|{checked.visits}|[{String.intercalate "," values.toList}]|{original}"
'''


def test_zero_reference(rows, results):
    probes = 0
    for row in rows:
        fields = results[row['name']]
        assert fields[0] == row['status'], (row['name'], fields)
        if row['status'] != 'checked':
            continue
        expected = []
        for label in range(1 << (1+len(row['request']['fresh']))):
            for reference in range(2):
                old = label & 1
                z = [(-1 if old else 1)*(old+2*reference+1), 3*old-5*reference] if label < 2 else [0, 0]
                expected.append([label, reference, *z])
        assert json.loads(fields[2]) == expected, row['name']
        original, current = int(fields[3]), int(fields[1])
        assert current <= original
        assert (current < original) == bool(row['request']['fresh'])
        probes += len(expected)
    return probes


def test_preparation_transport(rows, results, kernel):
    for row in rows:
        observed = inspect(kernel, 'preparation', encode_preparation(row['request'], row['packet'], row['budget']))
        assert observed['status'] == row['status'], (row['name'], observed)
        if row['status'] == 'checked':
            assert observed['work'] == int(results[row['name']][1])
    r, p = base(1)
    good = encode_preparation(r, p)
    malformed = [b'', b'QLZ2'+good[4:], good[:-1], good+b'\0', b'QLZ1'+struct.pack('<I', 100001)]
    for i, payload in enumerate(malformed):
        assert inspect(kernel, 'preparation', payload)['status'] == ('format' if i < 4 else 'limit')
    r['fresh'][0]['owner'] = 2**32
    try:
        encode_preparation(r, p)
    except ValueError:
        pass
    else:
        raise AssertionError('transport truncated u32')
    return len(malformed)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    rows, source = cases(), PRELUDE+REPORT
    for i, row in enumerate(rows):
        source += f'def case{i} : IO Unit := prepareReport {json.dumps(row["name"])} ({lean_request(row["request"])}) ({lean_packet(row["packet"])}) {row["budget"]}\n'
    source += 'def main : IO Unit := do\n'+'\n'.join(f'  case{i}' for i in range(len(rows)))+'\n'
    commands, binary_hash = build_and_run(source, args.record)
    results = {}
    for line in commands[-1]['stdout'].splitlines():
        name, *fields = line.split('|')
        assert name not in results
        results[name] = fields
    assert len(results) == len(rows)
    probes = test_zero_reference(rows, results)
    kernel = ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel'
    malformed = test_preparation_transport(rows, results, kernel)
    report = dict(format='qleisli.preparation-validation', version=1, status='passed',
        cases=len(rows), coefficient_probes=probes, malformed_frames=malformed,
        max_fresh_qubits=3, max_total_qubits=4, production_integration=False,
        binary_sha256=binary_hash, kernel_sha256=hashlib.sha256(kernel.read_bytes()).hexdigest(),
        commands=commands, results=results,
        accounting=[dict(case=row['name'],original=int(results[row['name']][3]),
            current=int(results[row['name']][1]),exact_threshold_checked=True)
            for row in rows if row['status']=='checked'],
        source_sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in (
            'lean-kernel/QleisliKernel/Semantics/Preparation.lean',
            'lean-kernel/QleisliKernel/Hierarchical/Preparation.lean',
            'scripts/instrument_transport.py', 'scripts/test_hierarchical_preparation.py')})
    if args.record:
        args.record.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('commands','results','source_sha256')}))


if __name__ == '__main__':
    main()
