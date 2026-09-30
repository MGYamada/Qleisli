#!/usr/bin/env python3
"""Actual readout nodes versus an independent small branch/bit-order oracle.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
This checks the readout component, not a QPE receipt or production integration.
"""
import argparse
import copy
import hashlib
import itertools
import json
from pathlib import Path
import struct
import subprocess

from test_hierarchical_artifact import ROOT, build_and_run


def base(width, order=None):
    owners = [13 + 5 * i for i in range(width)]
    inputs = dict(quantum=[dict(owner=o, basis='bit', axes=[7 + 3 * i])
                           for i, o in enumerate(owners)] + [
        dict(owner=501, basis='bit', axes=[89]),
        dict(owner=502, basis='unit', axes=[]),
        dict(owner=503, basis='bits 0', axes=[])],
        classical=[dict(value=991, basis='bits 2')])
    selected = owners if order is None else [owners[i] for i in order]
    request = dict(inputs=inputs, owners=selected, result=900)
    before, measurements, names = copy.deepcopy(inputs), [], []
    for i, owner in enumerate(selected):
        value = 200 + 7 * i
        after = dict(quantum=[p for p in before['quantum'] if p['owner'] != owner],
                     classical=before['classical'] + [dict(value=value, basis='bit')])
        measurements.append(dict(inputs=before, outputs=after, effect='observe',
                                 owner=owner, value=value, body='observeZ'))
        before = after
        names.append(value)
    packet = dict(measurements=measurements, pack=names,
        outputs=dict(quantum=before['quantum'], classical=inputs['classical'] + [
            dict(value=900, basis=f'bits {width}')]))
    # Serialized proposals have no Python object aliases across headers.
    return json.loads(json.dumps(request)), json.loads(json.dumps(packet))


def cases():
    rows = []

    def add(name, request, packet, status='checked', budget=2000000):
        rows.append(dict(name=name, request=request, packet=packet, status=status, budget=budget))

    for width in range(4):
        for order in itertools.permutations(range(width)):
            request, packet = base(width, order)
            add(f'width-{width}-order-{order}', request, packet)
    request, packet = base(2)

    def mutate(name, change, status='contract'):
        r, p = copy.deepcopy((request, packet))
        change(r, p)
        add(name, r, p, status)

    mutate('reversed-pack', lambda r, p: p['pack'].reverse())
    mutate('duplicate-pack', lambda r, p: p['pack'].__setitem__(1, p['pack'][0]))
    mutate('stale-pack', lambda r, p: p['pack'].__setitem__(0, 991))
    mutate('missing-pack', lambda r, p: p['pack'].pop())
    mutate('wrong-request-order', lambda r, p: r['owners'].reverse())
    mutate('duplicate-request-owner', lambda r, p: r['owners'].__setitem__(1, r['owners'][0]))
    mutate('unknown-request-owner', lambda r, p: r['owners'].__setitem__(1, 333))
    mutate('request-empty-owner', lambda r, p: r['owners'].__setitem__(1, 503))
    mutate('result-alias', lambda r, p: r.__setitem__('result', 991))
    mutate('wrong-result-name', lambda r, p: r.__setitem__('result', 901))
    mutate('wrong-result-width', lambda r, p: p['outputs']['classical'][-1].__setitem__('basis', 'bits 1'))
    mutate('implicit-bits1', lambda r, p: r['inputs']['quantum'][0].__setitem__('basis', 'bits 1'))
    mutate('discard-empty-owner', lambda r, p: p['outputs']['quantum'].pop())
    mutate('discard-target', lambda r, p: p['outputs']['quantum'].pop(0))
    mutate('alter-target-axis', lambda r, p: p['outputs']['quantum'][0].__setitem__('axes', [88]))
    mutate('alter-classical-frame', lambda r, p: p['outputs']['classical'][0].__setitem__('basis', 'bit'))
    mutate('missing-measurement', lambda r, p: p['measurements'].pop())
    mutate('extra-measurement', lambda r, p: p['measurements'].append(copy.deepcopy(p['measurements'][0])))
    mutate('wrong-effect', lambda r, p: p['measurements'][0].__setitem__('effect', 'unitary'))
    mutate('wrong-body', lambda r, p: p['measurements'][0].__setitem__('body', 'init0'))
    mutate('wrong-measured-owner', lambda r, p: p['measurements'][0].__setitem__('owner', 501))
    mutate('wrong-measured-value', lambda r, p: p['measurements'][0].__setitem__('value', 991))
    mutate('reordered-nodes', lambda r, p: p['measurements'].reverse())
    mutate('broken-continuity', lambda r, p: p['measurements'][1]['inputs']['classical'].clear())
    mutate('aliased-axis', lambda r, p: r['inputs']['quantum'][1].__setitem__('axes', [7]))
    mutate('aliased-owner', lambda r, p: r['inputs']['quantum'][1].__setitem__('owner', 13))
    mutate('invalid-type-tree', lambda r, p: r['inputs']['quantum'][0].__setitem__('basis', 'tuple 2'))
    mutate('unbounded-label', lambda r, p: r['inputs']['quantum'][0].__setitem__('owner', 2**32))
    for name, budget in [('zero-budget', 0), ('profile-budget-excess', 2000001)]:
        add(name, request, packet, 'limit', budget)
    # Malformed header capacity probes, not maximum-size circuit generation.
    mutate('oversized-packing-header', lambda r, p: p.__setitem__('pack', [0]*100000), 'limit')
    empty_request, empty_packet = base(0)
    empty_packet['outputs']['classical'].pop()
    add('empty-result-must-exist', empty_request, empty_packet, 'contract')
    return rows


def array(values):
    return '#[' + ','.join(values) + ']'


def side(value):
    quantum = [f'⟨{p["owner"]},#[.{p["basis"]}],{array(map(str, p["axes"]))}⟩'
               for p in value['quantum']]
    classical = [f'⟨{p["value"]},#[.{p["basis"]}]⟩' for p in value['classical']]
    return f'⟨{array(quantum)},{array(classical)}⟩'


def render_request(value):
    return f'⟨{side(value["inputs"])},{array(map(str, value["owners"]))},{value["result"]}⟩'


def render_packet(value):
    definitions = []
    for d in value['measurements']:
        body = f'.observeZ {d["owner"]} {d["value"]}' if d['body'] == 'observeZ' else '.init0 0'
        definitions.append(f'⟨⟨{side(d["inputs"])},{side(d["outputs"])}⟩,.{d["effect"]},{body}⟩')
    pack = ('Array.replicate 100000 0' if len(value['pack']) == 100000
            else array(map(str, value['pack'])))
    return f'⟨{array(definitions)},{pack},{side(value["outputs"])}⟩'


PRELUDE = r'''import QleisliKernel
open QleisliKernel QleisliKernel.Hierarchical QleisliKernel.Hierarchical.Artifact
def bit (label index : Nat) : Bool := label / 2^index % 2 == 1
def coefficient (label reference : Nat) : Int × Int :=
  ((if label % 2 == 0 then 1 else -1) * (Int.ofNat label + 2 * Int.ofNat reference + 1),
    3 * Int.ofNat label - 5 * Int.ofNat reference)
def report (name : String) (request : Readout.Request) (packet : Readout.Packet)
    (budget : Nat) : IO Unit := do
  match Readout.check request packet budget with
  | .error e => IO.println s!"{name}|{match e with | .limit => "limit" | .invalidIr => "invalid_ir" | .contract => "contract"}"
  | .ok checked =>
    let original := Readout.headerCharge request packet +
      64 * (1 + request.owners.size + packet.pack.size) *
        (1 + sideCharge request.inputs + sideCharge packet.outputs +
          packet.measurements.foldl (fun n d => n + d.interface.charge) 0)
    let atOriginal := match Readout.check request packet original with
      | .ok same => same.visits == checked.visits | _ => false
    let atExact := match Readout.check request packet checked.visits with
      | .ok same => same.visits == checked.visits | _ => false
    let below := match Readout.check request packet (checked.visits-1) with
      | .error .limit => true | _ => false
    unless checked.visits ≤ original && atOriginal && atExact && below do
      throw (IO.userError s!"readout accounting boundary: {name}")
    let actual := (Readout.projected packet).getD #[]
    let axes := (actual.map (fun p => p.2.2)).toList
    let allAxes := (wires request.inputs).toList
    let residualAxes := (wires packet.outputs).toList
    let mut values : Array String := #[]
    for outcome in List.range (2^request.owners.size) do
      for residual in List.range (2^residualAxes.length) do
        for reference in List.range 2 do
          let input := fun (state : Nat → Bool) (ref : Nat) =>
            let label := (allAxes.zipIdx).foldl
              (fun n (axis, i) => n + if state axis then 2^i else 0) 0
            coefficient label ref
          let value := Semantics.Readout.sequential axes (bit outcome) input
            (fun axis => bit residual (residualAxes.idxOf axis)) reference
          let valueNames := (actual.map (fun p => p.2.1)).toList
          let packed := Readout.assemble packet (fun value => bit outcome (valueNames.idxOf value))
          values := values.push s!"[{outcome},{residual},{reference},{packed},{value.1},{value.2}]"
    IO.println s!"{name}|checked|{checked.visits}|[{String.intercalate "," values.toList}]|{original}"
'''


def expected_coefficients(request, packet):
    """Assign bits to original wire positions, independently of Lean substitution."""
    all_axes = [axis for p in request['inputs']['quantum'] for axis in p['axes']]
    residual_axes = [axis for p in packet['outputs']['quantum'] for axis in p['axes']]
    owners = {p['owner']: p['axes'][0] for p in request['inputs']['quantum'] if p['axes']}
    measured = [owners[owner] for owner in request['owners']]
    rows = []
    for outcome, residual, reference in itertools.product(
            range(1 << len(measured)), range(1 << len(residual_axes)), range(2)):
        assignment = {axis: (outcome >> i) & 1 for i, axis in enumerate(measured)}
        assignment.update({axis: (residual >> i) & 1 for i, axis in enumerate(residual_axes)})
        label = sum(assignment[axis] << i for i, axis in enumerate(all_axes))
        rows.append([outcome, residual, reference, outcome,
                     (-1 if label % 2 else 1) * (label + 2*reference + 1),
                     3*label - 5*reference])
    return rows


def test_native_rejections(rows, results):
    for row in rows:
        if row['status'] != 'checked':
            assert results[row['name']][0] == row['status'], (row['name'], results[row['name']])


def test_native_branches(rows, results):
    probes = 0
    for row in rows:
        if row['status'] != 'checked':
            continue
        status, *rest = results[row['name']]
        assert status == 'checked', (row['name'], status)
        expected = expected_coefficients(row['request'], row['packet'])
        assert json.loads(rest[1]) == expected, row['name']
        assert 0 < int(rest[0]) <= row['budget']
        original, current = int(rest[2]), int(rest[0])
        assert current <= original
        assert (current < original) == bool(row['request']['owners'])
        probes += len(expected)
    return probes


def bridge(request, packet, budget=2000000):
    """Untrusted private framing; checked u32 conversion never truncates labels."""
    data = bytearray(b'QLM1')

    def word(n):
        if type(n) is not int or not 0 <= n < 2**32:
            raise ValueError('readout transport u32 range')
        data.extend(struct.pack('<I', n))

    def array(values, emit):
        word(len(values))
        for value in values:
            emit(value)

    def basis(value):
        parts = value.split()
        word(1)
        word({'unit': 0, 'bit': 1, 'bits': 2, 'tuple': 3}[parts[0]])
        if len(parts) == 2:
            word(int(parts[1]))

    def side(value):
        def quantum(p):
            word(p['owner']); basis(p['basis']); array(p['axes'], word)
        def classical(p):
            word(p['value']); basis(p['basis'])
        array(value['quantum'], quantum)
        array(value['classical'], classical)

    def definition(value):
        side(value['inputs']); side(value['outputs'])
        word({'unitary': 0, 'iso': 1, 'observe': 2}[value['effect']])
        if value['body'] == 'observeZ':
            word(11); word(value['owner']); word(value['value'])
        else:
            word(12); word(0)

    side(request['inputs']); array(request['owners'], word); word(request['result'])
    array(packet['measurements'], definition); array(packet['pack'], word)
    side(packet['outputs']); word(budget)
    return bytes(data)


def inspect(kernel, payload):
    run = subprocess.run([str(kernel), '--readout-check'], input=payload,
                         capture_output=True, timeout=60)
    fields = run.stdout.decode('ascii').splitlines()
    assert len(fields) == 3 and fields[0] == 'qleisli.readout-result 1', (fields, run.stderr)
    assert run.returncode == (0 if fields[1] == 'checked' else 1), (run.returncode, fields)
    assert fields[1] in ('checked', 'error'), fields
    return fields[1:]


def test_component_transport(rows, results, kernel):
    checked = overflow = 0
    for row in rows:
        try:
            payload = bridge(row['request'], row['packet'], row['budget'])
        except ValueError:
            assert row['name'] == 'unbounded-label'
            overflow += 1
            continue
        observed = inspect(kernel, payload)
        expected = results[row['name']]
        assert observed == (expected[:2] if expected[0] == 'checked' else ['error', expected[0]]), row['name']
        checked += 1
    r, p = base(1)
    good = bridge(r, p)
    malformed = [b'', b'QLM2'+good[4:], good[:-1], good+b'\0',
                 b'QLM1'+struct.pack('<I', 100001),
                 b'QLM1'+struct.pack('<I', 0xFFFFFFFF)]
    for i, payload in enumerate(malformed):
        assert inspect(kernel, payload) == ['error', 'format' if i < 4 else 'limit']
    return dict(checked=checked, checked_u32_rejections=overflow, malformed=len(malformed))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    rows = cases()
    source = PRELUDE
    for index, row in enumerate(rows):
        source += (f'def case{index} : IO Unit := report {json.dumps(row["name"])} '
                   f'({render_request(row["request"])}) ({render_packet(row["packet"])}) '
                   f'{row["budget"]}\n')
    source += 'def main : IO Unit := do\n' + '\n'.join(f'  case{i}' for i in range(len(rows))) + '\n'
    commands, binary_hash = build_and_run(source, args.record)
    results = {}
    for line in commands[-1]['stdout'].splitlines():
        name, *fields = line.split('|')
        assert name not in results, name
        results[name] = fields
    assert len(results) == len(rows)
    test_native_rejections(rows, results)
    probes = test_native_branches(rows, results)
    kernel = ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel'
    transport = test_component_transport(rows, results, kernel)
    report = dict(format='qleisli.readout-validation', version=1, status='passed',
        cases=len(rows), accepted=sum(row['status'] == 'checked' for row in rows),
        coefficient_probes=probes, max_measured_qubits=3, max_total_qubits=4,
        production_integration=False, qpe_instrument_receipt=False,
        component_transport=transport,
        kernel_sha256=hashlib.sha256(kernel.read_bytes()).hexdigest(),
        binary_sha256=binary_hash, commands=commands, results=results,
        accounting=[dict(case=row['name'],original=int(results[row['name']][3]),
            current=int(results[row['name']][1]),exact_threshold_checked=True)
            for row in rows if row['status']=='checked'],
        source_sha256={p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in (
            'lean-kernel/QleisliKernel/Semantics/Readout.lean',
            'lean-kernel/QleisliKernel/Hierarchical/Readout.lean',
            'scripts/test_hierarchical_readout.py')})
    if args.record:
        args.record.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ('commands', 'results', 'source_sha256')}))


if __name__ == '__main__':
    main()
