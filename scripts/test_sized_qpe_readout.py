#!/usr/bin/env python3
"""Connect the real coherent QPE source graph to checked structural readout.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
The composite is an integration experiment, not a production QPE receipt.
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

from compile_sized_corpus import Producer, Quantum, text, wires
from test_hierarchical_artifact import ROOT, build_and_run
from test_hierarchical_readout import PRELUDE, render_request, render_packet, bridge, inspect
from test_sized_corpus import circuit_action, difference
from test_sized_qpe import compile_case, expected, modules


def connect(artifact, precision):
    """Untrusted producer: explicit register splitting, then actual observations."""
    producer = Producer()
    root = producer.import_artifact(artifact)
    producer.owner = max(p['owner'] for d in producer.definitions
                         for side in d['interface'].values() for p in side['quantum']) + 1
    producer.state = copy.deepcopy(producer.ends(root)[1])
    producer.steps = [root]
    phase, target = producer.state
    assert phase['basis'] == [dict(tag='bits', width=precision)]
    rest, bits = Quantum(('bits', precision), phase), []
    for width in range(precision, 0, -1):
        bit, rest = producer.call('take_bit', [width, 0], [rest])
        bits.append(bit.port)
    # The empty register is consumed by an actual checked structural operation.
    body = dict(tag='structural', operation=dict(tag='unpack_empty_bits'))
    producer.apply(producer.add([rest.port], [], body, body, 'structural'))
    producer.steps.append(producer.route(producer.state, bits + [target]))
    entry = producer.sequence(producer.steps)
    graph = dict(format='qleisli.hierarchical-ir', version=1, profile='qpe-dyadic8-v1',
        definitions=producer.definitions, meanings=producer.meanings, encodings=producer.encodings,
        proofs=producer.proofs, entry=dict(implementation=entry, proof=entry))
    inputs = copy.deepcopy(producer.definitions[entry]['interface']['outputs'])
    # The component harness uses concise Lean type atoms, with no implicit cast.
    def converted(side):
        out = copy.deepcopy(side)
        for port in out['quantum']:
            atom, = port['basis']
            port['basis'] = atom['tag'] + (f' {atom["width"]}' if atom['tag'] == 'bits' else '')
        return out
    inputs = converted(inputs)
    request = dict(inputs=inputs, owners=[b['owner'] for b in bits], result=10001)
    before, measurements, names = copy.deepcopy(inputs), [], []
    for i, bit in enumerate(bits):
        value = 20001 + i
        after = dict(quantum=[p for p in before['quantum'] if p['owner'] != bit['owner']],
                     classical=before['classical'] + [dict(value=value, basis='bit')])
        measurements.append(dict(inputs=before, outputs=after, effect='observe',
                                 body='observeZ', owner=bit['owner'], value=value))
        before = after
        names.append(value)
    packet = dict(measurements=measurements, pack=names,
                  outputs=dict(quantum=before['quantum'], classical=[dict(value=10001, basis=f'bits {precision}')]))
    assert packet['outputs']['quantum'] == converted(dict(quantum=[target], classical=[]))['quantum']
    return graph, request, packet


ROUTES = r'''
def routes (name : String) (request : Readout.Request) (packet : Readout.Packet) : IO Unit := do
  match Readout.check request packet 2000000 with
  | .error e => throw (IO.userError s!"readout rejected: {repr e}")
  | .ok _ =>
    let actual := (Readout.projected packet).getD #[]
    let axes := (actual.map (fun p => p.2.2)).toList
    let names := (actual.map (fun p => p.2.1)).toList
    let allAxes := (wires request.inputs).toList
    let residualAxes := (wires packet.outputs).toList
    let mut rows : Array String := #[]
    for outcome in List.range (2^request.owners.size) do
      for residual in List.range (2^residualAxes.length) do
        let column := Semantics.Readout.sequential axes (bit outcome)
          (fun (state : Nat → Bool) (_ : Unit) => (allAxes.zipIdx).foldl
            (fun n (axis, i) => n + if state axis then 2^i else 0) 0)
          (fun axis => bit residual (residualAxes.idxOf axis)) ()
        let packed := Readout.assemble packet (fun value => bit outcome (names.idxOf value))
        rows := rows.push s!"[{packed},{residual},{column}]"
    IO.println s!"{name}|[{String.intercalate "," rows.toList}]"
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    sources, entries = modules(), {}
    for n, m, j, d in [(1, 1, 1, 3), (1, 2, 1, 3), (1, 3, 1, 4), (2, 2, 3, 4)]:
        entries[f'qpe-{n}-{m}-{j}-{d}'] = (n, m, j, d, *connect(compile_case(sources, n, m, j, d), m))
    kernel = ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel'
    with tempfile.TemporaryDirectory(prefix='qleisli-qpe-readout-') as temporary:
        directory = Path(temporary)
        for name, (_, _, _, _, graph, _, _) in entries.items():
            (directory/f'{name}.json').write_text(text(graph))
        (directory/'cases.txt').write_text(''.join(f'{name}|ok\n' for name in entries))
        command = ['cargo', 'test', '--test', 'sized_corpus', 'inspect_source_produced_corpus', '--', '--ignored', '--nocapture']
        run = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=240,
            env=os.environ | {'QLEISLI_HIERARCHY_KERNEL': str(kernel), 'QLEISLI_SIZED_CORPUS': str(directory)})
        assert run.returncode == 0, run.stdout + run.stderr
    source = PRELUDE + ROUTES
    for i, (name, (_, _, _, _, _, request, packet)) in enumerate(entries.items()):
        source += f'def case{i} : IO Unit := routes {json.dumps(name)} ({render_request(request)}) ({render_packet(packet)})\n'
    source += 'def main : IO Unit := do\n' + '\n'.join(f'  case{i}' for i in range(len(entries))) + '\n'
    commands, binary_hash = build_and_run(source, args.record)
    routes = dict((name, json.loads(values)) for name, values in
                  (line.split('|', 1) for line in commands[-1]['stdout'].splitlines()))
    assert routes.keys() == entries.keys()
    for _, _, _, _, _, request, packet in entries.values():
        assert inspect(kernel, bridge(request, packet))[0] == 'checked'
    maximum, probes, faults = 0.0, 0, 0
    for name, (n, m, j, d, graph, _, _) in entries.items():
        evaluate, _ = circuit_action(graph)
        # Fresh-zero phase input, arbitrary target basis and entangled reference
        # columns. Initialization is a test premise, not a checked source feature.
        inputs = [{x << m: 1} for x in range(1 << n)] + [
            {0: 1/math.sqrt(3), ((1 << n)-1) << m: 1j/math.sqrt(6)},
            {0: (1+1j)/math.sqrt(12), 1 << m: -1/math.sqrt(3)}]
        for column in inputs:
            actual, wanted = evaluate(column), expected(n, m, column, j, d)
            measured = {(y, target): actual.get(index, 0) for y, target, index in routes[name]}
            required = {(y, target): wanted.get(y | (target << m), 0)
                        for y in range(1 << m) for target in range(1 << n)}
            maximum = max(maximum, difference(measured, required))
            probes += len(required)
            if m > 1:
                reversed_bits = {(int(f'{y:0{m}b}'[::-1], 2), target): z for (y, target), z in measured.items()}
                faults += difference(reversed_bits, required) > 0.1
    assert maximum < 1e-10 and faults > 0, (maximum, faults)
    report = dict(format='qleisli.sized-qpe-readout-validation', version=1, status='passed',
        cases=len(entries), branch_coefficients=probes, maximum_error=maximum,
        wrong_bit_order_counterexamples=faults, max_total_qubits=4,
        initialization='assumed zero in test inputs; source/checker integration pending',
        production_integration=False, named_qpe_receipt=False,
        kernel_sha256=hashlib.sha256(kernel.read_bytes()).hexdigest(), readout_binary_sha256=binary_hash,
        graph_reconstruction=dict(command=command, exit_code=run.returncode, stdout=run.stdout, stderr=run.stderr),
        readout_commands=commands,
        artifact_sha256={name: hashlib.sha256(text(row[4]).encode()).hexdigest() for name, row in entries.items()},
        source_sha256={key: hashlib.sha256(value.encode()).hexdigest() for key, value in sources.items()})
    if args.record:
        args.record.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: v for k, v in report.items() if k not in
                     ('graph_reconstruction', 'readout_commands', 'source_sha256', 'artifact_sha256')}))


if __name__ == '__main__':
    main()
