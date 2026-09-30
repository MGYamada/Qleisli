#!/usr/bin/env python3
"""Fresh QPE preparation/provider/circuit/readout binding on small source cases.

Returned finite equations are still obligations. Provider requests below freeze
baseline graphs for mutation tests; numerical probes independently compare full
complex branch amplitudes. This is not source-preservation or external evidence.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import hashlib
import json
from pathlib import Path

from compile_sized_corpus import Operation
from compile_sized_instrument import compile_instrument
from probe_hierarchical_qft_cost import array
from test_hierarchical_artifact import ROOT, build_and_run
from test_hierarchical_preparation import simple_side
from test_hierarchical_qpe_root import artifact, provider_fixture
from test_hierarchical_qpe_schedule import fixture
from test_hierarchical_readout import side as format_side
from test_sized_instrument import sources, probes


def side(value):
    return format_side(simple_side(value))


def definition(value):
    h, b = value['interface'], value['body']
    operator = (f'.init0 {b["output"]}' if b['tag'] == 'init0'
                else f'.observeZ {b["input"]} {b["output"]}')
    return f'⟨⟨{side(h["inputs"])},{side(h["outputs"])}⟩,.{value["effect"]},{operator}⟩'


def component_fixture(proposal, root_request, root_packet):
    root = proposal['graph']['definitions'][proposal['graph']['entry']['implementation']]['interface']
    readout = proposal['readout']
    fresh = side(dict(quantum=proposal['initialized'], classical=[]))
    request = (f'⟨⟨{side(proposal["inputs"])},({fresh} : Side).quantum⟩,{root_request},'
               f'⟨{side(readout["inputs"])},{array(readout["owners"])},{readout["result"]}⟩,{side(readout["outputs"])}⟩')
    packet = (f'⟨⟨{array(definition(d) for d in proposal["initialization"])},{side(root["inputs"])}⟩,{root_packet},'
              f'⟨{array(definition(d) for d in readout["measurements"])},{array(readout["pack"])},{side(readout["outputs"])}⟩⟩')
    return request, packet


PRELUDE = '''import QleisliKernel.Hierarchical.QpeInstrument
open QleisliKernel.Hierarchical Artifact
set_option maxRecDepth 20000
def report (name : String) (r : QpeInstrument.Request) (p : QpeInstrument.Packet) : IO Unit := do
  match QpeInstrument.checkAll r p with
  | .error e => IO.println s!"{name}|{repr e.kind}"
  | .ok checked => IO.println s!"{name}|pending|{checked.visits}|{checked.circuit.visits}|{checked.preparation.visits}|{checked.readout.visits}"
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    code, calls, expected, semantic = PRELUDE, [], {}, {}
    for name, n, m in [('small', 1, 2), ('target2', 2, 2), ('precision3', 1, 3), ('target2precision4', 2, 4)]:
        proposal = compile_instrument(sources(), 'measurement::qpe', dict(n=n, m=m),
                                      {'U': Operation('evolution::evolve', (n, 1, 3))})
        graph = proposal['graph']
        schedule, candidate, metadata = fixture(graph, n, m)
        proof, provider, pairs, order = provider_fixture(graph, metadata['stages'][0]['provider'])
        code += f'def graph_{name} : Artifact := {artifact(graph)}\n'
        code += f'def rootRequest_{name} : QpeRoot.Request := ⟨{schedule},{provider}⟩\n'
        code += f'def rootPacket_{name} : QpeRoot.Packet := ⟨graph_{name},Array.range (totalNodes graph_{name}),{proof},{pairs},{order},{candidate}⟩\n'
        request, packet = component_fixture(proposal, f'rootRequest_{name}', f'rootPacket_{name}')
        code += f'def request_{name} : QpeInstrument.Request := {request}\n'
        code += f'def packet_{name} : QpeInstrument.Packet := {packet}\n'
        calls.append(f'report "{name}" request_{name} packet_{name}')
        expected[name] = 'capacity' if name == 'target2precision4' else 'pending'
        semantic[name] = probes(proposal, n, m)

    def add(name, request='request_small', packet='packet_small', status='contract'):
        calls.append(f'report "{name}" ({request}) ({packet})')
        expected[name] = status
    add('missing-initialization', packet='{packet_small with preparation:={packet_small.preparation with initializations:=#[]}}')
    add('missing-readout', packet='{packet_small with readout:={packet_small.readout with measurements:=#[]}}')
    add('reversed-pack', packet='{packet_small with readout:={packet_small.readout with pack:=packet_small.readout.pack.reverse}}')
    add('wrong-result-name', request='{request_small with readout:={request_small.readout with result:=4294967295}}')
    add('wrong-phase-order', request='{request_small with circuit:={request_small.circuit with circuit:={request_small.circuit.circuit with phase:=#[1,2]}}}')
    add('drop-target', request='{request_small with outputs:={request_small.outputs with quantum:=#[]}}')
    add('wrong-fresh-order', request='{request_small with preparation:={request_small.preparation with fresh:=request_small.preparation.fresh.reverse}}')
    add('wrong-preparation-effect', packet='{packet_small with preparation:={packet_small.preparation with initializations:=packet_small.preparation.initializations.map fun d => {d with effect:=.unitary}}}')
    add('wrong-readout-effect', packet='{packet_small with readout:={packet_small.readout with measurements:=packet_small.readout.measurements.map fun d => {d with effect:=.unitary}}}')
    add('wrong-readout-owner', request='{request_small with readout:={request_small.readout with owners:=#[4294967295,4294967294]}}')
    add('wrong-requested-provider', request='{request_small with circuit:={request_small.circuit with circuit:={request_small.circuit.circuit with provider:=0}}}')
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
    maximum = max(v['maximum_error'] for v in semantic.values())
    assert maximum < 1e-12, semantic
    report = dict(format='qleisli.qpe-instrument-validation', version=1, status='passed',
                  native_cases=len(rows), results=rows, semantic_probes=semantic,
                  phase_sensitive_coefficients=sum(v['coefficients'] for v in semantic.values()), maximum_error=maximum,
                  source_sha256=hashlib.sha256(code.encode()).hexdigest(), binary_sha256=binary,
                  kernel_source_sha256=hashlib.sha256((ROOT/'lean-kernel/QleisliKernel/Hierarchical/QpeInstrument.lean').read_bytes()).hexdigest(),
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), commands=commands,
                  provider_request_origin='frozen baseline mutation fixture',
                  finite_equations_discharged=False, named_qpe_receipt=False, source_preservation=False, production_integration=False)
    if args.record:
        args.record.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('commands',)}))


if __name__ == '__main__':
    main()
