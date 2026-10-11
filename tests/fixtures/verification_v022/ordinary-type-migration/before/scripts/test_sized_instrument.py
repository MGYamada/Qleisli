#!/usr/bin/env python3
"""Ordinary initialization/readout and measured QPE/client source experiments.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Component validity and numerical algorithm tests do not issue a named receipt.
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

from compile_sized_corpus import Operation, SourceError, text, wires
from compile_sized_instrument import compile_instrument as produce_instrument
from compact_sized_graph import compact
from instrument_transport import encode_preparation, encode_readout, inspect
from test_sized_corpus import ROOT, circuit_action, difference
from test_sized_qpe import expected as qpe_expected
from test_sized_qpe_clients import sources as client_sources, expected as client_expected


def sources():
    return client_sources() | {p.stem:p.read_text() for p in
        (ROOT/'corpus/sized/measured_qpe').glob('*.qli')} | {
        'measured_'+p.stem:p.read_text() for p in (ROOT/'tests/fixtures/measured_clients').glob('*.qli')}


def compile_instrument(*args, **kwargs):
    return produce_instrument(*args, **kwargs, compact_graph=False)


def test_graph_compaction(proposal):
    graph = compact(proposal['graph'])
    before, _ = circuit_action(proposal['graph'])
    after, _ = circuit_action(graph)
    root = proposal['graph']['definitions'][proposal['graph']['entry']['implementation']]['interface']
    assert root == graph['definitions'][graph['entry']['implementation']]['interface']
    width = len(wires(root['inputs']['quantum']))
    columns = [{label:1} for label in range(1 << width)] + [
        {0:1/math.sqrt(3), (1 << width)-1:1j/math.sqrt(6)}]
    maximum = max(difference(before(column),after(column)) for column in columns)
    assert maximum < 1e-12, maximum
    return graph, dict(before=len(proposal['graph']['definitions']),after=len(graph['definitions']),
                       columns=len(columns),maximum_error=maximum)


def qpe(source, n=1, m=2, j=1, d=3):
    return compile_instrument(source, 'measurement::qpe', dict(n=n,m=m),
                              {'U':Operation('evolution::evolve',(n,j,d))})


def source_rejections(base):
    changes = [
        ('unitary-wrapper', 'measurement', 'pub observe fn', 'pub unitary fn'),
        ('unitary-initializer', 'initialization', 'pub iso fn', 'pub unitary fn'),
        ('iso-readout', 'readout', 'pub observe fn', 'pub iso fn'),
        ('missing-access', 'measurement', ', Controlled(U)', ''),
        ('wrong-classical-width', 'measurement', 'CBits<m>', 'CBits<m+1>'),
        ('drop-empty-owner', 'readout', 'let () = consume_empty(q);', ''),
        ('consume-nonempty', 'readout', 'let (bit,rest) = take_bit[n,0](q);', 'let () = consume_empty(q); let (bit,rest) = take_bit[n,0](q);'),
        ('reuse-measured-bit', 'readout', 'let first = measure_z(bit);', 'let first = measure_z(bit); let second = measure_z(bit);'),
        ('duplicate-classical-pattern', 'readout', 'let first = measure_z(bit);', 'let first = measure_z(bit); let (copy,copy) = (first,first);'),
        ('wrong-prepend-width', 'readout', 'prepend_bit[n-1]', 'prepend_bit[n]'),
        ('cycle-initializer', 'initialization', 'init_zero[n-1]()', 'init_zero[n]()'),
        ('unknown-empty-branch', 'readout', 'empty_bits()', 'missing()'),
        ('runtime-feedback', 'measurement', 'let phase = init_zero[m]();', 'if target { init_zero[m]() } else { init_zero[m]() }; let phase = init_zero[m]();'),
        ('bad-init-arity', 'initialization', 'init0()', 'init0(rest)'),
        ('unknown-static-size', 'initialization', 'init_zero[n-1]()', 'init_zero[missing]()'),
    ]
    rows = []
    for name, module, before, after in changes:
        assert before in base[module]
        changed = base | {module:base[module].replace(before,after)}
        try:
            qpe(changed)
        except SourceError as error:
            rows.append(dict(case=name, diagnostic=str(error)))
        else:
            raise AssertionError('invalid instrument source accepted: '+name)
    return rows


def components(proposal, kernel):
    root = proposal['graph']['definitions'][proposal['graph']['entry']['implementation']]['interface']
    preparation = dict(initializations=proposal['initialization'], outputs=root['inputs'])
    required = dict(inputs=proposal['inputs'],fresh=proposal['initialized'])
    initialized = inspect(kernel,'preparation',encode_preparation(required,preparation))
    assert initialized['status'] == 'checked', initialized
    readout = proposal['readout']
    if readout is None:
        return dict(preparation_work=initialized['work'],readout_work=0)
    assert readout['inputs'] == root['outputs']
    measured = inspect(kernel,'readout',encode_readout(readout,readout))
    assert measured['status'] == 'checked', measured
    return dict(preparation_work=initialized['work'],readout_work=measured['work'])


def instrument_action(proposal, column):
    """Execute the actual proposal's initialization, graph and named-bit pack."""
    inputs = wires(proposal['inputs']['quantum'])
    root = proposal['graph']['definitions'][proposal['graph']['entry']['implementation']]['interface']
    initialized = wires(root['inputs']['quantum'])
    fresh = [axis for port in proposal['initialized'] for axis in port['axes']]
    assert set(inputs).isdisjoint(fresh) and initialized == inputs+fresh
    # Each actual init0 contributes |0>; embedding retains every original
    # coefficient/reference column. No user-supplied zero flag is executed.
    for definition in proposal['initialization']:
        assert definition['body']['tag'] == 'init0'
    evaluate, _ = circuit_action(proposal['graph'])
    state = evaluate(column)
    readout = proposal['readout']
    if readout is None:
        return {(0,label):amplitude for label,amplitude in state.items()}
    inputs = readout['inputs']['quantum']
    axes = wires(inputs)
    ports = {p['owner']:p for p in inputs}
    residual = wires(readout['outputs']['quantum'])
    result = {}
    for label, amplitude in state.items():
        values = {}
        for definition in readout['measurements']:
            body = definition['body']
            axis, = ports[body['input']]['axes']
            values[body['output']] = (label >> axes.index(axis)) & 1
        outcome = sum(values[value] << i for i,value in enumerate(readout['pack']))
        target = sum(((label >> axes.index(axis)) & 1) << i for i,axis in enumerate(residual))
        result[outcome,target] = result.get((outcome,target),0)+amplitude
    return result


def probes(proposal, n, m, j=1, d=3, kind='qpe'):
    columns = [{label:1} for label in range(1 << n)] + [
        {0:1/math.sqrt(3), (1 << n)-1:1j/math.sqrt(6)},
        {0:(1+1j)/math.sqrt(12), 1:-1/math.sqrt(3)}]
    maximum, count = 0.0, 0
    for column in columns:
        reference_input = {x << m:z for x,z in column.items()}
        wanted = (qpe_expected(n,m,reference_input,j,d) if kind == 'qpe' else
                  client_expected(kind,n,m,reference_input,j,d))
        reference = {(x % (1 << m), x >> m):z for x,z in wanted.items()}
        actual = instrument_action(proposal,column)
        maximum = max(maximum,difference(actual,reference))
        count += (1 << (n+m))
    return dict(coefficients=count,maximum_error=maximum)


def test_interleaved_reference(proposal):
    # Independent source-order oracle: select the first observed bit, apply H
    # to the other bit, then create/measure a fresh zero. Two complex columns
    # retain correlations with an arbitrary reference system.
    columns = [{i:1} for i in range(4)] + [
        {0:1/math.sqrt(3), 3:1j/math.sqrt(6)},
        {1:(1+1j)/math.sqrt(12), 2:-1/math.sqrt(3)}]
    maximum = 0.0
    for column in columns:
        wanted = {}
        for label,value in column.items():
            for target in range(2):
                key = label & 1,target  # high measured bit is exactly zero
                wanted[key] = wanted.get(key,0)+value*((-1)**((label >> 1)*target))/math.sqrt(2)
        maximum = max(maximum,difference(instrument_action(proposal,column),wanted))
    assert maximum < 1e-12,maximum
    return dict(coefficients=len(columns)*8,maximum_error=maximum)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record',type=Path)
    args = parser.parse_args()
    source = sources()
    proposals, parameters = {}, {}
    for n,m,j,d in [(1,1,1,3),(1,2,1,3),(1,3,1,4),(2,2,3,4),(2,4,1,3)]:
        name=f'qpe-{n}-{m}'
        proposals[name]=qpe(source,n,m,j,d); parameters[name]=(n,m,j,d,'qpe')
    # Generic request/init/readout acceptance fits the unchanged allowance
    # (checked by test_instrument_host.py); named QPE binding is separate.
    pending_composed={}
    for n in range(4):
        proposals[f'init-{n}']=compile_instrument(source,'initialization::init_zero',dict(n=n))
        proposals[f'readout-{n}']=compile_instrument(source,'readout::measure_bits',dict(n=n))
    proposals['order']=compile_instrument(source,'measured_order::order_readout',dict(n=2,m=2),
        {'U':Operation('modular::mul_two',(2,))})
    parameters['order']=(2,2,1,3,'order')
    for j,d in [(0,3),(1,3),(1,4),(2,2)]:
        name=f'amplitude-{j}-{d}'
        proposals[name]=compile_instrument(source,'measured_amplitude::amplitude_readout',dict(n=1,m=2,j=j,d=d))
        parameters[name]=(1,2,j,d,'amplitude')
    copied = source | {'readout':source['readout'].replace('let first = measure_z(bit);',
        'let first = measure_z(bit); let unused = first; let first = first;').replace(
        'prepend_bit[n-1](first,tail)',
        'let tail = for static k in 0..2 carry value = tail { let unused = first; yield value; }; prepend_bit[n-1](first,tail)')}
    proposals['classical-copy-capture']=qpe(copied)
    parameters['classical-copy-capture']=(1,2,1,3,'qpe')
    wrong_sources = {
        'wrong-zero-helper':source | {'initialization':source['initialization'].replace(
            'use std::quantum::init0;','use std::quantum::init0;\nuse std::quantum::x;').replace('init0();','x(init0());')},
        'wrong-readout-order':source | {'readout':source['readout'].replace('take_bit[n,0]', 'take_bit[n,n-1]')},
    }
    for name,s in wrong_sources.items():
        proposals[name]=qpe(s)
    proposals['retiming']=compile_instrument(source,'measured_retiming::retimed',dict(n=2))
    normalization = {}
    for name,p in proposals.items():
        p['graph'],normalization[name] = test_graph_compaction(p)
    kernel=ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel'
    component_results={name:components(p,kernel) for name,p in proposals.items()}
    with tempfile.TemporaryDirectory(prefix='qleisli-instrument-') as directory:
        directory=Path(directory)
        for name,p in proposals.items():
            (directory/f'{name}.json').write_text(text(p['graph']))
        (directory/'cases.txt').write_text(''.join(f'{name}|ok\n' for name in proposals))
        command=['cargo','test','--test','sized_corpus','inspect_source_produced_corpus','--','--ignored','--nocapture']
        run=subprocess.run(command,cwd=ROOT,capture_output=True,text=True,timeout=240,env=os.environ | {
            'QLEISLI_SIZED_CORPUS':str(directory),'QLEISLI_HIERARCHY_KERNEL':str(kernel)})
        assert run.returncode==0,run.stdout+run.stderr
    for line in run.stdout.splitlines():
        fields = line.split('|')
        if len(fields) == 6 and fields[0] == 'CORPUS' and fields[2] == 'ok':
            row = component_results[fields[1]]
            row['graph_work'],row['exact_work'] = int(fields[3]),int(fields[4])
            row['aggregate_work'] = sum(row.values())
            # A diagnostic aggregate, not a composed acceptance receipt. Do
            # not hide the initialization/readout cost when tracking capacity.
            if fields[1] not in pending_composed:
                assert row['aggregate_work'] <= 2000000,(fields[1],row)
    semantic={name:probes(proposals[name],*params) for name,params in parameters.items()}
    semantic['retiming']=test_interleaved_reference(proposals['retiming'])
    assert all(p['maximum_error']<1e-10 for p in semantic.values()),semantic
    faults={name:probes(proposals[name],1,2) for name in wrong_sources}
    assert all(p['maximum_error']>0.1 for p in faults.values()),faults
    for n in range(4):
        assert difference(instrument_action(proposals[f'init-{n}'],{0:1}),{(0,0):1})<1e-12
        for label in range(1 << n):
            assert instrument_action(proposals[f'readout-{n}'],{label:1})=={(label,0):1}
    report=dict(format='qleisli.sized-instrument-validation',version=1,status='passed',
        proposals=len(proposals),components=component_results,semantics=semantic,semantic_faults=faults,
        normalization=normalization,
        source_rejections=source_rejections(source),pending_composed=pending_composed,
        production_integration=False,named_instrument_receipt=False,source_preservation_proved=False,
        max_checked_graph_qubits=6,unaccepted_composed_case_qubits=None,
        kernel_sha256=hashlib.sha256(kernel.read_bytes()).hexdigest(),
        graph_reconstruction=dict(command=command,exit_code=run.returncode,stdout=run.stdout,stderr=run.stderr),
        source_sha256={name:hashlib.sha256(value.encode()).hexdigest() for name,value in source.items()},
        implementation_sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in (
            'scripts/compile_sized_corpus.py','scripts/compile_sized_instrument.py',
            'scripts/compact_sized_graph.py',
            'scripts/instrument_transport.py','scripts/test_sized_instrument.py')})
    if args.record:
        args.record.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('graph_reconstruction','source_sha256','implementation_sha256','source_rejections','components')}))


if __name__=='__main__':
    main()
