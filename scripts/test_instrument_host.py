#!/usr/bin/env python3
"""Independent composite framing, finite discharge and shared decoder allowance.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import struct
import subprocess
import tempfile
import tomllib

from test_hierarchical_artifact import ROOT, build_and_run
from test_hierarchical_host import phase_bridge
from compile_sized_corpus import Operation
from compile_sized_instrument import compile_instrument
from test_sized_instrument import sources, probes, test_interleaved_reference

PRODUCT_VERSION = tomllib.loads((ROOT / 'Cargo.toml').read_text())['package']['version']


def words(values):
    return struct.pack('<'+'I'*len(values), *values)


SIDE = [1, 0, 1, 1, 1, 7, 0]
OUTPUT = [0, 1, 900, 1, 2, 1]


def root_frame(artifact):
    # Independent phase request and its singleton pair schedule.
    meaning = SIDE+SIDE+[9, 1, 8]
    return b'QLR1'+words([len(artifact)])+artifact+words(
        [0, 0]+SIDE+SIDE+[1]+meaning+[0, 1, 0, 0, 0, 1, 0])


def instrument_frame(root, huge=False):
    # No initialization is requested here; the Rust host tests additionally
    # exercise actual init0 and retention of an arbitrary control input.
    prepared = SIDE if not huge else [60000]+[0, 1, 1, 1, 7]*60000+[0]
    observed = [0, 1, 20, 1, 1]
    tail = prepared+[0, 0]+[0]+SIDE+SIDE+[1, 0, 900]
    tail += [1]+SIDE+observed+[2, 11, 0, 20]+[1, 20]+OUTPUT+OUTPUT
    return b'QLI1'+words([len(root)])+root+words(tail)


def oversized_composition():
    # Both nested frames fit their standalone limits. Together with an outer
    # header they exceed one million words. This is malformed metadata, not a
    # maximum-qubit corpus example, and is tested at the decoder directly.
    encoding = SIDE+SIDE+[0]
    definition = SIDE+SIDE+[0, 9, 0, 1, 8]
    meaning = SIDE+SIDE+[9, 1, 8]
    proof = [0, 9, 0, 0, 0, 0, 1, 1, 0, 0]
    count = 45000
    data = [1]+definition+[1]+meaning+[count]+encoding*count+[1]+proof
    data += [0, 0, count+3]+list(range(count+3))
    artifact = b'QLH1'+words(data)
    root = root_frame(artifact)
    assert len(artifact)//4 < 1000000
    frame = instrument_frame(root, huge=True)
    assert len(frame)//4 > 1000000
    return artifact, root, frame


def test_transport(kernel):
    good = instrument_frame(root_frame(phase_bridge()))
    cases = [('valid', good, 'pending'), ('empty', b'', 'format'),
             ('magic', b'QLI2'+good[4:], 'format'), ('trailing', good+b'\0', 'format'),
             ('oversized-nested-length', b'QLI1'+words([64*1024*1024+1]), 'limit')]
    cases.extend((f'truncated-{i}',good[:i],'format') for i in range(1,len(good)))
    for name, data, expected in cases:
        run = subprocess.run([str(kernel),'--instrument-pending',PRODUCT_VERSION],input=data,capture_output=True,timeout=30)
        lines = run.stdout.decode().splitlines()
        assert lines[:1] == ['qleisli.instrument-pending 3'], (name,run)
        if expected == 'pending':
            assert run.returncode == 0 and lines[1] == 'pending' and lines[3:] == ['0','0','0'], (name,lines)
            assert 0 < int(lines[2]) <= 2000000
        else:
            assert run.returncode == 1 and lines[1:] == ['error',expected], (name,lines)
    return len(cases)


def test_shared_decoder_allowance(record):
    with tempfile.TemporaryDirectory(prefix='qleisli-instrument-budget-') as temp:
        paths=[]
        for name, data in zip(('artifact','root','instrument'),oversized_composition()):
            path=Path(temp)/name
            path.write_bytes(data)
            paths.append(json.dumps(str(path)))
        source = '''import Protocol
open QleisliKernel.Protocol.Hierarchical
open QleisliKernel.Protocol
def main : IO Unit := do
  let artifact ← IO.FS.readBinFile %s
  let root ← IO.FS.readBinFile %s
  let instrument ← IO.FS.readBinFile %s
  match parse artifact, parseRequest root, parseInstrument instrument with
  | .ok _, .ok _, .error .limit => IO.println "shared-word-budget|passed"
  | _, _, _ => throw (IO.userError "nested decoder allowances were not shared")
''' % tuple(paths)
        commands, digest = build_and_run(source,record)
        assert commands[-1]['stdout'].strip() == 'shared-word-budget|passed'
        return dict(commands=commands,binary_sha256=digest)


def source_documents(proposal):
    graph, readout = proposal['graph'], proposal['readout']
    proof = graph['proofs'][graph['entry']['proof']]
    interface = graph['definitions'][graph['entry']['implementation']]['interface']
    profile = dict(version=1,profile='initialize-unitary-readout-v1')
    artifact = dict(profile,format='qleisli.instrument-ir',circuit=graph,
        preparation=dict(initializations=proposal['initialization'],outputs=interface['inputs']),
        readout={k:readout[k] for k in ('measurements','pack','outputs')})
    # This request freezes a baseline proposal for mutation regression. It is
    # deliberately NOT independent mathematical QPE evidence. Independent
    # equations are covered by the hand-authored Rust tests and numeric oracle.
    request = dict(profile,format='qleisli.instrument-request',
        preparation=dict(inputs=proposal['inputs'],fresh=proposal['initialized']),
        circuit=dict(format='qleisli.hierarchy-request',version=1,profile='qpe-dyadic8-v1',
            kind='equation',effect='unitary',interface=interface,
            meanings=graph['meanings'],entry=proof['meaning']),
        readout={k:readout[k] for k in ('inputs','owners','result')},outputs=readout['outputs'])
    return artifact,request


def test_source_connection(kernel):
    modules=sources()
    qpe=lambda s: compile_instrument(s,'measurement::qpe',dict(n=1,m=2),
                                     {'U':Operation('evolution::evolve',(1,1,3))})
    proposals={
        'qpe':qpe(modules),
        'order':compile_instrument(modules,'measured_order::order_readout',dict(n=2,m=2),
            {'U':Operation('modular::mul_two',(2,))}),
        'amplitude':compile_instrument(modules,'measured_amplitude::amplitude_readout',dict(n=1,m=2,j=1,d=3)),
        'retiming':compile_instrument(modules,'measured_retiming::retimed',dict(n=2)),
        'qpe-1-3':compile_instrument(modules,'measurement::qpe',dict(n=1,m=3),
            {'U':Operation('evolution::evolve',(1,1,3))}),
        'qpe-2-4':compile_instrument(modules,'measurement::qpe',dict(n=2,m=4),
            {'U':Operation('evolution::evolve',(2,1,3))}),
    }
    rows={name:(*source_documents(p),'ok') for name,p in proposals.items()}
    for name,module,before,after in [
        ('wrong-zero','initialization','init0();','x(init0());'),
        ('wrong-order','readout','take_bit[n,0]','take_bit[n,n-1]')]:
        source=modules[module].replace(before,after)
        if name == 'wrong-zero':
            source=source.replace('use std::quantum::init0;',
                'use std::quantum::init0;\nuse std::quantum::x;')
        changed=qpe(modules | {module:source})
        rows[name]=(source_documents(changed)[0],rows['qpe'][1],'contract')
    # All small generic composed cases fit the unchanged allowance. Their
    # baseline-derived request is still distinct from named QPE acceptance.
    with tempfile.TemporaryDirectory(prefix='qleisli-instrument-source-') as directory:
        directory=Path(directory)
        for name,(artifact,request,_) in rows.items():
            (directory/f'{name}.json').write_text(json.dumps(artifact))
            (directory/f'{name}.request.json').write_text(json.dumps(request))
        (directory/'cases.txt').write_text(''.join(f'{name}|{expected}\n' for name,(_,_,expected) in rows.items()))
        command=['cargo','test','--test','sized_corpus','check_source_instrument_contracts','--','--ignored','--nocapture']
        run=subprocess.run(command,cwd=ROOT,env=os.environ | {'QLEISLI_HIERARCHY_KERNEL':str(kernel),
            'QLEISLI_SIZED_INSTRUMENT':str(directory)},text=True,capture_output=True,timeout=120)
        assert run.returncode == 0,run.stdout+run.stderr
    semantics={name:probes(proposals[name],n,m,1,3,kind) for name,n,m,kind in [
        ('qpe',1,2,'qpe'),('order',2,2,'order'),('amplitude',1,2,'amplitude'),
        ('qpe-1-3',1,3,'qpe'),('qpe-2-4',2,4,'qpe')]}
    semantics['retiming']=test_interleaved_reference(proposals['retiming'])
    assert all(row['maximum_error']<1e-10 for row in semantics.values())
    return dict(cases=len(rows),command=command,stdout=run.stdout,stderr=run.stderr,
        pending_composed_capacity={},
        semantics=semantics,request_origin='baseline proposal; mutation regression only',
        source_sha256={name:hashlib.sha256(value.encode()).hexdigest() for name,value in modules.items()})


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record',type=Path)
    args=parser.parse_args()
    kernel=ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel'
    binary_cases=test_transport(kernel)
    budget=test_shared_decoder_allowance(args.record)
    source_connection=test_source_connection(kernel)
    command=['cargo','test','--test','hierarchical_host','instrument','--','--include-ignored','--nocapture']
    run=subprocess.run(command,cwd=ROOT,env=os.environ | {'QLEISLI_HIERARCHY_KERNEL':str(kernel)},
                       text=True,capture_output=True,timeout=120)
    assert run.returncode == 0,run.stdout+run.stderr
    report=dict(format='qleisli.instrument-host-validation',version=1,status='passed',
        binary_cases=binary_cases,shared_decoder_allowance=budget,source_connection=source_connection,
        host_command=command,stdout=run.stdout,stderr=run.stderr,
        kernel_sha256=hashlib.sha256(kernel.read_bytes()).hexdigest(),
        production_integration=False,named_qpe_binding=False)
    if args.record:
        args.record.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('shared_decoder_allowance','source_connection','stdout','stderr')}))


if __name__ == '__main__':
    main()
