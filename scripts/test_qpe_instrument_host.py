#!/usr/bin/env python3
"""Small private named-QPE framing and exact finite/H/provider reconstruction.
Provider graph layouts freeze mutation fixtures; numeric/full named semantics
and source preservation are separate obligations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import struct
import tempfile

from compact_sized_graph import remap
from compile_sized_corpus import Operation
from compile_sized_instrument import compile_instrument
from test_hierarchical_artifact import ROOT
from test_hierarchical_circuit_trace import source_atoms
from test_hierarchical_qpe_root import children
from test_hierarchical_qft import hadamard_matrix
from test_hierarchical_routed_power import source_stages
from test_hierarchical_wiring import closure
from test_instrument_host import source_documents, oversized_composition, SIDE
from test_sized_instrument import sources


def documents(proposal,n,m):
    graph=proposal['graph']; definitions=graph['definitions']
    selected,order=source_atoms(graph); stages=source_stages(graph)
    hs=[i for i in selected if definitions[i]['body']['tag']=='leaf']
    inverse,=[i for i in selected if definitions[i]['body']['tag']=='inverse']
    forward=definitions[inverse]['body']['definition']; shell=definitions[forward]['body']['children']
    provider=stages[0]['provider']
    proof,=[i for i,p in enumerate(graph['proofs']) if p['implementation']==provider]
    root=graph['proofs'][proof]['meaning']; seen=set();post=[]
    def visit(index):
        if index in seen:return
        seen.add(index)
        for child in children(graph['meanings'][index]['body']):visit(child)
        post.append(index)
    visit(root);indices={old:new for new,old in enumerate(post)}
    meanings=[dict(interface=graph['meanings'][i]['interface'],body=remap(graph['meanings'][i]['body'],indices)) for i in post]
    # The exact H target is independently specified, not copied from leaf bytes.
    for meaning in meanings:
        if meaning['body']['tag']=='finite':meaning['body']['description']=hadamard_matrix()
    provider_request=dict(format='qleisli.hierarchy-request',version=1,profile='qpe-dyadic8-v1',kind='equation',effect='unitary',interface=definitions[provider]['interface'],meanings=meanings,entry=indices[root])
    payload,generic=source_documents(proposal)
    interface=definitions[graph['entry']['implementation']]['interface']
    phase=list(range(n+m-1,n-1,-1));target=list(range(n))
    request=dict(format='qleisli.qpe-instrument-request',version=1,profile='qpe-dyadic8-v1',preparation=generic['preparation'],circuit=dict(interface=interface,phase=phase,target=target,route=phase+target,provider=provider),provider=provider_request,readout=generic['readout'],outputs=generic['outputs'])
    atom=lambda i:dict(index=i,interface=definitions[i]['interface'])
    candidate=dict(format='qleisli.qpe-instrument-candidate',version=1,profile='qpe-dyadic8-v1',provider_proof=proof,hadamards=[atom(i) for i in hs],powers=[atom(s['index']) for s in stages],inverse_fourier=atom(inverse),trace_order=order,power_orders=[s['routes'] for s in stages],fourier_order=closure(graph,[shell[0],*shell[2:]]))
    return payload,request,candidate


def expected_obligations(payload,request,candidate):
    graph=payload['circuit'];d=graph['definitions'];proofs=[i for i,p in enumerate(graph['proofs']) if p['rule']['tag']=='finite']
    provider_proof=graph['proofs'][candidate['provider_proof']]
    pairs=[(provider_proof['meaning'],request['provider']['entry'])];seen={pairs[0]:0};finite=[]
    for index,(a,r) in enumerate(pairs):
        am,rm=graph['meanings'][a],request['provider']['meanings'][r]
        if am['body']['tag']==rm['body']['tag']=='finite':finite.append(index)
        for pair in zip(children(am['body']),children(rm['body'])):
            if pair not in seen:seen[pair]=len(pairs);pairs.append(pair)
    hs={a['index'] for a in candidate['hadamards']}
    inverse=d[candidate['inverse_fourier']['index']]['body']['definition']
    index=d[inverse]['body']['children'][1]
    for width in range(len(candidate['hadamards']),0,-1):
        stage=d[index]['body']['children'];h=d[stage[1]]['body']['left']
        hs.add(d[h]['body']['children'][0])
        if width>1:index=d[stage[3]]['body']['right']
    return proofs,finite,sorted(hs)


def test_binary_transport(frame_path):
    kernel=ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel';good=frame_path.read_bytes()
    words=lambda values:struct.pack('<'+'I'*len(values),*values)
    cuts=sorted(set([0,*range(1,33),*range(len(good)-32,len(good)),len(good)//4,len(good)//2]))
    cases=[(f'truncated-{i}',good[:i],'format') for i in cuts]
    cases += [('valid',good,'pending'),('wrong-magic',b'QLQ2'+good[4:],'format'),('trailing',good+b'\0','format'),('oversized-nested',b'QLQ1'+words([64*1024*1024+1]),'limit')]
    # The nested root and candidate are each below one million words, but their
    # combined decoder work exceeds it. Metadata only; no large-qubit corpus.
    _,root,_=oversized_composition()
    header=[0,0]+SIDE+SIDE+[1,0,1,1,2,0,1,0]
    atoms=[30000]+([0]+SIDE+SIDE)*30000
    assert len(root)//4<1000000 and len(atoms)<1000000
    cases.append(('shared-word-budget',b'QLQ1'+words([len(root)])+root+words(header+atoms),'limit'))
    for name,data,expected in cases:
        run=subprocess.run([str(kernel),'--qpe-instrument-pending'],input=data,capture_output=True,timeout=30)
        lines=run.stdout.decode().splitlines()
        assert lines[:1]==['qleisli.qpe-instrument-pending 3'],(name,run)
        if expected=='pending':assert run.returncode==0 and lines[1]=='pending',(name,lines)
        else:assert run.returncode==1 and lines[1:]==['error',expected],(name,lines)
    return dict(cases=len(cases),shared_word_budget='rejected before semantic checking',maximum_qubit_corpus_generated=False)


def test_named_host(record=None):
    modules=sources();rows={}
    for name,n,m in [('small',1,2),('target2',2,2),('precision3',1,3),('capacity',2,4)]:
        p=compile_instrument(modules,'measurement::qpe',dict(n=n,m=m),{'U':Operation('evolution::evolve',(n,1,3))})
        rows[name]=(*documents(p,n,m),'limit' if name=='capacity' else 'ok')
    hmodules=modules|{'evolution':modules['evolution'].replace('use std::quantum::phase;','use std::quantum::h;').replace('phase[j,d](bit)','h(bit)')}
    hp=compile_instrument(hmodules,'measurement::qpe',dict(n=1,m=2),{'U':Operation('evolution::evolve',(1,1,3))})
    rows['finite-provider']=(*documents(hp,1,2),'ok')
    def mutate(name,fn,expected='contract',base='small'):
        p,r,c,_=copy.deepcopy(rows[base]);fn(p,r,c);rows[name]=(p,r,c,expected)
    mutate('wrong-provider-phase',lambda p,r,c: next(x for x in r['provider']['meanings'] if x['body']['tag']=='phase')['body'].update(j=2))
    mutate('wrong-phase-order',lambda p,r,c:r['circuit']['phase'].reverse())
    mutate('wrong-route',lambda p,r,c:r['circuit']['route'].reverse())
    mutate('wrong-pack',lambda p,r,c:p['readout']['pack'].reverse())
    mutate('missing-init',lambda p,r,c:p['preparation']['initializations'].clear())
    mutate('missing-measurement',lambda p,r,c:p['readout']['measurements'].clear())
    mutate('wrong-provider-proof',lambda p,r,c:c.update(provider_proof=p['circuit']['entry']['proof']))
    mutate('missing-trace',lambda p,r,c:c.update(trace_order=[]))
    mutate('candidate-success-flag',lambda p,r,c:c.update(checked=True),'format')
    mutate('request-success-flag',lambda p,r,c:r.update(checked=True),'format')
    mutate('wrong-candidate-profile',lambda p,r,c:c.update(profile='unchecked'),'format')
    mutate('missing-H',lambda p,r,c:c['hadamards'].pop())
    mutate('out-of-range-H',lambda p,r,c:c['hadamards'][0].update(index=99999),'format')
    def replace_h(p,r,c):
        index=c['hadamards'][0]['index'];graph=p['circuit'];program=json.loads(graph['definitions'][index]['body']['program'])
        program['programs'][0]['operations'][0]['gate']='x'
        graph['definitions'][index]['body']['program']=json.dumps(program)
        proof=next(x for x in graph['proofs'] if x['implementation']==index)
        matrix=json.loads(graph['meanings'][proof['meaning']]['body']['description'])
        matrix['entries']=[[dict(numerator=str(int(k in (1,2) and j==0)),denominator_bits=0) for j in range(4)] for k in range(4)]
        graph['meanings'][proof['meaning']]['body']['description']=json.dumps(matrix)
    mutate('coordinated-wrong-H',replace_h)
    def negative_h(p,r,c):
        index=c['hadamards'][0]['index'];graph=p['circuit']
        program=json.loads(graph['definitions'][index]['body']['program'])
        op=program['programs'][0]['operations'][0]
        program['programs'][0]['operations'][0]=dict(tag='apply_unitary',input=op['input'],output=op['output'],
            steps=[dict(controls=[],action=dict(tag='hadamard',target=0)),
                   dict(controls=[],action=dict(tag='monomial',indices=[],permutation=[0],phases=[4]))])
        graph['definitions'][index]['body']['program']=json.dumps(program)
        proof=next(x for x in graph['proofs'] if x['implementation']==index)
        matrix=json.loads(graph['meanings'][proof['meaning']]['body']['description'])
        for entry in matrix['entries']:
            for coefficient in entry:coefficient['numerator']=str(-int(coefficient['numerator']))
        graph['meanings'][proof['meaning']]['body']['description']=json.dumps(matrix)
    mutate('coordinated-H-global-phase',negative_h)
    def wrong_finite(p,r,c):
        m=next(x for x in r['provider']['meanings'] if x['body']['tag']=='finite');matrix=json.loads(m['body']['description'])
        for entry in matrix['entries']:
            for coeff in entry:coeff['numerator']=str(-int(coeff['numerator']))
        m['body']['description']=json.dumps(matrix)
    mutate('independent-provider-global-phase',wrong_finite,base='finite-provider')
    with tempfile.TemporaryDirectory(prefix='qleisli-qpe-host-') as directory:
        directory=Path(directory)
        for name,(p,r,c,_) in rows.items():
            for suffix,value in [('payload',p),('request',r),('candidate',c)]:
                (directory/f'{name}.{suffix}.json').write_text(json.dumps(value))
        (directory/'cases.txt').write_text(''.join(f'{name}|{expected}\n' for name,(*_,expected) in rows.items()))
        a,b,h=expected_obligations(*rows['finite-provider'][:3]);assert b
        def response(a=a,b=b,h=h):return '\n'.join(map(str,['qleisli.qpe-instrument-pending 3','pending',0,0,len(a),*a,len(b),*b,len(h),*h]))+'\n'
        bad={'omit-proof':response(a=a[:-1]),'duplicate-proof':response(a=a+[a[0]]),'omit-provider':response(b=[]),'duplicate-provider':response(b=b+b),'omit-H':response(h=h[:-1]),'duplicate-H':response(h=h+[h[0]]),'substitute-H':response(h=[99999,*h[1:]]),'trailing':response()+'extra\n','noncanonical':response().replace('pending\n0\n','pending\n00\n'),'claimed-seal':response().replace('\npending\n','\nchecked\n'),'failure-trailing':'qleisli.qpe-instrument-pending 3\nerror\ncontract\nextra\n'}
        (directory/'bad-responses').mkdir()
        for name,value in bad.items():(directory/'bad-responses'/name).write_text(value)
        command=['cargo','test','--test','hierarchical_qpe_host','--','--include-ignored','--nocapture']
        run=subprocess.run(command,cwd=ROOT,capture_output=True,text=True,timeout=180,env=os.environ|{'QLEISLI_QPE_HOST_FIXTURES':str(directory),'QLEISLI_HIERARCHY_KERNEL':str(ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel')})
        assert run.returncode==0,run.stdout+run.stderr
        raw=test_binary_transport(directory/'captured-frame')
    report=dict(format='qleisli.qpe-instrument-host-validation',version=1,status='passed',native_cases=len(rows),response_faults=len(bad),binary_transport=raw,command=command,stdout=run.stdout,stderr=run.stderr,exit_code=run.returncode,request_origin='provider structure frozen for mutation tests; finite H target independently specified',kernel_sha256=hashlib.sha256((ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel').read_bytes()).hexdigest(),source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [ROOT/'lean-kernel/Protocol.lean',ROOT/'lean-kernel/Main.lean',ROOT/'src/interchange/hierarchical.rs',ROOT/'src/interchange/hierarchical/bridge/qpe.rs',Path(__file__).resolve(),ROOT/'tests/hierarchical_qpe_host.rs']},source_preservation_proved=False,production_authority=False,external_schema_enabled=False)
    if record:record.write_text(json.dumps(report,indent=2)+'\n')
    return report

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--record',type=Path);args=parser.parse_args()
    report=test_named_host(args.record);print(json.dumps({k:v for k,v in report.items() if k not in ('stdout','stderr','source_sha256')}))
