#!/usr/bin/env python3
"""Fresh named Fourier host requests, coordinated faults and binary framing.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
No producer receipt or numerical matrix is accepted by the host API.
"""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import time

from test_hierarchical_qft import SharedGradientCircuit, port, side, text
from test_hierarchical_request import replace_word
from test_hierarchical_wiring import closure

ROOT = Path(__file__).resolve().parent.parent


def request(n):
    header = dict(inputs=side([port(0, range(n))]), outputs=side([port(0, range(n))]))
    return dict(format='qleisli.hierarchy-request', version=1, profile='qpe-dyadic8-v1',
                kind='equation', effect='unitary', interface=header, entry=0,
                meanings=[dict(interface=copy.deepcopy(header), body=dict(tag='qft', width=n))])


def binary_frame(a, r):
    """Independent fixture encoder for the actual QFT subset, not the Rust codec."""
    word = lambda n: struct.pack('<I', n)
    seq = lambda xs, f=word: word(len(xs))+b''.join(map(f, xs))
    block = lambda s: word(len(s.encode()))+s.encode()
    def basis(atoms):
        def atom(v):
            tag = ['unit', 'bit', 'bits', 'tuple'].index(v['tag'])
            return word(tag)+(word(v['width' if tag == 2 else 'arity']) if tag >= 2 else b'')
        return seq(atoms, atom)
    def side_bytes(s):
        return seq(s['quantum'], lambda p: word(p['owner'])+basis(p['basis'])+seq(p['axes']))+seq(s['classical'], lambda p: word(p['value'])+basis(p['basis']))
    header = lambda h: side_bytes(h['inputs'])+side_bytes(h['outputs'])
    mapping = lambda m: seq(m['owners'])+seq(m['axes'])+seq(m['classical'])
    def structural(b):
        code = ['take_bit','put_bit','split_tuple','join_tuple','bit_to_bits','bits_to_bit',
                'pack_unit','unpack_unit','pack_empty_bits','unpack_empty_bits'].index(b['tag'])
        return word(code)+(word(b['width'])+word(b['position']) if code < 2 else b'')
    def body(b, logical=False):
        tag = b['tag']
        if tag in ('leaf', 'finite'):
            return word(1 if logical else 0)+block(b['description' if logical else 'program'])
        if tag == 'sequence': return word(2 if logical else 1)+seq(b['children'])
        if tag == 'tensor': return word(3 if logical else 2)+word(b['left'])+word(b['right'])
        if tag in ('repeat', 'power'): return word(6 if logical else 4)+word(b['child'] if logical else b['count'])+word(b['count'] if logical else b['definition'])
        if tag == 'control': return word(5 if logical else 6)+word(b['child' if logical else 'definition'])+word(b['polarity'])
        if tag == 'rewire': return word(7)+mapping(b['permutation'])
        if tag == 'structural': return word(8)+structural(b['operation'])
        if tag in ('phase', 'dyadic_phase'): return word(9)+(b'' if logical else word(b['target']))+word(b['j'])+word(b['k'])
        if tag == 'identity': return word(0)
        if tag == 'qft': return word(10)+word(b['width'])
        raise AssertionError(tag)
    tags = ['finite','sequence','tensor','inverse','control','repeat','associativity',
            'rewire','structural','phase','computed','conjugation']
    def proof(p):
        return (word(0)+word(tags.index(p['rule']['tag']))+seq(p['premises'])+
                b''.join(word(p[k]) for k in ['implementation','meaning','input_encoding','output_encoding'])+
                word(p['witness']['template_version'])+seq(p['witness']['parameters'])+seq(p['witness']['references']))
    assert all(e['body']['tag'] == 'identity' for e in a['encodings'])
    assert all(not p['witness']['references'] for p in a['proofs'])
    # Producer tables are topological and have independent table offsets.
    count = sum(len(a[k]) for k in ['definitions','meanings','encodings','proofs'])
    embedded = (b'QLH1'+seq(a['definitions'],lambda d: header(d['interface'])+word(0)+body(d['body']))+
                seq(a['meanings'],lambda m: header(m['interface'])+body(m['body'],True))+
                seq(a['encodings'],lambda e: side_bytes(e['logical'])+side_bytes(e['physical'])+word(0))+
                seq(a['proofs'],proof)+word(a['entry']['implementation'])+word(a['entry']['proof'])+seq(list(range(count))))
    data = bytearray(b'QLF1'+word(len(embedded))+embedded)
    fields = {}
    def put(name, value):
        fields[name] = len(data)
        data.extend(value)
    put('kind',word(0)); put('effect',word(0)); put('interface',header(r['interface']))
    put('count',word(1)); put('meaning',header(r['meanings'][0]['interface']))
    put('body',body(r['meanings'][0]['body'],True)); put('entry',word(0))
    children = a['definitions'][a['entry']['implementation']]['body']['children']
    put('order',seq(closure(a,[children[0],*children[2:]])))
    return bytes(data), fields


def host_cases(directory):
    a = SharedGradientCircuit().qft(4)
    r = request(4)
    cases = []
    def add(name, artifact=a, required=r, inspect='ok', outcome='contract', executable=''):
        (directory/f'{name}.json').write_text(text(artifact))
        (directory/f'{name}-request.json').write_text(text(required))
        cases.append('|'.join([name,f'{name}.json',f'{name}-request.json',inspect,outcome,executable]))
    for n in range(1,9):
        add(f'width-{n}',SharedGradientCircuit().qft(n),request(n),outcome='ok')
    # Legal artifact adapters do not make the named qft meaning accept Bit or
    # an open owner-renaming boundary; that meaning specifically requires Bits.
    bit=json.loads(text(SharedGradientCircuit().qft(1)))
    req=request(1)
    def outer_bit(v):
        if isinstance(v,dict):
            if v.get('owner')==0 and v.get('basis')==[dict(tag='bits',width=1)]:v['basis']=[dict(tag='bit')]
            for x in v.values():outer_bit(x)
        elif isinstance(v,list):
            for x in v:outer_bit(x)
    outer_bit(bit);outer_bit(req)
    root1=bit['entry']['implementation'];children=bit['definitions'][root1]['body']['children']
    for index,tag in [(children[0],'bit_to_bits'),(children[2],'bits_to_bit')]:
        b=dict(tag='structural',operation=dict(tag=tag))
        bit['definitions'][index]['body']=b;bit['meanings'][index]['body']=copy.deepcopy(b);bit['proofs'][index]['rule']=dict(tag='structural')
    add('named-bit-boundary',bit,req)
    opened=json.loads(text(SharedGradientCircuit().qft(1)));req=request(1)
    root1=opened['entry']['implementation'];leave=opened['definitions'][root1]['body']['children'][2]
    output=copy.deepcopy(req['interface']['outputs']);output['quantum'][0]['owner']=999
    encoding=len(opened['encodings']);opened['encodings'].append(dict(logical=output,physical=copy.deepcopy(output),body=dict(tag='identity')))
    for i in [leave,root1]:
        opened['definitions'][i]['interface']['outputs']=copy.deepcopy(output)
        opened['meanings'][i]['interface']['outputs']=copy.deepcopy(output)
        opened['proofs'][i]['output_encoding']=encoding
    req['interface']['outputs']=copy.deepcopy(output);req['meanings'][0]['interface']=copy.deepcopy(req['interface'])
    add('named-open-boundary',opened,req)
    for field, value in [('kind','instrument'),('effect','observe'),('entry',1)]:
        bad = copy.deepcopy(r); bad[field] = value
        add(f'request-{field}',required=bad,outcome='invalid_ir' if field == 'entry' else 'contract')
    for n in [0,3,9]:
        bad=copy.deepcopy(r);bad['meanings'][0]['body']['width']=n
        add(f'request-width-{n}',required=bad,outcome='limit' if n in (0,9) else 'contract')
    for field in ['owner','axes','basis']:
        bad=copy.deepcopy(r)
        bad['interface']['inputs']['quantum'][0][field]={'owner':99,'axes':[3,2,1,0],'basis':[dict(tag='bits',width=3)]}[field]
        add(f'header-{field}',required=bad)
        bad['meanings'][0]['interface']=copy.deepcopy(bad['interface'])
        add(f'coordinated-header-{field}',required=bad)
    bad=copy.deepcopy(r);bad['meanings'].append(copy.deepcopy(bad['meanings'][0]));add('extra-meaning',required=bad)
    bad=copy.deepcopy(r);bad['checked']=True;add('producer-flag',required=bad,outcome='format')
    root=a['entry']['implementation']
    for fault in ['phase','polarity','repeat','missing-reversal','commuting-swaps','negative-h','x-h','empty-owner']:
        bad=copy.deepcopy(a)
        if fault == 'commuting-swaps':
            children=bad['definitions'][root]['body']['children']
            children=children[:3]+list(reversed(children[3:]))
            bad['definitions'][root]['body']['children']=children
            bad['meanings'][root]['body']['children']=children
            bad['proofs'][root]['premises']=children
        elif fault == 'missing-reversal':
            # Keep all nodes reachable and well typed, while turning each final
            # lifted SWAP into identity in both implementation and meaning.
            for i,d in enumerate(bad['definitions']):
                b=d['body']
                if b['tag']=='rewire' and b['permutation']['owners']==[1,0,2]:
                    b['permutation']['owners']=[0,1,2]
                    b['permutation']['axes']=list(range(len(b['permutation']['axes'])))
                    bad['meanings'][i]['body']=copy.deepcopy(b)
        else:
            for i,d in enumerate(bad['definitions']):
                b=d['body'];m=bad['meanings'][i]['body']
                if fault=='phase' and b['tag']=='dyadic_phase': b['j']=m['j']=2;break
                if fault=='polarity' and b['tag']=='control': b['polarity']=m['polarity']=False;break
                if fault=='repeat' and b['tag']=='repeat': b['count']=m['count']=3;break
                if fault=='empty-owner' and b['tag']=='structural' and b['operation']['tag']=='take_bit':
                    ports=d['interface']['outputs']['quantum'];ports[1]['owner']=ports[0]['owner'];break
                if fault in ('negative-h','x-h') and b['tag']=='leaf':
                    program=json.loads(b['program']);raw=program['programs'][0]
                    matrix=json.loads(m['description'])
                    if fault=='negative-h':
                        tokens=[raw['quantum_inputs'][0]['token'],1000,1001,1002,1003,raw['quantum_outputs'][0]]
                        raw['operations']=[dict(tag='gate',gate=g,input=tokens[j],output=tokens[j+1]) for j,g in enumerate(['h','x','z','x','z'])]
                        for entry in matrix['entries']:
                            for coefficient in entry: coefficient['numerator']=str(-int(coefficient['numerator']))
                    else:
                        raw['operations'][0]['gate']='x'
                        matrix['entries']=[[dict(numerator=str(v if k==0 else 0),denominator_bits=0) for k in range(4)] for v in [0,1,1,0]]
                    b['program']=text(program);m['description']=text(matrix);break
        add(fault,bad,inspect='invalid_ir' if fault=='empty-owner' else 'ok',outcome='invalid_ir' if fault=='empty-owner' else 'ok' if fault=='commuting-swaps' else 'contract')
    # Definition numbering is independent of proof and meaning numbering.
    # JSON round trip separates aliased producer dictionaries so only the
    # definition table is renumbered; meanings keep their original references.
    bad=json.loads(text(a));size=len(bad['definitions']);remap=lambda i:size-1-i
    for d in bad['definitions']:
        b=d['body']
        if b['tag']=='sequence':b['children']=list(map(remap,b['children']))
        for field in (['left','right'] if b['tag']=='tensor' else ['definition'] if b['tag'] in ('repeat','control') else []):b[field]=remap(b[field])
    bad['definitions'].reverse()
    for p in bad['proofs']:p['implementation']=remap(p['implementation'])
    bad['entry']['implementation']=remap(root)
    add('reindexed-definitions',bad,outcome='ok')
    # Malformed subprocess responses must never become checked request reports.
    finite=[i for i,p in enumerate(a['proofs']) if p['rule']['tag']=='finite']
    h=[p['implementation'] for p in a['proofs'] if p['rule']['tag']=='finite']
    header=['qleisli.hierarchy-fourier-pending 1','pending','1',str(len(finite)),*map(str,finite)]
    for name, tail in [('missing-h',['0']),('duplicate-h',['4',*map(str,[h[0]]*4)]),
                       ('outside-h',['4','99999',*map(str,h[1:])]),('nonleaf-h',['4',str(root),*map(str,h[1:])]),
                       ('too-many-h',['9']),('truncated-h',['4',str(h[0])])]:
        response='\n'.join(header+tail)+'\n'
        script=directory/f'mock-{name}'
        script.write_text('#!'+sys.executable+'\nimport sys\nsys.stdin.buffer.read()\nsys.stdout.write('+repr(response)+')\n')
        script.chmod(0o755)
        add(name,outcome='limit' if name=='too-many-h' else 'format',executable=script.name)
    (directory/'cases.txt').write_text('\n'.join(cases)+'\n')
    return len(cases)


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--record',type=Path);args=parser.parse_args()
    kernel=ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel'
    a=SharedGradientCircuit().qft(1);good,fields=binary_frame(a,request(1))
    cases=[('valid',good,'pending'),('magic',b'QLR1'+good[4:],'format'),('trailing',good+b'\0','format')]
    cases += [(f'truncated-{i}',good[:i],'format') for i in [*range(9),*range(fields['kind'],len(good))]]
    for name,field,delta,value,expected in [
        ('instrument','kind',0,1,'format'),('observe','effect',0,2,'format'),
        ('header-owner','interface',4,99,'format'),('meaning-owner','meaning',4,99,'format'),
        ('unknown-body','body',0,99,'format'),('wrong-width','body',4,2,'contract'),
        ('zero-width','body',4,0,'limit'),('missing-entry','entry',0,1,'format'),
        ('large-count','count',0,100001,'limit'),('large-order','order',0,100001,'limit'),
        ('wrong-order','order',4,99999,'invalid_ir')]:
        cases.append((name,replace_word(good,fields[field]+delta,value),expected))
    results=[];start=time.monotonic()
    for name,data,expected in cases:
        p=subprocess.run([str(kernel),'--hierarchy-fourier-pending'],input=data,capture_output=True,timeout=30)
        lines=p.stdout.decode().splitlines();assert lines[:1]==['qleisli.hierarchy-fourier-pending 1'],(name,p)
        actual='pending' if lines[1]=='pending' else lines[2]
        assert actual==expected,(name,actual,expected)
        assert p.returncode==(0 if actual=='pending' else 1)
        if actual=='pending':
            assert 0<int(lines[2])<=2000000
            assert lines[3]=='1' and lines[5]=='1'
        results.append(dict(case=name,result=actual))
    with tempfile.TemporaryDirectory(prefix='qleisli-fourier-host-') as temp:
        directory=Path(temp);count=host_cases(directory)
        env=os.environ.copy();env['QLEISLI_HIERARCHY_KERNEL']=str(kernel);env['QLEISLI_FOURIER_FIXTURES']=str(directory)
        command=['cargo','test','--test','qft_hierarchy','native_fourier_request_faults','--','--ignored','--nocapture']
        run=subprocess.run(command,cwd=ROOT,env=env,capture_output=True,text=True,timeout=120)
    record=dict(format='qleisli.fourier-host-validation',version=1,status='passed' if run.returncode==0 else 'failed',
                binary_cases=len(cases),host_cases=count,results=results,seconds=round(time.monotonic()-start,3),
                binary_sha256=hashlib.sha256(kernel.read_bytes()).hexdigest(),argv=command,exit_code=run.returncode,
                stdout=run.stdout,stderr=run.stderr,semantic_evidence_issued=False)
    if args.record:args.record.write_text(json.dumps(record,indent=2)+'\n')
    print(text({k:v for k,v in record.items() if k not in ('results','stdout','stderr')}))
    if run.returncode:print(run.stdout+run.stderr);raise SystemExit(run.returncode)


if __name__=='__main__':main()
