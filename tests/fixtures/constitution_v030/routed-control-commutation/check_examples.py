#!/usr/bin/env python3
"""Independent small-matrix and original-artifact fixture checks.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
from pathlib import Path
import cmath
import hashlib
import json
import math
import generate_examples
ROOT=Path(__file__).resolve().parent
NAMES=('ab','ba','overlap-ab','overlap-ba','wrong-output-route','unit-ab','unit-ba')

def expected(name,row,col):
    if name.startswith('unit-'):
        return (cmath.exp(1j*math.pi/4) if col==3 else 1) if row==col else 0
    if name=='wrong-output-route':
        row=(row&~3)|((row&1)<<1)|((row&2)>>1)
    if col&4==0:
        return int(row==col)
    if row&14!=col&14:
        return 0
    angle=(row&1) if name=='overlap-ab' else (col&1) if name=='overlap-ba' else ((col>>3)&1)
    return (-1)**((col&1)*(row&1))/math.sqrt(2)*cmath.exp(1j*math.pi/4*angle)

def main():
    artifacts={n:json.loads((ROOT/f'{n}.json').read_text()) for n in NAMES}
    matrices={n:[complex(*x) for x in json.loads((ROOT/f'{n}.matrix.json').read_text())] for n in NAMES}
    errors={}
    for name in NAMES:
        dim=4 if name.startswith('unit-') else 16
        assert len(matrices[name])==dim*dim
        err=max(abs(v-expected(name,i%dim,i//dim)) for i,v in enumerate(matrices[name]))
        assert err<1e-12,(name,err)
        errors[name]=err
    assert matrices['ab']==matrices['ba']
    assert matrices['unit-ab']==matrices['unit-ba']
    negative={}
    for left,right in [('overlap-ab','overlap-ba'),('ab','wrong-output-route')]:
        size,i,x,y=max((abs(x-y),i,x,y) for i,(x,y) in enumerate(zip(matrices[left],matrices[right])))
        assert size>0.5
        negative[f'{left}/{right}']={'row':i%16,'column':i//16,'absolute_difference':size,
                                    'left':[x.real,x.imag],'right':[y.real,y.imag]}
    routes={}
    for name,a in artifacts.items():
        entry=a['definitions'][a['entry']['implementation']]
        dim=sum(len(p['axes']) for p in entry['interface']['inputs']['quantum'])
        current=list(range(dim));maps=[]
        for i in entry['body']['children']:
            d=a['definitions'][i]
            if d['body']['tag']=='rewire':
                axes=d['body']['permutation']['axes'];assert sorted(axes)==list(range(dim))
                current=[current[j] for j in axes];maps.append(axes)
        if name=='wrong-output-route':assert current==[1,0,2,3]
        else:assert current==list(range(dim))
        routes[name]={'actual_maps':maps,'composite':current}
        if name.startswith('unit-'):
            before=entry['interface']['inputs']['quantum'];after=entry['interface']['outputs']['quantum']
            assert len(before)==len(after)==4
            assert [p['axes'] for p in before]==[[],[],[0],[1]]
            assert [p['axes'] for p in after]==[[],[],[0],[1]]
            assert before[0]['basis']==before[1]['basis']==[{'tag':'bits','width':0}]
    assert routes['ab']['actual_maps']!=routes['ba']['actual_maps']
    rendered=generate_examples.render()
    assert (ROOT/'ArtifactData.lean.txt').read_text()==rendered
    assert (ROOT/'Examples.lean').read_text().startswith(rendered)
    # A reference-labelled column pair preserves the phase between control sectors.
    for name in ['ab','ba']:
        joint0=[matrices[name][r] for r in range(16)]
        joint1=[1j*matrices[name][r+16*12] for r in range(16)]
        assert all(abs(v-(1 if r==0 else 0))<1e-12 for r,v in enumerate(joint0))
        assert all(abs(v-(1j*cmath.exp(1j*math.pi/4)/math.sqrt(2) if r in [12,13] else 0))<1e-12
                   for r,v in enumerate(joint1))
    initial=json.loads((ROOT/'initial-source-identities.json').read_text())['files']
    repo=ROOT.parents[3]
    unchanged={}
    for name,digest in initial.items():
        if (name.startswith('lean/') or name.startswith('lean-kernel/')) and name!='lean/Qleisli.lean':
            actual=hashlib.sha256((repo/name).read_bytes()).hexdigest()
            assert actual==digest,name
            unchanged[name]=digest
    result={'status':'passed','matrix_entries_checked':sum(map(len,matrices.values())),
            'max_absolute_errors':errors,'negative_witnesses':negative,'routes':routes,
            'rendered_original_artifact_bytes':len(rendered.encode()),
            'unchanged_preexisting_lean_files':unchanged,
            'scope':'bounded numerical/runtime evidence; the Lean corollary retains explicit original provider/leaf/evaluation premises'}
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()
