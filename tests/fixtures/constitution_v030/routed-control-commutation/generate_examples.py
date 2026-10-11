#!/usr/bin/env python3
"""Render frozen JSON data as literal Lean artifact records; no source lowering.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
from pathlib import Path
import json
ROOT = Path(__file__).resolve().parent

def array(items):
    return '#[' + ','.join(items) + ']'
def nums(items):
    return array(map(str, items))
def atom(a):
    tag = a['tag']
    return '.' + tag + (f" {a['width']}" if tag == 'bits' else f" {a['arity']}" if tag == 'tuple' else '')
def side(s):
    assert not s['classical']
    return '⟨' + array(f"⟨{p['owner']},{array(map(atom,p['basis']))},{nums(p['axes'])}⟩" for p in s['quantum']) + ',#[]⟩'
def interface(i):
    return '⟨' + side(i['inputs']) + ',' + side(i['outputs']) + '⟩'
def portmap(p):
    return f"⟨{nums(p['owners'])},{nums(p['axes'])},{nums(p['classical'])}⟩"
def body(b):
    tag = b['tag']
    if tag in ['leaf','finite']:
        key = 'program' if tag == 'leaf' else 'description'
        return f".{tag} ({json.dumps(b[key],ensure_ascii=False)}).toUTF8"
    if tag == 'sequence': return '.sequence ' + nums(b['children'])
    if tag == 'rewire': return '.rewire ' + portmap(b['permutation'])
    if tag == 'tensor': return f".tensor {b['left']} {b['right']}"
    if tag == 'control': return f".control {b.get('definition',b.get('child'))} {str(b['polarity']).lower()}"
    if tag == 'dyadic_phase': return f".dyadicPhase {b['target']} {b['j']} {b['k']}"
    if tag == 'phase': return f".phase {b['j']} {b['k']}"
    if tag == 'identity': return '.identity'
    raise ValueError(tag)
def artifact(a):
    definitions = array(f"⟨{interface(d['interface'])},.{d['effect']},{body(d['body'])}⟩" for d in a['definitions'])
    meanings = array(f"⟨{interface(d['interface'])},{body(d['body'])}⟩" for d in a['meanings'])
    encodings = array(f"⟨{side(e['logical'])},{side(e['physical'])},{body(e['body'])}⟩" for e in a['encodings'])
    def proof(p):
        w=p['witness'];assert not w['references']
        return f"⟨.{p['kind']},.{p['rule']['tag']},{nums(p['premises'])},{p['implementation']},{p['meaning']},{p['input_encoding']},{p['output_encoding']},⟨{w['template_version']},{nums(w['parameters'])},#[]⟩⟩"
    proofs=array(map(proof,a['proofs']))
    return f"⟨\n  {definitions},\n  {meanings},\n  {encodings},\n  {proofs},\n  ⟨{a['entry']['implementation']},{a['entry']['proof']}⟩⟩"

prefix='''import Qleisli.RoutedControlCommutation
import Protocol.HierarchicalFinite

/-! Literal original emitted artifact data plus a conditional instantiation of
actual-body commutation. The JSON/Lean rendering is checked by this fixture's
recorder, not proved as a codec theorem. Native inspection and exact semantic
proof are separately recorded. Copyright 2026 Masahiko G. Yamada.
SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RoutedControlCommutation.Examples
open QleisliKernel.Hierarchical
open Artifact HierarchicalOperators HierarchicalUnitary HierarchicalSemantics
open Qleisli.CoordinateOperators (Bits)
open scoped BigOperators Matrix

'''
def render():
    result = prefix
    for order in ['ab','ba']:
        original=json.loads((ROOT/f'{order}.json').read_text())
        result+=f'private def {order} : Artifact := '+artifact(original)+'\n\n'
    return result

if __name__ == '__main__':
    rendered=render()
    (ROOT/'ArtifactData.lean.txt').write_text(rendered)
    print('Rendered original artifact records:',len(rendered.encode()),'bytes')
