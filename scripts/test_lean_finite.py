#!/usr/bin/env python3
"""VM-24 native finite reconstruction, original bytes and independent meanings.

Neither executable receives the other's result. Rust remains production authority.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import native_harness
import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random
import subprocess
import tempfile

import test_lean_exact as exact

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / 'tests/fixtures/verification_v024'
ZERO = [Fraction(0)] * 4
ONE = [Fraction(1), *[Fraction(0)] * 3]


def wire(value):
    return [{'numerator': str(v.numerator), 'denominator_bits': v.denominator.bit_length()-1}
            for v in value]


def description(matrix):
    return dict(format='qleisli.finite-matrix', version=1, domain='zeta8-dyadic-v1',
                rows=len(matrix), cols=len(matrix[0]), entries=[wire(v) for row in matrix for v in row])


def identity(n):
    return [[ONE if r == c else ZERO for c in range(n)] for r in range(n)]


def mono(axes, permutation, phases, controls=()):
    return dict(controls=[dict(index=a, when_one=p) for a, p in controls],
                action=dict(tag='monomial', indices=axes, permutation=permutation, phases=phases))


def hadamard(axis, controls=()):
    return dict(controls=[dict(index=a, when_one=p) for a, p in controls],
                action=dict(tag='hadamard', target=axis))


def call(axes, dependency, adjoint=False, controls=()):
    return dict(controls=[dict(index=a, when_one=p) for a, p in controls],
                action=dict(tag='contract', indices=axes, evidence=dependency, adjoint=adjoint))


def phase(k):
    half = Fraction(1, 2)
    return [[1,0,0,0], [0,half,0,half], [0,0,1,0], [0,-half,0,half],
            [-1,0,0,0], [0,-half,0,-half], [0,0,-1,0], [0,half,0,-half]][k % 8]


def circuit_oracle(body, dependencies=()):
    """Full rational gate matrices composed by polynomial formulas, not columns."""
    n = 2 ** body['basis'].count('bit')
    result = identity(n)
    for step in body['steps']:
        gate = [[ZERO[:] for _ in range(n)] for _ in range(n)]
        action = step['action']
        for source in range(n):
            enabled = all(bool(source & (1 << c['index'])) == c['when_one'] for c in step['controls'])
            if not enabled:
                gate[source][source] = ONE
                continue
            if action['tag'] == 'hadamard':
                target = action['target']
                for output in [0, 1]:
                    dest = (source & ~(1 << target)) | (output << target)
                    gate[dest][source] = [0, Fraction(-1 if (source >> target & 1) and output else 1, 2), 0, 0]
            else:
                axes = action['indices']
                index = sum(((source >> a) & 1) << j for j, a in enumerate(axes))
                if action['tag'] == 'monomial':
                    terms = [(action['permutation'][index], phase(action['phases'][index]))]
                else:
                    meaning = dependencies[action['evidence']]
                    if action['adjoint']:
                        meaning = exact.oracle_adjoint(meaning)
                    terms = [(output, row[index]) for output, row in enumerate(meaning)]
                for output, value in terms:
                    dest = source
                    for j, axis in enumerate(axes):
                        dest = (dest & ~(1 << axis)) | (((output >> j) & 1) << axis)
                    gate[dest][source] = value
        result = exact.oracle_compose(gate, result)
    return result


def contract(basis, logical, input_map=None, output_map=None, logical_basis=None):
    logical_basis = logical_basis or basis
    n = 2 ** basis.count('bit')
    return dict(input=dict(logical=logical_basis, physical=basis, map=description(input_map or identity(n))),
                output=dict(logical=logical_basis, physical=basis, map=description(output_map or identity(n))),
                logical=description(logical))


def artifact(entries, root=0):
    return dict(format='qleisli.finite-component', version=1, root=root, evidence=entries)


def dumps(value):
    return json.dumps(value, separators=(',', ':'),default=str)


def cases():
    cases = []
    def add(name, op, expected=True, **kwargs):
        cases.append(dict(name=name, op=op, expected=expected, budget=kwargs.pop('budget', 10000000), **kwargs))
    matrices = [identity(1), identity(2), exact.oracle_matrix(exact.H),
                [[Fraction(-1),0,0,0]],]
    matrices[-1] = [matrices[-1]]
    matrices += [[[Fraction(1,2),Fraction(1,8),Fraction(-3,16),Fraction(5,32)]]]
    matrices[-1] = [matrices[-1]]
    for i, matrix in enumerate(matrices):
        value = description(matrix)
        for budget in [0, 4*len(value['entries'])-1, 4*len(value['entries']), 10000000, 10000001]:
            add(f'matrix_{i}_work_{budget}', 'matrix', budget >= 4*len(value['entries']) and budget <= 10000000,
                text=dumps(value), budget=budget, oracle=matrix)
    for name, matrix, accepted in [
        ('unit_scalar_unitary', [[[-1,0,0,0]]], True),
        ('hadamard_whole_space', exact.oracle_matrix(exact.H), True),
        ('proper_subspace_only', [[ONE,ZERO],[ZERO,ZERO]], False),
        ('tall_isometry_not_unitary', [[ONE],[ZERO]], False),
    ]:
        add(name,'whole',accepted,text=dumps(description(matrix)),oracle=matrix)
    base = description(identity(1))
    mutations = {
        'unknown_domain': lambda x: x.update(domain='float'),
        'unknown_field': lambda x: x.update(accepted=True),
        'zero_dimension': lambda x: x.update(rows=0),
        'too_large_dimension': lambda x: x.update(rows=65),
        'wrong_entry_count': lambda x: x.update(entries=[]),
        'missing_coefficient': lambda x: x['entries'][0].pop(),
        'unreduced': lambda x: x['entries'][0][0].update(numerator='2',denominator_bits=1),
        'negative_zero': lambda x: x['entries'][0][0].update(numerator='-0'),
        'leading_zero': lambda x: x['entries'][0][0].update(numerator='01'),
        'overflow': lambda x: x['entries'][0][0].update(numerator=str(2**127)),
        'denominator_overflow': lambda x: x['entries'][0][0].update(denominator_bits=127),
        'coefficient_field': lambda x: x['entries'][0][0].update(cache=True),
    }
    for name, mutate in mutations.items():
        value = copy.deepcopy(base); mutate(value)
        add(name, 'matrix', False, text=dumps(value))
    text = dumps(base)
    for name, value in [('duplicate_field', text.replace('"rows":1','"rows":1,"rows":1')),
                        ('escaped_duplicate', text.replace('"rows":1','"rows":1,"r\\u006fws":1')),
                        ('truncated', text[:-1]), ('trailing', text+'null'),
                        ('fraction', text.replace('"rows":1','"rows":1.0')),
                        ('numeric_leading_zero', text.replace('"rows":1','"rows":01')),
                        ('negative_number', text.replace('"rows":1','"rows":-1')),
                        ('unsigned_overflow', text.replace('"rows":1','"rows":18446744073709551616')),
                        ('too_deep', '['*65+'0'+']'*65), ('invalid_utf8_escape', '"\\uD800"')]:
        add(name, 'matrix', False, text=value)
    bodies = [dict(basis=['unit'],steps=[mono([], [0], [4])]),
              dict(basis=['bit'],steps=[hadamard(0),mono([0],[0,1],[0,1])]),
              dict(basis=['pair','bit','bit'],steps=[hadamard(1),mono([0],[1,0],[0,0],[(1,False)])]),
              dict(basis=['tuple:3','bit','unit','bit'],steps=[mono([1,0],[0,2,3,1],[1,7,2,4])]),
              dict(basis=['pair','bit','bit'],steps=[mono([0],[1,0],[0,0],[(1,False)]),mono([1],[1,0],[0,0])]),
              dict(basis=['bit'],steps=[mono([0],[0,1],[0,6]),hadamard(0),mono([0],[0,1],[0,6]),mono([],[0],[7])])]
    for budget in [23,24]:
        body=dict(basis=['bit'],steps=[hadamard(0)])
        add(f'hadamard_precharge_{budget}','circuit',budget==24,body=body,budget=budget,oracle=circuit_oracle(body))
    unit_body=dict(basis=['unit'],steps=[mono([],[0],[0])]*1024)
    for budget in [6143,6144]:
        add(f'unit_step_capacity_{budget}','circuit',budget==6144,body=unit_body,budget=budget,oracle=identity(1))
    add('excess_step_capacity','circuit',False,body=dict(basis=['unit'],steps=unit_body['steps']+[mono([],[0],[0])]))
    add('excess_width_capacity','circuit',False,body=dict(basis=['tuple:7']+['bit']*7,steps=[]))
    add('excess_type_depth','circuit',False,body=dict(basis=['pair','unit']*33+['unit'],steps=[]))
    rng = random.Random(24102026)
    for _ in range(40):
        bits = rng.randrange(1,4)
        basis = ['bit'] if bits == 1 else ['pair','bit','bit'] if bits == 2 else ['tuple:3','bit','bit','bit']
        steps=[]
        for _ in range(rng.randrange(1,8)):
            axes=rng.sample(range(bits),rng.randrange(bits+1))
            permutation=list(range(2**len(axes)));rng.shuffle(permutation)
            available=[a for a in range(bits) if a not in axes]
            controls=[(a,bool(rng.randrange(2))) for a in available if rng.randrange(2)]
            steps.append(mono(axes,permutation,[rng.randrange(8) for _ in permutation],controls))
            if rng.randrange(3)==0: steps.append(hadamard(rng.randrange(bits)))
        bodies.append(dict(basis=basis,steps=steps))
    for i, body in enumerate(bodies):
        meaning = circuit_oracle(body)
        for budget in [0,10000000]:
            add(f'circuit_{i}_work_{budget}', 'circuit', budget != 0, body=body, budget=budget, oracle=meaning)
        claim = contract(body['basis'],meaning)
        add(f'equation_{i}', 'graph', text=dumps(artifact([dict(circuit=body,claim=claim)])),
            required=dumps(claim), order=[0], oracle=meaning)
    base_body = bodies[1]; meaning=circuit_oracle(base_body); claim=contract(base_body['basis'],meaning)
    base_artifact=artifact([dict(circuit=base_body,claim=claim)])
    # Keep required text fixed independently when changing the producer's claim/body.
    def graph_fault(name, mutate, source=base_artifact, required=claim, order=(0,)):
        value=copy.deepcopy(source); mutate(value)
        add(name,'graph',False,text=dumps(value),required=dumps(required),order=list(order))
    graph_fault('wrong_scalar_phase',lambda x:x['evidence'][0]['circuit']['steps'].append(mono([],[0],[4])))
    graph_fault('coordinated_body_claim_mutation',lambda x:(x['evidence'][0]['circuit']['steps'].append(mono([],[0],[4])),
        x['evidence'][0]['claim'].update(logical=description([[[-v for v in e] for e in row] for row in meaning]))))
    graph_fault('changed_owned_type',lambda x:x['evidence'][0]['circuit'].update(basis=['pair','bit','unit']))
    graph_fault('overlapping_control',lambda x:x['evidence'][0]['circuit']['steps'][0].update(controls=[dict(index=0,when_one=True)]))
    graph_fault('out_of_bounds_axis',lambda x:x['evidence'][0]['circuit']['steps'][0]['action'].update(target=1))
    graph_fault('duplicate_permutation',lambda x:x['evidence'][0]['circuit']['steps'][1]['action'].update(permutation=[0,0]))
    graph_fault('unbound_dependency',lambda x:x['evidence'][0]['circuit'].update(steps=[call([0],0)]))
    graph_fault('invalid_tuple_shape',lambda x:x['evidence'][0]['circuit'].update(basis=['tuple:2','bit','unit']))
    graph_fault('producer_success_flag',lambda x:x.update(accepted=True))
    graph_fault('producer_matrix_cache',lambda x:x['evidence'][0].update(matrix=description(meaning)))
    add('shared_work_exhaustion','graph',False,text=dumps(base_artifact),required=dumps(claim),order=[0],budget=100)
    # A proper subspace equation can hold while the full-space physical map is invalid.
    zero_map=[[ONE],[ZERO]]
    bad_dep_body=dict(basis=['bit'],steps=[mono([0],[0,1],[0,0])])
    clean_claim=contract(['bit'],identity(1),zero_map,zero_map,['unit'])
    add('zero_scratch_encoding','graph',text=dumps(artifact([dict(circuit=bad_dep_body,claim=clean_claim)])),
        required=dumps(clean_claim),order=[0],oracle=identity(2))
    zero_dirty=dict(basis=['bit'],steps=[mono([0],[1,0],[0,0])])
    graph_fault('dirty_zero_scratch',lambda x:x['evidence'][0].update(circuit=zero_dirty),
        artifact([dict(circuit=bad_dep_body,claim=clean_claim)]),clean_claim)
    swapped=[[ZERO,ONE],[ONE,ZERO]]
    coordinates=contract(['bit'],identity(2),output_map=swapped)
    add('same_image_different_coordinates','graph',False,
        text=dumps(artifact([dict(circuit=dict(basis=['bit'],steps=[]),claim=coordinates)])),
        required=dumps(coordinates),order=[0])
    compute_body=dict(basis=['pair','bit','bit'],steps=[mono([1],[1,0],[0,0],[(0,True)])])
    computed=[[ONE,ZERO],[ZERO,ZERO],[ZERO,ZERO],[ZERO,ONE]]
    released=[[ONE,ZERO],[ZERO,ONE],[ZERO,ZERO],[ZERO,ZERO]]
    compute_claim=contract(compute_body['basis'],identity(2),computed,released,['bit'])
    add('computed_encoding_uncompute','graph',text=dumps(artifact([dict(circuit=compute_body,claim=compute_claim)])),
        required=dumps(compute_claim),order=[0],oracle=circuit_oracle(compute_body))
    wrong_compute_claim=contract(compute_body['basis'],identity(2),released,released,['bit'])
    add('wrong_computed_encoding','graph',False,text=dumps(artifact([dict(circuit=compute_body,claim=wrong_compute_claim)])),
        required=dumps(wrong_compute_claim),order=[0])
    child=bodies[1];child_meaning=circuit_oracle(child);child_claim=contract(child['basis'],child_meaning)
    parent=dict(basis=['pair','bit','bit'],steps=[call([1],0,False,[(0,False)]),call([1],0,True,[(0,False)])])
    parent_meaning=circuit_oracle(parent,[child_meaning]);parent_claim=contract(parent['basis'],parent_meaning)
    dependency_artifact=artifact([dict(circuit=child,claim=child_claim),dict(circuit=parent,claim=parent_claim)],1)
    add('fresh_dependency_adjoint_control','graph',text=dumps(dependency_artifact),required=dumps(parent_claim),order=[0,1],oracle=parent_meaning)
    graph_fault('changed_dependency',lambda x:x['evidence'][0]['circuit']['steps'].append(mono([],[0],[4])),dependency_artifact,parent_claim,[0,1])
    graph_fault('parent_before_dependency',lambda x:None,dependency_artifact,parent_claim,[1,0])
    graph_fault('duplicate_order',lambda x:None,dependency_artifact,parent_claim,[0,0])
    graph_fault('invalid_root',lambda x:x.update(root=2),dependency_artifact,parent_claim,[0,1])
    restricted=artifact([dict(circuit=bad_dep_body,claim=clean_claim),dict(circuit=dict(basis=['bit'],steps=[call([0],0)]),claim=contract(['bit'],identity(2)))],1)
    graph_fault('restricted_encoding_not_callable',lambda x:None,restricted,contract(['bit'],identity(2)),[0,1])
    for length in [32,33]:
        entries=[];unit_claim=contract(['unit'],identity(1))
        for i in range(length):
            body=dict(basis=['unit'],steps=[] if i==0 else [call([],i-1)])
            entries.append(dict(circuit=body,claim=unit_claim))
        add(f'dependency_depth_{length}','graph',length==32,text=dumps(artifact(entries,length-1)),
            required=dumps(unit_claim),order=list(range(length)),oracle=identity(1))
    # Mutate polarity and ordered axes while keeping the mathematical request fixed.
    for name, i, mutate in [('control_polarity',2,lambda b:b['steps'][1]['controls'][0].update(when_one=True)),
                            ('ordered_axes',3,lambda b:b['steps'][0]['action'].update(indices=[0,1]))]:
        body=copy.deepcopy(bodies[i]);original=contract(body['basis'],circuit_oracle(body));mutate(body)
        add(name,'graph',False,text=dumps(artifact([dict(circuit=body,claim=original)])),required=dumps(original),order=[0])
    return cases


LEAN = '''import Protocol
import Lean
open Lean QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite QleisliKernel.Finite
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
def coeff (x : Coefficient) : Json := Json.arr #[toJson (toString x.numerator),toJson x.exponent]
def scalarJson (x : Scalar) : Json := Json.arr #[coeff x.a,coeff x.b,coeff x.c,coeff x.d]
def matrixJson (x : Matrix) : Json := Json.mkObj [("rows",toJson x.rows),("cols",toJson x.cols),
  ("entries",toJson (x.entries.map scalarJson))]
def adapt {α : Type} (x : Except String α) : WorkM α := lift (x.mapError (fun _ => .invalid))
def execute (value : Json) : WorkM Matrix := do
  let op ← adapt ((← adapt (value.getObjVal? "op")).getStr?)
  if op == "matrix" then QleisliKernel.Protocol.FiniteCodec.readMatrix (← adapt ((← adapt (value.getObjVal? "text")).getStr?))
  else if op == "whole" then do
    let matrix ← QleisliKernel.Protocol.FiniteCodec.readMatrix (← adapt ((← adapt (value.getObjVal? "text")).getStr?))
    wholeSpace matrix
    pure matrix
  else if op == "circuit" then do
    let body ← adapt (QleisliKernel.Protocol.FiniteCodec.circuit (← adapt (value.getObjVal? "body")))
    circuitMatrix [] body
  else do
    let artifact ← QleisliKernel.Protocol.FiniteCodec.readArtifact (← adapt ((← adapt (value.getObjVal? "text")).getStr?))
    let required ← QleisliKernel.Protocol.FiniteCodec.readRequirement (← adapt ((← adapt (value.getObjVal? "required")).getStr?))
    let order ← adapt ((← adapt ((← adapt (value.getObjVal? "order")).getArr?)).toList.mapM Json.getNat?)
    pure (← checkAll artifact order required).meaning
def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := do
      let value ← QleisliKernel.Protocol.FiniteCodec.parse line
      let budget ← (← value.getObjVal? "budget").getNat?
      pure ((execute value).run budget)
    let record := match result with
      | .error _ => Json.mkObj [("accepted",toJson false),("remaining",toJson (0:Nat))]
      | .ok (decision,left) => match decision with
        | .error e => Json.mkObj [("accepted",toJson false),("remaining",toJson left),("error",toJson (reprStr e))]
        | .ok matrix => Json.mkObj [("accepted",toJson true),("remaining",toJson left),("matrix",matrixJson matrix)]
    output.putStrLn record.compress
'''


def rust_basis(atoms):
    cursor=iter(atoms)
    def visit():
        atom=next(cursor)
        if atom=='unit': return 'BasisType::Unit'
        if atom=='bit': return 'BasisType::Bit'
        if atom=='pair': return f'BasisType::pair({visit()},{visit()})'
        return 'BasisType::Tuple(vec!['+','.join(visit() for _ in range(int(atom[6:])))+'])'
    value=visit()
    assert list(cursor)==[]
    return value


def rust_circuit(body):
    result=[]
    for step in body['steps']:
        controls=','.join(f'BitControl{{index:{c["index"]},when_one:{str(c["when_one"]).lower()}}}' for c in step['controls'])
        a=step['action']
        if a['tag']=='hadamard': action=f'CircuitAction::Hadamard{{target:{a["target"]}}}'
        else:
            action='CircuitAction::Monomial{indices:vec!'+repr(a['indices'])+',permutation:vec!'+repr(a['permutation'])+',phases:vec!'+repr(a['phases'])+'}'
        result.append(f'CircuitStep{{controls:vec![{controls}],action:{action}}}')
    return f'Circuit::new({rust_basis(body["basis"])},vec!['+','.join(result)+'])'


def rust_contract(value):
    def enc(e):
        return 'enc('+rust_basis(e['logical'])+','+rust_basis(e['physical'])+','+json.dumps(dumps(e['map']))+',&mut b)?'
    return 'cn('+enc(value['input'])+','+enc(value['output'])+','+json.dumps(dumps(value['logical']))+',&mut b)?'


def rust_graph(case):
    data=json.loads(case['text'])
    if set(data)!={'format','version','root','evidence'}:return None
    if data['root']>=len(data['evidence']): return None
    entry=data['evidence'][data['root']]
    if set(entry)!={'circuit','claim'}:return None
    if len(data['evidence'])!=1 or any(s['action']['tag']=='contract' for s in entry['circuit']['steps']):return None
    claim=rust_contract(entry['claim']);required=rust_contract(json.loads(case['required']))
    body=rust_circuit(entry['circuit'])
    return '(||{let claim='+claim+';let required='+required+';if claim!=required{return None;}'+ \
      'let circuit='+body+'.ok()?;CheckedContract::check(circuit.clone(),claim,&mut b).ok()?;'+ \
      'let actual=circuit.matrix(&mut b).ok()?;if !actual.is_isometry(&mut b).ok()?{return None;}Some(actual)})()'


def native(all_cases, log):
    exact.command(['lake','env','lean','--version'],ROOT/'lean-kernel',log)
    exact.command(['lake','env','leanc','--version'],ROOT/'lean-kernel',log)
    exact.command(['rustc','-vV'],ROOT,log)
    with tempfile.TemporaryDirectory(prefix='qleisli-finite-native-') as directory:
        project=Path(directory)
        (project/'Main.lean').write_text(LEAN)
        binary = native_harness.build(project, log)
        payload='\n'.join(dumps({k:v for k,v in c.items() if k not in {'oracle','expected','name'}}) for c in all_cases)+'\n'
        run=subprocess.run([str(binary)],input=payload,text=True,capture_output=True,timeout=180)
        log.append(dict(command=['finite-test < original JSON requests'],exit=run.returncode,stderr=run.stderr))
        assert run.returncode==0,run.stderr
        lean=[json.loads(line) for line in run.stdout.splitlines()]
        selected=[(i,c) for i,c in enumerate(all_cases) if c['op'] in ['matrix','circuit','whole'] or (c['op']=='graph' and rust_graph(c) is not None)]
        actions=[]
        for _,c in selected:
            budget=c['budget']
            if c['op']=='matrix': expression=f'qleisli::interchange::finite_matrix::decode({json.dumps(c["text"])}.as_bytes(),&mut b).ok()'
            elif c['op']=='whole': expression=f'qleisli::interchange::finite_matrix::decode({json.dumps(c["text"])}.as_bytes(),&mut b).ok().and_then(|x|if x.rows()==x.cols() && x.is_isometry(&mut b).ok()? {{Some(x)}} else {{None}})'
            elif c['op']=='circuit': expression=f'{rust_circuit(c["body"])}.ok().and_then(|x|x.matrix(&mut b).ok())'
            else: expression=rust_graph(c)
            actions.append(f'{{let mut b=Budget::new({budget});let result={expression};show(result,b.remaining());}}')
        rust='''use qleisli::contract::{Circuit,BasisType,Encoding,Contract,CheckedContract};
use qleisli::ir::{CircuitStep,CircuitAction,BitControl};
use qleisli::contract::exact::{Budget,Matrix};
fn show(result:Option<Matrix>,remaining:usize){
 match result {Some(x)=>{let bytes=qleisli::interchange::finite_matrix::encode(&x).unwrap();
 println!("{{\\"accepted\\":true,\\"remaining\\":{},\\"matrix\\":{}}}",remaining,String::from_utf8(bytes).unwrap());},
 None=>println!("{{\\"accepted\\":false,\\"remaining\\":{}}}",remaining)}}
fn enc(logical:BasisType,physical:BasisType,text:&str,b:&mut Budget)->Option<Encoding>{
 let map=qleisli::interchange::finite_matrix::decode(text.as_bytes(),b).ok()?;
 Encoding::new(logical,physical,map,b).ok()}
fn cn(input:Encoding,output:Encoding,text:&str,b:&mut Budget)->Option<Contract>{
 let logical=qleisli::interchange::finite_matrix::decode(text.as_bytes(),b).ok()?;
 Contract::new(input,output,logical,b).ok()}
fn main(){
'''+ '\n'.join(actions)+'\n}\n'
        (project/'Cargo.toml').write_text('[package]\nname="qleisli_finite_test"\nversion="0.0.0"\nedition="2024"\n[dependencies]\nqleisli={path='+json.dumps(str(ROOT))+'}\n[[bin]]\nname="finite-test"\npath="main.rs"\n')
        (project/'main.rs').write_text(rust)
        stdout=exact.command(['cargo','run','--offline','--quiet'],project,log)
        decoder=json.JSONDecoder();records=[]
        while stdout.strip():
            stdout=stdout.lstrip();value,end=decoder.raw_decode(stdout)
            records.append(value);stdout=stdout[end:]
        assert len(records)==len(selected)
        return lean,dict(zip((i for i,_ in selected),records))


def compare(all_cases, lean, rust):
    assert len(all_cases)==len(lean)
    mathematical=0
    for i,(case,result) in enumerate(zip(all_cases,lean)):
        assert result['accepted']==case['expected'],(case['name'],result)
        if i in rust:
            other=rust[i]
            assert result['accepted']==other['accepted'],(case['name'],result,other)
            if case['op']!='graph':
                assert result['remaining']==other['remaining'],(case['name'],result,other)
            if result['accepted']:
                normalized=[[[v['numerator'],v['denominator_bits']] for v in s] for s in other['matrix']['entries']]
                assert result['matrix']['entries']==normalized,(case['name'],result,other)
        if result['accepted']:
            m=result['matrix'];expected=case['oracle']
            assert m['rows']==len(expected) and m['cols']==len(expected[0])
            assert [exact.decoded(v) for v in m['entries']]==[v for row in expected for v in row],case['name']
            if case['op']!='matrix':
                assert exact.oracle_compose(exact.oracle_adjoint(expected),expected)==identity(len(expected))
            mathematical+=1
    return mathematical


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record',type=Path)
    args=parser.parse_args()
    all_cases=cases();log=[]
    lean,rust=native(all_cases,log)
    mathematical=compare(all_cases,lean,rust)
    faults=[]
    for case in all_cases:
        if case['expected'] or case['op']!='graph':continue
        index=all_cases.index(case);wrong=copy.deepcopy(lean);wrong[index]['accepted']=True
        try:compare(all_cases,wrong,rust)
        except AssertionError:faults.append(case['name'])
        else:raise AssertionError('missed '+case['name'])
    semantic_faults=[]
    for name, case_name in [('erased_unit_phase','circuit_0_work_10000000'),
                            ('axis_order','circuit_3_work_10000000'),
                            ('refunded_invalid_description','unreduced')]:
        wrong=copy.deepcopy(lean)
        index=next(i for i,c in enumerate(all_cases) if c['name']==case_name)
        if name=='erased_unit_phase':wrong[index]['matrix']['entries'][0][0][0]='1'
        elif name=='axis_order':
            entries=wrong[index]['matrix']['entries'];entries[4:8],entries[8:12]=entries[8:12],entries[4:8]
        else:wrong[index]['remaining']=all_cases[index]['budget']
        try:compare(all_cases,wrong,rust)
        except AssertionError:semantic_faults.append(name)
        else:raise AssertionError('oracle missed '+name)
    report=dict(native_lean_cases=len(all_cases),native_rust_comparisons=len(rust),
        independent_rational_matrix_checks=mathematical,rejected_inputs=sum(not c['expected'] for c in all_cases),
        detected_graph_faults=faults,detected_semantic_faults=semantic_faults,
        largest_circuit_qubits=3,production_authority='Rust',external_schemas_enabled=0,
        remaining_premises=['RawProgram extraction/ownership/effects (VM-25/26)',
            'native transport/decoder correspondence'],
        budget_scope='Published matrix decoding, direct circuit and whole-space budgets compared exactly. Selected Rust CheckedContract API equations compare acceptance and full matrices; graph work additionally reads all maps, checks whole-space Gram and rechecks the root under one experimental aggregate budget. No production graph price change.',
        cases_sha256=hashlib.sha256(dumps(all_cases).encode()).hexdigest(),outcomes_sha256=hashlib.sha256(dumps(lean).encode()).hexdigest(),
        commands=log,source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [
          ROOT/'lean-kernel/Protocol.lean',ROOT/'lean-kernel/QleisliKernel/Finite.lean',
          ROOT/'lean-kernel/QleisliKernel/Semantics/Finite.lean',ROOT/'lean/Qleisli/Finite.lean',
          ROOT/'lean/Qleisli/Semantics/Finite.lean',ROOT/'src/contract/mod.rs',ROOT/'src/interchange/finite_matrix.rs',Path(__file__).resolve()]})
    if args.record:
        args.record.write_text(json.dumps(report,indent=2)+'\n')
        args.record.with_name('native-inputs.json').write_text('[\n'+',\n'.join(dumps(case) for case in all_cases)+'\n]\n')
    print(f'{len(all_cases)} native Lean cases; {len(rust)} Rust comparisons; {mathematical} independent matrices; {len(faults)} graph fault detectors')


if __name__=='__main__':main()
