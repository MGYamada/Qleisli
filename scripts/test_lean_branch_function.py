#!/usr/bin/env python3
"""Fresh VM-26 full classical-branch function graphs, independent Rust and R8.
Every checker receives original bodies/identities and separate bindings only.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import native_harness
import argparse
import ast
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

import test_lean_exact as exact
import test_lean_finite as finite
import test_lean_raw as raw
import test_lean_observation as observation
import test_lean_raw_completion as completion
ROOT = raw.ROOT


def cases():
    records = [c for c in completion.cases() if c['mode'] == 'functions']
    def add(name, body, expected=True, bindings=None, **extra):
        entry = completion.attached(dict(signature=['bit'], implementation=body,
            specification=raw.program(1)), sources=[('main.qli','original closed branch source\n')])
        records.append(dict(name=name,functions=[entry],bindings=copy.deepcopy([entry] if bindings is None else bindings),
                            mode='functions',budget=100000000,expected=expected,**extra))
    for a in [False,True]:
        for b in [False,True]:
            ops=[raw.op('classical_const',value=a,output=0),raw.op('classical_const',value=b,output=1),
                 raw.op('classical_xor',left=0,right=1,output=2),raw.op('classical_not',input=2,output=3),
                 raw.op('classical_and',left=2,right=3,output=4),
                 observation.branch(4, [raw.op('gate',gate='x',input=0,output=1)],[],
                    [observation.qphi(1,0,2,[1])])]
            add('closed_truth_'+str(a)+str(b),observation.p([raw.port(0,[0])],operations=ops,outputs=[2],effect='unitary'),counts=[1],depths=[1])
    for choice in [False,True]:
        body=observation.p([raw.port(0,[0])],operations=[raw.op('classical_const',value=choice,output=0),
            observation.branch(0,[raw.op('gate',gate='x',input=0,output=1)],
                [raw.op('gate',gate='z',input=0,output=2)],[observation.qphi(1,2,3,[1])])],outputs=[3],effect='unitary')
        entry=completion.attached(dict(signature=['bit'],implementation=body,
            specification=raw.program(1,[raw.op('gate',gate='x' if choice else 'z',input=0,output=1)],1)), sources=[('branch.qli','original branch source')])
        records.append(dict(name='selected_'+str(choice),functions=[entry],bindings=copy.deepcopy([entry]),
            mode='functions',budget=100000000,expected=True,counts=[1],depths=[1]))
    base=copy.deepcopy(records[-2])
    for name,mutation,binding in [
        ('unselected_invalid_owner',lambda e:e['implementation']['operations'][1]['then_ops'][0].update(input=99),False),
        ('global_identity_across_arms',lambda e:e['implementation']['operations'][1]['then_ops'][0].update(output=2),False),
        ('missing_quantum_phi',lambda e:e['implementation']['operations'][1].update(quantum_phis=[]),False),
        ('same_operator_changed_unselected_arm',lambda e:e['implementation']['operations'][1]['then_ops'][0].update(gate='h'),True),
        ('changed_branch_source',lambda e:e['identity']['sources'][0].update(source='changed source'),True),
    ]:
        changed=copy.deepcopy(base);changed.update(name=name,expected=False)
        mutation(changed['functions'][0])
        if not binding:changed['bindings']=copy.deepcopy(changed['functions'])
        records.append(changed)
    changed=copy.deepcopy(base);changed.update(name='phase_in_selected_specification',expected=False)
    changed['functions'][0]['specification']=raw.program(1,[raw.op('apply_unitary',input=0,output=1,
        steps=[finite.mono([0],[0,1],[0,4]),finite.mono([], [0],[4])])],1)
    changed['bindings']=copy.deepcopy(changed['functions']);records.append(changed)
    # Classical phis feed a subsequent quantum branch; source values are simultaneous.
    body=observation.p([raw.port(0,[0])],operations=[raw.op('classical_const',value=True,output=0),
        observation.branch(0,[raw.op('classical_const',value=True,output=1)],
            [raw.op('classical_const',value=False,output=2)],[observation.qphi(0,0,1,[1])],
            [observation.cphi(1,2,3),observation.cphi(0,0,4)]),
        observation.branch(3,[raw.op('gate',gate='x',input=1,output=2)],[],[observation.qphi(2,1,3,[2])]),
        raw.op('gate',gate='x',input=3,output=4)],outputs=[4],effect='unitary')
    add('classical_phi_drives_second_branch',body,counts=[2],depths=[1])
    changed=copy.deepcopy(records[-1]);changed.update(name='phi_reads_earlier_phi_output',expected=False)
    changed['functions'][0]['implementation']['operations'][1]['classical_phis'][1]['then_id']=3
    changed['bindings']=copy.deepcopy(changed['functions']);records.append(changed)
    # Calls in unselected arms must resolve in the freshly reconstructed prefix.
    hbody=raw.program(1,[raw.op('gate',gate='h',input=0,output=1)],1)
    first=completion.attached(dict(signature=['bit'],implementation=hbody,specification=hbody),'H')
    second_body=observation.p([raw.port(0,[0])],operations=[raw.op('classical_const',value=False,output=0),
        observation.branch(0,[raw.op('apply_unitary',input=0,output=1,steps=[finite.call([0],0)])],[],
            [observation.qphi(1,0,2,[1])])],outputs=[2],effect='unitary')
    second=completion.attached(dict(signature=['bit'],implementation=second_body,specification=raw.program(1)),'g')
    records.append(dict(name='unselected_prefix_dependency',functions=[first,second],bindings=copy.deepcopy([first,second]),
        mode='functions',budget=100000000,expected=True,counts=[1,1],depths=[1,2]))
    changed=copy.deepcopy(records[-1]);changed.update(name='unselected_forward_dependency',expected=False,rust=False)
    changed['functions'][1]['implementation']['operations'][1]['then_ops'][0]['steps'][0]['action']['evidence']=2
    changed['bindings']=copy.deepcopy(changed['functions']);records.append(changed)
    changed=copy.deepcopy(records[-2]);changed.update(name='changed_dependency_meaning',expected=False)
    changed['functions'][0]['specification']=raw.program(1)
    changed['bindings']=copy.deepcopy(changed['functions']);records.append(changed)
    reverse=observation.branch(0,quantum=[observation.qphi(2,2,3,[2]),observation.qphi(1,1,4,[3])])
    routed=observation.p([raw.port(0,[0,1])],operations=[raw.op('classical_const',value=True,output=0),
        raw.op('split',input=0,left=1,right=2,left_bits=1),reverse,raw.op('join',left=3,right=4,output=5)],
        outputs=[5],effect='unitary')
    swapped=raw.program(2,[raw.op('split',input=0,left=1,right=2,left_bits=1),raw.op('join',left=2,right=1,output=3)],3)
    entry=completion.attached(dict(signature=['pair','bit','bit'],implementation=routed,specification=swapped),'route')
    records.append(dict(name='branch_complete_permutation',functions=[entry],bindings=copy.deepcopy([entry]),
        mode='functions',budget=100000000,expected=True,counts=[1],depths=[1]))
    twice=observation.p([raw.port(0,[0,1])],operations=[raw.op('classical_const',value=True,output=0),
        raw.op('split',input=0,left=1,right=2,left_bits=1),reverse,
        raw.op('gate',gate='x',input=3,output=5),
        observation.branch(0,quantum=[observation.qphi(4,4,6,[4]),observation.qphi(5,5,7,[5])]),
        raw.op('join',left=6,right=7,output=8)],outputs=[8],effect='unitary')
    target_x=raw.program(2,[raw.op('apply_unitary',input=0,output=1,steps=[finite.mono([1],[1,0],[0,0])])],1)
    entry=completion.attached(dict(signature=['pair','bit','bit'],implementation=twice,specification=target_x),'twice')
    records.append(dict(name='composite_route_cancels_with_gate',functions=[entry],bindings=copy.deepcopy([entry]),
        mode='functions',budget=100000000,expected=True,counts=[1],depths=[1]))
    low=copy.deepcopy(base);low.update(name='work_exhausted',budget=0,expected=False,rust=False);records.append(low)
    return records


LEAN = 'import Protocol.BranchFunction\n'+finite.LEAN[:finite.LEAN.index('def execute')]+'''
def execute (value : Json) : WorkM Json := do
  let functions ← adapt (QleisliKernel.Protocol.BranchFunction.inputs (← adapt (value.getObjVal? "functions")))
  let bindings ← adapt (QleisliKernel.Protocol.BranchFunction.inputs (← adapt (value.getObjVal? "bindings")))
  let receipts ← QleisliKernel.Raw.BranchFunction.checkAll functions bindings
  return Json.mkObj [("receipts",toJson (receipts.map fun r =>
    Json.mkObj [("depth",toJson r.depth),("expanded",toJson r.expandedSteps),("matrix",matrixJson r.meaning)]))]
'''+finite.LEAN[finite.LEAN.index('def main'):].replace('("matrix",matrixJson matrix)','("result",matrix)')


def rust_compare(records, project, log):
    actions=[]
    for case in records:
        if not case.get('rust',True) or case['name'] in {'self_dependency','forward_dependency','producer_accepted_rejected','producer_matrix_rejected'}:continue
        commands=[]
        for entry,binding in zip(case['functions'],case['bindings']):
            commands.append('let receipt=FunctionEvidence::check('+finite.rust_basis(entry['signature'])+','+
                observation.rust_program(entry['implementation'])+','+observation.rust_program(entry['specification'])+','+
                completion.rust_identity(entry['identity'])+',&mut budget).ok()?;')
            commands.append('receipt.check_binding(&'+finite.rust_basis(binding['signature'])+',&'+completion.rust_identity(binding['identity'])+',&'+
                observation.rust_program(binding['implementation'])+',&'+observation.rust_program(binding['specification'])+').ok()?;')
            commands.append('receipts.push(std::sync::Arc::new(receipt));')
        if len(case['functions'])!=len(case['bindings']):commands.append('return None;')
        commands.append('Some(receipts.iter().map(|r|(r.depth(),r.expanded_steps())).collect::<Vec<_>>())')
        actions.append('let result=(||{let mut budget=Budget::new(100000000);let mut receipts:Vec<std::sync::Arc<FunctionEvidence>>=vec![];'+''.join(commands)+'})();'+
            'println!("{} {} {:?}",'+json.dumps(case['name'])+',result.is_some(),result);')
    source='#![allow(unused_variables,unused_mut,unreachable_code)]\nuse qleisli::ir::*;\nuse qleisli::contract::{FunctionEvidence,FunctionIdentity,BasisType};\nuse qleisli::contract::exact::Budget;\nfn main(){\n'+'\n'.join(actions)+'\n}\n'
    (project/'main.rs').write_text(source)
    (project/'Cargo.toml').write_text('[package]\nname="branch_function_test"\nversion="0.0.0"\nedition="2024"\n[dependencies]\nqleisli={path='+json.dumps(str(ROOT))+'}\n[[bin]]\nname="branch-functions"\npath="main.rs"\n')
    output=exact.command(['cargo','run','--offline','--quiet'],project,log)
    results={}
    for line in output.splitlines():
        name,ok,stats=line.split(' ',2);results[name]=dict(accepted=ok=='true')
        if ok=='true':
            vals=ast.literal_eval(stats[5:-1]);results[name].update(depths=[v[0] for v in vals],counts=[v[1] for v in vals])
    return results,output


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--record',type=Path,required=True);args=parser.parse_args()
    records=cases();log=[]
    payload='\n'.join(finite.dumps({k:c[k] for k in ['functions','bindings','budget']}) for c in records)+'\n'
    with tempfile.TemporaryDirectory(prefix='qleisli-branch-functions-') as directory:
        project=Path(directory)
        (project/'Main.lean').write_text(LEAN)
        binary = native_harness.build(project, log)
        run=subprocess.run([str(binary)],input=payload,text=True,capture_output=True,timeout=180)
        assert run.returncode==0,run.stderr
        observed=[json.loads(line) for line in run.stdout.splitlines()]
        rust,rust_output=rust_compare(records,project,log)
        args.record.parent.mkdir(parents=True,exist_ok=True)
        args.record.with_name('branch-observed.json').write_text(json.dumps(dict(lean=observed,rust=rust),indent=2)+'\n')
        assert len(observed)==len(records)
        matrices=0
        for case,actual in zip(records,observed):
            assert actual['accepted']==case['expected'],(case['name'],actual)
            if case['name'] in rust:assert rust[case['name']]['accepted']==case.get('native_expected',actual['accepted']),(case['name'],actual,rust[case['name']])
            if not actual['accepted']:continue
            receipts=actual['result']['receipts']
            if 'counts' in case:
                assert [r['expanded'] for r in receipts]==case['counts'],(case['name'],receipts)
                assert [r['depth'] for r in receipts]==case['depths'],case['name']
                if case['name'] in rust and rust[case['name']]['accepted']:assert rust[case['name']]['counts']==case['counts'] and rust[case['name']]['depths']==case['depths'],(case['name'],rust[case['name']])
            dependencies=[]
            for entry,receipt in zip(case['functions'],receipts):
                if case['name'] in {'six_auxiliary_metadata_two_bit_h','high_auxiliary_bit_exact_phase'}:
                    # Auxiliary capacities are metadata; compare the independently
                    # fixed small logical specification, never a wide physical matrix.
                    wanted=observation.oracle(entry['specification'],dependencies=dependencies)
                else:
                    wanted=observation.oracle(entry['implementation'],dependencies=dependencies)
                assert len(wanted)==1 and not wanted[0]['hidden'],case['name']
                operator=wanted[0]['operator'];matrix=receipt['matrix']
                assert matrix['rows']==len(operator) and matrix['cols']==len(operator[0]),case['name']
                assert [exact.decoded(v) for v in matrix['entries']]==[v for row in operator for v in row],case['name']
                dependencies.append(operator);matrices+=1
        bindings=dict(native_binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
            native_input_sha256=hashlib.sha256(payload.encode()).hexdigest(),native_stdout_sha256=hashlib.sha256(run.stdout.encode()).hexdigest(),
            rust_binary_sha256=hashlib.sha256((project/'target/debug/branch-functions').read_bytes()).hexdigest(),
            rust_stdout_sha256=hashlib.sha256(rust_output.encode()).hexdigest())
    args.record.write_text(json.dumps(dict(status='passed',native_cases=len(records),rust_comparisons=len(rust),
        native_boundary_differences=[dict(name=c['name'],component=c['expected'],native=c['native_expected'],reason=c['native_boundary']) for c in records if 'native_expected' in c],
        exact_original_operators=matrices,max_semantic_qubits=2,native_bindings=bindings,commands=log,
        source_sha256={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in [
            ROOT/'lean-kernel/QleisliKernel/ObservationBinding.lean',ROOT/'lean-kernel/QleisliKernel/Raw/BranchFunction.lean',
            ROOT/'lean-kernel/QleisliKernel/Semantics/ObservingFunction.lean',ROOT/'lean-kernel/Protocol/BranchFunction.lean',
            ROOT/'lean/Qleisli/RawBranchFunction.lean',ROOT/'lean/Qleisli/Semantics/ObservingFunction.lean',Path(__file__)]}),indent=2)+'\n')
    args.record.with_name('branch-inputs.json').write_text(json.dumps(records,indent=2)+'\n')
    print(f'{len(records)} native branch-function cases; {len(rust)} Rust comparisons; {matrices} exact operators')

if __name__=='__main__':main()
