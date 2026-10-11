#!/usr/bin/env python3
"""VM-25 complete attachments, capacities and non-dense pure checking.

Original data and independently selected bindings go to both native checkers.
Semantic matrices remain at three qubits; wide cases inspect metadata only.
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

ROOT = raw.ROOT


def attached(body, name='f', sources=()):
    return dict(**copy.deepcopy(body), identity=dict(implementation=name,
        specification=name+'.reference', sources=[dict(name=n, source=s) for n, s in sources]))


def cases():
    result = []
    def add(name, functions, expected=True, mode='functions', program=None, bindings=None, **extra):
        result.append(dict(name=name, functions=copy.deepcopy(functions),
            bindings=copy.deepcopy(functions if bindings is None else bindings), mode=mode,
            program=raw.program(0) if program is None else program, budget=100000000,
            expected=expected, **extra))
    unit = attached(dict(signature=['unit'], implementation=raw.program(0), specification=raw.program(0)),
                    sources=[('empty.qli', 'fn empty(q: Q<Unit>) -> Q<Unit> { q }\n')])
    add('exact_attachment', [unit], counts=[1], depths=[1])
    for field in ['implementation', 'specification', 'sources']:
        changed = copy.deepcopy(unit)
        changed['identity'][field] = ('changed' if field != 'sources' else [dict(name='empty.qli', source='changed')])
        add('changed_identity_'+field, [changed], False, bindings=[unit])
    changed = copy.deepcopy(unit)
    changed['implementation'] = raw.program(0, [raw.op('apply_unitary', input=0, output=1,
        steps=[finite.mono([], [0], [0])])], 1)
    add('same_matrix_changed_body', [changed], False, bindings=[unit])
    changed = copy.deepcopy(unit); changed['signature'] = ['pair', 'unit', 'unit']
    add('same_width_changed_type_tree', [changed], False, bindings=[unit])
    for name, mutate in [
        ('empty_implementation', lambda x: x.update(implementation='')),
        ('empty_specification', lambda x: x.update(specification='')),
        ('long_utf8_identity', lambda x: x.update(implementation='λ'*2049)),
        ('duplicate_source', lambda x: x.update(sources=[dict(name='x', source='a'), dict(name='x', source='b')])),
        ('excess_sources', lambda x: x.update(sources=[dict(name=str(i), source='') for i in range(129)])),
        ('long_source_name', lambda x: x.update(sources=[dict(name='x'*4097, source='')])),
        ('excess_source_bytes', lambda x: x.update(sources=[dict(name='x', source='x'*1048576)])),
    ]:
        entry = copy.deepcopy(unit); mutate(entry['identity']); add(name, [entry], False)
    entry = copy.deepcopy(unit); entry['identity']['implementation'] = 'λ'*2048
    add('utf8_identity_boundary', [entry])
    entry = copy.deepcopy(unit); entry['identity']['sources'] = [dict(name='', source='')]
    # The component permits an empty provenance name. The public native QIRF
    # envelope independently requires nonempty source path labels after #276.
    add('empty_source_name_allowed', [entry], native_expected=False,
        native_boundary='QIRF requires nonempty source path labels')
    add('missing_binding', [unit], False, bindings=[])
    add('extra_binding', [], False, bindings=[unit])
    for field, value in [('accepted', True), ('matrix', finite.description(finite.identity(1)))]:
        entry = copy.deepcopy(unit); entry[field] = value
        add('producer_'+field+'_rejected', [entry], False)
    def graph(size, repeat):
        entries = [copy.deepcopy(unit)]
        for i in range(1, size):
            body = raw.program(0, [raw.op('apply_unitary', input=0, output=1,
                steps=[finite.call([], i-1) for _ in range(repeat)])], 1)
            entries.append(attached(dict(signature=['unit'], implementation=body, specification=body), str(i)))
        return entries
    add('depth_32', graph(32, 1), counts=[1]*32, depths=list(range(1, 33)),
        native_expected=False, native_boundary='production QIRF graph/work bounds')
    add('depth_33', graph(33, 1), False)
    add('expanded_524288', graph(20, 2), counts=[2**i for i in range(20)], depths=list(range(1, 21)),
        native_expected=False, native_boundary='production QIRF graph/work bounds')
    add('expanded_1048576_rejected', graph(21, 2), False)
    for name, index in [('self_dependency', 0), ('forward_dependency', 1)]:
        body = raw.program(0, [raw.op('apply_unitary', input=0, output=1, steps=[finite.call([], index)])], 1)
        add(name, [attached(dict(signature=['unit'], implementation=body, specification=body))], False)
    for count in [1024, 1025]:
        body = raw.program(0, [raw.op('apply_unitary', input=0, output=1,
            steps=[finite.mono([], [0], [0])]*count)], 1)
        add('literal_steps_'+str(count), [attached(dict(signature=['unit'], implementation=body, specification=body))],
            count == 1024, counts=[count], depths=[1])
    bad = copy.deepcopy(unit); bad['specification'] = raw.program(0,
        [raw.op('apply_unitary', input=0, output=1, steps=[finite.mono([], [0], [4])])], 1)
    add('phase_sensitive_body_equation', [bad], False)
    # Only the two-qubit logical operator is evaluated. Auxiliary widths are
    # metadata; zero return is the general proved non-dense law, not an 8-qubit matrix.
    uses = [dict(tag='controlled_target_gate',
        controls=[dict(bit=dict(region='ancilla',index=5),when_one=False)],target_index=0,gate='h')]
    actual = raw.program(2,[raw.op('split',input=0,left=1,right=2,left_bits=1),
        raw.op('compute_use_uncompute',source=1,source_out=3,targets=[dict(input=2,output=4)],
            ancilla_wires=list(range(2,8)),function=[0,0],use_ops=uses),
        raw.op('join',left=3,right=4,output=5)],5)
    specified = raw.program(2,[raw.op('apply_unitary',input=0,output=1,steps=[finite.hadamard(1)])],1)
    entry = attached(dict(signature=['pair','bit','bit'],implementation=actual,specification=specified))
    add('six_auxiliary_metadata_two_bit_h', [entry], counts=[2],depths=[1])
    changed=copy.deepcopy(entry); changed['implementation']['operations'][1]['ancilla_wires'].append(8)
    add('seven_auxiliary_function_metadata_rejected',[changed],False)
    actual = raw.program(1,[raw.op('compute_use_uncompute',source=0,source_out=1,targets=[],
        ancilla_wires=list(range(1,7)),function=[0,32],
        use_ops=[dict(tag='protected_gate',bit=dict(region='ancilla',index=5),gate='t')])],1)
    specified = raw.program(1,[raw.op('apply_unitary',input=0,output=1,steps=[finite.mono([0],[0,1],[0,1])])],1)
    add('high_auxiliary_bit_exact_phase',
        [attached(dict(signature=['bit'],implementation=actual,specification=specified))],counts=[1],depths=[1])
    # Scope validation uses one source bit and one target bit; no large state is evaluated.
    p = dict(quantum_inputs=[raw.port(0,[0]),raw.port(1,[1])], classical_inputs=[],
        operations=[raw.op('compute_use_uncompute',source=0,source_out=2,
            targets=[dict(input=1,output=3)],ancilla_wires=[2],function=[0,1],
            use_ops=[dict(tag='controlled_target_gate',controls=[dict(bit=dict(region='ancilla',index=0),when_one=True)],
                          target_index=0,gate='h')])], quantum_outputs=[2,3],classical_outputs=[],declared_effect='unitary')
    add('original_target_h_protected_scope', [], mode='structured', program=p)
    dirty = copy.deepcopy(p); dirty['operations'][0]['use_ops'] = [dict(tag='protected_gate',bit=dict(region='ancilla',index=0),gate='x')]
    add('original_protected_x_rejected', [], False, mode='structured', program=dirty)
    # Metadata only: the checker constructs no vector/matrix for this frame.
    add('twelve_bit_metadata', [], mode='structured', program=raw.program(12))
    add('thirteen_bit_metadata_rejected', [], False, mode='structured', program=raw.program(13))
    for case in raw.cases():
        if case['name'].startswith(('producer_', 'unknown_')): continue
        functions = [attached(e, str(i)) for i, e in enumerate(case['artifact']['evidence'])]
        add('bounded_'+case['name'], functions, case['expected'], mode='bounded',
            program=case['artifact']['program'], required=case['required'], oracle=case.get('oracle'))
        result[-1]['budget'] = case['budget']
    return result


LEAN = finite.LEAN[:finite.LEAN.index('def execute')] + '''
import QleisliKernel.Raw.Pure
def inputs (value : Json) (field : String) : WorkM (List QleisliKernel.Semantics.Function.Input) :=
  adapt (do
    let values ← (← value.getObjVal? field).getArr?
    values.toList.mapM QleisliKernel.Protocol.Raw.functionInput)
def receiptsJson (values : List QleisliKernel.Semantics.Function.Receipt) : Json :=
  toJson (values.map fun r => Json.mkObj [("depth",toJson r.depth),("expanded",toJson r.expandedSteps)])
def execute (value : Json) : WorkM Json := do
  let functions ← inputs value "functions"
  let bindings ← inputs value "bindings"
  let mode ← adapt ((← adapt (value.getObjVal? "mode")).getStr?)
  if mode == "functions" then
    return Json.mkObj [("receipts",receiptsJson (← QleisliKernel.Raw.Function.checkAll functions bindings))]
  let body ← adapt (QleisliKernel.Protocol.Raw.program (← adapt (value.getObjVal? "program")))
  if mode == "structured" then
    let checked ← QleisliKernel.Raw.Pure.inspect functions bindings body
    return Json.mkObj [("receipts",receiptsJson checked.receipts)]
  let required ← QleisliKernel.Protocol.FiniteCodec.readMatrixValue (← adapt (value.getObjVal? "required"))
  let actual ← QleisliKernel.Raw.Function.inspect functions bindings body required
  return Json.mkObj [("matrix",matrixJson actual)]
''' + finite.LEAN[finite.LEAN.index('def main'):].replace(
    '("matrix",matrixJson matrix)', '("result",matrix)')
# Imports must precede declarations in a standalone module.
LEAN = LEAN.replace('\nimport QleisliKernel.Raw.Pure\n', '\n')
LEAN = 'import QleisliKernel.Raw.Pure\n' + LEAN


def rust_identity(identity):
    def string(value):
        # JSON syntax escapes differ only for control escapes not used by these fixtures.
        return json.dumps(value, ensure_ascii=False)+'.into()'
    sources = ','.join('('+string(x['name'])+','+string(x['source'])+')' for x in identity['sources'])
    return 'FunctionIdentity{implementation:'+string(identity['implementation'])+',specification:'+string(identity['specification'])+',sources:vec!['+sources+']}'


def compare_rust(all_cases, project, log):
    actions = []
    for case in all_cases:
        if case['mode'] == 'bounded' or case['name'] in {
                'self_dependency','forward_dependency','producer_accepted_rejected','producer_matrix_rejected'}: continue
        commands = []
        for entry, binding in zip(case['functions'], case['bindings']):
            commands.append('let receipt=FunctionEvidence::check('+finite.rust_basis(entry['signature'])+','+
                raw.rust_program(entry['implementation'])+','+raw.rust_program(entry['specification'])+','+
                rust_identity(entry['identity'])+',&mut budget).ok()?;')
            commands.append('receipt.check_binding(&'+finite.rust_basis(binding['signature'])+',&'+rust_identity(binding['identity'])+',&'+
                raw.rust_program(binding['implementation'])+',&'+raw.rust_program(binding['specification'])+').ok()?;')
            commands.append('receipts.push(std::sync::Arc::new(receipt));')
        if len(case['functions']) != len(case['bindings']): commands.append('return None;')
        if case['mode'] == 'structured': commands.append('qleisli::interchange::native::Kernel::selected().expect("explicit native checker").accept_raw('+raw.rust_program(case['program'])+').ok()?;')
        commands.append('Some(receipts.iter().map(|r|(r.depth(),r.expanded_steps())).collect::<Vec<_>>())')
        actions.append('let result=(||{let mut budget=Budget::new(100000000);let mut receipts:Vec<std::sync::Arc<FunctionEvidence>>=vec![];'+''.join(commands)+'})();'+
            'println!("{} {} {:?}",'+json.dumps(case['name'])+',result.is_some(),result);')
    rust = '#![allow(unused_variables,unused_mut,unreachable_code)]\nuse qleisli::ir::*;\nuse qleisli::contract::{FunctionEvidence,FunctionIdentity,BasisType};\nuse qleisli::contract::exact::Budget;\nfn main(){\n'+'\n'.join(actions)+'\n}\n'
    (project/'main.rs').write_text(rust)
    (project/'Cargo.toml').write_text('[package]\nname="raw_completion_test"\nversion="0.0.0"\nedition="2024"\n[dependencies]\nqleisli={path='+json.dumps(str(ROOT))+'}\n[[bin]]\nname="raw-completion"\npath="main.rs"\n')
    output = exact.command(['cargo','run','--offline','--quiet'], project, log)
    records = {}
    for line in output.splitlines():
        name, accepted, stats = line.split(' ',2)
        records[name] = dict(accepted=accepted=='true')
        if accepted=='true':
            values = ast.literal_eval(stats[5:-1])
            records[name].update(depths=[v[0] for v in values], counts=[v[1] for v in values])
    return records, output


def main():
    parser = argparse.ArgumentParser(); parser.add_argument('--record', type=Path, required=True)
    args = parser.parse_args(); all_cases = cases(); log = []
    payload = '\n'.join(finite.dumps({k:v for k,v in c.items() if k not in {'expected','oracle','counts','depths','name'}})
                        for c in all_cases)+'\n'
    with tempfile.TemporaryDirectory(prefix='qleisli-vm25-complete-') as directory:
        project = Path(directory)
        (project/'Main.lean').write_text(LEAN)
        binary = native_harness.build(project, log)
        run = subprocess.run([str(binary)],input=payload,text=True,capture_output=True,timeout=180)
        assert run.returncode==0, run.stderr
        outputs = [json.loads(line) for line in run.stdout.splitlines()]
        assert len(outputs)==len(all_cases)
        rust, rust_output = compare_rust(all_cases, project, log)
        matrices = 0
        for case, actual in zip(all_cases, outputs):
            assert actual['accepted']==case['expected'], (case['name'],actual)
            other = rust.get(case['name'])
            if other: assert other['accepted']==case.get('native_expected', actual['accepted']), (case['name'],actual,other)
            if not actual['accepted']: continue
            if 'counts' in case:
                assert [r['expanded'] for r in actual['result']['receipts']]==case['counts'],case['name']
                assert [r['depth'] for r in actual['result']['receipts']]==case['depths'],case['name']
                if other and other['accepted']:
                    assert other['counts']==case['counts'] and other['depths']==case['depths'],(case['name'],other)
            if case['mode']=='bounded':
                matrix=actual['result']['matrix']; oracle=case['oracle']
                assert [exact.decoded(v) for v in matrix['entries']]==[v for row in oracle for v in row],case['name']
                assert matrix['rows']==len(oracle) and matrix['cols']==len(oracle[0]),case['name']
                matrices+=1
        bindings=dict(native_binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
            native_input_sha256=hashlib.sha256(payload.encode()).hexdigest(),
            native_stdout_sha256=hashlib.sha256(run.stdout.encode()).hexdigest(),
            rust_binary_sha256=hashlib.sha256((project/'target/debug/raw-completion').read_bytes()).hexdigest(),
            rust_stdout_sha256=hashlib.sha256(rust_output.encode()).hexdigest())
    args.record.parent.mkdir(parents=True,exist_ok=True)
    report=dict(status='passed',native_cases=len(all_cases),rust_comparisons=len(rust),independent_matrices=matrices,
        native_boundary_differences=[dict(name=c['name'],component=c['expected'],native=c['native_expected'],reason=c['native_boundary']) for c in all_cases if 'native_expected' in c],
        max_semantic_qubits=3,wide_cases='metadata only; no vectors, matrices or maximum-size corpus',
        native_bindings=bindings,commands=log,
        source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
            list((ROOT/'lean-kernel/QleisliKernel/Raw').glob('*.lean'))+
            list((ROOT/'lean-kernel/QleisliKernel/Semantics').glob('Raw*.lean'))+
            [ROOT/'lean-kernel/QleisliKernel/Semantics/Function.lean',ROOT/'lean-kernel/QleisliKernel/Semantics/Protected.lean',
             ROOT/'lean-kernel/Protocol/Raw.lean',Path(__file__).resolve()]})
    args.record.write_text(json.dumps(report,indent=2)+'\n')
    args.record.with_name('completion-inputs.json').write_text(json.dumps(all_cases,indent=2,default=str)+'\n')
    print(f'{len(all_cases)} native completion cases; {len(rust)} Rust comparisons; {matrices} independent matrices')


if __name__=='__main__': main()
