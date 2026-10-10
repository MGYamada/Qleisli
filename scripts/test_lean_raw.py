#!/usr/bin/env python3
"""VM-25 original pure raw bodies against native Lean, Rust and rational maps.

Expected decisions and oracle annotations stay outside native inputs. The
independent required operator is supplied explicitly; neither executable
receives the other's decision. Production acceptance belongs to native Lean.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import native_harness
import argparse
import copy
import hashlib
import json
from pathlib import Path
import random
import subprocess
import tempfile

import test_lean_exact as exact
import test_lean_finite as finite
import observation_sources
from check_input_corpus import current_project as current_corpus_project

ROOT = Path(__file__).resolve().parents[1]
ZERO, ONE = finite.ZERO, finite.ONE


def port(token, wires):
    return dict(token=token, wires=wires, shape=dict(bits=len(wires)))


def program(bits, operations=(), output=0, effect='unitary'):
    return dict(quantum_inputs=[port(0, list(range(bits)))], classical_inputs=[],
                operations=list(operations), quantum_outputs=[output], classical_outputs=[],
                declared_effect=effect)


def op(tag, **fields):
    return dict(tag=tag, **fields)


def gate_steps(gate, axis, controls=()):
    if gate == 'h':
        return finite.hadamard(axis, controls)
    return finite.mono([axis], [1, 0] if gate == 'x' else [0, 1],
                       [0, 4 if gate == 'z' else 1 if gate == 't' else 0], controls)


def remap(step, axes):
    step = copy.deepcopy(step)
    for c in step['controls']: c['index'] = axes[c['index']]
    action = step['action']
    if action['tag'] == 'hadamard': action['target'] = axes[action['target']]
    else: action['indices'] = [axes[a] for a in action['indices']]
    return step


def raw_oracle(p, dependencies=()):
    """Literal rational operators; compute scopes use full C/W/C matrices.

    This oracle has no Lean/Rust extraction/validity result as an input. It
    projects auxiliary zero only after independently checking every dirty row.
    """
    live = {v['token']: v['wires'][:] for v in p['quantum_inputs']}
    frame = [w for v in p['quantum_inputs'] for w in v['wires']]
    result = finite.identity(2**len(frame))

    def axes(wires): return [frame.index(w) for w in wires]
    def apply(steps):
        nonlocal result
        body = dict(basis=['bit']*len(frame), steps=steps)
        result = exact.oracle_compose(finite.circuit_oracle(body, dependencies), result)
    def mapping(labels, output_bits):
        nonlocal result
        matrix = [[ONE if labels[c] == r else ZERO for c in range(len(labels))]
                  for r in range(2**output_bits)]
        result = exact.oracle_compose(matrix, result)
    def local_unitary(u):
        if u['tag'] == 'gate': return gate_steps(u['gate'], u['target_index'])
        if u['tag'] == 'scalar_phase': return finite.mono([], [0], [4 if u['phase']=='minus_one' else 1])
        cs = [u['control_index']] if u['tag']=='cnot' else [u['control_a_index'],u['control_b_index']]
        return gate_steps('x',u['target_index'],[(a,True) for a in cs])
    for command in p['operations']:
        tag = command['tag']
        if tag == 'pack_unit':
            if command['output'] in live:
                raise ValueError('Unit output already live')
            live[command['output']] = []
        elif tag == 'unpack_unit':
            if live.pop(command['input']):
                raise ValueError('Unit input has physical wires')
        elif tag == 'init0':
            mapping(list(range(2**len(frame))),len(frame)+1)
            frame.append(command['wire']);live[command['output']]=[command['wire']]
        elif tag == 'gate':
            wires=live.pop(command['input']);apply([gate_steps(command['gate'],axes(wires)[0])])
            live[command['output']]=wires
        elif tag in {'cnot','toffoli','quantum_if'}:
            inputs=['control','target'] if tag!='toffoli' else ['control_a','control_b','target']
            wires=[live.pop(command[k]) for k in inputs]
            if tag=='quantum_if':
                for polarity,arm in [(False,command['zero_ops']),(True,command['one_ops'])]:
                    for u in arm:
                        step=remap(local_unitary(u),axes(wires[1]))
                        step['controls'].append(dict(index=axes(wires[0])[0],when_one=polarity));apply([step])
            else: apply([gate_steps('x',axes(wires[-1])[0],[(axes(w)[0],True) for w in wires[:-1]])])
            for key,w in zip(inputs,wires): live[command[key+'_out']]=w
        elif tag=='split':
            w=live.pop(command['input']);k=command['left_bits']
            live[command['left']]=w[:k];live[command['right']]=w[k:]
        elif tag=='join': live[command['output']]=live.pop(command['left'])+live.pop(command['right'])
        elif tag=='lift_basis':
            old=live.pop(command['input']);new=command['output_wires'];before=len(frame)
            frame.extend(new[len(old):]);labels=[]
            for x in range(2**before):
                local=sum(((x>>a)&1)<<j for j,a in enumerate(axes(old)))
                dest=x
                for j,a in enumerate(axes(new)):dest=(dest&~(1<<a))|(((command['table'][local]>>j)&1)<<a)
                labels.append(dest)
            mapping(labels,len(frame));live[command['output']]=new
        elif tag=='apply_unitary':
            w=live.pop(command['input']);apply([remap(s,axes(w)) for s in command['steps']]);live[command['output']]=w
        elif tag in {'certified_compute','compute_use_uncompute'}:
            source=live.pop(command['source']);targets=command.get('targets',[])
            target_wires=[live.pop(t['input']) for t in targets];data=source+sum(target_wires,[])
            n=len(source);d=len(data);a=len(command['ancilla_wires']);total=d+a
            function=command['function']
            compute=finite.mono(list(range(total)),[x^(function[x%(2**n)]<<d) for x in range(2**total)],[0]*(2**total))
            if tag=='certified_compute': use=command['use_steps']
            else:
                def protected(bit): return bit['index']+(d if bit['region']=='ancilla' else 0)
                use=[]
                for u in command['use_ops']:
                    if u['tag']=='protected_gate':use.append(gate_steps(u['gate'],protected(u['bit'])))
                    else:
                        cs=[(protected(c['bit']),c['when_one']) for c in u['controls']]
                        if u['tag']=='controlled_target_gate':use.append(gate_steps(u['gate'],n+u['target_index'],cs))
                        else:use.append(finite.mono([], [0], [4 if u['phase']=='minus_one' else 1],cs))
            physical=finite.circuit_oracle(dict(basis=['bit']*total,steps=[compute]+use+[compute]),dependencies)
            assert all(v==ZERO for row in physical[2**d:] for v in row[:2**d]),'dirty cleanup'
            logical=[row[:2**d] for row in physical[:2**d]]
            if tag=='certified_compute':
                specified=finite.circuit_oracle(dict(basis=['bit']*d,steps=command['logical_steps']),dependencies)
                assert logical==specified,'wrong logical map'
            # Promote the local complete matrix via original data axes.
            body=dict(basis=['bit']*len(frame),steps=[finite.call(axes(data),len(dependencies))])
            result=exact.oracle_compose(finite.circuit_oracle(body,[*dependencies,logical]),result)
            live[command['source_out']]=source
            for t,w in zip(targets,target_wires):live[t['output']]=w
        else: raise ValueError(tag)
    wires=sum((live[t] for t in p['quantum_outputs']),[])
    mapping([sum(((x>>frame.index(w))&1)<<j for j,w in enumerate(wires))
             for x in range(2**len(frame))],len(frame))
    return result


def cases():
    result=[]
    def add(name,p,accepted=True,evidence=(),**kw):
        artifact=dict(format='qleisli.raw-pure-component',version=1,evidence=list(evidence),program=p)
        result.append(dict(name=name,artifact=artifact,expected=accepted,budget=kw.pop('budget',10000000),**kw))
    def closed(operations, outputs=()):
        return dict(quantum_inputs=[],classical_inputs=[],operations=operations,
                    quantum_outputs=list(outputs),classical_outputs=[],declared_effect='unitary')
    add('pack_unit',closed([op('pack_unit',output=0)],[0]))
    unpack=closed([op('unpack_unit',input=0)])
    unpack['quantum_inputs']=[port(0,[])]
    add('unpack_unit',unpack)
    add('unit_roundtrip',closed([op('pack_unit',output=0),op('unpack_unit',input=0)]))
    add('unit_roundtrip_phase',closed([op('pack_unit',output=0),
        op('apply_unitary',input=0,output=1,steps=[finite.mono([], [0],[1])]),
        op('unpack_unit',input=1)]))
    add('unit_with_reference',program(2,[op('pack_unit',output=1),op('unpack_unit',input=1)]))
    add('pack_live_owner',program(0,[op('pack_unit',output=0)]),False)
    add('pack_consumed_owner',closed([op('pack_unit',output=0),op('unpack_unit',input=0),
        op('pack_unit',output=0)],[0]),False)
    add('unpack_nonempty_owner',program(1,[op('unpack_unit',input=0)]),False)
    add('unpack_missing_owner',closed([op('unpack_unit',input=0)]),False)
    add('unpack_twice',closed([op('pack_unit',output=0),op('unpack_unit',input=0),
        op('unpack_unit',input=0)]),False)
    for gate in ['h','x','z','t']:
        add('gate_'+gate,program(1,[op('gate',gate=gate,input=0,output=1)],1))
    add('unit_scalar_phase',program(0,[op('apply_unitary',input=0,output=1,steps=[finite.mono([], [0],[7])])],1))
    for tag,bits in [('cnot',2),('toffoli',3)]:
        split=[op('split',input=0,left=1,right=2,left_bits=1)]
        if bits==3:split.append(op('split',input=2,left=3,right=4,left_bits=1))
        gate=op('cnot',control=1,target=2,control_out=5,target_out=6) if bits==2 else op('toffoli',control_a=1,control_b=3,target=4,control_a_out=5,control_b_out=6,target_out=7)
        joins=[op('join',left=5,right=6,output=8)]
        if bits==3:joins.append(op('join',left=8,right=7,output=9))
        add(tag,program(bits,split+[gate]+joins,8 if bits==2 else 9))
    add('reordered_split_join',program(2,[op('split',input=0,left=1,right=2,left_bits=1),op('join',left=2,right=1,output=3)],3))
    for bits in [0,1,2]:
        add('unit_owner_'+str(bits),program(bits,[op('split',input=0,left=1,right=2,left_bits=0),op('join',left=1,right=2,output=3)],3))
    add('width_preserving_lift',program(2,[op('lift_basis',input=0,output=1,output_wires=[0,1],table=[1,2,3,0])],1))
    add('injective_lift',program(1,[op('lift_basis',input=0,output=1,output_wires=[0,5],table=[3,0])],1,'iso'))
    add('init0',dict(quantum_inputs=[],classical_inputs=[],operations=[op('init0',output=1,wire=0)],quantum_outputs=[1],classical_outputs=[],declared_effect='iso'))
    add('init0_with_reference',program(1,[op('init0',output=1,wire=5),op('join',left=0,right=1,output=2)],2,'iso'))
    for bits,zero,one in [(1,[op('scalar_phase',phase='minus_one')],[op('scalar_phase',phase='eighth_turn')]),
                          (3,[op('cnot',control_index=0,target_index=1)],[op('gate',gate='h',target_index=1)])]:
        p=program(bits,[op('split',input=0,left=1,right=2,left_bits=1),
            op('quantum_if',control=1,target=2,control_out=3,target_out=4,zero_ops=zero,one_ops=one),
            op('join',left=3,right=4,output=5)],5)
        add('quantum_if_'+str(bits),p)
    for predicate in [[0,1],[1,0],[1,1]]:
        phases=[4*x for x in predicate]
        add('certified_'+str(predicate),program(1,[op('certified_compute',source=0,source_out=1,ancilla_wires=[5],function=predicate,
            use_steps=[gate_steps('z',1)],logical_steps=[finite.mono([0],[0,1],phases)])],1))
    add('certified_changes_protected_labels',program(1,[op('certified_compute',source=0,source_out=1,ancilla_wires=[5],function=[0,1],
        use_steps=[gate_steps('x',0),gate_steps('x',1)],logical_steps=[gate_steps('x',0)])],1))
    cf=gate_steps('x',1,[(0,True)])
    add('certified_changes_protected_superposition',program(1,[op('certified_compute',source=0,source_out=1,ancilla_wires=[5],function=[0,1],
        use_steps=[cf,finite.hadamard(0),cf],logical_steps=[finite.hadamard(0)])],1))
    add('protected_phase',program(1,[op('compute_use_uncompute',source=0,source_out=1,targets=[],ancilla_wires=[5],function=[0,1],
        use_ops=[op('controlled_phase',controls=[dict(bit=dict(region='ancilla',index=0),when_one=True)],phase='eighth_turn')])],1))
    add('protected_multi_bit',program(1,[op('compute_use_uncompute',source=0,source_out=1,targets=[],ancilla_wires=[5,6],function=[2,1],
        use_ops=[op('protected_gate',bit=dict(region='ancilla',index=1),gate='z')])],1))
    add('protected_unit_ancilla',program(0,[op('compute_use_uncompute',source=0,source_out=1,targets=[],ancilla_wires=[],function=[0],
        use_ops=[op('controlled_phase',controls=[],phase='minus_one')])],1))
    p=program(2,[op('split',input=0,left=1,right=2,left_bits=1),op('compute_use_uncompute',source=1,source_out=3,
        targets=[dict(input=2,output=4)],ancilla_wires=[5],function=[0,1],use_ops=[op('controlled_target_gate',
        controls=[dict(bit=dict(region='ancilla',index=0),when_one=False)],target_index=0,gate='h')]),op('join',left=3,right=4,output=5)],5)
    add('protected_target_with_negative_control',p)
    evidence=[dict(signature=['bit'],implementation=program(1,[op('gate',gate='h',input=0,output=1)],1),specification=program(1,[op('apply_unitary',input=0,output=1,steps=[finite.hadamard(0)])],1))]
    for adjoint in [False,True]:add('retained_actual_body_'+str(adjoint),program(1,[op('apply_unitary',input=0,output=1,steps=[finite.call([0],0,adjoint)])],1),evidence=evidence)
    scalar=program(0,[op('apply_unitary',input=0,output=1,steps=[finite.mono([], [0],[1])])],1)
    scalar_evidence=[dict(signature=['unit'],implementation=scalar,specification=copy.deepcopy(scalar))]
    for adjoint in [False,True]:
        add('controlled_scalar_receipt_'+str(adjoint),program(1,[op('apply_unitary',input=0,output=1,
            steps=[finite.call([],0,adjoint,[(0,False)])])],1),evidence=scalar_evidence)
    independent=[dict(signature=['unit'],implementation=program(0),specification=program(0)) for _ in range(33)]
    add('independent_receipts_are_not_depth',program(0,[op('apply_unitary',input=0,output=1,steps=[finite.call([],32)])],1),evidence=independent)
    cyclic=copy.deepcopy(scalar_evidence);cyclic[0]['implementation']['operations'][0]['steps']=[finite.call([],0)]
    add('self_referenced_raw_evidence',program(0),False,evidence=cyclic)
    forward=copy.deepcopy(independent[:2]);forward[0]['implementation']=program(0,[op('apply_unitary',input=0,output=1,steps=[finite.call([],1)])],1)
    add('forward_raw_evidence',program(0),False,evidence=forward)
    rng=random.Random(25102026)
    for i in range(48):
        bits=rng.randrange(1,4);steps=[]
        for _ in range(rng.randrange(1,8)):
            axis=rng.randrange(bits);available=[a for a in range(bits) if a!=axis]
            controls=[(a,bool(rng.randrange(2))) for a in available if rng.randrange(2)]
            steps.append(gate_steps(rng.choice(['h','x','z','t']),axis,controls))
        add('random_phase_control_'+str(i),program(bits,[op('apply_unitary',input=0,output=1,steps=steps)],1))
    # Keep reference requirements fixed while mutating well-typed semantics.
    for original in copy.deepcopy(result):
        if original['name'] in {'gate_h','unit_scalar_phase','reordered_split_join','protected_phase','retained_actual_body_False'}:
            changed=copy.deepcopy(original);changed['name']='request_fault_'+changed['name'];changed['expected']=False
            changed['required']=finite.description(raw_oracle(original['artifact']['program'],[raw_oracle(e['implementation']) for e in original['artifact']['evidence']]))
            p=changed['artifact']['program']
            if original['name']=='gate_h':p['operations'][0]['gate']='x'
            elif original['name']=='reordered_split_join':p['operations'][1].update(left=1,right=2)
            elif original['name']=='protected_phase':p['operations'][0]['use_ops'][0]['phase']='minus_one'
            elif original['name']=='retained_actual_body_False':changed['artifact']['evidence'][0]['implementation']['operations'][0]['gate']='x'
            else:p['operations'][0]['steps'][0]['action']['phases']=[0]
            result.append(changed)
    base=program(1,[op('gate',gate='h',input=0,output=1)],1)
    faults={
        'omitted_owner':lambda p:p.update(quantum_outputs=[]),
        'duplicate_output':lambda p:p.update(quantum_outputs=[1,1]),
        'dead_output':lambda p:p.update(quantum_outputs=[0]),
        'revived_token':lambda p:p['operations'][0].update(output=0),
        'missing_input':lambda p:p['operations'][0].update(input=9),
        'input_shape':lambda p:p['quantum_inputs'][0]['shape'].update(bits=0),
        'input_wire_alias':lambda p:p['quantum_inputs'].append(port(9,[0])),
        'input_token_alias':lambda p:p['quantum_inputs'].append(port(0,[9])),
        'narrow_gate':lambda p:p['quantum_inputs'][0].update(wires=[],shape=dict(bits=0)),
        'classical_interface':lambda p:p.update(classical_inputs=[5]),
        'observing_constructor':lambda p:p['operations'].append(op('discard',input=1)),
    }
    for name,mutate in faults.items():p=copy.deepcopy(base);mutate(p);add(name,p,False)
    for name,change in [('dirty_auxiliary',dict(use_steps=[gate_steps('x',1)])),('wrong_logical',dict(logical_steps=[])),
                        ('changed_predicate',dict(function=[1,0])),('reused_auxiliary',dict(ancilla_wires=[0]))]:
        p=copy.deepcopy(next(c['artifact']['program'] for c in result if c['name']=='certified_[0, 1]'));p['operations'][0].update(change);add(name,p,False)
    for name,mutate in [
        ('protected_nondiagonal',lambda p:p['operations'][0]['use_ops'][0].update(gate='h')),
        ('lift_duplicate_label',lambda p:p['operations'][0].update(table=[1,1])),
        ('lift_wire_order',lambda p:p['operations'][0].update(output_wires=[5,0])),
        ('lift_effect',lambda p:p.update(declared_effect='unitary')),
        ('unit_owner_omitted',lambda p:p.update(operations=p['operations'][:1],quantum_outputs=[2])),
        ('overlapping_controls',lambda p:p['operations'][0].update(steps=[finite.hadamard(0,[(0,True)])])),
        ('missing_dependency',lambda p:p['operations'][0].update(steps=[finite.call([0],8)])),
    ]:
        source='protected_multi_bit' if name.startswith('protected') else 'injective_lift' if name.startswith('lift') else 'unit_owner_0' if name.startswith('unit_owner') else 'gate_h'
        p=copy.deepcopy(next(c['artifact']['program'] for c in result if c['name']==source))
        if name in {'overlapping_controls','missing_dependency'}:p['operations'][0]=op('apply_unitary',input=0,output=1,steps=[])
        mutate(p);add(name,p,False)
    for case in result:
        if case['expected']:
            deps=[]
            for e in case['artifact']['evidence']:
                actual=raw_oracle(e['implementation'],deps);assert actual==raw_oracle(e['specification'],deps);deps.append(actual)
            case['oracle']=raw_oracle(case['artifact']['program'],deps)
            case['required']=finite.description(case['oracle'])
        else:case.setdefault('required',finite.description(finite.identity(1)))
    wrong_phase=copy.deepcopy(next(c for c in result if c['name']=='unit_roundtrip_phase'))
    wrong_phase.update(name='request_fault_unit_phase',expected=False,
                       required=finite.description(finite.identity(1)))
    result.append(wrong_phase)
    for budget in [0,1,23]:
        case=copy.deepcopy(next(c for c in result if c['name']=='gate_h'))
        case.update(name='exhausted_work_'+str(budget),expected=False,budget=budget);result.append(case)
    for name,mutate in [
        ('producer_accepted_flag',lambda a:a.update(accepted=True)),
        ('producer_matrix_cache',lambda a:a['evidence'][0].update(meaning=finite.description(finite.identity(2)))),
        ('unknown_raw_field',lambda a:a['program'].update(checked=True)),
        ('unknown_constructor_field',lambda a:a['program']['operations'][0].update(checked=True)),
    ]:
        case=copy.deepcopy(next(c for c in result if c['name']=='retained_actual_body_False'))
        case.update(name=name,expected=False);mutate(case['artifact']);result.append(case)
    return result


def pure_source_prefix(artifact):
    """Retain the selected root and complete circuit dependencies before readout.

    The common lossless projection validates and topologically renames calls.
    Pure transport has no identity fields; the original QIRF bytes retain those
    identities and are separately checked by the production native boundary.
    """
    component = observation_sources.component(artifact)
    p = component['program']
    ops = p['operations']
    first = next((j for j, operation in enumerate(ops)
                  if operation['tag'] == 'measure_z'), None)
    if first is None or not all(operation['tag'] == 'measure_z' for operation in ops[first:]):
        raise ValueError('source prefix requires terminal destructive measurements')
    p.update(operations=ops[:first], quantum_outputs=[operation['input'] for operation in ops[first:]],
             classical_outputs=[], declared_effect='iso')
    evidence = [{key: entry[key] for key in ('signature', 'implementation', 'specification')}
                for entry in component['dependencies']]
    return dict(format='qleisli.raw-pure-component', version=1, evidence=evidence, program=p)


def pure_component_oracle(artifact):
    """Independently evaluate every retained implementation and specification."""
    dependencies = []
    for entry in artifact['evidence']:
        actual = raw_oracle(entry['implementation'], dependencies)
        required = raw_oracle(entry['specification'], dependencies)
        assert actual == required, 'source dependency implementation/specification disagreement'
        dependencies.append(actual)
    return raw_oracle(artifact['program'], dependencies)


def source_cases(log, record=None, compiler=None):
    """Curated bridge from actual Rust source output to the pure prefix.

    Complete observing roots stay outside VM-25. This untrusted adapter ends
    immediately before terminal measurement and lists those residual owners;
    Lean rechecks the resulting actual prefix. No source-preservation claim.
    """
    compiler=ROOT/'target/debug/qleisli' if compiler is None else Path(compiler)
    if not compiler.is_file():
        if compiler != ROOT/'target/debug/qleisli':raise FileNotFoundError(compiler)
        exact.command(['cargo','build','--offline','--bin','qleisli'],ROOT,log)
    paths=['quantum_katas/controlled_z2','quantum_katas/toffoli3','qualtran/less_equal1',
           'qualtran/greater_than1','pennylane_demos/rotation_mixed_sign','pennylane_demos/qaoa_mixer2']
    result=[]
    with tempfile.TemporaryDirectory(prefix='qleisli-raw-source-') as directory:
        for i,path in enumerate(paths):
            project=current_corpus_project({'project':path})
            output=Path(directory)/f'{i}.qirf.json'
            source_paths=sorted(project.rglob('*.qli'))+sorted((ROOT/'stdlib/src').rglob('*.qli'))
            source_paths += [ROOT/'corpus/Qargo.toml',ROOT/'stdlib/Qargo.toml']
            if (project/'Qargo.toml').is_file():source_paths.append(project/'Qargo.toml')
            source_hashes={str(s.relative_to(ROOT)):hashlib.sha256(s.read_bytes()).hexdigest() for s in source_paths}
            exact.command([str(compiler),'emit-ir',str(project),'--output='+str(output),'--format=json'],ROOT,log)
            assert source_hashes=={str(s.relative_to(ROOT)):hashlib.sha256(s.read_bytes()).hexdigest() for s in source_paths}
            original=output.read_bytes();artifact=json.loads(original)
            if record:
                saved=record.parent/'source-ir'/f'{i}.qirf.json'
                saved.parent.mkdir(parents=True,exist_ok=True);saved.write_bytes(original)
            component=pure_source_prefix(artifact)
            assert sum(port['shape']['bits'] for port in component['program']['quantum_inputs'])<=3
            meaning=pure_component_oracle(component)
            result.append(dict(name='source_prefix_'+path.replace('/','_'),
                artifact=component,original_qirf=original.decode('utf-8'),
                expected=True,budget=10000000,oracle=meaning,required=finite.description(meaning),
                provenance=dict(source_root=str(project.relative_to(ROOT)),historical_source_root='corpus/'+path,
                    qirf_sha256=hashlib.sha256(original).hexdigest(),
                    compiler_sha256=hashlib.sha256(compiler.read_bytes()).hexdigest(),
                    sources=source_hashes,
                    embedded_sources={s['path']:hashlib.sha256(s['text'].encode()).hexdigest() for s in artifact['sources']},
                    adapter='original straight-line prefix before terminal destructive measurement; '
                            'all circuit dependencies retained with topological index renaming; '
                            'complete original QIRF separately checked')))
    return result


LEAN = finite.LEAN[:finite.LEAN.index('def execute')] + '''
def referenceChecks (value : Json) : Nat × Bool :=
  match value.getObjVal? "artifact" >>= QleisliKernel.Protocol.Raw.artifact with
  | .error _ => (0,true)
  | .ok artifact =>
    let signatures := artifact.evidence.map (·.signature)
    let programs := (artifact.evidence.flatMap fun evidence =>
      [evidence.implementation,evidence.specification]) ++ [artifact.program]
    programs.foldl (fun (count,matched) program =>
      match QleisliKernel.Raw.prepare signatures program with
      | .error _ => (count,matched)
      | .ok prepared => (count+1,matched &&
          QleisliKernel.Semantics.RawTrace.run program == some prepared.reference)) (0,true)
def execute (value : Json) : WorkM Matrix := do
  let artifact ← adapt (QleisliKernel.Protocol.Raw.artifact (← adapt (value.getObjVal? "artifact")))
  let required ← QleisliKernel.Protocol.FiniteCodec.readMatrixValue (← adapt (value.getObjVal? "required"))
  QleisliKernel.Raw.inspect artifact.evidence artifact.program required
''' + finite.LEAN[finite.LEAN.index('def main'):].replace(
    '    output.putStrLn record.compress',
    '''    let (count,matched) := match QleisliKernel.Protocol.FiniteCodec.parse line with
      | .error _ => (0,true)
      | .ok value => referenceChecks value
    let record := match record.getObj? with
      | .error _ => record
      | .ok fields => Json.mkObj (fields.toList ++
          [("reference_programs",toJson count),("reference_match",toJson matched)])
    output.putStrLn record.compress''')


def rust_program(p, receipts='receipts'):
    def vec(xs):return 'vec!['+','.join(map(str,xs))+']'
    def token(x):return f'TokenId({x})'
    def wire(x):return f'WireId({x})'
    def rust_step(s):
        a=s['action'];cs=','.join(f'BitControl{{index:{c["index"]},when_one:{str(c["when_one"]).lower()}}}' for c in s['controls'])
        if a['tag']=='hadamard':action=f'CircuitAction::Hadamard{{target:{a["target"]}}}'
        elif a['tag']=='monomial':action=f'CircuitAction::Monomial{{indices:{vec(a["indices"])},permutation:{vec(a["permutation"])},phases:{vec(a["phases"])}}}'
        else:action=f'CircuitAction::Contract{{indices:{vec(a["indices"])},evidence:{receipts}[{a["evidence"]}].clone(),adjoint:{str(a["adjoint"]).lower()}}}'
        return f'CircuitStep{{controls:vec![{cs}],action:{action}}}'
    def rs(steps):return 'vec!['+','.join(rust_step(s) for s in steps)+']'
    def unit(u):
        if u['tag']=='scalar_phase':return 'UnitaryStep::ScalarPhase(ScalarPhase::'+('MinusOne' if u['phase']=='minus_one' else 'EighthTurn')+')'
        tag={'gate':'Gate','cnot':'Cnot','toffoli':'Toffoli'}[u['tag']]
        fields=','.join(k+':'+('SingleGate::'+v.upper() if k=='gate' else str(v)) for k,v in u.items() if k!='tag')
        return f'UnitaryStep::{tag}{{{fields}}}'
    def use(u):
        def pb(b):return f'ProtectedBit{{region:ProtectedRegion::{b["region"].capitalize()},index:{b["index"]}}}'
        cs=lambda: 'vec!['+','.join(f'Control{{bit:{pb(c["bit"])},when_one:{str(c["when_one"]).lower()}}}' for c in u['controls'])+']'
        if u['tag']=='protected_gate':return f'ProtectedUse::ProtectedGate{{bit:{pb(u["bit"])},gate:SingleGate::{u["gate"].upper()}}}'
        if u['tag']=='controlled_target_gate':return f'ProtectedUse::ControlledTargetGate{{controls:{cs()},target_index:{u["target_index"]},gate:SingleGate::{u["gate"].upper()}}}'
        return f'ProtectedUse::ControlledPhase{{controls:{cs()},phase:ScalarPhase::'+('MinusOne' if u['phase']=='minus_one' else 'EighthTurn')+'}'
    tags={'pack_unit':'PackUnit','unpack_unit':'UnpackUnit','init0':'Init0','gate':'Gate','cnot':'Cnot','toffoli':'Toffoli','quantum_if':'QuantumIf','split':'Split','join':'Join','lift_basis':'LiftBasis','apply_unitary':'ApplyUnitary','certified_compute':'CertifiedCompute','compute_use_uncompute':'ComputeUseUncompute','discard':'Discard'}
    commands=[]
    for o in p['operations']:
        fields=[]
        for k,v in o.items():
            if k=='tag':continue
            if k=='gate':value='SingleGate::'+v.upper()
            elif k in {'steps','use_steps','logical_steps'}:value=rs(v)
            elif k in {'zero_ops','one_ops'}:value='vec!['+','.join(unit(u) for u in v)+']'
            elif k=='use_ops':value='vec!['+','.join(use(u) for u in v)+']'
            elif k=='targets':value='vec!['+','.join(f'TargetTransition{{input:{token(t["input"])},output:{token(t["output"])}}}' for t in v)+']'
            elif k in {'ancilla_wires','output_wires'}:value='vec!['+','.join(wire(w) for w in v)+']'
            elif k in {'function','table'}:value=vec(v)
            elif k=='left_bits':value=str(v)
            elif k=='wire':value=wire(v)
            else:value=token(v)
            fields.append(k+':'+value)
        commands.append('RawOp::'+tags[o['tag']]+'{'+','.join(fields)+'}')
    inputs=','.join(f'QuantumPort{{token:{token(v["token"])},wires:vec![{",".join(wire(w) for w in v["wires"])}],shape:BasisShape{{bits:{v["shape"]["bits"]}}}}}' for v in p['quantum_inputs'])
    return f'RawProgram{{quantum_inputs:vec![{inputs}],classical_inputs:vec![{",".join("ClassicalId("+str(i)+")" for i in p["classical_inputs"])}],operations:vec![{",".join(commands)}],quantum_outputs:vec![{",".join(token(t) for t in p["quantum_outputs"])}],classical_outputs:vec![],declared_effect:Effect::{p["declared_effect"].capitalize()}}}'


def native(all_cases, log):
    with tempfile.TemporaryDirectory(prefix='qleisli-raw-native-') as directory:
        project=Path(directory)
        (project/'Main.lean').write_text(LEAN)
        binary = native_harness.build(project, log)
        payload='\n'.join(finite.dumps({k:v for k,v in c.items() if k in {'artifact','required','budget'}}) for c in all_cases)+'\n'
        run=subprocess.run([str(binary)],input=payload,text=True,capture_output=True,timeout=180)
        assert run.returncode==0,run.stderr
        bindings=dict(lean_binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                      lean_input_sha256=hashlib.sha256(payload.encode()).hexdigest(),
                      lean_stdout_sha256=hashlib.sha256(run.stdout.encode()).hexdigest(),
                      lean_stderr_sha256=hashlib.sha256(run.stderr.encode()).hexdigest(),lean_exit=run.returncode)
        lean=[json.loads(line) for line in run.stdout.splitlines()]
        actions=[]
        for c in all_cases:
            if c['name'].startswith(('request_fault','exhausted_work','producer_','unknown_')) or c['name'] in {'classical_interface','observing_constructor','self_referenced_raw_evidence','forward_raw_evidence'}:continue
            a=c['artifact'];p=a['program'];statements=[]
            if 'original_qirf' in c:
                filename=f'source-{len(actions)}.qirf'
                (project/filename).write_bytes(c['original_qirf'].encode('utf-8'))
                statements.append('qleisli::interchange::native::Kernel::selected().expect("explicit native checker")'
                    '.check(include_bytes!('+json.dumps(filename)+'),None).ok()?;')
            if c['name']=='missing_dependency':continue
            for e in a['evidence']:
                statements.append('receipts.push(std::sync::Arc::new(qleisli::contract::FunctionEvidence::check('+finite.rust_basis(e['signature'])+','+rust_program(e['implementation'])+','+rust_program(e['specification'])+',identity(),&mut b).ok()?));')
            statements.append('let raw='+rust_program(p)+';let verified=qleisli::interchange::native::Kernel::selected().expect("explicit native checker").accept_raw(raw.clone()).ok()?;')
            unary=len(p['quantum_inputs'])==1 and len(p['quantum_outputs'])==1 and p['declared_effect']=='unitary'
            if unary:
                bits=p['quantum_inputs'][0]['shape']['bits']
                basis=['unit'] if bits==0 else ['pair','bit']*(bits-1)+['bit']
                statements.append('let m=qleisli::contract::FunctionEvidence::check('+finite.rust_basis(basis)+',raw.clone(),raw,identity(),&mut b).ok()?;Some(Some(m.meaning().clone()))')
            else:statements.append('let _=verified;Some(None)')
            actions.append('let result=(||{let mut b=Budget::new(10000000);let mut receipts:Vec<std::sync::Arc<qleisli::contract::FunctionEvidence>>=vec![];'+''.join(statements)+'})();show('+json.dumps(c['name'])+',result);')
        rust='''#![allow(unused_variables,unused_mut)]
use qleisli::ir::*;
use qleisli::contract::{BasisType,FunctionIdentity};
use qleisli::contract::exact::{Budget,Matrix};
fn identity()->FunctionIdentity{FunctionIdentity{implementation:"actual".into(),specification:"reference".into(),sources:vec![]}}
fn show(name:&str,result:Option<Option<Matrix>>){match result{None=>println!("{{\\"name\\":\\"{}\\",\\"accepted\\":false}}",name),Some(matrix)=>{
let value=matrix.map(|x|String::from_utf8(qleisli::interchange::finite_matrix::encode(&x).unwrap()).unwrap()).unwrap_or("null".into());
println!("{{\\"name\\":\\"{}\\",\\"accepted\\":true,\\"matrix\\":{}}}",name,value)}}}
fn main(){
'''+ '\n'.join(actions)+'\n}\n'
        (project/'Cargo.toml').write_text('[package]\nname="qleisli_raw_test"\nversion="0.0.0"\nedition="2024"\n[dependencies]\nqleisli={path='+json.dumps(str(ROOT))+'}\n[[bin]]\nname="raw-test"\npath="main.rs"\n')
        (project/'main.rs').write_text(rust)
        stdout=exact.command(['cargo','run','--offline','--quiet'],project,log)
        bindings.update(rust_binary_sha256=hashlib.sha256((project/'target/debug/raw-test').read_bytes()).hexdigest(),
                        rust_stdout_sha256=hashlib.sha256(stdout.encode()).hexdigest())
        records={};decoder=json.JSONDecoder()
        while stdout.strip():
            stdout=stdout.lstrip();record,end=decoder.raw_decode(stdout)
            records[record['name']]=record;stdout=stdout[end:]
        return lean,records,bindings


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--record',type=Path)
    parser.add_argument('--compiler',type=Path,default=ROOT/'target/debug/qleisli');args=parser.parse_args()
    log=[]
    for argv,cwd in [(['lake','env','lean','--version'],ROOT/'lean-kernel'),(['rustc','-vV'],ROOT)]:
        exact.command(argv,cwd,log)
    all_cases=cases()+source_cases(log,args.record,args.compiler.resolve());lean,rust,bindings=native(all_cases,log)
    assert len(lean)==len(all_cases)
    matrices=0
    for case,result in zip(all_cases,lean):
        assert result['reference_match'],(case['name'],result)
        assert result['accepted']==case['expected'],(case['name'],result)
        other=rust.get(case['name'])
        if other:assert result['accepted']==other['accepted'],(case['name'],result,other)
        if not result['accepted']:continue
        m=result['matrix'];expected=case['oracle']
        assert m['rows']==len(expected) and m['cols']==len(expected[0]),case['name']
        assert [exact.decoded(v) for v in m['entries']]==[v for row in expected for v in row],case['name']
        assert exact.oracle_compose(exact.oracle_adjoint(expected),expected)==finite.identity(len(expected[0])),case['name']
        if other and other['matrix']:
            values=[[[v['numerator'],v['denominator_bits']] for v in s] for s in other['matrix']['entries']]
            assert values==m['entries'],case['name']
        matrices+=1
    pure_tags=sorted({o['tag'] for c in all_cases if c['expected']
                      for o in c['artifact']['program']['operations']})
    report=dict(native_cases=len(all_cases),rust_comparisons=len(rust),independent_matrices=matrices,
        independent_raw_trace_programs=sum(r['reference_programs'] for r in lean),
        pure_constructors=len(pure_tags),pure_constructor_tags=pure_tags,max_semantic_qubits=3,rust_source_prefixes=6,original_qirf_checks=6,
        commands=log,native_bindings=bindings,
        remaining=['VM-26 classical control/observation',
                   'VM-27 hierarchy closure','native packaging and byte/decoder refinement'],
        source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [
            ROOT/'lean-kernel/QleisliKernel/Semantics/Raw.lean',ROOT/'lean-kernel/QleisliKernel/Raw/Structure.lean',
            ROOT/'lean-kernel/QleisliKernel/Raw/Finite.lean',ROOT/'lean-kernel/Protocol/Raw.lean',ROOT/'lean/Qleisli/Raw.lean',
            Path(observation_sources.__file__),Path(finite.__file__),Path(exact.__file__),
            ROOT/'scripts/check_input_corpus.py',Path(__file__).resolve()]})
    report['source_sha256'].update({str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [
        ROOT/'lean-kernel/QleisliKernel/Semantics/RawTrace.lean',ROOT/'lean-kernel/QleisliKernel/Raw/Trace.lean']})
    if args.record:
        args.record.parent.mkdir(parents=True,exist_ok=True);args.record.write_text(json.dumps(report,indent=2)+'\n')
        args.record.with_name('native-inputs.json').write_text(json.dumps(all_cases,indent=2,default=str)+'\n')
    print(f'{len(all_cases)} native raw cases; {len(rust)} Rust comparisons; {matrices} independent rational matrices; '
          f"{report['independent_raw_trace_programs']} independent raw trace comparisons")


if __name__=='__main__':main()
