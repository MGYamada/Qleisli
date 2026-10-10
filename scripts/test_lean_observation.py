#!/usr/bin/env python3
"""VM-26 actual original bodies: native Lean, Rust and exact Kraus oracles.

No executable receives another checker decision or an oracle matrix. Quantum
states are compared as complete unnormalized operators, including hidden reset/
discard histories and surviving reference correlations. Semantic cases use at
most three qubits. Metadata capacities are separate from corpus execution.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import native_harness
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

import test_lean_exact as exact
import test_lean_finite as finite
import test_lean_raw as raw
import observation_sources
from check_input_corpus import current_project as current_corpus_project
from check_verification_inventory import variants

ROOT = Path(__file__).resolve().parents[1]
ZERO, ONE = finite.ZERO, finite.ONE
OBS = {'measure_z', 'reset', 'discard', 'classical_const', 'classical_not',
       'classical_xor', 'classical_and', 'classical_branch'}


def p(inputs=(), classical=(), operations=(), outputs=(), results=(), effect='observe'):
    return dict(quantum_inputs=list(inputs), classical_inputs=list(classical),
                operations=list(operations), quantum_outputs=list(outputs),
                classical_outputs=list(results), declared_effect=effect)


def qphi(left, right, output, wires):
    return dict(then_token=left, else_token=right, output=output, output_wires=wires)


def cphi(left, right, output):
    return dict(then_id=left, else_id=right, output=output)


def branch(condition, left=(), right=(), quantum=(), classical=()):
    return raw.op('classical_branch', condition=condition, then_ops=list(left),
                  else_ops=list(right), quantum_phis=list(quantum), classical_phis=list(classical))


def route(frame, ordered):
    assert sorted(frame) == sorted(ordered)
    labels = [sum(((x >> frame.index(w)) & 1) << j for j, w in enumerate(ordered))
              for x in range(2**len(frame))]
    return [[ONE if labels[c] == r else ZERO for c in range(len(labels))]
            for r in range(len(labels))]


def pure_live(live, op):
    live = copy.deepcopy(live)
    tag = op['tag']
    if tag == 'pack_unit':
        if op['output'] in live:
            raise ValueError('Unit output already live')
        live[op['output']] = []
    elif tag == 'unpack_unit':
        if live.pop(op['input']):
            raise ValueError('Unit input has physical wires')
    elif tag == 'init0':
        live[op['output']] = [op['wire']]
    elif tag in {'gate', 'apply_unitary'}:
        live[op['output']] = live.pop(op['input'])
    elif tag in {'cnot', 'toffoli', 'quantum_if'}:
        keys = ['control_a', 'control_b', 'target'] if tag == 'toffoli' else ['control', 'target']
        ports = [live.pop(op[k]) for k in keys]
        for key, wires in zip(keys, ports): live[op[key+'_out']] = wires
    elif tag == 'split':
        wires = live.pop(op['input'])
        live[op['left']], live[op['right']] = wires[:op['left_bits']], wires[op['left_bits']:]
    elif tag == 'join':
        live[op['output']] = live.pop(op['left']) + live.pop(op['right'])
    elif tag == 'lift_basis':
        live.pop(op['input']); live[op['output']] = op['output_wires']
    elif tag in {'certified_compute', 'compute_use_uncompute'}:
        source = live.pop(op['source'])
        targets = [(t, live.pop(t['input'])) for t in op.get('targets', [])]
        live[op['source_out']] = source
        for target, wires in targets: live[target['output']] = wires
    else:
        raise ValueError(tag)
    return live


def oracle(program, classical=(), dependencies=()):
    """Literal rational Kraus calculus over full input/residual coordinates.

    Pure actions are built from gate matrices and physical C/W/C circuits.
    Erasure takes every basis bra; reset then appends a zero ket. There is no
    measurement sampling, normalization, product-state assumption or float.
    """
    live = {v['token']: v['wires'][:] for v in program['quantum_inputs']}
    frame = sum(live.values(), [])
    initial = dict(live=live, frame=frame, values=dict(zip(program['classical_inputs'], classical)),
                   hidden=[], operator=finite.identity(2**len(frame)))

    def walk(operations, h):
        histories = [h]
        for op in operations:
            following = []
            for h in histories:
                tag = op['tag']
                if tag not in OBS:
                    live = pure_live(h['live'], op)
                    inputs = [raw.port(t, w) for t, w in h['live'].items()]
                    order = sum(h['live'].values(), [])
                    operator = raw.raw_oracle(p(inputs, operations=[op], outputs=list(live),
                                                effect='iso'), dependencies)
                    operator = exact.oracle_compose(operator, route(h['frame'], order))
                    following.append(dict(h, live=live, frame=sum(live.values(), []),
                                          operator=exact.oracle_compose(operator, h['operator'])))
                elif tag in {'measure_z', 'reset', 'discard'}:
                    live = copy.deepcopy(h['live'])
                    erased = live.pop(op['input'])
                    kept = [w for w in h['frame'] if w not in erased]
                    for outcome in range(2**len(erased)):
                        def selected(col):
                            label = sum(((col >> h['frame'].index(w)) & 1) << j for j, w in enumerate(erased))
                            residual = sum(((col >> h['frame'].index(w)) & 1) << j for j, w in enumerate(kept))
                            return label, residual
                        rows = 2**len(kept)
                        matrix = [[ONE if selected(col) == (outcome, row) else ZERO
                                   for col in range(2**len(h['frame']))] for row in range(rows)]
                        values = dict(h['values'])
                        out_live, out_frame = copy.deepcopy(live), kept[:]
                        if tag == 'measure_z': values[op['output']] = bool(outcome)
                        if tag == 'reset':
                            out_live[op['output']] = [op['fresh_wire']]
                            out_frame.append(op['fresh_wire'])
                            matrix += [[ZERO for _ in row] for row in matrix]
                        following.append(dict(live=out_live, frame=out_frame, values=values,
                            hidden=h['hidden']+[outcome], operator=exact.oracle_compose(matrix, h['operator'])))
                elif tag == 'classical_branch':
                    choice = h['values'][op['condition']]
                    for arm in walk(op['then_ops'] if choice else op['else_ops'], h):
                        ordered = sum((arm['live'][phi['then_token'] if choice else phi['else_token']]
                                       for phi in op['quantum_phis']), [])
                        values = dict(arm['values'])
                        phis = [(phi['output'], arm['values'][phi['then_id'] if choice else phi['else_id']])
                                for phi in op['classical_phis']]
                        values.update(phis)
                        live = {phi['output']: phi['output_wires'][:] for phi in op['quantum_phis']}
                        following.append(dict(arm, live=live, frame=sum(live.values(), []), values=values,
                            operator=exact.oracle_compose(route(arm['frame'], ordered), arm['operator'])))
                else:
                    values = dict(h['values'])
                    if tag == 'classical_const': value = op['value']
                    elif tag == 'classical_not': value = not values[op['input']]
                    elif tag == 'classical_xor': value = values[op['left']] != values[op['right']]
                    else: value = values[op['left']] and values[op['right']]
                    values[op['output']] = value
                    following.append(dict(h, values=values))
            histories = following
        return histories

    results = []
    for h in walk(program['operations'], initial):
        ordered = sum((h['live'][t] for t in program['quantum_outputs']), [])
        operator = exact.oracle_compose(route(h['frame'], ordered), h['operator'])
        results.append(dict(hidden=h['hidden'], results=[h['values'][i] for i in program['classical_outputs']],
                            operator=operator))
    return results


def cases():
    records = []
    def add(name, program, accepted=True, classical=(), mode='instrument', **kw):
        records.append(dict(name=name, expected=accepted, mode=mode, classical=list(classical),
            budget=kw.pop('budget', 10000000),
            artifact=dict(format='qleisli.raw-observing-component', version=1, dependencies=[],
                          bindings=[], program=copy.deepcopy(program)), **kw))
    # Every accepted dependency-free pure case also crosses the observing boundary.
    for c in raw.cases():
        if c['expected'] and 'oracle' in c and not c['artifact']['evidence']:
            add('pure_'+c['name'], c['artifact']['program'])
    for effect in ['unitary', 'iso', 'observe']:
        add('measure_effect_'+effect, p([raw.port(0,[0])],
            operations=[raw.op('measure_z', input=0, output=0)], results=[0], effect=effect), effect=='observe')
        add('reset_effect_'+effect, p([raw.port(0,[0])],
            operations=[raw.op('reset', input=0, output=1, fresh_wire=1)], outputs=[1], effect=effect), effect=='observe')
        add('discard_effect_'+effect, p([raw.port(0,[0])],
            operations=[raw.op('discard', input=0)], effect=effect), effect=='observe')
    add('unit_after_measurement', p([raw.port(0,[0]),raw.port(1,[1])],
        operations=[raw.op('measure_z',input=0,output=0),raw.op('pack_unit',output=2),
                    raw.op('unpack_unit',input=2)], outputs=[1],results=[0]))
    add('unit_after_discard', p([raw.port(0,[0]),raw.port(1,[1])],
        operations=[raw.op('discard',input=0),raw.op('pack_unit',output=2),
                    raw.op('unpack_unit',input=2)], outputs=[1]))
    add('pack_measured_owner', p([raw.port(0,[0])],
        operations=[raw.op('measure_z',input=0,output=0),raw.op('pack_unit',output=0)],
        outputs=[0],results=[0]),False)
    for choice in [False,True]:
        add('unit_in_branch_'+str(choice), p(classical=[0],
            operations=[branch(0,[raw.op('pack_unit',output=1)],
                [raw.op('pack_unit',output=2)],quantum=[qphi(1,2,3,[])]),
                raw.op('unpack_unit',input=3)],effect='unitary'),classical=[choice])
    add('discard_unit', p([raw.port(0,[])], operations=[raw.op('discard',input=0)]))
    add('discard_two_bits', p([raw.port(0,[4,2])], operations=[raw.op('discard',input=0)]))
    add('measure_unit_rejected', p([raw.port(0,[])], operations=[raw.op('measure_z',input=0,output=0)],results=[0]),False)
    add('reset_old_wire', p([raw.port(0,[0])], operations=[raw.op('reset',input=0,output=1,fresh_wire=0)],outputs=[1]),False)
    add('reset_dead_token', p([raw.port(0,[0])], operations=[raw.op('reset',input=0,output=0,fresh_wire=1)],outputs=[0]),False)
    add('measured_owner_reused', p([raw.port(0,[0])], operations=[raw.op('measure_z',input=0,output=0),
        raw.op('gate',gate='x',input=0,output=1)],outputs=[1],results=[0]),False)
    for bits in [0,1]:
        add('implicit_drop_'+str(bits), p([raw.port(0,list(range(bits)))]),False)
    classical_ops = [raw.op('classical_const',value=True,output=2),
        raw.op('classical_not',input=0,output=3),raw.op('classical_xor',left=0,right=1,output=4),
        raw.op('classical_and',left=0,right=1,output=5)]
    for a in [False,True]:
        for b in [False,True]:
            add('classical_truth_'+str(int(a))+str(int(b)),
                p(classical=[0,1],operations=classical_ops,results=[2,3,4,5,0,0],effect='unitary'),classical=[a,b])
    for tag in ['classical_not','classical_xor','classical_and']:
        fields=dict(input=99,output=1) if tag=='classical_not' else dict(left=0,right=99,output=1)
        add(tag+'_undefined',p(classical=[0],operations=[raw.op(tag,**fields)],results=[1]),False,classical=[False])
    add('classical_input_duplicate',p(classical=[0,0],results=[0]),False,classical=[False,True])
    add('classical_redefinition',p(classical=[0],operations=[raw.op('classical_const',value=False,output=0)]),False,classical=[True])
    add('classical_missing_values',p(classical=[0],results=[0]),False)
    for choice in [False,True]:
        b = branch(0,[raw.op('gate',gate='x',input=0,output=1)],[],
                   [qphi(1,0,2,[1])])
        add('pure_branch_'+str(choice),p([raw.port(0,[0])],[0],[b],[2],effect='unitary'),classical=[choice])
        add('unit_frame_branch_'+str(choice),p([raw.port(0,[]),raw.port(1,[])],[0],
            [branch(0,quantum=[qphi(1,1,2,[]),qphi(0,0,3,[])])],[2,3],effect='unitary'),classical=[choice])
    base = p([raw.port(0,[0]),raw.port(1,[1])],[0],[branch(0,
        [raw.op('gate',gate='x',input=0,output=2)],
        [raw.op('gate',gate='z',input=0,output=3)],
        [qphi(2,3,4,[2]),qphi(1,1,5,[3])])],[4,5],effect='unitary')
    for choice in [False,True]: add('whole_caller_frame_'+str(choice),base,classical=[choice])
    for name,mutate in [
        ('missing_frame',lambda b:b['operations'][0]['quantum_phis'].pop()),
        ('same_token_across_arms',lambda b:b['operations'][0]['else_ops'][0].update(output=2)),
        ('revive_dead_owner',lambda b:b['operations'][0]['quantum_phis'][0].update(output=0)),
        ('reuse_old_wire',lambda b:b['operations'][0]['quantum_phis'][0].update(output_wires=[0])),
        ('duplicate_phi_operand',lambda b:b['operations'][0]['quantum_phis'][1].update(then_token=2)),
        ('duplicate_phi_output',lambda b:b['operations'][0]['quantum_phis'][1].update(output=4)),
        ('phi_shape',lambda b:b['operations'][0]['quantum_phis'][0].update(output_wires=[])),
        ('undefined_condition',lambda b:b['operations'][0].update(condition=99)),
    ]:
        bad=copy.deepcopy(base);mutate(bad);add(name,bad,False,classical=[True])
    cbase = p(classical=[0],operations=[branch(0,
        [raw.op('classical_const',value=True,output=1)],
        [raw.op('classical_const',value=False,output=2)],classical=[cphi(1,2,3),cphi(0,0,4)])],
        results=[3,4],effect='unitary')
    for choice in [False,True]:add('classical_phi_'+str(choice),cbase,classical=[choice])
    for name,mutate in [
        ('ssa_across_exclusive_arms',lambda b:b['operations'][0]['else_ops'][0].update(output=1)),
        ('phi_forward_reference',lambda b:b['operations'][0]['classical_phis'][1].update(then_id=3)),
        ('phi_cross_arm_reference',lambda b:b['operations'][0]['classical_phis'][0].update(then_id=2)),
        ('phi_undefined_else',lambda b:b['operations'][0]['classical_phis'][0].update(else_id=99)),
    ]:
        bad=copy.deepcopy(cbase);mutate(bad);add(name,bad,False,classical=[True])
    escaped=copy.deepcopy(cbase);escaped['classical_outputs']=[1]
    add('arm_local_escape',escaped,False,classical=[True])
    nested=p(classical=[0],operations=[branch(0,[branch(0,
        [raw.op('classical_const',value=True,output=1)],
        [raw.op('classical_const',value=False,output=2)],classical=[cphi(1,2,3)])],
        [raw.op('classical_const',value=False,output=4)],classical=[cphi(3,4,5)])],
        results=[5],effect='unitary')
    for choice in [False,True]:add('nested_scope_'+str(choice),nested,classical=[choice])
    bad=copy.deepcopy(nested);bad['operations'][0]['classical_phis'][0]['then_id']=1
    add('nested_local_not_arm_visible',bad,False,classical=[True])
    previous = p(classical=[0],operations=[branch(0,
        [raw.op('classical_const',value=True,output=1)],[]),
        branch(0,classical=[cphi(1,0,2)])],results=[2],effect='unitary')
    add('closed_previous_arm_not_visible',previous,False,classical=[True])
    # Selection acts on a full two-bit input, hence includes arbitrary references.
    for tag in ['measure_z','reset','discard']:
        op=raw.op(tag,input=0)
        outputs=[1]
        if tag=='measure_z':op['output']=0
        if tag=='reset':op.update(output=2,fresh_wire=2);outputs=[1,2]
        add('residual_reference_'+tag,p([raw.port(0,[0]),raw.port(1,[1])],
            operations=[op],outputs=outputs,results=[0] if tag=='measure_z' else []))
    measured=p([raw.port(0,[0]),raw.port(1,[1])],operations=[
        raw.op('measure_z',input=0,output=0),
        branch(0,[raw.op('gate',gate='x',input=1,output=2)],[],[qphi(2,1,3,[2])]),
        raw.op('measure_z',input=3,output=1)],results=[1,0])
    add('adaptive_measurement_reversed_results',measured)
    add('hidden_measurement_coarse_graining',p([raw.port(0,[0])],operations=[
        raw.op('measure_z',input=0,output=0),raw.op('classical_const',value=False,output=1)],results=[1]))
    add('two_hidden_resets',p([raw.port(0,[0])],operations=[
        raw.op('reset',input=0,output=1,fresh_wire=1),
        raw.op('gate',gate='h',input=1,output=2),
        raw.op('reset',input=2,output=3,fresh_wire=2)],outputs=[3]))
    add('phase_before_erasure',p([raw.port(0,[0])],operations=[
        raw.op('gate',gate='t',input=0,output=1),
        raw.op('measure_z',input=1,output=0)],results=[0]))
    arm_measure = p([raw.port(0,[0]),raw.port(1,[1])],[0],[branch(0,
        [raw.op('measure_z',input=0,output=1)],
        [raw.op('measure_z',input=0,output=2)],
        [qphi(1,1,2,[2])],[cphi(1,2,3)])],[2],[3])
    arm_reset = p([raw.port(0,[0]),raw.port(1,[1])],[0],[branch(0,
        [raw.op('reset',input=0,output=2,fresh_wire=2)],
        [raw.op('reset',input=0,output=3,fresh_wire=3)],
        [qphi(2,3,4,[4]),qphi(1,1,5,[5])])],[5,4])
    for choice in [False,True]:
        add('measurement_in_selected_arm_'+str(choice),arm_measure,classical=[choice])
        add('reset_in_selected_arm_'+str(choice),arm_reset,classical=[choice])
    bad=copy.deepcopy(arm_reset)
    bad['operations'][0]['else_ops'][0]['fresh_wire']=2
    add('fresh_wire_shared_across_exclusive_arms',bad,False,classical=[False])
    bad=copy.deepcopy(arm_measure);bad['declared_effect']='unitary'
    add('observing_branch_in_unitary',bad,False,classical=[False])
    add('branch_implicit_unit_drop',p([raw.port(0,[])],[0],[branch(0)],effect='unitary'),
        False,classical=[True])
    for c in list(records):
        if c['name'] in {'pure_gate_h','classical_phi_True','adaptive_measurement_reversed_results'}:
            bad=copy.deepcopy(c);bad.update(name='work_limit_'+c['name'],budget=0,expected=False,rust=False)
            records.append(bad)
    bad=copy.deepcopy(next(c for c in records if c['name']=='pure_gate_h'))
    bad.update(name='producer_success_flag',expected=False,rust=False)
    bad['artifact']['program']['accepted']=True;records.append(bad)
    bad=copy.deepcopy(next(c for c in records if c['name']=='pure_gate_h'))
    bad.update(name='unknown_profile',expected=False,rust=False)
    bad['artifact']['format']='qleisli.raw-observing-component.future';records.append(bad)
    return records


def component_oracle(artifact, classical=()):
    """Interpret original implementations and specifications independently."""
    dependencies = []
    for entry in artifact['dependencies']:
        actual = oracle(entry['implementation'], dependencies=dependencies)
        required = oracle(entry['specification'], dependencies=dependencies)
        assert len(actual) == len(required) == 1 and not actual[0]['hidden'] and not required[0]['hidden']
        assert actual == required, 'source dependency implementation/specification disagreement'
        dependencies.append(actual[0]['operator'])
    return oracle(artifact['program'], classical, dependencies)


LEAN = finite.LEAN[:finite.LEAN.index('def execute')] + '''
open QleisliKernel.Raw.Instrument
def execute (value : Json) : WorkM Json := do
  let artifact ← adapt (QleisliKernel.Protocol.Observation.artifact (← adapt (value.getObjVal? "artifact")))
  let classical ← adapt ((← adapt ((← adapt (value.getObjVal? "classical")).getArr?)).toList.mapM Json.getBool?)
  let mode ← adapt ((← adapt (value.getObjVal? "mode")).getStr?)
  if mode == "structure" then do
    let receipts ← QleisliKernel.Raw.Function.checkAll artifact.dependencies artifact.bindings
    let checked ← QleisliKernel.Raw.Observation.verify
      (receipts.map QleisliKernel.Semantics.Function.Receipt.dependency) artifact.program
    return Json.mkObj [("owners",toJson checked.state.quantum.live.length),
      ("bits",toJson checked.state.quantum.frame.length)]
  guard (mode == "instrument")
  let checked ← inspect artifact.dependencies artifact.bindings artifact.program classical
  let histories ← checked.histories.mapM fun history => do
    let values ← artifact.program.classicalOutputs.mapM (lookup history.values)
    return Json.mkObj [("hidden",toJson history.hidden),("results",toJson values),
      ("matrix",matrixJson history.operator)]
  return Json.mkObj [("histories",toJson histories)]
''' + finite.LEAN[finite.LEAN.index('def main'):].replace('("matrix",matrixJson matrix)','("result",matrix)')


def rust_program(program):
    def cid(x):return f'ClassicalId({x})'
    def tid(x):return f'TokenId({x})'
    def wid(x):return f'WireId({x})'
    def operation(op):
        tag=op['tag']
        if tag not in OBS:
            text=raw.rust_program(raw.program(0,[op]))
            return text.split('operations:vec![',1)[1].rsplit('],quantum_outputs:',1)[0]
        tags={'measure_z':'MeasureZ','reset':'Reset','discard':'Discard',
              'classical_const':'ClassicalConst','classical_not':'ClassicalNot',
              'classical_xor':'ClassicalXor','classical_and':'ClassicalAnd',
              'classical_branch':'ClassicalBranch'}
        parts=[]
        for key,value in op.items():
            if key=='tag':continue
            if key in {'then_ops','else_ops'}:value='vec!['+','.join(operation(o) for o in value)+']'
            elif key=='quantum_phis':
                value='vec!['+','.join('QuantumPhi{then_token:'+tid(v['then_token'])+',else_token:'+tid(v['else_token'])+
                    ',output:'+tid(v['output'])+',output_wires:vec!['+','.join(wid(w) for w in v['output_wires'])+']}' for v in value)+']'
            elif key=='classical_phis':
                value='vec!['+','.join('ClassicalPhi{then_id:'+cid(v['then_id'])+',else_id:'+cid(v['else_id'])+
                    ',output:'+cid(v['output'])+'}' for v in value)+']'
            elif key=='value':value=str(value).lower()
            elif key=='fresh_wire':value=wid(value)
            elif key=='condition' or tag.startswith('classical_') or (tag=='measure_z' and key=='output'):value=cid(value)
            else:value=tid(value)
            parts.append(key+':'+value)
        return 'RawOp::'+tags[tag]+'{'+','.join(parts)+'}'
    empty=copy.deepcopy(program);empty['operations']=[];empty['classical_outputs']=[]
    text=raw.rust_program(empty)
    text=text.replace('operations:vec![]','operations:vec!['+','.join(operation(o) for o in program['operations'])+']')
    return text.replace('classical_outputs:vec![]','classical_outputs:vec!['+','.join(cid(v) for v in program['classical_outputs'])+']')


def source_cases(log, record, compiler=None):
    cases=[]
    compiler=ROOT/'target/debug/qleisli' if compiler is None else Path(compiler)
    paths=['tests/fixtures/frontend_v030/ordinary-type-cutover/current/authoring_sessions/raw-observing-v026/first','examples/bell',
           'corpus/quantum_katas/graph_state2','corpus/qualtran/control_zero_reflection2',
           'corpus/pennylane_demos/ising_zz_negative2']
    with tempfile.TemporaryDirectory(prefix='qleisli-observation-source-') as directory:
        for index,path in enumerate(paths):
            project = (current_corpus_project({'project': path.removeprefix('corpus/')})
                       if path.startswith('corpus/') else ROOT/path)
            output=Path(directory)/f'{index}.json'
            exact.command([str(compiler),'emit-ir',str(project),'--output='+str(output),'--format=json'],ROOT,log)
            original=output.read_bytes();artifact=json.loads(original)
            component=observation_sources.component(artifact)
            program=component['program']
            assert sum(port['shape']['bits'] for port in program['quantum_inputs'])<=3
            source_hashes={str(s.relative_to(ROOT)):hashlib.sha256(s.read_bytes()).hexdigest()
                           for s in sorted(project.rglob('*.qli'))}
            if record:
                dest=record.parent/'source-ir'/f'{index}.qirf.json'
                dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(original)
            cases.append(dict(name='source_'+str(index),expected=True,mode='instrument',classical=[],budget=10000000,
                artifact=component, original_qirf=original.decode('utf-8'),
                provenance=dict(source_root=str(project.relative_to(ROOT)),historical_source_root=path,
                    qirf_sha256=hashlib.sha256(original).hexdigest(),sources=source_hashes,
                    compiler_sha256=hashlib.sha256(compiler.read_bytes()).hexdigest(),
                    adapter='complete observing root and original dependency bodies; topological index renaming only')))
    return cases


def native(records, log, lean_source=LEAN):
    with tempfile.TemporaryDirectory(prefix='qleisli-observation-native-') as directory:
        project=Path(directory)
        (project/'Main.lean').write_text(lean_source)
        binary = native_harness.build(project, log)
        payload='\n'.join(finite.dumps({k:v for k,v in c.items() if k in {'artifact','classical','budget','mode'}}) for c in records)+'\n'
        run=subprocess.run([str(binary)],input=payload,text=True,capture_output=True,timeout=180)
        assert run.returncode==0,run.stderr
        observed=[json.loads(line) for line in run.stdout.splitlines()]
        bindings=dict(lean_binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
            lean_input_sha256=hashlib.sha256(payload.encode()).hexdigest(),
            lean_stdout_sha256=hashlib.sha256(run.stdout.encode()).hexdigest(),
            lean_stderr_sha256=hashlib.sha256(run.stderr.encode()).hexdigest())
        actions=[]
        for c in records:
            if not c.get('rust',True):continue
            if 'original_qirf' in c:
                filename=f'source-{len(actions)}.qirf'
                (project/filename).write_bytes(c['original_qirf'].encode('utf-8'))
                actions.append('println!("{} {}",'+json.dumps(c['name'])+
                    ',qleisli::interchange::native::Kernel::selected().expect("explicit native checker")'+
                    '.check(include_bytes!('+json.dumps(filename)+'),None).is_ok());')
                continue
            text=rust_program(c['artifact']['program'])
            actions.append('println!("{} {}",'+json.dumps(c['name'])+',qleisli::interchange::native::Kernel::selected().expect("explicit native checker").accept_raw('+text+').is_ok());')
        source='use qleisli::ir::*;\nfn main(){\n'+'\n'.join(actions)+'\n}\n'
        (project/'Cargo.toml').write_text('[package]\nname="qleisli_observation_test"\nversion="0.0.0"\nedition="2024"\n[dependencies]\nqleisli={path='+json.dumps(str(ROOT))+'}\n[[bin]]\nname="observation-test"\npath="main.rs"\n')
        (project/'main.rs').write_text(source)
        output=exact.command(['cargo','run','--offline','--quiet'],project,log)
        rust={line.split()[0]:line.split()[1]=='true' for line in output.splitlines()}
        bindings.update(rust_binary_sha256=hashlib.sha256((project/'target/debug/observation-test').read_bytes()).hexdigest(),
            rust_stdout_sha256=hashlib.sha256(output.encode()).hexdigest())
        return observed,rust,bindings


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--record',type=Path)
    parser.add_argument('--compiler',type=Path,default=ROOT/'target/debug/qleisli')
    args=parser.parse_args()
    log=[];records=cases()+source_cases(log,args.record,args.compiler.resolve())
    observed,rust,bindings=native(records,log)
    if args.record:
        args.record.parent.mkdir(parents=True,exist_ok=True)
        args.record.with_name('native-observed.json').write_text(json.dumps(
            dict(lean=observed,rust=rust,bindings=bindings),indent=2)+'\n')
    assert len(observed)==len(records)
    operators=histories=0
    for case,result in zip(records,observed):
        assert result['accepted']==case['expected'],(case['name'],result)
        if case['name'] in rust:
            # Missing caller values are transport-level, not Rust raw validity.
            if case['name']!='classical_missing_values':
                assert result['accepted']==rust[case['name']],(case['name'],result,rust[case['name']])
        if not result['accepted'] or case['mode']=='structure':continue
        expected=component_oracle(case['artifact'],case['classical'])
        actual=result['result']['histories']
        assert len(actual)==len(expected),(case['name'],len(actual),len(expected))
        dimension=len(expected[0]['operator'][0]);gram=[[ZERO[:] for _ in range(dimension)] for _ in range(dimension)]
        for output,wanted in zip(actual,expected):
            assert output['hidden']==wanted['hidden'] and output['results']==wanted['results'],case['name']
            matrix=output['matrix'];target=wanted['operator']
            assert matrix['rows']==len(target) and matrix['cols']==len(target[0]),case['name']
            assert [exact.decoded(v) for v in matrix['entries']]==[v for row in target for v in row],case['name']
            term=exact.oracle_compose(exact.oracle_adjoint(target),target)
            gram=[[[x+y for x,y in zip(a,b)] for a,b in zip(ar,br)] for ar,br in zip(gram,term)]
            operators+=1
        assert gram==finite.identity(dimension),case['name']
        histories+=len(actual)
    paths=[ROOT/'lean-kernel/QleisliKernel/Semantics/Observation.lean',
           ROOT/'lean-kernel/QleisliKernel/Raw/Observation.lean',
           ROOT/'lean-kernel/QleisliKernel/Raw/Instrument.lean',
           ROOT/'lean-kernel/Protocol/Observation.lean',ROOT/'lean/Qleisli/RawInstrument.lean',
        ROOT/'lean/Qleisli/RawInstrumentDenotation.lean',ROOT/'lean/Qleisli/Semantics/RawInstrument.lean',
        Path(observation_sources.__file__),Path(raw.__file__),Path(finite.__file__),Path(exact.__file__),
        ROOT/'scripts/check_verification_inventory.py',ROOT/'src/ir.rs',Path(__file__)]
    comparisons=sum(name!='classical_missing_values' for name in rust)
    report=dict(native_cases=len(records),rust_checks=len(rust),rust_comparisons=comparisons,
        original_constructors=len(variants((ROOT/'src/ir.rs').read_text(),'RawOp')),
        independent_operators=operators,hidden_histories=histories,complete_observing_sources=5,
        max_semantic_qubits=3,native_bindings=bindings,commands=log,
        source_sha256={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in paths},
        remaining=['six-bit dense component; general matrix-free acceptance and branch functions use separate VM-26 modules',
                   'general source/runtime preservation',
                   'native compiler/decoder/runtime correspondence'])
    if args.record:
        args.record.parent.mkdir(parents=True,exist_ok=True)
        args.record.write_text(json.dumps(report,indent=2)+'\n')
        args.record.with_name('native-inputs.json').write_text(json.dumps(records,indent=2,default=str)+'\n')
    print(f'{len(records)} native cases; {comparisons} Rust comparisons; {operators} exact Kraus operators; {histories} retained histories')


if __name__=='__main__':
    main()
