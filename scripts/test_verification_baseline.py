#!/usr/bin/env python3
"""VM-22 bounded comparison: Rust, independent complex oracle, Lean word slice.
No oracle below issues evidence. Full Lean finite verification starts at VM-23.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import cmath
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import tempfile

from check_verification_inventory import ROOT, check
from check_input_corpus import current_project as current_corpus_project

FIXTURES = ROOT/'tests/fixtures/verification_v022'
NAMES = ['h','t','unit_phase','toffoli','raw_qif_unit','raw_computed_target']


def unique(pairs):
    result = {}
    for key,value in pairs:
        if key in result: raise ValueError('duplicate result field: '+key)
        result[key]=value
    return result


def invoke(args, expected=0, timeout=60, env=None):
    # Bound retained output, even for a malfunctioning native executable.
    with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
        result=subprocess.run([str(x) for x in args],cwd=ROOT,stdout=out,stderr=err,timeout=timeout,env=env,check=False)
        out.seek(0); err.seek(0)
        stdout,stderr=out.read(1_048_577),err.read(1_048_577)
    if len(stdout)>1_048_576 or len(stderr)>1_048_576: raise ValueError('process output limit exceeded')
    if result.returncode!=expected: raise ValueError(f'process exit {result.returncode}, expected {expected}: {stderr.decode(errors="replace")} {stdout.decode(errors="replace")}')
    return stdout.decode(),stderr.decode()


def matrix(description):
    if description['domain']!='zeta8-dyadic-v1': raise ValueError('unsupported test domain')
    basis=[1,math.sqrt(2),1j,1j*math.sqrt(2)]
    return [sum(int(c['numerator'])*2.0**(-c['denominator_bits'])*basis[j] for j,c in enumerate(entry)) for entry in description['entries']]


def gate(state, axis, name, controls=()):
    for x in range(len(state)):
        if x & (1<<axis) or not all(bool(x&(1<<a))==v for a,v in controls): continue
        y=x|(1<<axis)
        a,b=state[x],state[y]
        if name=='h': state[x],state[y]=(a+b)/math.sqrt(2),(a-b)/math.sqrt(2)
        elif name=='x': state[x],state[y]=b,a
        elif name=='z': state[y]=-b
        elif name=='t': state[y]=b*cmath.exp(1j*math.pi/4)
        else: raise ValueError('unsupported oracle gate')


def oracle(artifact):
    """Independent basis-column evolution for ONLY the six frozen pure cases.

    Direct complex gates and explicit scratch preparation/cleanup; no Rust
    extraction, claimed matrix, inverse-pair oracle or probability-only equality.
    This does not implement general raw validity or a production decoder.
    """
    program=artifact['programs'][artifact['root']]
    inputs=program['quantum_inputs']
    if len(inputs)!=1 or program['declared_effect']!='unitary' or artifact['evidence']: raise ValueError('outside bounded oracle scope')
    wires=inputs[0]['wires']; n=len(wires); dimension=1<<n
    if n>3: raise ValueError('oracle scope is at most three qubits')
    columns=[]
    for original in range(dimension):
        owners={inputs[0]['token']:list(range(n))}
        state=[complex(x==original) for x in range(dimension)]
        for op in program['operations']:
            tag=op['tag']
            if tag=='split':
                axes=owners.pop(op['input']); cut=op['left_bits']
                owners[op['left']],owners[op['right']]=axes[:cut],axes[cut:]
            elif tag=='join': owners[op['output']]=owners.pop(op['left'])+owners.pop(op['right'])
            elif tag=='gate':
                axes=owners.pop(op['input']); gate(state,axes[0],op['gate']); owners[op['output']]=axes
            elif tag=='toffoli':
                a,b,t=(owners.pop(op[k]) for k in ['control_a','control_b','target'])
                if len({a[0],b[0],t[0]})!=3: raise ValueError('aliased oracle operand')
                gate(state,t[0],'x',[(a[0],True),(b[0],True)])
                for key,axes in zip(['control_a_out','control_b_out','target_out'],[a,b,t]): owners[op[key]]=axes
            elif tag=='quantum_if':
                control=owners.pop(op['control']); target=owners.pop(op['target'])
                if target: raise ValueError('oracle qif slice requires Unit target')
                for x in range(dimension):
                    for step in op['one_ops'] if x&(1<<control[0]) else op['zero_ops']:
                        if step!={'tag':'scalar_phase','phase':'eighth_turn'}: raise ValueError('unsupported oracle qif step')
                        state[x]*=cmath.exp(1j*math.pi/4)
                owners[op['control_out']],owners[op['target_out']]=control,target
            elif tag=='apply_unitary':
                axes=owners.pop(op['input'])
                if axes or op['steps']!=[{'action':{'indices':[],'permutation':[0],'phases':[1],'tag':'monomial'},'controls':[]}]: raise ValueError('unsupported scalar slice')
                state[0]*=cmath.exp(1j*math.pi/4); owners[op['output']]=axes
            elif tag=='compute_use_uncompute':
                source=owners.pop(op['source']); target=op['targets'][0]; targets=owners.pop(target['input'])
                if len(source)!=1 or len(targets)!=1 or op['function']!=[0,1] or len(op['ancilla_wires'])!=1: raise ValueError('unsupported computed slice')
                # Prepare f(x) in a fresh scratch bit, use it coherently, undo.
                extended=[0j]*(dimension*2)
                for x,amplitude in enumerate(state): extended[x|(((x>>source[0])&1)<<n)]=amplitude
                for use in op['use_ops']:
                    if use!={'tag':'controlled_target_gate','controls':[{'bit':{'index':0,'region':'ancilla'},'when_one':True}],'target_index':0,'gate':'x'}: raise ValueError('unsupported protected slice')
                    gate(extended,targets[0],'x',[(n,True)])
                cleaned=[0j]*(dimension*2)
                for x,amplitude in enumerate(extended): cleaned[x^(((x>>source[0])&1)<<n)]+=amplitude
                if any(abs(x)>1e-12 for x in cleaned[dimension:]): raise ValueError('dirty scratch')
                state=cleaned[:dimension]; owners[op['source_out']]=source; owners[target['output']]=targets
            else: raise ValueError('outside oracle constructor slice: '+tag)
        if len(owners)!=1 or len(program['quantum_outputs'])!=1: raise ValueError('incomplete oracle outputs')
        axes=owners[program['quantum_outputs'][0]]
        if axes!=list(range(n)): raise ValueError('changed output axes')
        columns.append(state)
    return [columns[col][row] for row in range(dimension) for col in range(dimension)]


def agrees(actual, expected):
    return len(actual)==len(expected) and all(abs(x-y)<2e-12 for x,y in zip(actual,expected))


def word_oracle(program, required):
    """Independent two-trajectory oracle for the captured word component."""
    try:
        header='qleisli.phase-word 1 phase256-word-v1\nBit->Bit\n'
        if not program.startswith(header) or not required.startswith(header): return False
        claim,count,*word=program[len(header):].splitlines()
        count=int(count)
        if not 0<=count<=4096 or count!=len(word): return False
        if not claim.startswith('claim ') or not required[len(header):].startswith('expect '): return False
        claimed=tuple(map(int,claim.split()[1:])); expected=tuple(map(int,required[len(header):].split()[1:]))
        trajectories=[]
        for original in [0,1]:
            bit,phase=original,0
            for line in word:
                if line=='x': bit^=1
                else:
                    name,ticks=line.split()
                    if name!='phase' or not 0<=int(ticks)<256: return False
                    if bit: phase=(phase+int(ticks))%256
            trajectories.append((bit,phase))
        actual=(trajectories[0][0],trajectories[0][1],trajectories[1][1])
        return claimed==actual==expected
    except (ValueError,IndexError): return False


def frozen(name, data, capture):
    path=FIXTURES/name
    if capture:
        path.parent.mkdir(parents=True,exist_ok=True); path.write_bytes(data)
    elif path.read_bytes()!=data: raise ValueError('frozen fixture drift: '+name)
    return path


def finite_comparisons():
    records=[]
    for name in NAMES:
        required=matrix(json.loads((FIXTURES/f'finite/{name}.matrix.json').read_text()))
        wrong=matrix(json.loads((FIXTURES/f'finite/{name}.wrong-phase.json').read_text()))
        for version in ['v1','v2']:
            actual=oracle(json.loads((FIXTURES/f'finite/{name}.{version}.qirf').read_text()))
            if not agrees(actual,required) or agrees(actual,wrong): raise ValueError('independent finite oracle disagreement: '+name)
            records.append(dict(case=name,version=version,qubits=int(math.log2(math.sqrt(len(actual)))),rust_required=True,oracle_required=True,rust_wrong_phase=False,oracle_wrong_phase=False,lean_finite='not implemented; VM-23–26'))
    return records


def source_comparisons(binary):
    from observation_sources import component
    from test_lean_observation import component_oracle
    sources=[
        ('corpus/quantum_katas/swap2',{(True,False):1}),
        ('corpus/quantum_katas/fredkin3',{(True,True,False):1}),
        ('corpus/qualtran/xor_constant2',{(False,False):1}),
        ('corpus/qualtran/bitwise_not2',{(True,False):1}),
        ('corpus/pennylane_demos/rx_quarter',{(False,):.5,(True,):.5}),
        ('corpus/pennylane_demos/phase_kickback1',{(True,True):1}),
        ('examples/bell',{(False,False):.5,(True,True):.5}),
        ('examples/feedback',{(False,False):.5,(True,False):.5}),
    ]
    records=[]
    for project,required in sources:
        current_project = (current_corpus_project({'project': project.removeprefix('corpus/')})
                           if project.startswith('corpus/') else ROOT/project)
        decisions={}
        for command in ['check','run']:
            stdout,_=invoke([binary,command,current_project,'--format=json'])
            data=json.loads(stdout,object_pairs_hook=unique)
            if data['outcome']!='ok' or data['diagnostics']: raise ValueError('source check failed')
            decisions[command]=data
        actual={tuple(x['bits']):x['probability'] for x in decisions['run']['result']['distribution']}
        if any(abs(actual.get(k,0)-required.get(k,0))>2e-12 for k in actual.keys()|required.keys()): raise ValueError('source probability disagreement: '+project)
        with tempfile.TemporaryDirectory(prefix='qleisli-vm22-source-') as directory:
            emitted=Path(directory)/'program.qirf'
            invoke([binary,'emit-ir',current_project,'--output='+str(emitted),'--format=json'])
            path=FIXTURES/'source'/str(project.replace('/','_')+'.qirf')
            original, current = path.read_bytes(), emitted.read_bytes()
            verifications = {}
            for label, artifact_path in [('historical', path), ('current', emitted)]:
                stdout,_=invoke([binary,'verify-ir',artifact_path,'--format=json'])
                verified=json.loads(stdout,object_pairs_hook=unique)
                if verified['result']!={'verified':True,'request_checked':False}: raise ValueError('unexpected ordinary IR guarantee')
                verifications[label] = verified
            # Encoding and dependency graphs may evolve. The frozen artifact
            # remains immutable; compare full exact unnormalized operators,
            # including phase and ordered hidden/classical outcomes.
            before=component_oracle(component(json.loads(original,object_pairs_hook=unique)))
            after=component_oracle(component(json.loads(current,object_pairs_hook=unique)))
            if before != after: raise ValueError('source instrument drift: '+project)
        records.append(dict(project=project,current_project=str(current_project.relative_to(ROOT)),
            artifact=str(path.relative_to(ROOT)),decisions=decisions,raw_verification=verifications,
            historical_sha256=hashlib.sha256(original).hexdigest(),current_sha256=hashlib.sha256(current).hexdigest(),
            exact_instrument_comparison=True,
            reference_distribution=[dict(bits=list(k),probability=v) for k,v in required.items()]))
    for name in ['duplicate_owner','measured_owner','measurement_adjoint','dirty_auxiliary']:
        project='corpus/negative/'+name
        current_project = current_corpus_project({'project': project.removeprefix('corpus/')})
        stdout,_=invoke([binary,'check',current_project,'--format=json'],1)
        data=json.loads(stdout,object_pairs_hook=unique)
        if data['outcome']!='error' or not data['diagnostics']: raise ValueError('missing negative source diagnostic')
        records.append(dict(project=project,current_project=str(current_project.relative_to(ROOT)),decision=data))
    return records


def native_comparisons(binary, capture):
    header='qleisli.phase-word 1 phase256-word-v1\nBit->Bit\n'
    artifact=header+'claim 0 0 32\n1\nphase 32\n'
    request=header+'expect 0 0 32\n'
    cases=[('t',artifact,request,True,'accepted','verification'),
           ('t_wrong_phase',artifact,header+'expect 0 128 160\n',False,'rejected','verification'),
           ('t_forged_claim',artifact.replace('claim 0 0 32','claim 0 0 31'),request,False,'rejected','verification'),
           ('t_wrong_domain',artifact.replace('phase256-word-v1','zeta8-dyadic-v1'),request,False,'syntax','artifact'),
           ('t_bad_count',artifact.replace('\n1\n','\n4097\n'),request,False,'limit','artifact')]
    records=[]
    for name,program,required,accepted,code,stage in cases:
        a=frozen('native/'+name+'.qpk',program.encode(),capture)
        r=frozen('native/'+name+'.qpr',required.encode(),capture)
        stdout,stderr=invoke([binary,a,r],0 if accepted else 1,timeout=5)
        data=json.loads(stdout,object_pairs_hook=unique)
        if stderr or data!=dict(format='qleisli.kernel-result',version=1,profile='phase256-word-v1',accepted=accepted,code=code,stage=stage): raise ValueError('native protocol disagreement')
        reference=word_oracle(program,required)
        if reference!=accepted: raise ValueError('independent word oracle disagreement')
        records.append(dict(case=name,decision=data,reference_accepted=reference,scope='experimental word component; R8 phase exponent 1 embeds as 32/256'))
    return records


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('binary',type=Path)
    parser.add_argument('--kernel',type=Path)
    parser.add_argument('--report',type=Path)
    parser.add_argument('--capture',action='store_true',help='explicitly replace native/hierarchy snapshots; historical source IR stays immutable')
    args=parser.parse_args()
    errors=check()
    if errors: raise ValueError('; '.join(errors))
    environment=dict(os.environ)
    for key in ['QLEISLI_VM22_CAPTURE','QLEISLI_VM22_HIERARCHY_CAPTURE']: environment.pop(key,None)
    stdout,stderr=invoke(['cargo','test','--test','verification_boundary'],env=environment)
    report=dict(format='qleisli.verification-baseline',version=1,packet='VM-22',authority='Lean production acceptance; independent bounded historical/current comparisons',rust_test=dict(stdout=stdout,stderr=stderr),finite=finite_comparisons(),source=source_comparisons(args.binary.resolve()))
    report['native']=native_comparisons(args.kernel.resolve(),args.capture) if args.kernel else 'not run; optional source-built kernel'
    if args.kernel:
        environment['QLEISLI_HIERARCHY_KERNEL']=str(args.kernel.resolve())
        if args.capture: environment['QLEISLI_VM22_HIERARCHY_CAPTURE']=str(FIXTURES/'hierarchy')
        output,error=invoke(['cargo','test','--test','hierarchical_host','vm22_frozen_hierarchy_requests_recheck_finite_premises_and_cycles','--','--ignored','--exact'],env=environment)
        report['hierarchy']=dict(stdout=output,stderr=error,cases=4,scope='Fresh native structural/request checking plus Rust finite reconstruction; conditional, not production Lean evidence',decisions={'h':'request checked','wrong_phase_request':'contract','wrong_leaf_under_zero_repeat':'contract','cycle':'invalid_ir'})
    else: report['hierarchy']='not run; optional source-built kernel'
    report['binaries']={'rust':hashlib.sha256(args.binary.read_bytes()).hexdigest()}
    if args.kernel: report['binaries']['lean']=hashlib.sha256(args.kernel.read_bytes()).hexdigest()
    report['maximum_qubits']=3
    report['claims']='Bounded comparisons and frozen inputs; not a soundness proof or production dual checking.'
    if args.report:
        args.report.parent.mkdir(parents=True,exist_ok=True); args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(f"VM-22: {len(report['finite'])} finite comparisons, {len(report['source'])} source decisions, {len(report['native']) if isinstance(report['native'],list) else 0} native component decisions; at most three qubits.")


if __name__=='__main__': main()
