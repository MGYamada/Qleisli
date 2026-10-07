#!/usr/bin/env python3
"""Original matrix-free instrument: independent native, Rust and exact R8.
Only small post-acceptance operators are materialized for comparison.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import test_lean_observation as observation
import test_lean_exact as exact
import test_lean_finite as finite
import test_lean_raw as raw
import test_lean_raw_completion as completion
ROOT = observation.ROOT

LEAN = observation.finite.LEAN[:observation.finite.LEAN.index('def execute')] + '''
open QleisliKernel.Raw.StreamedInstrument
def execute (value : Json) : WorkM Json := do
  let artifact ← adapt (QleisliKernel.Protocol.StreamedObservation.artifact (← adapt (value.getObjVal? "artifact")))
  let classical ← adapt ((← adapt ((← adapt (value.getObjVal? "classical")).getArr?)).toList.mapM Json.getBool?)
  let mode ← adapt ((← adapt (value.getObjVal? "mode")).getStr?)
  if mode == "structure" then do
    let receipts ← QleisliKernel.Raw.BranchFunction.checkAll artifact.dependencies artifact.bindings
    let checked ← QleisliKernel.Raw.Observation.verify
      (receipts.map QleisliKernel.Semantics.ObservingFunction.Receipt.dependency) artifact.program
    return Json.mkObj [("owners",toJson checked.state.quantum.live.length),
      ("bits",toJson checked.state.quantum.frame.length)]
  guard (mode == "instrument")
  let checked ← inspect artifact.dependencies artifact.bindings artifact.program classical
  let histories ← checked.histories.mapM fun history => do
    let values ← artifact.program.classicalOutputs.mapM (QleisliKernel.Raw.Instrument.lookup history.values)
    let rows := 2^checked.structureCheck.state.quantum.frame.length
    let cols := 2^checked.structureCheck.prepared.inputBits
    let entries ← (List.range (rows*cols)).mapM (fun index => history.operator (index / cols) (index % cols))
    return Json.mkObj [("hidden",toJson history.hidden),("results",toJson values),
      ("matrix",Json.mkObj [("rows",toJson rows),("cols",toJson cols),("entries",toJson (entries.map scalarJson))])]
  return Json.mkObj [("histories",toJson histories)]
''' + observation.finite.LEAN[observation.finite.LEAN.index('def main'):].replace('("matrix",matrixJson matrix)','("result",matrix)')



def cases():
    records=observation.cases()
    for case in records:
        if case['name']!='unknown_profile':case['artifact']['format']='qleisli.raw-instrument-component'
        case['budget']=100000000 if case['budget'] else 0
    body=observation.p([raw.port(0,[0])],operations=[raw.op('classical_const',value=True,output=0),
        observation.branch(0,[raw.op('gate',gate='t',input=0,output=1)],
            [raw.op('gate',gate='z',input=0,output=2)],[observation.qphi(1,2,3,[1])])],outputs=[3],effect='unitary')
    specified=raw.program(1,[raw.op('gate',gate='t',input=0,output=1)],1)
    function=completion.attached(dict(signature=['bit'],implementation=body,specification=specified),
        sources=[('branch.qli','original T branch source')])
    root=observation.p([raw.port(0,[0,1])],operations=[
        raw.op('apply_unitary',input=0,output=1,steps=[finite.call([1],0,True,[(0,False)])]),
        raw.op('split',input=1,left=2,right=3,left_bits=1),raw.op('measure_z',input=3,output=0)],outputs=[2],results=[0])
    record=dict(name='retained_branch_negative_control_adjoint',expected=True,mode='instrument',classical=[],budget=100000000,
        artifact=dict(format='qleisli.raw-instrument-component',version=1,dependencies=[function],bindings=copy.deepcopy([function]),program=root),rust=False)
    records.append(record)
    for name,mutation in [
        ('retained_unselected_invalid_owner',lambda e:e['implementation']['operations'][1]['else_ops'][0].update(input=99)),
        ('retained_changed_unselected_body_binding',lambda e:e['implementation']['operations'][1]['else_ops'][0].update(gate='h')),
        ('retained_changed_source_binding',lambda e:e['identity']['sources'][0].update(source='changed')),
    ]:
        changed=copy.deepcopy(record);changed.update(name=name,expected=False)
        mutation(changed['artifact']['dependencies'][0])
        records.append(changed)
    return records


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--record',type=Path,required=True)
    parser.add_argument('--compiler',type=Path,default=ROOT/'target/debug/qleisli')
    args=parser.parse_args()
    log=[];records=cases()+observation.source_cases(log,args.record,args.compiler.resolve())
    for case in records:
        if case['name'].startswith('source_'):case['artifact']['format']='qleisli.raw-instrument-component';case['budget']=100000000
    observed,rust,bindings=observation.native(records,log,LEAN)
    assert len(observed)==len(records)
    args.record.parent.mkdir(parents=True,exist_ok=True)
    args.record.with_name('streamed-observed.json').write_text(json.dumps(dict(lean=observed,rust=rust,bindings=bindings),indent=2)+'\n')
    operators=0
    for case,result in zip(records,observed):
        assert result['accepted']==case['expected'],(case['name'],result)
        if case['name'] in rust and case['name']!='classical_missing_values':
            assert result['accepted']==rust[case['name']],(case['name'],result,rust[case['name']])
        if not result['accepted'] or case['mode']=='structure':continue
        expected=observation.component_oracle(case['artifact'],case['classical'])
        actual=result['result']['histories'];assert len(actual)==len(expected),case['name']
        dimension=len(expected[0]['operator'][0]);gram=[[finite.ZERO[:] for _ in range(dimension)] for _ in range(dimension)]
        for output,wanted in zip(actual,expected):
            assert output['hidden']==wanted['hidden'] and output['results']==wanted['results'],case['name']
            matrix=output['matrix'];target=wanted['operator']
            assert matrix['rows']==len(target) and matrix['cols']==len(target[0]),case['name']
            assert [exact.decoded(v) for v in matrix['entries']]==[v for row in target for v in row],case['name']
            term=exact.oracle_compose(exact.oracle_adjoint(target),target)
            gram=[[[x+y for x,y in zip(a,b)] for a,b in zip(ar,br)] for ar,br in zip(gram,term)]
            operators+=1
        assert gram==finite.identity(dimension),case['name']
    paths=[ROOT/'lean-kernel/QleisliKernel/Raw/Coefficient.lean',ROOT/'lean-kernel/QleisliKernel/Raw/StreamedInstrument.lean',
        ROOT/'lean-kernel/Protocol/StreamedObservation.lean',ROOT/'lean/Qleisli/RawCoefficient.lean',
        ROOT/'lean/Qleisli/RawStreamedInstrument.lean',ROOT/'lean/Qleisli/Semantics/ObservingAction.lean',Path(__file__),
        ROOT/'scripts/test_lean_observation.py',ROOT/'scripts/observation_sources.py']
    report=dict(status='passed',native_cases=len(records),rust_comparisons=sum(name!='classical_missing_values' for name in rust),
        independent_operators=operators,hidden_histories=operators,original_constructors=19,max_semantic_qubits=3,
        complete_observing_sources=5,retained_branch_dependency_cases=4,native_bindings=bindings,commands=log,
        source_sha256={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in paths},
        scope='actual matrix-free coefficient checker; post-acceptance small operator display; exponential budgeted verification',
        remaining=['general source/runtime preservation','native compiler/decoder/runtime correspondence'])
    args.record.write_text(json.dumps(report,indent=2)+'\n')
    args.record.with_name('streamed-inputs.json').write_text(json.dumps(records,indent=2)+'\n')
    print(f'{len(records)} native streamed cases; {report["rust_comparisons"]} Rust comparisons; {operators} exact Kraus operators')

if __name__=='__main__':main()
