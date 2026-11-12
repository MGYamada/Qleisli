import QleisliKernel.Qirf.RuntimePrimitiveSource
import QleisliKernel.Qirf.RuntimePureInterval
import QleisliKernel.Raw.ProtectedEvaluation

/-! An original unary operation application with different source port types.
The caller supplies the exact action from the checked original operation graph.
The literal pure interval, canonical codes, and complete owner change must all
agree before the result can participate in source-body traversal.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeRectangularOperation
open QleisliKernel Finite SourceTypes
open RuntimeStructuralAction (SourceState)
open RuntimePrimitiveSource (PortAt readPort)
open RuntimeOwnerMap (Owner Port)

def continued (before : SourceState) (input output : Owner) (returned : Port) : SourceState :=
  ⟨before.bindings.filter (fun binding => binding.owner != input) ++ [⟨output,returned⟩],
    before.issued ++ [output],before.nextOrdinal+1⟩

structure SourcePorts {sources caller} (event : SourceOperationApplication.Event sources caller)
    (before : SourceState) where
  input : Owner
  output : Owner
  originalInputs : event.inputOwners = [input]
  originalOutputs : event.outputOwners = [output]
  retired : event.consumed = [input]
  allocated : event.allocated = [output]
  fresh : event.nextOrdinal = before.nextOrdinal ∧ output.ordinal = before.nextOrdinal ∧
    event.afterOrdinal = before.nextOrdinal+1 ∧ output.ordinal ∉ before.issued.map (·.ordinal)
  changed : input.basis ≠ output.basis

private def readSourcePorts {sources caller} (event : SourceOperationApplication.Event sources caller)
    (before : SourceState) : WorkM (SourcePorts event before) := do
  exactWork (Exact.charge (16*(Raw.OwnerFlow.fields (event.inputOwners ++ event.outputOwners ++
    event.consumed ++ event.allocated ++ before.issued)+1)))
  match inputs : event.inputOwners, outputs : event.outputOwners with
  | [input],[output] =>
    if transition : event.consumed = [input] ∧ event.allocated = [output] ∧
        (event.nextOrdinal = before.nextOrdinal ∧ output.ordinal = before.nextOrdinal ∧
          event.afterOrdinal = before.nextOrdinal+1 ∧ output.ordinal ∉ before.issued.map (·.ordinal)) ∧
        input.basis ≠ output.basis then
      return ⟨input,output,inputs,outputs,transition.1,transition.2.1,transition.2.2.1,transition.2.2.2⟩
    else throw .request
  | _,_ => throw .request

structure Checked {sources caller dependencies program block start count}
    (event : SourceOperationApplication.Event sources caller)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before : SourceState) (expected : Semantics.Exact.Matrix) where
  source : SourcePorts event before
  entry : PortAt source.input before.bindings
  returned : Port
  frame : RuntimePureInterval.Literal block start count [entry.port.token] [returned.token] event.effect
  sameInterval : frame.interval = interval
  entryPort : frame.selected = [entry.port]
  returnPort : frame.returned = [returned]
  after : RuntimeOwnerMap.Checked ((continued before source.input source.output returned).bindings.map (·.owner))
    interval.after
  afterBindings : after.bindings = (continued before source.input source.output returned).bindings
  inputCode : Semantics.Exact.Matrix
  outputCode : Semantics.Exact.Matrix
  inputRead : RuntimeInterval.Computed (Carrier.ownerCode [⟨entry.port,source.input.basis⟩]) inputCode
  outputRead : RuntimeInterval.Computed (Carrier.ownerCode [⟨returned,source.output.basis⟩]) outputCode
  physical : Semantics.Exact.Matrix
  physicalRead : RuntimeInterval.Computed (Raw.ProtectedEvaluation.reconstruct dependencies
    (RuntimePureInterval.fragmentWithEffect frame.selected frame.operations [returned.token] event.effect)) physical
  action : CodeSpace.Map inputCode outputCode physical
  equation : action.logical = expected

def read {sources caller dependencies program block start count}
    (event : SourceOperationApplication.Event sources caller)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before : SourceState) (expected : Semantics.Exact.Matrix) : WorkM (Checked event interval before expected) := do
  let source ← readSourcePorts event before
  let entry ← readPort source.input before.bindings
  let spectators := PureInterval.spectators interval.before [entry.port.token]
  exactWork (Exact.charge (16*((spectators.length+1)*(interval.after.quantum.live.length+1)+1)))
  let [returned] := interval.after.quantum.live.filter (fun port => !spectators.contains port)
    | throw .request
  let frame ← RuntimePureInterval.readLiteral interval [entry.port.token] [returned.token] event.effect
  if ports : frame.val.selected = [entry.port] ∧ frame.val.returned = [returned] then
    let next := continued before source.input source.output returned
    let after ← RuntimeOwnerMap.checkBindings (next.bindings.map (·.owner)) interval.after next.bindings
    let input ← NaturalAffine.witness (Carrier.ownerCode [⟨entry.port,source.input.basis⟩])
    let output ← NaturalAffine.witness (Carrier.ownerCode [⟨returned,source.output.basis⟩])
    let physical ← NaturalAffine.witness (Raw.ProtectedEvaluation.reconstruct dependencies
      (RuntimePureInterval.fragmentWithEffect frame.val.selected frame.val.operations [returned.token] event.effect))
    let action ← CodeSpace.readMap input.val output.val physical.val
    exactWork (Exact.charge (action.logical.entries.length+expected.entries.length+1))
    if equation : action.logical = expected then
      return ⟨source,entry,returned,frame.val,frame.property,ports.1,ports.2,after.val,after.property,
        input.val,output.val,by with_reducible exact input.property,by with_reducible exact output.property,
        physical.val,by with_reducible exact physical.property,action,equation⟩
    else throw .equation
  else throw .request

end QleisliKernel.Qirf.RuntimeRectangularOperation
