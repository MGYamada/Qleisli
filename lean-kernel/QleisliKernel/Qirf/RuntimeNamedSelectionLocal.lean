import QleisliKernel.Qirf.RuntimeNamedSelectionOccurrence
import QleisliKernel.Qirf.RuntimeNamedBoundary

/-! An original named selection at its genuine internal caller interval.
The surrounding traversal supplies the actual current source/native frame.
Only the selected ports enter the canonical callee program; caller spectators
remain in the parent interval. No whole-caller input, return or singleton-body
claim is manufactured by this local adapter.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNamedSelectionLocal
open QleisliKernel Finite SourceTypes
open QleisliKernel.SourceTypes.SourceRuntimeValues (valueOwners owners)
abbrev Map := RuntimeOwnerMap.Map
abbrev SourceState := RuntimeStructuralAction.SourceState

structure Frame {artifact owner name arguments source request}
    (occurrence : @RuntimeNamedSelectionOccurrence.Prepared artifact owner name arguments source request)
    (root : Validity.Root) {program : Semantics.Observation.Program}
    (block : RuntimeInterval.Block root.dependencies program) (before : SourceState) where
  interval : RuntimeInterval.Checked block occurrence.parts.position.start occurrence.parts.position.count
  callerFrame : RuntimeOwnerMap.Checked (before.bindings.map (·.owner)) interval.before
  sameCaller : callerFrame.bindings = before.bindings
  completeFrame : (occurrence.parts.event.held ++ occurrence.parts.event.inputOwners ++
    owners occurrence.parts.event.remaining).Perm (before.bindings.map (·.owner))
  inputs : Map
  inputRead : RuntimeInterval.Computed
    (RuntimeOwnerMap.order occurrence.parts.event.inputOwners before.bindings) inputs
  scope : RuntimeCallInterval.Checked block occurrence.parts.position.start occurrence.parts.position.count
    (inputs.map (·.port.token))
  initial : Map
  initialRead : RuntimeInterval.Computed (RuntimeSourceBoundary.bindings
    (occurrence.call.callee.checked.summary.parameterValues.flatMap valueOwners)
    ((scope.selected.zip occurrence.parts.event.inputOwners).map fun (port,role) =>
      (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner))) initial

def prepare {artifact owner name arguments source request}
    (occurrence : @RuntimeNamedSelectionOccurrence.Prepared artifact owner name arguments source request)
    (root : Validity.Root) {program : Semantics.Observation.Program}
    (block : RuntimeInterval.Block root.dependencies program) (before : SourceState) :
    WorkM (Frame occurrence root block before) := do
  let event := occurrence.parts.event
  let position := occurrence.parts.position
  let roles := event.held ++ event.inputOwners ++ owners event.remaining
  exactWork (Exact.charge (64*(Raw.OwnerFlow.fields roles+Raw.OwnerFlow.fields
    (before.bindings.map (·.owner))+1)*(roles.length+before.bindings.length+1)^2))
  let interval ← RuntimeInterval.check block position.start position.count
  let callerFrame ← RuntimeOwnerMap.checkBindings (before.bindings.map (·.owner)) interval.before before.bindings
  if completeFrame : roles.Perm (before.bindings.map (·.owner)) then
    let inputs ← NaturalAffine.witness (RuntimeOwnerMap.order event.inputOwners before.bindings)
    let scope ← RuntimeCallInterval.read block position.start position.count (inputs.val.map (·.port.token))
    let initial ← NaturalAffine.witness (RuntimeSourceBoundary.bindings
      (occurrence.call.callee.checked.summary.parameterValues.flatMap valueOwners)
      ((scope.selected.zip event.inputOwners).map fun (port,role) =>
        (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)))
    return ⟨interval,callerFrame.val,callerFrame.property,completeFrame,inputs.val,
      by with_reducible exact inputs.property,scope,initial.val,by with_reducible exact initial.property⟩
  else throw .request

structure Checked {artifact owner name arguments source request}
    (occurrence : @RuntimeNamedSelectionOccurrence.Prepared artifact owner name arguments source request)
    (root : Validity.Root) {program : Semantics.Observation.Program}
    (block : RuntimeInterval.Block root.dependencies program) (before : SourceState) where
  supplies : RuntimeNamedSelectionPrefix.Checked occurrence.call.supplies root
  suppliesRead : RuntimeInterval.Computed (RuntimeNamedSelectionPrefix.read occurrence.call.supplies root) supplies
  frame : Frame occurrence root block before
  frameRead : RuntimeInterval.Computed (prepare occurrence root block before) frame
  child : RuntimeSelectionMeaning.LocalChecked occurrence.call.selection root frame.scope.prepared frame.initial
  childRead : RuntimeInterval.Computed
    (RuntimeSelectionMeaning.readAt occurrence.call.selection root frame.scope.prepared frame.initial) child
  boundary : RuntimeNamedBoundary.Checked frame.scope.interval (frame.inputs.map (·.port.token))
    occurrence.parts.event before child.history child.retired child.value
  boundaryRead : RuntimeInterval.Computed (RuntimeNamedBoundary.read frame.scope.interval
    (frame.inputs.map (·.port.token)) occurrence.parts.event before child.history child.retired child.value) boundary

/-- Consume every original header actual and arm under this same final root,
then use the original named boundary for exact canonical-to-caller transport.
The enclosing source fold still owns its cursor, earlier/later actions and
complete typed final return. -/
def read {artifact owner name arguments source request}
    (occurrence : @RuntimeNamedSelectionOccurrence.Prepared artifact owner name arguments source request)
    (root : Validity.Root) {program : Semantics.Observation.Program}
    (block : RuntimeInterval.Block root.dependencies program) (before : SourceState) :
    WorkM (Checked occurrence root block before) := do
  let supplies ← NaturalAffine.witness (RuntimeNamedSelectionPrefix.read occurrence.call.supplies root)
  let frame ← NaturalAffine.witness (prepare occurrence root block before)
  let child ← NaturalAffine.witness
    (RuntimeSelectionMeaning.readAt occurrence.call.selection root frame.val.scope.prepared frame.val.initial)
  let boundary ← NaturalAffine.witness (RuntimeNamedBoundary.read frame.val.scope.interval
    (frame.val.inputs.map (·.port.token)) occurrence.parts.event before child.val.history child.val.retired child.val.value)
  return ⟨supplies.val,by with_reducible exact supplies.property,frame.val,by with_reducible exact frame.property,
    child.val,by with_reducible exact child.property,boundary.val,by with_reducible exact boundary.property⟩

def Checked.node {artifact owner name arguments source request occurrence root program block before}
    (checked : @Checked artifact owner name arguments source request occurrence root program block before) :
    RuntimePureBody.Node root.dependencies program block :=
  .named occurrence.parts.event checked.frame.scope occurrence.call.callee occurrence.call.calleeRead
    checked.frame.scope.prepared.block checked.boundary (RuntimePureBody.Nodes.ofList [checked.child.node])

end QleisliKernel.Qirf.RuntimeNamedSelectionLocal
