import QleisliKernel.Qirf.RuntimeNamedBoundary
import QleisliKernel.Qirf.RuntimeSourceBoundary
import QleisliKernel.Qirf.SourceSequence

/-! A literal pure call frame for one actual original named event/body.
The source traversal owns event membership, caller order and the callee read.
Every call uses its current full frame; only original arguments seed the
canonical local namespace. This component checks no callee operation meaning.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNamedCallFrame
open QleisliKernel Finite SourceTypes
open QleisliKernel.SourceTypes.SourceRuntimeValues (valueOwners owners)
abbrev Map := RuntimeOwnerMap.Map
abbrev SourceState := RuntimeStructuralAction.SourceState
abbrev Position := SourceSequence.Position

structure Checked {sources caller dependencies program}
    (event : SourceRuntimeContext.NamedEvent sources caller)
    (callee : SourceRuntimeTrace.Body event.target.signature)
    (block : RuntimeInterval.Block dependencies program) (position : Position) (before : SourceState) where
  interval : RuntimeInterval.Checked block position.start position.count
  callerFrame : RuntimeOwnerMap.Checked (before.bindings.map (·.owner)) interval.before
  sameCaller : callerFrame.bindings = before.bindings
  completeFrame : (event.held ++ event.inputOwners ++ owners event.remaining).Perm (before.bindings.map (·.owner))
  inputs : Map
  inputRead : RuntimeInterval.Computed (RuntimeOwnerMap.order event.inputOwners before.bindings) inputs
  scope : RuntimeCallInterval.Checked block position.start position.count (inputs.map (·.port.token))
  sameInterval : scope.interval = interval
  initial : Map
  initialRead : RuntimeInterval.Computed (RuntimeSourceBoundary.bindings
    (callee.checked.summary.parameterValues.flatMap valueOwners)
    ((scope.selected.zip event.inputOwners).map fun (port,role) =>
      (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner))) initial

def read {sources caller dependencies program}
    (event : SourceRuntimeContext.NamedEvent sources caller)
    (callee : SourceRuntimeTrace.Body event.target.signature)
    (block : RuntimeInterval.Block dependencies program) (position : Position) (before : SourceState) :
    WorkM (Checked event callee block position before) := do
  let roles := event.held ++ event.inputOwners ++ owners event.remaining
  exactWork (Exact.charge (16+64*(Raw.OwnerFlow.fields roles+Raw.OwnerFlow.fields
    (before.bindings.map (·.owner))+1)*(roles.length+before.bindings.length+1)^2))
  guard (position.offset == event.call.calleeOffset && event.effect == .unitary) .request
  let interval ← RuntimeInterval.check block position.start position.count
  let callerFrame ← RuntimeOwnerMap.checkBindings (before.bindings.map (·.owner)) interval.before before.bindings
  if completeFrame : roles.Perm (before.bindings.map (·.owner)) then
    let inputs ← NaturalAffine.witness (RuntimeOwnerMap.order event.inputOwners before.bindings)
    let scope ← RuntimeCallInterval.readWithInterval interval (inputs.val.map (·.port.token))
    let initial ← NaturalAffine.witness (RuntimeSourceBoundary.bindings
      (callee.checked.summary.parameterValues.flatMap valueOwners)
      ((scope.val.selected.zip event.inputOwners).map fun (port,role) =>
        (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)))
    return ⟨interval,callerFrame.val,callerFrame.property,completeFrame,inputs.val,
      by with_reducible exact inputs.property,scope.val,scope.property,initial.val,by with_reducible exact initial.property⟩
  else throw .request

end QleisliKernel.Qirf.RuntimeNamedCallFrame
