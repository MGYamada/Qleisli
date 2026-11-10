import QleisliKernel.Qirf.RuntimeOwnerTransition
import QleisliKernel.Qirf.RuntimePureInterval
import QleisliKernel.Qirf.RuntimeStructuralAction

/-! Source owner transport for a literal pure transform. The Raw traversal
retains its original ordered ports; the written source creates its own output
identities. A returned physical wire or equal width cannot choose those
identities. The transform's operator and access are checked separately.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeTransformOwners
open Finite SourceTypes
open SourceRuntimeValues (valueOwners owners)
open RuntimeOwnerMap (Map)
abbrev SourceState := RuntimeStructuralAction.SourceState

def inputs {sources caller} (event : SourceRuntimeContext.TransformEvent sources caller) :=
  event.arguments.flatMap valueOwners

def outputs {sources caller} (event : SourceRuntimeContext.TransformEvent sources caller) :=
  valueOwners event.value

def assigned {sources caller} (event : SourceRuntimeContext.TransformEvent sources caller)
    (returned : Map) : Map :=
  ((outputs event).zip returned).map fun (owner,binding) => ⟨owner,binding.port⟩

structure Checked {dependencies program block start count sources caller}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (event : SourceRuntimeContext.TransformEvent sources caller) (before : SourceState) where
  inputFrame : RuntimeOwnerMap.Checked (before.bindings.map (·.owner)) interval.before
  sameInput : inputFrame.bindings = before.bindings
  complete : (event.held ++ inputs event ++ owners event.remaining).Perm (before.bindings.map (·.owner))
  issued : before.issued.map (·.ordinal) = List.range before.nextOrdinal
  liveIssued : before.bindings.all (fun binding => before.issued.contains binding.owner) = true
  entryOrdinal : event.nextOrdinal = before.nextOrdinal
  fresh : event.allocated.map (·.ordinal) = (List.range event.allocated.length).map (before.nextOrdinal+·)
  exitOrdinal : event.afterOrdinal = before.nextOrdinal+event.allocated.length
  native : RuntimeOwnerTransition.Checked interval before.bindings
  nativeRead : RuntimeInterval.Computed (RuntimeOwnerTransition.read interval before.bindings) native
  selected : Map
  returned : Map
  selectedRead : RuntimeInterval.Computed (RuntimeOwnerMap.order (inputs event) before.bindings) selected
  returnedRead : RuntimeInterval.Computed (RuntimeOwnerMap.order (inputs event) native.after.bindings) returned
  literal : RuntimePureInterval.Checked block (inputs event).length start count
    (selected.map (·.port.token)) (returned.map (·.port.token)) (inputs event)
  sameInterval : literal.interval = interval
  selectedPorts : literal.selected = selected.map (·.port)
  returnedPorts : literal.returned = returned.map (·.port)
  inputWidths : RuntimeStructuralAction.widths literal.selected (inputs event) = true
  outputWidths : RuntimeStructuralAction.widths literal.returned (outputs event) = true
  afterFrame : RuntimeOwnerMap.Checked (event.held ++ outputs event ++ owners event.remaining) interval.after
  afterRead : RuntimeInterval.Computed (do
    let kept := native.after.bindings.filter (fun binding => !(inputs event).contains binding.owner)
    let mapped ← RuntimeOwnerMap.order (event.held ++ outputs event ++ owners event.remaining)
      (kept ++ assigned event returned)
    RuntimeOwnerMap.check (event.held ++ outputs event ++ owners event.remaining) interval.after mapped) afterFrame

def Checked.after {dependencies program block start count sources caller interval event before}
    (checked : @Checked dependencies program block start count sources caller interval event before) : SourceState :=
  ⟨checked.afterFrame.bindings,before.issued ++ event.allocated,event.afterOrdinal⟩

def read {dependencies program block start count sources caller}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (event : SourceRuntimeContext.TransformEvent sources caller) (before : SourceState) :
    WorkM (Checked interval event before) := do
  let roles := event.held ++ inputs event ++ owners event.remaining
  let candidates := before.bindings.map (·.owner)
  let visits := roles.length+candidates.length+before.issued.length+event.allocated.length+before.nextOrdinal+1
  exactWork (Exact.charge (16*(Raw.OwnerFlow.fields
    (roles ++ candidates ++ before.issued ++ event.allocated ++ outputs event)+1)*visits+64*visits^2))
  let inputFrame ← RuntimeOwnerMap.checkBindings candidates interval.before before.bindings
  if complete : roles.Perm candidates then
    if history : before.issued.map (·.ordinal) = List.range before.nextOrdinal ∧
        before.bindings.all (fun binding => before.issued.contains binding.owner) = true ∧
        event.nextOrdinal = before.nextOrdinal ∧
        event.allocated.map (·.ordinal) = (List.range event.allocated.length).map (before.nextOrdinal+·) ∧
        event.afterOrdinal = before.nextOrdinal+event.allocated.length then
      let native ← NaturalAffine.witness (RuntimeOwnerTransition.read interval before.bindings)
      let selected ← NaturalAffine.witness (RuntimeOwnerMap.order (inputs event) before.bindings)
      let returned ← NaturalAffine.witness (RuntimeOwnerMap.order (inputs event) native.val.after.bindings)
      let literal ← RuntimePureInterval.checkAt interval (inputs event).length
        (selected.val.map (·.port.token)) (returned.val.map (·.port.token)) (inputs event)
      if ports : literal.val.selected = selected.val.map (·.port) ∧
          literal.val.returned = returned.val.map (·.port) ∧
          RuntimeStructuralAction.widths literal.val.selected (inputs event) = true ∧
          RuntimeStructuralAction.widths literal.val.returned (outputs event) = true then
        let after ← NaturalAffine.witness (do
          let kept := native.val.after.bindings.filter (fun binding => !(inputs event).contains binding.owner)
          let mapped ← RuntimeOwnerMap.order (event.held ++ outputs event ++ owners event.remaining)
            (kept ++ assigned event returned.val)
          RuntimeOwnerMap.check (event.held ++ outputs event ++ owners event.remaining) interval.after mapped)
        return ⟨inputFrame.val,inputFrame.property,complete,history.1,history.2.1,history.2.2.1,
          history.2.2.2.1,history.2.2.2.2,native.val,by with_reducible exact native.property,
          selected.val,returned.val,by with_reducible exact selected.property,
          by with_reducible exact returned.property,literal.val,literal.property,ports.1,ports.2.1,
          ports.2.2.1,ports.2.2.2,after.val,by with_reducible exact after.property⟩
      else throw .request
    else throw .request
  else throw .request

end QleisliKernel.Qirf.RuntimeTransformOwners
