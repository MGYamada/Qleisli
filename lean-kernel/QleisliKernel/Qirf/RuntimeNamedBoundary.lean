import QleisliKernel.Qirf.RuntimeCallInterval
import QleisliKernel.Qirf.RuntimeStructuralAction

/-! Exact original named-call owner transport after recursive body checking.
Canonical callee owners are mapped only by the original call's complete typed
owner map. Every issued and retired owner is retained, including intermediate
aliases that do not survive the call. The literal local scope and full caller
frame remain separate; this boundary supplies no body or operator acceptance.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNamedBoundary
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open SourceRuntimeValues (valueOwners mappedOwner transport ordinary)
open RuntimeOwnerMap (Owner Map)
abbrev SourceState := RuntimeStructuralAction.SourceState

structure Checked {dependencies program sources caller block start count inputs}
    (frame : @RuntimeCallInterval.Checked dependencies program block start count inputs)
    (event : SourceRuntimeContext.NamedEvent sources caller) (before child : SourceState)
    (childRetired : List Owner) (childValue : SourceRuntimeValues.Value) where
  issued : before.issued.map (·.ordinal) = List.range before.nextOrdinal
  liveIssued : before.bindings.all (fun binding => before.issued.contains binding.owner) = true
  fresh : event.allocated.map (·.ordinal) = (List.range event.allocated.length).map (before.nextOrdinal+·)
  completeHistory : child.issued.mapM (mappedOwner event.ownerMap) = .ok event.ownerMap
  completeRetired : childRetired.mapM (mappedOwner event.ownerMap) = .ok event.consumed
  result : transport ⟨caller,event.target.callerName,event.call.calleeOffset⟩ event.ownerMap
    (event.arguments.flatMap ordinary) childValue = .ok event.value
  mapped : Map
  mappedRead : child.bindings.mapM (fun binding => do
    let owner ← mappedOwner event.ownerMap binding.owner
    pure (⟨owner,binding.port⟩ : RuntimeOwnerMap.Binding)) = .ok mapped
  resultOwners : mapped.map (·.owner) = valueOwners event.value
  returned : List Semantics.Raw.Port
  returnRead : returned = mapped.map (·.port)
  atExit : PureInterval.ports frame.interval.after (returned.map (·.token)) = some returned
  spectators : PureInterval.spectators frame.interval.before inputs =
    PureInterval.spectators frame.interval.after (returned.map (·.token))
  after : SourceState
  afterBindings : after.bindings = before.bindings.filter (fun binding => !event.inputOwners.contains binding.owner) ++ mapped
  afterIssued : after.issued = before.issued ++ event.allocated
  afterOrdinal : after.nextOrdinal = before.nextOrdinal+event.allocated.length
  afterFrame : RuntimeOwnerMap.Checked (after.bindings.map (·.owner)) frame.interval.after

def read {dependencies program sources caller block start count inputs}
    (frame : @RuntimeCallInterval.Checked dependencies program block start count inputs)
    (event : SourceRuntimeContext.NamedEvent sources caller) (before child : SourceState)
    (childRetired : List Owner) (childValue : SourceRuntimeValues.Value) :
    WorkM (Checked frame event before child childRetired childValue) := do
  exactWork (Exact.charge (64*(Raw.OwnerFlow.fields (before.issued ++ event.ownerMap ++ child.issued ++ childRetired)+
    SourceRuntimeValues.valueFields childValue+SourceRuntimeValues.valueFields event.value+
    before.bindings.length+child.bindings.length+before.nextOrdinal+1)^2))
  if issued : before.issued.map (·.ordinal) = List.range before.nextOrdinal then
    if liveIssued : before.bindings.all (fun binding => before.issued.contains binding.owner) = true then
      if fresh : event.allocated.map (·.ordinal) = (List.range event.allocated.length).map (before.nextOrdinal+·) then
        if completeHistory : child.issued.mapM (mappedOwner event.ownerMap) = .ok event.ownerMap then
          if completeRetired : childRetired.mapM (mappedOwner event.ownerMap) = .ok event.consumed then
            if result : transport ⟨caller,event.target.callerName,event.call.calleeOffset⟩ event.ownerMap
                (event.arguments.flatMap ordinary) childValue = .ok event.value then
              match mappedRead : child.bindings.mapM (fun binding => do
                  let owner ← mappedOwner event.ownerMap binding.owner
                  pure (⟨owner,binding.port⟩ : RuntimeOwnerMap.Binding)) with
              | .error _ => throw .request
              | .ok mapped =>
                if resultOwners : mapped.map (·.owner) = valueOwners event.value then
                  let returned := mapped.map (·.port)
                  if atExit : PureInterval.ports frame.interval.after (returned.map (·.token)) = some returned then
                    if spectators : PureInterval.spectators frame.interval.before inputs =
                        PureInterval.spectators frame.interval.after (returned.map (·.token)) then
                      let bindings := before.bindings.filter (fun binding => !event.inputOwners.contains binding.owner) ++ mapped
                      let after : SourceState := ⟨bindings,before.issued ++ event.allocated,
                        before.nextOrdinal+event.allocated.length⟩
                      let afterFrame ← RuntimeOwnerMap.check (after.bindings.map (·.owner)) frame.interval.after after.bindings
                      return ⟨issued,liveIssued,fresh,completeHistory,completeRetired,result,mapped,mappedRead,
                        resultOwners,returned,rfl,atExit,spectators,after,rfl,rfl,rfl,afterFrame⟩
                    else throw .request
                  else throw .request
                else throw .request
            else throw .request
          else throw .request
        else throw .request
      else throw .request
    else throw .request
  else throw .request

end QleisliKernel.Qirf.RuntimeNamedBoundary
