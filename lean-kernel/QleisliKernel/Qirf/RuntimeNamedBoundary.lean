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

private def exactResult {α : Type} [DecidableEq α] (action : Except String α) (expected : α) :
    WorkM (PLift (action = .ok expected)) := do
  match action with
  | .error _ => throw .request
  | .ok actual =>
    if same : actual = expected then return ⟨congrArg Except.ok same⟩
    else throw .request

structure Inputs {dependencies program sources caller block start count}
    (interval : @RuntimeInterval.Checked dependencies program block start count) (tokens : List Nat)
    (event : SourceRuntimeContext.NamedEvent sources caller) (before : SourceState) where
  ordered : Map
  orderRead : RuntimeInterval.Computed (RuntimeOwnerMap.order event.inputOwners before.bindings) ordered
  sameTokens : (ordered.map (·.port)).map (·.token) = tokens
  atEntry : PureInterval.ports interval.before tokens = some (ordered.map (·.port))

private def portFields (port : Semantics.Raw.Port) : Nat :=
  port.wires.foldl (fun total wire => total+wire.log2/8+1) (port.token.log2/8+port.bits.log2/8+3)

/-- Reuse the caller's original owner-order read and the scope's exact port
selection. Port equality includes tokens, ordered wires, and zero-width ports. -/
def bindInputs {dependencies program sources caller block start count}
    (interval : @RuntimeInterval.Checked dependencies program block start count) (tokens : List Nat)
    (event : SourceRuntimeContext.NamedEvent sources caller) (before : SourceState)
    (ordered : Map) (read : RuntimeInterval.Computed (RuntimeOwnerMap.order event.inputOwners before.bindings) ordered)
    (sameTokens : (ordered.map (·.port)).map (·.token) = tokens)
    (selected : List Semantics.Raw.Port) (found : PureInterval.ports interval.before tokens = some selected) :
    WorkM (Inputs interval tokens event before) := do
  exactWork (Exact.charge (16*(ordered.foldl (fun total b => total+portFields b.port) 0+
    selected.foldl (fun total p => total+portFields p) 0+1)))
  if same : selected = ordered.map (·.port) then
    return ⟨ordered,read,sameTokens,found.trans (congrArg some same)⟩
  else throw .request

structure Checked {dependencies program sources caller block start count}
    (interval : @RuntimeInterval.Checked dependencies program block start count) (inputs : List Nat)
    (event : SourceRuntimeContext.NamedEvent sources caller) (before child : SourceState)
    (childRetired : List Owner) (childValue : SourceRuntimeValues.Value) where
  input : Inputs interval inputs event before
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
  atExit : PureInterval.ports interval.after (returned.map (·.token)) = some returned
  spectators : PureInterval.spectators interval.before inputs =
    PureInterval.spectators interval.after (returned.map (·.token))
  after : SourceState
  afterBindings : after.bindings = before.bindings.filter (fun binding => !event.inputOwners.contains binding.owner) ++ mapped
  afterIssued : after.issued = before.issued ++ event.allocated
  afterOrdinal : after.nextOrdinal = before.nextOrdinal+event.allocated.length
  afterFrame : RuntimeOwnerMap.Checked (after.bindings.map (·.owner)) interval.after
  sameAfter : afterFrame.bindings = after.bindings

def readWithInputs {dependencies program sources caller block start count}
    (interval : @RuntimeInterval.Checked dependencies program block start count) (inputs : List Nat)
    (event : SourceRuntimeContext.NamedEvent sources caller) (before child : SourceState)
    (childRetired : List Owner) (childValue : SourceRuntimeValues.Value) (input : Inputs interval inputs event before) :
    WorkM (Checked interval inputs event before child childRetired childValue) := do
  exactWork (Exact.charge (64*(Raw.OwnerFlow.fields (before.issued ++ event.ownerMap ++ child.issued ++ childRetired)+
    SourceRuntimeValues.valueFields childValue+SourceRuntimeValues.valueFields event.value+
    before.bindings.length+child.bindings.length+before.nextOrdinal+1)^2))
  if issued : before.issued.map (·.ordinal) = List.range before.nextOrdinal then
    if liveIssued : before.bindings.all (fun binding => before.issued.contains binding.owner) = true then
      if fresh : event.allocated.map (·.ordinal) = (List.range event.allocated.length).map (before.nextOrdinal+·) then
        let completeHistory ← exactResult (child.issued.mapM (mappedOwner event.ownerMap)) event.ownerMap
        let completeRetired ← exactResult (childRetired.mapM (mappedOwner event.ownerMap)) event.consumed
        let result ← exactResult
          (transport ⟨caller,event.target.callerName,event.call.calleeOffset⟩ event.ownerMap
            (event.arguments.flatMap ordinary) childValue) event.value
        match mappedRead : child.bindings.mapM (fun binding => do
            let owner ← mappedOwner event.ownerMap binding.owner
            pure (⟨owner,binding.port⟩ : RuntimeOwnerMap.Binding)) with
        | .error _ => throw .request
        | .ok mapped =>
          if resultOwners : mapped.map (·.owner) = valueOwners event.value then
            let returned := mapped.map (·.port)
            if atExit : PureInterval.ports interval.after (returned.map (·.token)) = some returned then
              if spectators : PureInterval.spectators interval.before inputs =
                  PureInterval.spectators interval.after (returned.map (·.token)) then
                let bindings := before.bindings.filter (fun binding => !event.inputOwners.contains binding.owner) ++ mapped
                let after : SourceState := ⟨bindings,before.issued ++ event.allocated,
                  before.nextOrdinal+event.allocated.length⟩
                let afterFrame ← RuntimeOwnerMap.checkBindings (after.bindings.map (·.owner)) interval.after after.bindings
                return ⟨input,issued,liveIssued,fresh,completeHistory.down,completeRetired.down,result.down,mapped,mappedRead,
                  resultOwners,returned,rfl,atExit,spectators,after,rfl,rfl,rfl,afterFrame.val,afterFrame.property⟩
              else throw .request
            else throw .request
          else throw .request
      else throw .request
    else throw .request
  else throw .request

def read {dependencies program sources caller block start count}
    (interval : @RuntimeInterval.Checked dependencies program block start count) (inputs : List Nat)
    (event : SourceRuntimeContext.NamedEvent sources caller) (before child : SourceState)
    (childRetired : List Owner) (childValue : SourceRuntimeValues.Value) :
    WorkM (Checked interval inputs event before child childRetired childValue) := do
  let ordered ← NaturalAffine.witness (RuntimeOwnerMap.order event.inputOwners before.bindings)
  let liveKeys := interval.before.quantum.live.foldl (fun total p => total+p.token.log2/8+1) 0
  let inputKeys := inputs.foldl (fun total i => total+i.log2/8+1) 0
  exactWork (Exact.charge (16*((liveKeys+1)*(inputKeys+1)+ordered.val.length+1)))
  if same : (ordered.val.map (·.port)).map (·.token) = inputs then
    match found : PureInterval.ports interval.before inputs with
    | none => throw .request
    | some selected =>
      let input ← bindInputs interval inputs event before ordered.val
        (by with_reducible exact ordered.property) same selected found
      readWithInputs interval inputs event before child childRetired childValue input
  else throw .request

end QleisliKernel.Qirf.RuntimeNamedBoundary
