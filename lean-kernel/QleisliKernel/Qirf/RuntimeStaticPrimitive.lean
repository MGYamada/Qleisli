import QleisliKernel.Qirf.RuntimePrimitiveAction
import QleisliKernel.Qirf.RuntimeStructuralAction
import QleisliKernel.SourceTypes.SourceRuntimeTrace

/-! A transparent static source selection in the same literal runtime block.
Only identity or one existing primitive is connected here. The exact original
guard and both source arms remain in StaticEvent.generic; this component
neither grants inactive duties nor invents a runtime condition, phi or child
context. Source allocation/retirement and compound selected bodies refuse this
bounded continuation. Native root, final storage/history and all pending
provider/Meaning/path obligations remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeStaticPrimitive
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open SourceRuntimeValues
abbrev Owner := Semantics.SourceOwners.Owner
abbrev Kind := Semantics.PrimitiveOperator.Kind

inductive Action where
  | identity
  | primitive (role : Owner) (kind : Kind)

def classify {sources caller} : List (SourceRuntimeContext.Event sources caller) → Except String Action
  | [] => .ok .identity
  | [.phase event] => .ok (.primitive event.operand (.phase event.application.coefficient.exponent))
  | [.primitive event] => do
    let [[.owner operand]] := event.arguments | throw "static primitive argument"
    match event.kind with
    | .h => pure (.primitive operand .h)
    | .globalPhaseEighth => pure (.primitive operand .globalPhaseEighth)
    | _ => throw "static primitive continuation is not connected"
  | _ => .error "compound static continuation is not connected"

structure Source {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) where
  selected : SourceRuntimeTrace.StaticBody event
  original : RuntimeInterval.Computed (SourceRuntimeTrace.readStaticSource event) selected
  action : Action
  classified : classify selected.result.events = .ok action
  unchanged : selected.result.allocated = [] ∧ selected.result.consumed = [] ∧
    selected.result.nextOrdinal = event.nextOrdinal

def readSource {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) :
    WorkM (Source event) := do
  let selected ← NaturalAffine.witness (SourceRuntimeTrace.readStaticSource event)
  exactWork (Exact.charge (32*(selected.val.result.events.length+
    Raw.OwnerFlow.fields (selected.val.result.allocated ++ selected.val.result.consumed)+1)))
  if unchanged : selected.val.result.allocated = [] ∧ selected.val.result.consumed = [] ∧
      selected.val.result.nextOrdinal = event.nextOrdinal then
    match classified : classify selected.val.result.events with
    | .error _ => throw .request
    | .ok action => return ⟨selected.val,by with_reducible exact selected.property,action,
        (by first | exact classified | rfl),unchanged⟩
  else throw .request

def Source.sourceRows {sources caller event} (source : @Source sources caller event) : List (String × String) :=
  event.naturals.sourceRows ++ source.selected.result.staticRows ++
    source.selected.result.events.flatMap (fun event => match event with
      | .primitive event => CallName.sourceRows event.candidate
      | .phase event => CallName.sourceRows event.application.candidate ++ event.naturals.sourceRows
      | _ => [])

structure Frame (roles : List Owner) (state : Raw.Observation.State) (bindings : RuntimeOwnerMap.Map) where
  checked : RuntimeOwnerMap.Checked roles state
  same : checked.bindings.Perm bindings

private def readFrame (roles : List Owner) (state : Raw.Observation.State) (bindings : RuntimeOwnerMap.Map) :
    WorkM (Frame roles state bindings) := do
  exactWork (Exact.charge (32*(Raw.OwnerFlow.fields roles+
    Raw.OwnerFlow.fields (bindings.map (·.owner))+
    (bindings.map fun binding => binding.port.wires.length+3).sum+1)*(bindings.length+1)^2))
  let ordered ← RuntimeOwnerMap.order roles bindings
  let checked ← RuntimeOwnerMap.check roles state ordered
  if same : checked.bindings.Perm bindings then return ⟨checked,same⟩ else throw .request

inductive Bound {dependencies program} (block : RuntimeInterval.Block dependencies program)
    (start count : Nat) : Action → Type where
  | identity (empty : count = 0) : Bound block start count .identity
  | primitive {input output role kind}
      (checked : RuntimePrimitiveAction.Checked block start count input output role kind) :
      Bound block start count (.primitive role kind)

private def bindAction {dependencies program} (block : RuntimeInterval.Block dependencies program)
    (start count : Nat) (before after : RuntimeOwnerMap.Map) : (action : Action) → WorkM (Bound block start count action)
  | .identity => do
    if empty : count = 0 then return .identity empty else throw .request
  | .primitive role kind => do
    exactWork (Exact.charge (16*(Raw.OwnerFlow.fields [role]+1)*(before.length+after.length+1)))
    let some input := RuntimeOwnerMap.byOwner before role | throw .request
    let some output := RuntimeOwnerMap.byOwner after role | throw .request
    return .primitive (← RuntimePrimitiveAction.check block start count input.port.token output.port.token role kind)

structure Checked {sources caller dependencies program} (block : RuntimeInterval.Block dependencies program)
    (start count : Nat) (event : SourceRuntimeContext.StaticEvent sources caller)
    (before : RuntimeStructuralAction.SourceState) (after : RuntimeOwnerMap.Map) where
  source : Source event
  interval : RuntimeInterval.Checked block start count
  intervalRead : RuntimeInterval.Computed (RuntimeInterval.check block start count) interval
  ordinal : before.nextOrdinal = event.nextOrdinal
  beforeFrame : Frame (event.held ++ owners event.before) interval.before before.bindings
  afterFrame : Frame (event.held ++ valueOwners source.selected.result.value ++ owners source.selected.result.remaining)
    interval.after after
  action : Bound block start count source.action

def read {sources caller dependencies program} (block : RuntimeInterval.Block dependencies program)
    (start count : Nat) (event : SourceRuntimeContext.StaticEvent sources caller)
    (before : RuntimeStructuralAction.SourceState) (after : RuntimeOwnerMap.Map) :
    WorkM (Checked block start count event before after) := do
  let source ← readSource event
  let interval ← NaturalAffine.witness (RuntimeInterval.check block start count)
  if ordinal : before.nextOrdinal = event.nextOrdinal then
    let beforeFrame ← readFrame (event.held ++ owners event.before) interval.val.before before.bindings
    let afterFrame ← readFrame (event.held ++ valueOwners source.selected.result.value ++ owners source.selected.result.remaining)
      interval.val.after after
    let action ← bindAction block start count before.bindings after source.action
    return ⟨source,interval.val,by with_reducible exact interval.property,ordinal,beforeFrame,afterFrame,action⟩
  else throw .request

end QleisliKernel.Qirf.RuntimeStaticPrimitive
