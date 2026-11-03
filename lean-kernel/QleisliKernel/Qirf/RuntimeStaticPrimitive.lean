import QleisliKernel.Qirf.RuntimePrimitiveAction
import QleisliKernel.Qirf.RuntimeStructuralAction
import QleisliKernel.Qirf.SourceSequence
import QleisliKernel.SourceTypes.SourceRuntimeTrace

/-! A transparent static source selection in the same literal runtime block.
Selected primitive sequences use the one common event step. The exact original
guard and both source arms remain in StaticEvent.generic; this component
neither grants inactive duties nor invents a runtime condition, phi or child
context. Source allocation/retirement and nonprimitive selected bodies refuse this
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

def classifyEvent {sources caller} : SourceRuntimeContext.Event sources caller → Except String Action
  | .phase event => .ok (.primitive event.operand (.phase event.application.coefficient.exponent))
  | .primitive event => do
    let [[.owner operand]] := event.arguments | throw "static primitive argument"
    match event.kind with
    | .h => pure (.primitive operand .h)
    | .globalPhaseEighth => pure (.primitive operand .globalPhaseEighth)
    | _ => throw "static primitive continuation is not connected"
  | _ => .error "nonprimitive static continuation is not connected"

def classify {sources caller} : List (SourceRuntimeContext.Event sources caller) → Except String Action
  | [] => .ok .identity
  | [event] => classifyEvent event
  | _ => .error "compound static continuation uses the common event step"

private structure Selected {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) where
  selected : SourceRuntimeTrace.StaticBody event
  original : RuntimeInterval.Computed (SourceRuntimeTrace.readStaticSource event) selected
  unchanged : selected.result.allocated = [] ∧ selected.result.consumed = [] ∧
    selected.result.nextOrdinal = event.nextOrdinal

private def readSelected {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) :
    WorkM (Selected event) := do
  let selected ← NaturalAffine.witness (SourceRuntimeTrace.readStaticSource event)
  exactWork (Exact.charge (32*(selected.val.result.events.length+
    Raw.OwnerFlow.fields (selected.val.result.allocated ++ selected.val.result.consumed)+1)))
  if unchanged : selected.val.result.allocated = [] ∧ selected.val.result.consumed = [] ∧
      selected.val.result.nextOrdinal = event.nextOrdinal then
    return ⟨selected.val,by with_reducible exact selected.property,unchanged⟩
  else throw .request

structure Source {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) where
  selected : SourceRuntimeTrace.StaticBody event
  original : RuntimeInterval.Computed (SourceRuntimeTrace.readStaticSource event) selected
  action : Action
  classified : classify selected.result.events = .ok action
  unchanged : selected.result.allocated = [] ∧ selected.result.consumed = [] ∧
    selected.result.nextOrdinal = event.nextOrdinal

def readSource {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) :
    WorkM (Source event) := do
  let selected ← readSelected event
  match classified : classify selected.selected.result.events with
  | .error _ => throw .request
  | .ok action => return ⟨selected.selected,selected.original,action,
      (by first | exact classified | rfl),selected.unchanged⟩

/-- These are the genuine selected source events. No synthetic body or
signature is made, and each event is later run by the existing common step. -/
structure Sequence {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) where
  selected : SourceRuntimeTrace.StaticBody event
  original : RuntimeInterval.Computed (SourceRuntimeTrace.readStaticSource event) selected
  actions : List Action
  classified : selected.result.events.mapM classifyEvent = .ok actions
  unchanged : selected.result.allocated = [] ∧ selected.result.consumed = [] ∧
    selected.result.nextOrdinal = event.nextOrdinal

def readSequence {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) :
    WorkM (Sequence event) := do
  let selected ← readSelected event
  exactWork (Exact.charge (8*(selected.selected.result.events.length+1)))
  match classified : selected.selected.result.events.mapM classifyEvent with
  | .error _ => throw .request
  | .ok actions => return ⟨selected.selected,selected.original,actions,
      (by first | exact classified | rfl),selected.unchanged⟩

private def selectedRows {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller)
    (selected : SourceRuntimeTrace.StaticBody event) : List (String × String) :=
  event.naturals.sourceRows ++ selected.result.staticRows ++
    selected.result.events.flatMap (fun event => match event with
      | .primitive event => CallName.sourceRows event.candidate
      | .phase event => CallName.sourceRows event.application.candidate ++ event.naturals.sourceRows
      | _ => [])

def Source.sourceRows {sources caller event} (source : @Source sources caller event) : List (String × String) :=
  selectedRows event source.selected

def Sequence.sourceRows {sources caller event} (source : @Sequence sources caller event) : List (String × String) :=
  selectedRows event source.selected

/-- Existing zero/single-event intervals keep their original behavior. For
compound primitives this first eligible decomposition has one literal Raw
instruction per event; each slice still needs the independent local equation.
There is no new count maximum and no claim about other equivalent decompositions. -/
def Sequence.positions {sources caller event} (sequence : @Sequence sources caller event)
    (parent : SourceSequence.Position) : WorkM (List SourceSequence.Position) := do
  let events := sequence.selected.result.events
  exactWork (Exact.charge (16*(events.length+1)))
  match events with
  | [] =>
    guard (parent.count == 0) .request
    return []
  | [event] => return [⟨event.offset,parent.start,parent.count⟩]
  | _ =>
    guard (parent.count == events.length) .request
    return events.zipIdx.map fun (event,index) => ⟨event.offset,parent.start+index,1⟩

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


structure Before {sources caller dependencies program block start count event}
    (sequence : @Sequence sources caller event)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before : RuntimeStructuralAction.SourceState) where
  ordinal : before.nextOrdinal = event.nextOrdinal
  frame : Frame (event.held ++ owners event.before) interval.before before.bindings

def readBefore {sources caller dependencies program block start count event}
    (sequence : @Sequence sources caller event)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before : RuntimeStructuralAction.SourceState) : WorkM (Before sequence interval before) := do
  if ordinal : before.nextOrdinal = event.nextOrdinal then
    return ⟨ordinal,← readFrame (event.held ++ owners event.before) interval.before before.bindings⟩
  else throw .request

structure After {sources caller dependencies program block start count event}
    (sequence : @Sequence sources caller event)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before after : RuntimeStructuralAction.SourceState) where
  ordinal : after.nextOrdinal = before.nextOrdinal
  issued : after.issued = before.issued
  frame : Frame (event.held ++ valueOwners sequence.selected.result.value ++ owners sequence.selected.result.remaining)
    interval.after after.bindings

def readAfter {sources caller dependencies program block start count event}
    (sequence : @Sequence sources caller event)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before after : RuntimeStructuralAction.SourceState) : WorkM (After sequence interval before after) := do
  exactWork (Exact.charge (16*(Raw.OwnerFlow.fields (before.issued ++ after.issued)+1)))
  if same : after.nextOrdinal = before.nextOrdinal ∧ after.issued = before.issued then
    let frame ← readFrame (event.held ++ valueOwners sequence.selected.result.value ++ owners sequence.selected.result.remaining)
      interval.after after.bindings
    return ⟨same.1,same.2,frame⟩
  else throw .request

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
