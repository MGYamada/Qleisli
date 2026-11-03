import QleisliKernel.Qirf.RuntimePrimitiveAction
import QleisliKernel.Qirf.RuntimeStructuralAction
import QleisliKernel.Qirf.SourceSequence
import QleisliKernel.SourceTypes.SourceRuntimeTrace

/-! A transparent static source selection in the same literal runtime block.
Selected primitives or one named call with closed Basis/Nat actuals use the
common event step.
The mixed continuation separately retains a destructive observing call's exact
source delta; the pure continuation still requires unchanged ownership.
The exact original
guard and both source arms remain in StaticEvent.generic; this component
neither grants inactive duties nor invents a runtime condition, phi or child
context. Source allocation and other selected bodies refuse this bounded
continuation. Native root, final storage/history and all pending
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

private structure OriginalSelection {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) where
  selected : SourceRuntimeTrace.StaticBody event
  original : RuntimeInterval.Computed (SourceRuntimeTrace.readStaticSource event) selected

/-- Both continuation modes authenticate the same original selected body using
the existing evaluator. Neither mode supplies a replacement source summary. -/
private def readOriginalSelection {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) :
    WorkM (OriginalSelection event) := do
  let selected ← NaturalAffine.witness (SourceRuntimeTrace.readStaticSource event)
  exactWork (Exact.charge (32*(selected.val.result.events.length+
    Raw.OwnerFlow.fields (selected.val.result.allocated ++ selected.val.result.consumed)+1)))
  return ⟨selected.val,by with_reducible exact selected.property⟩

private structure Selected {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) where
  selected : SourceRuntimeTrace.StaticBody event
  original : RuntimeInterval.Computed (SourceRuntimeTrace.readStaticSource event) selected
  unchanged : selected.result.allocated = [] ∧ selected.result.consumed = [] ∧
    selected.result.nextOrdinal = event.nextOrdinal

private def readSelected {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) :
    WorkM (Selected event) := do
  let selected ← readOriginalSelection event
  if unchanged : selected.selected.result.allocated = [] ∧ selected.selected.result.consumed = [] ∧
      selected.selected.result.nextOrdinal = event.nextOrdinal then
    return ⟨selected.selected,selected.original,unchanged⟩
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

def basisNatFormals (formals : List StaticHeaders.Formal) : Bool :=
  formals.all fun formal => match formal.kind with
    | .basis | .natural => true
    | .operation _ => false

/-- The exact original application already retains ordered actuals and their
original premise transfer. Its same selected signature retains checked Basis
values and closed Nat premises. These additional proofs bound this continuation
to Basis/Nat formals; they neither reconstruct those receipts nor grant an
operation actual, body equation, public effect or native capability. -/
structure BasisNatActuals {sources caller} (call : SourceRuntimeContext.NamedEvent sources caller) : Type where
  applicationKinds : basisNatFormals call.target.actuals.target.header.formals = true
  signatureKinds : basisNatFormals call.target.signature.checked.environment.numeric.original.header.formals = true
  noOperations : call.target.signature.arguments.operations = []

private def readBasisNatActuals {sources caller} (call : SourceRuntimeContext.NamedEvent sources caller) :
    WorkM (BasisNatActuals call) := do
  -- Only the two retained formal-kind lists and the operation-list constructor
  -- are examined here. All actual parsing/substitution/body checks remain with
  -- their original readers, independently for this occurrence.
  exactWork (Exact.charge (16*(call.target.actuals.target.header.formals.length+
    call.target.signature.checked.environment.numeric.original.header.formals.length+1)))
  if checked : basisNatFormals call.target.actuals.target.header.formals = true ∧
      basisNatFormals call.target.signature.checked.environment.numeric.original.header.formals = true ∧
      call.target.signature.arguments.operations = [] then
    return ⟨checked.1,checked.2.1,checked.2.2⟩
  else throw .request

/-- Compound primitives and one original named call use the same common event
handler. Closed Basis/Nat instances retain their original application receipts;
general operation actuals and compound call partitions remain separate. -/
inductive EligibleEvents {sources caller} (events : List (SourceRuntimeContext.Event sources caller)) : Type where
  | primitives (actions : List Action) (classified : events.mapM classifyEvent = .ok actions)
  | named (call : SourceRuntimeContext.NamedEvent sources caller)
      (single : events = [.named call]) (nongeneric : call.target.signature.staticNames.isEmpty = true)
  | basisNat (call : SourceRuntimeContext.NamedEvent sources caller)
      (single : events = [.named call]) (actuals : BasisNatActuals call)

/-- These are the genuine selected source events. No synthetic body or
signature is made, and each event is later run by the existing common step. -/
structure Sequence {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) where
  selected : SourceRuntimeTrace.StaticBody event
  original : RuntimeInterval.Computed (SourceRuntimeTrace.readStaticSource event) selected
  eligible : EligibleEvents selected.result.events
  unchanged : selected.result.allocated = [] ∧ selected.result.consumed = [] ∧
    selected.result.nextOrdinal = event.nextOrdinal

private def sequenceWithSelected {sources caller event} (selected : @Selected sources caller event) :
    WorkM (Sequence event) := do
  exactWork (Exact.charge (8*(selected.selected.result.events.length+1)))
  match single : selected.selected.result.events with
  | [.named call] =>
    let names := call.target.signature.staticNames
    exactWork (Exact.charge (16*((names.map fun name => name.utf8ByteSize+1).sum+names.length+1)))
    if nongeneric : call.target.signature.staticNames.isEmpty = true then
      return ⟨selected.selected,selected.original,
        .named call (by first | exact single | rfl) nongeneric,selected.unchanged⟩
    else
      let actuals ← readBasisNatActuals call
      return ⟨selected.selected,selected.original,
        .basisNat call (by first | exact single | rfl) actuals,selected.unchanged⟩
  | _ =>
    match classified : selected.selected.result.events.mapM classifyEvent with
    | .error _ => throw .request
    | .ok actions => return ⟨selected.selected,selected.original,
        .primitives actions (by first | exact classified | rfl),selected.unchanged⟩

def readSequence {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) :
    WorkM (Sequence event) := do
  sequenceWithSelected (← readSelected event)

/-- The bounded mixed path permits one original observing call, without fresh
owners. Its complete consumed-role list must be the selected source result's
own list, before the common named step checks the actual child history. -/
structure Observing {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) where
  selected : SourceRuntimeTrace.StaticBody event
  original : RuntimeInterval.Computed (SourceRuntimeTrace.readStaticSource event) selected
  call : SourceRuntimeContext.NamedEvent sources caller
  single : selected.result.events = [.named call]
  nongeneric : call.target.signature.staticNames.isEmpty = true
  effect : call.effect = .observe
  allocated : selected.result.allocated = []
  callAllocated : call.allocated = []
  consumed : selected.result.consumed = call.consumed
  ordinal : selected.result.nextOrdinal = event.nextOrdinal

inductive Continuation {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) where
  | unchanged (source : Sequence event)
  | observing (source : Observing event)

def Continuation.selected {sources caller event} : @Continuation sources caller event → SourceRuntimeTrace.StaticBody event
  | .unchanged source => source.selected
  | .observing source => source.selected

def Continuation.original {sources caller event} (source : @Continuation sources caller event) :
    RuntimeInterval.Computed (SourceRuntimeTrace.readStaticSource event) source.selected :=
  match source with
  | .unchanged source => source.original
  | .observing source => source.original

/-- Used only by discovery and Mode.runtimeBody. Pure checking uses readSequence
and retains its previous no-consumption contract. No failed read is retried. -/
def readContinuation {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) :
    WorkM (Continuation event) := do
  let selected ← readOriginalSelection event
  if unchanged : selected.selected.result.allocated = [] ∧ selected.selected.result.consumed = [] ∧
      selected.selected.result.nextOrdinal = event.nextOrdinal then
    return .unchanged (← sequenceWithSelected ⟨selected.selected,selected.original,unchanged⟩)
  else
    match single : selected.selected.result.events with
    | [.named call] =>
      let names := call.target.signature.staticNames
      exactWork (Exact.charge (32*((names.map fun name => name.utf8ByteSize+1).sum+names.length+
        caller.utf8ByteSize+call.target.resolution.moduleName.utf8ByteSize+
        Raw.OwnerFlow.fields (selected.selected.result.allocated ++ selected.selected.result.consumed ++
          call.allocated ++ call.consumed)+selected.selected.result.nextOrdinal+event.nextOrdinal+1)))
      if checked : call.target.signature.staticNames.isEmpty = true ∧ call.effect = .observe ∧
          selected.selected.result.allocated = [] ∧ call.allocated = [] ∧
          selected.selected.result.consumed = call.consumed ∧
          selected.selected.result.nextOrdinal = event.nextOrdinal then
        return .observing ⟨selected.selected,selected.original,call,(by first | exact single | rfl),
          checked.1,checked.2.1,checked.2.2.1,checked.2.2.2.1,checked.2.2.2.2.1,checked.2.2.2.2.2⟩
      else throw .request
    | _ => throw .request

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

def Continuation.sourceRows {sources caller event} (source : @Continuation sources caller event) : List (String × String) :=
  selectedRows event source.selected

/-- Existing zero/single-event intervals keep their original behavior. For
compound primitives this first eligible decomposition has one literal Raw
instruction per event; each slice still needs the independent local equation.
There is no new count maximum and no claim about other equivalent decompositions. -/
private def selectedPositions {sources caller} (events : List (SourceRuntimeContext.Event sources caller))
    (parent : SourceSequence.Position) : WorkM (List SourceSequence.Position) := do
  exactWork (Exact.charge (16*(events.length+1)))
  match events with
  | [] =>
    guard (parent.count == 0) .request
    return []
  | [event] => return [⟨event.offset,parent.start,parent.count⟩]
  | _ =>
    guard (parent.count == events.length) .request
    return events.zipIdx.map fun (event,index) => ⟨event.offset,parent.start+index,1⟩

def Sequence.positions {sources caller event} (sequence : @Sequence sources caller event)
    (parent : SourceSequence.Position) : WorkM (List SourceSequence.Position) :=
  selectedPositions sequence.selected.result.events parent

def Continuation.positions {sources caller event} (source : @Continuation sources caller event)
    (parent : SourceSequence.Position) : WorkM (List SourceSequence.Position) :=
  selectedPositions source.selected.result.events parent

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

structure ContinuationBefore {sources caller dependencies program block start count event}
    (source : @Continuation sources caller event)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before : RuntimeStructuralAction.SourceState) where
  ordinal : before.nextOrdinal = event.nextOrdinal
  frame : Frame (event.held ++ owners event.before) interval.before before.bindings

def readContinuationBefore {sources caller dependencies program block start count event}
    (source : @Continuation sources caller event)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before : RuntimeStructuralAction.SourceState) : WorkM (ContinuationBefore source interval before) := do
  if ordinal : before.nextOrdinal = event.nextOrdinal then
    return ⟨ordinal,← readFrame (event.held ++ owners event.before) interval.before before.bindings⟩
  else throw .request

/-- The mixed exit uses the exact selected source deltas. Issued and retired
identities include every consumed owner; no live-frame comparison can erase
that history. The ordinary SSA result remains the actual common step's state. -/
structure ContinuationAfter {sources caller dependencies program block start count event}
    (source : @Continuation sources caller event)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before after : RuntimeStructuralAction.SourceState) (beforeRetired afterRetired : List Owner) where
  ordinal : after.nextOrdinal = source.selected.result.nextOrdinal
  issued : after.issued = before.issued ++ source.selected.result.allocated
  retired : afterRetired = beforeRetired ++ source.selected.result.consumed
  frame : Frame (event.held ++ valueOwners source.selected.result.value ++ owners source.selected.result.remaining)
    interval.after after.bindings

def readContinuationAfter {sources caller dependencies program block start count event}
    (source : @Continuation sources caller event)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before after : RuntimeStructuralAction.SourceState) (beforeRetired afterRetired : List Owner) :
    WorkM (ContinuationAfter source interval before after beforeRetired afterRetired) := do
  exactWork (Exact.charge (32*(Raw.OwnerFlow.fields (before.issued ++ after.issued ++
    source.selected.result.allocated ++ beforeRetired ++ afterRetired ++ source.selected.result.consumed)+
    after.nextOrdinal+source.selected.result.nextOrdinal+1)))
  if history : after.nextOrdinal = source.selected.result.nextOrdinal ∧
      after.issued = before.issued ++ source.selected.result.allocated ∧
      afterRetired = beforeRetired ++ source.selected.result.consumed then
    let frame ← readFrame (event.held ++ valueOwners source.selected.result.value ++ owners source.selected.result.remaining)
      interval.after after.bindings
    return ⟨history.1,history.2.1,history.2.2,frame⟩
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
