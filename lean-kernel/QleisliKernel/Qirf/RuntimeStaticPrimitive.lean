import QleisliKernel.Qirf.RuntimePrimitiveAction
import QleisliKernel.Qirf.RuntimeStructuralAction
import QleisliKernel.Qirf.SourceSequence
import QleisliKernel.SourceTypes.SourceRuntimeTrace

/-! A transparent static source selection in the same literal runtime block.
Selected primitive and original named events with closed Basis/Nat actuals
use the same common event step in their original order. Mixed continuations
retain the complete selected source delta; pure continuations still require
unchanged ownership.
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

/-- Eligibility is indexed by the genuine selected event list. Composition
adds no source event, argument instance or semantic evaluator. Each named leaf
retains the same original actual receipts; operation actuals and other event
forms still require their own connection to the common step. -/
inductive EligibleEvents {sources caller} : List (SourceRuntimeContext.Event sources caller) → Type where
  | primitives {events : List (SourceRuntimeContext.Event sources caller)} (actions : List Action)
      (classified : events.mapM classifyEvent = .ok actions) :
      EligibleEvents events
  | primitive (event : SourceRuntimeContext.Event sources caller) (action : Action)
      (classified : classifyEvent event = .ok action) : EligibleEvents [event]
  | named {events : List (SourceRuntimeContext.Event sources caller)}
      (call : SourceRuntimeContext.NamedEvent sources caller)
      (single : events = [.named call]) (nongeneric : call.target.signature.staticNames.isEmpty = true) :
      EligibleEvents events
  | basisNat {events : List (SourceRuntimeContext.Event sources caller)}
      (call : SourceRuntimeContext.NamedEvent sources caller)
      (single : events = [.named call]) (actuals : BasisNatActuals call) : EligibleEvents events
  | selection (event : SourceRuntimeContext.Event sources caller)
      (written : event.qmatchOffset.isSome = true) : EligibleEvents [event]
  | cons {first : SourceRuntimeContext.Event sources caller} {rest : List (SourceRuntimeContext.Event sources caller)}
      (head : EligibleEvents [first]) (tail : EligibleEvents rest) :
      EligibleEvents (first :: rest)

/-- Reuse the same original named-argument eligibility in both continuation
modes. The actual application, closed signature and premise receipts stay on
this exact event; no alternate source reader or specialization is selected. -/
private def readNamedEligibility {sources caller} (call : SourceRuntimeContext.NamedEvent sources caller) :
    WorkM (EligibleEvents [.named call]) := do
  let names := call.target.signature.staticNames
  exactWork (Exact.charge (16*((names.map fun name => name.utf8ByteSize+1).sum+names.length+1)))
  if nongeneric : call.target.signature.staticNames.isEmpty = true then
    return .named call rfl nongeneric
  else
    return .basisNat call rfl (← readBasisNatActuals call)

private def readEventEligibility {sources caller} (coherent : Bool)
    (event : SourceRuntimeContext.Event sources caller) :
    WorkM (EligibleEvents [event]) := do
  match event with
  | .named call => readNamedEligibility call
  | .selection tokens parsed original selector target scope naturals held remaining =>
    if coherent then
      return .selection (.selection tokens parsed original selector target scope naturals held remaining) rfl
    else throw .request
  | other =>
    match classified : classifyEvent other with
    | .error _ => throw .request
    | .ok action => return .primitive other action (by first | exact classified | rfl)

private def readEventList {sources caller} (coherent : Bool)
    (events : List (SourceRuntimeContext.Event sources caller)) :
    WorkM (EligibleEvents events) :=
  let visit : Nat → (events : List (SourceRuntimeContext.Event sources caller)) → WorkM (EligibleEvents events) :=
    Nat.rec (fun _ => throw .limit) (fun _ next events => do
      match events with
      | [] => pure (.primitives [] rfl)
      | first :: rest => do
        let head ← readEventEligibility coherent first
        let tail ← next rest
        return .cons head tail)
  visit (events.length+1) events

/-- Keep the existing empty, primitive-only and singleton-call paths. A mixed
list uses one structural eligibility traversal, followed by the common native
step for every event; it never retries a failed source or callee reader. -/
private def readEvents {sources caller} (coherent : Bool)
    (events : List (SourceRuntimeContext.Event sources caller)) :
    WorkM (EligibleEvents events) := do
  exactWork (Exact.charge (8*(events.length+1)))
  match events with
  | [.named call] => readNamedEligibility call
  | others =>
    match classified : others.mapM classifyEvent with
    | .ok actions => return .primitives actions (by first | exact classified | rfl)
    | .error _ =>
      exactWork (Exact.charge (16*(others.length+1)))
      readEventList coherent others

/-- These are the genuine selected source events. No synthetic body or
signature is made, and each event is later run by the existing common step. -/
structure Sequence {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) where
  selected : SourceRuntimeTrace.StaticBody event
  original : RuntimeInterval.Computed (SourceRuntimeTrace.readStaticSource event) selected
  eligible : EligibleEvents selected.result.events
  unchanged : selected.result.allocated = [] ∧ selected.result.consumed = [] ∧
    selected.result.nextOrdinal = event.nextOrdinal

private def sequenceWithSelected {sources caller event} (selected : @Selected sources caller event)
    (coherent : Bool := false) :
    WorkM (Sequence event) := do
  let eligible ← readEvents coherent selected.selected.result.events
  return ⟨selected.selected,selected.original,eligible,selected.unchanged⟩

def readSequence {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) :
    WorkM (Sequence event) := do
  sequenceWithSelected (← readSelected event)

private def eventAllocated {sources caller} : SourceRuntimeContext.Event sources caller → List Owner
  | .named call => call.allocated
  | _ => []

private def eventConsumed {sources caller} : SourceRuntimeContext.Event sources caller → List Owner
  | .named call => call.consumed
  | _ => []

/-- A general selected event sequence keeps the exact aggregate source delta.
Only the already connected primitive/named leaves are eligible. No fresh owner
is admitted here; all source consumption is accounted for by the genuine
named steps, with their original effects and complete child histories. -/
structure Events {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) : Type where
  selected : SourceRuntimeTrace.StaticBody event
  original : RuntimeInterval.Computed (SourceRuntimeTrace.readStaticSource event) selected
  eligible : EligibleEvents selected.result.events
  allocated : selected.result.allocated = []
  noEventAllocation : selected.result.events.flatMap eventAllocated = []
  consumed : selected.result.consumed = selected.result.events.flatMap eventConsumed
  ordinal : selected.result.nextOrdinal = event.nextOrdinal

inductive Continuation {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) where
  | unchanged (source : Sequence event)
  | events (source : Events event)

def Continuation.selected {sources caller event} : @Continuation sources caller event → SourceRuntimeTrace.StaticBody event
  | .unchanged source => source.selected
  | .events source => source.selected

def Continuation.original {sources caller event} (source : @Continuation sources caller event) :
    RuntimeInterval.Computed (SourceRuntimeTrace.readStaticSource event) source.selected :=
  match source with
  | .unchanged source => source.original
  | .events source => source.original

/-- Used only by discovery and Mode.runtimeBody. Pure checking uses readSequence
and retains its no-consumption contract. The mixed path uses the same original
selection reader and common event handlers, without a combination-specific
source evaluator or a public-effect refinement. -/
def readContinuation {sources caller} (event : SourceRuntimeContext.StaticEvent sources caller) :
    WorkM (Continuation event) := do
  let selected ← readOriginalSelection event
  if unchanged : selected.selected.result.allocated = [] ∧ selected.selected.result.consumed = [] ∧
      selected.selected.result.nextOrdinal = event.nextOrdinal then
    return .unchanged (← sequenceWithSelected ⟨selected.selected,selected.original,unchanged⟩ true)
  else
    let events := selected.selected.result.events
    let allocated := events.flatMap eventAllocated
    let consumed := events.flatMap eventConsumed
    let namedFields := (events.map fun event => match event with
      | .named call =>
        let names := call.target.signature.staticNames
        (names.map fun name => name.utf8ByteSize+1).sum+names.length+
          caller.utf8ByteSize+call.target.resolution.moduleName.utf8ByteSize
      | _ => 1).sum
    exactWork (Exact.charge (32*(namedFields+events.length+
      Raw.OwnerFlow.fields (selected.selected.result.allocated ++ selected.selected.result.consumed ++
        allocated ++ consumed)+selected.selected.result.nextOrdinal+event.nextOrdinal+1)))
    if checked : selected.selected.result.allocated = [] ∧ allocated = [] ∧
        selected.selected.result.consumed = consumed ∧
        selected.selected.result.nextOrdinal = event.nextOrdinal then
      let eligible ← readEvents true events
      return .events ⟨selected.selected,selected.original,eligible,checked.1,
        checked.2.1,checked.2.2.1,checked.2.2.2⟩
    else throw .request

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

/-- The interval partition is source ordered and contiguous. For compound
lists each primitive owns one instruction, while every named leaf takes its
exact next interval from the existing ordered call context. Those contexts
are consumed independently by discovery and the common named step. Remaining
calls belong to later enclosing events and are not consumed by this reader. -/
private def compoundPositions {sources caller} (events : List (SourceRuntimeContext.Event sources caller))
    (parent : SourceSequence.Position) (calls sites : List SourceSequence.Position) :
    WorkM (List SourceSequence.Position) := do
  let finish := parent.start+parent.count
  let (reversed,cursor,_,_) ← events.foldlM (fun (positions,cursor,calls,sites) event => do
    match event with
    | .named _ =>
      let position :: calls := calls | throw .request
      guard (position.offset == event.offset && position.start == cursor &&
        position.start+position.count ≤ finish) .request
      return (position :: positions,position.start+position.count,calls,sites)
    | .selection .. =>
      let position :: sites := sites | throw .request
      guard (position.offset == event.offset && position.start == cursor &&
        position.start+position.count ≤ finish) .request
      return (position :: positions,position.start+position.count,calls,sites)
    | .primitive _ | .phase _ =>
      guard (cursor+1 ≤ finish) .request
      return (⟨event.offset,cursor,1⟩ :: positions,cursor+1,calls,sites)
    | _ => throw .request) (([] : List SourceSequence.Position),parent.start,calls,sites)
  guard (cursor == finish) .request
  return reversed.reverse

/-- Existing zero/single-event intervals retain their original whole slice.
Compound source lists use the same literal parent and existing call intervals;
other equivalent native decompositions are not inferred from widths or counts. -/
private def selectedPositions {sources caller} (events : List (SourceRuntimeContext.Event sources caller))
    (parent : SourceSequence.Position) (calls sites : List SourceSequence.Position) :
    WorkM (List SourceSequence.Position) := do
  exactWork (Exact.charge (16*(events.length+calls.length+sites.length+1)))
  match events with
  | [] =>
    guard (parent.count == 0) .request
    return []
  | [event] => return [⟨event.offset,parent.start,parent.count⟩]
  | _ => compoundPositions events parent calls sites

def Sequence.positions {sources caller event} (sequence : @Sequence sources caller event)
    (parent : SourceSequence.Position) (calls : List SourceSequence.Position := []) :
    WorkM (List SourceSequence.Position) :=
  selectedPositions sequence.selected.result.events parent calls []

def Continuation.positions {sources caller event} (source : @Continuation sources caller event)
    (parent : SourceSequence.Position) (calls sites : List SourceSequence.Position := []) :
    WorkM (List SourceSequence.Position) :=
  selectedPositions source.selected.result.events parent calls sites

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
