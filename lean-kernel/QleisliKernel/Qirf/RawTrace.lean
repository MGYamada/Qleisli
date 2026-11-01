import QleisliKernel.SourceTypes.SourceTrace
import QleisliKernel.Qirf.PrimitiveAction
import QleisliKernel.Raw.OwnerBoundaries
import QleisliKernel.Qirf.SourceSequence

/-! Bind the complete original event stream to actual Raw intervals.
Primitive actions use existing literal instructions; qmatch intervals still need
their independently checked arm/code/control equations. This component grants
no standalone execution handle or complete source-preservation claim. Source lookup,
quantum-only signatures and supported forms retain SourceTrace's explicit scope.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RawTrace
open QleisliKernel.SourceTypes
open QleisliKernel QleisliKernel.Finite QleisliKernel.Semantics.SourceOwners
abbrev Position := Qirf.SourceSequence.Position
abbrev Source := SourceTrace.Checked
abbrev Event := SourceTrace.Event

def offset {sources owner} : Event sources owner → Nat
  | .selection event .. => event.parsed.keyword.span.startByte
  | .primitive event => event.call.calleeOffset
  | .phase event => event.call.calleeOffset

def selected {sources owner} : Event sources owner → List Owner
  | .selection event .. => [event.selector,event.target]
  | .primitive event => [event.operand]
  | .phase event => [event.operand]

def frameOwners {sources owner} : Event sources owner → List Owner
  | .selection event held .. => held ++ owners event.before
  | .primitive event => event.held ++ owners event.before
  | .phase event => event.held ++ owners event.before

def leafRoles (frame : Qirf.SourceSequence.Frame) : Option (List Owner) :=
  frame.mapM fun (_,tree) => match tree with
    | .owner role _ => some role
    | .pair .. => none

def completeFrame (frame : Qirf.SourceSequence.Frame) (roles : List Owner) : Prop :=
  match leafRoles frame with | none => False | some actual => actual.Perm roles

instance (frame : Qirf.SourceSequence.Frame) (roles : List Owner) :
    Decidable (completeFrame frame roles) := by
  unfold completeFrame
  split <;> infer_instance

def primitiveKind : SourceTrace.PrimitiveKind → PrimitiveAction.Kind
  | .h => .h | .globalPhaseEighth => .globalPhaseEighth

/-- The selected source event determines the checked action. The selection
case checks the interval only; its arm semantics must be supplied separately. -/
def Action {sources owner} (event : Event sources owner)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (position : Position) (inputs outputs : List Nat) : Type :=
  match event with
  | .selection event .. => Qirf.PureInterval.Many.Checked 2 dependencies program
      position.start position.count inputs outputs [event.selector,event.target]
  | .primitive event =>
    match inputs,outputs with
    | [input],[output] => PrimitiveAction.Checked dependencies program
        position.start position.count input output event.operand (primitiveKind event.kind)
    | _,_ => Empty
  | .phase event =>
    match inputs,outputs with
    | [input],[output] => PrimitiveAction.Checked dependencies program
        position.start position.count input output event.operand
        (.phase event.application.coefficient.exponent)
    | _,_ => Empty

def readAction {sources owner} (event : Event sources owner)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (prepared : Qirf.PureInterval.Many.Prepared dependencies program)
    (position : Position) (inputs outputs : List Nat) :
    WorkM (Action event dependencies program position inputs outputs) := do
  match event with
  | .selection event .. =>
    Qirf.PureInterval.Many.checkPrepared 2 dependencies program prepared
      position.start position.count inputs outputs [event.selector,event.target]
  | .primitive event =>
    match inputs,outputs with
    | [input],[output] =>
      PrimitiveAction.checkPrepared dependencies program prepared
        position.start position.count input output event.operand (primitiveKind event.kind)
    | _,_ => throw .request
  | .phase event =>
    match inputs,outputs with
    | [input],[output] =>
      PrimitiveAction.checkPrepared dependencies program prepared
        position.start position.count input output event.operand
        (.phase event.application.coefficient.exponent)
    | _,_ => throw .request

structure Site {sources owner name} (source : Source sources owner name)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (whole : Qirf.PureInterval.Slice program 0 program.operations.length)
    (event : Event sources owner) (position : Position) where
  originalOffset : position.offset = offset event
  before : QleisliKernel.Raw.OwnerBoundaries.Boundary (Qirf.SourceInterval.parameterOwners source.signature)
    program.inputs whole.operations position.start
  after : QleisliKernel.Raw.OwnerBoundaries.Boundary (Qirf.SourceInterval.parameterOwners source.signature)
    program.inputs whole.operations (position.start+position.count)
  beforeFrame : completeFrame before.val (frameOwners event)
  afterFrame : completeFrame after.val (frameOwners event)
  inputs : List Nat
  inputBinding : Qirf.SourceSequence.tokensOf before.val (selected event) = some inputs
  outputs : List Nat
  outputBinding : Qirf.SourceSequence.tokensOf after.val (selected event) = some outputs
  action : Action event dependencies program position inputs outputs

def readSite {sources owner name} (source : Source sources owner name)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (whole : Qirf.PureInterval.Slice program 0 program.operations.length)
    (prepared : Qirf.PureInterval.Many.Prepared dependencies program)
    (boundaries : QleisliKernel.Raw.OwnerBoundaries.Checked (Qirf.SourceInterval.parameterOwners source.signature)
      program.inputs whole.operations)
    (event : Event sources owner) (position : Position) :
    WorkM (Site source dependencies program whole event position) := do
  if originalOffset : position.offset = offset event then
    let before ← QleisliKernel.Raw.OwnerBoundaries.lookup boundaries position.start
    let after ← QleisliKernel.Raw.OwnerBoundaries.lookup boundaries (position.start+position.count)
    exactWork (Exact.charge (64*(Raw.OwnerFlow.fields (frameOwners event)+1)*
      (before.val.length+after.val.length+1)^2))
    if beforeFrame : completeFrame before.val (frameOwners event) then
      if afterFrame : completeFrame after.val (frameOwners event) then
        match inputBinding : Qirf.SourceSequence.tokensOf before.val (selected event) with
        | none => throw .request
        | some inputs =>
          match outputBinding : Qirf.SourceSequence.tokensOf after.val (selected event) with
          | none => throw .request
          | some outputs =>
            let action ← readAction event dependencies program prepared position inputs outputs
            return ⟨originalOffset,before,after,beforeFrame,afterFrame,
              inputs,inputBinding,outputs,outputBinding,action⟩
      else throw .request
    else throw .request
  else throw .request

/-- Indexing by the actual event and position lists avoids accepting an
unchecked copy or comparing proof-bearing structures through erased views. -/
inductive Sites {sources owner name} (source : Source sources owner name)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (whole : Qirf.PureInterval.Slice program 0 program.operations.length) :
    List (Event sources owner) → List Position → Type where
  | nil : Sites source dependencies program whole [] []
  | cons {event events position positions}
      (site : Site source dependencies program whole event position)
      (rest : Sites source dependencies program whole events positions) :
      Sites source dependencies program whole (event::events) (position::positions)

def readSites {sources owner name} (source : Source sources owner name)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (whole : Qirf.PureInterval.Slice program 0 program.operations.length)
    (prepared : Qirf.PureInterval.Many.Prepared dependencies program)
    (boundaries : QleisliKernel.Raw.OwnerBoundaries.Checked (Qirf.SourceInterval.parameterOwners source.signature)
      program.inputs whole.operations) :
    (events : List (Event sources owner)) → (positions : List Position) →
      WorkM (Sites source dependencies program whole events positions) := fun events positions =>
  let traverse : Nat → (events : List (Event sources owner)) → (positions : List Position) →
      WorkM (Sites source dependencies program whole events positions) :=
    Nat.rec (fun _ _ => throw .limit) (fun _ next events positions => do
      match events,positions with
      | [],[] => pure .nil
      | event::events,position::positions => do
        let site ← readSite source dependencies program whole prepared boundaries event position
        let rest ← next events positions
        return .cons site rest
      | _,_ => throw .request)
  traverse (events.length+1) events positions

structure Checked {sources owner name} (source : Source sources owner name)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (positions : List Position) where
  root : Qirf.PureInterval.Witness (Raw.Observation.verify dependencies program)
  whole : Qirf.PureInterval.Slice program 0 program.operations.length
  boundaries : QleisliKernel.Raw.OwnerBoundaries.Checked (Qirf.SourceInterval.parameterOwners source.signature)
    program.inputs whole.operations
  effect : Qirf.SourceInterval.effectMatches source.signature.original.parsedHeader.effect program.effect
  noClassical : program.classicalInputs = [] ∧ program.classicalOutputs = []
  widths : Qirf.SourceInterval.inputWidths program
    (Qirf.SourceInterval.parameterOwners source.signature) = true
  allOwners : Semantics.RawOwnerFlow.Returns (Qirf.SourceInterval.parameterOwners source.signature)
    ⟨program.inputs,whole.operations,program.outputs,.unitary⟩ (valueOwners source.result.value)
  complete : Qirf.SourceSequence.covers program.operations.length positions = true
  sites : Sites source dependencies program whole source.result.events positions

/-- The indexed Sites traversal consumes the two list spines once; no runtime
comparison of complete event records remains. Covers is a single position fold.
The separate width reservation funds inputWidths's full finite layout replay:
its original signature witnesses bound each basis to 128 nodes and six bits.
Stack length/take/drop can be quadratic in basis nodes; tensor edges carry at
most 64 labels. Layout does not inspect nominal-origin strings. These are work
accounting units, not a proved wall-time or general runtime bound. -/
def headerWork {sources owner name} (source : Source sources owner name)
    (program : Semantics.Observation.Program) (positions : List Position) : Nat :=
  let roles := Qirf.SourceInterval.parameterOwners source.signature
  let widthReservation := 32*(program.inputs.length+roles.length+1) +
    128*(roles.map fun role => (role.basis.length+1)^2).sum
  32*(positions.length+source.result.events.length+1) + widthReservation

def check {sources owner name} (source : Source sources owner name)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (positions : List Position) : WorkM (Checked source dependencies program positions) := do
  exactWork (Exact.charge (headerWork source program positions))
  guard (positions.length == source.result.events.length) .request
  let prepared ← Qirf.PureInterval.Many.prepare dependencies program
  let whole ← Qirf.PureInterval.readSlice program 0 program.operations.length
  let boundaries ← QleisliKernel.Raw.OwnerBoundaries.check (Qirf.SourceInterval.parameterOwners source.signature)
    program.inputs whole.operations
  if effect : Qirf.SourceInterval.effectMatches source.signature.original.parsedHeader.effect program.effect then
    if noClassical : program.classicalInputs = [] ∧ program.classicalOutputs = [] then
      if widths : Qirf.SourceInterval.inputWidths program
          (Qirf.SourceInterval.parameterOwners source.signature) = true then
        let allOwners ← Raw.OwnerFlow.check (Qirf.SourceInterval.parameterOwners source.signature)
          (valueOwners source.result.value) ⟨program.inputs,whole.operations,program.outputs,.unitary⟩
        if complete : Qirf.SourceSequence.covers program.operations.length positions = true then
          let sites ← readSites source dependencies program whole prepared boundaries source.result.events positions
          return ⟨prepared.whole,whole,boundaries,effect,noClassical,widths,allOwners.down,complete,sites⟩
        else throw .request
      else throw .request
    else throw .request
  else throw .request

theorem Sites.offsets {sources owner name dependencies program whole events positions}
    {source : Source sources owner name}
    (checked : Sites source dependencies program whole events positions) :
    positions.map (·.offset) = events.map offset := by
  induction checked with
  | nil => rfl
  | cons site rest ih => simp only [List.map_cons,site.originalOffset,ih]

theorem Checked.everyOriginalEvent {sources owner name dependencies program positions}
    {source : Source sources owner name} (checked : Checked source dependencies program positions) :
    positions.map (·.offset) = source.result.events.map offset := checked.sites.offsets

theorem Checked.completeOperations {sources owner name dependencies program positions}
    {source : Source sources owner name} (checked : Checked source dependencies program positions) :
    program.operations = checked.whole.operations.map Semantics.Observation.Op.pure := by
  simpa using checked.whole.original

end QleisliKernel.Qirf.RawTrace
