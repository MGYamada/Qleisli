import QleisliKernel.Qirf.SourceInterval
import QleisliKernel.SourceTypes.QuantumSequence

/-! Literal intervals for every qmatch in one complete original structural
body. Positions are untrusted: they must exhaust the actual operation list in
source order. Actual Raw owner moves derive the tokens at both boundaries;
physical widths or a supplied source-role map cannot replace that derivation.
Fresh graph/arm/control/sector checks and paired native/QDV integration are
still enclosing requirements. This component grants no accepted handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceSequence
open Finite Semantics.SourceOwners
abbrev Source := SourceTypes.QuantumSequence.Checked
abbrev Event := SourceTypes.QuantumSequence.Event
abbrev Frame := Semantics.RawOwnerFlow.Frame

structure Position where
  offset : Nat
  start : Nat
  count : Nat
  deriving BEq, DecidableEq, Repr

def covers (length : Nat) (positions : List Position) : Bool :=
  positions.foldlM (fun expected position =>
    if position.start == expected then some (expected+position.count) else none) 0 == some length

def eventFields (event : Event) : Nat :=
  let cells := event.before ++ event.remaining
  (event.parsed.tokens.map fun token => token.text.utf8ByteSize+4).sum*4 +
    (event.scope.map fun name => name.utf8ByteSize+1).sum +
    (cells.map fun cell => cell.name.utf8ByteSize+cell.value.length+1).sum +
    Raw.OwnerFlow.fields (owners cells ++ [event.selector,event.target])

/-- Distinct zero-width source owners still have distinct ordinal/type
identities. Only an actual leaf in the original Raw owner frame is eligible. -/
def tokenOf (frame : Frame) (role : Owner) : Option Nat :=
  match frame.filterMap (fun (token,tree) => match tree with
    | .owner owner _ => if owner = role then some token else none
    | .pair _ _ _ => none) with
  | [token] => some token
  | _ => none

/-- A successful lookup names the exact original logical owner, not another
leaf of equal physical width or with the same empty wire list. -/
theorem tokenOf_original (frame : Frame) (role : Owner) (token : Nat)
    (ok : tokenOf frame role = some token) :
    ∃ bits, (token,Semantics.RawOwnerFlow.Tree.owner role bits) ∈ frame := by
  let select := fun (cell : Nat × Semantics.RawOwnerFlow.Tree) => match cell.2 with
    | .owner owner _ => if owner = role then some cell.1 else none
    | .pair _ _ _ => none
  have only : frame.filterMap select = [token] := by
    unfold tokenOf at ok
    split at ok
    next found selected =>
      have same : found = token := Option.some.inj ok
      simpa only [same] using selected
    next => cases ok
  have member : token ∈ frame.filterMap select := by rw [only]; simp
  obtain ⟨⟨found,tree⟩,present,selected⟩ := List.mem_filterMap.mp member
  cases tree with
  | owner actual bits =>
    dsimp only [select] at selected
    split at selected
    next same =>
      have tokenSame : found = token := Option.some.inj selected
      subst actual
      subst found
      exact ⟨bits,present⟩
    next => cases selected
  | pair left right bits => cases selected

def tokensOf (frame : Frame) (roles : List Owner) : Option (List Nat) :=
  roles.mapM (tokenOf frame)

private def present {α : Type} (value : Option α) : WorkM α :=
  match value with | none => throw .request | some value => pure value

def frameAt (roles : List Owner) (inputs : List Semantics.Raw.Port)
    (operations : List Semantics.Raw.Op) (offset : Nat) : WorkM Frame := do
  guard (offset ≤ operations.length) .request
  exactWork (Exact.charge (8*(Raw.OwnerFlow.fields roles+1)+
    128*(offset+1)*(roles.length+1)^2))
  let initial ← present (Semantics.RawOwnerFlow.seed roles inputs)
  present ((operations.take offset).foldlM Semantics.RawOwnerFlow.step initial)

structure Site {sources owner name} (source : Source sources owner name)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (whole : PureInterval.Slice program 0 program.operations.length) (event : Event) (position : Position) where
  originalOffset : position.offset = event.parsed.keyword.span.startByte
  before : PureInterval.Witness
    (frameAt (SourceInterval.parameterOwners source.signature) program.inputs whole.operations position.start)
  after : PureInterval.Witness
    (frameAt (SourceInterval.parameterOwners source.signature) program.inputs whole.operations
      (position.start+position.count))
  inputs : List Nat
  inputBinding : tokensOf before.val [event.selector,event.target] = some inputs
  outputs : List Nat
  outputBinding : tokensOf after.val [event.selector,event.target] = some outputs
  interval : PureInterval.Checked dependencies program position.start position.count inputs outputs
    [event.selector,event.target]

def readSite {sources owner name} (source : Source sources owner name)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (whole : PureInterval.Slice program 0 program.operations.length) (event : Event) (position : Position) :
    WorkM (Site source dependencies program whole event position) := do
  if original : position.offset = event.parsed.keyword.span.startByte then
    let before ← SourceTypes.NaturalAffine.witness
      (frameAt (SourceInterval.parameterOwners source.signature) program.inputs whole.operations position.start)
    let after ← SourceTypes.NaturalAffine.witness
      (frameAt (SourceInterval.parameterOwners source.signature) program.inputs whole.operations
        (position.start+position.count))
    exactWork (Exact.charge (32*(before.val.length+after.val.length+1)))
    match inputBinding : tokensOf before.val [event.selector,event.target] with
    | none => throw .request
    | some inputs =>
      match outputBinding : tokensOf after.val [event.selector,event.target] with
      | none => throw .request
      | some outputs =>
        let interval ← PureInterval.check dependencies program position.start position.count inputs outputs
          [event.selector,event.target]
        return ⟨original,before,after,inputs,inputBinding,outputs,outputBinding,interval⟩
  else throw .request

structure Bound {sources owner name} (source : Source sources owner name)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (whole : PureInterval.Slice program 0 program.operations.length) where
  event : Event
  position : Position
  site : Site source dependencies program whole event position

def readOne {sources owner name} (source : Source sources owner name)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (whole : PureInterval.Slice program 0 program.operations.length) (pair : Event × Position) :
    WorkM (Bound source dependencies program whole) := do
  let site ← readSite source dependencies program whole pair.1 pair.2
  return ⟨pair.1,pair.2,site⟩

structure Checked {sources owner name} (source : Source sources owner name)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (positions : List Position) where
  whole : PureInterval.Slice program 0 program.operations.length
  effect : SourceInterval.effectMatches source.signature.original.parsedHeader.effect program.effect
  noClassical : program.classicalInputs = [] ∧ program.classicalOutputs = []
  widths : SourceInterval.inputWidths program (SourceInterval.parameterOwners source.signature) = true
  allOwners : Semantics.RawOwnerFlow.Returns (SourceInterval.parameterOwners source.signature)
    ⟨program.inputs,whole.operations,program.outputs,.unitary⟩ (valueOwners source.outcome.value)
  complete : covers program.operations.length positions = true
  sites : List (Bound source dependencies program whole)
  everySource : sites.map (·.event) = source.outcome.events
  everyPosition : sites.map (·.position) = positions

/-- No prefix/suffix or extra Raw operation can hide outside the checked
sequence. Every original site is retained even when two adjacent operations
cancel or their exact matrices happen to coincide. Arm equations remain the
responsibility of the enclosing source-sector gate. -/
def check {sources owner name} (source : Source sources owner name)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (positions : List Position) : WorkM (Checked source dependencies program positions) := do
  guard (positions.length ≤ 128 && source.outcome.events.length ≤ 128) .limit
  exactWork (Exact.charge (32*(positions.length+source.outcome.events.length+1)^2+
    32*(source.outcome.events.map eventFields).sum))
  guard (positions.length == source.outcome.events.length) .request
  let whole ← PureInterval.readSlice program 0 program.operations.length
  if effect : SourceInterval.effectMatches source.signature.original.parsedHeader.effect program.effect then
    if noClassical : program.classicalInputs = [] ∧ program.classicalOutputs = [] then
      if widths : SourceInterval.inputWidths program (SourceInterval.parameterOwners source.signature) = true then
        let allOwners ← Raw.OwnerFlow.check (SourceInterval.parameterOwners source.signature)
          (valueOwners source.outcome.value) ⟨program.inputs,whole.operations,program.outputs,.unitary⟩
        if complete : covers program.operations.length positions = true then
          let sites ← (source.outcome.events.zip positions).mapM (readOne source dependencies program whole)
          if everySource : sites.map (·.event) = source.outcome.events then
            if everyPosition : sites.map (·.position) = positions then
              return ⟨whole,effect,noClassical,widths,allOwners.down,complete,sites,everySource,everyPosition⟩
            else throw .request
          else throw .request
        else throw .request
      else throw .request
    else throw .request
  else throw .request

theorem Checked.allOriginalOccurrences {sources owner name dependencies program positions}
    {source : Source sources owner name} (checked : Checked source dependencies program positions) :
    checked.sites.map (·.event.parsed.keyword.span.startByte) =
      SourceTypes.QuantumSequence.originalOffsets source.signature.original.occurrence.body := by
  simpa only [List.map_map] using
    (congrArg (List.map fun event => event.parsed.keyword.span.startByte) checked.everySource).trans
      source.everyOccurrence

theorem Checked.completeOperations {sources owner name dependencies program positions}
    {source : Source sources owner name} (checked : Checked source dependencies program positions) :
    program.operations = checked.whole.operations.map Semantics.Observation.Op.pure := by
  simpa using checked.whole.original

end QleisliKernel.Qirf.SourceSequence
