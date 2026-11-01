import QleisliKernel.Qirf.RawTrace
import QleisliKernel.Qirf.SelectionCore

/-! Complete source events, literal Raw intervals and original qmatch equations.
Primitive events remain alongside all original selections.
Only the selected source forms in SourceTrace are supported; no fallback or
execution handle is introduced. Ordinary/observing/generic calls remain pending.
Original arm IR is freshly checked and source-bound; recursive source-arm body
lowering correspondence remains a separate duty, as in SourceArm.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.ContextSector
open QleisliKernel.SourceTypes
open QleisliKernel QleisliKernel.Qirf
open Finite Semantics.SourceOwners
open QleisliKernel.Qirf.PureInterval (Witness)
abbrev Source := SourceTrace.Checked
abbrev Request := SelectionCore.Request
abbrev Position := SourceSequence.Position

def selection {sources owner} : SourceTrace.Event sources owner → Option SourceTypes.QuantumSequence.Event
  | .selection event .. => some event
  | .primitive _ => none
  | .phase _ => none

structure Headers (artifact : Artifact) (owner name : String) (requests : List Request) where
  source : Witness (SourceTrace.read artifact.sources owner name)
  sites : List (SelectionCore.Header artifact source.val.signature)
  everyEvent : sites.map (·.event) = source.val.result.events.filterMap selection
  everyRequest : sites.map (·.request) = requests

def readHeaders (artifact : Artifact) (owner name : String) (requests : List Request) :
    WorkM (Headers artifact owner name requests) := do
  guard (0 < requests.length && requests.length ≤ 128) .limit
  let source ← SourceTypes.NaturalAffine.witness (SourceTrace.read artifact.sources owner name)
  let events := source.val.result.events.filterMap selection
  exactWork (Exact.charge (64*(requests.length+events.length+1)^2+
    64*(events.map SourceSequence.eventFields).sum))
  guard (events.length == requests.length) .request
  let sites ← (events.zip requests).mapM (SelectionCore.readHeader artifact source.val.signature)
  if everyEvent : sites.map (·.event) = source.val.result.events.filterMap selection then
    if everyRequest : sites.map (·.request) = requests then
      return ⟨source,sites,everyEvent,everyRequest⟩
    else throw .request
  else throw .request

/-- Every retained absence lookup still names exactly one original module row. -/
theorem lookupRow {sources owner name} (lookup : SourceLookup.Checked sources owner name) :
    (owner,lookup.source) ∈ sources.toList := by
  have present : (owner,lookup.source) ∈
      sources.toList.filter (fun row => row.1 == owner) := by
    rw [lookup.originalModule]
    exact List.mem_cons_self
  exact (List.mem_filter.mp present).1

def preludeRows {sources name} : {disabled : Bool} →
    CallName.PreludeMiss sources name disabled → List (String × String)
  | _,.disabled => []
  | _,.enabled lookup _ => [("std::prelude",lookup.source)]

theorem preludeRowsOriginal {sources name disabled}
    (lookup : CallName.PreludeMiss sources name disabled) (row : String × String)
    (member : row ∈ preludeRows lookup) : row ∈ sources.toList := by
  cases lookup with
  | disabled => simp [preludeRows] at member
  | enabled lookup missing =>
    have same : row = ("std::prelude",lookup.source) := by simpa [preludeRows] using member
    subst row
    exact lookupRow lookup

/-- Primitive resolution depends on the original caller policy and, when enabled,
the exact prelude declaration scan. These rows are relevant even when the name
is absent. Merely appearing elsewhere in the source table grants no relevance. -/
def candidateRows {sources owner scope tokens} (candidate : CallName.Checked sources owner scope tokens) :
    List (String × String) :=
  match candidate.decision with
  | .primitive _ _ _ localMissing _ preludeMissing _ _ =>
    (owner,localMissing.lookup.source) :: preludeRows preludeMissing
  | _ => []

theorem candidateRowsOriginal {sources owner scope tokens}
    (candidate : CallName.Checked sources owner scope tokens) (row : String × String)
    (member : row ∈ candidateRows candidate) : row ∈ sources.toList := by
  cases h : candidate.decision with
  | lexical => simp [candidateRows,h] at member
  | named => simp [candidateRows,h] at member
  | prelude => simp [candidateRows,h] at member
  | primitive name spelling unbound localMissing policy preludeMissing candidate originalName =>
    simp only [candidateRows,h,List.mem_cons] at member
    rcases member with same | member
    · subst row
      exact lookupRow localMissing.lookup
    · exact preludeRowsOriginal preludeMissing row member

def primitiveRows {sources owner} (event : SourceTrace.PrimitiveEvent sources owner) :
    List (String × String) := candidateRows event.candidate

theorem primitiveRowsOriginal {sources owner}
    (event : SourceTrace.PrimitiveEvent sources owner) (row : String × String)
    (member : row ∈ primitiveRows event) : row ∈ sources.toList :=
  candidateRowsOriginal event.candidate row member

def eventRows {sources owner} : SourceTrace.Event sources owner → List (String × String)
  | .primitive event => primitiveRows event
  | .phase event => candidateRows event.application.candidate
  | .selection .. => []

def rows {artifact owner name requests} (headers : Headers artifact owner name requests) : List (String × String) :=
  headers.source.val.signature.sourceRows ++ headers.source.val.result.events.flatMap eventRows ++
    headers.sites.flatMap fun header =>
    Carrier.sourceRows header.request.attached header.request.required ++ header.rows.val

def roots {artifact owner name requests} (headers : Headers artifact owner name requests) : List Nat :=
  (artifact.root :: headers.sites.flatMap (·.roots.val)).eraseDups

structure Body {artifact owner name requests} (order : Array Nat)
    (headers : Headers artifact owner name requests) (positions : List Position) where
  root : Witness (Validity.checkRootFromRoots artifact order (rows headers) (roots headers))
  context : Witness (RawTrace.check headers.source.val root.val.dependencies root.val.program positions)

def prepare {artifact owner name requests} (order : Array Nat)
    (headers : Headers artifact owner name requests) (positions : List Position) :
    WorkM (Body order headers positions) := do
  let bytes := (artifact.sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
  let nodes := headers.sites.foldl (fun count header =>
    count+Carrier.sourceNodes header.request.attached header.request.required) 0
  let rowCount := headers.source.val.signature.sourceRows.length+
    (headers.source.val.result.events.flatMap eventRows).length+nodes+
    headers.sites.foldl (fun count header => count+header.rows.val.length) 0
  let rootCount := 1+headers.sites.foldl (fun count header => count+header.roots.val.length) 0
  exactWork (Exact.charge (4*nodes+5+(bytes+artifact.sources.size+1)*(rowCount+1)+16*rootCount^2))
  let root ← SourceTypes.NaturalAffine.witness
    (Validity.checkRootFromRoots artifact order (rows headers) (roots headers))
  let context ← SourceTypes.NaturalAffine.witness
    (RawTrace.check headers.source.val root.val.dependencies root.val.program positions)
  return ⟨root,context⟩

/-- This is an actual dependent member of the original RawTrace.Sites list,
not a separately decoded event or an interval reconstructed by another reader. -/
structure SelectionSite {sources owner name} (source : Source sources owner name)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (whole : PureInterval.Slice program 0 program.operations.length) where
  event : SourceTypes.QuantumSequence.Event
  held : List Owner
  scope : List String
  frame : (held ++ owners event.before).Perm
    ([event.selector,event.target] ++ held ++ owners event.remaining)
  position : Position
  site : RawTrace.Site source dependencies program whole (.selection event held scope frame) position

def collect {sources owner name dependencies program whole events positions}
    {source : Source sources owner name}
    (sites : RawTrace.Sites source dependencies program whole events positions) :
    WorkM (List (SelectionSite source dependencies program whole)) :=
  let traverse : Nat → {events : List (SourceTrace.Event sources owner)} →
      {positions : List Position} →
      RawTrace.Sites source dependencies program whole events positions →
      WorkM (List (SelectionSite source dependencies program whole)) :=
    Nat.rec (fun {_} {_} _ => throw .limit) (fun _ next {_} {_} sites => do
      exactWork (Exact.charge 1)
      match sites with
      | .nil => return []
      | .cons (event := event) (position := position) site rest =>
        let collected ← next rest
        match event with
        | .selection event held scope frame =>
          return ⟨event,held,scope,frame,position,site⟩ :: collected
        | .primitive _ => return collected
        | .phase _ => return collected)
  traverse (events.length+1) sites

def interval {artifact owner name requests order positions}
    {headers : Headers artifact owner name requests}
    (body : Body order headers positions)
    (header : SelectionCore.Header artifact headers.source.val.signature)
    (bound : SelectionSite headers.source.val body.root.val.dependencies body.root.val.program body.context.val.whole)
    (event : header.event = bound.event) (position : header.request.position = bound.position) :
    PureInterval.Many.Checked 2 body.root.val.dependencies body.root.val.program
      header.request.position.start header.request.position.count bound.site.inputs bound.site.outputs
      [header.event.selector,header.event.target] := by
  simpa only [event,position,RawTrace.Action] using bound.site.action

structure Local {artifact owner name requests order positions}
    {headers : Headers artifact owner name requests}
    (body : Body order headers positions) where
  header : SelectionCore.Header artifact headers.source.val.signature
  bound : SelectionSite headers.source.val body.root.val.dependencies body.root.val.program body.context.val.whole
  event : header.event = bound.event
  position : header.request.position = bound.position
  checked : SelectionCore.Checked header body.root.val (SelectionContract.rootFresh body.root)
    (interval body header bound event position)

def readLocal {artifact owner name requests order positions}
    {headers : Headers artifact owner name requests}
    (body : Body order headers positions)
    (pair : SelectionCore.Header artifact headers.source.val.signature ×
      SelectionSite headers.source.val body.root.val.dependencies body.root.val.program body.context.val.whole) :
    WorkM (Local body) := do
  let header := pair.1
  let bound := pair.2
  exactWork (Exact.charge (64*(SourceSequence.eventFields header.event+
    SourceSequence.eventFields bound.event+1)))
  if event : header.event = bound.event then
    if position : header.request.position = bound.position then
      let checked ← SelectionCore.check header body.root.val (SelectionContract.rootFresh body.root)
        (interval body header bound event position)
      return ⟨header,bound,event,position,checked⟩
    else throw .request
  else throw .request

structure Checked (artifact : Artifact) (order : Array Nat) (owner name : String)
    (positions : List Position) (requests : List Request) where
  headers : Headers artifact owner name requests
  body : Body order headers positions
  locals : List (Local body)
  everyEvent : locals.map (·.bound.event) = headers.source.val.result.events.filterMap selection
  everyRequest : locals.map (·.header.request) = requests

def check (artifact : Artifact) (order : Array Nat) (owner name : String)
    (positions : List Position) (requests : List Request) :
    WorkM (Checked artifact order owner name positions requests) := do
  let headers ← readHeaders artifact owner name requests
  let body ← prepare order headers positions
  let selected ← collect body.context.val.sites
  guard (headers.sites.length == selected.length) .request
  let locals ← (headers.sites.zip selected).mapM (readLocal body)
  if everyEvent : locals.map (·.bound.event) = headers.source.val.result.events.filterMap selection then
    if everyRequest : locals.map (·.header.request) = requests then
      return ⟨headers,body,locals,everyEvent,everyRequest⟩
    else throw .request
  else throw .request

theorem Checked.originalRoot {artifact order owner name positions requests}
    (checked : Checked artifact order owner name positions requests) :
    ∃ work, Validity.SourceRootPostconditionFromRoots artifact order (rows checked.headers)
      (roots checked.headers) checked.body.root.val work := by
  obtain ⟨work,left,ran⟩ := checked.body.root.property
  exact ⟨work,Validity.checkRootFromRoots_postcondition _ _ _ _ _ _ _ ran⟩

theorem Checked.allOriginalEvents {artifact order owner name positions requests}
    (checked : Checked artifact order owner name positions requests) :
    positions.map (·.offset) = checked.headers.source.val.result.events.map RawTrace.offset :=
  checked.body.context.val.everyOriginalEvent

theorem Checked.publicEffect {artifact order owner name positions requests}
    (checked : Checked artifact order owner name positions requests)
    (isPublic : checked.headers.source.val.signature.original.declaration.isPublic = true) :
    checked.headers.source.val.signature.original.parsedHeader.effect =
      some checked.body.root.val.program.effect := by
  have present := checked.headers.source.val.signature.publicEffect isPublic
  have effect := checked.body.context.val.effect
  cases h : checked.headers.source.val.signature.original.parsedHeader.effect with
  | none => simp [h] at present
  | some declared =>
    simp only [SourceInterval.effectMatches,h] at effect
    simp only [effect]

end QleisliKernel.Qirf.ContextSector
