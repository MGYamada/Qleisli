import QleisliKernel.Qirf.SelectionCore

/-! Every original structural selection uses the shared header and exact
arm/control/sector equations. SourceSequence still checks the complete literal
sequence. Reusing the already-read original caller removes duplicate parsing;
this intended work-accounting change does not waive any acceptance check.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SequenceSector
open Finite Semantics.Exact Semantics.CarrierInterface
open PureInterval (Witness)
abbrev Computed {α : Type} (action : WorkM α) (value : α) : Prop :=
  SelectionContract.Computed action value
abbrev Source := SourceTypes.QuantumSequence.Checked
abbrev Event := SourceTypes.QuantumSequence.Event
abbrev Request := SelectionContract.Request

abbrev Header (artifact : Artifact) {owner name} (source : Source artifact.sources owner name) :=
  SelectionCore.Header artifact source.signature

def readHeader (artifact : Artifact) {owner name} (source : Source artifact.sources owner name)
    (pair : Event × Request) : WorkM (Header artifact source) :=
  SelectionCore.readHeader artifact source.signature pair

structure Headers (artifact : Artifact) (owner name : String) (requests : List Request) where
  source : Witness (SourceTypes.QuantumSequence.read artifact.sources owner name)
  sites : List (Header artifact source.val)
  everyEvent : sites.map (·.event) = source.val.outcome.events
  everyRequest : sites.map (·.request) = requests

def readHeaders (artifact : Artifact) (owner name : String) (requests : List Request) :
    WorkM (Headers artifact owner name requests) := do
  guard (0 < requests.length && requests.length ≤ 128) .limit
  let source ← SourceTypes.NaturalAffine.witness (SourceTypes.QuantumSequence.read artifact.sources owner name)
  exactWork (Exact.charge (64*(requests.length+source.val.outcome.events.length+1)^2+
    64*(source.val.outcome.events.map SourceSequence.eventFields).sum))
  guard (source.val.outcome.events.length == requests.length) .request
  let sites ← (source.val.outcome.events.zip requests).mapM (readHeader artifact source.val)
  if everyEvent : sites.map (·.event) = source.val.outcome.events then
    if everyRequest : sites.map (·.request) = requests then
      return ⟨source,sites,everyEvent,everyRequest⟩
    else throw .request
  else throw .request

def rows {artifact owner name requests} (headers : Headers artifact owner name requests) : List (String × String) :=
  headers.source.val.signature.sourceRows ++ headers.sites.flatMap fun header =>
    Carrier.sourceRows header.request.attached header.request.required ++ header.rows.val

def roots {artifact owner name requests} (headers : Headers artifact owner name requests) : List Nat :=
  (artifact.root :: headers.sites.flatMap (·.roots.val)).eraseDups

theorem rootFresh {artifact order rows roots}
    (root : Witness (Validity.checkRootFromRoots artifact order rows roots)) :
    CheckedGraph artifact (Array.replicate artifact.entries.size none) order.toList root.val.receipts :=
  SelectionContract.rootFresh root

structure Body {artifact owner name requests} (order : Array Nat) (headers : Headers artifact owner name requests) where
  root : Witness (Validity.checkRootFromRoots artifact order (rows headers) (roots headers))
  context : Witness (SourceSequence.check headers.source.val root.val.dependencies root.val.program
    (requests.map (·.position)))

def prepare {artifact owner name requests} (order : Array Nat) (headers : Headers artifact owner name requests) :
    WorkM (Body order headers) := do
  let bytes := (artifact.sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
  let nodes := headers.sites.foldl (fun count header =>
    count+Carrier.sourceNodes header.request.attached header.request.required) 0
  let rowCount := headers.source.val.signature.sourceRows.length+nodes+
    headers.sites.foldl (fun count header => count+header.rows.val.length) 0
  let rootCount := 1+headers.sites.foldl (fun count header => count+header.roots.val.length) 0
  -- Row coverage scans full source strings as in Carrier.sourceRootWithRows;
  -- root deduplication compares bounded numeric indices, not source strings.
  exactWork (Exact.charge (4*nodes+5+(bytes+artifact.sources.size+1)*(rowCount+1)+16*rootCount^2))
  let root ← SourceTypes.NaturalAffine.witness (Validity.checkRootFromRoots artifact order (rows headers) (roots headers))
  let context ← SourceTypes.NaturalAffine.witness (SourceSequence.check headers.source.val root.val.dependencies
    root.val.program (requests.map (·.position)))
  return ⟨root,context⟩

/-- Bind the shared selection checker to the exact event/interval already
retained by the complete structural traversal. -/
def interval {artifact owner name requests order} {headers : Headers artifact owner name requests}
    (body : Body order headers) (header : Header artifact headers.source.val)
    (bound : SourceSequence.Bound headers.source.val body.root.val.dependencies body.root.val.program body.context.val.whole)
    (event : header.event = bound.event) (position : header.request.position = bound.position) :
    PureInterval.Many.Checked 2 body.root.val.dependencies body.root.val.program
      header.request.position.start header.request.position.count bound.site.inputs bound.site.outputs
      [header.event.selector,header.event.target] := by
  simpa only [event,position] using bound.site.interval.toMany

structure Local {artifact owner name requests order} {headers : Headers artifact owner name requests}
    (body : Body order headers) where
  header : Header artifact headers.source.val
  bound : SourceSequence.Bound headers.source.val body.root.val.dependencies body.root.val.program body.context.val.whole
  event : header.event = bound.event
  position : header.request.position = bound.position
  checked : SelectionCore.Checked header body.root.val (SelectionContract.rootFresh body.root)
    (interval body header bound event position)

/-- Retain the established observation field through the common equation result. -/
def Local.logical {artifact owner name requests order} {headers : Headers artifact owner name requests}
    {body : Body order headers} (checked : Local body) : List Matrix :=
  checked.checked.equations.logical

def readLocal {artifact owner name requests order} {headers : Headers artifact owner name requests}
    (body : Body order headers) (pair : Header artifact headers.source.val ×
      SourceSequence.Bound headers.source.val body.root.val.dependencies body.root.val.program body.context.val.whole) :
    WorkM (Local body) := do
  let header := pair.1
  let bound := pair.2
  exactWork (Exact.charge (64*(SourceSequence.eventFields header.event+SourceSequence.eventFields bound.event+1)))
  if event : header.event = bound.event then
    if position : header.request.position = bound.position then
      let checked ← SelectionCore.check header body.root.val (SelectionContract.rootFresh body.root)
        (interval body header bound event position)
      return ⟨header,bound,event,position,checked⟩
    else throw .request
  else throw .request

structure Checked (artifact : Artifact) (order : Array Nat) (owner name : String) (requests : List Request) where
  headers : Headers artifact owner name requests
  body : Body order headers
  locals : List (Local body)
  everyEvent : locals.map (·.bound.event) = headers.source.val.outcome.events
  everyRequest : locals.map (·.header.request) = requests

def check (artifact : Artifact) (order : Array Nat) (owner name : String) (requests : List Request) :
    WorkM (Checked artifact order owner name requests) := do
  let headers ← readHeaders artifact owner name requests
  let body ← prepare order headers
  let locals ← (headers.sites.zip body.context.val.sites).mapM (readLocal body)
  if everyEvent : locals.map (·.bound.event) = headers.source.val.outcome.events then
    if everyRequest : locals.map (·.header.request) = requests then
      return ⟨headers,body,locals,everyEvent,everyRequest⟩
    else throw .request
  else throw .request

theorem Checked.originalRoot {artifact order owner name requests}
    (checked : Checked artifact order owner name requests) :
    ∃ work, Validity.SourceRootPostconditionFromRoots artifact order (rows checked.headers)
      (roots checked.headers) checked.body.root.val work := by
  obtain ⟨work,left,ran⟩ := checked.body.root.property
  exact ⟨work,Validity.checkRootFromRoots_postcondition _ _ _ _ _ _ _ ran⟩

theorem Checked.publicEffect {artifact order owner name requests}
    (checked : Checked artifact order owner name requests)
    (isPublic : checked.headers.source.val.signature.original.declaration.isPublic = true) :
    checked.headers.source.val.signature.original.parsedHeader.effect = some checked.body.root.val.program.effect := by
  have present := checked.headers.source.val.signature.publicEffect isPublic
  have effect := checked.body.context.val.effect
  cases h : checked.headers.source.val.signature.original.parsedHeader.effect with
  | none => simp [h] at present
  | some declared =>
    simp only [SourceInterval.effectMatches,h] at effect
    simp only [effect]

end QleisliKernel.Qirf.SequenceSector
