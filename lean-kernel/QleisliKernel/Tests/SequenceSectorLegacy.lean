import QleisliKernel.Qirf.SourceSequence
import QleisliKernel.Qirf.SourceFrameSector

/-! Test-only frozen pre-sharing checker. Runtime callers never import it.
Check every original selection against its actual interval in one fresh
graph. Reuse original arm/evidence bindings, code checks, independent controls
and exact sector equations. Structural correspondence alone never grants this
result. Native/QDV dispatch and ordinary compiler integration remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SequenceSectorLegacy
open QleisliKernel.Qirf
open Finite Semantics.Exact Semantics.CarrierInterface
open PureInterval (Witness)
abbrev Computed {α : Type} (action : WorkM α) (value : α) : Prop :=
  ∃ work left, action.run work = (.ok value,left)
abbrev Source := SourceTypes.QuantumSequence.Checked
abbrev Event := SourceTypes.QuantumSequence.Event

structure Request where
  attached : Interface
  required : Interface
  position : SourceSequence.Position
  programs : List SourceArm.Programs
  deriving BEq, DecidableEq, Repr

structure Header (artifact : Artifact) {owner name} (source : Source artifact.sources owner name) where
  event : Event
  request : Request
  ports : NominalSector.Ports
  portsRead : NominalSector.ports request.required = some ports
  interface : request.attached = request.required
  types : NominalSector.sameTypes request.required ports = true
  roles : ports.selectorIn.basis = event.selector.basis ∧ ports.targetIn.basis = event.target.basis
  table : Witness (SourceTypes.QuantumArms.read artifact.sources owner name request.position.offset
    ports.selectorIn.basis ports.targetIn.basis)
  original : table.val.site.original.source = source.signature.original.source ∧ table.val.site.parsed = event.parsed
  bindings : Witness (SourceArm.readAll artifact table.val.arms request.programs)
  roots : Witness (SourceArm.readRoots artifact bindings.val)
  rows : Witness (SourceSector.readRowsWithSignature table.val source.signature)

def readHeader (artifact : Artifact) {owner name} (source : Source artifact.sources owner name)
    (pair : Event × Request) : WorkM (Header artifact source) := do
  let event := pair.1
  let request := pair.2
  guard (NominalSector.shape request.attached request.required) .request
  SourceTypes.checkMany artifact.sources (NominalSector.forests request.attached request.required)
  exactWork (Exact.charge (16*(SourceSequence.eventFields event+source.signature.original.source.utf8ByteSize+1)))
  match portsRead : NominalSector.ports request.required with
  | none => throw .request
  | some ports =>
    if interface : request.attached = request.required then
      if types : NominalSector.sameTypes request.required ports = true then
        if roles : ports.selectorIn.basis = event.selector.basis ∧ ports.targetIn.basis = event.target.basis then
          let table ← SourceTypes.NaturalAffine.witness (SourceTypes.QuantumArms.read artifact.sources owner name
            request.position.offset ports.selectorIn.basis ports.targetIn.basis)
          if original : table.val.site.original.source = source.signature.original.source ∧
              table.val.site.parsed = event.parsed then
            let bindings ← SourceTypes.NaturalAffine.witness (SourceArm.readAll artifact table.val.arms request.programs)
            let roots ← SourceTypes.NaturalAffine.witness (SourceArm.readRoots artifact bindings.val)
            let rows ← SourceTypes.NaturalAffine.witness (SourceSector.readRowsWithSignature table.val source.signature)
            return ⟨event,request,ports,portsRead,interface,types,roles,table,original,bindings,roots,rows⟩
          else throw .request
        else throw .request
      else throw .request
    else throw .request

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
    CheckedGraph artifact (Array.replicate artifact.entries.size none) order.toList root.val.receipts := by
  obtain ⟨work,left,ran⟩ := root.property
  exact (Validity.checkRootFromRoots_postcondition _ _ _ _ _ _ _ ran).fresh

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

structure SiteBody {artifact owner name requests order} {headers : Headers artifact owner name requests}
    (body : Body order headers) (header : Header artifact headers.source.val)
    (bound : SourceSequence.Bound headers.source.val body.root.val.dependencies body.root.val.program body.context.val.whole) where
  event : header.event = bound.event
  position : header.request.position = bound.position
  inputs : bound.site.interval.selected = header.request.attached.inputs.map (·.port)
  outputs : bound.site.interval.returned = header.request.attached.outputs.map (·.port)
  codes : SourceFrameSector.Codes header.ports
  restriction : Witness (QleisliKernel.Raw.Sector.read body.root.val.dependencies
    [.bits codes.selectorLayout.val.bits] [.bits codes.targetLayout.val.bits]
    (PureInterval.fragment bound.site.interval.selected bound.site.interval.slice bound.site.outputs))
  entries : Witness (header.bindings.val.mapM fun binding =>
    SourceSector.readEntry artifact body.root.val.receipts binding (rootFresh body.root))

def prepareSite {artifact owner name requests order} {headers : Headers artifact owner name requests}
    (body : Body order headers) (header : Header artifact headers.source.val)
    (bound : SourceSequence.Bound headers.source.val body.root.val.dependencies body.root.val.program body.context.val.whole) :
    WorkM (SiteBody body header bound) := do
  exactWork (Exact.charge (64*(SourceSequence.eventFields header.event+SourceSequence.eventFields bound.event+1)))
  if event : header.event = bound.event then
    if position : header.request.position = bound.position then
      if inputs : bound.site.interval.selected = header.request.attached.inputs.map (·.port) then
        if outputs : bound.site.interval.returned = header.request.attached.outputs.map (·.port) then
          let codes ← SourceFrameSector.readCodes header.ports
          let restriction ← SourceTypes.NaturalAffine.witness (QleisliKernel.Raw.Sector.read body.root.val.dependencies
            [.bits codes.selectorLayout.val.bits] [.bits codes.targetLayout.val.bits]
            (PureInterval.fragment bound.site.interval.selected bound.site.interval.slice bound.site.outputs))
          let entries ← SourceTypes.NaturalAffine.witness (header.bindings.val.mapM fun binding =>
            SourceSector.readEntry artifact body.root.val.receipts binding (rootFresh body.root))
          return ⟨event,position,inputs,outputs,codes,restriction,entries⟩
        else throw .request
      else throw .request
    else throw .request
  else throw .request

structure Local {artifact owner name requests order} {headers : Headers artifact owner name requests}
    (body : Body order headers) where
  header : Header artifact headers.source.val
  bound : SourceSequence.Bound headers.source.val body.root.val.dependencies body.root.val.program body.context.val.whole
  prepared : SiteBody body header bound
  arms : List SectorArms.BoundArm
  armsRead : Computed (SectorArms.readAll artifact body.root.val.dependencies header.ports.targetIn.basis
    prepared.codes.targetLayout.val.bits prepared.codes.targetIn.val prepared.codes.targetOut.val
    prepared.codes.selectorLayout.val.labels.length (header.bindings.val.map (·.reference))) arms
  logical : List Matrix
  logicalRead : Computed (NominalSector.checkLogicals prepared.codes.targetIn.val prepared.codes.targetOut.val
    prepared.restriction.val.sectors prepared.codes.selectorLayout.val.labels (arms.map (·.checked.logical))) logical

def finishSite {artifact owner name requests order} {headers : Headers artifact owner name requests}
    (body : Body order headers) (header : Header artifact headers.source.val)
    (bound : SourceSequence.Bound headers.source.val body.root.val.dependencies body.root.val.program body.context.val.whole)
    (prepared : SiteBody body header bound) : WorkM (Local body) := do
  let arms ← SourceTypes.NaturalAffine.witness (SectorArms.readAll artifact body.root.val.dependencies
    header.ports.targetIn.basis prepared.codes.targetLayout.val.bits prepared.codes.targetIn.val prepared.codes.targetOut.val
    prepared.codes.selectorLayout.val.labels.length (header.bindings.val.map (·.reference)))
  let logical ← SourceTypes.NaturalAffine.witness (NominalSector.checkLogicals prepared.codes.targetIn.val
    prepared.codes.targetOut.val prepared.restriction.val.sectors prepared.codes.selectorLayout.val.labels
    (arms.val.map (·.checked.logical)))
  return ⟨header,bound,prepared,arms.val,by with_reducible exact arms.property,
    logical.val,by with_reducible exact logical.property⟩

def readLocal {artifact owner name requests order} {headers : Headers artifact owner name requests}
    (body : Body order headers) (pair : Header artifact headers.source.val ×
      SourceSequence.Bound headers.source.val body.root.val.dependencies body.root.val.program body.context.val.whole) :
    WorkM (Local body) := do
  let prepared ← prepareSite body pair.1 pair.2
  finishSite body pair.1 pair.2 prepared

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

end QleisliKernel.Tests.SequenceSectorLegacy
