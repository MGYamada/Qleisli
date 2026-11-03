import QleisliKernel.Qirf.RuntimeNamedSelectionPrefix

/-! Prepare a selection from the authentic body of one original named call.
The parent remains subject to the strict root-actual boundary. The child is
read only through that exact event and retains its original signature/supply,
including constructed Op actuals, before arm/Meaning discovery. This preparation
checks no root or literal caller and grants no execution authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNamedSelectionSource
open QleisliKernel Finite SourceTypes
abbrev Context := RuntimeContextRequest.Context
abbrev Request := RuntimeProviderHeader.Request

/-- One actual named occurrence, without asserting that it exhausts its
caller's source body or native program. Its enclosing traversal must retain
the original event/position order, complete caller frame and final return. -/
structure Call {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments)
    (event : SourceRuntimeContext.NamedEvent artifact.sources owner)
    (position : SourceSequence.Position) (child : Context) (references : List (List (List Request))) where
  member : (.named event : SourceRuntimeContext.Event artifact.sources owner) ∈ source.body.checked.events
  callerName : event.target.callerName = name
  offset : position.offset = event.call.calleeOffset
  visibleUnitary : event.effect = .unitary
  callee : SourceRuntimeTrace.Body event.target.signature
  calleeRead : RuntimeInterval.Computed (SourceRuntimeTrace.readNamedBody event) callee
  supplies : RuntimeNamedSelectionPrefix.Prepared source.catalogue callee.checked.signature child.bodies references
  suppliesRead : RuntimeInterval.Computed (RuntimeNamedSelectionPrefix.prepare source.catalogue
    callee.checked.signature child.bodies references) supplies
  site : RuntimeSelectionSource.Site callee (supplies.siteContext child)
  siteRead : RuntimeInterval.Computed (RuntimeSelectionSource.readSite callee (supplies.siteContext child)) site
  selection : RuntimeSelectionMeaning.PreparedSite source.catalogue site supplies.collection.references
  selectionRead : RuntimeInterval.Computed
    (RuntimeSelectionMeaning.prepareSite source.catalogue site supplies.collection.references) selection
  relevance : SourceRows.Retained ([(owner,source.body.checked.signature.original.source)] ++
    source.signature.sourceRows ++ source.body.checked.summary.staticRows ++ event.target.sourceRows ++
    supplies.rows ++ selection.relevance.rows)

def Call.rows {artifact owner name arguments source event position child references}
    (call : @Call artifact owner name arguments source event position child references) : List SourceRows.Row :=
  call.relevance.rows

def Call.roots {artifact owner name arguments source event position child references}
    (call : @Call artifact owner name arguments source event position child references) : List Nat :=
  call.supplies.roots ++ call.selection.roots

/-- Read the callee only through this genuine original occurrence. Header
actuals and arm contexts remain distinct; no replacement caller is built. -/
def prepareCall {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments)
    (event : SourceRuntimeContext.NamedEvent artifact.sources owner)
    (member : (.named event : SourceRuntimeContext.Event artifact.sources owner) ∈ source.body.checked.events)
    (position : SourceSequence.Position) (child : Context) (references : List (List (List Request))) :
    WorkM (Call source event position child references) := do
  exactWork (Exact.charge (16*(name.utf8ByteSize+event.target.callerName.utf8ByteSize+1)))
  if callerName : event.target.callerName = name then
    if offset : position.offset = event.call.calleeOffset then
      if visibleUnitary : event.effect = .unitary then
        let callee ← NaturalAffine.witness (SourceRuntimeTrace.readNamedBody event)
        let supplies ← NaturalAffine.witness (RuntimeNamedSelectionPrefix.prepare source.catalogue
          callee.val.checked.signature child.bodies references)
        let site ← NaturalAffine.witness (RuntimeSelectionSource.readSite callee.val (supplies.val.siteContext child))
        let selection ← NaturalAffine.witness
          (RuntimeSelectionMeaning.prepareSite source.catalogue site.val supplies.val.collection.references)
        let relevance ← SourceRows.read ([(owner,source.body.checked.signature.original.source)] ++
          source.signature.sourceRows ++ source.body.checked.summary.staticRows ++ event.target.sourceRows ++
          supplies.val.rows ++ selection.val.relevance.rows)
        return ⟨member,callerName,offset,visibleUnitary,callee.val,by with_reducible exact callee.property,
          supplies.val,by with_reducible exact supplies.property,site.val,by with_reducible exact site.property,
          selection.val,by with_reducible exact selection.property,relevance⟩
      else throw .request
    else throw .request
  else throw .request

structure Prepared {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments) (request : Context)
    (references : List (List (List Request))) where
  noRootActuals : source.signature.arguments.operations.isEmpty = true ∧
    source.signature.operations.actuals.isEmpty = true ∧ source.signature.operations.hasMeaningRequirements = false
  event : SourceRuntimeContext.NamedEvent artifact.sources owner
  original : source.body.checked.events = [.named event]
  position : SourceSequence.Position
  positions : request.positions = [position]
  childRequest : Context
  calls : request.calls = [(position,childRequest)]
  offset : position.offset = event.call.calleeOffset
  outerEmpty : request.sites.isEmpty = true ∧ request.branches.isEmpty = true ∧ request.bodies.isEmpty = true
  visibleUnitary : event.effect = .unitary
  callee : SourceRuntimeTrace.Body event.target.signature
  calleeRead : RuntimeInterval.Computed (SourceRuntimeTrace.readNamedBody event) callee
  supplies : RuntimeNamedSelectionPrefix.Prepared source.catalogue callee.checked.signature childRequest.bodies references
  suppliesRead : RuntimeInterval.Computed (RuntimeNamedSelectionPrefix.prepare source.catalogue
    callee.checked.signature childRequest.bodies references) supplies
  site : RuntimeSelectionSource.Site callee (supplies.siteContext childRequest)
  siteRead : RuntimeInterval.Computed (RuntimeSelectionSource.readSite callee (supplies.siteContext childRequest)) site
  selection : RuntimeSelectionMeaning.PreparedSite source.catalogue site supplies.collection.references
  selectionRead : RuntimeInterval.Computed
    (RuntimeSelectionMeaning.prepareSite source.catalogue site supplies.collection.references) selection
  relevance : SourceRows.Retained ([(owner,source.body.checked.signature.original.source)] ++
    source.signature.sourceRows ++ source.body.checked.summary.staticRows ++ event.target.sourceRows ++
    supplies.rows ++ selection.relevance.rows)

def Prepared.rows {artifact owner name arguments source request references}
    (prepared : @Prepared artifact owner name arguments source request references) : List SourceRows.Row :=
  prepared.relevance.rows

def Prepared.roots {artifact owner name arguments source request references}
    (prepared : @Prepared artifact owner name arguments source request references) : List Nat :=
  (artifact.root :: prepared.supplies.roots ++ prepared.selection.roots).eraseDups

/-- No caller/callee source replacement occurs here. The exact call receipt
owns every static actual; the shared site and arm readers consume that Body.
Unsupported parent shapes and unauthenticated root Op actuals refuse directly. -/
def prepare {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments) (request : Context)
    (references : List (List (List Request))) : WorkM (Prepared source request references) := do
  exactWork (Exact.charge (32*(source.body.checked.events.length+request.positions.length+request.calls.length+
    request.sites.length+request.branches.length+request.bodies.length+1)))
  if noRootActuals : source.signature.arguments.operations.isEmpty = true ∧
      source.signature.operations.actuals.isEmpty = true ∧ source.signature.operations.hasMeaningRequirements = false then
    match original : source.body.checked.events,positions : request.positions,calls : request.calls with
    | [.named event],[position],[(callPosition,childRequest)] =>
      if valid : callPosition = position ∧ position.offset = event.call.calleeOffset ∧
          request.sites.isEmpty = true ∧ request.branches.isEmpty = true ∧ request.bodies.isEmpty = true then
        if visibleUnitary : event.effect = .unitary then
          have member : (.named event : SourceRuntimeContext.Event artifact.sources owner) ∈ source.body.checked.events := by
            exact original.symm ▸ List.mem_singleton_self _
          let call ← prepareCall source event member position childRequest references
          return ⟨noRootActuals,event,original,position,positions,childRequest,
            by simpa only [valid.1] using calls,valid.2.1,valid.2.2,visibleUnitary,
            call.callee,call.calleeRead,call.supplies,call.suppliesRead,call.site,call.siteRead,
            call.selection,call.selectionRead,call.relevance⟩
        else throw .request
      else throw .request
    | _,_,_ => throw .request
  else throw .request

end QleisliKernel.Qirf.RuntimeNamedSelectionSource
