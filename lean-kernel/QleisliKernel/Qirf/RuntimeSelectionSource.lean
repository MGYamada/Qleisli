import QleisliKernel.Qirf.RuntimeBodyDiscovery

/-! Recover the indexed source table and literal request site of a function
whose only quantum event is a coherent selection. Arm evidence is consumed
separately, under the root which includes its original source dependencies.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeSelectionSource
open QleisliKernel Finite SourceTypes

abbrev Context := RuntimeContextRequest.Context

/-- The exact selection site of a retained original body. This is source
preparation only: an enclosing root or authenticated named-call boundary must
retain how that Body/signature and its operation actuals were obtained. -/
structure Site {artifact : Artifact} {owner name : String}
    {signature : SourceRuntimeContext.Signature artifact.sources owner name}
    (body : SourceRuntimeTrace.Body signature) (request : Context) where
  selector : Semantics.SourceOwners.Owner
  target : Semantics.SourceOwners.Owner
  scope : List String
  naturals : PhaseApplication.Naturals artifact.sources
  offset : Nat
  original : ∃ (tokens : List LocatedToken) (parsed : QuantumMatch.Parsed) (written : QuantumMatch.parse tokens = .ok (parsed,[]))
      (held : List Semantics.SourceOwners.Owner) (remaining : SourceRuntimeValues.Environment), body.checked.events =
      [.selection tokens parsed written selector target scope naturals held remaining] ∧
      offset = parsed.keyword.span.startByte
  table : QuantumArms.Table artifact.sources owner name offset selector.basis target.basis
  tableRead : RuntimeInterval.Computed (QuantumArms.readArmsWithInstantiation
    body.checked.signature.original body.checked.signature.instantiation
    body.checked.signature.supply offset selector.basis target.basis (some naturals) scope) table
  site : RuntimeContextRequest.Site
  sites : request.sites = [site]
  positions : request.positions = [site.position]
  offsetMatches : site.position.offset = offset
  arity : site.arms.length = table.arms.length
  noCalls : request.calls.isEmpty = true ∧ request.branches.isEmpty = true
  relevance : SourceRows.Retained ([(owner,body.checked.signature.original.source)] ++
    body.checked.signature.sourceRows ++ body.checked.summary.staticRows ++
    Carrier.sourceRows site.attached site.required ++ table.arms.flatMap (·.sourceRows))

structure Checked {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments) (request : Context)
    extends Site source.body request where
  noRootActuals : source.signature.arguments.operations.isEmpty = true ∧
    source.signature.operations.actuals.isEmpty = true ∧ source.signature.operations.hasMeaningRequirements = false

private def readData {artifact : Artifact} {owner name : String}
    {signature : SourceRuntimeContext.Signature artifact.sources owner name}
    (original : SourceRuntimeTrace.Body signature) (request : Context) : WorkM (Site original request) := do
  let body := original.checked
  match events : body.events, sites : request.sites with
  | [.selection tokens parsed written selector target scope naturals held remaining],[site] =>
    let offset := parsed.keyword.span.startByte
    if valid : request.positions = [site.position] ∧ site.position.offset = offset ∧
        request.calls.isEmpty = true ∧ request.branches.isEmpty = true then
      let table ← NaturalAffine.witness (QuantumArms.readArmsWithInstantiation body.signature.original
        body.signature.instantiation body.signature.supply offset selector.basis target.basis (some naturals) scope)
      if arity : site.arms.length = table.val.arms.length then
        let relevance ← SourceRows.read ([(owner,body.signature.original.source)] ++ body.signature.sourceRows ++
          body.summary.staticRows ++ Carrier.sourceRows site.attached site.required ++ table.val.arms.flatMap (·.sourceRows))
        return ⟨selector,target,scope,naturals,offset,⟨tokens,parsed,written,held,remaining,events,rfl⟩,
          table.val,by with_reducible exact table.property,site,sites,valid.1,valid.2.1,arity,valid.2.2,relevance⟩
      else throw .request
    else throw .request
  | _,_ => throw .request

/-- Shared source preparation accepts an already retained Body, never free
operation descriptors or a replacement declaration. It supplies no root gate. -/
def readSite {artifact : Artifact} {owner name : String}
    {signature : SourceRuntimeContext.Signature artifact.sources owner name}
    (body : SourceRuntimeTrace.Body signature) (request : Context) : WorkM (Site body request) := do
  exactWork (Exact.charge (32*(body.checked.events.length+request.positions.length+request.sites.length+1)))
  readData body request

def read {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments) (request : Context) :
    WorkM (Checked source request) := do
  let body := source.body.checked
  -- Keep this charge before the original root-actual gate, including failure.
  exactWork (Exact.charge (32*(body.events.length+request.positions.length+request.sites.length+1)))
  if noRootActuals : source.signature.arguments.operations.isEmpty = true ∧
      source.signature.operations.actuals.isEmpty = true ∧ source.signature.operations.hasMeaningRequirements = false then
    return ⟨← readData source.body request,noRootActuals⟩
  else throw .request

end QleisliKernel.Qirf.RuntimeSelectionSource
