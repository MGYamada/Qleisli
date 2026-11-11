import QleisliKernel.Qirf.RuntimeSelectionMeaning

/-! Original callee operation actuals before its selection events. The mixed
header chooses every actual exactly once, including unused formals; every graph
keeps its child-edge providers, local Meaning groups and original supply context.
Header-refined root Meaning requirements remain an explicit refusal until their
exact whole-actual equation is consumed. No signature is reconstructed here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNamedSelectionPrefix
open QleisliKernel Finite SourceTypes
abbrev Request := RuntimeProviderHeader.Request

/-- This is the same original-header access rule used by the common body
prefix. Convenient actual capabilities never rewrite the formal declaration. -/
def required {sources owner name} (signature : SourceRuntimeContext.Signature sources owner name)
    (argument : String) : StaticOperation.Paths :=
  match signature.instantiation with
  | .closed _ => OperationAccess.empty
  | .static _ environment _ =>
    ⟨environment.numeric.original.header.access.contains (.applicable,argument),
      environment.numeric.original.header.access.contains (.adjointable,argument),
      environment.numeric.original.header.access.contains (.controllable,argument)⟩

structure Entry {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    {owner name : String} (signature : SourceRuntimeContext.Signature artifact.sources owner name)
    (actuals : List (Sigma (StaticOperation.Actual artifact.sources signature.context))) where
  index : Fin actuals.length
  actual : Sigma (StaticOperation.Actual artifact.sources signature.context)
  atIndex : actuals[index.val]'index.isLt = actual
  implementations : List Request
  references : List (List Request)
  graph : RuntimePreparedOperation.GraphPrepared artifact catalogue actual.2.graph implementations references
  original : RuntimeInterval.Computed
    (RuntimePreparedOperation.prepareGraph artifact catalogue actual.2.graph implementations references) graph

def Entry.rows {artifact catalogue owner name signature actuals}
    (entry : @Entry artifact catalogue owner name signature actuals) : List SourceRows.Row := entry.graph.rows

def Entry.roots {artifact catalogue owner name signature actuals}
    (entry : @Entry artifact catalogue owner name signature actuals) : List Nat := entry.graph.roots

structure Collection {artifact catalogue owner name signature actuals} where
  entries : List (@Entry artifact catalogue owner name signature actuals)
  bodies : List Request
  references : List (List (List Request))

private def collect {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    {owner name : String} (signature : SourceRuntimeContext.Signature artifact.sources owner name)
    (actuals : List (Sigma (StaticOperation.Actual artifact.sources signature.context)))
    (bodies : List Request) (references : List (List (List Request))) :
    WorkM (@Collection artifact catalogue owner name signature actuals) := do
  exactWork (Exact.charge (16*(actuals.length+bodies.length+references.length+1)^2+
    16*(actuals.length+1)*(SourceTrace.Meter.tokenFields signature.original.occurrence.header+1)))
  let (entries,bodies,references) ← (List.finRange actuals.length).foldlM
    (fun (entries,bodies,references) index => do
      let actual := actuals[index.val]'index.isLt
      let group :: rest := references | throw .request
      let occurrences ← StaticOperation.readOccurrences actual.1.2
      let count := (RuntimeProviderHeaders.providerIndices actual.1.2 occurrences).length
      guard (count ≤ bodies.length) .request
      let implementations := bodies.take count
      let graph ← NaturalAffine.witness
        (RuntimePreparedOperation.prepareGraph artifact catalogue actual.2.graph implementations group)
      let entry : Entry catalogue signature actuals :=
        ⟨index,actual,rfl,implementations,group,graph.val,by with_reducible exact graph.property⟩
      return (entry :: entries,bodies.drop count,rest)) ([],bodies,references)
  return ⟨entries.reverse,bodies,references⟩

structure Prepared {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    {owner name : String} (signature : SourceRuntimeContext.Signature artifact.sources owner name)
    (bodies : List Request) (references : List (List (List Request))) where
  noRootRequirements : signature.operations.rootRequirements.isEmpty = true
  actuals : List (Sigma (StaticOperation.Actual artifact.sources signature.context))
  originals : RuntimeInterval.Computed (RuntimeProviderHeaders.originalActuals signature.operations) actuals
  collection : @Collection artifact catalogue owner name signature actuals
  collected : RuntimeInterval.Computed (collect catalogue signature actuals bodies references) collection
  every : collection.entries.map (·.index) = List.finRange actuals.length

def prepare {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    {owner name : String} (signature : SourceRuntimeContext.Signature artifact.sources owner name)
    (bodies : List Request) (references : List (List (List Request))) :
    WorkM (Prepared catalogue signature bodies references) := do
  if noRootRequirements : signature.operations.rootRequirements.isEmpty = true then
    let actuals ← NaturalAffine.witness (RuntimeProviderHeaders.originalActuals signature.operations)
    let collection ← NaturalAffine.witness (collect catalogue signature actuals.val bodies references)
    if every : collection.val.entries.map (·.index) = List.finRange actuals.val.length then
      return ⟨noRootRequirements,actuals.val,by with_reducible exact actuals.property,collection.val,
        by with_reducible exact collection.property,every⟩
    else throw .request
  else throw .request

def Prepared.rows {artifact catalogue owner name signature bodies references}
    (prepared : @Prepared artifact catalogue owner name signature bodies references) : List SourceRows.Row :=
  signature.operations.sourceRows ++ prepared.collection.entries.flatMap Entry.rows

def Prepared.roots {artifact catalogue owner name signature bodies references}
    (prepared : @Prepared artifact catalogue owner name signature bodies references) : List Nat :=
  prepared.collection.entries.flatMap Entry.roots

/-- Only the two consumed queues change. Every other untrusted site/call field
is copied literally; the original full context remains on the enclosing call. -/
def Prepared.siteContext {artifact catalogue owner name signature bodies references}
    (prepared : @Prepared artifact catalogue owner name signature bodies references)
    (original : RuntimeContextRequest.Context) : RuntimeContextRequest.Context :=
  .withReferences original.positions original.sites original.calls original.branches
    prepared.collection.bodies prepared.collection.references original.staticIntervals

theorem Prepared.siteContext_bodies {artifact catalogue owner name signature bodies references}
    (prepared : @Prepared artifact catalogue owner name signature bodies references)
    (original : RuntimeContextRequest.Context) :
    (prepared.siteContext original).bodies = prepared.collection.bodies := rfl

theorem Prepared.siteContext_references {artifact catalogue owner name signature bodies references}
    (prepared : @Prepared artifact catalogue owner name signature bodies references)
    (original : RuntimeContextRequest.Context) :
    (prepared.siteContext original).references = prepared.collection.references := rfl

structure Realized {artifact catalogue owner name signature actuals}
    (entry : @Entry artifact catalogue owner name signature actuals) (root : Validity.Root) where
  checked : RuntimeOperationTree.Checked entry.graph root (required signature entry.actual.1.1)
  original : RuntimeInterval.Computed
    (RuntimeOperationTree.read entry.graph root (required signature entry.actual.1.1)) checked

private def consume {artifact catalogue owner name signature bodies references}
    (prepared : @Prepared artifact catalogue owner name signature bodies references) (root : Validity.Root) :
    WorkM (List (Σ entry : Entry catalogue signature prepared.actuals, Realized entry root)) :=
  prepared.collection.entries.mapM fun entry => do
    let checked ← NaturalAffine.witness
      (RuntimeOperationTree.read entry.graph root (required signature entry.actual.1.1))
    return ⟨entry,checked.val,by with_reducible exact checked.property⟩

structure Checked {artifact catalogue owner name signature bodies references}
    (prepared : @Prepared artifact catalogue owner name signature bodies references) (root : Validity.Root) where
  entries : List (Σ entry : Entry catalogue signature prepared.actuals, Realized entry root)
  consumed : RuntimeInterval.Computed (consume prepared root) entries
  every : entries.map (fun entry => entry.1.index) = List.finRange prepared.actuals.length

def read {artifact catalogue owner name signature bodies references}
    (prepared : @Prepared artifact catalogue owner name signature bodies references) (root : Validity.Root) :
    WorkM (Checked prepared root) := do
  let entries ← NaturalAffine.witness (consume prepared root)
  if every : entries.val.map (fun entry => entry.1.index) = List.finRange prepared.actuals.length then
    return ⟨entries.val,by with_reducible exact entries.property,every⟩
  else throw .request

end QleisliKernel.Qirf.RuntimeNamedSelectionPrefix
