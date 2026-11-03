import QleisliKernel.Qirf.RuntimeProviderAction
import QleisliKernel.Qirf.RuntimeBodyDiscovery
import QleisliKernel.Qirf.SourceDutySlots

/-! Forward quantum-reference bodies of an actual original Meaning graph.
The graph/node index authenticates the reference's original caller and effect
metadata. A canonical provider description is an untrusted adapter checked by
the existing reader; no signature, Body, scope or invocation is fabricated.
Discovery precedes the enclosing single final graph, and the unchanged path
and common Body checks consume that same root and literal program.
This component proves no full request/graph transfer or subject/M equation,
grants no inverse/control access or handle, and does not enable a dispatcher.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceMeaningQuantum
open QleisliKernel Finite SourceTypes

/-- The complete genuine Checked read, rather than a freely supplied reference
record, authenticates every source/effect/context field of this occurrence. -/
structure At {sources caller owner name} (meaning : SourceMeaning.Checked sources caller owner name) where
  index : Fin meaning.graph.nodes.length
  reference : SourceMeaning.QuantumReference sources
  original : (meaning.graph.nodes[index.val]'index.isLt).action = .reference reference

def At.node {sources caller owner name meaning}
    (referenceSite : @At sources caller owner name meaning) : SourceMeaning.Node sources :=
  meaning.graph.nodes[referenceSite.index.val]'referenceSite.index.isLt

def At.rows {sources caller owner name meaning} (referenceSite : @At sources caller owner name meaning) :
    List SourceRows.Row :=
  [(referenceSite.node.owner,referenceSite.node.original.source)] ++ referenceSite.node.input.sourceRows ++
    referenceSite.node.output.sourceRows ++ referenceSite.node.queryRows

/-- This exact fresh-graph reference keeps its own occurrence index even when
another reference resolves to the same function or proposed native subject. -/
def fromDuty {sources catalogue record invocation demand request}
    {meaning : @SourceDutySlots.Meaning sources catalogue record invocation demand request}
    (reference : SourceDutySlots.QuantumReference meaning) : At meaning.selected.meaning :=
  ⟨reference.index,reference.reference,reference.original⟩

def description {sources} (reference : SourceMeaning.QuantumReference sources) : OperationDescription.Description :=
  ⟨[.provider reference.resolution.result.moduleName reference.resolution.result.declaration.name [] [] []],0⟩

private abbrev SameReference {sources caller owner name meaning}
    (referenceSite : @At sources caller owner name meaning)
    {graph : StaticOperation.CheckedGraph sources (.source referenceSite.reference.caller) (description referenceSite.reference)}
    (original : RuntimeProviderHeader.Original graph 0) : Prop :=
  let provider := original.supplied.provider
  let reference := referenceSite.reference
  provider.moduleName = reference.resolution.result.moduleName ∧
    provider.declarationName = reference.resolution.result.declaration.name ∧
    provider.signature.original.source = reference.signature.original.source ∧
    provider.signature.original.declaration = reference.signature.original.declaration ∧
    provider.signature.original.occurrence = reference.signature.original.occurrence ∧
    provider.signature.inputs = reference.signature.inputs ∧
    provider.signature.outputs = reference.signature.outputs ∧
    reference.signature.inputs = [referenceSite.node.input.basis] ∧
    reference.signature.outputs = [referenceSite.node.output.basis] ∧
    provider.signature.parts = reference.signature.parts ∧
    provider.signature.staticArguments = ({} : StaticTypes.Arguments) ∧
    reference.signature.staticArguments = ({} : StaticTypes.Arguments) ∧
    provider.expectedEffect = reference.expectedEffect ∧
    provider.internalInference = reference.internalInference ∧
    original.supplied.context = .source reference.caller ∧ reference.caller = referenceSite.node.owner

structure Original (artifact : Artifact) {caller owner name meaning}
    (referenceSite : @At artifact.sources caller owner name meaning) where
  graph : StaticOperation.CheckedGraph artifact.sources (.source referenceSite.reference.caller) (description referenceSite.reference)
  graphRead : SourceDutySlots.Computed
    (StaticOperation.check artifact.sources (.source referenceSite.reference.caller) (description referenceSite.reference)) graph
  providerSource : RuntimeProviderHeader.Original graph 0
  sourceRead : SourceDutySlots.Computed (RuntimeProviderHeader.readOriginal graph 0) providerSource
  bound : SameReference referenceSite providerSource

/-- The admitted reference syntax has no static argument list. Both genuine
readers must retain the exact empty instance; an unused actual cannot disappear
through this adapter if that syntax is extended later. -/
def readOriginal (artifact : Artifact) {caller owner name meaning}
    (referenceSite : @At artifact.sources caller owner name meaning) : WorkM (Original artifact referenceSite) := do
  let graph ← NaturalAffine.witness
    (StaticOperation.check artifact.sources (.source referenceSite.reference.caller) (description referenceSite.reference))
  let original ← NaturalAffine.witness (RuntimeProviderHeader.readOriginal graph.val 0)
  let provider := original.val.supplied.provider
  let reference := referenceSite.reference
  -- Exact source/declaration/occurrence and two-port comparisons examine these
  -- actual bytes/trees. Empty-argument tests only inspect list constructors.
  exactWork (Exact.charge (32*(provider.signature.original.source.utf8ByteSize+
    reference.signature.original.source.utf8ByteSize+provider.moduleName.utf8ByteSize+
    provider.declarationName.utf8ByteSize+reference.caller.utf8ByteSize+referenceSite.node.owner.utf8ByteSize+
    Raw.OwnerFlow.fields ((provider.signature.inputs ++ provider.signature.outputs ++
      reference.signature.inputs ++ reference.signature.outputs ++
      [referenceSite.node.input.basis,referenceSite.node.output.basis]).map fun basis => ⟨0,basis⟩)+1)))
  if bound : SameReference referenceSite original.val then
    return ⟨graph.val,by with_reducible exact graph.property,original.val,
      by with_reducible exact original.property,bound⟩
  else throw .request

structure Prepared (artifact : Artifact) {caller owner name meaning}
    (referenceSite : @At artifact.sources caller owner name meaning) (request : RuntimeProviderHeader.Request) where
  original : Original artifact referenceSite
  originalRead : SourceDutySlots.Computed (readOriginal artifact referenceSite) original
  header : {header : RuntimeProviderHeader.Header artifact original.graph 0 request //
    header.original = original.providerSource}
  headerRead : SourceDutySlots.Computed
    (RuntimeProviderHeader.readWithOriginal artifact original.providerSource request) header
  discovery : RuntimeBodyDiscovery.Discovery
  discovered : SourceDutySlots.Computed (RuntimeBodyDiscovery.visit artifact 128
    header.val.original.body.checked.signature header.val.original.body.checked.events
    header.val.original.body.checked.summary.staticRows request.2 true) discovery
  relevance : SourceRows.Retained (referenceSite.rows ++ header.val.rows ++ discovery.rows)

def Prepared.rows {artifact caller owner name meaning referenceSite request}
    (prepared : @Prepared artifact caller owner name meaning referenceSite request) : List SourceRows.Row :=
  prepared.relevance.rows

def Prepared.roots {artifact caller owner name meaning referenceSite request}
    (prepared : @Prepared artifact caller owner name meaning referenceSite request) : List Nat :=
  prepared.header.val.roots ++ prepared.discovery.roots

/-- Retain the actual original/reference/header/discovery runs once before the
enclosing graph. These rows are actual query closures, never catalogue-wide
relevance or a body equation. No final graph is checked by this function. -/
def prepare (artifact : Artifact) {caller owner name meaning}
    (referenceSite : @At artifact.sources caller owner name meaning) (request : RuntimeProviderHeader.Request) :
    WorkM (Prepared artifact referenceSite request) := do
  let original ← NaturalAffine.witness (readOriginal artifact referenceSite)
  let header ← NaturalAffine.witness
    (RuntimeProviderHeader.readWithOriginal artifact original.val.providerSource request)
  let body := header.val.val.original.body.checked
  let discovery ← NaturalAffine.witness (RuntimeBodyDiscovery.visit artifact 128 body.signature body.events
    body.summary.staticRows request.2 true)
  let relevance ← SourceRows.read (referenceSite.rows ++ header.val.val.rows ++ discovery.val.rows)
  return ⟨original.val,by with_reducible exact original.property,header.val,
    by with_reducible exact header.property,discovery.val,by with_reducible exact discovery.property,relevance⟩

def forward : OperationPaths.Paths := ⟨true,false,false⟩

abbrev Checked {artifact caller owner name meaning referenceSite request}
    (prepared : @Prepared artifact caller owner name meaning referenceSite request) (root : Validity.Root) :=
  RuntimeProviderAction.Checked prepared.header.val root forward

/-- Consume this exact forward reference at the caller's SAME final root.
Independent original/closed effect gates reject hidden observation. The checked
body cannot be replaced by a structurally unitary map or matching Gram data.
The enclosing M consumer still owes its full graph and subject equation. -/
def read {artifact caller owner name meaning referenceSite request}
    (prepared : @Prepared artifact caller owner name meaning referenceSite request) (root : Validity.Root) :
    WorkM (Checked prepared root) :=
  RuntimeProviderAction.read prepared.header.val root forward

def Checked.action {artifact caller owner name meaning referenceSite request prepared root}
    (checked : @Checked artifact caller owner name meaning referenceSite request prepared root) : Semantics.Exact.Matrix :=
  RuntimeProviderAction.Checked.action checked

end QleisliKernel.Qirf.SourceMeaningQuantum
