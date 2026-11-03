import QleisliKernel.Qirf.SourceDutyProviderHeader
import QleisliKernel.Qirf.RuntimeProviderPaths
import QleisliKernel.Qirf.RuntimeBodyDiscovery
import QleisliKernel.Qirf.RuntimePureBody

/-! Consume bounded nongeneric provider bodies under one retained final graph.
Discovery uses the same original Body/context before that graph. Contributions
retain their source occurrences in order; rows come only from actual discovery
and bound source headers. The final graph is supplied with its actual complete
checkRootFromRoots run, never reconstructed here. Every contribution then runs
the unchanged demanded-path checker and the common original body checker on
that same dependency vector and literal program. No supplied owner map or
prepared result substitutes for those computations. This consumes provider
bodies only: full Meaning graph transfer/equality, other operation-tree/source
obligations and production execution authority remain separate. General and
unsupported body forms retain the existing explicit refusals; no wire changes.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceDutyProviderBody
open QleisliKernel Finite SourceTypes

structure Discovered {artifact catalogue record invocation demand view provider prepared request}
    (header : @SourceDutyProviderHeader.Checked artifact catalogue record invocation demand view provider prepared request) where
  nongeneric : header.binding.header.original.supplied.provider.signature.original.parsedHeader.staticTokens.isNone = true
  discovery : RuntimeBodyDiscovery.Discovery
  original : SourceDutySlots.Computed (RuntimeBodyDiscovery.visit artifact 128
    header.binding.header.original.body.checked.signature header.binding.header.original.body.checked.events
    header.binding.header.original.body.checked.summary.staticRows request.2 true) discovery
  relevance : SourceRows.Retained (header.rows ++ discovery.rows)

def Discovered.rows {artifact catalogue record invocation demand view provider prepared request header}
    (source : @Discovered artifact catalogue record invocation demand view provider prepared request header) : List SourceRows.Row :=
  source.relevance.rows

def Discovered.roots {artifact catalogue record invocation demand view provider prepared request header}
    (source : @Discovered artifact catalogue record invocation demand view provider prepared request header) : List Nat :=
  header.roots ++ source.discovery.roots

/-- No source body is reread at the top boundary. The existing discovery
traversal retains all nested original query/subject obligations before the
caller checks the graph; unsupported nested forms refuse there. -/
def discover {artifact catalogue record invocation demand view provider prepared request}
    (header : @SourceDutyProviderHeader.Checked artifact catalogue record invocation demand view provider prepared request) :
    WorkM (Discovered header) := do
  if nongeneric : header.binding.header.original.supplied.provider.signature.original.parsedHeader.staticTokens.isNone = true then
    let body := header.binding.header.original.body.checked
    let discovery ← NaturalAffine.witness
      (RuntimeBodyDiscovery.visit artifact 128 body.signature body.events body.summary.staticRows request.2 true)
    let relevance ← SourceRows.read (header.rows ++ discovery.val.rows)
    return ⟨nongeneric,discovery.val,by with_reducible exact discovery.property,relevance⟩
  else throw .request

/-- A source contribution can only contain an actually discovered bound
provider. There is no arbitrary source-row list or numeric body-count input. -/
inductive Contribution (artifact : Artifact) where
  | provider {catalogue record invocation demand view provider prepared request}
      {header : @SourceDutyProviderHeader.Checked artifact catalogue record invocation demand view provider prepared request}
      (source : Discovered header)

def Contribution.rows {artifact} : Contribution artifact → List SourceRows.Row
  | .provider source => source.rows

def Contribution.roots {artifact} : Contribution artifact → List Nat
  | .provider source => source.roots

/-- This is a retained graph computation, not a graph checker. Its rows and
roots are derived from the complete ordered contribution list. The list does
not assert coverage of other catalogue duties, which remain mandatory elsewhere.
This provider-only graph still needs composition with genuinely retained
selected-root/body-discovery rows and roots for a whole runtime route. Omitted
selected-root dependencies gain no relevance or authorization here.
Only graph root indices are shared; body occurrences are never deduplicated. -/
structure Final (artifact : Artifact) where
  contributions : List (Contribution artifact)
  order : Array Nat
  root : Validity.Root
  original : SourceDutySlots.Computed (Validity.checkRootFromRoots artifact order
    (contributions.flatMap Contribution.rows)
    ((artifact.root :: contributions.flatMap Contribution.roots).eraseDups)) root

structure Checked {artifact catalogue record invocation demand view provider prepared request header}
    (source : @Discovered artifact catalogue record invocation demand view provider prepared request header)
    (root : Validity.Root) where
  paths : RuntimeProviderPaths.Checked header.binding.header root view.requested
  pathRead : SourceDutySlots.Computed (RuntimeProviderPaths.read header.binding.header root view.requested) paths
  sameProgram : paths.ir.original.program = header.binding.program
  initial : RuntimeOwnerMap.Map
  initialRead : SourceDutySlots.Computed (RuntimeSourceBoundary.bindings
    (header.binding.header.original.body.checked.summary.parameterValues.flatMap SourceRuntimeValues.valueOwners)
    [(⟨paths.ir.original.prepared.ports.input,paths.ir.original.prepared.ports.domain⟩ : Semantics.CarrierInterface.Owner)]) initial
  prepared : RuntimeInterval.Prepared root.dependencies paths.ir.original.program
  preparation : SourceDutySlots.Computed (RuntimeInterval.prepare root.dependencies paths.ir.original.program) prepared
  body : RuntimePureBody.Checked artifact root header.binding.header.original.body paths.ir.original.program request.2 initial
  consumed : SourceDutySlots.Computed (RuntimePureBody.checkPrepared artifact root header.binding.header.original.body
    paths.ir.original.program request.2 initial prepared) body

private def consume {artifact catalogue record invocation demand view provider prepared request header}
    (source : @Discovered artifact catalogue record invocation demand view provider prepared request header)
    (root : Validity.Root) : WorkM (Checked source root) := do
  let paths ← NaturalAffine.witness (RuntimeProviderPaths.read header.binding.header root view.requested)
  let native := paths.val
  have sameProgram : native.ir.original.program = header.binding.program :=
    Option.some.inj (native.ir.original.original.symm.trans header.binding.originalProgram)
  let body := header.binding.header.original.body
  let roles := body.checked.summary.parameterValues.flatMap SourceRuntimeValues.valueOwners
  let owner : Semantics.CarrierInterface.Owner :=
    ⟨native.ir.original.prepared.ports.input,native.ir.original.prepared.ports.domain⟩
  let initial ← NaturalAffine.witness (RuntimeSourceBoundary.bindings roles [owner])
  let prepared ← NaturalAffine.witness (RuntimeInterval.prepare root.dependencies native.ir.original.program)
  let checked ← NaturalAffine.witness (RuntimePureBody.checkPrepared artifact root body
    native.ir.original.program request.2 initial.val prepared.val)
  return ⟨paths.val,by with_reducible exact paths.property,sameProgram,initial.val,by with_reducible exact initial.property,
    prepared.val,by with_reducible exact prepared.property,checked.val,by with_reducible exact checked.property⟩

def Result {artifact} (root : Validity.Root) : Contribution artifact → Type
  | .provider source => Checked source root

private def consumeContribution {artifact} (root : Validity.Root) (contribution : Contribution artifact) :
    WorkM (Result root contribution) := do
  match contribution with
  | .provider source => consume source root

structure Entry {artifact} (final : Final artifact) where
  index : Fin final.contributions.length
  result : Result final.root (final.contributions[index.val]'index.isLt)
  original : SourceDutySlots.Computed
    (consumeContribution final.root (final.contributions[index.val]'index.isLt)) result

structure All {artifact} (final : Final artifact) where
  entries : List (Entry final)
  every : entries.map (·.index) = List.finRange final.contributions.length

/-- Every ordered contribution consumes its own original context/body and its
unaltered per-occurrence access demand under the exact same final root. Source
M/full-graph obligations are not consumed or credited by this body result. -/
def read {artifact} (final : Final artifact) : WorkM (All final) := do
  exactWork (Exact.charge (32*(final.contributions.length+1)^2))
  let entries ← (List.finRange final.contributions.length).mapM fun index => do
    let checked ← NaturalAffine.witness (consumeContribution final.root (final.contributions[index.val]'index.isLt))
    return (⟨index,checked.val,by with_reducible exact checked.property⟩ : Entry final)
  if every : entries.map (·.index) = List.finRange final.contributions.length then
    return ⟨entries,every⟩
  else throw .request

end QleisliKernel.Qirf.SourceDutyProviderBody
