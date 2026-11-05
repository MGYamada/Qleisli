import QleisliKernel.Qirf.SourceDutyProviderHeader
import QleisliKernel.Qirf.RuntimeProviderAction
import QleisliKernel.Qirf.RuntimeBodyDiscovery

/-! Consume bounded authenticated provider bodies under one retained final graph.
Nongeneric and source-bound Basis/Nat applications keep separate eligibility.
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

inductive Eligibility {artifact catalogue record invocation demand view provider prepared request}
    (header : @SourceDutyProviderHeader.Checked artifact catalogue record invocation demand view provider prepared request) : Type where
  | nongeneric (original : header.binding.header.original.supplied.provider.signature.original.parsedHeader.staticTokens.isNone = true)
  | applied (source : SourceDutyProviderApplied.Checked provider)
      (sameSource : prepared.provenance = .applied source)

structure Discovered {artifact catalogue record invocation demand view provider prepared request}
    (header : @SourceDutyProviderHeader.Checked artifact catalogue record invocation demand view provider prepared request) where
  eligibility : Eligibility header
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
  let eligibility : Eligibility header ←
    if nongeneric : header.binding.header.original.supplied.provider.signature.original.parsedHeader.staticTokens.isNone = true then
      pure (.nongeneric nongeneric)
    else match provenance : prepared.provenance with
      | .applied source => pure (.applied source provenance)
      | .fresh _ | .bare _ => throw .request
  let body := header.binding.header.original.body.checked
  let discovery ← NaturalAffine.witness
    (RuntimeBodyDiscovery.visit artifact 128 body.signature body.events body.summary.staticRows request.2 true)
  let relevance ← SourceRows.read (header.rows ++ discovery.val.rows)
  return ⟨eligibility,discovery.val,by with_reducible exact discovery.property,relevance⟩

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

/-- One original bare provider occurrence prepared for the existing body
consumer. These are actual source/header/discovery runs, not a producer slot
count or a proof of the remaining body, path or Meaning equations. -/
structure BarePrepared (artifact : Artifact) {catalogue record invocation demand view}
    (provider : @SourceDutySlots.Provider artifact.sources catalogue record invocation demand view)
    (request : RuntimeProviderHeader.Request) where
  prepared : SourceDutyProviderFresh.Checked provider
  preparedRead : SourceDutySlots.Computed (SourceDutyProviderFresh.readBare provider) prepared
  header : SourceDutyProviderHeader.Checked artifact prepared request
  headerRead : SourceDutySlots.Computed (SourceDutyProviderHeader.read artifact prepared request) header
  source : Discovered header
  discovered : SourceDutySlots.Computed (discover header) source

/-- Preserve this exact occurrence when assembling the ordered contribution
list before the one final graph. No equal-name/matrix/body sharing is implied.
-/
def BarePrepared.contribution {artifact catalogue record invocation demand view provider request}
    (prepared : @BarePrepared artifact catalogue record invocation demand view provider request) : Contribution artifact :=
  .provider prepared.source

/-- The explicit authenticated bare branch, bound to its requested forward
subject and original context. The same retained Body is discovered once; it is
not reread under a later callee module. Final graph checking and the unchanged
per-occurrence path/body consumer remain the caller's next stages. -/
def prepareBare (artifact : Artifact) {catalogue record invocation demand view}
    (provider : @SourceDutySlots.Provider artifact.sources catalogue record invocation demand view)
    (request : RuntimeProviderHeader.Request) : WorkM (BarePrepared artifact provider request) := do
  let prepared ← NaturalAffine.witness (SourceDutyProviderFresh.readBare provider)
  let header ← NaturalAffine.witness (SourceDutyProviderHeader.read artifact prepared.val request)
  let source ← NaturalAffine.witness (discover header.val)
  return ⟨prepared.val,by with_reducible exact prepared.property,
    header.val,by with_reducible exact header.property,source.val,by with_reducible exact source.property⟩

/-- The Basis/Nat path retains the exact source-selected original and uses
the same discovery and same-final-root body consumer as the bare path. -/
structure AppliedPrepared (artifact : Artifact) {catalogue record invocation demand view}
    (provider : @SourceDutySlots.Provider artifact.sources catalogue record invocation demand view)
    (request : RuntimeProviderHeader.Request) where
  prepared : SourceDutyProviderFresh.Checked provider
  preparedRead : SourceDutySlots.Computed (SourceDutyProviderFresh.readApplied provider) prepared
  header : SourceDutyProviderHeader.Checked artifact prepared request
  headerRead : SourceDutySlots.Computed (SourceDutyProviderHeader.read artifact prepared request) header
  source : Discovered header
  discovered : SourceDutySlots.Computed (discover header) source

def AppliedPrepared.contribution {artifact catalogue record invocation demand view provider request}
    (prepared : @AppliedPrepared artifact catalogue record invocation demand view provider request) : Contribution artifact :=
  .provider prepared.source

def prepareApplied (artifact : Artifact) {catalogue record invocation demand view}
    (provider : @SourceDutySlots.Provider artifact.sources catalogue record invocation demand view)
    (request : RuntimeProviderHeader.Request) : WorkM (AppliedPrepared artifact provider request) := do
  let prepared ← NaturalAffine.witness (SourceDutyProviderFresh.readApplied provider)
  let header ← NaturalAffine.witness (SourceDutyProviderHeader.read artifact prepared.val request)
  let source ← NaturalAffine.witness (discover header.val)
  return ⟨prepared.val,by with_reducible exact prepared.property,
    header.val,by with_reducible exact header.property,source.val,by with_reducible exact source.property⟩

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
  let checked ← RuntimeProviderAction.read header.binding.header root view.requested
  have sameProgram : checked.paths.ir.original.program = header.binding.program :=
    Option.some.inj (checked.paths.ir.original.original.symm.trans header.binding.originalProgram)
  return ⟨checked.paths,checked.pathRead,sameProgram,checked.initial,checked.initialRead,
    checked.interval,checked.intervalRead,checked.body,checked.consumed⟩

def Result {artifact} (root : Validity.Root) : Contribution artifact → Type
  | .provider source => Checked source root

private def consumeContribution {artifact} (root : Validity.Root) (contribution : Contribution artifact) :
    WorkM (Result root contribution) := do
  match contribution with
  | .provider source => consume source root

structure EntryAt {artifact} (contributions : List (Contribution artifact)) (root : Validity.Root) where
  index : Fin contributions.length
  result : Result root (contributions[index.val]'index.isLt)
  original : SourceDutySlots.Computed
    (consumeContribution root (contributions[index.val]'index.isLt)) result

structure AllAt {artifact} (contributions : List (Contribution artifact)) (root : Validity.Root) where
  entries : List (EntryAt contributions root)
  every : entries.map (·.index) = List.finRange contributions.length

abbrev Entry {artifact} (final : Final artifact) := EntryAt final.contributions final.root
abbrev All {artifact} (final : Final artifact) := AllAt final.contributions final.root

/-- Every ordered contribution consumes its own original context/body and its
unaltered per-occurrence access demand under the exact same final root. Source
M/full-graph obligations are not consumed or credited by this body result. -/
def readAt {artifact} (contributions : List (Contribution artifact)) (root : Validity.Root) :
    WorkM (AllAt contributions root) := do
  exactWork (Exact.charge (32*(contributions.length+1)^2))
  let entries ← (List.finRange contributions.length).mapM fun index => do
    let checked ← NaturalAffine.witness (consumeContribution root (contributions[index.val]'index.isLt))
    return (⟨index,checked.val,by with_reducible exact checked.property⟩ : EntryAt contributions root)
  if every : entries.map (·.index) = List.finRange contributions.length then
    return ⟨entries,every⟩
  else throw .request

def read {artifact} (final : Final artifact) : WorkM (All final) := readAt final.contributions final.root

end QleisliKernel.Qirf.SourceDutyProviderBody
