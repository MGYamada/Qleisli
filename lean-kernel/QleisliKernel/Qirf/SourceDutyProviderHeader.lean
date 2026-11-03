import QleisliKernel.Qirf.SourceDutyProviderFresh
import QleisliKernel.SourceTypes.SourceRows

/-! Bind an eligible fresh source provider to its actual artifact subject.
The supplied fresh preparation's Original, graph and Body are retained exactly;
no source body or supplier is reconstructed under the provider's module. Roots
and authenticated query rows are only pre-final-graph discovery data. They do
not prove complete discovery, original body lowering, access, Meaning graph
transfer or the later same-final-root IR/code equations. No graph/root checker,
wire reader, accepted handle or producer slot count is used here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceDutyProviderHeader
open QleisliKernel Finite SourceTypes

structure Binding (artifact : Artifact) {catalogue record invocation demand view}
    {provider : @SourceDutySlots.Provider artifact.sources catalogue record invocation demand view}
    (prepared : SourceDutyProviderFresh.Checked provider) (request : RuntimeProviderHeader.Request) where
  retained : {header : RuntimeProviderHeader.Header artifact prepared.graph provider.closed.data.description.root request //
    header.original = prepared.original}
  computed : SourceDutySlots.Computed (RuntimeProviderHeader.readWithOriginal artifact prepared.original request) retained
  program : Semantics.Observation.Program
  originalProgram : artifact.programs[retained.val.subject.programIndex]? = some program

def Binding.header {artifact catalogue record invocation demand view provider prepared request}
    (binding : @Binding artifact catalogue record invocation demand view provider prepared request) := binding.retained.val

theorem Binding.sameOriginal {artifact catalogue record invocation demand view provider prepared request}
    (binding : @Binding artifact catalogue record invocation demand view provider prepared request) :
    binding.header.original = prepared.original := binding.retained.property

/-- Exact original duty/supplier/query rows, followed by the retained native
header's original body/type/argument rows. The catalogue itself grants no row. -/
def Binding.rawRows {artifact catalogue record invocation demand view provider prepared request}
    (binding : @Binding artifact catalogue record invocation demand view provider prepared request) : List SourceRows.Row :=
  let supplier := provider.supplier.origin
  demand.source.original.sourceRows ++
    [(supplier.state.owner,supplier.state.prepared.original.envelope.source)] ++ supplier.rows ++
    CallName.sourceRows provider.candidate ++ binding.header.rows

/-- Preserve the concrete forward subject's complete root list, including its
evidence node when present. This does not assert the final graph is checked. -/
def Binding.roots {artifact catalogue record invocation demand view provider prepared request}
    (binding : @Binding artifact catalogue record invocation demand view provider prepared request) : List Nat :=
  binding.header.roots

structure Checked (artifact : Artifact) {catalogue record invocation demand view}
    {provider : @SourceDutySlots.Provider artifact.sources catalogue record invocation demand view}
    (prepared : SourceDutyProviderFresh.Checked provider) (request : RuntimeProviderHeader.Request) where
  binding : Binding artifact prepared request
  relevance : SourceRows.Retained binding.rawRows

def Checked.rows {artifact catalogue record invocation demand view provider prepared request}
    (checked : @Checked artifact catalogue record invocation demand view provider prepared request) : List SourceRows.Row :=
  checked.relevance.rows

def Checked.roots {artifact catalogue record invocation demand view provider prepared request}
    (checked : @Checked artifact catalogue record invocation demand view provider prepared request) : List Nat :=
  checked.binding.roots

/-- Artifact/header preparation only. Body-context traversal, every J/C/M
obligation and all actual final-dependency IR equations are still pending. The
retained request context is not treated as already consumed source evidence. -/
def read (artifact : Artifact) {catalogue record invocation demand view}
    {provider : @SourceDutySlots.Provider artifact.sources catalogue record invocation demand view}
    (prepared : SourceDutyProviderFresh.Checked provider) (request : RuntimeProviderHeader.Request) :
    WorkM (Checked artifact prepared request) := do
  let retained ← NaturalAffine.witness (RuntimeProviderHeader.readWithOriginal artifact prepared.original request)
  exactWork (Exact.charge 8)
  match originalProgram : artifact.programs[retained.val.val.subject.programIndex]? with
  | none => throw .request
  | some program =>
    let binding : Binding artifact prepared request :=
      ⟨retained.val,by with_reducible exact retained.property,program,originalProgram⟩
    let body := prepared.original.body.checked
    -- Precharge the original source/event/query traversal used to form rows.
    -- SourceRows.read separately charges every exact row-byte comparison; its
    -- sharing changes no provider, assertion, source query or body occurrence.
    exactWork (Exact.charge (16*(body.signature.original.occurrence.body.length+body.events.length+
      prepared.graph.results.length+demand.source.original.origin.rows.length+
      provider.supplier.origin.rows.length+1)^2))
    let relevance ← SourceRows.read binding.rawRows
    return ⟨binding,relevance⟩

end QleisliKernel.Qirf.SourceDutyProviderHeader
