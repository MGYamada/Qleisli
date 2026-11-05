import QleisliKernel.Qirf.SourceDutyProviderBody

/-! Internal preparation of every concrete provider in one exact original-duty
plan. Entry and provider ordinals retain actual immutable list/array bindings;
header references retain their canonical HeaderLink and add no duplicate slot.
The original conditional views, Meaning/reference templates, runtime-group
markers and pending obligations remain attached. Unsupported concrete supplier
or context preparation fails; it is never silently omitted.
This is a provider subset, not complete original-duty or runtime acceptance.
External root actuals, recursive families, general suppliers, Meaning graph
transfer/equations, reference bodies and selected-root discovery remain separate.
No root/handle/wire reader or Plan.bodyOrder-to-wire conversion is introduced.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceDutyProviderLedger
open QleisliKernel Finite SourceTypes
open GenericDutyQueue

/-- One real conversion, reused for every ordinal. These indices confer no
source relevance or authority beyond the exact original list equality. -/
structure Indexed {α : Type} (values : List α) where
  array : Array α
  converted : array = values.toArray
  indices : List (Fin values.length)
  every : indices = List.finRange values.length

def Indexed.at {α values} (indexed : @Indexed α values) (index : Fin values.length) : α :=
  indexed.array[index.val]'(by simpa only [indexed.converted,List.size_toArray] using index.isLt)

theorem Indexed.at_original {α values} (indexed : @Indexed α values) (index : Fin values.length) :
    indexed.at index = values[index.val]'index.isLt := by
  simp only [Indexed.at,indexed.converted,List.getElem_toArray]

private def readIndexed {α : Type} (values : List α) : WorkM (Indexed values) := do
  -- Length, array conversion and ordinal generation each traverse this list
  -- once. Later source/provider lookups use the array, including empty roots.
  exactWork (Exact.charge (16*(values.length+1)))
  return ⟨values.toArray,rfl,List.finRange values.length,rfl⟩

abbrev ProviderRequests {sources catalogue record invocation demand}
    (planned : @SourceDutySlots.DemandPlan sources catalogue record invocation demand) :=
  (index : Fin planned.providers.length) → (provider : Sigma (SourceDutySlots.Provider demand)) →
    provider = planned.providers[index.val]'index.isLt → RuntimeProviderHeader.Request

/-- Request values remain untrusted forward subjects and literal contexts.
Their count/order comes from the native original plan, never a supplied count.
The callback grants no source, body, path or Meaning success receipt. -/
def ItemRequests {sources} {catalogue : GenericCatalogue.Checked sources}
    (queue : GenericDutyQueue.Checked catalogue) (item : GenericDutyQueue.Item catalogue) :
    SourceDutySlots.ItemExpectation queue item → Type :=
  match item with
  | .demand _ _ => fun planned => ProviderRequests planned
  | .header .. | .call .. => fun _ => Unit
  | .pendingRecursion .. => fun _ => Empty

abbrev Requests {sources catalogue queue} (plan : @SourceDutySlots.Plan sources catalogue queue) :=
  (entry : SourceDutySlots.Entry plan.indexed) → ItemRequests queue entry.subject entry.subjectExpectation

inductive Branch where
  | bare
  | applied
  deriving BEq, DecidableEq, Repr

/-- The original retained source syntax selects the explicit preparation.
No caller flag, closed type coincidence or failed reader chooses a branch. -/
def branchOf {sources catalogue record invocation demand view}
    (provider : @SourceDutySlots.Provider sources catalogue record invocation demand view) : Branch :=
  match provider.written with | .name _ => .bare | .application _ => .applied

inductive Preparation (artifact : Artifact) {catalogue record invocation demand view}
    (provider : @SourceDutySlots.Provider artifact.sources catalogue record invocation demand view)
    (request : RuntimeProviderHeader.Request) : Type where
  | bare (original : branchOf provider = .bare)
      (prepared : SourceDutyProviderBody.BarePrepared artifact provider request)
      (computed : SourceDutySlots.Computed (SourceDutyProviderBody.prepareBare artifact provider request) prepared)
  | applied (original : branchOf provider = .applied)
      (prepared : SourceDutyProviderBody.AppliedPrepared artifact provider request)
      (computed : SourceDutySlots.Computed (SourceDutyProviderBody.prepareApplied artifact provider request) prepared)

def Preparation.branch {artifact catalogue record invocation demand view provider request} :
    @Preparation artifact catalogue record invocation demand view provider request → Branch
  | .bare .. => .bare
  | .applied .. => .applied

theorem Preparation.originalBranch {artifact catalogue record invocation demand view provider request}
    (prepared : @Preparation artifact catalogue record invocation demand view provider request) :
    prepared.branch = branchOf provider := by
  cases prepared with
  | bare original _ _ => exact original.symm
  | applied original _ _ => exact original.symm

def Preparation.contribution {artifact catalogue record invocation demand view provider request} :
    @Preparation artifact catalogue record invocation demand view provider request → SourceDutyProviderBody.Contribution artifact
  | .bare _ prepared _ => prepared.contribution
  | .applied _ prepared _ => prepared.contribution

/-- Both branches retain their actual source/header/discovery runs. Any
unsupported concrete provider refuses in its selected branch; errors never
retry another preparation and no source occurrence is omitted. -/
def readPreparation (artifact : Artifact) {catalogue record invocation demand view}
    (provider : @SourceDutySlots.Provider artifact.sources catalogue record invocation demand view)
    (request : RuntimeProviderHeader.Request) : WorkM (Preparation artifact provider request) := do
  exactWork (Exact.charge 4)
  match original : branchOf provider with
  | .bare =>
    let prepared ← NaturalAffine.witness (SourceDutyProviderBody.prepareBare artifact provider request)
    return .bare original prepared.val (by with_reducible exact prepared.property)
  | .applied =>
    let prepared ← NaturalAffine.witness (SourceDutyProviderBody.prepareApplied artifact provider request)
    return .applied original prepared.val (by with_reducible exact prepared.property)

structure ProviderPrepared (artifact : Artifact) {catalogue record invocation demand}
    (planned : @SourceDutySlots.DemandPlan artifact.sources catalogue record invocation demand) where
  index : Fin planned.providers.length
  provider : Sigma (SourceDutySlots.Provider demand)
  atIndex : provider = planned.providers[index.val]'index.isLt
  request : RuntimeProviderHeader.Request
  prepared : Preparation artifact provider.2 request
  computed : SourceDutySlots.Computed (readPreparation artifact provider.2 request) prepared

def ProviderPrepared.contribution {artifact catalogue record invocation demand planned}
    (source : @ProviderPrepared artifact catalogue record invocation demand planned) :
    SourceDutyProviderBody.Contribution artifact := source.prepared.contribution

private def conditionalViews {sources catalogue record invocation demand}
    (planned : @SourceDutySlots.DemandPlan sources catalogue record invocation demand) :
    List (List Nat × List GenericOperation.Key) :=
  planned.views.filterMap fun view => match view.status with
    | .closed _ => none
    | .conditional keys _ _ => some (view.path,keys)

/-- These are the original pending duties, not duties inferred from a prepared
body or a matching matrix. Open parents retain each closed provider sibling in
the separate every-provider list, including unused and zero-power children. -/
structure Residual {sources catalogue record invocation demand}
    (planned : @SourceDutySlots.DemandPlan sources catalogue record invocation demand) where
  conditional : List (List Nat × List GenericOperation.Key)
  originalConditional : conditional = conditionalViews planned
  pending : List SourceDutySlots.Pending
  originalPending : pending = planned.pending

def Residual.meaning {sources catalogue record invocation demand planned}
    (_residual : @Residual sources catalogue record invocation demand planned) := planned.meaning

def Residual.runtimeApplication {sources catalogue record invocation demand planned}
    (_residual : @Residual sources catalogue record invocation demand planned) := demand.source.original.runtimeApplication

structure DemandPrepared (artifact : Artifact) {catalogue record invocation demand}
    (planned : @SourceDutySlots.DemandPlan artifact.sources catalogue record invocation demand) where
  indexed : Indexed planned.providers
  indexing : SourceDutySlots.Computed (readIndexed planned.providers) indexed
  providers : List (ProviderPrepared artifact planned)
  every : providers.map (·.index) = List.finRange planned.providers.length
  residual : Residual planned

private def readDemand (artifact : Artifact) {catalogue record invocation demand}
    (planned : @SourceDutySlots.DemandPlan artifact.sources catalogue record invocation demand)
    (requests : ProviderRequests planned) : WorkM (DemandPrepared artifact planned) := do
  let indexed ← NaturalAffine.witness (readIndexed planned.providers)
  -- Filtering statuses and copying paths/keys traverses only these list spines;
  -- it does not compare or copy source snapshots stored in the original data.
  exactWork (Exact.charge (16*(planned.providers.length+planned.views.length+
    (planned.views.map fun view => view.path.length+1).sum+planned.pending.length+1)))
  let providers ← indexed.val.indices.mapM fun index => do
    let provider := indexed.val.at index
    have atIndex := indexed.val.at_original index
    let request := requests index provider atIndex
    let prepared ← NaturalAffine.witness (readPreparation artifact provider.2 request)
    return (⟨index,provider,atIndex,request,prepared.val,by with_reducible exact prepared.property⟩ :
      ProviderPrepared artifact planned)
  if every : providers.map (·.index) = indexed.val.indices then
    return ⟨indexed.val,by with_reducible exact indexed.property,providers,every.trans indexed.val.every,
      ⟨conditionalViews planned,rfl,planned.pending,rfl⟩⟩
  else throw .request

inductive ItemPrepared (artifact : Artifact) {catalogue : GenericCatalogue.Checked artifact.sources}
    (queue : GenericDutyQueue.Checked catalogue) :
    (item : GenericDutyQueue.Item catalogue) → SourceDutySlots.ItemExpectation queue item → Type where
  | demand {record} (invocation : Invocation catalogue record) (demand : Demand invocation)
      (planned : SourceDutySlots.DemandPlan demand) (prepared : DemandPrepared artifact planned) :
      ItemPrepared artifact queue (.demand invocation demand) planned
  | header {record} (invocation : Invocation catalogue record) (reference : HeaderReference invocation)
      (link : SourceDutySlots.HeaderLink queue reference) : ItemPrepared artifact queue (.header invocation reference) link
  | call {record} (invocation : Invocation catalogue record) (application : ApplicationAt catalogue record)
      (target : GenericDutyQueue.Target application) : ItemPrepared artifact queue (.call invocation application target) ()

/-- Only the concrete providers contribute here. The typed header/application
constructors above preserve all original identities but introduce no extra slot.
Quantum Meaning reference roles are retained by Residual.meaning, not hidden in
this list or declared consumed by its length. -/
def ItemPrepared.providerContributions {artifact catalogue queue item planned} :
    @ItemPrepared artifact catalogue queue item planned → List (SourceDutyProviderBody.Contribution artifact)
  | .demand _ _ _ prepared => prepared.providers.map ProviderPrepared.contribution
  | .header .. | .call .. => []

private def readItem (artifact : Artifact) {catalogue : GenericCatalogue.Checked artifact.sources}
    (queue : GenericDutyQueue.Checked catalogue) (item : GenericDutyQueue.Item catalogue) :
    (planned : SourceDutySlots.ItemExpectation queue item) → ItemRequests queue item planned →
      WorkM (ItemPrepared artifact queue item planned) :=
  match item with
  | .demand invocation demand => fun planned requests => do
    return .demand invocation demand planned (← readDemand artifact planned requests)
  | .header invocation reference => fun link _ => pure (.header invocation reference link)
  | .call invocation application target => fun _ _ => pure (.call invocation application target)
  | .pendingRecursion .. => fun impossible _ => nomatch impossible

structure Entry (artifact : Artifact) {catalogue queue}
    (plan : @SourceDutySlots.Plan artifact.sources catalogue queue) (requests : Requests plan) where
  index : Fin plan.entries.length
  source : SourceDutySlots.Entry plan.indexed
  atIndex : source = plan.entries[index.val]'index.isLt
  prepared : ItemPrepared artifact queue source.subject source.subjectExpectation
  computed : SourceDutySlots.Computed
    (readItem artifact queue source.subject source.subjectExpectation (requests source)) prepared

structure Ledger (artifact : Artifact) {catalogue queue}
    (plan : @SourceDutySlots.Plan artifact.sources catalogue queue) (requests : Requests plan) where
  indexed : Indexed plan.entries
  indexing : SourceDutySlots.Computed (readIndexed plan.entries) indexed
  entries : List (Entry artifact plan requests)
  every : entries.map (·.index) = List.finRange plan.entries.length

/-- Ordered concrete-provider preparation only. A whole-runtime continuation
must also bind external selected-root actuals and genuine selected-root/body
discovery before the one final graph; this list cannot grant missing rows or
replace Meaning/reference/group/recursive/general-supplier obligations. -/
def Ledger.providerContributions {artifact catalogue queue plan requests}
    (ledger : @Ledger artifact catalogue queue plan requests) : List (SourceDutyProviderBody.Contribution artifact) :=
  ledger.entries.flatMap fun entry => entry.prepared.providerContributions

/-- Every exact original entry and every concrete provider ordinal is visited.
Any unsupported closed provider fails the actual preparation. Recursive queue
coverage already prevents construction of the required SourceDutySlots.Plan;
an open formal is retained in Residual, never assigned a convenient actual. -/
def read (artifact : Artifact) {catalogue queue}
    (plan : @SourceDutySlots.Plan artifact.sources catalogue queue) (requests : Requests plan) :
    WorkM (Ledger artifact plan requests) := do
  let indexed ← NaturalAffine.witness (readIndexed plan.entries)
  exactWork (Exact.charge (16*(plan.entries.length+1)))
  let entries ← indexed.val.indices.mapM fun index => do
    let source := indexed.val.at index
    let prepared ← NaturalAffine.witness
      (readItem artifact queue source.subject source.subjectExpectation (requests source))
    return (⟨index,source,indexed.val.at_original index,prepared.val,
      by with_reducible exact prepared.property⟩ : Entry artifact plan requests)
  if every : entries.map (·.index) = indexed.val.indices then
    return ⟨indexed.val,by with_reducible exact indexed.property,entries,every.trans indexed.val.every⟩
  else throw .request

end QleisliKernel.Qirf.SourceDutyProviderLedger
