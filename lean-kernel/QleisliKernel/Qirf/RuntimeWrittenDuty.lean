import QleisliKernel.Qirf.RuntimeDutyInvocation
import QleisliKernel.Qirf.RuntimeSourceOperationMarkers

/-! Match a written assertion in a native arm receipt to its indexed original
queue entry. The call chain identifies the instance, and the original tokens,
lexical bindings and Meaning identify the duty within that instance. This
association retains the transported subject for a separate equation check.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeWrittenDuty
open QleisliKernel Finite SourceTypes

structure Located (sources : Sources) (owner : String) where
  scope : List String
  marker : SourceOperation.Marker sources owner scope
  record : Nat

def markerCount {artifact catalogue owner name context description graph origin implementations references}
    (site : @RuntimeGraphOperation.Site artifact.sources owner name context description graph origin)
    (prepared : RuntimePreparedOperation.GraphPrepared artifact catalogue graph implementations references)
    {root requested} (checked : RuntimeOperationTree.Checked prepared root requested)
    (source : RuntimeSourceOperationMarkers.OriginChecked origin prepared checked) : Nat := by
  cases site with
  | unlocated => exact 0
  | arm _ _ => exact source.entries.length

/-- Select an entry from the association already returned by native arm
consumption. Both source and native positions come from this same entry. -/
def locate {artifact catalogue owner name context description graph origin implementations references}
    (site : @RuntimeGraphOperation.Site artifact.sources owner name context description graph origin)
    (prepared : RuntimePreparedOperation.GraphPrepared artifact catalogue graph implementations references)
    {root requested} (checked : RuntimeOperationTree.Checked prepared root requested)
    (source : RuntimeSourceOperationMarkers.OriginChecked origin prepared checked) (index : Nat) :
    WorkM (Located artifact.sources owner) := by
  cases site with
  | unlocated => exact throw .request
  | arm table armIndex => exact do
    exactWork (Exact.charge (16*(source.entries.length+source.markers.length+1)))
    let some entry := source.entries[index]? | throw .request
    return ⟨source.scope,source.markers[entry.index],entry.assertion.binding.index.val⟩

structure Written {sources owner scope} (name : String)
    (marker : SourceOperation.Marker sources owner scope) (duty : GenericOperation.Duty sources) where
  kind : duty.kind = .checkedMeaning
  caller : duty.origin.state.owner = owner ∧ duty.origin.state.name = name
  tokens : duty.origin.tokens = marker.tokens
  visible : ∀ key, key ∈ duty.origin.scope ↔ key ∈ scope
  request : SourceMeaning.Request sources
  original : duty.requirement = .meaning request
  routes : request.queryRows = marker.selected.queryRows
  meaning : RuntimeSourceOperationMarkers.MeaningOriginal marker request

def readWritten {sources owner scope} (name : String)
    (marker : SourceOperation.Marker sources owner scope) (duty : GenericOperation.Duty sources) :
    WorkM (Written name marker duty) := do
  let origin := duty.origin
  let names := SourceTrace.Meter.nameFields origin.scope + SourceTrace.Meter.nameFields scope
  exactWork (Exact.charge (16*((names+1)*(origin.scope.length+scope.length+1)+
    SourceTrace.Meter.tokenFields origin.tokens+SourceTrace.Meter.tokenFields marker.tokens+
    owner.utf8ByteSize+name.utf8ByteSize+origin.state.owner.utf8ByteSize+origin.state.name.utf8ByteSize+1)))
  match original : duty.requirement with
  | .access _ => throw .request
  | .meaning request =>
    exactWork (Exact.charge (16*((request.queryRows ++ marker.selected.queryRows).foldl
      (fun n row => n+row.1.utf8ByteSize+row.2.utf8ByteSize+2) 1)))
    if same : duty.kind = .checkedMeaning ∧ origin.state.owner = owner ∧ origin.state.name = name ∧
        origin.tokens = marker.tokens ∧ RuntimeDutyInvocation.sameScope origin.scope scope = true ∧
        request.queryRows = marker.selected.queryRows then
      let meaning ← RuntimeSourceOperationMarkers.readMeaningOriginal marker request
      return ⟨same.1,⟨same.2.1,same.2.2.1⟩,same.2.2.2.1,RuntimeDutyInvocation.sameScope_members same.2.2.2.2.1,request,original,
        same.2.2.2.2.2,meaning⟩
    else throw .request

structure Binding {artifact catalogue queue context description graph origin implementations references root requested owner name rootOwner rootName}
    (site : @RuntimeGraphOperation.Site artifact.sources owner name context description graph origin)
    (prepared : RuntimePreparedOperation.GraphPrepared artifact catalogue graph implementations references)
    (checked : RuntimeOperationTree.Checked prepared root requested)
    (source : RuntimeSourceOperationMarkers.OriginChecked origin prepared checked) (index : Nat)
    (entry : @SourcePendingMeaning.Entry artifact.sources catalogue queue)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name) where
  located : Located artifact.sources owner
  native : RuntimeInterval.Computed (locate site prepared checked source index) located
  instanceBinding : RuntimeDutyInvocation.DemandBinding entry path
  invoked : RuntimeInterval.Computed (RuntimeDutyInvocation.readDemand entry path) instanceBinding
  written : Written name located.marker instanceBinding.demand.source.original
  identified : RuntimeInterval.Computed (readWritten name located.marker instanceBinding.demand.source.original) written

def read {artifact catalogue queue context description graph origin implementations references root requested owner name rootOwner rootName}
    (site : @RuntimeGraphOperation.Site artifact.sources owner name context description graph origin)
    (prepared : RuntimePreparedOperation.GraphPrepared artifact catalogue graph implementations references)
    (checked : RuntimeOperationTree.Checked prepared root requested)
    (source : RuntimeSourceOperationMarkers.OriginChecked origin prepared checked) (index : Nat)
    (entry : @SourcePendingMeaning.Entry artifact.sources catalogue queue)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name) :
    WorkM (Binding site prepared checked source index entry path) := do
  let located ← NaturalAffine.witness (locate site prepared checked source index)
  let instanceBinding ← NaturalAffine.witness (RuntimeDutyInvocation.readDemand entry path)
  let written ← NaturalAffine.witness (readWritten name located.val.marker instanceBinding.val.demand.source.original)
  return ⟨located.val,by with_reducible exact located.property,instanceBinding.val,
    by with_reducible exact instanceBinding.property,written.val,by with_reducible exact written.property⟩

/-- A queue ordinal is only a candidate. Require a unique written occurrence
in the identified original invocation before checking its full binding. -/
def selectEntry {sources catalogue owner scope} (pending : @SourcePendingMeaning.Prepared sources catalogue)
    (instanceId : GenericDutyQueue.InstanceId) (marker : SourceOperation.Marker sources owner scope) :
    WorkM (Fin pending.entries.length) := do
  exactWork (Exact.charge (16*(pending.entries.length+SourceTrace.Meter.tokenFields marker.tokens+1)))
  let items := pending.entries.toArray
  let tokenWork := SourceTrace.Meter.tokenFields marker.tokens
  let selected ← (List.finRange pending.entries.length).foldlM (init := none) fun previous i => do
    let entry := items[i.val]'(by simpa only [items,List.size_toArray] using i.isLt)
    match entry.subject with
    | .demand invocation demand =>
      if demand.source.original.kind != .checkedMeaning then return previous
      let tokens := demand.source.original.origin.tokens
      exactWork (Exact.charge (16*(tokenWork+SourceTrace.Meter.tokenFields tokens+1)))
      if tokens != marker.tokens then return previous
      exactWork (Exact.charge (16*((invocation.depth+1)^2+instanceId.calls.length+1)))
      if invocation.id != instanceId then return previous
      if previous.isSome then throw .request
      return some i
    | _ => return previous
  lift (readOption selected)

end QleisliKernel.Qirf.RuntimeWrittenDuty
