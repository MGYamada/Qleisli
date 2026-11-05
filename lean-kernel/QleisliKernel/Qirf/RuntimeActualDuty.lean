import QleisliKernel.Qirf.RuntimeLinkedEligibility

/-! Check the supplying caller’s written Meaning independently of the enclosing arm. The genuine original request, its native child, its provider and the same final dependency root are retained.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNestedDuty
open QleisliKernel Finite SourceTypes
open RuntimeInterval (Computed)
open RuntimeNativeSubject (Cursor)

abbrev ResultOf {α : Type} (action : WorkM α) := {value : α // Computed action value}

private def sourceIndex {sources catalogue owner scope}
    (pending : @SourcePendingMeaning.Prepared sources catalogue) (id : GenericDutyQueue.InstanceId)
    (marker : SourceOperation.Marker sources owner scope) : WorkM (Fin pending.entries.length) := do
  let some i ← RuntimeWrittenDuty.selectCandidate pending id marker | throw Finite.Error.request
  return i

structure Route {sources caller scope} (marker : SourceOperation.Marker sources caller scope)
    {catalogue rootOwner rootName callerName} (pending : @SourcePendingMeaning.Prepared sources catalogue)
    (path : RuntimeOrdinaryBody.CallPath sources rootOwner rootName caller callerName)
    (instanceId : GenericDutyQueue.InstanceId) where
  index : ResultOf (sourceIndex pending instanceId marker)
  invoked : ResultOf (RuntimeDutyInvocation.readDemand pending.entries[index.val] path)
  written : ResultOf (RuntimeWrittenDuty.readWritten callerName marker invoked.val.demand.source.original)

private def readRoute {sources caller scope} (marker : SourceOperation.Marker sources caller scope)
    {catalogue rootOwner rootName callerName} (pending : @SourcePendingMeaning.Prepared sources catalogue)
    (path : RuntimeOrdinaryBody.CallPath sources rootOwner rootName caller callerName)
    (instanceId : GenericDutyQueue.InstanceId) : WorkM (Route marker pending path instanceId) := do
  let i ← NaturalAffine.witness (sourceIndex pending instanceId marker)
  exactWork (Exact.charge (16*(pending.entries.length+1)))
  let bound ← NaturalAffine.witness (RuntimeDutyInvocation.readDemand pending.entries[i.val] path)
  let written ← NaturalAffine.witness (RuntimeWrittenDuty.readWritten callerName marker bound.val.demand.source.original)
  return ⟨i,bound,written⟩

private def bare (description : GenericOperation.Description) : Bool :=
  description.root == 0 && match description.nodes with | [.provider _ _ [] [] [] []] => true | _ => false

section
variable {artifact catalogue context description graph implementations references prepared root requested checked caller scope marker target
  queue rootOwner rootName owner name entry path}
  (asserted : @RuntimeSourceOperationMarkers.Assertion artifact catalogue context description graph implementations references
     prepared root requested caller scope checked marker target)
  (invoked : @RuntimeDutyInvocation.DemandBinding artifact.sources catalogue queue rootOwner rootName owner name entry path)

structure Exact (closed : GenericOperation.Closed invoked.demand.transported.subject.description) where
  meaning : ResultOf (RuntimeOriginalMeaning.read asserted invoked.demand.source.original)
  child : ResultOf (RuntimeNativeSubject.readSubject asserted)
  paired : ResultOf (RuntimeClosedSubject.read closed child.val.child.cursor)
  providers : ResultOf (RuntimeClosedProvider.read invoked.demand.transported.subject closed paired.val.matched.paired
    ⟨false,false,false⟩)
  allProviders : providers.val.AllBound

private def readExact (closed : GenericOperation.Closed invoked.demand.transported.subject.description) :
    WorkM (Exact asserted invoked closed) := do
  let meaning ← NaturalAffine.witness (RuntimeOriginalMeaning.read asserted invoked.demand.source.original)
  let child ← NaturalAffine.witness (RuntimeNativeSubject.readSubject asserted)
  let paired ← NaturalAffine.witness (RuntimeClosedSubject.read closed child.val.child.cursor)
  let providers ← NaturalAffine.witness (RuntimeClosedProvider.read invoked.demand.transported.subject closed paired.val.matched.paired
    ⟨false,false,false⟩)
  if all : providers.val.complete = true then return ⟨meaning,child,paired,providers,all⟩
  else throw Finite.Error.request

private def classification :
    WorkM {closed : GenericOperation.Closed invoked.demand.transported.subject.description //
      RuntimeLinkedSubject.assessment invoked = .classified (.closed closed)} :=
  match RuntimeLinkedSubject.assessment invoked with
  | .classified (.closed closed) => pure ⟨closed,rfl⟩
  | _ => throw Finite.Error.request
end

structure Inner {artifact catalogue context description graph implementations references prepared root requested checked caller scope}
    (marker : SourceOperation.Marker artifact.sources caller scope)
    (cursor : @Cursor artifact catalogue context description graph implementations references prepared root requested checked)
    {rootOwner rootName callerName} (pending : @SourcePendingMeaning.Prepared artifact.sources catalogue)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName caller callerName)
    (instanceId : GenericDutyQueue.InstanceId) where
  route : ResultOf (readRoute marker pending path instanceId)
  assertion : ResultOf (RuntimeSourceOperationMarkers.readBoundAssertion checked marker cursor.tree cursor.binding)
  closed : {closed : GenericOperation.Closed route.val.invoked.val.demand.transported.subject.description //
    RuntimeLinkedSubject.assessment route.val.invoked.val = .classified (.closed closed)}
  evaluated : ResultOf (readExact assertion.val route.val.invoked.val closed.val)
  eligible : route.val.invoked.val.demand.source.original.runtimeApplication.isNone = true ∧
    bare route.val.invoked.val.demand.source.original.subject = true ∧ route.val.invoked.val.invocation.depth = 0 ∧
    pending.entries[route.val.index.val].unconsumed = true

def readInner {artifact catalogue context description graph implementations references prepared root requested checked caller scope}
    (marker : SourceOperation.Marker artifact.sources caller scope)
    (cursor : @Cursor artifact catalogue context description graph implementations references prepared root requested checked)
    {rootOwner rootName callerName} (pending : @SourcePendingMeaning.Prepared artifact.sources catalogue)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName caller callerName)
    (instanceId : GenericDutyQueue.InstanceId) : WorkM (Inner marker cursor pending path instanceId) := do
  let route ← NaturalAffine.witness (readRoute marker pending path instanceId)
  let invoked := route.val.invoked.val
  let d := invoked.demand.source.original
  exactWork (Exact.charge (8*(pending.entries.length+1)))
  if eligible : d.runtimeApplication.isNone = true ∧ bare d.subject = true ∧
      invoked.invocation.depth = 0 ∧ pending.entries[route.val.index.val].unconsumed = true then
    let asserted ← NaturalAffine.witness (RuntimeSourceOperationMarkers.readBoundAssertion checked marker cursor.tree cursor.binding)
    let closed ← classification invoked
    let exactResult ← NaturalAffine.witness (readExact asserted.val invoked closed.val)
    return ⟨route,asserted,closed,exactResult,eligible⟩
  else throw Finite.Error.request

end QleisliKernel.Qirf.RuntimeNestedDuty
