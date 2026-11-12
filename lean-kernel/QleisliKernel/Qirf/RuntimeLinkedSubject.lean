import QleisliKernel.Qirf.RuntimeWrittenDuty
import QleisliKernel.Qirf.RuntimeForwardedSupply
import QleisliKernel.Qirf.RuntimeClosedEvaluation
import QleisliKernel.Qirf.RuntimeOriginalMeaning
import QleisliKernel.Qirf.RuntimeClosedProvider
import QleisliKernel.Qirf.RuntimeAppliedProvider

/-! Pair a closed queue subject with the native child of the very same written
assertion. A forwarded formal follows the original mixed arguments and
source tokens through the supplying callers. Other queue assessments retain their own status.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeLinkedSubject
open QleisliKernel Finite SourceTypes

structure ClosedAt {artifact catalogue owner description graph implementations references originals prepared root requested checked
    queue rootOwner rootName name entry path}
    (source : @RuntimeSourceOperationMarkers.Checked artifact catalogue owner description graph implementations references originals prepared root requested checked)
    (index : Nat)
    (invoked : @RuntimeDutyInvocation.DemandBinding artifact.sources catalogue queue rootOwner rootName owner name entry path)
    (closed : GenericOperation.Closed invoked.demand.transported.subject.description) where
  marker : RuntimeSourceOperationMarkers.Entry checked source.tree source.markers
  original : source.entries[index]? = some marker
  subject : RuntimeNativeSubject.Subject marker.assertion
  followed : RuntimeInterval.Computed (RuntimeNativeSubject.readSubject marker.assertion) subject
  structureMatch : RuntimeClosedSubject.Checked closed subject.child.cursor
  traversed : RuntimeInterval.Computed (RuntimeClosedSubject.read closed subject.child.cursor) structureMatch
  suppliers : RuntimeForwardedSupply.Chain invoked.binding invoked.demand.transported.receipt structureMatch.matched.paired
  identified : RuntimeInterval.Computed (RuntimeForwardedSupply.read invoked.binding
    invoked.demand.transported.receipt structureMatch.matched.paired) suppliers
  evaluated : RuntimeClosedEvaluation.Evaluation closed checked invoked.demand.transported.subject.description.root
    structureMatch.matched.terminal
  providers : RuntimeClosedProvider.Checked invoked.demand.transported.subject closed structureMatch.matched.paired ⟨false,false,false⟩
  providersRead : RuntimeInterval.Computed (RuntimeClosedProvider.read invoked.demand.transported.subject
    closed structureMatch.matched.paired ⟨false,false,false⟩) providers
  applied : Option (RuntimeAppliedProvider.Checked invoked.demand structureMatch.matched.terminal)
  appliedRead : RuntimeInterval.Computed
    (RuntimeAppliedProvider.read? invoked.demand structureMatch.matched.terminal) applied
  originalMeaning : RuntimeOriginalMeaning.Checked marker.assertion invoked.demand.source.original
  meaningRead : RuntimeInterval.Computed
    (RuntimeOriginalMeaning.read marker.assertion invoked.demand.source.original) originalMeaning
  equation : RuntimeOperationTree.Equation structureMatch.matched.terminal.value marker.assertion.requirement
    marker.assertion.equation.specification

theorem ClosedAt.originalEquation {artifact catalogue owner description graph implementations references originals prepared root requested checked
    queue rootOwner rootName name entry path}
    {source : @RuntimeSourceOperationMarkers.Checked artifact catalogue owner description graph implementations references originals prepared root requested checked}
    {index : Nat}
    {invoked : @RuntimeDutyInvocation.DemandBinding artifact.sources catalogue queue rootOwner rootName owner name entry path}
    {closed : GenericOperation.Closed invoked.demand.transported.subject.description}
    (link : ClosedAt source index invoked closed) :
    link.structureMatch.matched.terminal.value.input = link.originalMeaning.request.meaning.graph.input ∧
    link.structureMatch.matched.terminal.value.output = link.originalMeaning.request.meaning.graph.output ∧
    link.structureMatch.matched.terminal.value.action = link.originalMeaning.specification.action := by
  have same := link.subject.same.symm
  exact ⟨link.structureMatch.matched.ports.1.trans
      ((congrArg RuntimeOperationTree.Value.input same).trans link.originalMeaning.input),
    link.structureMatch.matched.ports.2.trans
      ((congrArg RuntimeOperationTree.Value.output same).trans link.originalMeaning.output),
    link.structureMatch.matched.action.trans
      ((congrArg RuntimeOperationTree.Value.action same).trans link.originalMeaning.action)⟩

private def readClosed {artifact catalogue owner description graph implementations references originals prepared root requested checked
    queue rootOwner rootName name entry path}
    (source : @RuntimeSourceOperationMarkers.Checked artifact catalogue owner description graph implementations references originals prepared root requested checked)
    (index : Nat)
    (invoked : @RuntimeDutyInvocation.DemandBinding artifact.sources catalogue queue rootOwner rootName owner name entry path)
    (closed : GenericOperation.Closed invoked.demand.transported.subject.description) :
    WorkM (ClosedAt source index invoked closed) := do
  exactWork (Exact.charge (16*(source.entries.length+1)))
  match original : source.entries[index]? with
  | none => throw .request
  | some marker =>
    let subject ← NaturalAffine.witness (RuntimeNativeSubject.readSubject marker.assertion)
    let matched ← NaturalAffine.witness (RuntimeClosedSubject.read closed subject.val.child.cursor)
    let suppliers ← NaturalAffine.witness (RuntimeForwardedSupply.read invoked.binding
      invoked.demand.transported.receipt matched.val.matched.paired)
    let providers ← NaturalAffine.witness (RuntimeClosedProvider.read invoked.demand.transported.subject
      closed matched.val.matched.paired ⟨false,false,false⟩)
    let applied ← NaturalAffine.witness (RuntimeAppliedProvider.read? invoked.demand matched.val.matched.terminal)
    let meaning ← NaturalAffine.witness (RuntimeOriginalMeaning.read marker.assertion invoked.demand.source.original)
    have semantic := RuntimeClosedEvaluation.assertion marker.assertion subject.val matched.val
    return ⟨marker,original,subject.val,by with_reducible exact subject.property,
      matched.val,by with_reducible exact matched.property,suppliers.val,by with_reducible exact suppliers.property,
      semantic.1,providers.val,by with_reducible exact providers.property,
      applied.val,by with_reducible exact applied.property,meaning.val,by with_reducible exact meaning.property,semantic.2⟩

def assessment {sources catalogue queue rootOwner rootName owner name entry path}
    (invoked : @RuntimeDutyInvocation.DemandBinding sources catalogue queue rootOwner rootName owner name entry path) :
    SourcePendingMeaning.DemandStatus invoked.demand :=
  (congrArg SourcePendingMeaning.Assessment invoked.subject).mp entry.subjectAssessment

def ForStatus {artifact catalogue owner description graph implementations references originals prepared root requested checked
    queue rootOwner rootName name entry path}
    (source : @RuntimeSourceOperationMarkers.Checked artifact catalogue owner description graph implementations references originals prepared root requested checked)
    (index : Nat)
    (invoked : @RuntimeDutyInvocation.DemandBinding artifact.sources catalogue queue rootOwner rootName owner name entry path) :
    SourcePendingMeaning.DemandStatus invoked.demand → Type
  | .classified (.closed closed) => ClosedAt source index invoked closed
  | .classified (.conditional ..) | .inactive _ => Unit

private def readStatus {artifact catalogue owner description graph implementations references originals prepared root requested checked
    queue rootOwner rootName name entry path}
    (source : @RuntimeSourceOperationMarkers.Checked artifact catalogue owner description graph implementations references originals prepared root requested checked)
    (index : Nat)
    (invoked : @RuntimeDutyInvocation.DemandBinding artifact.sources catalogue queue rootOwner rootName owner name entry path)
    (status : SourcePendingMeaning.DemandStatus invoked.demand) : WorkM (ForStatus source index invoked status) := by
  cases status with
  | inactive => exact pure ()
  | classified kind =>
    cases kind with
    | conditional => exact pure ()
    | closed closed => exact readClosed source index invoked closed

def Evidence {artifact catalogue queue context description graph origin implementations references root requested owner name rootOwner rootName}
    (site : @RuntimeGraphOperation.Site artifact.sources owner name context description graph origin)
    (prepared : RuntimePreparedOperation.GraphPrepared artifact catalogue graph implementations references)
    (checked : RuntimeOperationTree.Checked prepared root requested)
    (source : RuntimeSourceOperationMarkers.OriginChecked origin prepared checked) (index : Nat)
    {entry : @SourcePendingMeaning.Entry artifact.sources catalogue queue}
    {path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name}
    (invoked : RuntimeDutyInvocation.DemandBinding entry path) : Type := by
  cases site with
  | unlocated => exact Empty
  | arm | application => exact ForStatus source index invoked (assessment invoked)
  | supplying event slot caller =>
    exact ForStatus source index invoked (assessment invoked) ×
      RuntimeDutyInvocation.Supplying event slot (caller.symm ▸ path) invoked.demand.source.original

def read {artifact catalogue queue context description graph origin implementations references root requested owner name rootOwner rootName}
    (site : @RuntimeGraphOperation.Site artifact.sources owner name context description graph origin)
    (prepared : RuntimePreparedOperation.GraphPrepared artifact catalogue graph implementations references)
    (checked : RuntimeOperationTree.Checked prepared root requested)
    (source : RuntimeSourceOperationMarkers.OriginChecked origin prepared checked) (index : Nat)
    {entry : @SourcePendingMeaning.Entry artifact.sources catalogue queue}
    {path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name}
    (invoked : RuntimeDutyInvocation.DemandBinding entry path) :
    WorkM (Evidence site prepared checked source index invoked) := by
  cases site with
  | unlocated => exact throw .request
  | arm | application => exact readStatus source index invoked (assessment invoked)
  | supplying event slot caller =>
    exact do
      let original ← RuntimeDutyInvocation.readSupplying event slot (caller.symm ▸ path) invoked.demand.source.original
      let subject ← readStatus source index invoked (assessment invoked)
      pure ⟨subject,original⟩

end QleisliKernel.Qirf.RuntimeLinkedSubject
