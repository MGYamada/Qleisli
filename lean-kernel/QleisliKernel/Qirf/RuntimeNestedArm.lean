import QleisliKernel.Qirf.RuntimeBodyOperationTraversal
import QleisliKernel.Qirf.RuntimeNestedDuty

/-! Associate separate enclosing and supplying source obligations with the
actual link returned by the common arm traversal.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNestedArm
open QleisliKernel Finite SourceTypes
open RuntimeNestedDuty (Role Supplement)

section
variable {artifact catalogue owner tokens implementations references operation prepared root requested checked
    rootOwner rootName name path}
    (pending : @SourcePendingMeaning.Prepared artifact.sources catalogue) (position : Fin pending.entries.length)
    (source : @RuntimeSourceOperationMarkers.Checked artifact catalogue owner tokens implementations references operation prepared root requested checked)
    (index : Nat)
    (invoked : @RuntimeDutyInvocation.DemandBinding artifact.sources catalogue pending.queue rootOwner rootName owner name
      pending.entries[position] path)

private def StatusRole : (status : SourcePendingMeaning.DemandStatus invoked.demand) →
    RuntimeLinkedSubject.ForStatus source index invoked status → Role pending.entries.length → Type
  | .classified (.closed _),link => RuntimeNestedDuty.ForRole pending position link
  | .classified (.conditional ..),_ | .inactive _,_ => fun _ => Empty

private def readStatus : (status : SourcePendingMeaning.DemandStatus invoked.demand) →
    (evidence : RuntimeLinkedSubject.ForStatus source index invoked status) →
    WorkM (Option (Supplement (StatusRole pending position source index invoked status evidence)))
  | .classified (.closed _),link => RuntimeNestedDuty.read? pending position link
  | .classified (.conditional ..),_ | .inactive _,_ => pure none
end

section
variable {artifact catalogue context description graph origin implementations references root requested owner name rootOwner rootName}
    (pending : @SourcePendingMeaning.Prepared artifact.sources catalogue) (position : Fin pending.entries.length)
    (site : @RuntimeGraphOperation.Site artifact.sources owner name context description graph origin)
    (prepared : RuntimePreparedOperation.GraphPrepared artifact catalogue graph implementations references)
    (checked : RuntimeOperationTree.Checked prepared root requested)
    (source : RuntimeSourceOperationMarkers.OriginChecked origin prepared checked) (index : Nat)
    {path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name}
    (invoked : RuntimeDutyInvocation.DemandBinding pending.entries[position] path)

private def SiteRole :
    RuntimeLinkedSubject.Evidence site prepared checked source index invoked → Role pending.entries.length → Type := by
  cases site with
  | unlocated => exact fun _ _ => Empty
  | arm => exact StatusRole pending position source index invoked (RuntimeLinkedSubject.assessment invoked)

private def readSite : (evidence : RuntimeLinkedSubject.Evidence site prepared checked source index invoked) →
    WorkM (Option (Supplement (SiteRole pending position site prepared checked source index invoked evidence))) := by
  cases site with
  | unlocated => exact fun impossible => nomatch impossible
  | arm => exact readStatus pending position source index invoked (RuntimeLinkedSubject.assessment invoked)
end

variable {artifact owner name arguments request prepared root runtime}
    (body : @RuntimeBodyOperations.AtRoot artifact owner name arguments request prepared root runtime)
    (link : RuntimeBodyOperations.ArmLink body)

def Evidence : Role prepared.source.pending.entries.length → Type :=
  let receipt := body.receipts[link.receiptIndex]
  @SiteRole artifact prepared.source.catalogue receipt.request.context receipt.request.description
    receipt.request.graph receipt.request.origin receipt.request.implementations receipt.request.references root
    receipt.request.requested receipt.location.owner receipt.location.name receipt.location.rootOwner receipt.location.rootName
    prepared.source.pending link.queueIndex receipt.location.site receipt.prepared receipt.evidence.checked
    receipt.evidence.source link.markerIndex receipt.location.path link.binding.instanceBinding link.subject

def read : WorkM (Option (Supplement (Evidence body link))) := do
  exactWork (Exact.charge (16*(body.receipts.length+prepared.source.pending.entries.length+1)))
  let receipt := body.receipts[link.receiptIndex]
  @readSite artifact prepared.source.catalogue receipt.request.context receipt.request.description
    receipt.request.graph receipt.request.origin receipt.request.implementations receipt.request.references root
    receipt.request.requested receipt.location.owner receipt.location.name receipt.location.rootOwner receipt.location.rootName
    prepared.source.pending link.queueIndex receipt.location.site receipt.prepared receipt.evidence.checked
    receipt.evidence.source link.markerIndex receipt.location.path link.binding.instanceBinding link.subject

end QleisliKernel.Qirf.RuntimeNestedArm
