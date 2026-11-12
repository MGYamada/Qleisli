import QleisliKernel.Qirf.RuntimeLinkedSubject

/-! A positive written Meaning link identifies its original queue duty, follows
the supplied operation to the same native occurrence, and checks every provider
in its closed evaluation. Conditional and inactive links cannot discharge it.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeLinkedSubject
open QleisliKernel Finite SourceTypes

-- An arm's checked_op names a single original operand. Constructed operations
-- can enter through a named formal and retain their whole substitution chain.
private def writtenName (description : GenericOperation.Description) : Bool :=
  description.root == 0 && match description.nodes with
    | [.formal _] | [.provider _ _ [] [] [] []] | [.primitive ..] => true
    | _ => false

section
variable {artifact catalogue owner description graph implementations references originals prepared root requested checked
    queue rootOwner rootName name entry path}
    {source : @RuntimeSourceOperationMarkers.Checked artifact catalogue owner description graph implementations references originals prepared root requested checked}
    {index : Nat}
    {invoked : @RuntimeDutyInvocation.DemandBinding artifact.sources catalogue queue rootOwner rootName owner name entry path}
    {closed : GenericOperation.Closed invoked.demand.transported.subject.description}

structure Fulfilled (link : ClosedAt source index invoked closed) : Prop where
  written : invoked.demand.source.original.kind = .checkedMeaning
  operand : writtenName invoked.demand.source.original.subject = true
  bindings : invoked.demand.source.original.bindings.isEmpty = true
  application : invoked.demand.source.original.runtimeApplication.isNone = true
  providers : link.providers.AllBound ∨ link.applied.isSome = true
  input : link.structureMatch.matched.terminal.value.input = link.originalMeaning.request.meaning.graph.input
  output : link.structureMatch.matched.terminal.value.output = link.originalMeaning.request.meaning.graph.output
  action : link.structureMatch.matched.terminal.value.action = link.originalMeaning.specification.action

private structure Verdict where
  claim : Prop
  positive : Bool
  sound : positive = true → claim

private def closedVerdict (link : ClosedAt source index invoked closed) : Verdict :=
  let duty := invoked.demand.source.original
  if h : duty.kind = .checkedMeaning ∧ writtenName duty.subject = true ∧ duty.bindings.isEmpty = true ∧
      duty.runtimeApplication.isNone = true ∧ (link.providers.complete = true ∨ link.applied.isSome = true) then
    ⟨Fulfilled link,true,fun _ =>
      ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,link.originalEquation.1,link.originalEquation.2.1,link.originalEquation.2.2⟩⟩
  else ⟨Fulfilled link,false,by intro impossible; cases impossible⟩

private def statusVerdict
    (source : @RuntimeSourceOperationMarkers.Checked artifact catalogue owner description graph implementations references originals prepared root requested checked)
    (index : Nat)
    (invoked : @RuntimeDutyInvocation.DemandBinding artifact.sources catalogue queue rootOwner rootName owner name entry path) :
    (status : SourcePendingMeaning.DemandStatus invoked.demand) → ForStatus source index invoked status → Verdict
  | .classified (.closed _),link => closedVerdict link
  | .classified (.conditional ..),_ | .inactive _,_ => ⟨False,false,by decide⟩
end

section
variable {artifact catalogue queue context description graph origin implementations references root requested owner name rootOwner rootName}
    (site : @RuntimeGraphOperation.Site artifact.sources owner name context description graph origin)
    (prepared : RuntimePreparedOperation.GraphPrepared artifact catalogue graph implementations references)
    (checked : RuntimeOperationTree.Checked prepared root requested)
    (source : RuntimeSourceOperationMarkers.OriginChecked origin prepared checked) (index : Nat)
    {entry : @SourcePendingMeaning.Entry artifact.sources catalogue queue}
    {path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name}
    (invoked : RuntimeDutyInvocation.DemandBinding entry path)
    (evidence : Evidence site prepared checked source index invoked)

private def verdict : Verdict := by
  cases site with
  | unlocated => exact evidence.elim
  | arm | application => exact statusVerdict source index invoked (assessment invoked) evidence

def Positive : Prop := (verdict site prepared checked source index invoked evidence).claim

def positive : Bool := (verdict site prepared checked source index invoked evidence).positive

theorem positive_sound : positive site prepared checked source index invoked evidence = true →
    Positive site prepared checked source index invoked evidence :=
  (verdict site prepared checked source index invoked evidence).sound
end
end QleisliKernel.Qirf.RuntimeLinkedSubject
