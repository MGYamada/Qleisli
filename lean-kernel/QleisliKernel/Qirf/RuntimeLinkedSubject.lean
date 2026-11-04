import QleisliKernel.Qirf.RuntimeWrittenDuty
import QleisliKernel.Qirf.RuntimeClosedSubject
import QleisliKernel.Qirf.RuntimeFormalActual

/-! Pair a closed queue subject with the native child of the very same written
assertion. Direct formal references also identify the original mixed argument,
including its source tokens. Other queue assessments retain their own status.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeLinkedSubject
open QleisliKernel Finite SourceTypes
open QleisliKernel.Semantics.SymbolicBasis (Parameter)

private def keyOf : GenericOperation.Node → Option Parameter
  | .formal key => some key
  | _ => none

private theorem keyOf_some {node key} (found : keyOf node = some key) : node = .formal key := by
  cases node <;> simp_all [keyOf]

private def wrapped : OperationDescription.Node → Bool
  | .formal .. => true
  | _ => false

inductive Head {artifact catalogue context description graph implementations references prepared root requested checked
    queue rootOwner rootName owner name entry path}
    (invoked : @RuntimeDutyInvocation.DemandBinding artifact.sources catalogue queue rootOwner rootName owner name entry path)
    (cursor : @RuntimeNativeSubject.Cursor artifact catalogue context description graph implementations references prepared root requested checked) where
  | direct (node : GenericOperation.Node)
      (original : invoked.demand.source.original.subject.nodes[invoked.demand.source.original.subject.root]? = some node)
      (concrete : keyOf node = none) (native : wrapped cursor.node = false)
  | formal (key : Parameter)
      (original : invoked.demand.source.original.subject.nodes[invoked.demand.source.original.subject.root]? = some (.formal key))
      (selected : RuntimeNativeSubject.Formal cursor)
      (selection : RuntimeInterval.Computed (RuntimeNativeSubject.readFormal cursor) selected)
      (choice : RuntimeFormalActual.Choice)
      (actual : RuntimeInterval.Computed (RuntimeFormalActual.readChoice selected) choice)
      (supply : RuntimeFormalActual.Evidence invoked.binding invoked.demand key choice)
      (supplied : RuntimeInterval.Computed (RuntimeFormalActual.read invoked.binding invoked.demand key choice) supply)

private def readHead {artifact catalogue context description graph implementations references prepared root requested checked
    queue rootOwner rootName owner name entry path}
    (invoked : @RuntimeDutyInvocation.DemandBinding artifact.sources catalogue queue rootOwner rootName owner name entry path)
    (cursor : @RuntimeNativeSubject.Cursor artifact catalogue context description graph implementations references prepared root requested checked)
    {closed : GenericOperation.Closed invoked.demand.transported.subject.description}
    (matched : RuntimeClosedSubject.Checked closed cursor) :
    WorkM (Head invoked cursor) := do
  let original := invoked.demand.source.original.subject
  exactWork (Exact.charge (16*(original.nodes.length+1)))
  match source : original.nodes[original.root]? with
  | none => throw .request
  | some node =>
    match identity : keyOf node with
    | some key =>
      have same := keyOf_some identity
      let some selected := matched.matched.outerFormal | throw .request
      let choice ← NaturalAffine.witness (RuntimeFormalActual.readChoice selected.val)
      let supply ← NaturalAffine.witness (RuntimeFormalActual.read invoked.binding invoked.demand key choice.val)
      return .formal key (source.trans (congrArg some same)) selected.val selected.property
        choice.val (by with_reducible exact choice.property) supply.val (by with_reducible exact supply.property)
    | none =>
      if native : wrapped cursor.node = false then return .direct node source identity native
      else throw .request

structure ClosedAt {artifact catalogue owner tokens implementations references operation prepared root requested checked
    queue rootOwner rootName name entry path}
    (source : @RuntimeSourceOperationMarkers.Checked artifact catalogue owner tokens implementations references operation prepared root requested checked)
    (index : Nat)
    (invoked : @RuntimeDutyInvocation.DemandBinding artifact.sources catalogue queue rootOwner rootName owner name entry path)
    (closed : GenericOperation.Closed invoked.demand.transported.subject.description) where
  marker : RuntimeSourceOperationMarkers.Entry checked source.tree source.markers
  original : source.entries[index]? = some marker
  subject : RuntimeNativeSubject.Subject marker.assertion
  followed : RuntimeInterval.Computed (RuntimeNativeSubject.readSubject marker.assertion) subject
  structureMatch : RuntimeClosedSubject.Checked closed subject.child.cursor
  traversed : RuntimeInterval.Computed (RuntimeClosedSubject.read closed subject.child.cursor) structureMatch
  head : Head invoked subject.child.cursor
  identified : RuntimeInterval.Computed (readHead invoked subject.child.cursor structureMatch) head
  equation : RuntimeOperationTree.Equation structureMatch.matched.terminal.value marker.assertion.requirement
    marker.assertion.equation.specification

private def readClosed {artifact catalogue owner tokens implementations references operation prepared root requested checked
    queue rootOwner rootName name entry path}
    (source : @RuntimeSourceOperationMarkers.Checked artifact catalogue owner tokens implementations references operation prepared root requested checked)
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
    let head ← NaturalAffine.witness (readHead invoked subject.val.child.cursor matched.val)
    have equation := marker.assertion.equation.equation
    have same := subject.val.same.symm
    let result := matched.val.matched
    return ⟨marker,original,subject.val,by with_reducible exact subject.property,
      matched.val,by with_reducible exact matched.property,head.val,by with_reducible exact head.property,
      ⟨result.ports.1.trans ((congrArg RuntimeOperationTree.Value.input same).trans equation.input),
        result.ports.2.trans ((congrArg RuntimeOperationTree.Value.output same).trans equation.output),
        result.action.trans ((congrArg RuntimeOperationTree.Value.action same).trans equation.action)⟩⟩

def assessment {sources catalogue queue rootOwner rootName owner name entry path}
    (invoked : @RuntimeDutyInvocation.DemandBinding sources catalogue queue rootOwner rootName owner name entry path) :
    SourcePendingMeaning.DemandStatus invoked.demand :=
  (congrArg SourcePendingMeaning.Assessment invoked.subject).mp entry.subjectAssessment

def ForStatus {artifact catalogue owner tokens implementations references operation prepared root requested checked
    queue rootOwner rootName name entry path}
    (source : @RuntimeSourceOperationMarkers.Checked artifact catalogue owner tokens implementations references operation prepared root requested checked)
    (index : Nat)
    (invoked : @RuntimeDutyInvocation.DemandBinding artifact.sources catalogue queue rootOwner rootName owner name entry path) :
    SourcePendingMeaning.DemandStatus invoked.demand → Type
  | .classified (.closed closed) => ClosedAt source index invoked closed
  | .classified (.conditional ..) | .inactive _ => Unit

private def readStatus {artifact catalogue owner tokens implementations references operation prepared root requested checked
    queue rootOwner rootName name entry path}
    (source : @RuntimeSourceOperationMarkers.Checked artifact catalogue owner tokens implementations references operation prepared root requested checked)
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
  | arm => exact ForStatus source index invoked (assessment invoked)

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
  | arm => exact readStatus source index invoked (assessment invoked)

end QleisliKernel.Qirf.RuntimeLinkedSubject
