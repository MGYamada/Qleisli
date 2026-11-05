import QleisliKernel.Qirf.RuntimeClosedSubject

/-! The executable computation at each occurrence of a closed generic
operation uses that occurrence's original ordered operands and provider row.
Binding a provider to the source duty that supplied it is a separate premise.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeClosedEvaluation
open QleisliKernel Finite SourceTypes
open QleisliKernel.SourceTypes.OperationDescription (Node)
open RuntimeNativeSubject (Cursor)
open RuntimeClosedSubject (Paired ChildRead shape)
open RuntimeInterval (Computed)

structure Calculation {original : GenericOperation.Description} (closed : GenericOperation.Closed original)
    {artifact catalogue context description graph implementations references prepared root requested checked}
    (index : Nat)
    (cursor : @Cursor artifact catalogue context description graph implementations references prepared root requested checked)
    (payload : Node) : Prop where
  selected : closed.data.description.nodes[index]? = some payload
  shape : RuntimeClosedSubject.shape cursor.node = RuntimeClosedSubject.shape payload
  arity : cursor.binding.record.checked.children.length = payload.children.length
  closure : ∃ source row, original.nodes[index]? = some source ∧ closed.data.nodes[index]? = some row ∧
    Computed (GenericOperation.readNode source) row ∧ row.node = payload ∧ source.children = payload.children
  action : Computed (OperationIRMeaning.readNode cursor.binding.record.occurrence.result payload
    (cursor.binding.record.checked.children.map RuntimeOperationTree.Value.action)
    cursor.binding.record.checked.provider.actions 0) (cursor.value.action,cursor.binding.record.checked.consumedProviders)
  providers : cursor.binding.record.checked.consumedProviders = cursor.binding.record.checked.provider.actions.length
  ports : cursor.value.input = cursor.binding.record.occurrence.result.input ∧
    cursor.value.output = cursor.binding.record.occurrence.result.output

private theorem calculate {original : GenericOperation.Description} (closed : GenericOperation.Closed original)
    {artifact catalogue context description graph implementations references prepared root requested checked}
    {index : Nat} (cursor : @Cursor artifact catalogue context description graph implementations references prepared root requested checked)
    (payload : Node) (selected : closed.data.description.nodes[index]? = some payload)
    (same : shape cursor.node = shape payload)
    (arity : cursor.binding.record.checked.children.length = payload.children.length) : Calculation closed index cursor payload := by
  obtain ⟨source,row,atSource,atRow,identity,read,edges⟩ := closed.originalNodeAt index selected
  refine ⟨selected,same,arity,⟨source,row,atSource,atRow,read,identity,edges.symm⟩,?_,cursor.binding.record.checked.consumed,⟨rfl,rfl⟩⟩
  let run := fun n => OperationIRMeaning.readNode cursor.binding.record.occurrence.result n
    (cursor.binding.record.checked.children.map RuntimeOperationTree.Value.action)
    cursor.binding.record.checked.provider.actions 0
  have normalized (node : Node) : run (shape node) = run node :=
    OperationIRMeaning.readNode_remap _ _ _ _ _ _
  have equality : run cursor.node = run payload :=
    (normalized cursor.node).symm.trans ((congrArg run same).trans (normalized payload))
  exact (congrArg (fun action => Computed action (cursor.value.action,cursor.binding.record.checked.consumedProviders))
    equality).mp cursor.binding.record.checked.calculated

/- Each semantic argument is the entire actual Value selected at that
ordinal in the parent's computation, together with the evaluated closed
child occurrence. Native formal projection conserves both ports and action. -/
mutual
inductive Evaluation {original : GenericOperation.Description} (closed : GenericOperation.Closed original)
    {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested) :
    Nat → Cursor checked → Prop where
  | node {index : Nat} {cursor : Cursor checked} (payload : Node) (ran : Calculation closed index cursor payload)
      (arguments : Arguments closed checked cursor payload.children.zipIdx) : Evaluation closed checked index cursor

inductive Arguments {original : GenericOperation.Description} (closed : GenericOperation.Closed original)
    {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested) :
    Cursor checked → List (Nat × Nat) → Prop where
  | nil {cursor : Cursor checked} : Arguments closed checked cursor []
  | cons {cursor terminal : Cursor checked} {index position : Nat} {rest : List (Nat × Nat)}
      (child : ChildRead cursor position)
      (ports : child.val.cursor.value.input = terminal.value.input ∧ child.val.cursor.value.output = terminal.value.output)
      (action : child.val.cursor.value.action = terminal.value.action)
      (nested : Evaluation closed checked index terminal) (tail : Arguments closed checked cursor rest) :
      Arguments closed checked cursor ((index,position) :: rest)
end

theorem evaluated {original : GenericOperation.Description} (closed : GenericOperation.Closed original)
    {artifact catalogue context description graph implementations references prepared root requested checked index cursor terminal}
    (paired : @Paired artifact catalogue context description graph implementations references prepared root requested checked
      closed.data.description index cursor terminal) :
    Evaluation closed checked index terminal ∧ cursor.value.input = terminal.value.input ∧
      cursor.value.output = terminal.value.output ∧ cursor.value.action = terminal.value.action := by
  induction paired using Paired.rec (motive_2 := fun cursor edges _ => Arguments closed checked cursor edges) with
  | node payload selected _ same _ arity _ children =>
    exact ⟨.node payload (calculate closed _ payload selected same arity) children,rfl,rfl,rfl⟩
  | formal selected _ _ ih =>
    exact ⟨ih.1,selected.ports.1.symm.trans ih.2.1,selected.ports.2.symm.trans ih.2.2.1,
      selected.action.symm.trans ih.2.2.2⟩
  | nil => exact .nil
  | cons child _ _ _ nested tail =>
    exact .cons child ⟨nested.2.1,nested.2.2.1⟩ nested.2.2.2 nested.1 tail

/-- The recursive closed-root evaluation and the original checked Meaning
equation refer to one terminal Value and one actual assertion occurrence. -/
theorem assertion {original : GenericOperation.Description} {closed : GenericOperation.Closed original}
    {artifact catalogue context description graph implementations references prepared root requested caller scope checked marker target}
    (asserted : @RuntimeSourceOperationMarkers.Assertion artifact catalogue context description graph implementations references prepared
      root requested caller scope checked marker target)
    (subject : RuntimeNativeSubject.Subject asserted) (matched : RuntimeClosedSubject.Checked closed subject.child.cursor) :
    Evaluation closed checked original.root matched.matched.terminal ∧
    RuntimeOperationTree.Equation matched.matched.terminal.value asserted.requirement asserted.equation.specification := by
  have evaluation := (evaluated closed matched.matched.paired).1
  have atRoot := (congrArg (fun i => Evaluation closed checked i matched.matched.terminal) closed.root_eq).mp evaluation
  have equation := asserted.equation.equation
  have same := subject.same.symm
  exact ⟨atRoot,
    ⟨matched.matched.ports.1.trans ((congrArg RuntimeOperationTree.Value.input same).trans equation.input),
     matched.matched.ports.2.trans ((congrArg RuntimeOperationTree.Value.output same).trans equation.output),
     matched.matched.action.trans ((congrArg RuntimeOperationTree.Value.action same).trans equation.action)⟩⟩

end QleisliKernel.Qirf.RuntimeClosedEvaluation
