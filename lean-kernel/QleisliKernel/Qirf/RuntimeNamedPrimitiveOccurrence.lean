import QleisliKernel.Qirf.RuntimeNamedFrameAxes

/-! Recover a one-primitive named call from the body the common checker returned.
This inspection uses the stored child interval on the named frame's own block.
It does not rerun source traversal, Raw verification or matrix reconstruction.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNamedPrimitiveOccurrence
open QleisliKernel Finite SourceTypes

inductive Literal (input output : Nat) : Semantics.Raw.Op → Type where
  | gate (gate : Semantics.Raw.Gate) : Literal input output (.gate gate input output)
  | applyUnitary (steps : List Semantics.Finite.Step) : Literal input output (.applyUnitary input output steps)

private def literal? (input output : Nat) : (op : Semantics.Raw.Op) → Option (Literal input output op)
  | .gate gate i o => do
    if h : (i,o) = (input,output) then
      return (by obtain ⟨rfl,rfl⟩ := Prod.mk.inj h; exact .gate gate)
    else none
  | .applyUnitary i o steps => do
    if h : (i,o) = (input,output) then
      return (by obtain ⟨rfl,rfl⟩ := Prod.mk.inj h; exact .applyUnitary steps)
    else none
  | _ => none

structure Bound {dependencies program block start count inputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (ordered : RuntimeOwnerMap.Map) {first size input output role kind}
    (action : RuntimePrimitiveAction.Checked scope.prepared.block first size input output role kind) where
  binding : RuntimeOwnerMap.Binding
  singleton : ordered = [binding]
  token : binding.port.token = input
  entry : action.interval.selected = [binding.port]
  outputs : scope.returned.map (·.token) = [output]
  operation : Semantics.Raw.Op
  form : Literal input output operation
  child : action.interval.operations = [operation]
  parent : (block.operations.drop start).take count = [.pure operation]

private def bind? {dependencies program block start count inputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (ordered : RuntimeOwnerMap.Map) {first size input output role kind}
    (action : RuntimePrimitiveAction.Checked scope.prepared.block first size input output role kind) :
    Option (Bound scope ordered action) := do
  match ordered, child : action.interval.operations with
  | [binding], [operation] =>
    let form ← literal? input output operation
    if aligned : first = 0 ∧ size = ((block.operations.drop start).take count).length ∧
        binding.port.token = input ∧ action.interval.selected = [binding.port] ∧
        scope.returned.map (·.token) = [output] then
      let ⟨atStart,covers,token,entry,outputs⟩ := aligned
      return ⟨binding,rfl,token,entry,outputs,operation,form,child,by
        calc
          _ = (((block.operations.drop start).take count).drop first).take size := by
            rw [atStart,List.drop_zero,covers,List.take_length]
          _ = action.interval.operations.map Semantics.Observation.Op.pure := action.interval.literal
          _ = _ := congrArg (List.map Semantics.Observation.Op.pure) child⟩
    else none
  | _, _ => none

/-- The index is the original named step, including the precise source event,
callee, primitive, and ordered child body. -/
inductive Occurrence {dependencies program block} : RuntimePureBody.Step dependencies program block → Type where
  | named {start count inputs sources caller before childHistory childRetired ordinary first size input output role kind}
      {event : SourceRuntimeContext.NamedEvent sources caller}
      {scope : RuntimeCallScope.Checked block start count inputs ordinary event.effect}
      {body : SourceRuntimeTrace.Body event.target.signature}
      {read : RuntimeInterval.Computed (SourceRuntimeTrace.readNamedBody event) body}
      {boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before childHistory childRetired body.checked.summary.value}
      {finalOrdinary : RuntimeOrdinaryBody.State}
      {action : RuntimePrimitiveAction.Checked scope.prepared.block first size input output role kind}
      (original : RuntimePrimitiveSource.Checked action)
      (bound : Bound scope boundary.input.ordered action) :
      Occurrence (.named event scope body read boundary finalOrdinary (.cons (.pure (.primitive action original)) .nil))

def inspect? {dependencies program block} (step : RuntimePureBody.Step dependencies program block) :
    Option (Occurrence step) :=
  match step with
  | .named _ scope _ _ boundary _ (.cons (.pure (.primitive action original)) .nil) => do
    let bound ← bind? scope boundary.input.ordered action
    return .named original bound
  | _ => none

end QleisliKernel.Qirf.RuntimeNamedPrimitiveOccurrence
