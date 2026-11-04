import Qleisli.RuntimeNamedPrimitiveSourceLift
import QleisliKernel.Qirf.RuntimeNamedPrimitiveOccurrence

/-! The source-to-caller action for a primitive recovered from the actual named
step. Its native form, ports and child fragment come from the indexed occurrence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedOccurrenceAction
open QleisliKernel QleisliKernel.Qirf QleisliKernel.SourceTypes
open RuntimeNamedPrimitiveOccurrence RuntimeNamedPrimitiveSourceLift

private def nativeForm {input output op} : Literal input output op → RuntimeNamedGateLift.Form
  | .gate gate => .gate gate
  | .applyUnitary steps => .applyUnitary steps

private theorem form_operation {input output op} (form : Literal input output op) :
    (nativeForm form).operation input output = op := by
  cases form <;> rfl

private abbrev AtScope {dependencies program block start count inputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    {ordered first size input output role kind}
    {action : RuntimePrimitiveAction.Checked scope.prepared.block first size input output role kind}
    (original : RuntimePrimitiveSource.Checked action) (bound : Bound scope ordered action) :=
  MixedAction scope bound.binding (nativeForm bound.form) output action original

private theorem atScope {dependencies program block start count inputs ordinary effect sources caller before child retired value}
    {event : SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    {first size input output role kind}
    {action : RuntimePrimitiveAction.Checked scope.prepared.block first size input output role kind}
    (original : RuntimePrimitiveSource.Checked action) (bound : Bound scope boundary.input.ordered action) :
    AtScope scope original bound := by
  have spelling : (nativeForm bound.form).operation bound.binding.port.token output = bound.operation := by
    rw [bound.token]
    exact form_operation bound.form
  refine mixed_reference_action scope boundary bound.binding bound.singleton (nativeForm bound.form) output ?_ action original ?_
  · rw [spelling]
    exact bound.parent
  · rw [bound.entry,bound.child,spelling]

/-- The compiled subject and source operator are fixed by the returned step. -/
def Action {dependencies program block step} (found : @Occurrence dependencies program block step) : Prop :=
  match found with
  | .named written bound => AtScope _ written bound

theorem preserved {dependencies program block step} (found : @Occurrence dependencies program block step) :
    Action found := by
  cases found with
  | @named _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ scope _ _ boundary _ _ written bound =>
    exact atScope scope boundary written bound

#print axioms preserved
end Qleisli.RuntimeNamedOccurrenceAction
