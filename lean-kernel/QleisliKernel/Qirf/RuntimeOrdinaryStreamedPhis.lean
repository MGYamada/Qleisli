import QleisliKernel.Qirf.RuntimeOrdinaryPhis
import QleisliKernel.Raw.StreamedInstrument

/-! Actual lazy-history companion to the ordinary source/SSA phi bridge.
The same original BranchEvent, actual Raw branch, fixed operand snapshots and
source valuation are retained. This module invokes StreamedInstrument.merge
itself; it never materializes or substitutes a dense history. Complete actual
hidden-history coverage and surrounding source/code checks remain enclosing
obligations. No native handle, dispatcher or wider profile is enabled here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeOrdinaryStreamedPhis
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open RuntimeOrdinarySSA

structure MergedAt {sources caller dependencies program block offset source actual before left right}
    (bound : @RuntimeOrdinaryPhis.Bound sources caller dependencies program block offset
      source actual before left right)
    (reference : Valuation) (history : Raw.StreamedInstrument.History) where
  condition : RuntimeOrdinaryPhis.ConditionAt bound reference history.values
  result : Raw.StreamedInstrument.History
  original : RuntimeInterval.Computed
    (Raw.StreamedInstrument.merge condition.value actual.classical history) result
  agreement : CheckedAgreement reference result.values bound.outputs

/-- Every actual phi is read simultaneously from this complete arm history.
The original source condition and output table use the same valuation/history
as the lazy Instrument operation. No outcome or coefficient is inspected to
select which histories are checked. -/
def readMerged {sources caller dependencies program block offset source actual before left right}
    (bound : @RuntimeOrdinaryPhis.Bound sources caller dependencies program block offset
      source actual before left right)
    (reference : Valuation) (history : Raw.StreamedInstrument.History) :
    WorkM (MergedAt bound reference history) := do
  let condition ← RuntimeOrdinaryPhis.readCondition bound reference history.values
  let merged ← NaturalAffine.witness (Raw.StreamedInstrument.merge condition.value actual.classical history)
  let agreement ← RuntimeOrdinarySSA.readAgreement reference merged.val.values bound.outputs
  return ⟨condition,merged.val,by with_reducible exact merged.property,agreement⟩

theorem merge_retains (choice : Bool) (phis : List Semantics.Observation.ClassicalPhi)
    (history result : Raw.StreamedInstrument.History) (work remaining : Nat)
    (executed : (Raw.StreamedInstrument.merge choice phis history).run work = (.ok result,remaining)) :
    result.hidden = history.hidden ∧ result.operator = history.operator := by
  unfold Raw.StreamedInstrument.merge at executed
  obtain ⟨values,middle,_read,finish⟩ := bind_success _ _ _ _ _ executed
  have same : result = {history with values := history.values ++ values} := (pure_success _ _ _ _ finish).1
  subst result
  exact ⟨rfl,rfl⟩

theorem MergedAt.retains {sources caller dependencies program block offset source actual before left right
    bound reference history}
    (merged : @MergedAt sources caller dependencies program block offset source actual before left right
      bound reference history) :
    merged.result.hidden = history.hidden ∧ merged.result.operator = history.operator := by
  obtain ⟨work,remaining,executed⟩ := merged.original
  exact merge_retains merged.condition.value actual.classical history merged.result work remaining executed

/-- Equality retains each actual coefficient computation, including failures
and remaining work. It is stronger than equal returned scalar values and does
not evaluate the operator while merging classical outputs. -/
theorem MergedAt.coefficient_run {sources caller dependencies program block offset source actual before left right
    bound reference history}
    (merged : @MergedAt sources caller dependencies program block offset source actual before left right
      bound reference history) (row col work : Nat) :
    (merged.result.operator row col).run work = (history.operator row col).run work := by
  rw [merged.retains.2]

end QleisliKernel.Qirf.RuntimeOrdinaryStreamedPhis
