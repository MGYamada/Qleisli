import QleisliKernel.Tests.IntervalLegacy
import QleisliKernel.Tests.PureIntervalLegacy

/-! Equality of the complete executable computations, including errors and work.
Frozen baselines are test-only and are not alternate production acceptance paths.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.PureInterval.Many
open Finite

private theorem map_dite {α β : Type} (f : α → β) (p : Prop) [Decidable p]
    (yes : p → WorkM α) (no : ¬ p → WorkM α) :
    f <$> (if h : p then yes h else no h) =
      if h : p then f <$> yes h else f <$> no h := by
  split <;> rfl

private theorem map_interval_match {α β : Type} (f : α → β)
    (value : Option (List Semantics.Raw.Port)) (no : value = none → WorkM α)
    (yes : (ports : List Semantics.Raw.Port) → value = some ports → WorkM α) :
    f <$> finish.match_1 (fun _ => WorkM α) value no yes =
      QleisliKernel.Tests.PureIntervalLegacy.check.match_1 (fun _ => WorkM β) value
        (fun h => f <$> no h) (fun ports h => f <$> yes ports h) := by
  cases value <;> rfl

theorem standalone_refinement (arity dependencies program start count inputs outputs roles) :
    check arity dependencies program start count inputs outputs roles =
      QleisliKernel.Tests.IntervalLegacy.check arity dependencies program start count inputs outputs roles := by
  unfold check prepare finish QleisliKernel.Tests.IntervalLegacy.check
  simp only [bind_assoc, pure_bind]
  rfl

/-- The old public entrypoint and new arity specialization are the same core. -/
theorem two_owner_specialization (dependencies program start count inputs outputs roles) :
    (check 2 dependencies program start count inputs outputs roles).map Checked.toOriginal =
      QleisliKernel.Qirf.PureInterval.check dependencies program start count inputs outputs roles := rfl

/-- The actual former two-owner algorithm agrees for every starting budget,
including each failure and remaining-work result; this is not boolean testing. -/
theorem two_owner_legacy_refinement (dependencies program start count inputs outputs roles) :
    QleisliKernel.Qirf.PureInterval.check dependencies program start count inputs outputs roles =
      QleisliKernel.Tests.PureIntervalLegacy.check dependencies program start count inputs outputs roles := by
  change (Checked.toOriginal <$> check 2 dependencies program start count inputs outputs roles) = _
  unfold check prepare finish QleisliKernel.Tests.PureIntervalLegacy.check
  simp only [Finite.guard, Nat.reduceLeDiff, decide_true, ↓reduceIte,
    pure_bind, bind_assoc, map_bind, map_dite, map_interval_match, map_pure,
    ExceptT.map_throw, Checked.toOriginal]

end QleisliKernel.Qirf.PureInterval.Many
