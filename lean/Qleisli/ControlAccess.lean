import Qleisli.Semantics.Exact
import QleisliKernel.Qirf.ControlAccess
import Mathlib.Algebra.BigOperators.Ring.List

/-! Exact complex meaning of the bounded original-artifact sector obligation.
Projectors act on the full joint amplitude with an arbitrary reference index.
Phase kickback and correlations are retained; no separability premise occurs.
This is not source-place preservation, scheduling or a new ledger guarantee.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.ControlAccess
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.ControlAccess Qleisli.Semantics.Exact

theorem zero_scalar (value : Scalar) (h : Zero value) : scalar value = 0 := by
  rcases h with ⟨ha,hb,hc,hd⟩
  simp [scalar,rational,ha,hb,hc,hd]

/-- A computational-sector projector, without observing the joint state. -/
def project {R : Type} (axes : List Nat) (sector : Nat) (joint : Nat → R → ℂ)
    (row : Nat) (reference : R) : ℂ :=
  if gather row axes = sector then joint row reference else 0

/-- Exact operator/projector commutation, simultaneously for every input joint
amplitude and reference. This is not equality up to phase or a numerical test. -/
theorem action_project (matrix : Matrix) (axes : List Nat)
    (preserves : PreservesSectors matrix axes) {R : Type}
    (joint : Nat → R → ℂ) (row : Nat) (hr : row ∈ List.range matrix.rows)
    (sector : Nat) (reference : R) :
    action matrix (project axes sector joint) row reference =
      project axes sector (action matrix joint) row reference := by
  unfold action project
  by_cases hrow : gather row axes = sector
  · simp only [hrow, if_pos]
    congr 1
    apply List.map_congr_left
    intro col hc
    by_cases hcol : gather col axes = sector
    · simp [hcol]
    · have different : gather row axes ≠ gather col axes := by
        intro same
        exact hcol (same.symm.trans hrow)
      have vanished := zero_scalar _ (preserves row hr col hc different)
      simp [hcol,entry,vanished]
  · simp only [hrow]
    apply List.sum_eq_zero
    intro value hv
    obtain ⟨col,hc,rfl⟩ := List.mem_map.mp hv
    by_cases hcol : gather col axes = sector
    · have different : gather row axes ≠ gather col axes := by
        intro same
        exact hrow (same.trans hcol)
      have vanished := zero_scalar _ (preserves row hr col hc different)
      simp [hcol,entry,vanished]
    · simp [hcol]

/-- Connect the exact joint-reference law to the actual checked original QIRF
matrix. The original-root/reconstruction binding remains in check_bound. -/
theorem checked_action_project (artifact : QleisliKernel.Qirf.Artifact)
    (order : Array Nat) (signature : Basis) (axes : List Nat) (matrix : Matrix)
    (work left : Nat)
    (ok : (QleisliKernel.Qirf.ControlAccess.check artifact order signature axes).run work =
      (.ok matrix,left)) {R : Type} (joint : Nat → R → ℂ) (row : Nat)
    (hr : row ∈ List.range matrix.rows) (sector : Nat) (reference : R) :
    action matrix (project axes sector joint) row reference =
      project axes sector (action matrix joint) row reference := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,preserves⟩ :=
    QleisliKernel.Qirf.ControlAccess.check_bound _ _ _ _ _ _ _ ok
  exact action_project matrix axes preserves joint row hr sector reference

end Qleisli.ControlAccess
