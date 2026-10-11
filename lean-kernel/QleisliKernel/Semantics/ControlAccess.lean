import QleisliKernel.Semantics.Finite

/-! Computational-basis sectors of an exact ordered finite interface.
This reference definition imports data only, not acceptance or reconstruction.
Zero coefficients retain their exact meaning regardless of denominator spelling.
It makes no ownership, separability, unchanged-state or scheduling claim.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.ControlAccess
open Exact Finite

def Zero (value : Scalar) : Prop :=
  value.a.numerator = 0 ∧ value.b.numerator = 0 ∧
  value.c.numerator = 0 ∧ value.d.numerator = 0

instance (value : Scalar) : Decidable (Zero value) := by
  unfold Zero
  infer_instance

/-- Original row/column labels use the ordered interface's bit coordinates.
An empty physical axis list is vacuous, not permission to forget a Unit owner. -/
def PreservesSectors (matrix : Matrix) (axes : List Nat) : Prop :=
  ∀ row ∈ List.range matrix.rows, ∀ col ∈ List.range matrix.cols,
    gather row axes ≠ gather col axes → Zero (matrix.entry row col)

end QleisliKernel.Semantics.ControlAccess
