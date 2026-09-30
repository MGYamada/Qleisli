import Std

/-! Fresh-zero coefficient semantics, independent of acceptance and producers.
The input coefficient function ranges over the retained axes and an arbitrary
reference. The new axes contribute precisely the computational zero factor.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Semantics.Preparation

def zero {Scalar Reference : Type} [OfNat Scalar 0] (axes : List Nat)
    (input : (Nat → Bool) → Reference → Scalar) (state : Nat → Bool)
    (reference : Reference) : Scalar :=
  if axes.all (fun axis => !state axis) then input state reference else 0

/-- Operational initialization, one fresh zero factor at a time. Use the
standard structural fold so compiled helpers remain within the runtime policy. -/
def sequential {Scalar Reference : Type} [OfNat Scalar 0] (axes : List Nat)
    (input : (Nat → Bool) → Reference → Scalar) : (Nat → Bool) → Reference → Scalar :=
  axes.foldr (fun axis next state reference => if state axis then 0 else next state reference) input

theorem sequential_zero {Scalar Reference : Type} [OfNat Scalar 0] (axes : List Nat)
    (input : (Nat → Bool) → Reference → Scalar) (state : Nat → Bool)
    (reference : Reference) :
    sequential axes input state reference = zero axes input state reference := by
  induction axes with
  | nil => simp [sequential, zero]
  | cons axis axes ih =>
    change (if state axis then 0 else sequential axes input state reference) = _
    rw [ih]
    cases h : state axis <;> simp [zero, h]

theorem zero_empty {Scalar Reference : Type} [OfNat Scalar 0]
    (input : (Nat → Bool) → Reference → Scalar) (state : Nat → Bool)
    (reference : Reference) : zero [] input state reference = input state reference := by
  simp [zero]

theorem zero_nonzero_branch {Scalar Reference : Type} [OfNat Scalar 0] (axes : List Nat)
    (input : (Nat → Bool) → Reference → Scalar) (state : Nat → Bool)
    (reference : Reference) (axis : Nat) (member : axis ∈ axes) (one : state axis = true) :
    zero axes input state reference = 0 := by
  have notAll : axes.all (fun a => !state a) = false := by
    apply Bool.eq_false_iff.mpr
    intro all
    have selected := List.all_eq_true.mp all axis member
    simp [one] at selected
  simp [zero, notAll]

end QleisliKernel.Semantics.Preparation
