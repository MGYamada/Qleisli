import QleisliKernel.Semantics.OrdinaryValue

/-! Independent ordinary argument-code semantics. This describes
classical finite data only; no source, acceptance or runtime check defines it.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.OrdinaryInputs
open FiniteCarrier OrdinaryValue

/-- Argument count and each complete type remain in the separate forest.
Its ordered code puts the first argument on the low coordinates. -/
def forest (bases : List Basis) : Option Layout :=
  bases.foldr (fun basis rest => do return tensor (← layout basis) (← rest)) (some singleton)

/-- Low-coordinate-first finite binary expansion, including width zero. -/
def bits : Nat → Nat → List Bool :=
  Nat.rec (fun _ => []) (fun _ next label => (label % 2 == 1) :: next (label / 2))

theorem bits_length (width label : Nat) : (bits width label).length = width := by
  induction width generalizing label with
  | zero => rfl
  | succ width ih =>
    change (bits width (label/2)).length + 1 = width + 1
    rw [ih]

/-- Every enumerated code is supplied to the actual input bindings in its
original value, rather than duplicated, permuted or truncated to another row. -/
theorem bits_value (width label : Nat) (bound : label < 2^width) :
    littleEndian (bits width label) = label := by
  induction width generalizing label with
  | zero =>
    have same : label = 0 := by simpa using bound
    subst label
    rfl
  | succ width ih =>
    have modulus := Nat.mod_lt label (by decide : 0 < 2)
    have decomposition := Nat.mod_add_div label 2
    have power : 2^(width+1) = 2^width * 2 := Nat.pow_succ 2 width
    have half : label / 2 < 2^width := by rw [power] at bound; omega
    have low : (if label % 2 == 1 then 1 else 0) = label % 2 := by
      by_cases one : label % 2 = 1
      · simp [one]
      · simp [one]; omega
    change (if label % 2 == 1 then 1 else 0) + 2 * littleEndian (bits width (label/2)) = label
    rw [low,ih (label/2) half]
    exact decomposition

end QleisliKernel.Semantics.OrdinaryInputs
