/-
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
-/
import QPTL.FiniteMatrix

/-! A coherent control retains the active block exactly, including its phase. -/
namespace QPTL.FiniteMatrix
open scoped Matrix

variable {A : Type*} [DecidableEq A]

/-- On the first coordinate, the inactive block is identity and the active
block is the supplied operator. -/
noncomputable def controlled (op : Matrix A A ℂ) : Matrix (A × Bool) (A × Bool) ℂ :=
  Matrix.blockDiagonal (fun b => if b then op else 1)

@[simp] theorem controlled_active (op : Matrix A A ℂ) (row col : A) :
    controlled op (row,true) (col,true) = op row col := by
  simp [controlled,Matrix.blockDiagonal_apply_eq]

/-- Equality of the active block recovers the entire operator. In particular,
a projectively equivalent provider needs the same exact operator to supply
the same coherent control. -/
theorem controlled_injective : Function.Injective (controlled (A := A)) := by
  intro left right same
  ext row col
  simpa only [controlled_active] using
    congrArg (fun matrix => matrix (row,true) (col,true)) same

/-- A controlled sequence composes on the complete active and inactive
sectors without a quotient by global phase. -/
theorem controlled_mul [Fintype A] (first second : Matrix A A ℂ) :
    controlled (first * second) = controlled first * controlled second := by
  rw [controlled,controlled,controlled,← Matrix.blockDiagonal_mul]
  congr 1
  funext b
  cases b <;> simp

/-- Repeated application preserves the same control; the zero power has
identity in both sectors. -/
theorem controlled_pow [Fintype A] (op : Matrix A A ℂ) (n : Nat) :
    controlled (op ^ n) = controlled op ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, controlled, ite_self]
    simpa only [Pi.one_def] using (Matrix.blockDiagonal_one (m := A) (o := Bool) (α := ℂ))
  | succ power ih => rw [pow_succ, controlled_mul, ih, pow_succ]

/-- A literal scalar phase can be seen by reading the controlled active entry.
A nonzero entry suffices to separate a phase substitution. -/
theorem controlled_phase_ne (op : Matrix A A ℂ) {phase : ℂ} (different : phase ≠ 1)
    {row col : A} (nonzero : op row col ≠ 0) : controlled (phase • op) ≠ controlled op := by
  intro same
  have entry := congrArg (fun matrix : Matrix A A ℂ => matrix row col) (controlled_injective same)
  change phase * op row col = op row col at entry
  exact different (mul_right_cancel₀ nonzero (entry.trans (one_mul _).symm))

#print axioms controlled_mul
#print axioms controlled_pow
#print axioms controlled_phase_ne
end QPTL.FiniteMatrix
