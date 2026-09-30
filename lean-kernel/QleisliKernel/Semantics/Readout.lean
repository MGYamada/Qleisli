import Std

/-! Reference semantics for projective readout and little-endian classical bits.
This module does not import a checker. Coefficients may be complex and the
reference type is arbitrary; no tensor-product input assumption is made.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Semantics.Readout

/-- Position zero is the low bit, including the unique empty result. -/
def encode (bits : List Bool) : Nat :=
  bits.foldr (fun bit rest => (if bit then 1 else 0) + 2 * rest) 0

/-- Outcomes are indexed by measurement position, not by physical wire label.
An unmeasured coordinate remains exactly the caller's residual coordinate. -/
def select (axes : List Nat) (outcome : Nat → Bool) (residual : Nat → Bool)
    (axis : Nat) : Bool :=
  if axis ∈ axes then outcome (axes.idxOf axis) else residual axis

/-- Unnormalized branch amplitudes, including the residual target and reference.
Taking squared norms and sampling are separate execution responsibilities. -/
def branch {Scalar Reference : Type} (axes : List Nat) (outcome : Nat → Bool)
    (input : (Nat → Bool) → Reference → Scalar)
    (residual : Nat → Bool) (reference : Reference) : Scalar :=
  input (select axes outcome residual) reference

/-- Operational readout: consume one measurement outcome at a time. The
continuation receives the unnormalized post-measurement coefficient function. -/
def sequential {Scalar Reference : Type} (axes : List Nat) : (Nat → Bool) →
    ((Nat → Bool) → Reference → Scalar) → (Nat → Bool) → Reference → Scalar :=
  axes.foldr
    (fun axis next outcome input residual reference =>
      next (fun i => outcome (i + 1))
        (fun remaining ref => input (fun wire => if wire = axis then outcome 0 else remaining wire) ref)
        residual reference)
    (fun _ input residual reference => input residual reference)

theorem select_cons (axis : Nat) (axes : List Nat) (outcome residual : Nat → Bool) :
    select (axis :: axes) outcome residual =
      (fun wire => if wire = axis then outcome 0 else
        select axes (fun i => outcome (i + 1)) residual wire) := by
  funext wire
  by_cases same : wire = axis
  · subst wire; simp [select]
  · by_cases member : wire ∈ axes <;>
      simp [select, same, Ne.symm same, member, List.idxOf_cons, cond_eq_ite, beq_iff_eq]

/-- Sequential projective measurements implement the joint branch selector.
The checker separately excludes repeated/aliased axes via exact interfaces. -/
theorem sequential_branch {Scalar Reference : Type} (axes : List Nat)
    (outcome : Nat → Bool) (input : (Nat → Bool) → Reference → Scalar)
    (residual : Nat → Bool) (reference : Reference) :
    sequential axes outcome input residual reference = branch axes outcome input residual reference := by
  induction axes generalizing outcome input with
  | nil =>
    have identity : select [] outcome residual = residual := by
      funext axis
      simp [select]
    simp only [sequential, List.foldr_nil, branch, identity]
  | cons axis axes ih =>
    change sequential axes (fun i => outcome (i + 1))
      (fun remaining ref => input (fun wire => if wire = axis then outcome 0 else remaining wire) ref)
      residual reference = _
    rw [ih]
    simp only [branch, select_cons]

theorem select_unmeasured (axes : List Nat) (outcome residual : Nat → Bool)
    (axis : Nat) (unmeasured : axis ∉ axes) :
    select axes outcome residual axis = residual axis := by
  simp [select, unmeasured]

theorem select_measured (axes : List Nat) (outcome residual : Nat → Bool)
    (axis : Nat) (measured : axis ∈ axes) :
    select axes outcome residual axis = outcome (axes.idxOf axis) := by
  simp [select, measured]

theorem branch_empty {Scalar Reference : Type} (outcome : Nat → Bool)
    (input : (Nat → Bool) → Reference → Scalar)
    (residual : Nat → Bool) (reference : Reference) :
    branch [] outcome input residual reference = input residual reference := by
  have identity : select [] outcome residual = residual := by
    funext axis
    simp [select]
  rw [branch, identity]

theorem encode_bound (bits : List Bool) : encode bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [encode]
  | cons bit rest ih =>
    simp only [encode] at ih
    cases bit <;> simp only [encode, List.foldr_cons, List.length_cons, Nat.pow_succ,
      Bool.false_eq_true, ↓reduceIte] <;> omega

end QleisliKernel.Semantics.Readout
