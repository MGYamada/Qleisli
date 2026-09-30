import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Fresh initialization commutes with an operation on disjoint old coordinates.
The reference index is arbitrary: no product-state or absence-of-entanglement
assumption is made. A producer must separately establish the coordinate frames,
freshness and the exact operation being moved across initialization.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.FreshInitialization
open scoped BigOperators

variable {A B R : Type*} [Fintype A] [DecidableEq B]

/-- Append a fresh register in its designated zero basis state. -/
def freshZero (zero : B) (state : A → R → ℂ) : A → B → R → ℂ :=
  fun a b r => if b = zero then state a r else 0

/-- Apply an arbitrary exact linear map to the old coordinates, preserving
each external-reference coordinate. Unitarity is unnecessary for this identity. -/
def applyOld (operation : A → A → ℂ) (state : A → R → ℂ) : A → R → ℂ :=
  fun a r => ∑ x, operation a x * state x r

/-- This is the complete coefficient identity used for stable fresh-init
extraction. Both sides retain the same old operation and reference coordinate. -/
theorem commute (zero : B) (operation : A → A → ℂ) (state : A → R → ℂ) :
    (fun a b r => ∑ x, operation a x * freshZero zero state x b r) =
      freshZero zero (applyOld operation state) := by
  funext a b r
  by_cases same : b = zero <;> simp [freshZero,applyOld,same]

end Qleisli.Semantics.FreshInitialization
