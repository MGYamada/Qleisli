/-
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Necessary determinant conditions for exact same-wire realization.
The gate embeddings preserve the full scalar and the declared axis reindexing. -/

namespace QPTL.FiniteMatrix

open scoped Kronecker

/-- Embedding a gate with identity on the other axes raises its determinant
to the spectator dimension. Simultaneous reindexing preserves the result. -/
theorem det_embedded {A S P R : Type*} [Fintype A] [DecidableEq A]
    [Fintype S] [DecidableEq S] [Fintype P] [DecidableEq P] [CommRing R]
    (gate : Matrix A A R) (layout : A × S ≃ P) :
    (Matrix.reindex layout layout (gate ⊗ₖ (1 : Matrix S S R))).det =
      gate.det ^ Fintype.card S := by
  rw [Matrix.det_reindex_self, Matrix.det_kronecker]
  simp

/-- A determinant predicate containing one and closed under multiplication
is preserved by the ordered circuit product of its accepted generators. -/
theorem det_list_prod {P R : Type*} [Fintype P] [DecidableEq P] [CommRing R]
    {allowed : R → Prop} (identity : allowed 1)
    (multiply : ∀ {a b}, allowed a → allowed b → allowed (a * b))
    (steps : List (Matrix P P R))
    (generators : ∀ gate ∈ steps, allowed gate.det) : allowed steps.prod.det := by
  induction steps with
  | nil => simpa using identity
  | cons gate more ih =>
    rw [List.prod_cons, Matrix.det_mul]
    exact multiply (generators gate (List.mem_cons_self ..))
      (ih (fun gate member => generators gate (List.mem_cons_of_mem _ member)))

/-- An exact target operator with a forbidden determinant cannot be the
product of this gate list. The premise concerns the selected target profile. -/
theorem exact_same_wire_obstruction
    {P R : Type*} [Fintype P] [DecidableEq P] [CommRing R]
    {allowed : R → Prop} (identity : allowed 1)
    (multiply : ∀ {a b}, allowed a → allowed b → allowed (a * b))
    (steps : List (Matrix P P R))
    (generators : ∀ gate ∈ steps, allowed gate.det)
    {requested : Matrix P P R} (excluded : ¬ allowed requested.det) :
    steps.prod ≠ requested := by
  intro same
  exact excluded (same ▸ det_list_prod identity multiply steps generators)

#print axioms det_embedded
#print axioms exact_same_wire_obstruction

end QPTL.FiniteMatrix
