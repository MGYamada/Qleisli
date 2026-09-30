import Qleisli.Semantics.Instrument
import Mathlib.Data.List.Nodup

/-! Coordinate laws for the independent initialize/unitary/readout semantics.
These lemmas keep declared axis order and exact complex phase. No checker or
algorithm model is imported. The caller must establish distinct physical axes;
separate ownership alone is not a product-state premise.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Semantics.Instrument
open QleisliKernel.Semantics
open scoped BigOperators

/-- Reading a declared coordinate assignment recovers every bit in order. -/
theorem assignment_axes (axes : List Nat) (distinct : axes.Nodup)
    (bits : Fin axes.length → Bool) :
    axes.map (assignment axes bits) = List.ofFn bits := by
  apply List.ext_getElem
  · simp
  · intro i first second
    have inside : i < axes.length := by simpa using first
    simp only [List.getElem_map]
    simp [assignment, distinct.idxOf_getElem i inside, inside]

/-- A basis state extended by freshly initialized zero coordinates. -/
def initializedBasis (old fresh : List Nat) (input : List Bool)
    (sized : input.length = old.length) : Fin (old ++ fresh).length → Bool :=
  fun i => (input ++ List.replicate fresh.length false)[i.val]'(by simpa [sized] using i.isLt)

theorem initializedBasis_list (old fresh : List Nat) (input : List Bool)
    (sized : input.length = old.length) :
    List.ofFn (initializedBasis old fresh input sized) =
      input ++ List.replicate fresh.length false := by
  apply List.ext_getElem
  · simp [sized]
  · intro i first second
    simp [initializedBasis]

/-- Zero initialization selects exactly one complete input basis column. -/
theorem initializedBasis_unique (old fresh : List Nat) (distinct : (old ++ fresh).Nodup)
    (input : List Bool) (sized : input.length = old.length)
    (basis : Fin (old ++ fresh).length → Bool) :
    fresh.all (fun axis => !assignment (old ++ fresh) basis axis) = true ∧
      old.map (assignment (old ++ fresh) basis) = input ↔
        basis = initializedBasis old fresh input sized := by
  have coordinates := assignment_axes (old ++ fresh) distinct basis
  rw [List.map_append] at coordinates
  constructor
  · rintro ⟨zero, before⟩
    have after : fresh.map (assignment (old ++ fresh) basis) = List.replicate fresh.length false := by
      apply List.eq_replicate_iff.mpr
      refine ⟨by simp, ?_⟩
      intro bit member
      obtain ⟨axis, present, rfl⟩ := List.mem_map.mp member
      have h := List.all_eq_true.mp zero axis present
      simpa using h
    apply List.ofFn_inj.mp
    rw [initializedBasis_list, ← coordinates, before, after]
  · intro same
    subst basis
    rw [initializedBasis_list] at coordinates
    have before : old.map (assignment (old ++ fresh) (initializedBasis old fresh input sized)) = input := by
      have taken := congrArg (List.take old.length) coordinates
      simpa [← sized] using taken
    have after : fresh.map (assignment (old ++ fresh) (initializedBasis old fresh input sized)) =
        List.replicate fresh.length false := by
      rw [before] at coordinates
      exact List.append_cancel_left coordinates
    refine ⟨List.all_eq_true.mpr ?_, before⟩
    intro axis member
    have bit : assignment (old ++ fresh) (initializedBasis old fresh input sized) axis ∈
        List.replicate fresh.length false := by
      rw [← after]
      exact List.mem_map.mpr ⟨axis,member,rfl⟩
    have zero := (List.mem_replicate.mp bit).2
    simp [zero]

/-- The complete input-space sum collapses to the actual old input column
extended by zeros. This is an exact complex identity, including global phase;
it assumes no special form or algorithmic property of the middle operator. -/
theorem specified_basis_coefficient (old fresh outputs measured : List Nat)
    (distinct : (old ++ fresh).Nodup) (operator : Coefficient)
    (input : List Bool) (sized : input.length = old.length)
    (outcome residual : Coordinates) :
    specified old fresh (old ++ fresh) outputs measured operator
      (fun label (_ : Unit) => if label = input then 1 else 0) outcome residual () =
        operator (outputs.map (Readout.select measured outcome residual))
          (input ++ List.replicate fresh.length false) := by
  rw [specified_coefficient]
  rw [Finset.sum_eq_single (initializedBasis old fresh input sized)]
  · have ready := (initializedBasis_unique old fresh distinct input sized
      (initializedBasis old fresh input sized)).mpr rfl
    simp only [ready.1,ready.2,↓reduceIte,mul_one]
    exact congrArg (operator (outputs.map (Readout.select measured outcome residual)))
      (initializedBasis_list old fresh input sized)
  · intro basis _ different
    by_cases zero : fresh.all (fun axis => !assignment (old ++ fresh) basis axis) = true
    · have other : old.map (assignment (old ++ fresh) basis) ≠ input := by
        intro same
        exact different ((initializedBasis_unique old fresh distinct input sized basis).mp ⟨zero,same⟩)
      simp [zero,other]
    · simp [zero]
  · intro missing
    exact False.elim (missing (Finset.mem_univ _))

/-- Operational initialization and measurement have the same exact column
formula. The theorem covers every outcome and every residual basis column. -/
theorem execute_branchMatrix (old fresh outputs measured residual : List Nat)
    (distinct : (old ++ fresh).Nodup) (operator : Coefficient)
    (outcome : Fin measured.length → Bool)
    (output : Fin residual.length → Bool) (input : Fin old.length → Bool) :
    branchMatrix old residual measured.length
      (execute old fresh (old ++ fresh) outputs measured operator) outcome output input =
        operator
          (outputs.map (Readout.select measured
            (fun position => (List.ofFn outcome)[position]?.getD false)
            (assignment residual output)))
          (List.ofFn input ++ List.replicate fresh.length false) := by
  unfold branchMatrix
  rw [execute_specified]
  exact specified_basis_coefficient old fresh outputs measured distinct operator
    (List.ofFn input) (by simp) _ _

end Qleisli.Semantics.Instrument
