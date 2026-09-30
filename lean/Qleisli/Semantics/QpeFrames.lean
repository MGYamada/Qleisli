import Qleisli.Semantics.CoordinateOperators
import Qleisli.Semantics.InstrumentPartitions

/-! Independent bit-coordinate identities for an initialized phase register
and ordered computational-basis readout. No acceptance module is imported.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.QpeFrames
open CoordinateOperators

/-- If the complete target occupies the old input columns in order, every
other input coordinate belongs to the fresh phase register. -/
theorem phase_after_target (m n : Nat) (route : Equiv.Perm (Fin (m+n)))
    (target : ∀ i : Fin n, (route (i.natAdd m)).val = i.val) (i : Fin m) :
    n ≤ (route (i.castAdd n)).val := by
  by_contra earlier
  have bound : (route (i.castAdd n)).val < n := by omega
  let j : Fin n := ⟨(route (i.castAdd n)).val,bound⟩
  have equal : route (j.natAdd m) = route (i.castAdd n) := Fin.ext (target j)
  have equal := congrArg Fin.val (route.injective equal)
  simp only [Fin.val_natAdd,Fin.val_castAdd] at equal
  omega

/-- The phase-first abstract zero column equals the actual old-then-fresh
initialization list, even when the physical fresh coordinates are permuted. -/
theorem input_zero_list (m n : Nat) (route : Equiv.Perm (Fin (m+n)))
    (target : ∀ i : Fin n, (route (i.natAdd m)).val = i.val) (input : Bits n) :
    List.ofFn ((basisEquiv route).symm (Fin.append (fun _ : Fin m => false) input)) =
      List.ofFn input ++ List.replicate m false := by
  let zeroColumn : Bits (m+n) := fun i => if h : i.val < n then input ⟨i.val,h⟩ else false
  have frame : basisEquiv route zeroColumn = Fin.append (fun _ : Fin m => false) input := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have fresh := phase_after_target m n route target j
      simp [basisEquiv,zeroColumn,show ¬(route (j.castAdd n)).val < n by omega]
    · simp [basisEquiv,zeroColumn,target,j.isLt]
  rw [← frame,Equiv.symm_apply_apply]
  apply List.ext_getElem
  · simp; omega
  · intro i left right
    simp only [List.getElem_ofFn,List.getElem_append,List.length_ofFn,List.getElem_replicate]
    by_cases before : i < n
    · simp [zeroColumn,before]
    · simp [zeroColumn,before]

/-- Ordered readout rows in a separately declared final physical permutation.
The premise states individual coordinate labels, not an operator equation. -/
theorem output_row (m n : Nat) (inputRoute outputRoute : Equiv.Perm (Fin (m+n)))
    (outputAxes : Fin (m+n) → Nat) (measured : Fin m → Nat) (residual : Fin n → Nat)
    (distinct : (List.ofFn measured).Nodup)
    (separate : List.Disjoint (List.ofFn measured) (List.ofFn residual))
    (phase : ∀ i : Fin m, outputAxes (outputRoute.symm (inputRoute (i.castAdd n))) = measured i)
    (target : ∀ i : Fin n, outputAxes (outputRoute.symm (inputRoute (i.natAdd m))) = residual i)
    (outcome : Bits m) (output : Bits n) (residualState : Nat → Bool)
    (retained : ∀ i, residualState (residual i) = output i) :
    List.ofFn (basisEquiv outputRoute ((basisEquiv inputRoute).symm (Fin.append outcome output))) =
      List.ofFn (fun i => QleisliKernel.Semantics.Readout.select (List.ofFn measured)
        (fun k => (List.ofFn outcome)[k]?.getD false) residualState (outputAxes i)) := by
  let row : Bits (m+n) := fun i => QleisliKernel.Semantics.Readout.select (List.ofFn measured)
    (fun k => (List.ofFn outcome)[k]?.getD false) residualState (outputAxes i)
  have frame : basisEquiv inputRoute ((basisEquiv outputRoute).symm row) = Fin.append outcome output := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [basisEquiv,Equiv.coe_fn_mk,Equiv.symm_mk,Function.comp_apply,Fin.append_left,row]
      rw [phase]
      have position : (List.ofFn measured).idxOf (measured j) = j.val := by
        simpa using distinct.idxOf_getElem j.val (by simp)
      simp [QleisliKernel.Semantics.Readout.select,position]
    · simp only [basisEquiv,Equiv.coe_fn_mk,Equiv.symm_mk,Function.comp_apply,Fin.append_right,row]
      rw [target,QleisliKernel.Semantics.Readout.select_unmeasured]
      · exact retained j
      · intro member
        exact separate member (List.mem_ofFn.mpr ⟨j,rfl⟩)
  have equal := congrArg (fun bits => basisEquiv outputRoute ((basisEquiv inputRoute).symm bits)) frame
  simp only [Equiv.symm_apply_apply,Equiv.apply_symm_apply] at equal
  exact congrArg List.ofFn equal.symm

end Qleisli.Semantics.QpeFrames
