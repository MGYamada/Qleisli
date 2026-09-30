import Qleisli.Semantics.InstrumentCoordinates
import Qleisli.Semantics.InstrumentComplete

/-! Independent coordinate partitions for complete projective instruments.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
This module has no checker imports. A later acceptance theorem must derive the
distinctness, disjointness and complete coverage premises from actual IR. -/

namespace Qleisli.Semantics.Instrument
open QleisliKernel.Semantics

def coordinateBits (axes : List Nat) (state : Coordinates) : Fin axes.length → Bool :=
  fun i => state axes[i]

theorem coordinateBits_list (axes : List Nat) (state : Coordinates) :
    List.ofFn (coordinateBits axes state) = axes.map state := by
  apply List.ext_getElem
  · simp
  · intro i left right
    simp [coordinateBits]

theorem assignment_coordinateBits (axes : List Nat) (state : Coordinates)
    (axis : Nat) (member : axis ∈ axes) :
    assignment axes (coordinateBits axes state) axis = state axis := by
  have inside := List.idxOf_lt_length_of_mem member
  simp [assignment,coordinateBits,inside]

theorem assignment_at (axes : List Nat) (distinct : axes.Nodup)
    (bits : Fin axes.length → Bool) (i : Fin axes.length) :
    assignment axes bits axes[i] = bits i := by
  simp [assignment,distinct.idxOf_getElem i.val i.isLt]

/-- Every measured/outcome bit and every retained bit contributes exactly once
to the complete output basis, in the independently declared output order. -/
def outputEquiv (outputs measured residual : List Nat)
    (outputND : outputs.Nodup) (measuredND : measured.Nodup) (residualND : residual.Nodup)
    (separate : List.Disjoint measured residual)
    (complete : outputs.Perm (measured ++ residual)) :
    ((Fin measured.length → Bool) × (Fin residual.length → Bool)) ≃ (Fin outputs.length → Bool) where
  toFun pair := coordinateBits outputs
    (Readout.select measured (fun i => (List.ofFn pair.1)[i]?.getD false)
      (assignment residual pair.2))
  invFun bits := (coordinateBits measured (assignment outputs bits),
    coordinateBits residual (assignment outputs bits))
  left_inv pair := by
    apply Prod.ext
    · funext i
      change assignment outputs (coordinateBits outputs _) measured[i] = pair.1 i
      have member : measured[i] ∈ outputs := complete.mem_iff.mpr (by simp)
      rw [assignment_coordinateBits outputs _ _ member]
      simp [Readout.select,measuredND.idxOf_getElem i.val i.isLt]
    · funext i
      change assignment outputs (coordinateBits outputs _) residual[i] = pair.2 i
      have member : residual[i] ∈ outputs := complete.mem_iff.mpr (by simp)
      have unmeasured : residual[i] ∉ measured := fun h => separate h (List.getElem_mem _)
      rw [assignment_coordinateBits outputs _ _ member,Readout.select_unmeasured _ _ _ _ unmeasured]
      exact assignment_at residual residualND pair.2 i
  right_inv bits := by
    funext i
    change Readout.select measured _ _ outputs[i] = bits i
    have member : outputs[i] ∈ measured ∨ outputs[i] ∈ residual := by
      simpa using complete.mem_iff.mp (List.getElem_mem _)
    rcases member with measuredHere | residualHere
    · rw [Readout.select_measured _ _ _ _ measuredHere]
      change assignment measured (coordinateBits measured (assignment outputs bits)) outputs[i] = bits i
      rw [assignment_coordinateBits measured _ _ measuredHere]
      exact assignment_at outputs outputND bits i
    · by_cases measuredHere : outputs[i] ∈ measured
      · exact False.elim (separate measuredHere residualHere)
      · rw [Readout.select_unmeasured _ _ _ _ measuredHere,
          assignment_coordinateBits residual _ _ residualHere]
        exact assignment_at outputs outputND bits i

/-- The zero-input column embedding keeps every input bit exactly; no two old
basis states become the same initialized basis state. -/
theorem initializedBasis_injective (old fresh : List Nat) :
    Function.Injective (fun input : Fin old.length → Bool =>
      initializedBasis old fresh (List.ofFn input) (by simp)) := by
  intro first second same
  have lists := congrArg List.ofFn same
  simp only [initializedBasis_list] at lists
  exact List.ofFn_inj.mp (List.append_cancel_right lists)

open scoped BigOperators Matrix

/-- A full row partition and an injective zero-input embedding make the exact
branch matrices complete. The caller must establish these coordinate premises
and the column equation independently of this finite matrix argument. -/
theorem branchMatrix_complete (old fresh outputs measured residual : List Nat)
    (outputND : outputs.Nodup) (measuredND : measured.Nodup) (residualND : residual.Nodup)
    (separate : List.Disjoint measured residual)
    (partition : outputs.Perm (measured ++ residual))
    (precision : Nat) (length : measured.length = precision)
    (transform : Transform Unit) (coefficient : Coefficient)
    (isometry : let matrix : Matrix (Fin outputs.length → Bool) (Fin (old++fresh).length → Bool) ℂ :=
      fun output input => coefficient (List.ofFn output) (List.ofFn input)
      matrixᴴ * matrix = 1)
    (columns : ∀ outcome output input,
      branchMatrix old residual precision transform outcome output input =
        coefficient (outputs.map (Readout.select measured
          (fun position => (List.ofFn outcome)[position]?.getD false)
          (assignment residual output)))
          (List.ofFn input ++ List.replicate fresh.length false)) :
    ∑ outcome, (branchMatrix old residual precision transform outcome)ᴴ *
      branchMatrix old residual precision transform outcome = 1 := by
  subst precision
  let rows := outputEquiv outputs measured residual outputND measuredND residualND separate partition
  let embed := fun input : Fin old.length → Bool => initializedBasis old fresh (List.ofFn input) (by simp)
  let matrix : Matrix (Fin outputs.length → Bool) (Fin (old++fresh).length → Bool) ℂ :=
    fun output input => coefficient (List.ofFn output) (List.ofFn input)
  have complete := sliced_complete matrix isometry embed (initializedBasis_injective old fresh) rows
  have equal : branchMatrix old residual measured.length transform = sliced matrix embed rows := by
    funext outcome output input
    rw [columns]
    simp only [sliced,matrix,embed,rows,outputEquiv,Equiv.coe_fn_mk]
    rw [coordinateBits_list,initializedBasis_list]
  rw [equal]
  exact complete

end Qleisli.Semantics.Instrument
