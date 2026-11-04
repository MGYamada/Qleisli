import Init.Data.List.Find
import QleisliKernel.Qirf.RuntimeSelectionPartition
import QleisliKernel.Raw.Ownership

/-! Original selected axes from the same complete caller and source lookup.
Raw validity and the actual selected/complement partition supply distinctness
and frame membership. No Literal, supplied axis list, matrix equation or
additional acceptance check is a premise. Empty owners retain their cells.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeSelectionAxes
open QleisliKernel QleisliKernel.Qirf
open RuntimeOwnerMap (Binding Map)

private theorem index_injective (frame : List Nat) (left right : Nat)
    (leftMem : left ∈ frame) (rightMem : right ∈ frame)
    (same : frame.idxOf left = frame.idxOf right) : left = right := by
  induction frame with
  | nil => cases leftMem
  | cons first rest ih =>
    by_cases firstLeft : first = left
    · subst first
      by_cases leftRight : left = right
      · exact leftRight
      · simp [List.idxOf_cons,cond_eq_ite,beq_iff_eq,leftRight] at same
    · by_cases firstRight : first = right
      · subst first
        simp [List.idxOf_cons,cond_eq_ite,beq_iff_eq,firstLeft] at same
      · apply ih
          ((List.mem_cons.mp leftMem).resolve_left (Ne.symm firstLeft))
          ((List.mem_cons.mp rightMem).resolve_left (Ne.symm firstRight))
        simpa [List.idxOf_cons,cond_eq_ite,beq_iff_eq,firstLeft,firstRight] using same

private theorem indices_nodup (frame wires : List Nat) (unique : wires.Nodup)
    (covered : ∀ wire ∈ wires,wire ∈ frame) : (wires.map frame.idxOf).Nodup := by
  induction wires with
  | nil => exact List.nodup_nil
  | cons first rest ih =>
    obtain ⟨absent,remaining⟩ := List.nodup_cons.mp unique
    apply List.nodup_cons.mpr
    constructor
    · intro present
      obtain ⟨other,member,same⟩ := List.mem_map.mp present
      have equal := index_injective frame other first
        (covered other (List.mem_cons_of_mem _ member)) (covered first List.mem_cons_self) same
      exact absent (equal ▸ member)
    · exact ih remaining (fun wire member => covered wire (List.mem_cons_of_mem _ member))

private theorem selected_wires {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles) :
    (source.selected.toList.flatMap (fun binding => binding.port.wires)).Nodup ∧
      ∀ wire ∈ source.selected.toList.flatMap (fun binding => binding.port.wires),
        wire ∈ frame.interval.before.quantum.frame := by
  have valid := Raw.Ownership.valid _ frame.interval.history.1
  have complete : (source.before.bindings.flatMap (fun binding => binding.port.wires)).Perm
      (frame.interval.before.quantum.live.flatMap (fun port => port.wires)) := by
    simpa only [List.flatMap_map,Function.comp_def] using
      source.before.complete.flatMap_right (fun port => port.wires)
  have partition := (RuntimeSelectionPartition.source_input_partition frame source).flatMap_right
    (fun binding => binding.port.wires)
  have allUnique : (source.before.bindings.flatMap (fun binding => binding.port.wires)).Nodup := by
    apply complete.symm.nodup
    exact valid.exclusive
  rw [List.flatMap_append] at partition
  have selectedUnique := partition.symm.nodup allUnique
  refine ⟨(List.nodup_append.mp selectedUnique).1,?_⟩
  intro wire member
  have original := partition.mem_iff.mp (List.mem_append.mpr (Or.inl member))
  exact valid.covered wire (complete.mem_iff.mp original)

/-- The actual source-selected wire indices are distinct, including reversed
or interleaved physical placement. Width never identifies a logical owner. -/
theorem distinct {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles) :
    (RuntimeForestCode.forestAxes frame.interval.before.quantum.frame source.selected.toList).Nodup :=
  indices_nodup _ _ (selected_wires frame source).1 (selected_wires frame source).2

/-- Every selected index refers to the original complete caller frame. -/
theorem bounded {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles) :
    ∀ axis ∈ RuntimeForestCode.forestAxes frame.interval.before.quantum.frame source.selected.toList,
      axis < frame.interval.before.quantum.frame.length := by
  intro axis present
  obtain ⟨wire,member,rfl⟩ := List.mem_map.mp present
  exact List.idxOf_lt_length_of_mem ((selected_wires frame source).2 wire member)

#print axioms distinct
#print axioms bounded

end Qleisli.RuntimeSelectionAxes
