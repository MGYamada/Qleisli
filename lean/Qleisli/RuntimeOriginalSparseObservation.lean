import Qleisli.RuntimeOriginalObservation
import Qleisli.RuntimeStructuralHistory

/-! Exact erasure of the original measured or discarded owner in a sparse
source forest. The surviving layouts are carried independently of bounded
native carrier reconstruction.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeOriginalSparseObservation
open QleisliKernel QleisliKernel.Qirf
open RuntimeOwnerMap (Map)
open RuntimeForestCode (forestAxes embed sparseEntry tensor_agrees ofLayout_agrees)
open Qleisli.RuntimeSemanticForest (Frame action frame_exists ownerLayout owner_layout product product_agrees)
open Qleisli.RuntimeOriginalObservation
  (erase_at gather_retained erasure_geometry observation_bindings outcomeJointLayout)
open Qleisli.RuntimeForestProduct (layout_bounds gather_append)
open Qleisli.RuntimeForestOrderedProduct (agrees_entry layout_tensor_coefficient)
open Qleisli.Semantics.Exact (scalar entry)
open QleisliKernel.Semantics.Finite (gather)
open Semantics.FiniteCarrier (layout tensor)

private theorem action_cast {first second : Map} (same : first = second) (frame : Frame first)
    (physicalFrame : List Nat) {Reference : Type} (joint : Nat → Reference → ℂ) :
    action frame physicalFrame joint = action (same ▸ frame) physicalFrame joint := by
  cases same
  rfl

/-- Select the actual original erasure coordinate in each outcome. The
result is the exact source effect on the removed owner's layout tensored
with the unchanged surviving encoding, column by column. -/
theorem original_sparse_erasure_action {sources caller dependencies program functionName event block position previous}
    (checked : @RuntimeObservationAction.Checked sources caller dependencies program functionName
      event block position previous) (input : Frame checked.before.bindings) :
    let before := checked.interval.before.quantum.frame
    let after := checked.interval.after.quantum.frame
    let axes := checked.input.port.wires.map before.idxOf
    let removed := ownerLayout checked.input
    layout checked.operand.basis = some removed ∧
    removed.bits = axes.length ∧
    ∃ output : Frame checked.after.bindings,
      ∀ {Reference : Type} (joint : Nat → Reference → ℂ) outcome row,
        outcome < 2^axes.length → row < 2^after.length → ∀ ref,
        Qleisli.Semantics.ObservingAction.erase before.length axes outcome
          (fun physical => action input before joint physical ref) row =
            action output after (outcomeJointLayout removed outcome joint) row ref := by
  intro before after axes removed
  let kept := (List.range before.length).filter (fun axis => !axes.contains axis)
  have same := observation_bindings checked
  let ordered : Frame (checked.input :: checked.after.bindings) := same ▸ input
  obtain ⟨layoutRead,wireWidth⟩ := owner_layout (ordered.available checked.input List.mem_cons_self)
  have width : removed.bits = axes.length := by
    rw [show axes.length = checked.input.port.wires.length from List.length_map _]
    exact wireWidth.symm
  have positive := layout_bounds _ _ layoutRead
  obtain ⟨output⟩ := frame_exists (fun binding member =>
    ordered.available binding (List.mem_cons_of_mem _ member))
  refine ⟨checked.originalOwner ▸ layoutRead,width,output,?_⟩
  obtain ⟨partition,keptAxes,covered⟩ := erasure_geometry checked
  have afterWidth : after.length = kept.length := by
    simpa only [List.length_map] using congrArg List.length keptAxes
  let survivors := checked.after.bindings.flatMap (·.port.wires)
  have survivingWires : survivors ⊆ after := by
    intro wire member
    obtain ⟨binding,present,belongs⟩ := List.mem_flatMap.mp member
    exact covered binding present belongs
  have inputCode := product_agrees ordered
  have outputCode := product_agrees output
  have inputSize : ordered.code.dimension = removed.labels.length * output.code.dimension := by
    rw [inputCode.dimension,outputCode.dimension]
    change (tensor removed (product checked.after.bindings)).labels.length = _
    exact (tensor_agrees (ofLayout_agrees removed) (ofLayout_agrees (product checked.after.bindings))).dimension.symm
  intro Reference joint outcome row outcomeBound rowBound ref
  have rowKept : row < 2^kept.length := by simpa only [← afterWidth] using rowBound
  obtain ⟨physical,selected,retained,erased⟩ := erase_at before.length axes outcome row
    (fun physical => action input before joint physical ref) partition outcomeBound rowKept
  have retainedCoordinate : gather physical.val (survivors.map before.idxOf) =
      gather row (forestAxes after checked.after.bindings) := by
    rw [← gather_retained before after survivors kept keptAxes survivingWires physical.val,retained]
    rfl
  have gathered : gather physical.val (forestAxes before (checked.input :: checked.after.bindings)) =
      outcome + 2^removed.bits * gather row (forestAxes after checked.after.bindings) := by
    simp only [forestAxes,List.flatMap_cons,List.map_append]
    change gather physical.val (axes ++ survivors.map before.idxOf) = _
    rw [gather_append,selected,retainedCoordinate,← width]
    rfl
  rw [erased,action_cast same input before joint]
  unfold action
  rw [inputSize,Qleisli.RuntimeNamedHeadCoefficients.sum_blocks]
  apply Qleisli.Exact.sum_map_congr
  intro tail _
  unfold outcomeJointLayout
  rw [← List.sum_map_mul_left]
  apply Qleisli.Exact.sum_map_congr
  intro digit member
  have bound := List.mem_range.mp member
  unfold embed
  rw [agrees_entry inputCode,agrees_entry outputCode,gathered]
  change scalar (sparseEntry (.ofLayout (tensor removed (product checked.after.bindings)))
      (outcome + 2^removed.bits * gather row (forestAxes after checked.after.bindings))
      (digit + removed.labels.length * tail)) * joint (digit + removed.labels.length * tail) ref = _
  have outcomeSmall : outcome < 2^removed.bits := by simpa only [width] using outcomeBound
  rw [layout_tensor_coefficient removed _ positive _ _ _ outcomeSmall,Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt bound,Nat.add_mul_div_left _ _ positive.1,Nat.div_eq_of_lt bound,Nat.zero_add]
  have coefficient := (ofLayout_agrees removed).encodingEntry outcome digit outcomeSmall bound
  rw [coefficient]
  unfold entry
  ring

#print axioms original_sparse_erasure_action
end Qleisli.RuntimeOriginalSparseObservation
