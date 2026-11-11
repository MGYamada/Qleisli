import Qleisli.RuntimeBasisOwnerGeometry
import Qleisli.RuntimeBasisFibreRefinement
import Qleisli.RuntimeSemanticSelectionFibre

/-! The original basis expression acts on the complete caller owner forest.
The actual returned order, including zero-width spectators, is kept.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeBasisReference
open QleisliKernel QleisliKernel.Qirf
open RuntimeOwnerMap (Binding Map)
open RuntimeSemanticForest (Frame ownerLayout action)
open Qleisli.RuntimeBasisSourceAction (applyRow)
open Qleisli.RuntimeForestRegroup (sourceDimension)
open Qleisli.MixedRadix (recode)
open Qleisli.Semantics.RawAction (event)

noncomputable def sourceOperator {Reference : Type}
    (before after : Map) (operand returned : Binding) (row : List Nat)
    (joint : Nat → Reference → ℂ) (index : Nat) (reference : Reference) : ℂ :=
  let spectators := before.erase operand
  let inputOrder := operand :: spectators
  let outputOrder := returned :: spectators
  applyRow row (ownerLayout returned).labels.length
    (fun digit ref => joint (recode inputOrder before (sourceDimension before) digit) ref)
    (recode after outputOrder (sourceDimension outputOrder) index) reference

/-- Lift the checked original basis row to the same actual full Raw event,
with no assumption of separability or completeness of the physical code. -/
theorem original_reference_action {sources caller dependencies program block start count original before roles}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (checked : @RuntimeBasisAction.Checked sources caller dependencies program block start count original interval before)
    (owners : RuntimeOwnerMap.Checked roles interval.before) (same : owners.bindings = before.bindings)
    (input : Frame before.bindings) {row : List Nat} (member : row ∈ original.function.rows) :
    let operand : Binding := ⟨original.input,checked.input.port⟩
    let returned : Binding := ⟨original.output,checked.output⟩
    let prior := interval.before.quantum.frame
    let next := interval.after.quantum.frame
    ∃ output : Frame checked.after.bindings,
      ∀ {Reference : Type} (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference),
        physical < 2^next.length →
        event dependencies (.liftBasis prior.length next.length
          (operand.port.wires.map prior.idxOf) (returned.port.wires.map next.idxOf) checked.table)
          (fun index => action input prior joint index reference) physical =
        action output next (sourceOperator before.bindings checked.after.bindings operand returned row joint)
          physical reference := by
  intro operand returned prior next
  let others := before.bindings.erase operand
  obtain ⟨beforePerm,afterPerm⟩ := RuntimeBasisOwnerGeometry.binding_partitions checked owners same
  obtain ⟨beforeWires,afterWires⟩ := RuntimeBasisOwnerGeometry.wire_partitions checked owners same
  obtain ⟨growth,localGrowth,tableBound,_⟩ := RuntimeBasisOwnerGeometry.literal_geometry checked owners same
  obtain ⟨output⟩ := RuntimeSemanticForest.frame_exists
    (RuntimeBasisOwnerGeometry.after_available checked owners same input.available)
  obtain ⟨groupedInput⟩ : Nonempty (Frame (operand :: others)) :=
    RuntimeSemanticForest.frame_exists (fun b mem => input.available b (beforePerm.mem_iff.mp mem))
  obtain ⟨groupedOutput⟩ : Nonempty (Frame (returned :: others)) :=
    RuntimeSemanticForest.frame_exists (fun b mem => output.available b (afterPerm.mem_iff.mp mem))
  have beforeUnique := (Qleisli.RuntimeSemanticSelectionFibre.unique_bindings owners : owners.bindings.Nodup)
  rw [same] at beforeUnique
  have afterUnique := Qleisli.RuntimeSemanticSelectionFibre.unique_bindings checked.after
  have inputLayout : ownerLayout operand = checked.codes.inputLayout := by
    simp [ownerLayout,operand,checked.codes.inputRead]
  have outputLayout : ownerLayout returned = original.function.outputLayout := by
    simp [ownerLayout,returned,checked.sourceOwner.1,checked.codes.outputRead]
  have tableCheck : RuntimeBasisAction.rowsMatch (ownerLayout operand) (ownerLayout returned)
      original.function.rows checked.table = true := by
    rw [inputLayout,outputLayout]
    exact checked.codes.agreement
  refine ⟨output,?_⟩
  intro Reference joint physical reference bounded
  let grouped := fun digit ref => joint (recode (operand :: others) before.bindings (sourceDimension before.bindings) digit) ref
  have regroup (index : Nat) : action input prior joint index reference =
      action groupedInput prior grouped index reference :=
    RuntimeSemanticForest.regroup_action input groupedInput beforePerm.symm beforeUnique prior joint index reference
  simp only [regroup]
  have priorUnique := (QleisliKernel.Raw.Ownership.valid _ interval.history.1).frame
  have nextUnique := (QleisliKernel.Raw.Ownership.valid _ interval.history.2.2.1).frame
  rw [RuntimeBasisFibreRefinement.encoded_fibre groupedInput groupedOutput tableCheck member dependencies prior next
    (returned.port.wires.drop operand.port.bits) priorUnique nextUnique beforeWires afterWires growth
    localGrowth tableBound grouped physical reference bounded]
  exact RuntimeSemanticForest.regroup_action groupedOutput output afterPerm (afterPerm.nodup_iff.mpr afterUnique) next
    (applyRow row (ownerLayout returned).labels.length grouped) physical reference

#print axioms original_reference_action
end Qleisli.RuntimeBasisReference
