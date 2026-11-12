import Qleisli.RawReconstructedAction
import Qleisli.RuntimeComputedForest
import Qleisli.RuntimeSemanticSelectionFibre

/-! The exact certified cleanup acts on the original data code in its actual
caller frame, preserving arbitrary reference amplitudes and spectators.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCertifiedComputedAction
open QleisliKernel Qirf
open RuntimeCertifiedComputed (Checked)
open RuntimeOwnerMap (Binding)
open RuntimeSemanticForest (Frame ownerLayout owner_layout)
open RuntimeSemanticSelectionFibre (target_slice target_update unique_bindings targetFibre)
open Semantics.Finite (gather scatter)
open Qleisli.Semantics.Exact (action)

theorem original_reference_action {sources caller dependencies program block start count event prepared interval before}
    (checked : @Checked sources caller dependencies program block start count event prepared interval before)
    (input : Frame before.bindings) :
    let operand : Binding := ⟨event.input,checked.literal.input.port⟩
    let frame := interval.before.quantum.frame
    let raw := Semantics.Raw.Event.computed frame.length (operand.port.wires.map frame.idxOf)
      operand.port.bits 1 checked.literal.table checked.literal.useSteps checked.literal.logicalSteps
    ∃ output : Frame checked.literal.after.bindings, ∀ {R : Type}
      (joint : Nat → R → ℂ) (row : Nat) (reference : R),
      Qleisli.Semantics.RawAction.event dependencies raw
        (fun i => RuntimeSemanticForest.action input frame joint i reference) row =
      RuntimeSemanticForest.action output interval.after.quantum.frame
        (RuntimeLiteralHistory.applySourceOwner before.bindings before.bindings operand operand prepared.logical.matrix joint)
        row reference := by
  intro operand frame raw
  have geometry := RuntimeComputedGeometry.certified_geometry checked.literal
  obtain ⟨output,rebound⟩ := RuntimeComputedForest.rebound_encoding_of_ports checked.literal.input
    checked.literal.output checked.literal.frame checked.literal.after checked.literal.afterBindings
    checked.literal.wires geometry.1 interval.history.2.2.1 input
  refine ⟨output,?_⟩
  intro R joint row reference
  let axes := operand.port.wires.map frame.idxOf
  have member : operand ∈ before.bindings := RuntimeBasisOwnerGeometry.selected_binding checked.literal.input
  have unique : before.bindings.Nodup := checked.literal.sameFrame ▸ unique_bindings checked.literal.frame
  have allAxes : (RuntimeForestCode.forestAxes frame before.bindings).Nodup := by
    simpa only [checked.literal.sameFrame,frame] using
      RuntimeNamedInputAction.axes_unique checked.literal.frame interval.history.1
  have layout := owner_layout (input.available operand member)
  have width : axes.length = (ownerLayout operand).bits := (List.length_map _).trans layout.2
  have held : operand ∈ checked.literal.frame.bindings := checked.literal.sameFrame.symm ▸ member
  have live := checked.literal.frame.complete.mem_iff.mp (List.mem_map.mpr ⟨operand,held,rfl⟩)
  have portBits := ((Raw.Ownership.valid _ interval.history.1).ports operand.port live).1
  have actualWidth : operand.port.bits = (ownerLayout operand).bits := portBits.trans layout.2
  obtain ⟨codeWork,codeLeft,codeRead⟩ := checked.logical.codeRead
  obtain ⟨shape,_,_,original,code,_⟩ :=
    FiniteCarrier.code_conditions _ _ codeWork codeLeft codeRead
  have sameLayout : shape = ownerLayout operand := Option.some.inj (original.symm.trans layout.1)
  have codeEq : checked.logical.code = Semantics.FiniteCarrier.encoding (ownerLayout operand) :=
    code.trans (congrArg Semantics.FiniteCarrier.encoding sameLayout)
  have rows : checked.logical.code.rows = 2^operand.port.bits := by rw [codeEq,actualWidth]; rfl
  have cols : checked.logical.code.cols = (ownerLayout operand).labels.length := by rw [codeEq]; rfl
  have size := checked.logical.action.logicalShape
  rw [checked.logical.equation,cols] at size
  obtain ⟨work,left,clean⟩ := checked.logical.emittedRead
  obtain ⟨result,first,last,otherFirst,otherLast,physical,specified⟩ := checked.logical.action.equation
  rw [checked.logical.equation] at specified
  let fibre := targetFibre before.bindings operand frame row joint
  let localRow := gather row axes
  have bounded : localRow < 2^operand.port.bits := by
    rw [actualWidth,← width]
    exact RuntimeForestProduct.gather_bound row axes
  have pull (digit : Nat) (small : digit < checked.logical.emitted.cols) :
      RuntimeSemanticForest.action input frame joint (scatter row axes digit) reference =
        action checked.logical.code fibre digit reference := by
    rw [checked.logical.action.physicalShape.1,rows,actualWidth] at small
    rw [codeEq]
    exact target_slice input unique operand member frame allAxes joint row digit reference small
  calc
    _ = action checked.logical.emitted
        (fun digit ref => RuntimeSemanticForest.action input frame joint (scatter row axes digit) ref)
        localRow reference := by
      have axesBits : axes.length = operand.port.bits := width.trans actualWidth.symm
      unfold raw
      change Qleisli.Semantics.RawAction.circuit dependencies
        ([Raw.computeStep operand.port.bits axes.length 1 checked.literal.table] ++ checked.literal.useSteps ++
          [Raw.computeStep operand.port.bits axes.length 1 checked.literal.table])
        (fun digit => if digit < 2^axes.length then
          RuntimeSemanticForest.action input frame joint (scatter row axes digit) reference else 0) localRow = _
      rw [axesBits]
      exact (Qleisli.Raw.ReconstructedAction.clean_action work left clean _ _ _ bounded).symm
    _ = action checked.logical.emitted (fun digit ref => action checked.logical.code fibre digit ref)
        localRow reference := by
      unfold action
      apply Qleisli.Exact.sum_map_congr
      intro digit present
      exact congrArg (Semantics.Exact.entry checked.logical.emitted localRow digit * ·)
        (pull digit (List.mem_range.mp present))
    _ = action checked.logical.code (fun digit ref => action prepared.logical.matrix fibre digit ref)
        localRow reference := by
      rw [← Qleisli.Exact.compose_action _ _ result first last physical _ _ _
        (checked.logical.action.physicalShape.2.symm ▸ (rows.symm ▸ bounded)),
        Qleisli.Exact.compose_action _ _ result otherFirst otherLast specified _ _ _ (rows.symm ▸ bounded)]
    _ = _ := by
      rw [rebound,codeEq,target_update input unique operand member frame prepared.logical.matrix size.1 size.2]

#print axioms original_reference_action
end Qleisli.RuntimeCertifiedComputedAction
