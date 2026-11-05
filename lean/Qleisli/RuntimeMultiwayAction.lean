import Qleisli.RuntimeMultiwayGram
import Qleisli.RuntimeCarrierLabels

/-! Physical selector coordinates and actual original-ordinal arm receipts.
Native layout labels retain padding and product order; only logical ordinals
index the complete arm table. Support and uniqueness follow from the same
source-owner/code reads, not a guessed ordinal-to-wire identity or extra Gram
premise. No joined matrix, native gate or bounded availability is introduced.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeMultiwayAction
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics.Exact
open QleisliKernel.Semantics.Finite (gather scatter bit width)
open QleisliKernel.FiniteRestriction (pack)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct Qleisli.MixedRadix
open Qleisli.RuntimeMultiwayGram

/-- The finite selector ordinal in the complete caller's original order. -/
def originalOrdinal
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode selectorBits targetBits retained restricted labels}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (index : Fin literal.outputCode.code.dimension) : Fin labels.length :=
  selectorIndex literal.outputCode codes.owners.returned.first
    ((RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered).1 (by simp))
    (selector_card frame codes layouts literal) index

/-- Nonzero full-forest support relates the original selector digit to the
native physical code label. It does not identify the digit with that label. -/
theorem selector_support
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode selectorBits targetBits retained restricted labels}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (physical : Nat) (index : Fin literal.outputCode.code.dimension)
    (nonzero : scalar (literal.outputCode.embedding physical index.val) ≠ 0) :
    labels[(originalOrdinal frame codes layouts literal index).val] =
      gather physical (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) := by
  obtain ⟨actual,_found,layout⟩ := returned_selector_layout frame codes layouts literal
  have support := Qleisli.RuntimeNominalSupport.returned_selector_support frame codes.owners literal
    actual physical index.val index.isLt nonzero
  let ordinal := originalOrdinal frame codes layouts literal index
  have coded : labels[ordinal.val]? = some
      (gather physical (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf)) := by
    simpa only [layout] using support.2
  rw [List.getElem?_eq_getElem ordinal.isLt] at coded
  exact Option.some.inj coded

/-- One actual physical code label determines the same original ordinal in
every nonzero coefficient, even for a padded product/nominal selector. -/
theorem supported_ordinal
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode selectorBits targetBits retained restricted labels}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (physical : Nat) (index : Fin literal.outputCode.code.dimension) (ordinal : Fin labels.length)
    (coordinate : gather physical
      (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) = labels[ordinal.val])
    (nonzero : scalar (literal.outputCode.embedding physical index.val) ≠ 0) :
    originalOrdinal frame codes layouts literal index = ordinal := by
  obtain ⟨actual,_found,layout⟩ := returned_selector_layout frame codes layouts literal
  have unique : labels.Nodup := by
    have retained := Qleisli.RuntimeCarrierLabels.owner_labels actual
    simpa only [layout] using retained
  have equal := (selector_support frame codes layouts literal physical index nonzero).trans coordinate
  apply Fin.ext
  apply (List.getElem?_inj (originalOrdinal frame codes layouts literal index).isLt unique).mp
  rw [List.getElem?_eq_getElem (originalOrdinal frame codes layouts literal index).isLt,
    List.getElem?_eq_getElem ordinal.isLt]
  exact congrArg some equal

/-- Select the real native receipt with the physical label of a supported
output coefficient, while its matrix is selected by the original ordinal. -/
theorem selected_receipt
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {labels : List Nat} {arms : List Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (table : OrdinalTable inputCode outputCode retained.sectors labels arms)
    (physical : Nat) (index : Fin literal.outputCode.code.dimension)
    (nonzero : scalar (literal.outputCode.embedding physical index.val) ≠ 0) :
    QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode retained.sectors
      (gather physical (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf),
        table.arm (originalOrdinal frame codes layouts literal index))
      (table.arm (originalOrdinal frame codes layouts literal index)) := by
  have binding := table.arm_checked (originalOrdinal frame codes layouts literal index)
  simpa only [selector_support frame codes layouts literal physical index nonzero] using binding

/-- The actual returned selector axes keep their native width and precede
the actual single target axis in local sector order. Distinctness comes from
the same complete Raw owner partition, including zero-width selector owners. -/
theorem returned_axes
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode selectorBits retained restricted labels}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits 1 labels)
    (targetBasis : target.basis = [.bit])
    (literal : RuntimeLocalEvents.Literal frame selectorBits 1 retained restricted
      codes.owners.before codes.owners.transport.after) :
    ∃ axis,
      codes.owners.returned.second.port.wires.map frame.interval.after.quantum.frame.idxOf = [axis] ∧
      (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf).length = selectorBits ∧
      forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList =
        codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf ++ [axis] ∧
      (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList).Nodup := by
  obtain ⟨first,_found,firstLayout⟩ := returned_selector_layout frame codes layouts literal
  have firstLength := first.reference.2.2
  rw [firstLayout] at firstLength
  have selected := RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered
  have member : codes.owners.returned.second ∈ codes.owners.transport.after.bindings := selected.1 (by simp)
  have owners : codes.owners.returned.first.owner = selector ∧ codes.owners.returned.second.owner = target := by
    simpa only [List.map_cons,List.map_nil,List.cons.injEq,and_true] using selected.2
  obtain ⟨second,_found⟩ := lookup_exists literal.outputCode.owners codes.owners.returned.second member
  have secondLength := second.reference.2.2
  rw [Qleisli.RuntimeTargetScatter.bit_layout second (by rw [owners.2,targetBasis])] at secondLength
  obtain ⟨axis,axisRead⟩ := Qleisli.RuntimeTargetScatter.singleton_axis
    (codes.owners.returned.second.port.wires.map frame.interval.after.quantum.frame.idxOf)
    (by simpa only [List.length_map] using secondLength)
  have axes : forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList =
      codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf ++ [axis] := by
    change (codes.owners.returned.first.port.wires ++ (codes.owners.returned.second.port.wires ++ [])).map
      frame.interval.after.quantum.frame.idxOf = _
    rw [List.append_nil,List.map_append,axisRead]
  have permutation := RuntimeSelectionPartition.source_output_partition frame codes.owners
  have mapped := (permutation.flatMap_right (fun binding : RuntimeOwnerMap.Binding => binding.port.wires)).map
    frame.interval.after.quantum.frame.idxOf
  have allUnique := mapped.symm.nodup (Qleisli.RuntimeTargetScatter.output_axes_unique frame codes.owners)
  have appended : (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList ++
      forestAxes frame.interval.after.quantum.frame (RuntimeSelectionPartition.complement
        codes.owners.transport.after.bindings codes.owners.returned.toList)).Nodup := by
    simpa only [forestAxes,List.flatMap_append,List.map_append] using allUnique
  exact ⟨axis,axisRead,by simpa only [List.length_map] using firstLength,axes,(List.nodup_append.mp appended).1⟩

private theorem write_packed_target (width label row input : Nat)
    (labelBound : label < 2^width) (rowBound : row < 2) :
    RuntimeScatterTransport.write (pack width label row) width input = pack width label input := by
  have high := QleisliKernel.FiniteRestriction.bit_target width label row 0 labelBound
  simp only [Nat.add_zero] at high
  have low : bit row 0 = row := by simp [bit,Nat.mod_eq_of_lt rowBound]
  rw [low] at high
  unfold RuntimeScatterTransport.write
  rw [high]
  unfold pack
  rw [Nat.mul_comm row (2^width),Nat.add_sub_cancel_right,Nat.mul_comm input (2^width)]

private theorem last_axis_set (physical : Nat) (selectorAxes : List Nat) (axis width label row input : Nat)
    (length : selectorAxes.length = width) (unique : (selectorAxes ++ [axis]).Nodup)
    (coordinate : gather physical (selectorAxes ++ [axis]) = pack width label row)
    (labelBound : label < 2^width) (rowBound : row < 2) (small : input < 2) :
    scatter physical (selectorAxes ++ [axis]) (pack width label input) = scatter physical [axis] input := by
  have inside : width < (selectorAxes ++ [axis]).length := by simp [length]
  have target : (selectorAxes ++ [axis])[width]'inside = axis :=
    List.getElem_of_append (show selectorAxes ++ [axis] = selectorAxes ++ axis::[] from rfl) length
  have actual := RuntimeScatterTransport.scatter_write physical (gather physical (selectorAxes ++ [axis]))
    (selectorAxes ++ [axis]) unique width inside input small
  rw [RuntimeScatterTransport.scatter_gather physical _ unique,target,coordinate,
    write_packed_target width label row input labelBound rowBound] at actual
  simpa only [Qleisli.RuntimeTargetScatter.scatter_one physical axis input small] using actual.symm

/-- A physical input of the same selected sector replaces only the original
Bit target digit in the complete caller code. The selector may be padded or
zero width and all spectator amplitudes remain arbitrary. -/
theorem target_scatter_references {Reference : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode selectorBits retained restricted labels}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits 1 labels)
    (targetBasis : target.basis = [.bit])
    (literal : RuntimeLocalEvents.Literal frame selectorBits 1 retained restricted
      codes.owners.before codes.owners.transport.after)
    (joint : Nat → Reference → ℂ) (physical label row input : Nat) (ref : Reference)
    (coordinate : gather physical (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList) =
      pack selectorBits label row)
    (labelBound : label < 2^selectorBits) (rowBound : row < 2) (small : input < 2) :
    referenceAction literal.outputCode joint
        (scatter physical (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList)
          (pack selectorBits label input)) ref =
      referenceAction literal.outputCode
        (fun logical reference => joint (RuntimeTargetDigit.update literal.outputCode
          codes.owners.returned.second logical input) reference) physical ref := by
  obtain ⟨axis,axisRead,length,axes,unique⟩ := returned_axes frame codes layouts targetBasis literal
  have actual : scatter physical (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList)
      (pack selectorBits label input) =
      scatter physical (codes.owners.returned.second.port.wires.map frame.interval.after.quantum.frame.idxOf) input := by
    rw [axes,axisRead]
    exact last_axis_set physical _ axis selectorBits label row input length (by rwa [← axes])
      (by rwa [← axes]) labelBound rowBound small
  rw [actual]
  exact Qleisli.RuntimeTargetScatter.bit_target_set_references frame codes targetBasis literal joint physical input ref small

/-- The actual sparse output encoding on a finite original logical family. -/
noncomputable def finiteReferenceAction {roles state checked} (code : @Frame roles state checked)
    {Reference : Type} (joint : Fin code.code.dimension → Reference → ℂ) (physical : Nat) (ref : Reference) : ℂ :=
  ((List.finRange code.code.dimension).map fun index => scalar (code.embedding physical index.val)*joint index ref).sum

private theorem finRange_values (size : Nat) :
    (List.finRange size).map (fun index : Fin size => index.val) = List.range size := by
  apply List.ext_getElem (by simp only [List.length_map,List.length_finRange,List.length_range])
  intro index _inside _bounded
  simp only [List.getElem_map,List.getElem_finRange,List.getElem_range]
  rfl

theorem finiteReferenceAction_of_nat {roles state checked} (code : @Frame roles state checked)
    {Reference : Type} (joint : Nat → Reference → ℂ) (physical : Nat) (ref : Reference) :
    finiteReferenceAction code (fun index => joint index.val) physical ref = referenceAction code joint physical ref := by
  unfold finiteReferenceAction referenceAction
  have same := congrArg (fun indices : List Nat =>
    (indices.map fun index => scalar (code.embedding physical index)*joint index ref).sum) (finRange_values code.code.dimension)
  simpa only [List.map_map,Function.comp_def] using same

/-- The actual multiway sector receipt acts on the logical target inside
the complete returned forest. All original selected/spectator axes and the
same two successful native code products remain bound to this interval. -/
theorem sector_action {Reference : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits : Nat} {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits 1]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained} {labels : List Nat}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits 1 labels)
    (targetBasis : target.basis = [.bit])
    (literal : RuntimeLocalEvents.Literal frame selectorBits 1 retained restricted
      codes.owners.before codes.owners.transport.after)
    (form : Qleisli.RuntimeOwnerTransitionAction.SelectionForm frame codes.owners)
    {label required logical}
    (binding : QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode retained.sectors (label,required) logical)
    (joint : Nat → Reference → ℂ) (physical row : Nat) (ref : Reference)
    (coordinate : gather physical (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList) =
      pack selectorBits label row) (rowBound : row < 2) :
    Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
        (fun input => referenceAction literal.inputCode joint input ref) physical =
      referenceAction literal.outputCode (fun index reference => action required
        (fun col => joint (RuntimeTargetDigit.update literal.outputCode codes.owners.returned.second index col)) row reference)
        physical ref := by
  rw [Qleisli.RuntimeOwnerTransitionAction.bit_target_selection_output frame codes targetBasis literal
    form binding joint physical row ref coordinate rowBound]
  let family := fun col index => joint (RuntimeTargetDigit.update literal.outputCode codes.owners.returned.second index col)
  have bounds := Qleisli.RuntimeBitSectorAction.binding_bounds frame codes targetBasis literal binding
  refine Eq.trans ?_ (Qleisli.RuntimeSelectionAction.reference_sum literal.outputCode required family physical row ref)
  unfold action
  apply Qleisli.Exact.sum_map_congr
  intro col member
  have small := List.mem_range.mp member
  rw [bounds.2] at small
  exact congrArg (fun value : ℂ => entry required row col*value)
    (target_scatter_references frame codes layouts targetBasis literal joint physical label row col ref
      coordinate bounds.1 rowBound small)

/-- On every physical row with an original selector code label, the actual
Raw selection intertwines the input encoding with the full original-ordinal
logical action. Padding-selector rows are handled separately, never assigned
a default identity arm. Spectator amplitudes and references are arbitrary. -/
theorem supported_caller_action {Reference : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits : Nat} {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits 1]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {labels : List Nat} {arms : List Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits 1 labels)
    (targetBasis : target.basis = [.bit])
    (literal : RuntimeLocalEvents.Literal frame selectorBits 1 retained restricted
      codes.owners.before codes.owners.transport.after)
    (form : Qleisli.RuntimeOwnerTransitionAction.SelectionForm frame codes.owners)
    (table : OrdinalTable inputCode outputCode retained.sectors labels arms)
    (joint : Nat → Reference → ℂ) (physical : Nat) (ref : Reference) (ordinal : Fin labels.length)
    (coordinate : gather physical
      (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) = labels[ordinal.val]) :
    Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
        (fun input => referenceAction literal.inputCode joint input ref) physical =
      finiteReferenceAction literal.outputCode (sourceAction frame codes layouts literal table joint) physical ref := by
  obtain ⟨axis,axisRead,length,axes,_unique⟩ := returned_axes frame codes layouts targetBasis literal
  let row := gather physical (codes.owners.returned.second.port.wires.map frame.interval.after.quantum.frame.idxOf)
  have rowBound : row < 2 := by
    change gather physical (codes.owners.returned.second.port.wires.map frame.interval.after.quantum.frame.idxOf) < 2
    rw [axisRead]
    simpa only [List.length_cons,List.length_nil] using gather_bound physical [axis]
  have packed : gather physical (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList) =
      pack selectorBits labels[ordinal.val] row := by
    rw [axes,gather_append,length]
    change _ = labels[ordinal.val]+2^selectorBits*row
    rw [coordinate]
    change _ = labels[ordinal.val]+2^selectorBits*gather physical
      (codes.owners.returned.second.port.wires.map frame.interval.after.quantum.frame.idxOf)
    rw [axisRead]
  rw [sector_action frame codes layouts targetBasis literal form (table.arm_checked ordinal)
    joint physical row ref packed rowBound]
  rw [← finiteReferenceAction_of_nat]
  unfold finiteReferenceAction
  apply Qleisli.Exact.sum_map_congr
  intro index _member
  by_cases empty : scalar (literal.outputCode.embedding physical index.val) = 0
  · simp only [empty,zero_mul]
  · have same := supported_ordinal frame codes layouts literal physical index ordinal coordinate empty
    have selected := RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered
    have member : codes.owners.returned.second ∈ codes.owners.transport.after.bindings := selected.1 (by simp)
    have owners : codes.owners.returned.first.owner = selector ∧ codes.owners.returned.second.owner = target := by
      simpa only [List.map_cons,List.map_nil,List.cons.injEq,and_true] using selected.2
    have targetDigit := Qleisli.RuntimeTargetScatter.bit_digit_support literal.outputCode codes.owners.returned.second
      member (by rw [owners.2,targetBasis]) physical index.val index.isLt empty
    change scalar (literal.outputCode.embedding physical index.val) *
      action (table.arm ordinal) (fun col => joint (RuntimeTargetDigit.update literal.outputCode
        codes.owners.returned.second index.val col)) row ref =
      scalar (literal.outputCode.embedding physical index.val) *
      action (table.arm (originalOrdinal frame codes layouts literal index))
        (fun col => joint (RuntimeTargetDigit.update literal.outputCode codes.owners.returned.second index.val col))
        (decode codes.owners.transport.after.bindings (dimensionAt literal.outputCode.owners) index.val codes.owners.returned.second) ref
    rw [same,targetDigit]

/-- Selector padding has zero support in the same complete output code. -/
theorem selector_padding_entry
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode selectorBits targetBits retained restricted labels}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (physical logical : Nat) (bound : logical < literal.outputCode.code.dimension)
    (padding : gather physical (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) ∉ labels) :
    scalar (literal.outputCode.embedding physical logical) = 0 := by
  obtain ⟨actual,_found,layout⟩ := returned_selector_layout frame codes layouts literal
  have selected := RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered
  have member : codes.owners.returned.first ∈ codes.owners.transport.after.bindings := selected.1 (by simp)
  exact Qleisli.RuntimeNominalSupport.owner_padding_zero literal.outputCode codes.owners.returned.first member actual
    physical logical bound (by simpa only [layout] using padding)

theorem selector_padding_reference {Reference : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode selectorBits targetBits retained restricted labels}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (joint : Nat → Reference → ℂ) (physical : Nat) (ref : Reference)
    (padding : gather physical (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) ∉ labels) :
    referenceAction literal.outputCode joint physical ref = 0 := by
  unfold referenceAction
  calc
    _ = ((List.range literal.outputCode.code.dimension).map fun _ => (0 : ℂ)).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro logical member
      rw [selector_padding_entry frame codes layouts literal physical logical (List.mem_range.mp member) padding,zero_mul]
    _ = 0 := by simp

theorem finite_selector_padding_reference {Reference : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode selectorBits targetBits retained restricted labels}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (joint : Fin literal.outputCode.code.dimension → Reference → ℂ) (physical : Nat) (ref : Reference)
    (padding : gather physical (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) ∉ labels) :
    finiteReferenceAction literal.outputCode joint physical ref = 0 := by
  unfold finiteReferenceAction
  calc
    _ = ((List.finRange literal.outputCode.code.dimension).map fun _ => (0 : ℂ)).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro index _member
      rw [selector_padding_entry frame codes layouts literal physical index.val index.isLt padding,zero_mul]
    _ = 0 := by simp

private theorem sector_bit_shape {dependencies selector operations label actual}
    (binding : QleisliKernel.FiniteRestriction.SectorEvaluationBinding dependencies selector [.bits 1] operations label actual) :
    actual.rows = 2 ∧ actual.cols = 2 := by
  obtain ⟨_label,restricted,before,after,_unitary,_restriction,native,_gram,_lifting⟩ := binding
  obtain ⟨_valid,columns,_read,made⟩ := QleisliKernel.Finite.circuitMatrix_columns dependencies
    ⟨[.bits 1],restricted⟩ actual before after native
  constructor
  · simpa only [width,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using congrArg Matrix.rows made
  · simpa only [width,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using congrArg Matrix.cols made

/-- The existing all-physical-label restriction also retains padding sectors.
Its actual matrix acts on a zero encoded slice, so padding outputs stay zero
without selecting, inventing or checking an extra logical arm. -/
theorem padding_caller_action {Reference : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits : Nat} {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits 1]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained} {labels : List Nat}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits 1 labels)
    (targetBasis : target.basis = [.bit])
    (literal : RuntimeLocalEvents.Literal frame selectorBits 1 retained restricted
      codes.owners.before codes.owners.transport.after)
    (form : Qleisli.RuntimeOwnerTransitionAction.SelectionForm frame codes.owners)
    (joint : Nat → Reference → ℂ) (physical : Nat) (ref : Reference)
    (padding : gather physical (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) ∉ labels) :
    Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
      (fun input => referenceAction literal.inputCode joint input ref) physical = 0 := by
  obtain ⟨axis,axisRead,length,axes,_unique⟩ := returned_axes frame codes layouts targetBasis literal
  let selected := forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList
  let low := gather physical (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf)
  let row := gather physical (codes.owners.returned.second.port.wires.map frame.interval.after.quantum.frame.idxOf)
  have lowBound : low < 2^selectorBits := by
    simpa only [length] using gather_bound physical
      (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf)
  have rowBound : row < 2 := by
    change gather physical (codes.owners.returned.second.port.wires.map frame.interval.after.quantum.frame.idxOf) < 2
    rw [axisRead]
    simpa only [List.length_cons,List.length_nil] using gather_bound physical [axis]
  have packed : gather physical selected = pack selectorBits low row := by
    change gather physical (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList) = _
    rw [axes,gather_append,length]
    change _ = low+2^selectorBits*gather physical
      (codes.owners.returned.second.port.wires.map frame.interval.after.quantum.frame.idxOf)
    rw [axisRead]
  let pulled := fun input => referenceAction literal.outputCode joint (scatter physical selected input) ref
  have code := Qleisli.RuntimeOwnerTransitionAction.selection_form_codes frame codes.owners literal form
  have sameCode (input : Nat) : referenceAction literal.inputCode joint input ref =
      referenceAction literal.outputCode joint input ref := by
    unfold referenceAction
    rw [code.1]
    apply Qleisli.Exact.sum_map_congr
    intro index _member
    rw [code.2 input index]
  have sameAxes := Qleisli.RuntimeOwnerTransitionAction.selection_form_axes frame codes.owners literal form
  have localized : Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
        (fun input => referenceAction literal.inputCode joint input ref) physical =
      Qleisli.Semantics.RawAction.circuit dependencies retained.steps pulled (pack selectorBits low row) := by
    have actual := congrFun (congrFun (Qleisli.Semantics.RawAction.Locality.literal_references literal
      (fun reference input => referenceAction literal.inputCode joint input reference)) ref) physical
    rw [sameAxes] at actual
    change _ = Qleisli.Semantics.RawAction.circuit dependencies retained.steps
      (fun input => referenceAction literal.inputCode joint (scatter physical selected input) ref)
      (gather physical selected) at actual
    rw [packed] at actual
    refine actual.trans ?_
    apply congrArg (fun values : Nat → ℂ => Qleisli.Semantics.RawAction.circuit dependencies retained.steps values (pack selectorBits low row))
    funext input
    exact sameCode _
  have zeroFamily (input : Nat) (small : input < 2) : pulled (pack selectorBits low input) = 0 := by
    change referenceAction literal.outputCode joint (scatter physical
      (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList) (pack selectorBits low input)) ref = 0
    rw [target_scatter_references frame codes layouts targetBasis literal joint physical low row input ref
      packed lowBound rowBound small]
    exact selector_padding_reference frame codes layouts literal _ physical ref padding
  have relation := literal.sectorReference.2.2.2.2.2.2.2
  have lengthSectors := QleisliKernel.Exact.listRel_length _ _ _ relation
  have inside : low < retained.sectors.length := by
    rw [lengthSectors,List.length_range]
    simpa only [width,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using lowBound
  let actual := retained.sectors[low]'inside
  have found : retained.sectors[low]? = some actual := List.getElem?_eq_getElem inside
  have binding : QleisliKernel.FiniteRestriction.SectorEvaluationBinding dependencies selectorBits [.bits 1] retained.steps low actual :=
    Qleisli.NominalSector.indexed_sector relation found
  have shape := sector_bit_shape binding
  have actualAction := Qleisli.Semantics.RawAction.Sector.sector_binding_action dependencies selectorBits [.bits 1]
    retained.steps low actual binding (fun input (_ : Unit) => pulled input) row () (by rw [shape.1]; exact rowBound)
  calc
    _ = _ := localized
    _ = action actual (fun input (_ : Unit) => pulled (pack selectorBits low input)) row () := actualAction
    _ = ((List.range actual.cols).map fun _ => (0 : ℂ)).sum := by
      unfold action
      apply Qleisli.Exact.sum_map_congr
      intro input member
      have small := List.mem_range.mp member
      rw [shape.2] at small
      change entry actual row input * pulled (pack selectorBits low input) = 0
      rw [zeroFamily input small,mul_zero]
    _ = 0 := by simp

/-- Complete phase-sensitive physical intertwining on every output row.
Supported rows select their native receipt by original ordinal; padding rows
are zero by the actual retained restriction, with no missing-arm fallback. -/
theorem caller_action {Reference : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits : Nat} {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits 1]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {labels : List Nat} {arms : List Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits 1 labels)
    (targetBasis : target.basis = [.bit])
    (literal : RuntimeLocalEvents.Literal frame selectorBits 1 retained restricted
      codes.owners.before codes.owners.transport.after)
    (form : Qleisli.RuntimeOwnerTransitionAction.SelectionForm frame codes.owners)
    (table : OrdinalTable inputCode outputCode retained.sectors labels arms)
    (joint : Nat → Reference → ℂ) (physical : Nat) (ref : Reference) :
    Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
        (fun input => referenceAction literal.inputCode joint input ref) physical =
      finiteReferenceAction literal.outputCode (sourceAction frame codes layouts literal table joint) physical ref := by
  by_cases supported : gather physical
      (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) ∈ labels
  · obtain ⟨ordinal,inside,same⟩ := List.mem_iff_getElem.mp supported
    exact supported_caller_action frame codes layouts targetBasis literal form table joint physical ref ⟨ordinal,inside⟩ same.symm
  · exact (padding_caller_action frame codes layouts targetBasis literal form joint physical ref supported).trans
      (finite_selector_padding_reference frame codes layouts literal _ physical ref supported).symm

/-- Consume the actual native table/layout/code receipts once, retaining both
the all-output physical intertwiner and the verified full logical Gram law. -/
theorem checked_selection {R S : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits : Nat} {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits 1]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {labels : List Nat} {expected logical : List Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits 1 labels)
    (equations : RuntimeInterval.Computed (QleisliKernel.Qirf.NominalSector.checkLogicals
      inputCode outputCode retained.sectors labels expected) logical)
    (targetBasis : target.basis = [.bit])
    (literal : RuntimeLocalEvents.Literal frame selectorBits 1 retained restricted
      codes.owners.before codes.owners.transport.after)
    (form : Qleisli.RuntimeOwnerTransitionAction.SelectionForm frame codes.owners)
    (joint : Nat → R → ℂ) (other : Nat → S → ℂ) (r : R) (s : S) :
    logical = expected ∧ ∃ table : OrdinalTable inputCode outputCode retained.sectors labels expected,
      (∀ physical, Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
        (fun input => referenceAction literal.inputCode joint input r) physical =
        finiteReferenceAction literal.outputCode (sourceAction frame codes layouts literal table joint) physical r) ∧
      ((List.finRange literal.outputCode.code.dimension).map fun index =>
        star (sourceAction frame codes layouts literal table joint index r) *
          sourceAction frame codes layouts literal table other index s).sum =
      ((List.finRange literal.outputCode.code.dimension).map fun index => star (joint index.val r)*other index.val s).sum := by
  obtain ⟨same,table,gram⟩ := Qleisli.RuntimeMultiwayGram.checked_selection frame codes layouts equations
    targetBasis literal joint other r s
  exact ⟨same,table,fun physical => caller_action frame codes layouts targetBasis literal form table joint physical r,gram⟩

#print axioms selector_support
#print axioms supported_ordinal
#print axioms selected_receipt
#print axioms returned_axes
#print axioms target_scatter_references
#print axioms sector_action
#print axioms supported_caller_action
#print axioms padding_caller_action
#print axioms caller_action
#print axioms checked_selection

end Qleisli.RuntimeMultiwayAction
