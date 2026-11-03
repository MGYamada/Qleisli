import Qleisli.RuntimeFiniteTargetScatter

/-! A genuine finite-target source sector acting through its rectangular code.
The actual local tape, original selected/returned owner pair, complete caller
codes and native indexed equation are retained. Logical target fibres may be
entangled with all spectators and references. Physical target padding is not
assigned a logical digit or identity arm. This module changes no native gate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeFiniteSectorAction
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open QleisliKernel.FiniteRestriction (pack)
open RuntimeOwnerMap (Binding)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct
open Qleisli.RuntimeForestRegroup Qleisli.RuntimeFiniteTargetFibre
open Qleisli.RuntimeFiniteTargetScatter

private theorem bit_ext (left right : Nat) (same : ∀ axis,bit left axis = bit right axis) : left = right := by
  apply Nat.eq_of_testBit_eq
  intro axis
  have equal := same axis
  simp only [bit] at equal
  rw [← Nat.toNat_testBit left axis,← Nat.toNat_testBit right axis] at equal
  cases leftBit : left.testBit axis <;> cases rightBit : right.testBit axis <;> simp_all

/-- Ordered low/high scatter is the same literal two-stage overwrite. Both
axis lists may be empty, reversed or noncontiguous in the caller frame. -/
theorem scatter_pair (physical low high : Nat) (first second : List Nat)
    (unique : (first ++ second).Nodup) (bound : low < 2^first.length) :
    scatter physical (first ++ second) (pack first.length low high) =
      scatter (scatter physical first low) second high := by
  have parts := List.nodup_append.mp unique
  apply bit_ext
  intro axis
  by_cases before : axis ∈ first
  · obtain ⟨index,inside,same⟩ := List.getElem_of_mem before
    subst axis
    have allBound : index < (first ++ second).length := by simp only [List.length_append]; omega
    have allAxis : (first ++ second)[index]'allBound = first[index]'inside := List.getElem_append_left inside
    have outside : first[index]'inside ∉ second := by
      intro present
      exact parts.2.2 _ (List.getElem_mem inside) _ present rfl
    calc
      _ = bit (pack first.length low high) index := by
        simpa only [allAxis] using RuntimeScatterTransport.scatter_at physical
          (pack first.length low high) (first ++ second) unique index allBound
      _ = bit low index := QleisliKernel.FiniteRestriction.bit_selector first.length low high index inside
      _ = _ := by
        rw [RuntimeScatterTransport.scatter_outside _ _ _ second outside]
        exact (RuntimeScatterTransport.scatter_at physical low first parts.1 index inside).symm
  · by_cases after : axis ∈ second
    · obtain ⟨index,inside,same⟩ := List.getElem_of_mem after
      subst axis
      have allBound : first.length+index < (first ++ second).length := by
        simp only [List.length_append]
        omega
      have allAxis : (first ++ second)[first.length+index]'allBound = second[index]'inside := by
        simpa only [Nat.add_sub_cancel_left] using
          (List.getElem_append_right (as:=first) (bs:=second) (i:=first.length+index) (by omega) (h₂:=allBound))
      calc
        _ = bit (pack first.length low high) (first.length+index) := by
          simpa only [allAxis] using RuntimeScatterTransport.scatter_at physical
            (pack first.length low high) (first ++ second) unique (first.length+index) allBound
        _ = bit high index := QleisliKernel.FiniteRestriction.bit_target first.length low high index bound
        _ = _ := (RuntimeScatterTransport.scatter_at (scatter physical first low) high second
          parts.2.1 index inside).symm
    · have outside : axis ∉ first ++ second := by simpa only [List.mem_append,not_or] using And.intro before after
      rw [RuntimeScatterTransport.scatter_outside _ _ _ _ outside,
        RuntimeScatterTransport.scatter_outside _ _ _ _ after,
        RuntimeScatterTransport.scatter_outside _ _ _ _ before]

/-- The same original target layout and both native code reads. -/
theorem returned_target_layout
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode selectorBits targetBits retained restricted labels}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after) :
    ∃ actual : OwnerCode codes.owners.returned.second,
      lookup literal.outputCode.owners codes.owners.returned.second = some actual ∧
      actual.layout.bits = targetBits ∧
      inputCode = Semantics.FiniteCarrier.encoding actual.layout ∧
      outputCode = Semantics.FiniteCarrier.encoding actual.layout := by
  have selected := RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered
  have member : codes.owners.returned.second ∈ codes.owners.transport.after.bindings := selected.1 (by simp)
  have owners : codes.owners.returned.first.owner = selector ∧ codes.owners.returned.second.owner = target := by
    simpa only [List.map_cons,List.map_nil,List.cons.injEq,and_true] using selected.2
  obtain ⟨actual,found⟩ := lookup_exists literal.outputCode.owners codes.owners.returned.second member
  obtain ⟨layout,original,bits,inputSame,outputSame,_inputGram,_outputGram⟩ :=
    Qleisli.RuntimeFiniteTargetCode.target_codes frame codes layouts
  have targetRead := actual.reference.1
  rw [owners.2] at targetRead
  have same : actual.layout = layout := Option.some.inj (targetRead.symm.trans original)
  exact ⟨actual,found,(congrArg Semantics.FiniteCarrier.Layout.bits same).trans bits,
    by rw [same]; exact inputSame,by rw [same]; exact outputSame⟩

/-- Native source layouts bind both real returned axis lengths, and the same
Raw owner partition supplies the distinct ordered pair axes. -/
theorem returned_axes
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode selectorBits targetBits retained restricted labels}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after) :
    let first := codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf
    let second := codes.owners.returned.second.port.wires.map frame.interval.after.quantum.frame.idxOf
    first.length = selectorBits ∧ second.length = targetBits ∧
      forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList = first ++ second ∧
      (first ++ second).Nodup := by
  obtain ⟨first,_firstRead,firstLayout⟩ := Qleisli.RuntimeMultiwayGram.returned_selector_layout frame codes layouts literal
  obtain ⟨second,_secondRead,secondBits,_inputSame,_outputSame⟩ := returned_target_layout frame codes layouts literal
  have firstLength := first.reference.2.2
  rw [firstLayout] at firstLength
  have secondLength := second.reference.2.2
  rw [secondBits] at secondLength
  have axes : forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList =
      codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf ++
        codes.owners.returned.second.port.wires.map frame.interval.after.quantum.frame.idxOf := by
    simp only [forestAxes,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_append]
  have permutation := RuntimeSelectionPartition.source_output_partition frame codes.owners
  have mapped := (permutation.flatMap_right (fun binding : Binding => binding.port.wires)).map
    frame.interval.after.quantum.frame.idxOf
  have allUnique := mapped.symm.nodup (Qleisli.RuntimeTargetScatter.output_axes_unique frame codes.owners)
  have appended : (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList ++
      forestAxes frame.interval.after.quantum.frame (RuntimeSelectionPartition.complement
        codes.owners.transport.after.bindings codes.owners.returned.toList)).Nodup := by
    simpa only [forestAxes,List.flatMap_append,List.map_append] using allUnique
  refine ⟨by simpa only [List.length_map] using firstLength,
    by simpa only [List.length_map] using secondLength,axes,?_⟩
  rw [← axes]
  exact (List.nodup_append.mp appended).1

/-- Slice the same whole caller at a physical selector label. Every physical
target row is reconstructed by the true finite target encoding. -/
theorem pair_slice_code_action {Reference : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode selectorBits targetBits retained restricted labels}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (joint : Nat → Reference → ℂ) (physical label row : Nat) (reference : Reference)
    (labelBound : label < 2^selectorBits) (rowBound : row < 2^targetBits) :
    referenceAction literal.outputCode joint
        (scatter physical (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList)
          (pack selectorBits label row)) reference =
      action inputCode
        (targetFibre literal.outputCode codes.owners.returned.second
          (scatter physical (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) label) joint)
        row reference := by
  obtain ⟨firstLength,_secondLength,axes,unique⟩ := returned_axes frame codes layouts literal
  obtain ⟨actual,_found,bits,inputSame,_outputSame⟩ := returned_target_layout frame codes layouts literal
  have selected := RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered
  have member : codes.owners.returned.second ∈ codes.owners.transport.after.bindings := selected.1 (by simp)
  have lowBound : label < 2^(codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf).length := by
    rwa [firstLength]
  have pairSplit : scatter physical
      (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList) (pack selectorBits label row) =
        scatter (scatter physical
          (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) label)
          (codes.owners.returned.second.port.wires.map frame.interval.after.quantum.frame.idxOf) row := by
    rw [axes]
    simpa only [firstLength] using scatter_pair physical label row _ _ unique lowBound
  rw [pairSplit]
  have sliced := target_slice_code_action frame codes.owners literal.outputCode codes.owners.returned.second member actual
    joint (scatter physical (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) label)
      row reference (by simpa only [bits] using rowBound)
  exact sliced.trans (congrArg (fun matrix => action matrix
    (targetFibre literal.outputCode codes.owners.returned.second
      (scatter physical (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) label) joint)
    row reference) inputSame.symm)

/-- An actual original source step acts through the finite target code on its
complete caller fibre. The same retained local tape and indexed native sector
products supply the action; padding is preserved by the rectangular code on
both sides. This does not equate bounded arithmetic runs or allocate a joined
caller matrix. -/
theorem sector_code_action {Reference : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained} {labels : List Nat}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (form : Qleisli.RuntimeOwnerTransitionAction.SelectionForm frame codes.owners)
    {label required logical}
    (binding : QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode retained.sectors (label,required) logical)
    (joint : Nat → Reference → ℂ) (physical row : Nat) (reference : Reference)
    (coordinate : gather physical
      (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList) = pack selectorBits label row)
    (rowBound : row < 2^targetBits) :
    Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
        (fun input => referenceAction literal.inputCode joint input reference) physical =
      action outputCode (fun output ref => action required
        (targetFibre literal.outputCode codes.owners.returned.second
          (scatter physical (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) label) joint)
        output ref) row reference := by
  let axes := forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList
  let family : Nat → Nat → Reference → ℂ := fun selected =>
    targetFibre literal.outputCode codes.owners.returned.second
      (scatter physical (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) selected) joint
  let pulled := fun input => referenceAction literal.outputCode joint (scatter physical axes input) reference
  have code := Qleisli.RuntimeOwnerTransitionAction.selection_form_codes frame codes.owners literal form
  have referenceCode : ∀ input ref,referenceAction literal.inputCode joint input ref =
      referenceAction literal.outputCode joint input ref := by
    intro input ref
    unfold referenceAction
    rw [code.1]
    apply Qleisli.Exact.sum_map_congr
    intro logical _present
    rw [code.2 input logical]
  have sourceAxes := Qleisli.RuntimeOwnerTransitionAction.selection_form_axes frame codes.owners literal form
  have read := literal.sectorReference
  obtain ⟨sector,found,_map,_same⟩ := Qleisli.NominalSector.logical_binding_map binding
  have inside := (List.getElem?_eq_some_iff.mp found).1
  have lengths := QleisliKernel.Exact.listRel_length _ _ _ read.2.2.2.2.2.2.2
  rw [lengths,List.length_range] at inside
  have labelBound : label < 2^selectorBits := by
    simpa only [width,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using inside
  obtain ⟨before,after,sectorsRead⟩ := read.2.2.2.2.2.2.1
  have valid := (QleisliKernel.FiniteRestriction.readSectors_bound _ _ _ _ _ before after sectorsRead).2.2.1
  have valid : retained.steps.all (QleisliKernel.Finite.stepValid dependencies (selectorBits+targetBits)) = true := by
    simpa only [width,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using valid
  have encoded (input : Nat) (bound : input < 2^(selectorBits+targetBits)) :
      pulled input = Qleisli.NominalSector.encodedTargets selectorBits inputCode family input reference := by
    have lowBound : input % 2^selectorBits < 2^selectorBits := Nat.mod_lt _ (Nat.two_pow_pos _)
    have highBound : input / 2^selectorBits < 2^targetBits :=
      Nat.div_lt_of_lt_mul (by simpa only [Nat.pow_add] using bound)
    have sliced := pair_slice_code_action frame codes layouts literal joint physical
      (input % 2^selectorBits) (input / 2^selectorBits) reference lowBound highBound
    have packed : pack selectorBits (input % 2^selectorBits) (input / 2^selectorBits) = input :=
      Nat.mod_add_div input (2^selectorBits)
    change referenceAction literal.outputCode joint (scatter physical axes input) reference =
      action inputCode (family (input % 2^selectorBits)) (input / 2^selectorBits) reference
    simpa only [packed] using sliced
  have packedBound : pack selectorBits label row < 2^(selectorBits+targetBits) := by
    rw [Nat.pow_add]
    change label+2^selectorBits*row < 2^selectorBits*2^targetBits
    calc
      label+2^selectorBits*row < 2^selectorBits+2^selectorBits*row := Nat.add_lt_add_right labelBound _
      _ = 2^selectorBits*(row+1) := by ring
      _ ≤ 2^selectorBits*2^targetBits := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt rowBound)
  have localized := congrFun (congrFun (Qleisli.Semantics.RawAction.Locality.literal_references literal
    (fun ref input => referenceAction literal.inputCode joint input ref)) reference) physical
  calc
    _ = Qleisli.Semantics.RawAction.circuit dependencies retained.steps
        (fun input => referenceAction literal.inputCode joint (scatter physical axes input) reference)
        (gather physical axes) := by simpa only [sourceAxes] using localized
    _ = Qleisli.Semantics.RawAction.circuit dependencies retained.steps pulled (gather physical axes) := by
      apply congrArg (fun values : Nat → ℂ => Qleisli.Semantics.RawAction.circuit dependencies retained.steps
        values (gather physical axes))
      funext input
      exact referenceCode _ _
    _ = Qleisli.Semantics.RawAction.circuit dependencies retained.steps pulled (pack selectorBits label row) := by
      rw [coordinate]
    _ = Qleisli.Semantics.RawAction.circuit dependencies retained.steps
        (fun input => Qleisli.NominalSector.encodedTargets selectorBits inputCode family input reference)
        (pack selectorBits label row) :=
      Qleisli.Finite.rawCircuit_congr dependencies (selectorBits+targetBits) retained.steps _ _
        valid encoded _ packedBound
    _ = _ := Qleisli.RuntimeFiniteTargetCode.local_code_action frame codes layouts literal binding
      family row reference rowBound

#print axioms returned_axes
#print axioms pair_slice_code_action
#print axioms sector_code_action

end Qleisli.RuntimeFiniteSectorAction
