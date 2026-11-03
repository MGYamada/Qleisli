import Qleisli.RuntimeFiniteTargetLogical

/-! Original source-sector action for arbitrary actual finite targets.
The local tape and its native rectangular code equation are connected to the
same complete caller code and original mixed-radix target update. Nominal
selector labels select receipts while original ordinals select logical arms.
No dense caller matrix, surrogate arm, bounded-availability converse or native
acceptance rule is introduced by these total-complex reference theorems.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeFiniteTargetAction
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open QleisliKernel.FiniteRestriction (pack)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct
open Qleisli.RuntimeForestRegroup Qleisli.RuntimeFiniteTargetFibre
open Qleisli.RuntimeFiniteTargetLogical Qleisli.RuntimeMultiwayGram

/-- The native sector at an authentic selector code label acts at the same
original logical target in the complete output forest. The target may have
physical padding or zero width, and all references remain arbitrary. -/
theorem sector_caller_action {Reference : Type}
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
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference)
    (selectorCoordinate : gather physical
      (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) = label) :
    Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
        (fun input => referenceAction literal.inputCode joint input reference) physical =
      referenceAction literal.outputCode
        (targetAction literal.outputCode codes.owners.returned.second required joint) physical reference := by
  obtain ⟨firstLength,secondLength,axes,unique⟩ :=
    Qleisli.RuntimeFiniteSectorAction.returned_axes frame codes layouts literal
  obtain ⟨actual,_found,_bits,inputSame,outputSame⟩ :=
    Qleisli.RuntimeFiniteSectorAction.returned_target_layout frame codes layouts literal
  let row := gather physical (codes.owners.returned.second.port.wires.map frame.interval.after.quantum.frame.idxOf)
  have rowBound : row < 2^targetBits := by
    simpa only [secondLength] using gather_bound physical
      (codes.owners.returned.second.port.wires.map frame.interval.after.quantum.frame.idxOf)
  have coordinate : gather physical
      (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList) = pack selectorBits label row := by
    rw [axes,gather_append,firstLength,selectorCoordinate]
    rfl
  have unchanged : scatter physical
      (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) label = physical := by
    rw [← selectorCoordinate]
    exact RuntimeScatterTransport.scatter_gather physical _ (List.nodup_append.mp unique).1
  have selected := RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered
  have member : codes.owners.returned.second ∈ codes.owners.transport.after.bindings := selected.1 (by simp)
  have inputColumns : inputCode.cols = actual.layout.labels.length := congrArg Matrix.cols inputSame
  have columns : required.cols = dimensionAt literal.outputCode.owners codes.owners.returned.second :=
    ((congrArg Matrix.cols binding.1.symm).trans binding.2.1).trans
      (inputColumns.trans (dimensionAt_eq literal.outputCode.owners codes.owners.returned.second member actual).symm)
  have native := Qleisli.RuntimeFiniteSectorAction.sector_code_action frame codes layouts literal form binding
    joint physical row reference coordinate rowBound
  have native : Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
      (fun input => referenceAction literal.inputCode joint input reference) physical =
        action outputCode (fun output ref => action required
          (targetFibre literal.outputCode codes.owners.returned.second physical joint) output ref) row reference := by
    simpa only [unchanged] using native
  exact native.trans ((congrArg (fun matrix => action matrix
    (fun output ref => action required (targetFibre literal.outputCode codes.owners.returned.second physical joint)
      output ref) row reference) outputSame).trans
        (target_action_code literal.outputCode codes.owners.returned.second member actual required columns joint
          physical reference).symm)

/-- A supported physical selector row uses the native receipt selected by its
original ordinal. Nonzero whole-code support proves that same ordinal for
every contributing caller coefficient, including target-padding cases. -/
theorem supported_caller_action {Reference : Type}
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
    (form : Qleisli.RuntimeOwnerTransitionAction.SelectionForm frame codes.owners)
    (table : OrdinalTable inputCode outputCode retained.sectors labels arms)
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) (ordinal : Fin labels.length)
    (selectorCoordinate : gather physical
      (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) = labels[ordinal.val]) :
    Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
        (fun input => referenceAction literal.inputCode joint input reference) physical =
      Qleisli.RuntimeMultiwayAction.finiteReferenceAction literal.outputCode
        (sourceAction frame codes layouts literal table joint) physical reference := by
  rw [sector_caller_action frame codes layouts literal form (table.arm_checked ordinal)
    joint physical reference selectorCoordinate]
  rw [← Qleisli.RuntimeMultiwayAction.finiteReferenceAction_of_nat]
  unfold Qleisli.RuntimeMultiwayAction.finiteReferenceAction
  apply Qleisli.Exact.sum_map_congr
  intro index _present
  by_cases empty : scalar (literal.outputCode.embedding physical index.val) = 0
  · simp only [empty,zero_mul]
  · have same := Qleisli.RuntimeMultiwayAction.supported_ordinal frame codes layouts literal
      physical index ordinal selectorCoordinate empty
    change scalar (literal.outputCode.embedding physical index.val) *
      action (table.arm ordinal) (fun col => joint
        (RuntimeTargetDigit.update literal.outputCode codes.owners.returned.second index.val col))
        (Qleisli.MixedRadix.decode codes.owners.transport.after.bindings (dimensionAt literal.outputCode.owners)
          index.val codes.owners.returned.second) reference =
      scalar (literal.outputCode.embedding physical index.val) *
        action (table.arm (Qleisli.RuntimeMultiwayAction.originalOrdinal frame codes layouts literal index))
          (fun col => joint (RuntimeTargetDigit.update literal.outputCode codes.owners.returned.second index.val col))
          (Qleisli.MixedRadix.decode codes.owners.transport.after.bindings (dimensionAt literal.outputCode.owners)
            index.val codes.owners.returned.second) reference
    rw [same]

private theorem sector_shape {dependencies selector targetBits operations label actual}
    (binding : QleisliKernel.FiniteRestriction.SectorEvaluationBinding
      dependencies selector [.bits targetBits] operations label actual) :
    actual.rows = 2^targetBits ∧ actual.cols = 2^targetBits := by
  obtain ⟨_label,restricted,before,after,_unitary,_restriction,native,_gram,_lifting⟩ := binding
  obtain ⟨_valid,_columns,_read,made⟩ := QleisliKernel.Finite.circuitMatrix_columns dependencies
    ⟨[.bits targetBits],restricted⟩ actual before after native
  constructor
  · simpa only [width,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using congrArg Matrix.rows made
  · simpa only [width,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using congrArg Matrix.cols made

/-- The existing restriction checks every physical selector sector. When its
label is padding, its actual matrix acts on a zero encoded slice. No logical
matrix is invented for the missing ordinal, even for a padded finite target. -/
theorem padding_caller_action {Reference : Type}
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
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference)
    (padding : gather physical
      (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) ∉ labels) :
    Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
      (fun input => referenceAction literal.inputCode joint input reference) physical = 0 := by
  obtain ⟨firstLength,secondLength,axes,unique⟩ :=
    Qleisli.RuntimeFiniteSectorAction.returned_axes frame codes layouts literal
  let first := codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf
  let second := codes.owners.returned.second.port.wires.map frame.interval.after.quantum.frame.idxOf
  let selected := forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList
  let low := gather physical first
  let row := gather physical second
  have firstSize : first.length = selectorBits := firstLength
  have secondSize : second.length = targetBits := secondLength
  have selectedAxes : selected = first ++ second := axes
  have lowBound : low < 2^selectorBits := by simpa only [firstSize] using gather_bound physical first
  have rowBound : row < 2^targetBits := by simpa only [secondSize] using gather_bound physical second
  have lowBoundFirst : low < 2^first.length := gather_bound physical first
  have packed : gather physical selected = pack selectorBits low row := by
    rw [selectedAxes,gather_append,firstSize]
    rfl
  let pulled := fun input => referenceAction literal.outputCode joint (scatter physical selected input) reference
  have code := Qleisli.RuntimeOwnerTransitionAction.selection_form_codes frame codes.owners literal form
  have sameCode (input : Nat) : referenceAction literal.inputCode joint input reference =
      referenceAction literal.outputCode joint input reference := by
    unfold referenceAction
    rw [code.1]
    apply Qleisli.Exact.sum_map_congr
    intro index _present
    rw [code.2 input index]
  have sameAxes := Qleisli.RuntimeOwnerTransitionAction.selection_form_axes frame codes.owners literal form
  have localized : Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
      (fun input => referenceAction literal.inputCode joint input reference) physical =
        Qleisli.Semantics.RawAction.circuit dependencies retained.steps pulled (pack selectorBits low row) := by
    have actual := congrFun (congrFun (Qleisli.Semantics.RawAction.Locality.literal_references literal
      (fun ref input => referenceAction literal.inputCode joint input ref)) reference) physical
    rw [sameAxes] at actual
    change _ = Qleisli.Semantics.RawAction.circuit dependencies retained.steps
      (fun input => referenceAction literal.inputCode joint (scatter physical selected input) reference)
      (gather physical selected) at actual
    rw [packed] at actual
    refine actual.trans ?_
    apply congrArg (fun values : Nat → ℂ => Qleisli.Semantics.RawAction.circuit dependencies retained.steps
      values (pack selectorBits low row))
    funext input
    exact sameCode _
  have parts := List.nodup_append.mp unique
  have disjoint : first.Disjoint second := List.disjoint_left.mpr
    (fun axis before after => parts.2.2 axis before axis after rfl)
  have zeroFamily (input : Nat) : pulled (pack selectorBits low input) = 0 := by
    have split : scatter physical selected (pack selectorBits low input) =
        scatter (scatter physical first low) second input := by
      rw [selectedAxes]
      simpa only [firstSize] using Qleisli.RuntimeFiniteSectorAction.scatter_pair physical low input
        first second unique lowBoundFirst
    have selectorAt : gather (scatter physical selected (pack selectorBits low input)) first = low := by
      rw [split,Qleisli.RuntimeTargetScatter.gather_disjoint _ input second first disjoint,
        Qleisli.RuntimeFiniteTargetScatter.gather_scatter physical low first parts.1 lowBoundFirst]
    exact Qleisli.RuntimeMultiwayAction.selector_padding_reference frame codes layouts literal joint
      (scatter physical selected (pack selectorBits low input)) reference (by rw [selectorAt]; exact padding)
  have relation := literal.sectorReference.2.2.2.2.2.2.2
  have lengthSectors := QleisliKernel.Exact.listRel_length _ _ _ relation
  have inside : low < retained.sectors.length := by
    rw [lengthSectors,List.length_range]
    simpa only [width,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using lowBound
  let actual := retained.sectors[low]'inside
  have found : retained.sectors[low]? = some actual := List.getElem?_eq_getElem inside
  have binding : QleisliKernel.FiniteRestriction.SectorEvaluationBinding dependencies selectorBits
      [.bits targetBits] retained.steps low actual := Qleisli.NominalSector.indexed_sector relation found
  have shape := sector_shape binding
  have actualAction := Qleisli.Semantics.RawAction.Sector.sector_binding_action dependencies selectorBits [.bits targetBits]
    retained.steps low actual binding (fun input (_ : Unit) => pulled input) row () (by rw [shape.1]; exact rowBound)
  calc
    _ = _ := localized
    _ = action actual (fun input (_ : Unit) => pulled (pack selectorBits low input)) row () := actualAction
    _ = ((List.range actual.cols).map fun _ => (0 : ℂ)).sum := by
      unfold action
      apply Qleisli.Exact.sum_map_congr
      intro input _present
      change entry actual row input * pulled (pack selectorBits low input) = 0
      rw [zeroFamily input,mul_zero]
    _ = 0 := by simp

/-- Complete physical intertwining for any actual finite selector and target.
All caller outputs, including both selector and target padding, use the same
native tape/code/table receipts and the original logical arm order. -/
theorem caller_action {Reference : Type}
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
    (form : Qleisli.RuntimeOwnerTransitionAction.SelectionForm frame codes.owners)
    (table : OrdinalTable inputCode outputCode retained.sectors labels arms)
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) :
    Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
        (fun input => referenceAction literal.inputCode joint input reference) physical =
      Qleisli.RuntimeMultiwayAction.finiteReferenceAction literal.outputCode
        (sourceAction frame codes layouts literal table joint) physical reference := by
  by_cases supported : gather physical
      (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) ∈ labels
  · obtain ⟨ordinal,inside,same⟩ := List.mem_iff_getElem.mp supported
    exact supported_caller_action frame codes layouts literal form table joint physical reference ⟨ordinal,inside⟩ same.symm
  · exact (padding_caller_action frame codes layouts literal form joint physical reference supported).trans
      (Qleisli.RuntimeMultiwayAction.finite_selector_padding_reference frame codes layouts literal _ physical reference supported).symm

#print axioms sector_caller_action
#print axioms supported_caller_action
#print axioms padding_caller_action
#print axioms caller_action

end Qleisli.RuntimeFiniteTargetAction
