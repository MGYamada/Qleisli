import Qleisli.RuntimeSelectionWitnessAction
import Qleisli.RawActionLocality
import QleisliKernel.Qirf.RuntimeNamedFrameAxes

import Qleisli.RuntimeNamedSelectionParent
import Qleisli.RuntimeFiniteTargetScatter

/-! The complete child selection acts on the original named caller's physical
state. Source arms are taken from the child's checked table and the event list
from the parent's literal trace. Spectators and external references can be correlated.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeNamedSelectionAction
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open RuntimeForestCode
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct Qleisli.RuntimeMultiwayGram

private theorem gather_compressed (base value : Nat) (axes children : List Nat)
    (unique : axes.Nodup) (inside : ∀ axis ∈ children, axis < axes.length) :
    gather (gather (scatter base axes value) axes) children = gather value children := by
  change ((children.zipIdx).map (fun pair =>
    bit (gather (scatter base axes value) axes) pair.1 * 2^pair.2)).sum =
    ((children.zipIdx).map (fun pair => bit value pair.1 * 2^pair.2)).sum
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair member
  have present : pair.1 ∈ children := by
    have mapped : pair.1 ∈ children.zipIdx.map (·.1) := List.mem_map.mpr ⟨pair,member,rfl⟩
    simpa only [List.zipIdx_map_fst] using mapped
  have bound := inside pair.1 present
  rw [RuntimeScatterTransport.gather_at _ axes pair.1 bound,
    RuntimeScatterTransport.scatter_at base value axes unique pair.1 bound]

private theorem forest_axes_bounded {dependencies program block arity start count inputs outputs roles allRoles}
    (frame : @RuntimePureInterval.Checked dependencies program block arity start count inputs outputs roles)
    (complete : RuntimeOwnerMap.Checked allRoles frame.interval.before) :
    ∀ axis ∈ forestAxes frame.interval.before.quantum.frame complete.bindings,
      axis < frame.interval.before.quantum.frame.length := by
  obtain ⟨work,left,read⟩ := frame.interval.prefixRead
  have valid := Raw.Ownership.valid _ (Raw.Observation.checkOps_invariants dependencies block.fuel block.entry
    frame.interval.before (block.operations.take start) work left read).1
  intro axis member
  obtain ⟨wire,covered,rfl⟩ := List.mem_map.mp member
  obtain ⟨binding,present,inside⟩ := List.mem_flatMap.mp covered
  have live : binding.port ∈ frame.interval.before.quantum.live :=
    complete.complete.mem_iff.mp (List.mem_map_of_mem (f := RuntimeOwnerMap.Binding.port) present)
  exact List.idxOf_lt_length_of_mem (valid.covered wire (List.mem_flatMap.mpr ⟨binding.port,live,inside⟩))

/-- Sparse input encodings only inspect the real child-frame axes. This
all-Nat equality avoids a new finite-circuit congruence or event analysis. -/
private theorem reference_compressed {roles state checked} (code : @Frame roles state checked)
    (axes : List Nat) (unique : axes.Nodup)
    (inside : ∀ axis ∈ forestAxes state.quantum.frame checked.bindings, axis < axes.length)
    {Reference : Type} (joint : Nat → Reference → ℂ) (base value : Nat) (reference : Reference) :
    referenceAction code joint (gather (scatter base axes value) axes) reference =
      referenceAction code joint value reference := by
  unfold referenceAction
  apply Qleisli.Exact.sum_map_congr
  intro logical _member
  change scalar (sparseEntry code.code
      (gather (gather (scatter base axes value) axes) (forestAxes state.quantum.frame checked.bindings)) logical) *
        joint logical reference =
    scalar (sparseEntry code.code (gather value (forestAxes state.quantum.frame checked.bindings)) logical) *
        joint logical reference
  rw [gather_compressed base value axes _ unique inside]

/-- Encode only the selected child input using its actual sparse input code.
The arbitrary spectator coordinate is the full parent label with the selected
axes cleared. Dependence between logical, spectator and external reference
coordinates is unrestricted; this is not a tensor-product state premise. -/
noncomputable def encodedParent {roles state checked} (code : @Frame roles state checked)
    (axes : List Nat) {Reference : Type} (joint : Nat → Nat → Reference → ℂ)
    (physical : Nat) (reference : Reference) : ℂ :=
  referenceAction code
    (fun logical (environment : Nat × Reference) => joint logical environment.1 environment.2)
    (gather physical axes) (scatter physical axes 0,reference)

def sourceSlice (axes : List Nat) (base : Nat) {Reference : Type}
    (joint : Nat → Nat → Reference → ℂ) : Nat → Reference → ℂ :=
  fun logical reference => joint logical (scatter base axes 0) reference

private theorem encoded_pull {roles state checked} (code : @Frame roles state checked)
    (axes : List Nat) (unique : axes.Nodup)
    (inside : ∀ axis ∈ forestAxes state.quantum.frame checked.bindings, axis < axes.length)
    {Reference : Type} (joint : Nat → Nat → Reference → ℂ) (base value : Nat) (reference : Reference) :
    encodedParent code axes joint (scatter base axes value) reference =
      referenceAction code (sourceSlice axes base joint) value reference := by
  unfold encodedParent
  rw [RuntimeFiniteTargetScatter.scatter_overwrite base value 0 axes unique]
  exact reference_compressed code axes unique inside
    (fun logical (environment : Nat × Reference) => joint logical environment.1 environment.2)
    base value (scatter base axes 0,reference)

/-- This is the fixed-Literal checked_selection consumer used inside
RuntimeSelectionWitnessAction.checked_selection. OrdinalTable is Prop; proof
irrelevance identifies its receipt, never different matrices or source uses. -/
private theorem fixed_selection_action {Reference : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {labels : List Nat} {expected logical : List Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (equations : RuntimeInterval.Computed (NominalSector.checkLogicals
      inputCode outputCode retained.sectors labels expected) logical)
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (table : OrdinalTable inputCode outputCode retained.sectors labels expected)
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) :
    Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
      (fun input => referenceAction literal.inputCode joint input reference) physical =
    Qleisli.RuntimeMultiwayAction.finiteReferenceAction literal.outputCode
      (sourceAction frame codes layouts literal table joint) physical reference := by
  obtain ⟨_same,_table,actual,_gram⟩ := Qleisli.RuntimeFiniteTargetGram.checked_selection
    frame codes layouts equations literal joint joint reference reference
  exact actual physical

/-- The same contiguous interval supplies both native folds. Its actual
parent trace realizes the child's original source table on each reference fibre. -/
theorem selection_reference_action
    {dependencies program block callStart callCount callInputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount callInputs ordinary effect)
    {start count inputs outputs selector target}
    (frame : RuntimePureInterval.Checked scope.prepared.block 2 start count inputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {labels : List Nat} {expected logical : List Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (equations : RuntimeInterval.Computed (NominalSector.checkLogicals
      inputCode outputCode retained.sectors labels expected) logical)
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (_original : RuntimeInterval.Computed (RuntimeLocalEvents.readSource frame selectorBits targetBits retained
      restricted codes.owners) literal)
    (starts : start = 0) (covers : count = ((block.operations.drop callStart).take callCount).length) :
    ∃ parentEvents, RuntimeLocalEvents.trace scope.interval.before.quantum.reference frame.operations =
        some ⟨scope.interval.after.quantum.reference,parentEvents,scope.interval.before.quantum.frame.length⟩ ∧
    logical = expected ∧ ∃ table : OrdinalTable inputCode outputCode retained.sectors labels expected,
      ∀ {Reference : Type} (joint : Nat → Nat → Reference → ℂ) (base physical : Nat) (reference : Reference),
        Qleisli.Semantics.RawAction.events dependencies parentEvents
          (fun input => encodedParent literal.inputCode (RuntimeNamedFrameAxes.mixedAxes scope) joint input reference)
          (scatter base (RuntimeNamedFrameAxes.mixedAxes scope) physical) =
        Qleisli.RuntimeMultiwayAction.finiteReferenceAction literal.outputCode
          (sourceAction frame codes layouts literal table
            (sourceSlice (RuntimeNamedFrameAxes.mixedAxes scope) base joint)) physical reference := by
  obtain ⟨parentEvents,parentTrace,parentAction⟩ :=
    RuntimeNamedSelectionParent.parent_action scope frame starts covers literal
  have entry : frame.interval.before.quantum.reference = scope.localEntry.quantum.reference :=
    (RuntimeNamedSelectionParent.at_zero frame.interval starts).trans
      ((RuntimeNamedFrameAxes.mixedAxes_input scope).2.2.1.trans (RuntimeNamedFrameAxes.mixedAxes_input scope).2.1.symm)
  have localFrame := congrArg Semantics.RawTrace.Interface.frame (RuntimeNamedFrameAxes.mixedAxes_input scope).2.1
  change scope.localEntry.quantum.frame = scope.selected.flatMap (·.wires) at localFrame
  have size : (RuntimeNamedFrameAxes.mixedAxes scope).length = scope.localEntry.quantum.frame.length := by
    simp only [RuntimeNamedFrameAxes.mixedAxes,RuntimeForestCode.portAxes,List.length_map,localFrame]
  refine ⟨parentEvents,parentTrace,?_⟩
  obtain ⟨same,table⟩ := ordinal_table equations
  have frameEq : frame.interval.before.quantum.frame = scope.localEntry.quantum.frame :=
    congrArg Semantics.RawTrace.Interface.frame entry
  have width : (RuntimeNamedFrameAxes.mixedAxes scope).length = frame.interval.before.quantum.frame.length := by
    rw [frameEq]
    exact size
  have unique := (RuntimeNamedFrameAxes.mixedAxes_bounds scope).1
  have inside : ∀ axis ∈ forestAxes frame.interval.before.quantum.frame codes.owners.before.bindings,
      axis < (RuntimeNamedFrameAxes.mixedAxes scope).length := by
    intro axis member
    rw [width]
    exact forest_axes_bounded frame codes.owners.before axis member
  refine ⟨same,table,?_⟩
  intro Reference joint base physical reference
  let values := fun input => encodedParent literal.inputCode (RuntimeNamedFrameAxes.mixedAxes scope) joint input reference
  have encoded : Qleisli.Semantics.RawAction.Locality.pull base (RuntimeNamedFrameAxes.mixedAxes scope) values =
      (fun input => referenceAction literal.inputCode
        (sourceSlice (RuntimeNamedFrameAxes.mixedAxes scope) base joint) input reference) := by
    funext input
    exact encoded_pull literal.inputCode _ unique inside joint base input reference
  calc
    _ = Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
        (Qleisli.Semantics.RawAction.Locality.pull base (RuntimeNamedFrameAxes.mixedAxes scope) values) physical :=
      congrFun (parentAction values base) physical
    _ = Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
        (fun input => referenceAction literal.inputCode
          (sourceSlice (RuntimeNamedFrameAxes.mixedAxes scope) base joint) input reference) physical := by rw [encoded]
    _ = _ := fixed_selection_action frame codes layouts equations literal table
      (sourceSlice (RuntimeNamedFrameAxes.mixedAxes scope) base joint) physical reference

#print axioms selection_reference_action

end Qleisli.RuntimeNamedSelectionAction
