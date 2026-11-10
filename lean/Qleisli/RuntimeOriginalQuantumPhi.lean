import Qleisli.RuntimeNamedThreePackedInstrument
import Qleisli.RuntimeOriginalBranch
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.Forall2

/-! The original quantum phi order pairs every selected arm owner with its
checked output. The exact Raw reorder reads the same ordered arm wires.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeOriginalQuantumPhi
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open RuntimeOwnerMap (Binding Map)

def armBindings {dependencies program block offset actual source spectators leftRoles rightRoles outputRoles left right}
    (bound : @RuntimeOwnerPhis.Bound dependencies program block offset actual source spectators
      leftRoles rightRoles outputRoles left right) (choice : Bool) : Map :=
  bound.phis.map (fun pair => if choice then pair.2.thenBinding else pair.2.elseBinding)

def outputBindings {dependencies program block offset actual source spectators leftRoles rightRoles outputRoles left right}
    (bound : @RuntimeOwnerPhis.Bound dependencies program block offset actual source spectators
      leftRoles rightRoles outputRoles left right) : Map :=
  bound.phis.map (fun pair => pair.2.binding)

theorem arm_valid {dependencies program block offset}
    (actual : @RuntimeInterval.Branch dependencies program block offset) (choice : Bool) :
    Raw.stateValid (if choice then actual.thenState else actual.elseState).quantum = true := by
  cases choice with
  | false =>
    obtain ⟨work,remaining,ran⟩ := actual.elseRead
    exact (Raw.Observation.checkOps_invariants _ _ _ _ _ work remaining ran).1
  | true =>
    obtain ⟨work,remaining,ran⟩ := actual.thenRead
    exact (Raw.Observation.checkOps_invariants _ _ _ _ _ work remaining ran).1

private theorem port_lookup {roles state} (checked : RuntimeOwnerMap.Checked roles state)
    (valid : Raw.stateValid state.quantum = true) (binding : Binding) (member : binding ∈ checked.bindings)
    (token : Nat) (same : binding.port.token = token) :
    state.quantum.live.find? (fun port => port.token == token) = some binding.port := by
  subst token
  have live := checked.complete.mem_iff.mp (List.mem_map_of_mem member)
  exact RuntimeNamedFrameAxes.tokenLookup state.quantum.live binding.port (Raw.Ownership.valid _ valid).owners live

private theorem equal_size_perm {selected original : Map}
    (unique : (selected.map (·.port.token)).Nodup)
    (contained : selected ⊆ original) (size : selected.length = original.length) : selected.Perm original := by
  have distinct : selected.Nodup := List.Pairwise.of_map (fun binding : Binding => binding.port.token)
    (fun _ _ different equal => different (congrArg (fun binding : Binding => binding.port.token) equal)) unique
  obtain ⟨other,permuted,sublist⟩ := List.subperm_iff.mp (distinct.subperm contained)
  have same := sublist.eq_of_length (size.trans permuted.length_eq.symm)
  exact same ▸ permuted

/-- The exact Raw phi order enumerates the complete selected arm map, retaining
separate owners even when their physical wire lists are empty. -/
theorem arm_bindings_perm {dependencies program block offset source spectators leftRoles rightRoles outputRoles}
    (actual : @RuntimeInterval.Branch dependencies program block offset)
    {left : RuntimeOwnerMap.Checked leftRoles actual.thenState}
    {right : RuntimeOwnerMap.Checked rightRoles actual.elseState}
    (bound : RuntimeOwnerPhis.Bound actual source spectators leftRoles rightRoles outputRoles left right)
    (choice : Bool) :
    (armBindings bound choice).Perm (if choice then left.bindings else right.bindings) := by
  have native := (RuntimeOriginalBranch.original_branch_phi_checks actual).1
  simp only [Raw.Observation.phiValid,Bool.and_eq_true,beq_iff_eq] at native
  obtain ⟨⟨⟨⟨⟨⟨thenUnique,elseUnique⟩,thenSize⟩,elseSize⟩,_⟩,_⟩,_⟩ := native
  have tokens : (armBindings bound choice).map (·.port.token) =
      actual.quantum.map (fun phi => if choice then phi.thenToken else phi.elseToken) := by
    rw [← bound.everyRaw]
    simp only [armBindings,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro pair _
    cases choice
    · exact pair.2.elseToken
    · exact pair.2.thenToken
  apply equal_size_perm
  · rw [tokens]
    cases choice
    · exact Raw.Ownership.unique_nodup _ elseUnique
    · exact Raw.Ownership.unique_nodup _ thenUnique
  · intro binding member
    obtain ⟨pair,_member,same⟩ := List.mem_map.mp member
    subst binding
    cases choice
    · exact pair.2.elseMember
    · exact pair.2.thenMember
  · have size := congrArg List.length bound.everyRaw
    simp only [List.length_map] at size
    unfold armBindings
    rw [List.length_map,size]
    cases choice
    · exact elseSize.trans (by simpa only [List.length_map] using right.complete.length_eq.symm)
    · exact thenSize.trans (by simpa only [List.length_map] using left.complete.length_eq.symm)

/-- The original source return ordering covers exactly the same bindings as
the Raw phi output list, including each fresh source result and spectator. -/
theorem output_bindings_perm {dependencies program block offset source spectators leftRoles rightRoles outputRoles}
    (actual : @RuntimeInterval.Branch dependencies program block offset)
    {left : RuntimeOwnerMap.Checked leftRoles actual.thenState}
    {right : RuntimeOwnerMap.Checked rightRoles actual.elseState}
    (bound : RuntimeOwnerPhis.Bound actual source spectators leftRoles rightRoles outputRoles left right)
    (trace : RuntimeOriginalBranch.Trace actual) : (outputBindings bound).Perm bound.output.bindings := by
  obtain ⟨work,remaining,ran⟩ := bound.outputDerived
  obtain ⟨ordered,middle,orderRead,checkRead⟩ := bind_success _ _ _ _ _ ran
  have bindings := RuntimeBoundaryOwnerEvidence.check_bindings bound.output ⟨middle,remaining,checkRead⟩
  have subset : bound.output.bindings ⊆ outputBindings bound := by
    rw [bindings]
    exact (RuntimeSelectionPartition.order_values _ _ _ ⟨work,middle,orderRead⟩).1
  have liveSize : actual.interval.after.quantum.live.length = actual.quantum.length := by
    simpa only [Semantics.Observation.phiInterface,List.length_map] using
      congrArg (fun state : Semantics.RawTrace.Interface => state.live.length) trace.joined
  have checkedSize : bound.output.bindings.length = actual.interval.after.quantum.live.length := by
    simpa only [List.length_map] using bound.output.complete.length_eq
  have size : bound.output.bindings.length = (outputBindings bound).length := by
    unfold outputBindings
    rw [List.length_map,checkedSize,liveSize]
    simpa only [List.length_map] using (congrArg List.length bound.everyRaw).symm
  exact (equal_size_perm bound.output.tokensDistinct subset size).symm

/-- The literal arm's final permutation reads precisely the ordered wires of
the checked source bindings that supply the original quantum phis. -/
theorem arm_wires {dependencies program block offset source spectators leftRoles rightRoles outputRoles}
    (actual : @RuntimeInterval.Branch dependencies program block offset)
    {left : RuntimeOwnerMap.Checked leftRoles actual.thenState}
    {right : RuntimeOwnerMap.Checked rightRoles actual.elseState}
    (bound : RuntimeOwnerPhis.Bound actual source spectators leftRoles rightRoles outputRoles left right)
    (choice : Bool) :
    let state := if choice then actual.thenState else actual.elseState
    Semantics.Observation.phiWires state.quantum.reference actual.quantum choice =
      (armBindings bound choice).flatMap (·.port.wires) := by
  intro state
  unfold Semantics.Observation.phiWires armBindings
  rw [← bound.everyRaw,List.flatMap_map,List.flatMap_map]
  apply List.flatMap_congr
  intro pair _
  cases choice with
  | false =>
    exact congrArg (fun port : Option Semantics.Raw.Port => (port.map (·.wires)).getD [])
      (port_lookup right (arm_valid actual false) pair.2.elseBinding pair.2.elseMember
        pair.1.elseToken pair.2.elseToken)
  | true =>
    exact congrArg (fun port : Option Semantics.Raw.Port => (port.map (·.wires)).getD [])
      (port_lookup left (arm_valid actual true) pair.2.thenBinding pair.2.thenMember
        pair.1.thenToken pair.2.thenToken)

def SameCarrier (input output : Binding) : Prop :=
  input.owner.basis = output.owner.basis ∧ input.port.bits = output.port.bits ∧
    input.port.wires.length = output.port.wires.length

/-- Each pair uses the original source phi's full basis and the actual
validated input and output port shapes. A spectator uses its original owner. -/
theorem phi_carriers {dependencies program block offset source spectators leftRoles rightRoles outputRoles}
    (actual : @RuntimeInterval.Branch dependencies program block offset)
    {left : RuntimeOwnerMap.Checked leftRoles actual.thenState}
    {right : RuntimeOwnerMap.Checked rightRoles actual.elseState}
    (bound : RuntimeOwnerPhis.Bound actual source spectators leftRoles rightRoles outputRoles left right)
    (choice : Bool) : List.Forall₂ SameCarrier (armBindings bound choice) (outputBindings bound) := by
  unfold armBindings outputBindings
  rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
  intro pair member
  have phiMember : pair.1 ∈ actual.quantum := bound.everyRaw ▸ List.mem_map_of_mem member
  have native := (RuntimeOriginalBranch.original_branch_phi_checks actual).1
  simp only [Raw.Observation.phiValid,Bool.and_eq_true,List.all_eq_true] at native
  have sizes := native.2 pair.1 phiMember
  have leftValid := arm_valid actual true
  have rightValid := arm_valid actual false
  rw [port_lookup left leftValid pair.2.thenBinding pair.2.thenMember pair.1.thenToken pair.2.thenToken,
    port_lookup right rightValid pair.2.elseBinding pair.2.elseMember pair.1.elseToken pair.2.elseToken] at sizes
  simp only [Bool.and_eq_true,beq_iff_eq] at sizes
  have leftShape := (Raw.Ownership.valid _ leftValid).ports pair.2.thenBinding.port
    (left.complete.mem_iff.mp (List.mem_map_of_mem pair.2.thenMember))
  have rightShape := (Raw.Ownership.valid _ rightValid).ports pair.2.elseBinding.port
    (right.complete.mem_iff.mp (List.mem_map_of_mem pair.2.elseMember))
  have leftBits : pair.2.thenBinding.port.bits = pair.1.wires.length := sizes.2.symm
  have rightBits : pair.2.elseBinding.port.bits = pair.1.wires.length := sizes.1.symm.trans leftBits
  have bases := pair.2.role.sameType
  cases choice
  · exact ⟨bases.2,rightBits,rightShape.1.symm.trans rightBits⟩
  · exact ⟨bases.1,leftBits,leftShape.1.symm.trans leftBits⟩

open RuntimeForestCode (OwnerCode OwnerCodes)
open Qleisli.RuntimeForestOrderedProduct (layouts layoutProduct)

/-- Preserve each actual layout along the complete phi pairing, with no new
owner-code evaluation and no identification by width alone. -/
theorem transport_codes {inputs outputs : Map} (paired : List.Forall₂ SameCarrier inputs outputs)
    (codes : OwnerCodes inputs) :
    ∃ after : OwnerCodes outputs, layouts after = layouts codes := by
  induction paired with
  | nil => cases codes; exact ⟨.nil,rfl⟩
  | @cons input output inputs outputs shape paired ih =>
    cases codes with
    | cons first rest =>
      obtain ⟨tail,same⟩ := ih rest
      have read : Carrier.readOwner ⟨output.port,output.owner.basis⟩ =
          Carrier.readOwner ⟨input.port,input.owner.basis⟩ := by
        unfold Carrier.readOwner
        rw [← shape.1,← shape.2.1,← shape.2.2]
      let current : OwnerCode output := ⟨first.layout,by rw [read]; exact first.original⟩
      refine ⟨.cons current tail,?_⟩
      simp only [layouts,same]
      rfl

open RuntimeForestCode (Frame forestAxes sparseEntry)
open RuntimeOwnerCodeReindex (dimensionAt reindex reindex_exists)
open Qleisli.RuntimeForestOrderedProduct (frame_product_agrees)
open Qleisli.RuntimeForestProduct (referenceAction)
open Qleisli.RuntimeNamedThreePackedOutput (packedAction recode_return reorder_packed final_axes_permutation)
open Qleisli.Semantics.Exact (scalar)
open Qleisli.Semantics.ObservingAction (History)
open Qleisli.RuntimeNamedThreePackedInstrument (pureHistory)
open QleisliKernel.Semantics.Finite (gather)

private def ordered_map {roles state} (checked : RuntimeOwnerMap.Checked roles state)
    (bindings : Map) (order : bindings.Perm checked.bindings) :
    RuntimeOwnerMap.Checked (bindings.map (·.owner)) state := by
  refine ⟨bindings,rfl,?_,(order.map (·.port.token)).nodup_iff.mpr checked.tokensDistinct,
    (order.map (·.port)).trans checked.complete⟩
  have original : (checked.bindings.map (fun binding => binding.owner.ordinal)).Nodup := by
    have distinct := checked.ownersDistinct
    rw [← checked.ordered] at distinct
    simpa only [List.map_map,Function.comp_def] using distinct
  simpa only [List.map_map,Function.comp_def] using
    (order.map (fun binding => binding.owner.ordinal)).nodup_iff.mpr original

theorem wire_count {inputs outputs : Map} (paired : List.Forall₂ SameCarrier inputs outputs) :
    (inputs.flatMap (·.port.wires)).length = (outputs.flatMap (·.port.wires)).length := by
  induction paired with
  | nil => rfl
  | cons head _ tail =>
    simp only [List.flatMap_cons,List.length_append,head.2.2,tail]

private theorem packed_same {leftRoles leftState leftChecked rightRoles rightState rightChecked}
    (left : @Frame leftRoles leftState leftChecked) (right : @Frame rightRoles rightState rightChecked)
    (same : layoutProduct left.owners = layoutProduct right.owners)
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (ref : Reference) :
    packedAction left joint row ref = packedAction right joint row ref := by
  have leftCode := frame_product_agrees left
  have rightCode := frame_product_agrees right
  rw [same] at leftCode
  unfold packedAction
  rw [leftCode.dimension.trans rightCode.dimension.symm]
  apply Qleisli.Exact.sum_map_congr
  intro logical _member
  have label := (leftCode.labels logical).trans (rightCode.labels logical).symm
  simp only [sparseEntry,label]

private theorem packed_identity {roles state checked} (frame : @Frame roles state checked)
    (axes : forestAxes state.quantum.frame checked.bindings = List.range state.quantum.frame.length)
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat)
    (bounded : row < 2^state.quantum.frame.length) (ref : Reference) :
    packedAction frame joint row ref = referenceAction frame joint row ref := by
  unfold packedAction referenceAction
  apply Qleisli.Exact.sum_map_congr
  intro logical _member
  change scalar (sparseEntry frame.code row logical) * joint logical ref =
    scalar (sparseEntry frame.code (gather row (forestAxes state.quantum.frame checked.bindings)) logical) * joint logical ref
  rw [axes,Raw.Sector.gather_identity row state.quantum.frame.length bounded]

/-- The original branch's quantum permutation transports the complete
selected arm encoding into the actual checked source output map. The two
logical recodes follow that arm's binding order, the exact phi pairing, and
the original output-owner order. All external reference columns are free. -/
theorem original_quantum_phi_action {dependencies program block offset source spectators leftRoles rightRoles outputRoles roles}
    (actual : @RuntimeInterval.Branch dependencies program block offset)
    {left : RuntimeOwnerMap.Checked leftRoles actual.thenState}
    {right : RuntimeOwnerMap.Checked rightRoles actual.elseState}
    (bound : RuntimeOwnerPhis.Bound actual source spectators leftRoles rightRoles outputRoles left right)
    (trace : RuntimeOriginalBranch.Trace actual) (choice : Bool)
    (arm : RuntimeOwnerMap.Checked roles (if choice then actual.thenState else actual.elseState))
    (armRead : arm.bindings = if choice then left.bindings else right.bindings)
    (input : Frame arm) :
    let state := if choice then actual.thenState else actual.elseState
    let axes := Semantics.RawTrace.axes state.quantum.reference
      (Semantics.Observation.phiWires state.quantum.reference actual.quantum choice)
    ∃ output : Frame bound.output,
    ∃ beforeCodes : OwnerCodes (armBindings bound choice),
    ∃ afterCodes : OwnerCodes (outputBindings bound),
      reindex input.owners (armBindings bound choice) = some beforeCodes ∧
      layouts afterCodes = layouts beforeCodes ∧
      reindex afterCodes bound.output.bindings = some output.owners ∧
      let index := fun logical =>
        Qleisli.MixedRadix.recode (armBindings bound choice) arm.bindings (dimensionAt input.owners)
          (Qleisli.MixedRadix.recode bound.output.bindings (outputBindings bound)
            (dimensionAt afterCodes) logical)
      (∀ {Reference : Type} (joint : Nat → Reference → ℂ) row,
        row < 2^actual.interval.after.quantum.frame.length → ∀ ref,
          Qleisli.Semantics.RawAction.event dependencies (.reorder state.quantum.frame.length axes)
            (fun physical => referenceAction input joint physical ref) row =
          referenceAction output (fun logical reference => joint (index logical) reference) row ref) ∧
      ∀ (recurse : List Semantics.Observation.Event → History → Option (List History))
        (joint : Nat → Nat → ℂ) (history : History),
        (∀ col, RawFiniteRows.OnRows state.quantum.frame.length (fun row => history.operator row col)
          (fun row => referenceAction input joint row col)) →
        ∃ after : History,
          Qleisli.Semantics.ObservingAction.step dependencies recurse
            (RuntimeOriginalBranch.armFinish state.quantum.reference actual.quantum choice) history = some [after] ∧
          after.hidden = history.hidden ∧ after.values = history.values ∧
          ∀ col, RawFiniteRows.OnRows actual.interval.after.quantum.frame.length
            (fun row => after.operator row col)
            (fun row => referenceAction output (fun logical reference => joint (index logical) reference) row col) := by
  intro state axes
  have beforePerm := (arm_bindings_perm actual bound choice).trans (List.Perm.of_eq armRead.symm)
  have afterPerm := output_bindings_perm actual bound trace
  have paired := phi_carriers actual bound choice
  obtain ⟨beforeCodes,beforeRead⟩ := reindex_exists input.owners _ beforePerm.subset
  obtain ⟨afterCodes,same⟩ := transport_codes paired beforeCodes
  obtain ⟨outputCodes,outputRead⟩ := reindex_exists afterCodes _ afterPerm.symm.subset
  let beforeMap := ordered_map arm (armBindings bound choice) beforePerm
  let afterMap := ordered_map bound.output (outputBindings bound) afterPerm
  obtain ⟨beforeFrame,beforeOwners⟩ := RuntimeForestFrameEvidence.with_ownerCodes beforeMap beforeCodes
  obtain ⟨afterFrame,afterOwners⟩ := RuntimeForestFrameEvidence.with_ownerCodes afterMap afterCodes
  obtain ⟨output,outputOwners⟩ := RuntimeForestFrameEvidence.with_ownerCodes bound.output outputCodes
  refine ⟨output,beforeCodes,afterCodes,beforeRead,same,by rw [outputOwners]; exact outputRead,?_⟩
  have beforeAxes : axes = forestAxes state.quantum.frame beforeMap.bindings := by
    change Semantics.RawTrace.axes state.quantum.reference
      (Semantics.Observation.phiWires state.quantum.reference actual.quantum choice) = _
    rw [arm_wires actual bound choice]
    rfl
  have afterWires : actual.interval.after.quantum.frame = (outputBindings bound).flatMap (·.port.wires) := by
    have frame := congrArg Semantics.RawTrace.Interface.frame trace.joined
    simpa only [Semantics.Observation.phiInterface,outputBindings,← bound.everyRaw,List.flatMap_map,
      RuntimeOwnerPhis.One.binding] using frame
  obtain ⟨work,remaining,checked⟩ := actual.interval.intervalRead
  have afterValid := (Raw.Observation.checkOps_invariants _ _ _ _ _ work remaining checked).1
  have beforeOrder := final_axes_permutation beforeMap (arm_valid actual choice)
  have afterAxes : forestAxes actual.interval.after.quantum.frame afterMap.bindings =
      List.range actual.interval.after.quantum.frame.length := by
    change ((outputBindings bound).flatMap (·.port.wires)).map actual.interval.after.quantum.frame.idxOf = _
    rw [← afterWires]
    exact RuntimeNamedCallerAction.self_indices _ (Raw.Ownership.valid _ afterValid).frame
  have beforeWidth : ((armBindings bound choice).flatMap (·.port.wires)).length = state.quantum.frame.length := by
    simpa only [forestAxes,List.length_map,List.length_range] using beforeOrder.length_eq
  have width : state.quantum.frame.length = actual.interval.after.quantum.frame.length :=
    beforeWidth.symm.trans ((wire_count paired).trans (congrArg List.length afterWires).symm)
  have sameLayout : layoutProduct beforeFrame.owners = layoutProduct afterFrame.owners := by
    unfold layoutProduct
    rw [beforeOwners,afterOwners]
    exact congrArg (List.foldr Semantics.FiniteCarrier.tensor Semantics.FiniteCarrier.singleton) same.symm
  let index := fun logical =>
    Qleisli.MixedRadix.recode (armBindings bound choice) arm.bindings (dimensionAt input.owners)
      (Qleisli.MixedRadix.recode bound.output.bindings (outputBindings bound) (dimensionAt afterCodes) logical)
  have equation : ∀ {Reference : Type} (joint : Nat → Reference → ℂ) row,
      row < 2^actual.interval.after.quantum.frame.length → ∀ ref,
        Qleisli.Semantics.RawAction.event dependencies (.reorder state.quantum.frame.length axes)
          (fun physical => referenceAction input joint physical ref) row =
        referenceAction output (fun logical reference => joint (index logical) reference) row ref := by
    intro Reference joint row bounded ref
    let reordered : Nat → Reference → ℂ := fun logical reference =>
      joint (Qleisli.MixedRadix.recode (armBindings bound choice) arm.bindings (dimensionAt input.owners) logical) reference
    have old : (fun physical => referenceAction input joint physical ref) =
        fun physical => referenceAction beforeFrame reordered physical ref := by
      funext physical
      exact recode_return input beforeFrame beforePerm rfl joint physical ref
    have inputBound : row < 2^state.quantum.frame.length := by rwa [width]
    rw [beforeAxes,old]
    calc
      _ = packedAction beforeFrame reordered row ref := reorder_packed beforeFrame dependencies beforeOrder reordered row inputBound ref
      _ = packedAction afterFrame reordered row ref := packed_same beforeFrame afterFrame sameLayout reordered row ref
      _ = referenceAction afterFrame reordered row ref := packed_identity afterFrame afterAxes reordered row bounded ref
      _ = _ := by
        have outputEq := recode_return afterFrame output afterPerm.symm rfl reordered row ref
        rwa [afterOwners] at outputEq
  refine ⟨equation,?_⟩
  intro recurse joint history represented
  let finish := Semantics.Raw.Event.reorder state.quantum.frame.length axes
  let after := pureHistory dependencies [finish] history
  refine ⟨after,rfl,rfl,rfl,?_⟩
  intro col row bounded
  have inputBound : row < 2^state.quantum.frame.length := by rwa [width]
  have transferred := (RawFiniteRows.BoundedEvent.reorder state.quantum.frame.length axes).congr
    dependencies _ _ (represented col) row inputBound
  exact transferred.trans (equation joint row bounded col)

#print axioms arm_bindings_perm
#print axioms output_bindings_perm
#print axioms arm_wires
#print axioms phi_carriers
#print axioms transport_codes
#print axioms original_quantum_phi_action
end Qleisli.RuntimeOriginalQuantumPhi
