import Qleisli.RuntimeOriginalBranchJoin
import Qleisli.RuntimeStructuralHistory

/-! The literal branch permutation transports the independent sparse frame
through the exact original owner phis, even after a structural join that
exceeds the bounded per-owner reader.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeOriginalSparsePhi
open QleisliKernel QleisliKernel.Qirf
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode (forestAxes embed)
open Qleisli.RuntimeOriginalQuantumPhi
open Qleisli.RuntimeOriginalBranchJoin (armChecked sourcePhiIndex armPermutation original_branch_join_with)
open RuntimeOrdinarySSA (Agreement bitValue)
open Qleisli.RuntimeObservingValueRetention (Supports)
open Qleisli.RuntimeObservingPrefix (Issued)
open Qleisli.RuntimeNamedThreePackedOutput (final_axes_permutation reorder_gather)
open Qleisli.RuntimeForestRegroup (sourceDimension)
open Qleisli.RuntimeSemanticForest (Available Frame action frame_exists regroup_action)
open Qleisli.RuntimeStructuralHistory (Represents)
open Qleisli.RuntimeNamedThreePackedInstrument (pureHistory)
open Qleisli.Semantics.ObservingAction (History step run)
open QleisliKernel.Semantics.Finite (gather)
open Qleisli.MixedRadix (recode)

private theorem available_to {before after : Map} (paired : List.Forall₂ SameCarrier before after)
    (available : Available before) : Available after := by
  induction paired with
  | nil => intro binding member; cases member
  | @cons input output before after shape _ ih =>
    intro binding member
    rcases List.mem_cons.mp member with rfl | tail
    · obtain ⟨layout⟩ := available input List.mem_cons_self
      exact ⟨⟨layout.layout,shape.1 ▸ layout.reference,shape.2.1 ▸ layout.bits,
        shape.2.2 ▸ layout.wires⟩⟩
    · exact ih (fun b found => available b (List.mem_cons_of_mem _ found)) binding tail

private theorem same_product {before after : Map} (paired : List.Forall₂ SameCarrier before after) :
    RuntimeSemanticForest.product before = RuntimeSemanticForest.product after := by
  induction paired with
  | nil => rfl
  | @cons input output before after shape _ ih =>
    change Semantics.FiniteCarrier.tensor (RuntimeSemanticForest.ownerLayout input)
        (RuntimeSemanticForest.product before) =
      Semantics.FiniteCarrier.tensor (RuntimeSemanticForest.ownerLayout output)
        (RuntimeSemanticForest.product after)
    rw [ih]
    exact congrArg (fun layout => Semantics.FiniteCarrier.tensor layout (RuntimeSemanticForest.product after))
      (congrArg (fun basis => (Semantics.FiniteCarrier.layout basis).getD Semantics.FiniteCarrier.singleton) shape.1)

private theorem bindings_unique {roles state} (checked : RuntimeOwnerMap.Checked roles state) :
    checked.bindings.Nodup :=
  List.Pairwise.of_map (fun binding : Binding => binding.port.token)
    (fun _ _ different same => different (congrArg (fun binding : Binding => binding.port.token) same))
    checked.tokensDistinct

/-- The actual selected arm's final reorder carries the same original source
operator to the output map. Both logical recodes use the full source trees,
and each reference column is arbitrary. -/
theorem original_sparse_phi {dependencies program block offset source spectators leftRoles rightRoles outputRoles}
    (actual : @RuntimeInterval.Branch dependencies program block offset)
    {left : RuntimeOwnerMap.Checked leftRoles actual.thenState}
    {right : RuntimeOwnerMap.Checked rightRoles actual.elseState}
    (bound : RuntimeOwnerPhis.Bound actual source spectators leftRoles rightRoles outputRoles left right)
    (trace : RuntimeOriginalBranch.Trace actual) (choice : Bool)
    (input : Frame (armChecked left right choice).bindings) :
    ∃ output : Frame bound.output.bindings,
    ∀ (recurse : List Semantics.Observation.Event → History → Option (List History))
      (joint : Nat → Nat → ℂ) (history : History),
      Represents input (if choice then actual.thenState else actual.elseState) history joint →
      ∃ moved : History,
        step dependencies recurse
          (RuntimeOriginalBranch.armFinish
            (if choice then actual.thenState else actual.elseState).quantum.reference actual.quantum choice)
          history = some [moved] ∧ moved.hidden = history.hidden ∧ moved.values = history.values ∧
        Represents output actual.interval.after moved (fun row column =>
          joint (sourcePhiIndex bound choice row) column) := by
  let arm := armChecked left right choice
  let state := if choice then actual.thenState else actual.elseState
  let incoming := armBindings bound choice
  let outgoing := outputBindings bound
  have armRead : arm.bindings = if choice then left.bindings else right.bindings := by cases choice <;> rfl
  have beforePerm : incoming.Perm arm.bindings :=
    (arm_bindings_perm actual bound choice).trans (List.Perm.of_eq armRead.symm)
  have afterPerm : outgoing.Perm bound.output.bindings := output_bindings_perm actual bound trace
  have paired : List.Forall₂ SameCarrier incoming outgoing := phi_carriers actual bound choice
  obtain ⟨orderedInput⟩ := frame_exists (fun b member => input.available b (beforePerm.subset member))
  have outgoingAvailable := available_to paired orderedInput.available
  obtain ⟨orderedOutput⟩ := frame_exists outgoingAvailable
  obtain ⟨output⟩ := frame_exists (fun b member => outgoingAvailable b (afterPerm.symm.subset member))
  have same := same_product paired
  have inputCode := RuntimeSemanticForest.product_agrees orderedInput
  have outputCode := RuntimeSemanticForest.product_agrees orderedOutput
  rw [same] at inputCode
  let axes := forestAxes state.quantum.frame incoming
  have literalAxes : Semantics.RawTrace.axes state.quantum.reference
      (Semantics.Observation.phiWires state.quantum.reference actual.quantum choice) = axes := by
    rw [arm_wires actual bound choice]
    rfl
  have order : axes.Perm (List.range state.quantum.frame.length) :=
    ((beforePerm.flatMap_right (fun b : Binding => b.port.wires)).map state.quantum.frame.idxOf).trans
      (final_axes_permutation arm (arm_valid actual choice))
  have afterWires : actual.interval.after.quantum.frame = outgoing.flatMap (·.port.wires) := by
    have frame := congrArg Semantics.RawTrace.Interface.frame trace.joined
    simpa only [Semantics.Observation.phiInterface,outputBindings,← bound.everyRaw,List.flatMap_map,
      RuntimeOwnerPhis.One.binding,outgoing] using frame
  obtain ⟨work,remaining,checked⟩ := actual.interval.intervalRead
  have afterValid := (Raw.Observation.checkOps_invariants _ _ _ _ _ work remaining checked).1
  have afterAxes : forestAxes actual.interval.after.quantum.frame outgoing =
      List.range actual.interval.after.quantum.frame.length := by
    unfold forestAxes
    rw [← afterWires]
    exact RuntimeNamedCallerAction.self_indices _ (Raw.Ownership.valid _ afterValid).frame
  have beforeWidth : (incoming.flatMap (·.port.wires)).length = state.quantum.frame.length := by
    simpa only [axes,forestAxes,List.length_map,List.length_range] using order.length_eq
  have width : state.quantum.frame.length = actual.interval.after.quantum.frame.length :=
    beforeWidth.symm.trans ((wire_count paired).trans (congrArg List.length afterWires).symm)
  refine ⟨output,?_⟩
  intro recurse joint history represented
  let finish := Semantics.Raw.Event.reorder state.quantum.frame.length
    (Semantics.RawTrace.axes state.quantum.reference
      (Semantics.Observation.phiWires state.quantum.reference actual.quantum choice))
  refine ⟨pureHistory dependencies [finish] history,rfl,rfl,rfl,?_⟩
  intro column row bounded
  have inputBound : row < 2^state.quantum.frame.length := by rwa [width]
  change Qleisli.Semantics.RawAction.event dependencies finish (fun r => history.operator r column) row = _
  rw [show finish = .reorder state.quantum.frame.length axes from by dsimp only [finish]; rw [literalAxes]]
  obtain ⟨original,small,coordinate,selected⟩ :=
    reorder_gather dependencies _ _ order (fun r => history.operator r column) row inputBound
  rw [selected,represented column original small]
  let reordered := fun logical ref => joint (recode incoming arm.bindings (sourceDimension arm.bindings) logical) ref
  have beforeEq := regroup_action input orderedInput beforePerm.symm (bindings_unique arm)
    state.quantum.frame joint original column
  rw [beforeEq]
  have moved : action orderedInput state.quantum.frame reordered original column =
      action orderedOutput actual.interval.after.quantum.frame reordered row column := by
    unfold action embed
    rw [show forestAxes state.quantum.frame incoming = axes from rfl,coordinate,afterAxes,
      Raw.Sector.gather_identity row actual.interval.after.quantum.frame.length bounded,
      inputCode.dimension.trans outputCode.dimension.symm]
    apply Qleisli.Exact.sum_map_congr
    intro logical _
    rw [Qleisli.RuntimeForestOrderedProduct.agrees_entry inputCode,
      Qleisli.RuntimeForestOrderedProduct.agrees_entry outputCode]
  rw [moved]
  exact regroup_action orderedOutput output afterPerm (afterPerm.symm.nodup (bindings_unique bound.output))
    actual.interval.after.quantum.frame reordered row column

/-- The literal selected-arm permutation in the independent sparse encoding. -/
theorem original_sparse_phi_history {dependencies program block offset source spectators leftRoles rightRoles outputRoles}
    (actual : @RuntimeInterval.Branch dependencies program block offset)
    {left : RuntimeOwnerMap.Checked leftRoles actual.thenState}
    {right : RuntimeOwnerMap.Checked rightRoles actual.elseState}
    (bound : RuntimeOwnerPhis.Bound actual source spectators leftRoles rightRoles outputRoles left right)
    (trace : RuntimeOriginalBranch.Trace actual) (choice : Bool)
    (joint : Nat → Nat → ℂ) (current : History)
    (frame : Frame (armChecked left right choice).bindings)
    (encoded : Represents frame (if choice then actual.thenState else actual.elseState) current joint) :
    ∃ output : Frame bound.output.bindings,
      Represents output actual.interval.after (pureHistory dependencies [armPermutation actual choice] current)
        (fun row column => joint (sourcePhiIndex bound choice row) column) := by
  obtain ⟨output,transport⟩ := original_sparse_phi actual bound trace choice frame
  obtain ⟨moved,ran,_,_,represented⟩ :=
    transport (run dependencies actual.childFuel) joint current encoded
  have literal : step dependencies (run dependencies actual.childFuel)
      (RuntimeOriginalBranch.armFinish (if choice then actual.thenState else actual.elseState).quantum.reference
        actual.quantum choice) current = some [pureHistory dependencies [armPermutation actual choice] current] := rfl
  have same : moved = pureHistory dependencies [armPermutation actual choice] current :=
    List.cons.inj (Option.some.inj (ran.symm.trans literal)) |>.1
  exact ⟨output,same ▸ represented⟩

/-- Carry the selected original child result family through both phi kinds
using the independent sparse representation for its quantum operators. -/
theorem original_sparse_branch_join {sources rootOwner rootName caller name dependencies program block offset
    path event source actual before left right ordinary leftOrdinary rightOrdinary}
    (action : @RuntimeBranchAction.Checked sources rootOwner rootName caller name dependencies program block offset
      path event source actual before left right ordinary leftOrdinary rightOrdinary)
    (trace : RuntimeOriginalBranch.Trace actual)
    (input : List Nat) (member : input ∈ action.condition.inputs.rows) (bits : List Bool)
    (width : bits.length = ordinary.measurements.length) (history : History)
    {SourceResult : Type} (sourceRun : Bool → Option (List SourceResult))
    (operator : SourceResult → Nat → Nat → ℂ) (outcomes : SourceResult → List Nat)
    (retains : SourceResult → Prop) :
    let reference := RuntimeBranchCondition.reference input ordinary.measurements bits
    Agreement reference history.values ordinary.table →
    Supports (Issued actual.interval.before) history →
    (∀ choice,
      Semantics.SourceOrdinary.evaluate reference action.condition.required = some (bitValue choice) →
      ∃ expected : List SourceResult, ∃ returned : List History,
        sourceRun choice = some expected ∧
        run dependencies actual.childFuel (trace.armBody choice) history = some returned ∧
        List.Forall₂ (fun logical result =>
          retains logical ∧ result.hidden = outcomes logical ∧
          Agreement reference result.values (if choice then leftOrdinary.table else rightOrdinary.table) ∧
          ∃ frame : Frame (armChecked action.thenFrame action.elseFrame choice).bindings,
            Represents frame (if choice then actual.thenState else actual.elseState) result (operator logical)) expected returned) →
    ∃ choice,
      Semantics.SourceOrdinary.evaluate reference action.condition.required = some (bitValue choice) ∧
      ∃ expected : List SourceResult, ∃ returned results : List History,
        sourceRun choice = some expected ∧
        run dependencies actual.childFuel (trace.armBody choice) history = some returned ∧
        step dependencies (run dependencies actual.childFuel)
          (RuntimeOriginalBranch.branchEvent actual trace.left trace.right) history = some results ∧
        List.Forall₂ (fun logical joined =>
          retains logical ∧ joined.hidden = outcomes logical ∧ Agreement reference joined.values action.ordinaryAfter.table ∧
          ∃ output : Frame action.ownerPhis.output.bindings,
            Represents output actual.interval.after joined (fun row column =>
              operator logical (sourcePhiIndex action.ownerPhis choice row) column)) expected results := by
  refine original_branch_join_with action trace input member bits width history sourceRun operator outcomes retains
    (fun choice actualOperator joint =>
      ∃ frame : Frame (armChecked action.thenFrame action.elseFrame choice).bindings,
        ∀ column row, row < 2^(if choice then actual.thenState else actual.elseState).quantum.frame.length →
          actualOperator row column = RuntimeSemanticForest.action frame
            (if choice then actual.thenState else actual.elseState).quantum.frame joint row column)
    (fun actualOperator joint =>
      ∃ frame : Frame action.ownerPhis.output.bindings,
        ∀ column row, row < 2^actual.interval.after.quantum.frame.length →
          actualOperator row column = RuntimeSemanticForest.action frame actual.interval.after.quantum.frame
            joint row column) ?_
  intro choice joint current ⟨frame,encoded⟩
  exact original_sparse_phi_history actual action.ownerPhis trace choice joint current frame encoded

#print axioms original_sparse_phi
#print axioms original_sparse_branch_join
end Qleisli.RuntimeOriginalSparsePhi
