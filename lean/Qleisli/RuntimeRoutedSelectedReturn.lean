import Qleisli.RuntimeRoutedReturn
import Qleisli.RuntimeNamedCodeTransport
import Qleisli.RuntimeRoutedPhiSpectators
import Qleisli.RuntimeRoutedCallRun
import Qleisli.RuntimeCallHistoryWeighted
import Qleisli.RuntimeCallHistorySourceReturn

/-! Build the source-owned sparse return frame from the actual selected
callee result and owners parked by the verified literal access route.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open RuntimeOwnerMap (Map)
open RuntimeCallTraceFrames (Partition)
open Qleisli.RuntimeSemanticForest (Available Frame frame_exists product)
open Qleisli.RuntimeSparseBlockEncoding (available_carriers)
open Qleisli.RuntimeStructuralHistory (Represents)
open Qleisli.RuntimeLiteralBody (SourceHistory SemanticHistoryAgreesWithInherited cast_represents)
open Qleisli.RuntimeObservingPrefix (Issued issued_mono)
open Qleisli.RuntimeObservingValueRetention (Supports)
open Qleisli.Semantics.ObservingAction (History WeightedHistory)

private theorem routed_spectators_available {dependencies program block offset roles inputTokens ordinary}
    {actual : @RuntimeInterval.Branch dependencies program block offset}
    {entry : RuntimeOwnerMap.Checked roles actual.interval.before}
    (frame : RuntimeBranchProjection.Checked actual entry inputTokens ordinary)
    (input : Available entry.bindings) :
    Available (frame.moves.map (·.2.original.binding)) := by
  intro result member
  obtain ⟨move,present,rfl⟩ := List.mem_map.mp member
  have old : move.2.original.thenBinding ∈ entry.bindings := List.mem_of_mem_filter move.2.original.thenMember
  obtain ⟨layout⟩ := input _ old
  have sameWidth := (checked_spectator_wire_width frame move present).trans layout.wires
  refine ⟨⟨layout.layout,?_,sameWidth,sameWidth⟩⟩
  rw [RuntimeBranchProjection.Move.owner]
  exact layout.reference

/-- The complete original caller state has the same arbitrary-reference
operator as the selected child weighted over the actual returned parked
owners. The output map is the one checked by the actual close operation. -/
theorem original_routed_selected_return
    {sources caller dependencies program block offset access suspended before ordinary
      childHistory childRetired childOrdinary value}
    {actual : @RuntimeInterval.Branch dependencies program block offset}
    (opening : @RuntimeExclusiveAction.Opened sources caller dependencies program block offset 1
      access actual.interval suspended before)
    (frame : RuntimeBranchProjection.Checked actual opening.frame (opening.route.selected.map (·.token)) ordinary)
    (child : RuntimeInterval.Branch frame.prepared.block 0)
    (event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller)
    (boundary : RuntimeNamedBoundary.Checked child.interval (opening.route.selected.map (·.token)) event
      (RuntimeExclusiveAction.selectedState opening) childHistory childRetired value)
    (closed : RuntimeExclusiveAction.BranchClosed opening frame boundary.after event.consumed childOrdinary)
    (input : Available opening.frame.bindings)
    (selected : Frame childHistory.bindings) {roles}
    (selectedChecked : RuntimeOwnerMap.Checked roles child.interval.after)
    (selectedBindings : selectedChecked.bindings = childHistory.bindings)
    (history : History) (localResults : Nat → History) (joint : Nat → Nat → Nat → ℂ) :
    let spectators := frame.moves.map (·.2.original.binding)
    Partition actual.interval.after.quantum.reference child.interval.after.quantum.reference (spectators.map (·.port)) →
    Agrees actual.interval.after.quantum.reference child.interval.after.quantum.reference (spectators.map (·.port))
      history localResults →
    (∀ high, Represents selected child.interval.after (localResults high) (returnFibre spectators high joint)) →
    ∃ output : Frame closed.childFrame.bindings,
      Represents output actual.interval.after history
        (returnedOperator childHistory.bindings closed.childFrame.bindings boundary.mapped spectators joint) := by
  intro spectators partition agrees childOperator
  have outputEq : closed.childFrame.bindings = boundary.mapped ++ spectators :=
    closed.childBindings.trans (congrArg (· ++ spectators) (projected_named_map opening frame child event boundary))
  have ordered : (boundary.mapped ++ spectators).Perm closed.childFrame.bindings := List.Perm.of_eq outputEq.symm
  have distinct : closed.childFrame.bindings.Nodup :=
    List.Pairwise.of_map (fun binding : RuntimeOwnerMap.Binding => binding.port.token)
      (fun _ _ different same => different (congrArg (fun b : RuntimeOwnerMap.Binding => b.port.token) same))
      closed.childFrame.tokensDistinct
  have carriers := RuntimeNamedCodeTransport.returned_carriers boundary
  have callee := available_carriers carriers selected.available
  have parked := routed_spectators_available frame input
  obtain ⟨frameReturned⟩ := frame_exists (bindings := boundary.mapped ++ spectators) (fun binding member => by
    rcases List.mem_append.mp member with here | there
    · exact callee binding here
    · exact parked binding there)
  let output : Frame closed.childFrame.bindings := outputEq.symm ▸ frameReturned
  exact ⟨output,routed_operator_return selected output frameReturned ordered distinct child.interval.history.2.2.1
    selectedChecked selectedBindings carriers partition history localResults joint agrees childOperator⟩

/-- Phis replace physical spectator ports while preserving their ordered
logical product. Transport the same weighted result family back through the
actual projected return and full caller frame. -/
theorem original_weighted_routed_returns {dependencies program block sources caller}
    (access : @RuntimePureBody.RoutedAccess dependencies program block sources caller)
    (input : Available access.opening.frame.bindings)
    (selected : Frame access.childHistory.bindings) {roles}
    (checked : RuntimeOwnerMap.Checked roles access.projected.interval.after)
    (same : checked.bindings = access.childHistory.bindings)
    {parents : List History} {children family : List (Nat → History)} {joints : List (Nat → Nat → Nat → ℂ)} :
    let original := access.frame.moves.map (·.2.original.thenBinding)
    let parked := access.frame.moves.map (·.2.original.binding)
    Partition access.actual.interval.after.quantum.reference access.projected.interval.after.quantum.reference
      (parked.map (·.port)) →
    List.Forall₂ (Agrees access.actual.interval.after.quantum.reference access.projected.interval.after.quantum.reference
      (parked.map (·.port))) parents children →
    (∀ high, List.Forall₂
      (WeightedHistory (List.range (product original).labels.length) (fun _ => spectatorWeight original high))
      (children.map (fun result => result high)) family) →
    List.Forall₂ (fun parts joint => ∀ index < (product parked).labels.length,
      Represents selected access.projected.interval.after (parts index) (fun digit reference => joint digit index reference))
      family joints →
    List.Forall₂ (fun actual joint => ∃ output : Frame access.closed.childFrame.bindings,
      Represents output access.actual.interval.after actual
        (returnedOperator access.childHistory.bindings access.closed.childFrame.bindings access.boundary.mapped parked joint))
      parents joints := by
  intro original parked partition paired weights logical
  have layout : product parked = product original := routed_spectator_product access.frame
  have sameWeights : ∀ high, List.Forall₂
      (WeightedHistory (List.range (product parked).labels.length) (fun _ => spectatorWeight parked high))
      (children.map (fun result => result high)) family := by
    intro high
    have sameWeight : spectatorWeight parked high = spectatorWeight original high := by
      unfold spectatorWeight
      rw [layout]
    simpa only [layout,sameWeight] using weights high
  have returns := weighted_return_families selected parked sameWeights logical
  refine List.forall₂_of_length_eq_of_get (paired.length_eq.trans returns.length_eq) ?_
  intro index parentBound jointBound
  have childBound : index < children.length := by simpa only [← paired.length_eq] using parentBound
  exact original_routed_selected_return access.opening access.frame access.projected access.event access.boundary
    access.closed input selected checked same _ _ _ partition (paired.get parentBound childBound)
    (returns.get childBound jointBound)

/-- Represent the selected return together with the checked parked phis,
then restore the written caller owner grouping through the literal suffix. -/
noncomputable def routedSourceResult {dependencies program block sources caller}
    (access : @RuntimePureBody.RoutedAccess dependencies program block sources caller)
    (logical : Nat → SourceHistory) : SourceHistory :=
  let parked := access.frame.moves.map (·.2.original.binding)
  let owners := {access.boundary.after with bindings := access.boundary.after.bindings ++ parked}
  let operator := returnedOperator access.childHistory.bindings access.closed.childFrame.bindings
    access.boundary.mapped parked (jointReturn parked logical)
  RuntimeExclusiveCoordinates.repartitionHistory (before := owners) (after := access.closed.after)
    access.closed.repartition access.actual.interval.after.quantum.frame { (logical 0) with owners, operator }

theorem routedSourceResult_congr {dependencies program block sources caller}
    (access : @RuntimePureBody.RoutedAccess dependencies program block sources caller)
    {first second : Nat → SourceHistory}
    (metadata : first 0 = second 0)
    (columns : ∀ index < (product (access.frame.moves.map (·.2.original.thenBinding))).labels.length,
      first index = second index) : routedSourceResult access first = routedSourceResult access second := by
  have same := routed_spectator_product access.frame
  have covered : ∀ index < (product (access.frame.moves.map (·.2.original.binding))).labels.length,
      first index = second index := by simpa only [same] using columns
  simp only [routedSourceResult,metadata,jointReturn_congr _ covered]

/-- Return the source call to the original owner grouping and keep the same
visible SSA values and inherited history on the complete literal chunk. -/
theorem CallRunOn.caller_history_after_routed_return {dependencies program block sources caller}
    (access : @RuntimePureBody.RoutedAccess dependencies program block sources caller)
    (input : Available access.opening.frame.bindings)
    {actual localHistory parentEvents childEvents parents children}
    (run : CallRunOn access.actual.interval access.frame.prepared access.projected.interval.after
      (access.frame.moves.map (·.2.original.binding.port)) actual localHistory parentEvents childEvents parents children)
    (ordinals : List Nat) (inherited : Option (Nat → Prop))
    (incoming : Supports (fun id => match inherited with
      | none => Issued access.actual.interval.before id
      | some held => held id ∨ Issued access.actual.interval.before id) actual)
    {nativeFamily : List (Nat → History)} {sourceFamily : List (Nat → SourceHistory)} :
    let original := access.frame.moves.map (·.2.original.thenBinding)
    (∀ high, List.Forall₂
      (WeightedHistory (List.range (product original).labels.length) (fun _ => spectatorWeight original high))
      (children.map (fun result => result high)) nativeFamily) →
    List.Forall₂ (fun logical native => ∀ index,
      SemanticHistoryAgreesWithInherited (some (fun id => id ∈ actual.values.map Prod.fst))
        ordinals access.projected.interval.after access.childHistory access.childOrdinary
        (logical index) (native index)) sourceFamily nativeFamily →
    List.Forall₂ (SemanticHistoryAgreesWithInherited inherited ordinals access.closed.route.literal.after
      access.closed.after access.closed.finalOrdinary.ssa) (sourceFamily.map (routedSourceResult access)) parents := by
  intro original weights returned
  let parked := access.frame.moves.map (·.2.original.binding)
  let full := {access.boundary.after with bindings := access.boundary.after.bindings ++ parked}
  let operator := fun logical => returnedOperator access.childHistory.bindings access.closed.childFrame.bindings
    access.boundary.mapped parked (jointReturn parked logical)
  have indexed := List.forall₂_map_left_iff.mp (weights 0)
  have paired := run.paired.paired
  have reconstructed : List.Forall₂ (fun actual logical => ∃ output : Frame access.closed.childFrame.bindings,
      Represents output access.actual.interval.after actual (operator logical)) parents sourceFamily := by
    cases sourceFamily with
    | nil =>
      have noNative := List.forall₂_nil_left_iff.mp returned
      have noChildren := List.forall₂_nil_right_iff.mp (noNative ▸ indexed)
      have noParents := List.forall₂_nil_right_iff.mp (noChildren ▸ paired)
      rw [noParents]
      exact .nil
    | cons first rest =>
      have selected : ∃ roles, ∃ checked : RuntimeOwnerMap.Checked roles access.projected.interval.after,
          checked.bindings = access.childHistory.bindings ∧ Nonempty (Frame access.childHistory.bindings) := by
        cases returned with
        | cons head _ =>
          obtain ⟨roles,checked,same,frame,_⟩ := (head 0).2.2.2.2
          exact ⟨roles,checked,same,⟨frame⟩⟩
      obtain ⟨_,checked,same,⟨selected⟩⟩ := selected
      have encodes : List.Forall₂ (fun native joint =>
          ∀ index < (product parked).labels.length,
            Represents selected access.projected.interval.after (native index) (fun digit reference => joint digit index reference))
          nativeFamily ((first::rest).map (jointReturn parked)) := by
        rw [List.forall₂_map_right_iff]
        apply returned.flip.imp
        intro native logical represented index bounded
        obtain ⟨_,_,_,localFrame,encoded⟩ := (represented index).2.2.2.2
        simpa only [jointReturn,if_pos bounded] using (same_frame localFrame selected ▸ encoded)
      have rebuilt := original_weighted_routed_returns access input selected checked same
        (by simpa only [List.map_map,Function.comp_def] using run.partition)
        (by simpa only [List.map_map,Function.comp_def] using paired) weights encodes
      rw [List.forall₂_map_right_iff] at rebuilt
      exact rebuilt
  have preserves : access.actual.interval.before.classical ⊆ access.actual.interval.after.classical := by
    obtain ⟨_,_,receipt⟩ := access.actual.interval.intervalRead
    exact (Raw.Observation.checkOps_history _ _ _ _ _ _ _ receipt).2.2
  rw [List.forall₂_map_left_iff]
  refine List.forall₂_of_length_eq_of_get reconstructed.length_eq.symm ?_
  intro index sourceBound parentBound
  have childBound : index < children.length := by simpa only [← paired.length_eq] using parentBound
  have componentBound : index < nativeFamily.length := by simpa only [← returned.length_eq] using sourceBound
  have callPair := paired.get parentBound childBound
  have weightPair := indexed.get childBound componentBound
  have sourceResult := (returned.get sourceBound componentBound) 0
  have equalValues := (callPair.values 0).trans (weightPair.values 0).symm
  have equalHidden := (callPair.hidden 0).trans (weightPair.hidden 0).symm
  obtain ⟨output,represented⟩ := reconstructed.get parentBound sourceBound
  let parent := parents.get ⟨index,parentBound⟩
  let logical := sourceFamily.get ⟨index,sourceBound⟩
  let staged := { (logical 0) with owners := full, operator := operator logical }
  have allowed := (run.parentValues parent (List.get_mem _ _)).2
  have fullBindings : access.closed.childFrame.bindings = full.bindings := access.closed.childBindings
  have checked : SemanticHistoryAgreesWithInherited inherited ordinals access.actual.interval.after full
      access.closed.finalOrdinary.ssa staged parent := by
    refine ⟨rfl,equalHidden.trans sourceResult.2.1,?_,⟨?_,?_⟩,_,access.closed.childFrame,
      fullBindings,fullBindings ▸ output,?_⟩
    · rw [access.closed.finalOrdinary.measurements,equalValues]
      exact sourceResult.2.2.1
    · intro id expression member
      rw [access.closed.finalOrdinary.measurements,equalValues]
      change (id,expression) ∈ access.closed.finalOrdinary.table at member
      rw [access.closed.finalOrdinary.original] at member
      exact sourceResult.2.2.2.1.1 id expression (List.mem_filter.mp member).1
    · intro id present
      rcases allowed present with old | wrote
      · cases inherited with
        | none => exact issued_mono preserves (incoming old)
        | some held => exact (incoming old).imp (fun held => held) (issued_mono preserves)
      · cases inherited with
        | none => exact wrote
        | some held => exact .inr wrote
    · exact cast_represents fullBindings output represented
  have final := routed_exit_history_agrees access.closed checked
  simpa only [access.closed.route.literalAfter] using final

#print axioms original_routed_selected_return
#print axioms CallRunOn.caller_history_after_routed_return
#print axioms original_weighted_routed_returns
end Qleisli.RuntimeCallHistory
