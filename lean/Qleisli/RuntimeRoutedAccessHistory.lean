import Qleisli.RuntimeRoutedOriginalBranch
import Qleisli.RuntimeExclusiveCoordinates

/-! Connect the paired branch run to the surrounding original access route.
The two route slices change owner groupings only. The selected child and
full caller still execute the actual ordinary condition and copied arms.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Finite
open Semantics.Observation (Event readOps)
open RuntimeCallTraceFrames (Partition)
open Qleisli.Semantics.ObservingAction (History run)
open Qleisli.RuntimeLiteralBody (SourceHistory SemanticHistoryAgreesWithInherited)

theorem projected_entry_state {dependencies program block offset roles inputTokens ordinary}
    {actual : @RuntimeInterval.Branch dependencies program block offset}
    {entry : RuntimeOwnerMap.Checked roles actual.interval.before}
    (frame : RuntimeBranchProjection.Checked actual entry inputTokens ordinary)
    (child : RuntimeInterval.Branch frame.prepared.block 0) :
    child.interval.before = frame.prepared.block.entry := by
  have input := RuntimeNamedFrameAxes.initialized frame.prepared.inputRead
  have initialRead := child.interval.prefixRead
  change RuntimeInterval.Computed (Raw.Observation.checkOps dependencies 65 frame.prepared.entry [])
    child.interval.before at initialRead
  exact RuntimeAdjacentSlices.checkOps_unique initialRead
    (RuntimeIntervalStates.empty_read dependencies 64 _ input.2.1)

theorem routed_entry_partition {dependencies program block offset roles inputTokens ordinary}
    {actual : @RuntimeInterval.Branch dependencies program block offset}
    {entry : RuntimeOwnerMap.Checked roles actual.interval.before}
    (frame : RuntimeBranchProjection.Checked actual entry inputTokens ordinary)
    (child : RuntimeInterval.Branch frame.prepared.block 0) :
    Partition actual.interval.before.quantum.reference child.interval.before.quantum.reference
      (frame.moves.map (·.2.original.thenBinding.port)) := by
  have input := RuntimeNamedFrameAxes.initialized frame.prepared.inputRead
  have chosen := congrArg Semantics.RawTrace.Interface.live input.1
  change frame.prepared.block.entry.quantum.live = frame.selected at chosen
  rw [projected_entry_state frame child]
  exact Partition.of_native _ _ _ actual.interval.history.1 input.2.1
    (by rw [chosen]; exact frame.completeEntry.symm)

theorem routed_checked_events {dependencies program block offset entry places roles ordinary returned events}
    {actual : @RuntimeInterval.Branch dependencies program block offset}
    (opening : RuntimeAccessPartition.ActiveEntry actual.interval entry places)
    {frame : RuntimeOwnerMap.Checked roles actual.interval.before}
    {projected : RuntimeBranchProjection.Checked actual frame (opening.selected.map (·.token)) ordinary}
    (closing : RuntimeAccessPartition.BranchExit opening projected returned)
    (read : readOps block.fuel actual.interval.before.quantum.reference
      ((block.operations.drop offset).take 1) = some (actual.interval.after.quantum.reference,events)) :
    let size := RuntimeAccessPartition.activeCount places
    readOps block.fuel opening.preamble.before.quantum.reference
      ((block.operations.drop (offset-size)).take (size+1+size)) =
      some (closing.after.quantum.reference,events) := by
  let size := RuntimeAccessPartition.activeCount places
  let original := block.operations.drop (offset-size)
  have split : original.take (size+1+size) =
      original.take size ++ (((block.operations.drop offset).take 1) ++
        ((block.operations.drop (offset+1)).take size)) := by
    simpa only [List.append_assoc] using
      RuntimeAdjacentSlices.three_adjacent_slices block.operations offset 1 size opening.bounded
  obtain ⟨preOps,prefixOps,prefixTrace,_⟩ :=
    Qleisli.Raw.AccessCommutation.structural_interval opening.preamble opening.routes
  obtain ⟨postOps,suffixOps,suffixTrace,_⟩ :=
    Qleisli.Raw.AccessCommutation.structural_trace closing.original closing.routes
  rw [opening.connected] at prefixTrace
  have before :
      readOps (actual.childFuel+1) opening.preamble.before.quantum.reference (original.take size) =
        some (actual.interval.before.quantum.reference,[]) := by
    rw [show original.take size = preOps.map Semantics.Observation.Op.pure from prefixOps]
    exact RuntimeAdjacentSlices.readOps_pure actual.childFuel _ _ _ prefixTrace
  have after :
      readOps (actual.childFuel+1) actual.interval.after.quantum.reference
        ((block.operations.drop (offset+1)).take size) = some (closing.after.quantum.reference,[]) := by
    rw [show (block.operations.drop (offset+1)).take size =
      postOps.map Semantics.Observation.Op.pure from suffixOps]
    exact RuntimeAdjacentSlices.readOps_pure actual.childFuel _ _ _ suffixTrace
  rw [actual.depth] at read
  change readOps block.fuel opening.preamble.before.quantum.reference
    (original.take (size+1+size)) = _
  rw [split,actual.depth,RuntimeAdjacentSlices.readOps_append,before]
  change (do
    let (last,later) ← readOps (actual.childFuel+1) actual.interval.before.quantum.reference
      (((block.operations.drop offset).take 1) ++ ((block.operations.drop (offset+1)).take size))
    return (last,[] ++ later)) = _
  rw [RuntimeAdjacentSlices.readOps_append,read]
  simp only [bind,Option.bind,after,List.nil_append,List.append_nil]
  rfl

private theorem agree_at_routed_return {old new child : Semantics.RawTrace.Interface}
    {spectators history localHistory} (frame : new.frame = old.frame)
    (agrees : Agrees old child spectators history localHistory) :
    Agrees new child spectators history localHistory := by
  refine ⟨agrees.values,agrees.hidden,?_⟩
  intro row column bounded
  have inside : row < 2^old.frame.length := by simpa only [frame] using bounded
  simpa only [project,Semantics.RawTrace.axes,frame] using agrees.operator row column inside

/-- The independently read complete access route has the same ordered
histories as the genuine selected callee on every spectator slice. Moving
the source-owned register back together never changes the output operator. -/
theorem original_routed_access_run
    {dependencies program block offset roles ordinary entry places returned}
    {actual : @RuntimeInterval.Branch dependencies program block offset}
    {inputFrame : RuntimeOwnerMap.Checked roles actual.interval.before}
    (opening : RuntimeAccessPartition.ActiveEntry actual.interval entry places)
    (frame : RuntimeBranchProjection.Checked actual inputFrame (opening.selected.map (·.token)) ordinary)
    (closing : RuntimeAccessPartition.BranchExit opening frame returned)
    (child : RuntimeInterval.Branch frame.prepared.block 0)
    (parentRead : RuntimeOriginalBranch.Trace actual) (childRead : RuntimeOriginalBranch.Trace child)
    (history : History) (localHistory : Nat → History)
    (agrees : Agrees actual.interval.before.quantum.reference child.interval.before.quantum.reference
      (frame.moves.map (·.2.original.thenBinding.port)) history localHistory)
    {events : List Event} {parents : List History}
    (read : readOps block.fuel opening.preamble.before.quantum.reference
      ((block.operations.drop (offset-RuntimeAccessPartition.activeCount places)).take
        (RuntimeAccessPartition.activeCount places+1+RuntimeAccessPartition.activeCount places)) =
      some (closing.after.quantum.reference,events))
    (executed : run dependencies block.fuel events history = some parents) :
    ∃ childEvents children,
      readOps frame.prepared.block.fuel child.interval.before.quantum.reference frame.prepared.block.operations =
        some (child.interval.after.quantum.reference,childEvents) ∧
      Results dependencies block.fuel frame.prepared.block.fuel closing.after.quantum.reference
        child.interval.after.quantum.reference (frame.moves.map (·.2.original.binding.port))
        events childEvents history localHistory parents children := by
  have own := routed_checked_events opening closing parentRead.parentRead
  have sameEvents : _ = events := congrArg Prod.snd (Option.some.inj (own.symm.trans read))
  subst events
  have actualRun := executed
  rw [actual.depth] at actualRun
  obtain ⟨children,paired⟩ := original_routed_branch_run frame child parentRead childRead
    (routed_entry_partition frame child) history localHistory agrees parents actualRun
  have localRead := childRead.parentRead
  change readOps frame.prepared.block.fuel child.interval.before.quantum.reference
    frame.prepared.block.operations = _ at localRead
  refine ⟨_,children,localRead,executed,?_,?_⟩
  · intro high
    rw [child.depth]
    exact paired.childRun high
  · exact paired.paired.imp (fun _ _ related => agree_at_routed_return closing.storage.1 related)

/-- Reassemble the original indexed owner in the source frame after the
ordinary branch. This is a sparse coordinate change valid for every
reference column of the actual complete operator. -/
theorem routed_exit_history_agrees
    {sources caller dependencies program block offset access suspended before ordinary child childRetired childOrdinary}
    {actual : @RuntimeInterval.Branch dependencies program block offset}
    {opening : @RuntimeExclusiveAction.Opened sources caller dependencies program block offset 1
      access actual.interval suspended before}
    {frame : RuntimeBranchProjection.Checked actual opening.frame (opening.route.selected.map (·.token)) ordinary}
    (closing : RuntimeExclusiveAction.BranchClosed opening frame child childRetired childOrdinary)
    {inherited inputs source history}
    (agrees : SemanticHistoryAgreesWithInherited inherited inputs actual.interval.after
      {child with bindings := child.bindings ++ frame.moves.map (·.2.original.binding)}
      closing.finalOrdinary.ssa source history) :
    SemanticHistoryAgreesWithInherited inherited inputs closing.route.after closing.after closing.finalOrdinary.ssa
      (Qleisli.RuntimeExclusiveCoordinates.repartitionHistory
        (before := {child with bindings := child.bindings ++ frame.moves.map (·.2.original.binding)})
        (after := closing.after) closing.repartition
        actual.interval.after.quantum.frame source) history := by
  obtain ⟨work,left,ran⟩ := closing.route.original
  have finalValid := (Raw.Observation.checkOps_invariants _ _ _ _ _ work left ran).1
  have keeps := (Raw.Observation.checkOps_history _ _ _ _ _ work left ran).2.2
  exact Qleisli.RuntimeExclusiveCoordinates.repartition_history_agrees
    (before := {child with bindings := child.bindings ++ frame.moves.map (·.2.original.binding)})
    (after := closing.after) closing.childFrame closing.afterFrame
    closing.childBindings closing.afterBindings actual.interval.history.2.2.1 finalValid
    closing.route.storage.1 keeps closing.repartition agrees

#print axioms routed_entry_partition
#print axioms routed_checked_events
#print axioms original_routed_access_run
#print axioms routed_exit_history_agrees
end Qleisli.RuntimeCallHistory
