import Qleisli.RuntimeCallTraceProjection
import Qleisli.RuntimeOriginalObservation

/-! Exact basis expansion in the original parent and child frames.
The finite input sum keeps the spectator coordinate of the output row
and allows arbitrary correlations in the incoming coefficients.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallTraceBasis
open QleisliKernel QleisliKernel.Qirf
open Semantics.Finite (gather scatter)
open RuntimeCallTraceFrames (Partition WireOrder basis_lift_events)
open RuntimeCallTraceProjection (split_axes split_eq sum_split scatter_project)
open RuntimeCallTraceAllocation (gather_extended old_axes)
open Qleisli.RuntimeForestProduct (gather_bound)
open Qleisli.RuntimeOriginalObservation (gather_retained)
open Qleisli.Semantics.RawAction (events event)

private theorem lift_sum (parent child spectators after localAfter inputWires outputWires extra table : List Nat)
    (partition : parent.Perm (child++spectators))
    (afterPartition : after.Perm (localAfter++spectators))
    (parentUnique : parent.Nodup) (afterUnique : after.Nodup)
    (parentGrowth : after = parent++extra) (childGrowth : localAfter = child++extra)
    (inputInside : inputWires ⊆ child) (outputInside : outputWires ⊆ localAfter)
    (joint : Nat → Nat → ℂ) (row : Nat) (bounded : row < 2^after.length) :
    ((List.range (2^parent.length)).map fun input =>
      if scatter input (outputWires.map after.idxOf)
          (table[gather input (inputWires.map parent.idxOf)]?.getD 0) = row then
        joint (gather input (child.map parent.idxOf)) (gather input (spectators.map parent.idxOf))
      else 0).sum =
    ((List.range (2^child.length)).map fun input =>
      if scatter input (outputWires.map localAfter.idxOf)
          (table[gather input (inputWires.map child.idxOf)]?.getD 0) =
          gather row (localAfter.map after.idxOf) then
        joint input (gather row (spectators.map after.idxOf))
      else 0).sum := by
  let environment := gather row (spectators.map after.idxOf)
  let localRow := gather row (localAfter.map after.idxOf)
  let write := fun input => scatter input (outputWires.map localAfter.idxOf)
    (table[gather input (inputWires.map child.idxOf)]?.getD 0)
  let term : Nat → Nat → ℂ := fun input high =>
    if write input = localRow ∧ environment = high then joint input high else 0
  have childInside : child ⊆ parent := fun _ member =>
    partition.mem_iff.mpr (List.mem_append_left _ member)
  have spectatorInside : spectators ⊆ parent := fun _ member =>
    partition.mem_iff.mpr (List.mem_append_right _ member)
  have outputParent : outputWires ⊆ after := fun _ member =>
    afterPartition.mem_iff.mpr (List.mem_append_left _ (outputInside member))
  have fresh : parent.Disjoint extra := by
    have unique : (parent++extra).Nodup := parentGrowth ▸ afterUnique
    exact List.disjoint_left.mpr (fun wire old new => (List.nodup_append.mp unique).2.2 wire old wire new rfl)
  have mapped := List.nodup_append.mp
    ((split_axes afterPartition afterUnique).nodup_iff.mpr List.nodup_range)
  have untouched : (spectators.map after.idxOf).Disjoint (outputWires.map after.idxOf) := by
    apply List.disjoint_left.mpr
    intro axis spectator chosen
    obtain ⟨wire,member,rfl⟩ := List.mem_map.mp chosen
    exact mapped.2.2 _ (List.mem_map_of_mem (outputInside member)) _ spectator rfl
  have sameSpectators : spectators.map after.idxOf = spectators.map parent.idxOf := by
    rw [parentGrowth]
    exact old_axes parent extra spectators spectatorInside
  have key (input : Nat) (inputBound : input < 2^parent.length) :
      scatter input (outputWires.map after.idxOf)
          (table[gather input (inputWires.map parent.idxOf)]?.getD 0) = row ↔
        write (gather input (child.map parent.idxOf)) = localRow ∧
          environment = gather input (spectators.map parent.idxOf) := by
    let replacement := table[gather input (inputWires.map parent.idxOf)]?.getD 0
    have original : gather (gather input (child.map parent.idxOf)) (inputWires.map child.idxOf) =
        gather input (inputWires.map parent.idxOf) :=
      gather_retained parent child inputWires _ rfl inputInside input
    have extended : gather input (localAfter.map after.idxOf) = gather input (child.map parent.idxOf) := by
      rw [parentGrowth,childGrowth]
      exact gather_extended parent child extra childInside fresh input inputBound
    have selected : gather (scatter input (outputWires.map after.idxOf) replacement)
        (localAfter.map after.idxOf) = write (gather input (child.map parent.idxOf)) := by
      rw [scatter_project outputInside mapped.1,extended]
      simp only [write,original,replacement]
    have other : gather (scatter input (outputWires.map after.idxOf) replacement)
        (spectators.map after.idxOf) = gather input (spectators.map parent.idxOf) := by
      rw [RuntimeTargetScatter.gather_disjoint input replacement _ _ untouched,sameSpectators]
    have larger : parent.length ≤ after.length := by simp [parentGrowth]
    have updatedBound : scatter input (outputWires.map after.idxOf) replacement < 2^after.length := by
      apply Qleisli.Finite.Pull.scatter_bound
      · exact Nat.lt_of_lt_of_le inputBound (Nat.pow_le_pow_right (by decide) larger)
      · intro axis present
        obtain ⟨wire,member,rfl⟩ := List.mem_map.mp present
        exact List.idxOf_lt_length_of_mem (outputParent member)
    change scatter input (outputWires.map after.idxOf) replacement = row ↔ _
    rw [split_eq afterPartition afterUnique updatedBound bounded,selected,other]
    change (_ = localRow ∧ _ = environment) ↔ _
    exact and_congr_right (fun _ => eq_comm)
  calc
    _ = ((List.range (2^parent.length)).map fun input =>
        term (gather input (child.map parent.idxOf)) (gather input (spectators.map parent.idxOf))).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro input member
      simp only [term,key input (List.mem_range.mp member)]
    _ = ((List.range (2^spectators.length)).map fun high =>
        ((List.range (2^child.length)).map fun input => term input high).sum).sum :=
      sum_split partition parentUnique term
    _ = ((List.range (2^spectators.length)).map fun high =>
        if environment = high then ((List.range (2^child.length)).map fun input =>
          if write input = localRow then joint input high else 0).sum else 0).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro high _
      by_cases same : environment = high
      · rw [if_pos same]
        simp only [term,same,and_true]
      · simp [term,same]
    _ = _ := by
      have environmentBound : environment < 2^spectators.length := by
        simpa only [environment,List.length_map] using gather_bound row (spectators.map after.idxOf)
      exact Qleisli.Exact.range_delta_sum _ _ _ environmentBound

/-- The two successful reads of the same original basis lift induce the
same action on the selected block in the actual caller's spectator slice. -/
theorem basis_lift_correlated (dependencies : List Semantics.Finite.Dependency)
    (parent child : Raw.State) (spectators : List Semantics.Raw.Port)
    (partition : Partition parent.reference child.reference spectators)
    (input output : Nat) (wires table : List Nat) (parentAfter childAfter : Raw.Transition)
    (parentRead : Raw.step (dependencies.map (·.signature)) parent (.liftBasis input output wires table) = .ok parentAfter)
    (childRead : Raw.step (dependencies.map (·.signature)) child (.liftBasis input output wires table) = .ok childAfter)
    (joint : Nat → Nat → ℂ) (row : Nat) (bounded : row < 2^parentAfter.state.frame.length) :
    let other := WireOrder spectators
    events dependencies parentAfter.events
      (fun input => joint (gather input (child.frame.map parent.frame.idxOf))
        (gather input (other.map parent.frame.idxOf))) row =
    events dependencies childAfter.events
      (fun input => joint input (gather row (other.map parentAfter.state.frame.idxOf)))
      (gather row (childAfter.state.frame.map parentAfter.state.frame.idxOf)) := by
  intro other
  obtain ⟨port,afterPartition,parentGrowth,childGrowth,inputInside,outputInside,parentEvents,childEvents,_,_⟩ :=
    basis_lift_events parent child spectators partition input output wires table parentAfter childAfter parentRead childRead
  obtain ⟨parentValid,_,afterValid⟩ := Raw.step_conditions _ _ _ _ parentRead
  simp only [parentEvents,childEvents,events,List.foldl_cons,List.foldl_nil,event,beq_iff_eq]
  exact lift_sum parent.frame child.frame other parentAfter.state.frame childAfter.state.frame port.wires wires
    (wires.drop port.bits) table partition.frame afterPartition.frame
    (Raw.Ownership.valid _ parentValid).frame (Raw.Ownership.valid _ afterValid).frame
    parentGrowth childGrowth inputInside outputInside joint row bounded

#print axioms basis_lift_correlated
end Qleisli.RuntimeCallTraceBasis
