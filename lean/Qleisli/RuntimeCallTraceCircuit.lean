import Qleisli.RuntimeCallTraceProjection
import Qleisli.RuntimeApplyTrace
import Qleisli.RuntimeTraceBounds
import Qleisli.RawFiniteRows

/-! Exact circuit locality in the original parent and child call frames.
Bounded rows allow the child tape to ignore coefficients outside its frame.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallTraceCircuit
open QleisliKernel QleisliKernel.Qirf Semantics.Finite
open Semantics.Raw (Port Event)
open RuntimeCallTraceFrames (Partition WireOrder)
open RuntimeCallTraceProjection (split_axes)
open Qleisli.RuntimeForestProduct (gather_bound)
open Qleisli.Semantics.RawAction (event events circuit)

theorem circuit_partition {parent child spectators : List Nat}
    (partition : parent.Perm (child++spectators)) (unique : parent.Nodup)
    (dependencies : List Dependency) (steps : List Step)
    (bounded : RuntimeLocalEvents.bounds child.length [steps] = true)
    (joint : Nat → Nat → ℂ) (row : Nat) :
    circuit dependencies (steps.map (Semantics.RawTrace.localize (child.map parent.idxOf)))
      (fun input => joint (gather input (child.map parent.idxOf))
        (gather input (spectators.map parent.idxOf))) row =
    circuit dependencies steps
      (fun input => joint input (gather row (spectators.map parent.idxOf)))
      (gather row (child.map parent.idxOf)) := by
  let selected := child.map parent.idxOf
  let other := spectators.map parent.idxOf
  let full := fun input => joint (gather input selected) (gather input other)
  let slice := fun input => joint input (gather row other)
  have mapped := List.nodup_append.mp ((split_axes partition unique).nodup_iff.mpr List.nodup_range)
  have apart : other.Disjoint selected :=
    List.disjoint_left.mpr fun axis second first => mapped.2.2 axis first axis second rfl
  have controls := RuntimeLocalEvents.bounds_controls bounded
  have targets := RuntimeLocalEvents.bounds_targets bounded
  have stepControls : ∀ step ∈ steps, ∀ control ∈ step.controls, control.index < selected.length := by
    simpa only [selected,List.length_map] using controls steps List.mem_cons_self
  have stepTargets : ∀ step ∈ steps, ∀ axis ∈ QleisliKernel.Finite.targets step.action, axis < child.length :=
    targets steps List.mem_cons_self
  have localAction := Qleisli.Semantics.RawAction.Locality.circuit_output
    dependencies row selected mapped.1 steps stepControls
    (by simpa only [selected,List.length_map] using stepTargets) full
  have same : RawFiniteRows.OnRows child.length
      (Qleisli.Semantics.RawAction.Locality.pull row selected full) slice := by
    intro input inputBound
    change joint (gather (scatter row selected input) selected) (gather (scatter row selected input) other) =
      joint input (gather row other)
    rw [RuntimeFiniteTargetScatter.gather_scatter row input selected mapped.1
      (by simpa only [selected,List.length_map] using inputBound),
      RuntimeTargetScatter.gather_disjoint row input selected other apart]
  have congruent := (RawFiniteRows.BoundedEvent.circuit child.length steps stepTargets).congr
    dependencies _ _ same
  have outputBound : gather row selected < 2^child.length := by
    simpa only [selected,List.length_map] using gather_bound row selected
  exact localAction.trans (congruent _ outputBound)

/-- The checked original applyUnitary tape uses the same local circuit
action in both actual frames, including when the original tape is empty. -/
theorem apply_correlated (dependencies : List Dependency)
    (parent child : Raw.State) (spectators : List Port)
    (partition : Partition parent.reference child.reference spectators)
    (input output : Nat) (written : List Step) (parentAfter childAfter : Raw.Transition)
    (parentRead : Raw.step (dependencies.map (·.signature)) parent (.applyUnitary input output written) = .ok parentAfter)
    (childRead : Raw.step (dependencies.map (·.signature)) child (.applyUnitary input output written) = .ok childAfter)
    (joint : Nat → Nat → ℂ) (row : Nat) :
    let other := WireOrder spectators
    Partition parentAfter.state.reference childAfter.state.reference spectators ∧
    parentAfter.state.frame = parent.frame ∧ childAfter.state.frame = child.frame ∧
    events dependencies parentAfter.events
      (fun input => joint (gather input (child.frame.map parent.frame.idxOf))
        (gather input (other.map parent.frame.idxOf))) row =
      events dependencies childAfter.events
        (fun input => joint input (gather row (other.map parent.frame.idxOf)))
        (gather row (child.frame.map parent.frame.idxOf)) := by
  intro other
  obtain ⟨steps,childEvents,parentEvents,live,parentFrame,childFrame,_,_⟩ :=
    RuntimeApplyTrace.applyUnitary_locality _ parent child spectators input output written
      parentAfter childAfter partition.live parentRead childRead
  have bounded := RuntimeTraceBounds.apply_bounds _ child input output written childAfter steps childRead childEvents
  have unique := (Raw.Ownership.valid _ (Raw.step_conditions _ _ _ _ parentRead).1).frame
  refine ⟨⟨live,?_⟩,parentFrame,childFrame,?_⟩
  · change parentAfter.state.frame.Perm (childAfter.state.frame ++ other)
    rw [parentFrame,childFrame]
    exact partition.frame
  · simp only [parentEvents,childEvents,events,List.foldl_cons,List.foldl_nil,event]
    exact circuit_partition partition.frame unique dependencies steps bounded joint row

#print axioms circuit_partition
#print axioms apply_correlated
end Qleisli.RuntimeCallTraceCircuit
