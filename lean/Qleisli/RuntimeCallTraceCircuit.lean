import Qleisli.RuntimeCallTraceProjection
import Qleisli.RuntimeApplyTrace
import Qleisli.RuntimeTraceBounds
import Qleisli.RuntimeGateTrace
import Qleisli.RuntimeCnotTrace
import Qleisli.RuntimeToffoliTrace
import Qleisli.RuntimeQuantumIfTrace
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

/-- Checked fixed frames and the exact action of the actual transition on
each spectator slice. The final state is the state of the original read. -/
structure Transfer (dependencies : List Dependency) (parent child : Raw.State)
    (spectators : List Port) (parentAfter childAfter : Raw.Transition) : Prop where
  partition : Partition parentAfter.state.reference childAfter.state.reference spectators
  parentFrame : parentAfter.state.frame = parent.frame
  childFrame : childAfter.state.frame = child.frame
  operator : ∀ (joint : Nat → Nat → ℂ) (row : Nat),
    events dependencies parentAfter.events
      (fun input => joint (gather input (child.frame.map parent.frame.idxOf))
        (gather input ((WireOrder spectators).map parent.frame.idxOf))) row =
      events dependencies childAfter.events
        (fun input => joint input (gather row ((WireOrder spectators).map parent.frame.idxOf)))
        (gather row (child.frame.map parent.frame.idxOf))

private theorem single_circuit {dependencies : List Dependency} {parent child : Raw.State}
    {spectators : List Port} {parentAfter childAfter : Raw.Transition} {steps : List Step}
    (partition : Partition parent.reference child.reference spectators)
    (unique : parent.frame.Nodup)
    (parentEvents : parentAfter.events = [.circuit parent.frame.length
      (steps.map (Semantics.RawTrace.localize (child.frame.map parent.frame.idxOf)))])
    (childEvents : childAfter.events = [.circuit child.frame.length steps])
    (live : parentAfter.state.live.Perm (childAfter.state.live ++ spectators))
    (parentFrame : parentAfter.state.frame = parent.frame)
    (childFrame : childAfter.state.frame = child.frame)
    (bounded : RuntimeLocalEvents.bounds child.frame.length [steps] = true) :
    Transfer dependencies parent child spectators parentAfter childAfter := by
  refine ⟨⟨live,?_⟩,parentFrame,childFrame,?_⟩
  · change parentAfter.state.frame.Perm (childAfter.state.frame ++ WireOrder spectators)
    rw [parentFrame,childFrame]
    exact partition.frame
  · intro joint row
    simp only [parentEvents,childEvents,events,List.foldl_cons,List.foldl_nil,event]
    exact circuit_partition partition.frame unique dependencies steps bounded joint row

/-- Original single-gate action, including its exact phase. -/
theorem gate_correlated (dependencies : List Dependency) (parent child : Raw.State) (spectators : List Port)
    (partition : Partition parent.reference child.reference spectators)
    (value : Semantics.Raw.Gate) (input output : Nat) (parentAfter childAfter : Raw.Transition)
    (parentRead : Raw.step (dependencies.map (·.signature)) parent (.gate value input output) = .ok parentAfter)
    (childRead : Raw.step (dependencies.map (·.signature)) child (.gate value input output) = .ok childAfter) :
    Transfer dependencies parent child spectators parentAfter childAfter := by
  obtain ⟨steps,childEvents,parentEvents,live,parentFrame,childFrame,_,_⟩ :=
    RuntimeGateTrace.gate_locality _ parent child spectators value input output parentAfter childAfter
      partition.live parentRead childRead
  exact single_circuit partition (Raw.Ownership.valid _ (Raw.step_conditions _ _ _ _ parentRead).1).frame
    parentEvents childEvents live parentFrame childFrame
    (RuntimeTraceBounds.gate_bounds _ child value input output childAfter steps childRead childEvents)

/-- The original CNOT retains the written control and target. -/
theorem cnot_correlated (dependencies : List Dependency) (parent child : Raw.State) (spectators : List Port)
    (partition : Partition parent.reference child.reference spectators)
    (control target controlOut targetOut : Nat) (parentAfter childAfter : Raw.Transition)
    (parentRead : Raw.step (dependencies.map (·.signature)) parent
      (.cnot control target controlOut targetOut) = .ok parentAfter)
    (childRead : Raw.step (dependencies.map (·.signature)) child
      (.cnot control target controlOut targetOut) = .ok childAfter) :
    Transfer dependencies parent child spectators parentAfter childAfter := by
  obtain ⟨steps,childEvents,parentEvents,live,parentFrame,childFrame,_,_⟩ :=
    RuntimeCnotTrace.cnot_locality _ parent child spectators control target controlOut targetOut
      parentAfter childAfter partition.live parentRead childRead
  exact single_circuit partition (Raw.Ownership.valid _ (Raw.step_conditions _ _ _ _ parentRead).1).frame
    parentEvents childEvents live parentFrame childFrame
    (RuntimeTraceBounds.cnot_bounds _ child control target controlOut targetOut childAfter steps childRead childEvents)

/-- The original Toffoli keeps both controls and their original axis order. -/
theorem toffoli_correlated (dependencies : List Dependency) (parent child : Raw.State) (spectators : List Port)
    (partition : Partition parent.reference child.reference spectators)
    (a b target aOut bOut targetOut : Nat) (parentAfter childAfter : Raw.Transition)
    (parentRead : Raw.step (dependencies.map (·.signature)) parent
      (.toffoli a b target aOut bOut targetOut) = .ok parentAfter)
    (childRead : Raw.step (dependencies.map (·.signature)) child
      (.toffoli a b target aOut bOut targetOut) = .ok childAfter) :
    Transfer dependencies parent child spectators parentAfter childAfter := by
  obtain ⟨steps,childEvents,parentEvents,live,parentFrame,childFrame,_,_⟩ :=
    RuntimeToffoliTrace.toffoli_locality _ parent child spectators a b target aOut bOut targetOut
      parentAfter childAfter partition.live parentRead childRead
  exact single_circuit partition (Raw.Ownership.valid _ (Raw.step_conditions _ _ _ _ parentRead).1).frame
    parentEvents childEvents live parentFrame childFrame
    (RuntimeTraceBounds.toffoli_bounds _ child a b target aOut bOut targetOut childAfter steps childRead childEvents)

/-- Both coherently controlled tapes use the same original controls and
tape order in the two checked frames. -/
theorem quantum_if_correlated (dependencies : List Dependency) (parent child : Raw.State) (spectators : List Port)
    (partition : Partition parent.reference child.reference spectators)
    (control target controlOut targetOut : Nat) (zero one : List Semantics.Raw.UnitaryStep)
    (parentAfter childAfter : Raw.Transition)
    (parentRead : Raw.step (dependencies.map (·.signature)) parent
      (.quantumIf control target controlOut targetOut zero one) = .ok parentAfter)
    (childRead : Raw.step (dependencies.map (·.signature)) child
      (.quantumIf control target controlOut targetOut zero one) = .ok childAfter) :
    Transfer dependencies parent child spectators parentAfter childAfter := by
  obtain ⟨zeroLocal,oneLocal,_,_,childEvents,parentEvents,live,parentFrame,childFrame,_,_⟩ :=
    RuntimeQuantumIfTrace.quantumIf_locality _ parent child spectators control target controlOut targetOut
      zero one parentAfter childAfter partition.live parentRead childRead
  exact single_circuit partition (Raw.Ownership.valid _ (Raw.step_conditions _ _ _ _ parentRead).1).frame
    (by simpa only [List.map_append] using parentEvents) childEvents live parentFrame childFrame
    (RuntimeTraceBounds.quantumIf_bounds _ child control target controlOut targetOut zero one
      childAfter (zeroLocal++oneLocal) childRead childEvents)

/-- The checked original applyUnitary tape uses the same local circuit
action in both actual frames, including when the original tape is empty. -/
theorem apply_correlated (dependencies : List Dependency)
    (parent child : Raw.State) (spectators : List Port)
    (partition : Partition parent.reference child.reference spectators)
    (input output : Nat) (written : List Step) (parentAfter childAfter : Raw.Transition)
    (parentRead : Raw.step (dependencies.map (·.signature)) parent (.applyUnitary input output written) = .ok parentAfter)
    (childRead : Raw.step (dependencies.map (·.signature)) child (.applyUnitary input output written) = .ok childAfter) :
    Transfer dependencies parent child spectators parentAfter childAfter := by
  obtain ⟨steps,childEvents,parentEvents,live,parentFrame,childFrame,_,_⟩ :=
    RuntimeApplyTrace.applyUnitary_locality _ parent child spectators input output written
      parentAfter childAfter partition.live parentRead childRead
  exact single_circuit partition (Raw.Ownership.valid _ (Raw.step_conditions _ _ _ _ parentRead).1).frame
    parentEvents childEvents live parentFrame childFrame
    (RuntimeTraceBounds.apply_bounds _ child input output written childAfter steps childRead childEvents)

#print axioms circuit_partition
#print axioms gate_correlated
#print axioms cnot_correlated
#print axioms toffoli_correlated
#print axioms quantum_if_correlated
#print axioms apply_correlated
end Qleisli.RuntimeCallTraceCircuit
