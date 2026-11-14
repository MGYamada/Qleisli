import Qleisli.RuntimeCallTraceProjection
import Qleisli.RuntimeOriginalObservation

/-! Exact locality of fixed-width computed actions in original call frames.
The selected action operates on an arbitrary correlated spectator slice.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallTraceComputed
open QleisliKernel
open Semantics.Finite (gather scatter)
open Semantics.Raw (Port)
open Semantics.RawTrace (Interface take insert axes)
open RuntimeCallTraceFrames (Partition WireOrder)
open RuntimeCallTraceProjection (split_axes scatter_project)
open Qleisli.RuntimeOriginalObservation (gather_retained)
open Qleisli.Semantics.RawAction (embed event events)

theorem embed_partition {parent child spectators wires : List Nat}
    (partition : parent.Perm (child++spectators)) (unique : parent.Nodup) (inside : wires ⊆ child)
    (action : (Nat → ℂ) → Nat → ℂ) (joint : Nat → Nat → ℂ) (row : Nat) :
    embed (wires.map parent.idxOf) action
      (fun input => joint (gather input (child.map parent.idxOf))
        (gather input (spectators.map parent.idxOf))) row =
    embed (wires.map child.idxOf) action
      (fun input => joint input (gather row (spectators.map parent.idxOf)))
      (gather row (child.map parent.idxOf)) := by
  have mapped := List.nodup_append.mp ((split_axes partition unique).nodup_iff.mpr List.nodup_range)
  have untouched : (spectators.map parent.idxOf).Disjoint (wires.map parent.idxOf) := by
    apply List.disjoint_left.mpr
    intro axis spectator selected
    obtain ⟨wire,member,rfl⟩ := List.mem_map.mp selected
    exact mapped.2.2 _ (List.mem_map_of_mem (inside member)) _ spectator rfl
  unfold embed
  rw [gather_retained parent child wires _ rfl inside row]
  congr 1
  funext replacement
  dsimp only
  rw [scatter_project inside mapped.1,
    RuntimeTargetScatter.gather_disjoint row replacement _ _ untouched]

/-- Two successful reads of the same certified compute use the same local
action, including the original scratch computation and its uncomputation. -/
theorem certified_compute_correlated (dependencies : List Semantics.Finite.Dependency)
    (parent child : Raw.State) (spectators : List Port)
    (partition : Partition parent.reference child.reference spectators)
    (input output : Nat) (ancilla function : List Nat) (uses logical : List Semantics.Finite.Step)
    (parentAfter childAfter : Raw.Transition)
    (parentRead : Raw.step (dependencies.map (·.signature)) parent
      (.certifiedCompute input output ancilla function uses logical) = .ok parentAfter)
    (childRead : Raw.step (dependencies.map (·.signature)) child
      (.certifiedCompute input output ancilla function uses logical) = .ok childAfter) :
    let other := WireOrder spectators
    Partition parentAfter.state.reference childAfter.state.reference spectators ∧
    parentAfter.state.frame = parent.frame ∧ childAfter.state.frame = child.frame ∧
    ∀ (joint : Nat → Nat → ℂ) (row : Nat),
    events dependencies parentAfter.events
      (fun input => joint (gather input (child.frame.map parent.frame.idxOf))
        (gather input (other.map parent.frame.idxOf))) row =
      events dependencies childAfter.events
        (fun input => joint input (gather row (other.map parent.frame.idxOf)))
        (gather row (child.frame.map parent.frame.idxOf)) := by
  intro other
  have parentFacts := Raw.Ownership.valid _ (Raw.step_conditions _ _ _ _ parentRead).1
  have childFacts := Raw.Ownership.valid _ (Raw.step_conditions _ _ _ _ childRead).1
  have parentTrace := Raw.step_reference _ _ _ _ parentRead
  have childTrace := Raw.step_reference _ _ _ _ childRead
  simp only [Semantics.RawTrace.step] at childTrace
  obtain ⟨⟨port,childTaken⟩,childTake,childResult⟩ := Option.bind_eq_some_iff.mp childTrace
  obtain ⟨parentTaken,parentTake,live,parentFrame,childFrame,_⟩ :=
    RuntimeTraceSpectators.take_spectators _ _ _ partition.live parentFacts.owners childTake
  have childData := Prod.mk.inj (Option.some.inj childResult)
  simp only [Semantics.RawTrace.step,parentTake,bind,Option.bind,pure] at parentTrace
  have parentData := Prod.mk.inj (Option.some.inj parentTrace)
  have inserted := RuntimeTraceSpectators.insert_spectators _ _ _ live output port.wires
  have pFrame : parentAfter.state.frame = parent.frame :=
    (congrArg Interface.frame parentData.1).symm.trans parentFrame
  have cFrame : childAfter.state.frame = child.frame :=
    (congrArg Interface.frame childData.1).symm.trans childFrame
  have afterLive : parentAfter.state.live.Perm (childAfter.state.live ++ spectators) := by
    change parentAfter.state.reference.live.Perm (childAfter.state.reference.live ++ spectators)
    rw [← parentData.1,← childData.1]
    exact inserted.1
  have inside : port.wires ⊆ child.frame := fun wire member => childFacts.covered wire
    (List.mem_flatMap.mpr ⟨port,RuntimeCallTraceFrames.taken_member childTake,member⟩)
  refine ⟨⟨afterLive,?_⟩,pFrame,cFrame,?_⟩
  · change parentAfter.state.frame.Perm (childAfter.state.frame ++ other)
    rw [pFrame,cFrame]
    exact partition.frame
  · intro joint row
    rw [← parentData.2,← childData.2]
    simp only [events,List.foldl_cons,List.foldl_nil,event,axes,List.length_map]
    exact embed_partition partition.frame parentFacts.frame inside _ joint row

/-- The original structural predicate acts on the same local data axes in
both call frames, retaining arbitrary spectator correlations. -/
theorem structural_compute_correlated (dependencies : List Semantics.Finite.Dependency)
    (parent child : Raw.State) (spectators : List Port)
    (partition : Partition parent.reference child.reference spectators)
    (input output scratch : Nat) (forward inverse : List Semantics.Finite.Step) (uses : List Semantics.Raw.Use)
    (parentAfter childAfter : Raw.Transition)
    (parentRead : Raw.step (dependencies.map (·.signature)) parent
      (.structuralCompute input output scratch forward inverse uses) = .ok parentAfter)
    (childRead : Raw.step (dependencies.map (·.signature)) child
      (.structuralCompute input output scratch forward inverse uses) = .ok childAfter) :
    let other := WireOrder spectators
    Partition parentAfter.state.reference childAfter.state.reference spectators ∧
    parentAfter.state.frame = parent.frame ∧ childAfter.state.frame = child.frame ∧
    ∀ (joint : Nat → Nat → ℂ) (row : Nat),
    events dependencies parentAfter.events
      (fun input => joint (gather input (child.frame.map parent.frame.idxOf))
        (gather input (other.map parent.frame.idxOf))) row =
      events dependencies childAfter.events
        (fun input => joint input (gather row (other.map parent.frame.idxOf)))
        (gather row (child.frame.map parent.frame.idxOf)) := by
  intro other
  have parentFacts := Raw.Ownership.valid _ (Raw.step_conditions _ _ _ _ parentRead).1
  have childFacts := Raw.Ownership.valid _ (Raw.step_conditions _ _ _ _ childRead).1
  have parentTrace := Raw.step_reference _ _ _ _ parentRead
  have childTrace := Raw.step_reference _ _ _ _ childRead
  simp only [Semantics.RawTrace.step] at childTrace
  obtain ⟨⟨port,childTaken⟩,childTake,childResult⟩ := Option.bind_eq_some_iff.mp childTrace
  obtain ⟨parentTaken,parentTake,live,parentFrame,childFrame,_⟩ :=
    RuntimeTraceSpectators.take_spectators _ _ _ partition.live parentFacts.owners childTake
  have childData := Prod.mk.inj (Option.some.inj childResult)
  simp only [Semantics.RawTrace.step,parentTake,bind,Option.bind,pure] at parentTrace
  have parentData := Prod.mk.inj (Option.some.inj parentTrace)
  have inserted := RuntimeTraceSpectators.insert_spectators _ _ _ live output port.wires
  have pFrame : parentAfter.state.frame = parent.frame :=
    (congrArg Interface.frame parentData.1).symm.trans parentFrame
  have cFrame : childAfter.state.frame = child.frame :=
    (congrArg Interface.frame childData.1).symm.trans childFrame
  have afterLive : parentAfter.state.live.Perm (childAfter.state.live ++ spectators) := by
    change parentAfter.state.reference.live.Perm (childAfter.state.reference.live ++ spectators)
    rw [← parentData.1,← childData.1]
    exact inserted.1
  have inside : port.wires ⊆ child.frame := fun wire member => childFacts.covered wire
    (List.mem_flatMap.mpr ⟨port,RuntimeCallTraceFrames.taken_member childTake,member⟩)
  refine ⟨⟨afterLive,?_⟩,pFrame,cFrame,?_⟩
  · change parentAfter.state.frame.Perm (childAfter.state.frame ++ other)
    rw [pFrame,cFrame]
    exact partition.frame
  · intro joint row
    rw [← parentData.2,← childData.2]
    simp only [events,List.foldl_cons,List.foldl_nil,event,axes,List.length_map]
    exact embed_partition partition.frame parentFacts.frame inside _ joint row

#print axioms embed_partition
#print axioms certified_compute_correlated
end Qleisli.RuntimeCallTraceComputed
