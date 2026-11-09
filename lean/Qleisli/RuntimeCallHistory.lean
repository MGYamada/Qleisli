import Qleisli.RuntimeCallTraceErasure
import Qleisli.RuntimeCallTraceAllocation
import Qleisli.RuntimeNamedThreePackedInstrument
import Qleisli.RuntimeLiteralHistory

/-! Ordered histories of an original named call in its two Raw frames.
A local history is indexed by the physical spectator row, so the relation
retains correlations and does not require a tensor product input.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel
open Semantics.Finite (Dependency gather)
open Semantics.Raw (Port)
open Semantics.RawTrace (Interface axes take)
open RuntimeCallTraceFrames (Partition WireOrder removed allocated erasure)
open Qleisli.Semantics.ObservingAction (History run erase)
open Qleisli.RuntimeLiteralHistory (run_single)
open Qleisli.RuntimeNamedThreePackedInstrument (pureHistory run_pure)
open Qleisli.RuntimeOriginalObservation (erasure_step_histories)

def project (parent : Interface) (wires : List Nat) (row : Nat) : Nat :=
  gather row (axes parent wires)

structure Agrees (parent child : Interface) (spectators : List Port)
    (actual : History) (localHistory : Nat → History) : Prop where
  values : ∀ high, actual.values = (localHistory high).values
  hidden : ∀ high, actual.hidden = (localHistory high).hidden
  operator : ∀ row col, row < 2^parent.frame.length →
    actual.operator row col =
      (localHistory (project parent (WireOrder spectators) row)).operator (project parent child.frame row) col

structure Results (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (parent child : Interface) (spectators : List Port)
    (parentEvents childEvents : List Semantics.Observation.Event)
    (actual : History) (localHistory : Nat → History)
    (parents : List History) (children : List (Nat → History)) : Prop where
  parentRun : run dependencies parentDepth parentEvents actual = some parents
  childRun : ∀ high, run dependencies childDepth childEvents (localHistory high) =
    some (children.map (fun history => history high))
  paired : List.Forall₂ (Agrees parent child spectators) parents children

private theorem erase_congr (bits : Nat) (indices : List Nat) (outcome row : Nat)
    {left right : Nat → ℂ} (agrees : RawFiniteRows.OnRows bits left right) :
    erase bits indices outcome left row = erase bits indices outcome right row := by
  unfold erase
  apply Qleisli.Exact.sum_map_congr
  intro input member
  rw [agrees input (List.mem_range.mp member)]

private theorem map_pair {A B : Type} {rel : A → B → Prop}
    {indices : List Nat} (parent : Nat → A) (child : Nat → B)
    (agrees : ∀ outcome ∈ indices, rel (parent outcome) (child outcome)) :
    List.Forall₂ rel (indices.map parent) (indices.map child) := by
  induction indices with
  | nil => exact .nil
  | cons outcome rest ih =>
    exact .cons (agrees outcome List.mem_cons_self)
      (ih (fun value member => agrees value (List.mem_cons_of_mem _ member)))

/-- Each original erasure outcome appears once in its literal order. A
measurement appends its original SSA ID and discard leaves the visible
values alone. Both extend the same hidden history. -/
theorem erase_histories (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (parent child : Raw.State) (spectators : List Port)
    (partition : Partition parent.reference child.reference spectators)
    (parentValid : Raw.stateValid parent = true) (childValid : Raw.stateValid child = true)
    {token : Nat} {port : Port} {childTaken : Interface}
    (childTake : take child.reference token = some (port,childTaken))
    (measured : Option Nat) (actual : History) (localHistory : Nat → History)
    (agrees : Agrees parent.reference child.reference spectators actual localHistory) :
    ∃ parentTaken parents children,
      take parent.reference token = some (port,parentTaken) ∧
      Partition (removed parent.reference parentTaken port) (removed child.reference childTaken port) spectators ∧
      Results dependencies (parentDepth+1) (childDepth+1)
        (removed parent.reference parentTaken port) (removed child.reference childTaken port) spectators
        [erasure parent.reference port measured] [erasure child.reference port measured]
        actual localHistory parents children := by
  obtain ⟨parentTaken,parentTake,after,_⟩ :=
    RuntimeCallTraceFrames.original_take parent child spectators partition parentValid childValid childTake
  let parentAxes := axes parent.reference port.wires
  let childAxes := axes child.reference port.wires
  let outcomes := List.range (2^port.wires.length)
  obtain ⟨p,pStep,pFacts⟩ := erasure_step_histories dependencies parent.frame.length parentAxes measured
    (run dependencies parentDepth) actual
  have each (high : Nat) := erasure_step_histories dependencies child.frame.length childAxes measured
    (run dependencies childDepth) (localHistory high)
  choose c cStep cFacts using each
  refine ⟨parentTaken,outcomes.map p,outcomes.map (fun outcome high => c high outcome),parentTake,after,?_⟩
  refine ⟨?_,?_,map_pair _ _ ?_⟩
  · rw [run_single]
    simpa only [erasure,parentAxes,axes,List.length_map,outcomes] using pStep
  · intro high
    rw [run_single,List.map_map]
    simpa only [erasure,childAxes,axes,List.length_map,outcomes,Function.comp_def] using cStep high
  · intro outcome member
    refine ⟨?_,?_,?_⟩
    · intro high
      rw [(pFacts outcome).1,(cFacts high outcome).1,agrees.values high]
    · intro high
      rw [(pFacts outcome).2.1,(cFacts high outcome).2.1,agrees.hidden high]
    · intro row col bound
      let pAfter := removed parent.reference parentTaken port
      let cAfter := removed child.reference childTaken port
      let high := project pAfter (WireOrder spectators) row
      change (p outcome).operator row col = (c high outcome).operator (project pAfter cAfter.frame row) col
      rw [(pFacts outcome).2.2,(cFacts high outcome).2.2]
      let joint := fun low high => (localHistory high).operator low col
      exact (erase_congr parent.frame.length parentAxes outcome row (fun input bounded =>
        agrees.operator input col bounded)).trans
        (RuntimeCallTraceErasure.erase_correlated parent child spectators partition parentValid childValid childTake
          joint outcome row (List.mem_range.mp member) bound)

private theorem allocation_history (dependencies : List Dependency)
    (parent child : Interface) (spectators : List Port)
    (partition : Partition parent child spectators) (output wire : Nat) (fresh : wire ∉ parent.frame)
    {actual : History} {localHistory : Nat → History}
    (agrees : Agrees parent child spectators actual localHistory) :
    Agrees (allocated parent output wire) (allocated child output wire) spectators
      (pureHistory dependencies [.init0 parent.frame.length] actual)
      (fun high => pureHistory dependencies [.init0 child.frame.length] (localHistory high)) := by
  refine ⟨agrees.values,agrees.hidden,?_⟩
  intro row col bound
  let parentEvent := Semantics.Raw.Event.init0 parent.frame.length
  let childEvent := Semantics.Raw.Event.init0 child.frame.length
  let event := Qleisli.Semantics.RawAction.event dependencies
  let joint := fun low high => (localHistory high).operator low col
  let high := project (allocated parent output wire) (WireOrder spectators) row
  change event parentEvent (fun input => actual.operator input col) row =
    event childEvent (fun input => joint input high) (project (allocated parent output wire) (child.frame++[wire]) row)
  have represented : RawFiniteRows.OnRows parent.frame.length (fun input => actual.operator input col)
      (fun input => joint (project parent child.frame input) (project parent (WireOrder spectators) input)) :=
    fun input inside => agrees.operator input col inside
  have congruent := (RawFiniteRows.BoundedEvent.init0 parent.frame.length).congr dependencies _ _ represented
  have grown : row < 2^(parent.frame.length+1) := by
    simpa only [allocated,List.length_append,List.length_singleton] using bound
  exact (congruent row grown).trans
    (RuntimeCallTraceAllocation.allocation_correlated parent child spectators partition output wire fresh
      dependencies joint row bound)

/-- Apply the same original zero initialization to one pair of histories. -/
theorem allocation_results (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (parent child : Interface) (spectators : List Port)
    (partition : Partition parent child spectators) (output wire : Nat) (fresh : wire ∉ parent.frame)
    {actual : History} {localHistory : Nat → History}
    (agrees : Agrees parent child spectators actual localHistory) :
    Results dependencies (parentDepth+1) (childDepth+1) (allocated parent output wire) (allocated child output wire) spectators
      [.pure (.init0 parent.frame.length)] [.pure (.init0 child.frame.length)] actual localHistory
      [pureHistory dependencies [.init0 parent.frame.length] actual]
      [fun high => pureHistory dependencies [.init0 child.frame.length] (localHistory high)] :=
  ⟨run_pure dependencies parentDepth [.init0 parent.frame.length] actual,
    fun high => run_pure dependencies childDepth [.init0 child.frame.length] (localHistory high),
    .cons (allocation_history dependencies parent child spectators partition output wire fresh agrees) .nil⟩

#print axioms erase_histories
#print axioms allocation_results
end Qleisli.RuntimeCallHistory
