import Qleisli.RuntimeCallHistory
import Qleisli.RuntimeObservingComposition

/-! Sequence the actual parent and child observing runs in original event
order. Every incoming pair contributes its complete result family in order.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel
open RuntimeCallTraceFrames (Partition removed allocated erasure)
open QleisliKernel.Semantics.Finite (Dependency)
open QleisliKernel.Semantics.Observation (Event)
open QleisliKernel.Semantics.Raw (Port)
open QleisliKernel.Semantics.RawTrace (Interface take)
open Qleisli.Semantics.ObservingAction (History run)
open Qleisli.RuntimeNamedThreePackedInstrument (run_append_event advance_pure pureHistory)
open Qleisli.RuntimeObservingComposition (runHistories runHistories_append runHistories_singleton)

private theorem runHistories_cons (dependencies : List Dependency) (depth : Nat)
    (events : List Event) (head : History) (tail : List History) :
    runHistories dependencies depth events (head::tail) = (do
      let first ← run dependencies depth events head
      let later ← runHistories dependencies depth events tail
      pure (first++later)) := by
  simp only [runHistories,List.mapM_cons,bind_assoc,pure_bind,List.flatten_cons]

private theorem suffix_from_run {dependencies : List Dependency} {parentDepth childDepth : Nat}
    {middleParent middleChild finalParent finalChild : Interface} {spectators : List Port}
    {parentEvents childEvents : List Event} {parents : List History} {children : List (Nat → History)}
    (paired : List.Forall₂ (Agrees middleParent middleChild spectators) parents children)
    (next : ∀ actual localHistory, Agrees middleParent middleChild spectators actual localHistory →
      ∀ produced, run dependencies parentDepth parentEvents actual = some produced →
      ∃ finalChildren,
        Results dependencies parentDepth childDepth finalParent finalChild spectators parentEvents childEvents
          actual localHistory produced finalChildren)
    {finalParents : List History} (executed : runHistories dependencies parentDepth parentEvents parents = some finalParents) :
    ∃ finalChildren,
      (∀ high, runHistories dependencies childDepth childEvents (children.map (fun history => history high)) =
        some (finalChildren.map (fun history => history high))) ∧
      List.Forall₂ (Agrees finalParent finalChild spectators) finalParents finalChildren := by
  induction paired generalizing finalParents with
  | nil =>
    have same : [] = finalParents := Option.some.inj executed
    subst finalParents
    exact ⟨[],fun _ => rfl,.nil⟩
  | @cons actual localHistory parents children agrees _ ih =>
    rw [runHistories_cons] at executed
    obtain ⟨firstParents,firstRan,rest⟩ := Option.bind_eq_some_iff.mp executed
    obtain ⟨laterParents,laterRan,done⟩ := Option.bind_eq_some_iff.mp rest
    have same : firstParents++laterParents = finalParents := Option.some.inj done
    subst finalParents
    obtain ⟨firstChildren,first⟩ := next actual localHistory agrees firstParents firstRan
    obtain ⟨laterChildren,later,matched⟩ := ih laterRan
    refine ⟨firstChildren++laterChildren,?_,List.rel_append first.paired matched⟩
    intro high
    rw [List.map_cons,runHistories_cons,first.childRun high,later high,List.map_append]
    rfl

/-- Sequence a paired prefix with the suffix of an actual successful parent
execution. A local law only needs to relate histories that actually run. -/
theorem Results.append_of_run {dependencies : List Dependency} {parentDepth childDepth : Nat}
    {middleParent middleChild finalParent finalChild : Interface} {spectators : List Port}
    {parentPrefix childPrefix parentSuffix childSuffix : List Event}
    {actual : History} {localHistory : Nat → History} {parents finalParents : List History}
    {children : List (Nat → History)}
    (first : Results dependencies (parentDepth+1) (childDepth+1) middleParent middleChild spectators
      parentPrefix childPrefix actual localHistory parents children)
    (executed : run dependencies (parentDepth+1) (parentPrefix++parentSuffix) actual = some finalParents)
    (next : ∀ p c, Agrees middleParent middleChild spectators p c →
      ∀ produced, run dependencies (parentDepth+1) parentSuffix p = some produced →
      ∃ finalChildren, Results dependencies (parentDepth+1) (childDepth+1) finalParent finalChild spectators
        parentSuffix childSuffix p c produced finalChildren) :
    ∃ finalChildren, Results dependencies (parentDepth+1) (childDepth+1) finalParent finalChild spectators
      (parentPrefix++parentSuffix) (childPrefix++childSuffix) actual localHistory finalParents finalChildren := by
  have suffix := executed
  rw [← runHistories_singleton,runHistories_append,runHistories_singleton,first.parentRun] at suffix
  obtain ⟨finalChildren,childRun,paired⟩ := suffix_from_run first.paired next suffix
  refine ⟨finalChildren,executed,?_,paired⟩
  intro high
  rw [← runHistories_singleton,runHistories_append,runHistories_singleton,first.childRun high]
  exact childRun high

/-- Reset reads the same erasure and zero allocation as the original reader.
Every erased outcome remains in the result family, including zero maps. -/
theorem reset_histories (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (parent child : Raw.State) (spectators : List Port)
    (partition : Partition parent.reference child.reference spectators)
    (parentValid : Raw.stateValid parent = true) (childValid : Raw.stateValid child = true)
    {token : Nat} {port : Port} {childTaken : Interface}
    (childTake : take child.reference token = some (port,childTaken))
    (output wire : Nat) (fresh : wire ∉ Semantics.Observation.remaining parent.reference port.wires)
    (actual : History) (localHistory : Nat → History)
    (agrees : Agrees parent.reference child.reference spectators actual localHistory) :
    ∃ parentTaken parents children,
      let p := removed parent.reference parentTaken port
      let c := removed child.reference childTaken port
      take parent.reference token = some (port,parentTaken) ∧
      Partition (allocated p output wire) (allocated c output wire) spectators ∧
      Results dependencies (parentDepth+1) (childDepth+1) (allocated p output wire) (allocated c output wire) spectators
        [erasure parent.reference port none,.pure (.init0 p.frame.length)]
        [erasure child.reference port none,.pure (.init0 c.frame.length)] actual localHistory parents children := by
  obtain ⟨parentTaken,parents,children,parentTake,after,erased⟩ :=
    erase_histories dependencies parentDepth childDepth parent child spectators partition parentValid childValid childTake none
      actual localHistory agrees
  let p := removed parent.reference parentTaken port
  let c := removed child.reference childTaken port
  let finalParents := parents.map (pureHistory dependencies [.init0 p.frame.length])
  have performed : run dependencies (parentDepth+1)
      ([erasure parent.reference port none]++[.pure (.init0 p.frame.length)]) actual = some finalParents := by
    rw [run_append_event,erased.parentRun]
    exact advance_pure _ _ _ _
  obtain ⟨finalChildren,final⟩ := erased.append_of_run performed
    (fun pHistory cHistory paired produced ran => by
      have result := allocation_results dependencies parentDepth childDepth p c spectators after output wire fresh paired
      have same := Option.some.inj (ran.symm.trans result.parentRun)
      subst produced
      exact ⟨_,result⟩)
  exact ⟨parentTaken,finalParents,finalChildren,parentTake,after.allocate output wire,final⟩

#print axioms Results.append_of_run
#print axioms reset_histories
end Qleisli.RuntimeCallHistory
