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
open Qleisli.RuntimeObservingComposition (runHistories runHistories_append runHistories_singleton)

private theorem suffix_families {dependencies : List Dependency} {fuel : Nat}
    {middleParent middleChild finalParent finalChild : Interface} {spectators : List Port}
    {parentEvents childEvents : List Event} {parents : List History} {children : List (Nat → History)}
    (paired : List.Forall₂ (Agrees middleParent middleChild spectators) parents children)
    (next : ∀ actual localHistory, Agrees middleParent middleChild spectators actual localHistory →
      ∃ finalParents finalChildren,
        Results dependencies fuel finalParent finalChild spectators parentEvents childEvents
          actual localHistory finalParents finalChildren) :
    ∃ finalParents finalChildren,
      runHistories dependencies fuel parentEvents parents = some finalParents ∧
      (∀ high, runHistories dependencies fuel childEvents (children.map (fun history => history high)) =
        some (finalChildren.map (fun history => history high))) ∧
      List.Forall₂ (Agrees finalParent finalChild spectators) finalParents finalChildren := by
  induction paired with
  | nil => exact ⟨[],[],rfl,fun _ => rfl,.nil⟩
  | @cons actual localHistory parents children agrees _ ih =>
    obtain ⟨firstParents,firstChildren,first⟩ := next actual localHistory agrees
    obtain ⟨laterParents,laterChildren,parentTail,childTail,tail⟩ := ih
    refine ⟨firstParents++laterParents,firstChildren++laterChildren,?_,?_,List.rel_append first.paired tail⟩
    · unfold runHistories at parentTail ⊢
      cases actualTail : parents.mapM (run dependencies fuel parentEvents) with
      | none => simp [actualTail] at parentTail
      | some groups =>
        simp [actualTail] at parentTail
        simp [List.mapM_cons,first.parentRun,actualTail,parentTail]
    · intro high
      have later := childTail high
      unfold runHistories at later ⊢
      cases actualTail : (children.map (fun history => history high)).mapM
          (run dependencies fuel childEvents) with
      | none => simp [actualTail] at later
      | some groups =>
        simp [actualTail] at later
        simp [List.mapM_cons,first.childRun high,actualTail,later]

/-- Append the exact next event chunks on both sides. The suffix is run once
per history, and flattening preserves the order and multiplicity of results. -/
theorem Results.append {dependencies : List Dependency} {fuel : Nat}
    {middleParent middleChild finalParent finalChild : Interface} {spectators : List Port}
    {parentPrefix childPrefix parentSuffix childSuffix : List Event}
    {actual : History} {localHistory : Nat → History} {parents : List History} {children : List (Nat → History)}
    (first : Results dependencies (fuel+1) middleParent middleChild spectators parentPrefix childPrefix
      actual localHistory parents children)
    (next : ∀ p c, Agrees middleParent middleChild spectators p c →
      ∃ finalParents finalChildren,
        Results dependencies (fuel+1) finalParent finalChild spectators parentSuffix childSuffix
          p c finalParents finalChildren) :
    ∃ finalParents finalChildren,
      Results dependencies (fuel+1) finalParent finalChild spectators (parentPrefix++parentSuffix)
        (childPrefix++childSuffix) actual localHistory finalParents finalChildren := by
  obtain ⟨finalParents,finalChildren,parentRun,childRun,paired⟩ := suffix_families first.paired next
  refine ⟨finalParents,finalChildren,?_,?_,paired⟩
  · rw [← runHistories_singleton,runHistories_append,runHistories_singleton,first.parentRun]
    exact parentRun
  · intro high
    rw [← runHistories_singleton,runHistories_append,runHistories_singleton,first.childRun high]
    exact childRun high

/-- Reset reads the same erasure and zero allocation as the original reader.
Every erased outcome remains in the result family, including zero maps. -/
theorem reset_histories (dependencies : List Dependency) (fuel : Nat)
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
      Results dependencies (fuel+1) (allocated p output wire) (allocated c output wire) spectators
        [erasure parent.reference port none,.pure (.init0 p.frame.length)]
        [erasure child.reference port none,.pure (.init0 c.frame.length)] actual localHistory parents children := by
  obtain ⟨parentTaken,parents,children,parentTake,after,erased⟩ :=
    erase_histories dependencies fuel parent child spectators partition parentValid childValid childTake none
      actual localHistory agrees
  let p := removed parent.reference parentTaken port
  let c := removed child.reference childTaken port
  obtain ⟨finalParents,finalChildren,final⟩ := erased.append
    (fun pHistory cHistory paired =>
      ⟨_,_,allocation_results dependencies fuel p c spectators after output wire fresh paired⟩)
  exact ⟨parentTaken,finalParents,finalChildren,parentTake,after.allocate output wire,final⟩

#print axioms Results.append
#print axioms reset_histories
end Qleisli.RuntimeCallHistory
