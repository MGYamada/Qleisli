import Qleisli.RuntimeCallBranchAction
import Qleisli.RuntimeRoutedPhiGeometry

/-! Ordered parent and projected child histories at one original branch.
An actual spectator phi changes the output port while both runs use the
same original ordinary condition and simultaneous classical phis.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel
open Semantics.Finite (Dependency)
open Semantics.Raw (Port)
open Semantics.RawTrace (Interface)
open Semantics.Observation (Event ClassicalPhi)
open Qleisli.Semantics.ObservingAction (History run)
open Qleisli.RuntimeLiteralHistory (run_single)
open Qleisli.RuntimeNamedThreePackedInstrument (pureHistory run_append_event advance_pure)

abbrev RoutedSegment (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (parent child parentAfter childAfter : Interface) (beforeSpectators afterSpectators : List Port)
    (parentEvents childEvents : List Event) : Prop :=
  ∀ actual localHistory, Agrees parent child beforeSpectators actual localHistory →
    ∀ parents, run dependencies (parentDepth+1) parentEvents actual = some parents →
    ∃ children, Results dependencies (parentDepth+1) (childDepth+1) parentAfter childAfter afterSpectators
      parentEvents childEvents actual localHistory parents children

theorem Segment.finish_routed_arm {dependencies : List Dependency} {parentDepth childDepth : Nat}
    {parent child pArm cArm finalParent finalChild : Interface} {pEvents cEvents : List Event}
    {beforeSpectators afterSpectators : List Port}
    (arm : Segment dependencies parentDepth childDepth parent child pArm cArm beforeSpectators pEvents cEvents)
    (pFinish cFinish : Semantics.Raw.Event)
    (permutes : ∀ actual localHistory, Agrees pArm cArm beforeSpectators actual localHistory →
      Agrees finalParent finalChild afterSpectators (pureHistory dependencies [pFinish] actual)
        (fun high => pureHistory dependencies [cFinish] (localHistory high))) :
    RoutedSegment dependencies parentDepth childDepth parent child finalParent finalChild beforeSpectators afterSpectators
      (pEvents++[.pure pFinish]) (cEvents++[.pure cFinish]) := by
  intro actual localHistory agrees parents executed
  have performed := executed
  rw [run_append_event] at performed
  obtain ⟨before,firstRan,finished⟩ := Option.bind_eq_some_iff.mp performed
  obtain ⟨children,initialRun⟩ := arm.transport actual localHistory agrees before firstRan
  rw [advance_pure] at finished
  have actualOrder := Option.some.inj finished
  subst parents
  let childFinish := fun history : Nat → History => fun high => pureHistory dependencies [cFinish] (history high)
  refine ⟨children.map childFinish,executed,?_,?_⟩
  · intro high
    rw [run_append_event,initialRun.childRun high,List.map_map]
    simp only [bind,Option.bind]
    rw [advance_pure,List.map_map]
    rfl
  · rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff]
    exact initialRun.paired.imp permutes

theorem branch_from_routed_arms {dependencies : List Dependency} {parentDepth childDepth : Nat}
    {parent child finalParent finalChild : Interface} {pThen pElse cThen cElse : List Event}
    {beforeSpectators afterSpectators : List Port} (condition : Nat) (phis : List ClassicalPhi)
    (yes : RoutedSegment dependencies parentDepth childDepth parent child finalParent finalChild
      beforeSpectators afterSpectators pThen cThen)
    (no : RoutedSegment dependencies parentDepth childDepth parent child finalParent finalChild
      beforeSpectators afterSpectators pElse cElse) :
    RoutedSegment dependencies (parentDepth+1) (childDepth+1) parent child finalParent finalChild
      beforeSpectators afterSpectators [.branch condition pThen pElse phis] [.branch condition cThen cElse phis] := by
  intro actual localHistory agrees parents executed
  have performed := executed
  rw [run_single] at performed
  simp only [Qleisli.Semantics.ObservingAction.step] at performed
  obtain ⟨choice,chosen,suffix⟩ := Option.bind_eq_some_iff.mp performed
  obtain ⟨rawParents,armRan,merged⟩ := Option.bind_eq_some_iff.mp suffix
  have arm : RoutedSegment dependencies parentDepth childDepth parent child finalParent finalChild
      beforeSpectators afterSpectators (if choice then pThen else pElse) (if choice then cThen else cElse) := by
    cases choice
    · exact no
    · exact yes
  obtain ⟨_,paired⟩ := arm actual localHistory agrees rawParents armRan
  obtain ⟨children,childMerge,relation⟩ := merge_family choice phis paired.paired merged
  refine ⟨children,executed,?_,relation⟩
  intro high
  have childChoice : Qleisli.Semantics.RawInstrument.value (localHistory high).values condition = some choice := by
    rw [← agrees.values high]
    exact chosen
  rw [run_single]
  simp only [Qleisli.Semantics.ObservingAction.step,childChoice,bind,Option.bind,paired.childRun high]
  exact childMerge high

#print axioms Segment.finish_routed_arm
#print axioms branch_from_routed_arms
end Qleisli.RuntimeCallHistory
