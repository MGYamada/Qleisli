import Qleisli.RuntimeCallBranchGeometry

/-! Transfer the actual chosen arm, its literal wire permutation and the
simultaneous classical phi merge. Each keeps every ordered history.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel
open Semantics.Finite (Dependency)
open Semantics.RawTrace (Interface)
open Semantics.Observation (Event ClassicalPhi)
open Qleisli.Semantics.ObservingAction (History run merge)
open Qleisli.RuntimeLiteralHistory (run_single)
open Qleisli.RuntimeNamedThreePackedInstrument (pureHistory run_append_event run_pure)
open RuntimeCallTraceFrames (Partition)

theorem Partition.same_frame (frame : Interface) : Partition frame frame [] :=
  ⟨by simp,by simp⟩

/-- Apply the literal arm finish to both actual result lists. The history
relation has already supplied the exact source rows before the permutation. -/
theorem Segment.finish_arm {dependencies : List Dependency} {parentDepth childDepth : Nat}
    {parent child pArm cArm final : Interface} {pEvents cEvents : List Event}
    (arm : Segment dependencies parentDepth childDepth parent child pArm cArm [] pEvents cEvents)
    (pFinish cFinish : Semantics.Raw.Event)
    (permutes : ∀ actual localHistory, Agrees pArm cArm [] actual localHistory →
      Agrees final final [] (pureHistory dependencies [pFinish] actual)
        (fun high => pureHistory dependencies [cFinish] (localHistory high))) :
    Segment dependencies parentDepth childDepth parent child final final []
      (pEvents++[.pure pFinish]) (cEvents++[.pure cFinish]) := by
  refine ⟨Partition.same_frame final,?_⟩
  intro actual localHistory agrees parents executed
  have performed := executed
  rw [run_append_event] at performed
  obtain ⟨before,firstRan,_⟩ := Option.bind_eq_some_iff.mp performed
  obtain ⟨_,initialRun⟩ := arm.transport actual localHistory agrees before firstRan
  refine initialRun.append_of_run executed ?_
  intro p c same produced ran
  have pRun := run_pure dependencies parentDepth [pFinish] p
  have cRun (high : Nat) := run_pure dependencies childDepth [cFinish] (c high)
  have equal : produced = [pureHistory dependencies [pFinish] p] := Option.some.inj (ran.symm.trans pRun)
  subst produced
  exact ⟨[fun high => pureHistory dependencies [cFinish] (c high)],
    pRun,cRun,.cons (permutes p c same) .nil⟩

/-- Equal incoming SSA selects the same arm. Both actual ordered arm
results then undergo the same original simultaneous classical phi merge. -/
theorem branch_from_arms {dependencies : List Dependency} {parentDepth childDepth : Nat}
    {parent child final : Interface} {pThen pElse cThen cElse : List Event}
    (condition : Nat) (phis : List ClassicalPhi)
    (yes : Segment dependencies parentDepth childDepth parent child final final [] pThen cThen)
    (no : Segment dependencies parentDepth childDepth parent child final final [] pElse cElse) :
    Segment dependencies (parentDepth+1) (childDepth+1) parent child final final []
      [.branch condition pThen pElse phis] [.branch condition cThen cElse phis] := by
  refine ⟨Partition.same_frame final,?_⟩
  intro actual localHistory agrees parents executed
  have performed := executed
  rw [run_single] at performed
  simp only [Qleisli.Semantics.ObservingAction.step] at performed
  obtain ⟨choice,chosen,suffix⟩ := Option.bind_eq_some_iff.mp performed
  obtain ⟨rawParents,armRan,merged⟩ := Option.bind_eq_some_iff.mp suffix
  have arm : Segment dependencies parentDepth childDepth parent child final final []
      (if choice then pThen else pElse) (if choice then cThen else cElse) := by
    cases choice
    · exact no
    · exact yes
  obtain ⟨rawChildren,paired⟩ := arm.transport actual localHistory agrees rawParents armRan
  obtain ⟨children,childMerge,relation⟩ := merge_family choice phis paired.paired merged
  refine ⟨children,executed,?_,relation⟩
  intro high
  have childChoice : Qleisli.Semantics.RawInstrument.value (localHistory high).values condition = some choice := by
    rw [← agrees.values high]
    exact chosen
  rw [run_single]
  simp only [Qleisli.Semantics.ObservingAction.step,childChoice,bind,Option.bind,paired.childRun high]
  exact childMerge high

#print axioms Segment.finish_arm
#print axioms branch_from_arms
end Qleisli.RuntimeCallHistory
