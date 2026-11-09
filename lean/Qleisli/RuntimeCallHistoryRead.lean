import Qleisli.RuntimeCallHistoryComposition

/-! Bind ordered call histories to the two actual native observation reads.
The original checked result interfaces and issued SSA IDs are retained.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel
open Semantics.Finite (Dependency)
open Semantics.Observation (Op Event readOps remaining)
open Semantics.RawTrace (Interface take)
open Semantics.Raw (Port)
open Raw.Observation (checkStep checkOps)
open Raw.ObservationAgreement (readStep Reader)
open RuntimeCallTraceFrames (Partition removed allocated erasure)
open Qleisli.RuntimeObservingPrefix (Issued checkStep_frames_valid checkStep_reference_with_writes)
open Qleisli.RuntimeObservingWrites (WritesWithin)
open Qleisli.Semantics.ObservingAction (History)

structure CheckedResults (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (parent child parentAfter childAfter : Raw.Observation.State) (spectators : List Port) (op : Op)
    (actual : History) (localHistory : Nat → History)
    (parents : List History) (children : List (Nat → History)) : Prop where
  partition : Partition parentAfter.quantum.reference childAfter.quantum.reference spectators
  traces : ∃ parentEvents childEvents,
    readStep (readOps parentDepth) parent.quantum.reference op = some (parentAfter.quantum.reference,parentEvents) ∧
    readStep (readOps childDepth) child.quantum.reference op = some (childAfter.quantum.reference,childEvents) ∧
    WritesWithin parentEvents (Issued parentAfter) ∧ WritesWithin childEvents (Issued childAfter) ∧
    Results dependencies (parentDepth+1) (childDepth+1) parentAfter.quantum.reference childAfter.quantum.reference spectators
      parentEvents childEvents actual localHistory parents children

def eraseOp (token : Nat) : Option Nat → Op
  | none => .discard token
  | some id => .measure token id

private theorem erase_read (reader : Reader) (state : Interface) (token : Nat) (measured : Option Nat) :
    readStep reader state (eraseOp token measured) =
      (take state token).bind (fun (port,taken) =>
        some (removed state taken port,[erasure state port measured])) := by
  cases measured <;> rfl

/-- Successful measure/discard reads determine the exact common outcomes
and both native SSA-write bounds. -/
theorem checked_erasure (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (parent child parentAfter childAfter : Raw.Observation.State) (spectators : List Port)
    (partition : Partition parent.quantum.reference child.quantum.reference spectators)
    (token : Nat) (measured : Option Nat) {parentWork parentLeft childWork childLeft : Nat}
    (parentRead : (checkStep dependencies (checkOps dependencies parentDepth) parent (eraseOp token measured)).run
      parentWork = (.ok parentAfter,parentLeft))
    (childRead : (checkStep dependencies (checkOps dependencies childDepth) child (eraseOp token measured)).run
      childWork = (.ok childAfter,childLeft))
    (actual : History) (localHistory : Nat → History)
    (agrees : Agrees parent.quantum.reference child.quantum.reference spectators actual localHistory) :
    ∃ parents children, CheckedResults dependencies parentDepth childDepth parent child parentAfter childAfter spectators
      (eraseOp token measured) actual localHistory parents children := by
  obtain ⟨_,pEvents,pRead,pWrites⟩ := checkStep_reference_with_writes _ _ _ _ _ _ _ parentRead
  obtain ⟨_,cEvents,cRead,cWrites⟩ := checkStep_reference_with_writes _ _ _ _ _ _ _ childRead
  have cTrace := cRead
  rw [erase_read] at cTrace
  obtain ⟨⟨port,cTaken⟩,cTake,cDone⟩ := Option.bind_eq_some_iff.mp cTrace
  obtain ⟨pTaken,parents,children,pTake,after,results⟩ := erase_histories dependencies parentDepth childDepth
    parent.quantum child.quantum spectators partition (checkStep_frames_valid parentRead).1
    (checkStep_frames_valid childRead).1 cTake measured actual localHistory agrees
  have pTrace := pRead
  rw [erase_read,pTake] at pTrace
  obtain ⟨pState,pEvent⟩ := Prod.mk.inj (Option.some.inj pTrace)
  obtain ⟨cState,cEvent⟩ := Prod.mk.inj (Option.some.inj cDone)
  refine ⟨parents,children,⟨?_,pEvents,cEvents,pRead,cRead,pWrites,cWrites,?_⟩⟩
  · rw [← pState,← cState]
    exact after
  · rw [← pState,← cState,← pEvent,← cEvent]
    exact results

private theorem reset_read (reader : Reader) (state : Interface) (token output wire : Nat) :
    readStep reader state (.reset token output wire) =
      (take state token).bind (fun (port,taken) =>
        let after := removed state taken port
        some (allocated after output wire,[erasure state port none,.pure (.init0 after.frame.length)])) := rfl

/-- The checked original reset keeps every erasure history and allocates the
literal fresh zero wire in both frames. Freshness follows from the exact
native post-frame, and the result retains both issued-value bounds. -/
theorem checked_reset (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (parent child parentAfter childAfter : Raw.Observation.State) (spectators : List Port)
    (partition : Partition parent.quantum.reference child.quantum.reference spectators)
    (token output wire : Nat) {parentWork parentLeft childWork childLeft : Nat}
    (parentRead : (checkStep dependencies (checkOps dependencies parentDepth) parent (.reset token output wire)).run
      parentWork = (.ok parentAfter,parentLeft))
    (childRead : (checkStep dependencies (checkOps dependencies childDepth) child (.reset token output wire)).run
      childWork = (.ok childAfter,childLeft))
    (actual : History) (localHistory : Nat → History)
    (agrees : Agrees parent.quantum.reference child.quantum.reference spectators actual localHistory) :
    ∃ parents children, CheckedResults dependencies parentDepth childDepth parent child parentAfter childAfter spectators
      (.reset token output wire) actual localHistory parents children := by
  obtain ⟨_,pEvents,pRead,pWrites⟩ := checkStep_reference_with_writes _ _ _ _ _ _ _ parentRead
  obtain ⟨_,cEvents,cRead,cWrites⟩ := checkStep_reference_with_writes _ _ _ _ _ _ _ childRead
  have parentValid := checkStep_frames_valid parentRead
  have childValid := checkStep_frames_valid childRead
  have cTrace := cRead
  rw [reset_read] at cTrace
  obtain ⟨⟨port,cTaken⟩,cTake,cDone⟩ := Option.bind_eq_some_iff.mp cTrace
  obtain ⟨pTaken,pTake,_,_⟩ :=
    RuntimeCallTraceFrames.original_take parent.quantum child.quantum spectators partition
      parentValid.1 childValid.1 cTake
  have pTrace := pRead
  rw [reset_read,pTake] at pTrace
  obtain ⟨pState,pEvent⟩ := Prod.mk.inj (Option.some.inj pTrace)
  obtain ⟨cState,cEvent⟩ := Prod.mk.inj (Option.some.inj cDone)
  have grown : (remaining parent.quantum.reference port.wires ++ [wire]).Nodup := by
    change (allocated (removed parent.quantum.reference pTaken port) output wire).frame.Nodup
    rw [pState]
    exact (Raw.Ownership.valid _ parentValid.2).frame
  have fresh : wire ∉ remaining parent.quantum.reference port.wires := fun held =>
    (List.nodup_append.mp grown).2.2 wire held wire List.mem_cons_self rfl
  obtain ⟨taken,parents,children,takeRead,after,results⟩ := reset_histories dependencies parentDepth childDepth
    parent.quantum child.quantum spectators partition parentValid.1 childValid.1 cTake
    output wire fresh actual localHistory agrees
  have equal : taken = pTaken := congrArg Prod.snd (Option.some.inj (takeRead.symm.trans pTake))
  subst taken
  refine ⟨parents,children,⟨?_,pEvents,cEvents,pRead,cRead,pWrites,cWrites,?_⟩⟩
  · rw [← pState,← cState]
    exact after
  · rw [← pState,← cState,← pEvent,← cEvent]
    exact results

#print axioms checked_erasure
#print axioms checked_reset
end Qleisli.RuntimeCallHistory
