import Qleisli.RuntimeObservingPrefix
import Qleisli.Semantics.ObservingAction
import QleisliKernel.Qirf.RuntimeBranchAction

/-! The actual conditional and both independently read arms, including their
literal return permutations. The retained source condition determines which
arm the observing interpreter takes on a represented history.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeOriginalBranch
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Observation (Event readOps)
open Qleisli.Semantics.ObservingAction (History)

def armFinish (state : Semantics.RawTrace.Interface) (quantum : List Semantics.Observation.QuantumPhi)
    (choice : Bool) : Event :=
  .pure (.reorder state.frame.length (Semantics.RawTrace.axes state
    (Semantics.Observation.phiWires state quantum choice)))

def branchEvent {dependencies program block offset} (actual : @RuntimeInterval.Branch dependencies program block offset)
    (left right : List Event) : Event :=
  .branch actual.condition (left++[armFinish actual.thenState.quantum.reference actual.quantum true])
    (right++[armFinish actual.elseState.quantum.reference actual.quantum false]) actual.classical

structure Trace {dependencies program block offset}
    (actual : @RuntimeInterval.Branch dependencies program block offset) where
  left : List Event
  right : List Event
  leftRead : readOps actual.childFuel actual.interval.before.quantum.reference actual.thenOps =
    some (actual.thenState.quantum.reference,left)
  rightRead : readOps actual.childFuel actual.interval.before.quantum.reference actual.elseOps =
    some (actual.elseState.quantum.reference,right)
  parentRead : readOps block.fuel actual.interval.before.quantum.reference ((block.operations.drop offset).take 1) =
    some (actual.interval.after.quantum.reference,[branchEvent actual left right])

/-- The original branch instruction fixes the exact event and both arm traces. -/
theorem original_branch_events {dependencies program block offset}
    (actual : @RuntimeInterval.Branch dependencies program block offset) : Nonempty (Trace actual) := by
  obtain ⟨work,left,ran⟩ := actual.thenRead
  obtain ⟨thenEvents,thenRead⟩ := RuntimeObservingPrefix.checkOps_reference _ _ _ _ _ _ _ ran
  obtain ⟨work,right,ran⟩ := actual.elseRead
  obtain ⟨elseEvents,elseRead⟩ := RuntimeObservingPrefix.checkOps_reference _ _ _ _ _ _ _ ran
  change readOps actual.childFuel actual.interval.before.quantum.reference actual.thenOps =
    some (actual.thenState.quantum.reference,thenEvents) at thenRead
  change readOps actual.childFuel actual.interval.before.quantum.reference actual.elseOps =
    some (actual.elseState.quantum.reference,elseEvents) at elseRead
  have inside : offset < block.operations.length := by have range := actual.interval.range; omega
  have literal : (block.operations.drop offset).take 1 =
      [.branch actual.condition actual.thenOps actual.elseOps actual.quantum actual.classical] := by
    rw [List.take_one_drop_eq_of_lt_length inside]
    congr 1
    exact Option.some.inj ((List.getElem?_eq_getElem inside).symm.trans actual.original)
  have read : readOps block.fuel actual.interval.before.quantum.reference ((block.operations.drop offset).take 1) =
      some (Semantics.Observation.phiInterface actual.quantum,[branchEvent actual thenEvents elseEvents]) := by
    rw [literal,actual.depth,Raw.ObservationAgreement.read_succ]
    simp [Raw.ObservationAgreement.layer,Raw.ObservationAgreement.readStep,thenRead,elseRead,branchEvent,armFinish]
  obtain ⟨work,left,ran⟩ := actual.interval.intervalRead
  obtain ⟨_events,original⟩ := RuntimeObservingPrefix.checkOps_reference _ _ _ _ _ _ _ ran
  have after : Semantics.Observation.phiInterface actual.quantum = actual.interval.after.quantum.reference :=
    congrArg Prod.fst (Option.some.inj (read.symm.trans original))
  refine ⟨⟨thenEvents,elseEvents,thenRead,elseRead,?_⟩⟩
  rw [read,after]

/-- Use the original condition check on the same finite ordinary inputs and
measurement row as the history that reaches the branch. -/
theorem checked_choice {sources rootOwner rootName owner name dependencies program block offset path source actual before}
    (checked : @RuntimeBranchCondition.Checked sources rootOwner rootName owner name dependencies program
      block offset path source actual before)
    (input : List Nat) (member : input ∈ checked.inputs.rows) (bits : List Bool)
    (width : bits.length = before.measurements.length) (history : History)
    (agrees : RuntimeOrdinarySSA.Agreement (RuntimeBranchCondition.reference input before.measurements bits)
      history.values before.table) :
    ∃ choice, Qleisli.Semantics.RawInstrument.value history.values actual.condition = some choice ∧
      Semantics.SourceOrdinary.evaluate (RuntimeBranchCondition.reference input before.measurements bits)
        checked.required = some (RuntimeOrdinarySSA.bitValue choice) := by
  obtain ⟨choice,read,evaluated⟩ := agrees _ _ checked.condition.member
  have same := checked.every input member bits width
  unfold RuntimeBranchCondition.sameAt at same
  rw [evaluated] at same
  cases reference : Semantics.SourceOrdinary.evaluate
      (RuntimeBranchCondition.reference input before.measurements bits) checked.required with
  | none => rw [reference] at same; cases same
  | some bit =>
    rw [reference] at same
    have equal : bit ≤ 1 ∧ bit = RuntimeOrdinarySSA.bitValue choice := of_decide_eq_true same
    exact ⟨choice,read,congrArg some equal.2⟩

/-- The actual branch event follows the source condition and applies its
literal classical phis to precisely the histories returned by that arm. -/
theorem original_branch_step {sources rootOwner rootName owner name dependencies program block offset path source actual before}
    (checked : @RuntimeBranchCondition.Checked sources rootOwner rootName owner name dependencies program
      block offset path source actual before)
    (trace : Trace actual)
    (recurse : List Event → History → Option (List History))
    (input : List Nat) (member : input ∈ checked.inputs.rows) (bits : List Bool)
    (width : bits.length = before.measurements.length) (history : History)
    (agrees : RuntimeOrdinarySSA.Agreement (RuntimeBranchCondition.reference input before.measurements bits)
      history.values before.table) :
    ∃ choice,
      Semantics.SourceOrdinary.evaluate (RuntimeBranchCondition.reference input before.measurements bits)
        checked.required = some (RuntimeOrdinarySSA.bitValue choice) ∧
      Qleisli.Semantics.ObservingAction.step dependencies recurse (branchEvent actual trace.left trace.right) history =
        (do
          let selected ← recurse (if choice then
            trace.left++[armFinish actual.thenState.quantum.reference actual.quantum true]
            else trace.right++[armFinish actual.elseState.quantum.reference actual.quantum false]) history
          selected.mapM (Qleisli.Semantics.ObservingAction.merge choice actual.classical)) := by
  obtain ⟨choice,read,evaluated⟩ := checked_choice checked input member bits width history agrees
  refine ⟨choice,evaluated,?_⟩
  simp only [branchEvent,Qleisli.Semantics.ObservingAction.step,read,bind,Option.bind]

#print axioms original_branch_events
#print axioms original_branch_step
end Qleisli.RuntimeOriginalBranch
