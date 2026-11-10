import Qleisli.RuntimeCallHistoryFold
import Qleisli.RuntimeCallHistoryPure

/-! Local laws for original observing and ordinary instructions of a call.
The parent result fixes each actual ordinary expression evaluation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open Semantics.Finite (Dependency)
open Semantics.Raw (Port)
open Semantics.Observation (Op Event Expr readOps)
open Semantics.RawTrace (Interface)
open Raw.Observation (checkOps checkStep)
open Raw.ObservationAgreement (readStep)
open RuntimeCallTraceFrames (Partition)
open Qleisli.Semantics.ObservingAction (History run)
open Qleisli.RuntimeLiteralHistory (run_single)

/-- An operation whose checked history law is total supplies a segment
law for each actual parent result. A common zero history projects the
structural partition alone, with the same native read receipts. -/
theorem step_of_total {dependencies : List Dependency} {parentDepth childDepth : Nat}
    {spectators : List Port} {op : Op}
    (total : ∀ (parent child parentAfter childAfter : Raw.Observation.State),
      RuntimeInterval.Computed (checkStep dependencies (checkOps dependencies parentDepth) parent op) parentAfter →
      RuntimeInterval.Computed (checkStep dependencies (checkOps dependencies childDepth) child op) childAfter →
      Partition parent.quantum.reference child.quantum.reference spectators →
      ∀ actual localHistory, Agrees parent.quantum.reference child.quantum.reference spectators actual localHistory →
      ∃ parents children, CheckedResults dependencies parentDepth childDepth parent child parentAfter childAfter
        spectators op actual localHistory parents children) :
    StepLaw dependencies parentDepth childDepth spectators op := by
  intro parent child parentAfter childAfter parentEvents childEvents parentRead childRead pTrace cTrace partition
  let empty : History := ⟨[],[],fun _ _ => 0⟩
  have emptyAgrees : Agrees parent.quantum.reference child.quantum.reference spectators empty (fun _ => empty) :=
    ⟨fun _ => rfl,fun _ => rfl,fun _ _ _ => rfl⟩
  have applyTotal := total parent child parentAfter childAfter parentRead childRead partition
  obtain ⟨_,_,structural⟩ := applyTotal empty (fun _ => empty) emptyAgrees
  refine ⟨structural.partition,?_⟩
  intro actual localHistory agrees parents executed
  obtain ⟨produced,children,result⟩ := applyTotal actual localHistory agrees
  obtain ⟨pEvents,cEvents,pRead,cRead,_,_,runs⟩ := result.traces
  have parentEq : pEvents = parentEvents := congrArg Prod.snd (Option.some.inj (pRead.symm.trans pTrace))
  have childEq : cEvents = childEvents := congrArg Prod.snd (Option.some.inj (cRead.symm.trans cTrace))
  subst pEvents
  subst cEvents
  have resultEq : produced = parents := Option.some.inj (runs.parentRun.symm.trans executed)
  subst produced
  exact ⟨children,runs⟩

theorem erasure_step_law (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (spectators : List Port) (token : Nat) (measured : Option Nat) :
    StepLaw dependencies parentDepth childDepth spectators (eraseOp token measured) := by
  apply step_of_total
  intro parent child parentAfter childAfter pRead cRead partition actual localHistory agrees
  obtain ⟨_,_,parentRead⟩ := pRead
  obtain ⟨_,_,childRead⟩ := cRead
  exact checked_erasure dependencies parentDepth childDepth parent child parentAfter childAfter spectators
    partition token measured parentRead childRead actual localHistory agrees

theorem reset_step_law (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (spectators : List Port) (input output wire : Nat) :
    StepLaw dependencies parentDepth childDepth spectators (.reset input output wire) := by
  apply step_of_total
  intro parent child parentAfter childAfter pRead cRead partition actual localHistory agrees
  obtain ⟨_,_,parentRead⟩ := pRead
  obtain ⟨_,_,childRead⟩ := cRead
  exact checked_reset dependencies parentDepth childDepth parent child parentAfter childAfter spectators
    partition input output wire parentRead childRead actual localHistory agrees

private theorem classical_segment (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (parent child : Interface) (spectators : List Port) (partition : Partition parent child spectators)
    (expr : Expr) (output : Nat) :
    Segment dependencies parentDepth childDepth parent child parent child spectators
      [.classical expr output] [.classical expr output] := by
  refine ⟨partition,?_⟩
  intro actual localHistory agrees parents executed
  have literal := executed
  rw [run_single] at literal
  simp only [Qleisli.Semantics.ObservingAction.step] at literal
  obtain ⟨value,valueRead,done⟩ := Option.bind_eq_some_iff.mp literal
  let updated := fun history : History => {history with values := history.values++[(output,value)]}
  have same : [updated actual] = parents := Option.some.inj done
  subst parents
  refine ⟨[fun high => updated (localHistory high)],executed,?_,.cons ?_ .nil⟩
  · intro high
    have sameValue : Qleisli.Semantics.RawInstrument.expression (localHistory high).values expr = some value := by
      rw [← agrees.values high]
      exact valueRead
    rw [run_single]
    simp [Qleisli.Semantics.ObservingAction.step,sameValue,updated]
  · refine ⟨fun high => ?_,agrees.hidden,agrees.operator⟩
    change actual.values++[(output,value)] = (localHistory high).values++[(output,value)]
    rw [agrees.values high]

private theorem classical_law (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (spectators : List Port) (op : Op) (expr : Expr) (output : Nat)
    (reader : ∀ depth state, readStep (readOps depth) state op = some (state,[.classical expr output])) :
    StepLaw dependencies parentDepth childDepth spectators op := by
  intro parent child parentAfter childAfter parentEvents childEvents _ _ pTrace cTrace partition
  obtain ⟨pState,pEvents⟩ := Prod.mk.inj (Option.some.inj ((reader _ _).symm.trans pTrace))
  obtain ⟨cState,cEvents⟩ := Prod.mk.inj (Option.some.inj ((reader _ _).symm.trans cTrace))
  rw [← pState,← cState,← pEvents,← cEvents]
  exact classical_segment dependencies parentDepth childDepth _ _ spectators partition expr output

theorem constant_step_law (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (spectators : List Port) (value : Bool) (output : Nat) :
    StepLaw dependencies parentDepth childDepth spectators (.constant value output) :=
  classical_law dependencies parentDepth childDepth spectators _ (.constant value) output (fun _ _ => rfl)

theorem not_step_law (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (spectators : List Port) (input output : Nat) :
    StepLaw dependencies parentDepth childDepth spectators (.not input output) :=
  classical_law dependencies parentDepth childDepth spectators _ (.not input) output (fun _ _ => rfl)

theorem xor_step_law (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (spectators : List Port) (left right output : Nat) :
    StepLaw dependencies parentDepth childDepth spectators (.xor left right output) :=
  classical_law dependencies parentDepth childDepth spectators _ (.xor left right) output (fun _ _ => rfl)

theorem and_step_law (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (spectators : List Port) (left right output : Nat) :
    StepLaw dependencies parentDepth childDepth spectators (.and left right output) :=
  classical_law dependencies parentDepth childDepth spectators _ (.and left right) output (fun _ _ => rfl)

#print axioms erasure_step_law
#print axioms reset_step_law
#print axioms xor_step_law
end Qleisli.RuntimeCallHistory
