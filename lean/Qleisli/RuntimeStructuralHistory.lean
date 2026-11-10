import Qleisli.RuntimeStructuralSourceAction
import Qleisli.RuntimeLiteralHistory

/-! The original structural step leaves the literal observing history intact.
Its source regrouping explains the same operator in the ordered result code,
including the visible ordinary table and arbitrary reference columns.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeStructuralHistory
open QleisliKernel QleisliKernel.Qirf
open Semantics.Observation (Event readOps)
open Qleisli.Semantics.ObservingAction (History run)
open Qleisli.RuntimeLiteralHistory (AgreesWithInherited pure_history_with_inherited)
open Qleisli.RuntimeNamedThreePackedInstrument (pureHistory)
open Qleisli.RuntimeStructuralSourceAction (sourceRegroup original_reference_action)
open Qleisli.RuntimeSemanticForest (Frame)

def Represents {bindings} (frame : Frame bindings) (state : Raw.Observation.State)
    (history : History) (joint : Nat → Nat → ℂ) : Prop :=
  ∀ column row, row < 2^state.quantum.frame.length →
    history.operator row column = RuntimeSemanticForest.action frame state.quantum.frame joint row column

theorem original_history {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before)
    (input : Frame before.bindings) (inherited : Option (Nat → Prop)) (inputs : List Nat) (ordinary : RuntimeOrdinaryBody.State)
    (history : History) (joint : Nat → Nat → ℂ)
    (agrees : AgreesWithInherited inherited inputs action.interval.before ordinary history)
    (represented : Represents input action.interval.before history joint) {events : List Event} {results : List History}
    (read : readOps block.fuel action.interval.before.quantum.reference ((block.operations.drop start).take count) =
      some (action.interval.after.quantum.reference,events))
    (executed : run dependencies block.fuel events history = some results) :
    results = [history] ∧ AgreesWithInherited inherited inputs action.interval.after ordinary history ∧
    ∃ output : Frame action.after.bindings, ∃ expected,
      sourceRegroup (event.arguments.flatMap SourceTypes.SourceRuntimeValues.valueOwners)
        before.bindings joint = some expected ∧ Represents output action.interval.after history expected := by
  obtain ⟨operations,rawEvents,literal,rawTrace,singleton,kept⟩ :=
    pure_history_with_inherited (.structural action) inherited inputs ordinary history agrees read executed
  have same : operations = [action.operation] :=
    (List.map_inj_right (f := Semantics.Observation.Op.pure)
      (fun _ _ equal => Semantics.Observation.Op.pure.inj equal)).mp
      (literal.symm.trans action.literal)
  subst operations
  have empty : rawEvents = [] := congrArg Semantics.RawTrace.Prepared.events
    (Option.some.inj (rawTrace.symm.trans (RuntimeStructuralWires.original_trace action)))
  subst rawEvents
  have unchanged : pureHistory dependencies [] history = history := by cases history; rfl
  rw [unchanged] at singleton kept
  obtain ⟨output,whole⟩ := original_reference_action action input
  obtain ⟨expected,sourceRead,corresponds⟩ := whole joint
  refine ⟨singleton,kept,output,expected,sourceRead,?_⟩
  intro column row bound
  rw [(RuntimeStructuralWires.original_wires action).1] at bound
  exact (represented column row bound).trans (corresponds row column)

#print axioms original_history
end Qleisli.RuntimeStructuralHistory
