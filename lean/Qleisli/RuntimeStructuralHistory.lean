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
open Qleisli.RuntimeLiteralHistory (Agrees pure_history)
open Qleisli.RuntimeOriginalBranchJoin (RepresentsOperator)
open Qleisli.RuntimeNamedThreePackedInstrument (pureHistory)
open Qleisli.RuntimeStructuralSourceAction (spectators original_reference_action)
open Qleisli.RuntimeForestRegroup (sourceDimension)
open Qleisli.Semantics.Exact (scalar)
open RuntimeForestCode
open RuntimeOwnerMap (Map Binding)

theorem original_history {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before)
    (input : Frame action.beforeFrame) (inputs : List Nat) (ordinary : RuntimeOrdinaryBody.State)
    (history : History) (joint : Nat → Nat → ℂ)
    (agrees : Agrees inputs action.interval.before ordinary history)
    (represented : RepresentsOperator input history joint) {events : List Event} {results : List History}
    (read : readOps block.fuel action.interval.before.quantum.reference ((block.operations.drop start).take count) =
      some (action.interval.after.quantum.reference,events))
    (executed : run dependencies block.fuel events history = some results) :
    results = [history] ∧ Agrees inputs action.interval.after ordinary history ∧
    ∃ selected : Map, selected.map Binding.owner = action.inputRoles ∧
      selected.map Binding.port = action.inputs ∧ (spectators action ++ selected).Perm before.bindings ∧
      ∃ output : Sparse, sparseLayout (forestBasis action.afterFrame.bindings) = some output ∧
        ∀ row column, row < 2^action.interval.after.quantum.frame.length →
          history.operator row column =
          ((List.range output.dimension).map fun logical =>
            scalar (embed action.interval.after.quantum.frame action.afterFrame.bindings output row logical) *
              joint (Qleisli.MixedRadix.recode (spectators action ++ selected) before.bindings
                (sourceDimension before.bindings) logical) column).sum := by
  obtain ⟨operations,rawEvents,literal,rawTrace,singleton,kept⟩ :=
    pure_history (.structural action) inputs ordinary history agrees read executed
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
  obtain ⟨selected,owners,ports,permutation,output,original,whole⟩ := original_reference_action action input
  refine ⟨singleton,kept,selected,owners,ports,permutation,output,by rwa [action.resultBindings],?_⟩
  intro row column bound
  rw [(RuntimeStructuralWires.original_wires action).1] at bound
  rw [action.resultBindings]
  exact (represented column row bound).trans (whole joint row column)

#print axioms original_history
end Qleisli.RuntimeStructuralHistory
