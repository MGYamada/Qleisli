import Qleisli.RuntimeCallHistoryReturn
import Qleisli.RuntimeIntervalStates

/-! Identify the original source child's final checked state with the
paired literal child's endpoint and transport the written return order.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Finite (bind_success lift_success)
open RuntimeOwnerMap (Binding)
open Qleisli.RuntimeNamedSourceFlow (Returned)
open Qleisli.RuntimeSemanticForest (Frame frame_exists regroup_action)
open Qleisli.RuntimeStructuralHistory (Represents)
open Qleisli.RuntimeLiteralHistory (return_permutation sourceReturn)

private theorem initial_unique {program : Semantics.Observation.Program} {first second : Raw.Observation.State}
    (left : RuntimeInterval.Computed (PureInterval.initial program) first)
    (right : RuntimeInterval.Computed (PureInterval.initial program) second) :
    first = second := by
  obtain ⟨pWork,pLeft,pRead⟩ := left
  obtain ⟨cWork,cLeft,cRead⟩ := right
  unfold PureInterval.initial at pRead cRead
  obtain ⟨pQuantum,_,pQuantumRead,pOrdinary⟩ := bind_success _ _ _ _ _ pRead
  obtain ⟨cQuantum,_,cQuantumRead,cOrdinary⟩ := bind_success _ _ _ _ _ cRead
  have equal : pQuantum = cQuantum :=
    Except.ok.inj ((lift_success _ _ _ _ pQuantumRead).1.symm.trans (lift_success _ _ _ _ cQuantumRead).1)
  subst cQuantum
  exact Except.ok.inj ((lift_success _ _ _ _ pOrdinary).1.symm.trans (lift_success _ _ _ _ cOrdinary).1)

/-- Both native initializations execute the same input and classical-input
folds, including the complete issued state. -/
theorem actual_child_start
    {dependencies program block start count inputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect) :
    scope.prepared.block.entry = scope.localEntry := by
  change scope.prepared.entry = scope.localEntry
  exact initial_unique scope.prepared.inputRead scope.entryRead

/-- The source child's final return checkpoint follows the same native
operation list, entry and depth as the paired original call. -/
theorem actual_child_final
    {dependencies program block start count inputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (native : RuntimeInterval.Checked scope.prepared.block scope.prepared.block.operations.length 0) :
    native.after = scope.localAfter := by
  have all := native.prefixRead
  simp only [List.take_length] at all
  have complete : RuntimeInterval.Computed (Raw.Observation.checkOps dependencies 65
      scope.localEntry ((block.operations.drop start).take count)) native.before := by
    rw [← actual_child_start scope]
    exact all
  have final := RuntimeAdjacentSlices.checkOps_unique complete scope.nativeRead
  have empty : RuntimeInterval.Computed
      (Raw.Observation.checkOps dependencies 65 native.before []) native.after := by
    simpa only [List.take_zero] using native.intervalRead
  exact (RuntimeAdjacentSlices.checkOps_unique empty
    (RuntimeIntervalStates.empty_read dependencies 64 native.before native.history.1)).trans final

/-- Retain the child's actual written owner lookup on the paired call's
exact native exit, including zero-width owners. -/
theorem actual_child_return
    {dependencies program block start count inputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    {roles before after}
    (returned : Returned scope.prepared.block roles before after) :
    ∃ owners : RuntimeOwnerMap.Checked roles scope.localAfter,
      RuntimeInterval.Computed (RuntimePureBody.reordered roles scope.localAfter before.bindings) owners ∧
      after = {before with bindings := owners.bindings} := by
  obtain ⟨native,_,owners,ordered,same⟩ := returned
  have proof : ∃ owners : RuntimeOwnerMap.Checked roles native.after,
      RuntimeInterval.Computed (RuntimePureBody.reordered roles native.after before.bindings) owners ∧
      after = {before with bindings := owners.bindings} := ⟨owners,ordered,same⟩
  exact actual_child_final scope native ▸ proof

/-- A checked written return changes the logical order on every source
result, while leaving the same literal operator and reference columns. -/
theorem source_return_order {state beforeRoles afterRoles}
    (before : RuntimeOwnerMap.Checked beforeRoles state) (after : RuntimeOwnerMap.Checked afterRoles state)
    (read : RuntimeInterval.Computed (RuntimePureBody.reordered afterRoles state before.bindings) after)
    (frame : Frame before.bindings) :
    ∃ returned : Frame after.bindings, ∀ history joint, Represents frame state history joint →
      Represents returned state history (sourceReturn before.bindings after.bindings joint) := by
  have ordered := return_permutation before after read
  obtain ⟨returned⟩ := frame_exists (fun binding present => frame.available binding (ordered.subset present))
  have distinct : before.bindings.Nodup := List.Pairwise.of_map (fun binding : Binding => binding.port.token)
    (fun _ _ different same => different (congrArg (fun binding : Binding => binding.port.token) same))
    before.tokensDistinct
  refine ⟨returned,?_⟩
  intro history joint represented column row bounded
  exact (represented column row bounded).trans
    (regroup_action frame returned ordered.symm distinct state.quantum.frame joint row column)

#print axioms actual_child_final
#print axioms actual_child_return
#print axioms source_return_order
end Qleisli.RuntimeCallHistory
