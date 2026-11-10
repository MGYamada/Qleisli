import Qleisli.RuntimeLiteralStructuralRefinement
import Qleisli.RuntimeOriginalSparseObservation

/-! The literal observation consumes one original owner and retains the
ordered outcome operators and updated SSA values in the shared sparse history.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Observation (readOps)
open Qleisli.Semantics.ObservingAction (History run erase)
open Qleisli.RuntimeLiteralHistory (sourceErasure observation_permutation run_single)
open Qleisli.RuntimeOriginalObservation
  (original_before_bindings original_erasure erasure_step_histories outcomeJointLayout)
open Qleisli.RuntimeOriginalSparseObservation (original_sparse_erasure_action)
open Qleisli.RuntimeSemanticForest (Frame frame_exists ownerLayout regroup_action action)
open Qleisli.RuntimeForestRegroup (sourceDimension)
open Qleisli.RuntimeStructuralHistory (Represents)
open RuntimeOwnerMap (Binding)
open RuntimePureBody (Step)
open Qleisli.RuntimeNamedChildRuns (OrdinaryAligned)
open Qleisli.RuntimeNamedSourceFlow (Aligned)
open RuntimeSelectionSteps (Edge)
open Qleisli.RuntimeObservingWrites (WritesWithin)
open Qleisli.RuntimeOriginalObservationValues
  (observation_measurement_ids observation_step_values observation_step_values_with_inherited)

private theorem sparse_observation_outcomes {sources rootOwner rootName caller functionName dependencies program
    path event block position before ssa roles}
    (observation : @RuntimeOrdinaryBody.Observation sources rootOwner rootName caller functionName dependencies
      program path event block position before ssa)
    (checked : RuntimeOwnerMap.Checked roles observation.checked.interval.before)
    (bindings : checked.bindings = before.bindings)
    (input : Frame before.bindings) (inputs : List Nat) (history : History) (joint : Nat → Nat → ℂ)
    (inherited : Option (Nat → Prop))
    (agrees : ScopedOrdinaryAgrees inherited inputs observation.checked.interval.before ssa history)
    (represented : Represents input observation.checked.interval.before history joint)
    {events : List Semantics.Observation.Event} {results : List History}
    (read : readOps block.fuel observation.checked.interval.before.quantum.reference
      ((block.operations.drop position.start).take position.count) =
        some (observation.checked.interval.after.quantum.reference,events))
    (avoids : TraceWriteBound (inherited.map (fun holds id => ¬ holds id)) events)
    (executed : run dependencies block.fuel events history = some results) :
    ∃ expected,
      sourceErasure observation.checked.operand (RuntimeObservationAction.spectators event) before.bindings joint =
        some expected ∧
      List.Forall₂ (fun sourceResult result =>
        result.values = (match observation.checked.measured with
          | none => history.values
          | some id => history.values ++ [(id,sourceResult.1 == 1)]) ∧
        result.hidden = history.hidden ++ [sourceResult.1] ∧
        ScopedOrdinaryAgrees inherited inputs observation.checked.interval.after observation.ordinary result ∧
        SemanticHistoryEncoding observation.checked.interval.after observation.checked.after.bindings
          result.operator sourceResult.2) expected results ∧
      (∀ id, observation.checked.measured = some id →
        Semantics.OrdinaryValue.lookup history.values id = none) := by
  let erased := observation.checked
  let selected := erased.before.bindings
  let physical := erased.interval.before.quantum.frame
  let axes := erased.input.port.wires.map physical.idxOf
  let layout := ownerLayout erased.input
  let sourceJoint := fun logical column =>
    joint (Qleisli.MixedRadix.recode selected before.bindings (sourceDimension before.bindings) logical) column
  have order : selected.Perm before.bindings :=
    (observation_permutation erased checked bindings).trans (List.Perm.of_eq bindings)
  have distinct : before.bindings.Nodup := bindings ▸
    (List.Pairwise.of_map (fun binding : Binding => binding.port.token)
      (fun _ _ different same => different (congrArg (fun binding : Binding => binding.port.token) same))
      checked.tokensDistinct)
  obtain ⟨ordered⟩ := frame_exists (fun binding present => input.available binding (order.subset present))
  have encoded (column row : Nat) (bounded : row < 2^physical.length) :
      history.operator row column = action ordered physical sourceJoint row column :=
    (represented column row bounded).trans
      (regroup_action input ordered order.symm distinct physical joint row column)
  obtain ⟨layoutRead,width,output,equation⟩ := original_sparse_erasure_action erased ordered
  have literal := (original_erasure erased).1
  have eventsEq : events = [.erase physical.length axes erased.measured] :=
    congrArg Prod.snd (Option.some.inj (read.symm.trans literal))
  subst events
  cases depth : block.fuel with
  | zero =>
    rw [depth] at executed
    cases executed
  | succ fuel =>
    obtain ⟨branch,performed,facts⟩ := erasure_step_histories dependencies physical.length axes
      erased.measured (run dependencies fuel) history
    have orderedResults : results = (List.range (2^axes.length)).map branch := by
      rw [depth,run_single,performed] at executed
      exact (Option.some.inj executed).symm
    have values : ∀ result ∈ (List.range (2^axes.length)).map branch,
        ScopedOrdinaryAgrees inherited inputs observation.checked.interval.after observation.ordinary result := by
      cases inherited with
      | none =>
        exact observation_step_values observation inputs history agrees.1 agrees.2
          (run dependencies fuel) performed
      | some holds =>
        exact observation_step_values_with_inherited observation inputs history holds agrees.1 agrees.2
          (run dependencies fuel) avoids performed
    refine ⟨(List.range (2^axes.length)).map (fun outcome => (outcome,outcomeJointLayout layout outcome sourceJoint)),
      ?_,?_,?_⟩
    · have choice := original_before_bindings erased
      change sourceErasure erased.operand (RuntimeObservationAction.spectators event) before.bindings joint = _
      simp only [sourceErasure,layoutRead,choice,bind,Option.bind,pure,width,sourceJoint,selected]
      rfl
    · rw [orderedResults,List.forall₂_map_left_iff,List.forall₂_map_right_iff]
      apply List.forall₂_same.2
      intro outcome member
      obtain ⟨visible,hidden,operator⟩ := facts outcome
      refine ⟨visible,hidden,values _ (List.mem_map_of_mem member),_,erased.after,rfl,output,?_⟩
      intro column row bounded
      rw [operator]
      calc
        _ = erase physical.length axes outcome (fun physicalRow => action ordered physical sourceJoint physicalRow column) row := by
          unfold erase
          apply Qleisli.Exact.sum_map_congr
          intro physicalRow present
          simp only [encoded column physicalRow (List.mem_range.mp present)]
        _ = _ := equation sourceJoint outcome row (List.mem_range.mp member) bounded column
    · intro id measured
      apply Qleisli.RuntimeOriginalClassicalJoin.lookup_unissued
      intro present
      have localFresh := (observation_measurement_ids observation measured).1
      cases inherited with
      | none => exact localFresh (agrees.2 present)
      | some holds =>
        have writes : WritesWithin [.erase physical.length axes erased.measured] (fun id => ¬ holds id) := avoids
        rw [show erased.measured = some id from measured] at writes
        exact (agrees.2 present).elim (writes List.mem_cons_self (.measure _ _ id)) localFresh

/-- Observation is a local sparse law at the actual source prefix position. -/
theorem sparse_observation_refines_with_inherited {sources rootOwner rootName caller functionName dependencies program
    path event block position before ssa}
    (observation : @RuntimeOrdinaryBody.Observation sources rootOwner rootName caller functionName dependencies
      program path event block position before ssa)
    (inputs : List Nat) (scope : List Edge) (ordinal : Nat) (inherited : Option (Nat → Prop))
    {ownerBefore ownerAfter ordinaryBefore ordinaryAfter}
    (owners : Aligned ownerBefore ownerAfter (.observation observation))
    (ordinary : OrdinaryAligned ordinaryBefore ordinaryAfter (.observation observation))
    {events source history results}
    (read : readOps block.fuel observation.checked.interval.before.quantum.reference
      ((block.operations.drop position.start).take position.count) =
        some (observation.checked.interval.after.quantum.reference,events))
    (avoids : TraceWriteBound (inherited.map (fun holds id => ¬ holds id)) events)
    (agrees : SemanticHistoryAgreesWithInherited inherited inputs observation.checked.interval.before
      ownerBefore ordinaryBefore source history)
    (executed : run dependencies block.fuel events history = some results) :
    ∃ expected, sourceObservationStep observation scope ordinal source = some expected ∧
      List.Forall₂ (SemanticHistoryAgreesWithInherited inherited inputs observation.checked.interval.after
        ownerAfter ordinaryAfter)
        expected results := by
  rcases owners with ⟨rfl,rfl⟩
  rcases ordinary with ⟨rfl,rfl⟩
  have incoming := agrees
  obtain ⟨_,_,_,values,_,checked,bindings,input,represented⟩ := agrees
  obtain ⟨expected,erased,paired,unused⟩ :=
    sparse_observation_outcomes observation checked bindings input inputs history source.operator inherited
      values represented read avoids executed
  exact observation_results_refine_with_inherited observation SemanticHistoryEncoding inputs scope ordinal inherited
    incoming unused erased paired

theorem sparse_observation_refines {sources rootOwner rootName caller functionName dependencies program
    path event block position before ssa}
    (observation : @RuntimeOrdinaryBody.Observation sources rootOwner rootName caller functionName dependencies
      program path event block position before ssa)
    (inputs : List Nat) (scope : List Edge) (ordinal : Nat) {ownerBefore ownerAfter ordinaryBefore ordinaryAfter}
    (owners : Aligned ownerBefore ownerAfter (.observation observation))
    (ordinary : OrdinaryAligned ordinaryBefore ordinaryAfter (.observation observation))
    {events source history results}
    (read : readOps block.fuel observation.checked.interval.before.quantum.reference
      ((block.operations.drop position.start).take position.count) =
        some (observation.checked.interval.after.quantum.reference,events))
    (agrees : SemanticHistoryAgrees inputs observation.checked.interval.before ownerBefore ordinaryBefore source history)
    (executed : run dependencies block.fuel events history = some results) :
    ∃ expected, sourceObservationStep observation scope ordinal source = some expected ∧
      List.Forall₂ (SemanticHistoryAgrees inputs observation.checked.interval.after ownerAfter ordinaryAfter)
        expected results :=
  sparse_observation_refines_with_inherited observation inputs scope ordinal none owners ordinary read trivial agrees executed

noncomputable def withSparseObservation {dependencies program block}
    (fallback : List (@Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (scope : List Edge) (prior : List (@Step dependencies program block)) (step : Step dependencies program block)
    (source : SourceHistory) : Option (List SourceHistory) :=
  match step with
  | .observation observation => sourceObservationStep observation scope prior.length source
  | _ => fallback prior step source

def NeedsNonObservation {dependencies program block} : @Step dependencies program block → Prop
  | .observation _ => False
  | _ => True

theorem sourceStep_with_sparse_observation {dependencies program block}
    (steps : List (@Step dependencies program block)) (inputs : List Nat)
    (certifies : Step dependencies program block → Prop)
    (fallback : List (@Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (scope : List Edge)
    (remaining : StepRefinement steps (fun step => certifies step ∧ NeedsNonObservation step)
      fallback (fun _ => SemanticHistoryAgrees inputs)) :
    StepRefinement steps certifies (withSparseObservation fallback scope) (fun _ => SemanticHistoryAgrees inputs) := by
  intro prior first later position certified ownerBefore ownerAfter ordinaryBefore ordinaryAfter
    owners ordinary chunk read source history outputs agrees executed
  cases first
  case observation observation =>
    exact sparse_observation_refines observation inputs scope prior.length owners ordinary read agrees executed
  all_goals
    exact remaining prior _ later position ⟨certified,trivial⟩ owners ordinary read agrees executed

/-- Refine the observation on its actual source prefix inside a child whose
literal writes are known to avoid the inherited history. -/
theorem sourceStep_with_scoped_observation {dependencies program block}
    (steps : List (@Step dependencies program block)) (inputs : List Nat) (inherited : Option (Nat → Prop))
    (certifies : Step dependencies program block → Prop)
    (fallback : List (@Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (scope : List Edge)
    (remaining : StepRefinement steps (fun step => certifies step ∧ NeedsNonObservation step)
      fallback (fun _ => SemanticHistoryAgreesWithInherited inherited inputs)
      (inherited.map (fun holds id => ¬ holds id))) :
    StepRefinement steps certifies (withSparseObservation fallback scope)
      (fun _ => SemanticHistoryAgreesWithInherited inherited inputs)
      (inherited.map (fun holds id => ¬ holds id)) := by
  intro prior first later position certified ownerBefore ownerAfter ordinaryBefore ordinaryAfter
    owners ordinary chunk read
  refine WithChunkWriteBound.of_trace ?_
  intro writes source history outputs agrees executed
  cases first
  case observation observation =>
    exact sparse_observation_refines_with_inherited observation inputs scope prior.length inherited
      owners ordinary read writes agrees executed
  all_goals
    exact ((remaining prior _ later position ⟨certified,trivial⟩ owners ordinary read).apply writes) agrees executed

#print axioms sourceStep_with_scoped_observation
#print axioms sparse_observation_refines
#print axioms sourceStep_with_sparse_observation
end Qleisli.RuntimeLiteralBody
