import Qleisli.RuntimeOriginalClassicalJoin
import Qleisli.RuntimeOriginalQuantumPhi
import Qleisli.RuntimeObservingValueRetention

/-! A literal original conditional composes the selected recursive arm, its
quantum return permutation, and the simultaneous classical phi merge on the
same ordered family of histories.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeOriginalBranchJoin
open QleisliKernel QleisliKernel.Qirf
open RuntimeForestCode (Frame OwnerCodes)
open RuntimeOwnerCodeReindex (dimensionAt reindex)
open RuntimeOrdinarySSA (Agreement bitValue)
open Qleisli.RuntimeObservingValueRetention (run_retains_values)
open Qleisli.RuntimeOriginalQuantumPhi (armBindings outputBindings original_quantum_phi_action)
open Qleisli.RuntimeForestOrderedProduct (layouts)
open Qleisli.Semantics.ObservingAction (History run step merge)
open Qleisli.RuntimeNamedThreePackedInstrument (advance_pure pureHistory run_append_event)
open Qleisli.RuntimeForestProduct (referenceAction)

def armChecked {dependencies program block offset}
    {actual : @RuntimeInterval.Branch dependencies program block offset} {leftRoles rightRoles}
    (left : RuntimeOwnerMap.Checked leftRoles actual.thenState)
    (right : RuntimeOwnerMap.Checked rightRoles actual.elseState) (choice : Bool) :
    RuntimeOwnerMap.Checked (if choice then leftRoles else rightRoles)
      (if choice then actual.thenState else actual.elseState) :=
  match choice with
  | true => left
  | false => right

def RepresentsOperator {roles state checked} (frame : @Frame roles state checked)
    (history : History) (joint : Nat → Nat → ℂ) : Prop :=
  ∀ col, RawFiniteRows.OnRows state.quantum.frame.length (fun row => history.operator row col)
    (fun row => referenceAction frame joint row col)

private def armPermutation {dependencies program block offset}
    (actual : @RuntimeInterval.Branch dependencies program block offset) (choice : Bool) : Semantics.Raw.Event :=
  let state := (if choice then actual.thenState else actual.elseState).quantum.reference
  .reorder state.frame.length (Semantics.RawTrace.axes state (Semantics.Observation.phiWires state actual.quantum choice))

/-- The independent interpreter uses the original child fuel and maps the
literal arm-final quantum permutation over every body result in order. -/
theorem original_arm_run {dependencies program block offset}
    {actual : @RuntimeInterval.Branch dependencies program block offset}
    (trace : RuntimeOriginalBranch.Trace actual) (choice : Bool) (history : History) :
    run dependencies actual.childFuel (trace.armEvents choice) history =
      (do
        let returned ← run dependencies actual.childFuel (trace.armBody choice) history
        return returned.map (pureHistory dependencies [armPermutation actual choice])) := by
  have literal : trace.armEvents choice = trace.armBody choice ++ [.pure (armPermutation actual choice)] := by
    cases choice <;> rfl
  cases depth : actual.childFuel with
  | zero =>
    have impossible := trace.leftRead
    rw [depth] at impossible
    cases impossible
  | succ fuel =>
    rw [literal,run_append_event dependencies fuel]
    simp only [advance_pure]
    rfl

/-- For every actual result of the original selected arm, the same literal
parent step applies the quantum return permutation and classical phi merge.
The resulting ordered family has the checked output Frame and visible SSA
values, with an exact logical reindexing on each operator column. -/
theorem original_branch_join {sources rootOwner rootName caller name dependencies program block offset
    path event source actual before left right ordinary leftOrdinary rightOrdinary}
    (action : @RuntimeBranchAction.Checked sources rootOwner rootName caller name dependencies program block offset
      path event source actual before left right ordinary leftOrdinary rightOrdinary)
    (trace : RuntimeOriginalBranch.Trace actual)
    (input : List Nat) (member : input ∈ action.condition.inputs.rows) (bits : List Bool)
    (width : bits.length = ordinary.measurements.length) (history : History) :
    let reference := RuntimeBranchCondition.reference input ordinary.measurements bits
    Agreement reference history.values ordinary.table →
    (∀ choice,
      Semantics.SourceOrdinary.evaluate reference action.condition.required = some (bitValue choice) →
      ∃ frame : Frame (armChecked action.thenFrame action.elseFrame choice),
      ∃ returned : List History,
        run dependencies actual.childFuel (trace.armBody choice) history = some returned ∧
        ∀ result ∈ returned,
          Agreement reference result.values (if choice then leftOrdinary.table else rightOrdinary.table) ∧
          result.values.map Prod.fst ⊆ (if choice then actual.thenState else actual.elseState).classical.map Prod.fst ∧
          ∃ joint, RepresentsOperator frame result joint) →
    ∃ choice,
      Semantics.SourceOrdinary.evaluate reference action.condition.required = some (bitValue choice) ∧
      ∃ frame : Frame (armChecked action.thenFrame action.elseFrame choice),
      ∃ output : Frame action.ownerPhis.output,
      ∃ beforeCodes : OwnerCodes (armBindings action.ownerPhis choice),
      ∃ afterCodes : OwnerCodes (outputBindings action.ownerPhis),
      ∃ returned results : List History,
        reindex frame.owners (armBindings action.ownerPhis choice) = some beforeCodes ∧
        layouts afterCodes = layouts beforeCodes ∧
        reindex afterCodes action.ownerPhis.output.bindings = some output.owners ∧
        run dependencies actual.childFuel (trace.armBody choice) history = some returned ∧
        step dependencies (run dependencies actual.childFuel)
          (RuntimeOriginalBranch.branchEvent actual trace.left trace.right) history = some results ∧
        let index := fun logical =>
          Qleisli.MixedRadix.recode (armBindings action.ownerPhis choice)
            (armChecked action.thenFrame action.elseFrame choice).bindings (dimensionAt frame.owners)
            (Qleisli.MixedRadix.recode action.ownerPhis.output.bindings (outputBindings action.ownerPhis)
              (dimensionAt afterCodes) logical)
        List.Forall₂ (fun arm joined =>
          joined.hidden = arm.hidden ∧ Agreement reference joined.values action.ordinaryAfter.table ∧
          ∃ joint, RepresentsOperator frame arm joint ∧
            RepresentsOperator output joined (fun logical column => joint (index logical) column)) returned results := by
  intro reference agrees armProof
  obtain ⟨choice,condition,actualStep⟩ := RuntimeOriginalBranch.original_branch_step action.condition trace
    (run dependencies actual.childFuel) input member bits width history agrees
  obtain ⟨frame,returned,bodyRead,each⟩ := armProof choice condition
  let arm := armChecked action.thenFrame action.elseFrame choice
  have sameBindings : arm.bindings = if choice then action.thenFrame.bindings else action.elseFrame.bindings := by
    cases choice <;> rfl
  obtain ⟨output,beforeCodes,afterCodes,inputRead,layoutsEq,outputRead,_equation,quantum⟩ :=
    original_quantum_phi_action actual action.ownerPhis trace choice arm sameBindings frame
  let index := fun logical =>
    Qleisli.MixedRadix.recode (armBindings action.ownerPhis choice) arm.bindings (dimensionAt frame.owners)
      (Qleisli.MixedRadix.recode action.ownerPhis.output.bindings (outputBindings action.ownerPhis)
        (dimensionAt afterCodes) logical)
  let transport := pureHistory dependencies [armPermutation actual choice]
  obtain ⟨results,merged,related⟩ := RuntimeOriginalClassicalJoin.merge_family choice actual.classical returned transport
    (fun armHistory joined =>
      joined.hidden = armHistory.hidden ∧ Agreement reference joined.values action.ordinaryAfter.table ∧
      ∃ joint, RepresentsOperator frame armHistory joint ∧
        RepresentsOperator output joined (fun logical column => joint (index logical) column)) (by
      intro current present
      obtain ⟨selected,issued,joint,encoded⟩ := each current present
      have retained := run_retains_values dependencies actual.childFuel (trace.armBody choice) history
        bodyRead current present
      obtain ⟨moved,ran,hidden,values,represented⟩ :=
        quantum (run dependencies (actual.childFuel-1)) joint current encoded
      have literal : step dependencies (run dependencies (actual.childFuel-1))
          (RuntimeOriginalBranch.armFinish (if choice then actual.thenState else actual.elseState).quantum.reference
            actual.quantum choice) current = some [transport current] := rfl
      have same : moved = transport current := List.cons.inj (Option.some.inj (ran.symm.trans literal)) |>.1
      subst moved
      have old : Agreement reference (transport current).values ordinary.table := by
        rw [values]
        intro id expression present
        obtain ⟨bit,known,sourceValue⟩ := agrees id expression present
        exact ⟨bit,retained id bit known,sourceValue⟩
      obtain ⟨joined,joinedRead,joinedHidden,operator,agreement⟩ :=
        RuntimeOriginalClassicalJoin.original_merge_agrees action reference choice (transport current)
          condition old (by rwa [values]) (by rwa [values])
      refine ⟨joined,joinedRead,joinedHidden.trans hidden,agreement,joint,encoded,?_⟩
      intro column row bounded
      rw [operator]
      exact represented column row bounded)
  refine ⟨choice,condition,frame,output,beforeCodes,afterCodes,returned,results,
    inputRead,layoutsEq,outputRead,bodyRead,?_,related⟩
  rw [actualStep,original_arm_run trace choice history,bodyRead]
  exact merged

#print axioms original_arm_run
#print axioms original_branch_join
end Qleisli.RuntimeOriginalBranchJoin
