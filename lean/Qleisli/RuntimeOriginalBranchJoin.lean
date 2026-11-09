import Qleisli.RuntimeOriginalClassicalJoin
import Qleisli.RuntimeOriginalQuantumPhi
import Qleisli.RuntimeObservingValueRetention

/-! A literal original conditional composes the selected recursive arm, its
quantum return permutation, and the simultaneous classical phi merge on the
same ordered family of histories.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeOriginalBranchJoin
open QleisliKernel QleisliKernel.Qirf
open RuntimeForestCode (Frame)
open RuntimeOwnerCodeReindex (dimensionAt)
open RuntimeOrdinarySSA (Agreement bitValue)
open Qleisli.RuntimeObservingValueRetention (Supports run_values)
open Qleisli.RuntimeObservingPrefix (Issued issued_mono)
open Qleisli.RuntimeOriginalQuantumPhi (armBindings outputBindings original_quantum_phi_action)
open Qleisli.RuntimeForestRegroup (sourceDimension dimensionAt_source)
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

/-- Logical coordinate transport through the source owners bound to the
actual phi. Cardinalities come from the original basis trees. -/
def sourcePhiIndex {dependencies program block offset actual source spectators leftRoles rightRoles outputRoles left right}
    (bound : @RuntimeOwnerPhis.Bound dependencies program block offset actual source spectators
      leftRoles rightRoles outputRoles left right) (choice : Bool) (logical : Nat) : Nat :=
  let incoming := (armChecked left right choice).bindings
  Qleisli.MixedRadix.recode (armBindings bound choice) incoming (sourceDimension incoming)
    (Qleisli.MixedRadix.recode bound.output.bindings (outputBindings bound) (sourceDimension (outputBindings bound)) logical)

def armPermutation {dependencies program block offset}
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

/-- Carry each expected source result through the original selected arm's
quantum return permutation and simultaneous classical phi merge. The output
operator uses the same source result that was paired with the child history. -/
theorem original_branch_join_with {sources rootOwner rootName caller name dependencies program block offset
    path event source actual before left right ordinary leftOrdinary rightOrdinary}
    (action : @RuntimeBranchAction.Checked sources rootOwner rootName caller name dependencies program block offset
      path event source actual before left right ordinary leftOrdinary rightOrdinary)
    (trace : RuntimeOriginalBranch.Trace actual)
    (input : List Nat) (member : input ∈ action.condition.inputs.rows) (bits : List Bool)
    (width : bits.length = ordinary.measurements.length) (history : History)
    {SourceResult : Type} (sourceRun : Bool → Option (List SourceResult))
    (operator : SourceResult → Nat → Nat → ℂ) (outcomes : SourceResult → List Nat)
    (retains : SourceResult → Prop)
    (ArmOperator : Bool → (Nat → Nat → ℂ) → (Nat → Nat → ℂ) → Prop)
    (OutputOperator : (Nat → Nat → ℂ) → (Nat → Nat → ℂ) → Prop)
    (transportOperator : ∀ choice (joint : Nat → Nat → ℂ) (current : History),
      ArmOperator choice current.operator joint →
      OutputOperator (pureHistory dependencies [armPermutation actual choice] current).operator
        (fun row column => joint (sourcePhiIndex action.ownerPhis choice row) column)) :
    let reference := RuntimeBranchCondition.reference input ordinary.measurements bits
    Agreement reference history.values ordinary.table →
    Supports (Issued actual.interval.before) history →
    (∀ choice,
      Semantics.SourceOrdinary.evaluate reference action.condition.required = some (bitValue choice) →
      ∃ expected : List SourceResult, ∃ returned : List History,
        sourceRun choice = some expected ∧
        run dependencies actual.childFuel (trace.armBody choice) history = some returned ∧
        List.Forall₂ (fun logical result =>
          retains logical ∧ result.hidden = outcomes logical ∧
          Agreement reference result.values (if choice then leftOrdinary.table else rightOrdinary.table) ∧
          ArmOperator choice result.operator (operator logical)) expected returned) →
    ∃ choice,
      Semantics.SourceOrdinary.evaluate reference action.condition.required = some (bitValue choice) ∧
      ∃ expected : List SourceResult, ∃ returned results : List History,
        sourceRun choice = some expected ∧
        run dependencies actual.childFuel (trace.armBody choice) history = some returned ∧
        step dependencies (run dependencies actual.childFuel)
          (RuntimeOriginalBranch.branchEvent actual trace.left trace.right) history = some results ∧
        List.Forall₂ (fun logical joined =>
          retains logical ∧ joined.hidden = outcomes logical ∧ Agreement reference joined.values action.ordinaryAfter.table ∧
          OutputOperator joined.operator (fun row column =>
            operator logical (sourcePhiIndex action.ownerPhis choice row) column)) expected results := by
  intro reference agrees incoming armProof
  obtain ⟨choice,condition,actualStep⟩ := RuntimeOriginalBranch.original_branch_step action.condition trace
    (run dependencies actual.childFuel) input member bits width history agrees
  obtain ⟨expected,returned,sourceRead,bodyRead,paired⟩ := armProof choice condition
  obtain ⟨kept,writes⟩ := RuntimeOriginalBranch.original_arm_writes trace choice
  have supported : Supports (Issued (if choice then actual.thenState else actual.elseState)) history := by
    intro id member
    exact issued_mono kept (incoming member)
  have historyFacts := run_values dependencies actual.childFuel (trace.armBody choice) history _ writes supported bodyRead
  let transport := pureHistory dependencies [armPermutation actual choice]
  have mergeStep : ∀ logical current, current ∈ returned →
      (retains logical ∧ current.hidden = outcomes logical ∧
        Agreement reference current.values (if choice then leftOrdinary.table else rightOrdinary.table) ∧
        ArmOperator choice current.operator (operator logical)) →
      ∃ joined, merge choice actual.classical (transport current) = some joined ∧
        retains logical ∧ joined.hidden = outcomes logical ∧ Agreement reference joined.values action.ordinaryAfter.table ∧
        OutputOperator joined.operator (fun row column =>
          operator logical (sourcePhiIndex action.ownerPhis choice row) column) := by
      intro logical current present ⟨keptSource,outcome,selected,encoded⟩
      obtain ⟨retained,issued⟩ := historyFacts current present
      have represented := transportOperator choice (operator logical) current encoded
      have values : (transport current).values = current.values := rfl
      have old : Agreement reference (transport current).values ordinary.table := by
        rw [values]
        intro id expression present
        obtain ⟨bit,known,sourceValue⟩ := agrees id expression present
        exact ⟨bit,retained id bit known,sourceValue⟩
      obtain ⟨joined,joinedRead,joinedHidden,sameOperator,agreement⟩ :=
        RuntimeOriginalClassicalJoin.original_merge_agrees action reference choice (transport current)
          condition old (by rwa [values]) (by rwa [values])
      exact ⟨joined,joinedRead,keptSource,joinedHidden.trans outcome,agreement,sameOperator.symm ▸ represented⟩
  obtain ⟨results,merged,related⟩ :=
    RuntimeOriginalClassicalJoin.merge_paired_family choice actual.classical transport paired mergeStep
  refine ⟨choice,condition,expected,returned,results,sourceRead,bodyRead,?_,related⟩
  rw [actualStep,original_arm_run trace choice history,bodyRead]
  exact merged

/-- Carry each expected source result through the original selected arm's
quantum return permutation and simultaneous classical phi merge. The output
operator uses the same source result that was paired with the child history. -/
theorem original_branch_join {sources rootOwner rootName caller name dependencies program block offset
    path event source actual before left right ordinary leftOrdinary rightOrdinary}
    (action : @RuntimeBranchAction.Checked sources rootOwner rootName caller name dependencies program block offset
      path event source actual before left right ordinary leftOrdinary rightOrdinary)
    (trace : RuntimeOriginalBranch.Trace actual)
    (input : List Nat) (member : input ∈ action.condition.inputs.rows) (bits : List Bool)
    (width : bits.length = ordinary.measurements.length) (history : History)
    {SourceResult : Type} (sourceRun : Bool → Option (List SourceResult))
    (operator : SourceResult → Nat → Nat → ℂ) (outcomes : SourceResult → List Nat)
    (retains : SourceResult → Prop) :
    let reference := RuntimeBranchCondition.reference input ordinary.measurements bits
    Agreement reference history.values ordinary.table →
    Supports (Issued actual.interval.before) history →
    (∀ choice,
      Semantics.SourceOrdinary.evaluate reference action.condition.required = some (bitValue choice) →
      ∃ expected : List SourceResult, ∃ returned : List History,
        sourceRun choice = some expected ∧
        run dependencies actual.childFuel (trace.armBody choice) history = some returned ∧
        List.Forall₂ (fun logical result =>
          retains logical ∧ result.hidden = outcomes logical ∧
          Agreement reference result.values (if choice then leftOrdinary.table else rightOrdinary.table) ∧
          ∃ frame : Frame (armChecked action.thenFrame action.elseFrame choice),
            RepresentsOperator frame result (operator logical)) expected returned) →
    ∃ choice,
      Semantics.SourceOrdinary.evaluate reference action.condition.required = some (bitValue choice) ∧
      ∃ expected : List SourceResult, ∃ returned results : List History,
        sourceRun choice = some expected ∧
        run dependencies actual.childFuel (trace.armBody choice) history = some returned ∧
        step dependencies (run dependencies actual.childFuel)
          (RuntimeOriginalBranch.branchEvent actual trace.left trace.right) history = some results ∧
        List.Forall₂ (fun logical joined =>
          retains logical ∧ joined.hidden = outcomes logical ∧ Agreement reference joined.values action.ordinaryAfter.table ∧
          ∃ output : Frame action.ownerPhis.output,
            RepresentsOperator output joined (fun row column =>
              operator logical (sourcePhiIndex action.ownerPhis choice row) column)) expected results := by
  refine original_branch_join_with action trace input member bits width history sourceRun operator outcomes retains
    (fun choice actualOperator joint =>
      ∃ frame : Frame (armChecked action.thenFrame action.elseFrame choice),
        ∀ col, RawFiniteRows.OnRows _ (fun row => actualOperator row col)
          (fun row => referenceAction frame joint row col))
    (fun actualOperator joint =>
      ∃ frame : Frame action.ownerPhis.output,
        ∀ col, RawFiniteRows.OnRows _ (fun row => actualOperator row col)
          (fun row => referenceAction frame joint row col)) ?_
  intro choice joint current ⟨frame,encoded⟩
  let arm := armChecked action.thenFrame action.elseFrame choice
  have sameBindings : arm.bindings = if choice then action.thenFrame.bindings else action.elseFrame.bindings := by
    cases choice <;> rfl
  obtain ⟨output,_,afterCodes,_,_,_,_,quantum⟩ :=
    original_quantum_phi_action actual action.ownerPhis trace choice arm sameBindings frame
  obtain ⟨moved,ran,_,_,represented⟩ :=
    quantum (run dependencies (actual.childFuel-1)) joint current encoded
  have literal : step dependencies (run dependencies (actual.childFuel-1))
      (RuntimeOriginalBranch.armFinish (if choice then actual.thenState else actual.elseState).quantum.reference
        actual.quantum choice) current = some [pureHistory dependencies [armPermutation actual choice] current] := rfl
  have same : moved = pureHistory dependencies [armPermutation actual choice] current :=
    List.cons.inj (Option.some.inj (ran.symm.trans literal)) |>.1
  subst moved
  refine ⟨output,?_⟩
  intro column row bounded
  dsimp only [sourcePhiIndex]
  rw [← funext (dimensionAt_source frame.owners),← funext (dimensionAt_source afterCodes)]
  exact represented column row bounded

#print axioms original_arm_run
#print axioms original_branch_join_with
#print axioms original_branch_join
end Qleisli.RuntimeOriginalBranchJoin
