import Qleisli.RuntimeCallHistoryEntry

/-! Return the child's logical operator in the original caller owner order.
The output uses the same spectator slice as the paired actual histories.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open Semantics.Finite (gather)
open RuntimeOwnerMap (Map)
open RuntimeForestCode (forestAxes sparseEntry)
open RuntimeCallTraceFrames (WireOrder)
open Qleisli.RuntimeSemanticForest (Frame action product)
open Qleisli.RuntimeSparseBlockEncoding (blockJoint coefficient)
open Qleisli.RuntimeSparseNamedBoundary (caller_return_action)
open Qleisli.RuntimeForestRegroup (sourceDimension)
open Qleisli.RuntimeStructuralHistory (Represents)
open Qleisli.RuntimeForestProduct (gather_bound)
open Qleisli.MixedRadix (recode)
open Qleisli.Semantics.Exact (scalar)
open Qleisli.Semantics.ObservingAction (History)

/-- Restrict an ordered logical child return family to a physical spectator
slice, retaining its reference column and exact sparse coefficients. -/
noncomputable def returnFibre {Reference : Type} (spectators : Map) (high : Nat)
    (joint : Nat → Nat → Reference → ℂ) (digit : Nat) (reference : Reference) : ℂ :=
  ((List.range (product spectators).labels.length).map fun logical =>
    scalar (sparseEntry (.ofLayout (product spectators)) high logical) * joint digit logical reference).sum

/-- Restore the caller owner order from the written child return and the
unchanged spectator owners. Logical dimensions include Unit owners. -/
noncomputable def returnedOperator {Reference : Type} (child output mapped spectators : Map)
    (joint : Nat → Nat → Reference → ℂ) (logical : Nat) (reference : Reference) : ℂ :=
  let order := mapped++spectators
  blockJoint (product mapped).labels.length
    (fun digit high ref => joint (recode child child (sourceDimension child) digit) high ref)
    (recode output order (sourceDimension order) logical) reference

/-- The actual ordered result pair determines the caller's encoded operator
when the original child source return is known on each spectator slice. -/
theorem original_call_return
    {dependencies program block start count inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before)
    (parent : Frame checked.bindings) (sameBindings : checked.bindings = before.bindings)
    (returned : Frame child.bindings) :
    let spectators := RuntimeSelectionPartition.complement checked.bindings boundary.input.ordered
    ∃ output : Frame boundary.afterFrame.bindings,
      ∀ (actual : History) (localResults : Nat → History) (joint : Nat → Nat → Nat → ℂ),
        Agrees scope.interval.after.quantum.reference scope.localAfter.quantum.reference
          (spectators.map (·.port)) actual localResults →
        (∀ high, Represents returned scope.localAfter (localResults high) (returnFibre spectators high joint)) →
        Represents output scope.interval.after actual
          (returnedOperator child.bindings boundary.afterFrame.bindings boundary.mapped spectators joint) := by
  intro spectators
  obtain ⟨output,encoded⟩ := caller_return_action scope boundary checked parent sameBindings returned
  refine ⟨output,?_⟩
  intro actual localResults joint paired childReturn col row bounded
  let physical := scope.interval.after.quantum.reference
  let localFrame := scope.localAfter.quantum.reference
  let high := project physical (WireOrder (spectators.map (·.port))) row
  let low := project physical localFrame.frame row
  have lowBound : low < 2^scope.localAfter.quantum.frame.length := by
    simpa only [low,project,Semantics.RawTrace.axes,List.length_map] using
      gather_bound row (Semantics.RawTrace.axes physical localFrame.frame)
  have highEq : high = gather row (forestAxes physical.frame spectators) := by
    simp only [high,project,Semantics.RawTrace.axes,forestAxes,List.flatMap_map]
  have fibreEq : returnFibre spectators high joint =
      (fun digit ref => ((List.range (product spectators).labels.length).map fun h =>
        coefficient spectators physical.frame row h * joint digit h ref).sum) := by
    rw [highEq]
    rfl
  calc
    actual.operator row col = (localResults high).operator low col := paired.operator row col bounded
    _ = action returned localFrame.frame (returnFibre spectators high joint) low col :=
      childReturn high col low lowBound
    _ = action output physical.frame
        (returnedOperator child.bindings boundary.afterFrame.bindings boundary.mapped spectators joint) row col := by
      rw [fibreEq]
      exact (encoded joint row col).symm

/-- Return the complete actual family in order using the same checked
caller frame for every result. Duplicate and zero results remain present. -/
theorem original_call_returns
    {dependencies program block start count inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before)
    (parent : Frame checked.bindings) (sameBindings : checked.bindings = before.bindings)
    (returned : Frame child.bindings)
    {parents : List History} {children : List (Nat → History)} {joints : List (Nat → Nat → Nat → ℂ)} :
    let spectators := RuntimeSelectionPartition.complement checked.bindings boundary.input.ordered
    List.Forall₂ (Agrees scope.interval.after.quantum.reference scope.localAfter.quantum.reference
      (spectators.map (·.port))) parents children →
    List.Forall₂ (fun localResults joint =>
      ∀ high, Represents returned scope.localAfter (localResults high) (returnFibre spectators high joint)) children joints →
    ∃ output : Frame boundary.afterFrame.bindings,
      List.Forall₂ (fun actual joint => Represents output scope.interval.after actual
        (returnedOperator child.bindings boundary.afterFrame.bindings boundary.mapped spectators joint)) parents joints := by
  intro spectators paired childReturns
  obtain ⟨output,encoded⟩ := original_call_return scope boundary checked parent sameBindings returned
  refine ⟨output,?_⟩
  induction paired generalizing joints with
  | nil =>
    cases childReturns
    exact .nil
  | cons agrees _ ih =>
    cases childReturns with
    | cons represented rest =>
      exact .cons (encoded _ _ _ agrees represented) (ih rest)

#print axioms original_call_return
#print axioms original_call_returns
end Qleisli.RuntimeCallHistory
