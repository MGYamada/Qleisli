import Qleisli.RuntimeCallHistoryScope
import Qleisli.RuntimeSparseNamedBoundary

/-! Run the original named child on the source-derived entry histories.
Earlier classical values stay available, and all new IDs come from the
actual child native check.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open Semantics.Observation (Event readOps)
open Semantics.Raw (Port)
open RuntimeCallTraceFrames (Partition)
open Qleisli.RuntimeObservingPrefix (Issued)
open Qleisli.RuntimeObservingValueRetention (Supports run_values)
open Qleisli.RuntimeSparseNamedBoundary (visible_entry_agreement)
open Qleisli.Semantics.ObservingAction (History run)

structure CheckedCallRun
    {dependencies program block start count inputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (spectators : List Port) (actual : History) (localHistory : Nat → History)
    (parentEvents childEvents : List Event) (parents : List History) (children : List (Nat → History)) : Prop where
  partition : Partition scope.interval.after.quantum.reference scope.localAfter.quantum.reference spectators
  childRead : readOps scope.prepared.block.fuel scope.prepared.block.entry.quantum.reference scope.prepared.block.operations =
    some (scope.localAfter.quantum.reference,childEvents)
  paired : Results dependencies block.fuel scope.prepared.block.fuel scope.interval.after.quantum.reference
    scope.localAfter.quantum.reference spectators parentEvents childEvents actual localHistory parents children
  parentValues : ∀ result ∈ parents,
    Semantics.OrdinaryValue.Extends actual.values result.values ∧
      Supports (fun id => id ∈ actual.values.map Prod.fst ∨ Issued scope.interval.after id) result
  childValues : ∀ high result, result ∈ children.map (fun history => history high) →
    Semantics.OrdinaryValue.Extends actual.values result.values ∧
      Supports (fun id => id ∈ actual.values.map Prod.fst ∨ Issued scope.localAfter id) result

/-- Relate the result list of the actual caller interval to the original
prepared child run on every spectator slice. Inherited ordinary values and
the complete hidden history are retained in the pairing. -/
theorem original_call_run
    {dependencies program block start count inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before)
    (bindings : checked.bindings = before.bindings)
    (actual : History) (localHistory : Nat → History)
    (agrees : Agrees scope.interval.before.quantum.reference scope.prepared.block.entry.quantum.reference
      ((RuntimeSelectionPartition.complement checked.bindings boundary.input.ordered).map (·.port))
      actual localHistory)
    {parentEvents : List Event} {parents : List History}
    (read : readOps block.fuel scope.interval.before.quantum.reference ((block.operations.drop start).take count) =
      some (scope.interval.after.quantum.reference,parentEvents))
    (executed : run dependencies block.fuel parentEvents actual = some parents) :
    let spectators := (RuntimeSelectionPartition.complement checked.bindings boundary.input.ordered).map (·.port)
    ∃ childEvents children, CheckedCallRun scope spectators actual localHistory
      parentEvents childEvents parents children := by
  intro spectators
  cases depth : block.fuel with
  | zero =>
    rw [depth] at executed
    cases executed
  | succ fuel =>
    obtain ⟨pEvents,cEvents,pRead,cRead,parentWrites,writes,segment⟩ :=
      actual_call_segment scope fuel depth spectators (RuntimeCallTraceFrames.original_entry scope boundary checked bindings)
    rw [depth] at executed
    have sameEvents : pEvents = parentEvents := congrArg Prod.snd (Option.some.inj (pRead.symm.trans read))
    subst pEvents
    obtain ⟨children,results⟩ := segment.transport actual localHistory agrees parents executed
    refine ⟨cEvents,children,⟨segment.partition,cRead,?_,?_,?_⟩⟩
    · simpa only [depth] using results
    · exact run_values dependencies (fuel+1) parentEvents actual _
        (parentWrites.mono (fun _ issued => Or.inr issued)) (fun _ present => Or.inl present) executed
    · intro high result member
      let allowed := fun id => id ∈ actual.values.map Prod.fst ∨ Issued scope.localAfter id
      have support : Supports allowed (localHistory high) := by
        intro id present
        apply Or.inl
        rw [agrees.values high]
        exact present
      have retained := run_values dependencies 65 cEvents (localHistory high) allowed
        (writes.mono (fun _ issued => Or.inr issued)) support (results.childRun high) result member
      rw [← agrees.values high] at retained
      exact retained

/-- The actual child keeps the caller's visible ordinary values on each
physical spectator slice, including expressions evaluated from prior IDs. -/
theorem visible_child_input
    {dependencies program block start count inputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (ordinals : List Nat) (actual : History) (localHistory : Nat → History)
    (same : ∀ high, actual.values = (localHistory high).values)
    (ordinaryAgrees : RuntimeOrdinarySSA.Agreement
      (RuntimeOrdinaryBody.valuation ordinals ordinary.measurements actual.values) actual.values ordinary.table) :
    ∀ high, RuntimeOrdinarySSA.Agreement
      (RuntimeOrdinaryBody.valuation ordinals scope.visible.ssa.measurements (localHistory high).values)
      (localHistory high).values scope.visible.ssa.table := by
  intro high
  rw [← same high]
  exact visible_entry_agreement scope ordinals actual ordinaryAgrees

#print axioms original_call_run
#print axioms visible_child_input
end Qleisli.RuntimeCallHistory
