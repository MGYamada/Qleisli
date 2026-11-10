import Qleisli.RuntimeCallHistoryRun
import Qleisli.RuntimeStructuralHistory

/-! The original source argument assignment supplies the child input of a
paired native call. Each physical spectator slice retains the full source
operator and the earlier ordinary and hidden history.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open Semantics.Finite (gather)
open Semantics.Observation (Event readOps)
open RuntimeOwnerMap (Map)
open RuntimeForestCode (forestAxes carrierOwners sparseEntry)
open RuntimeCallTraceFrames (Partition WireOrder)
open RuntimePureBody (Step runBlockCore)
open Qleisli.RuntimeNamedChildRuns (ChildRun)
open Qleisli.RuntimeSemanticForest (Frame action product)
open Qleisli.RuntimeSparseNamedBoundary (inputFibre actual_named_entry)
open Qleisli.RuntimeSparseBlockEncoding (coefficient coefficient_scatter)
open Qleisli.RuntimeForestRegroup (sourceDimension)
open Qleisli.RuntimeNamedHeadCoefficients (fibre)
open Qleisli.MixedRadix (recode)
open Qleisli.Semantics.Exact (scalar)
open Qleisli.RuntimeStructuralHistory (Represents)
open Qleisli.Semantics.ObservingAction (History run)

/-- Keep an arbitrary correlated source coefficient on the physical
spectator coordinate of the original caller row. -/
noncomputable def coordinateFibre {Reference : Type}
    (incoming selected spectators : Map) (high : Nat)
    (joint : Nat → Reference → ℂ) : Nat → Reference → ℂ :=
  fibre (product selected).labels.length (product spectators).labels.length
    (fun digit => scalar (sparseEntry (.ofLayout (product spectators)) high digit))
    (fun logical ref => joint (recode (selected++spectators) incoming (sourceDimension incoming) logical) ref)

theorem inputFibre_coordinate {Reference : Type}
    (incoming selected spectators : Map) (physicalFrame axes : List Nat)
    (disjoint : (forestAxes physicalFrame spectators).Disjoint axes)
    (row : Nat) (joint : Nat → Reference → ℂ) :
    inputFibre incoming selected spectators physicalFrame axes row joint =
      coordinateFibre incoming selected spectators (gather row (forestAxes physicalFrame spectators)) joint := by
  unfold inputFibre coordinateFibre
  have same : coefficient spectators physicalFrame (Semantics.Finite.scatter row axes 0) =
      coefficient spectators physicalFrame row := by
    funext digit
    exact coefficient_scatter spectators physicalFrame axes disjoint row 0 digit
  rw [same]
  rfl

/-- The child receives the original sparse source input and the complete
inherited history. Each spectator row supplies one source input operator. -/
noncomputable def inputHistory {bindings : Map}
    (frame : Frame bindings) (physical : List Nat) (incoming selected spectators : Map)
    (joint : Nat → Nat → ℂ) (actual : History) (high : Nat) : History :=
  {actual with operator := action frame physical (coordinateFibre incoming selected spectators high joint)}

private theorem original_child_history
    {dependencies program block start count inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    {roles bindings} (checked : RuntimeOwnerMap.Checked roles scope.interval.before)
    (same : checked.bindings = before.bindings) (parent : Frame checked.bindings) (frame : Frame bindings)
    (actual : History) (joint : Nat → Nat → ℂ)
    (represented : Represents parent scope.interval.before actual joint)
    (entry : ∀ row col, action parent scope.interval.before.quantum.frame joint row col =
      action frame scope.prepared.block.entry.quantum.frame
        (inputFibre checked.bindings boundary.input.ordered
          (RuntimeSelectionPartition.complement checked.bindings boundary.input.ordered)
          scope.interval.before.quantum.frame (RuntimeNamedFrameAxes.mixedAxes scope) row joint)
        (gather row (RuntimeNamedFrameAxes.mixedAxes scope)) col) :
    let selected := boundary.input.ordered
    let spectators := RuntimeSelectionPartition.complement checked.bindings selected
    let localHistory := inputHistory frame scope.prepared.block.entry.quantum.frame checked.bindings selected
      spectators joint actual
    Agrees scope.interval.before.quantum.reference scope.prepared.block.entry.quantum.reference
      (spectators.map (·.port)) actual localHistory := by
  intro selected spectators localHistory
  have partition := RuntimeNamedBlockEncoding.original_named_partition_geometry scope boundary checked same
  have apart := RuntimeNamedBlockSpectators.partition_axes_disjoint checked scope.interval.history.1
    selected spectators partition
  have inputAxes := (RuntimeNamedFrameAxes.mixed_bound_axes scope boundary).2.2
  have disjoint : (forestAxes scope.interval.before.quantum.frame spectators).Disjoint
      (RuntimeNamedFrameAxes.mixedAxes scope) := by
    rw [inputAxes]
    exact apart
  have actualAxes : RuntimeNamedFrameAxes.mixedAxes scope =
      scope.prepared.block.entry.quantum.frame.map scope.interval.before.quantum.frame.idxOf := by
    have frameEq := congrArg Semantics.RawTrace.Interface.frame
      (RuntimeNamedFrameAxes.mixedAxes_input scope).2.2.1
    change scope.prepared.block.entry.quantum.frame = scope.selected.flatMap (·.wires) at frameEq
    unfold RuntimeNamedFrameAxes.mixedAxes RuntimeForestCode.portAxes
    rw [frameEq]
  have spectatorAxes : forestAxes scope.interval.before.quantum.frame spectators =
      (WireOrder (spectators.map (·.port))).map scope.interval.before.quantum.frame.idxOf := by
    simp only [forestAxes,List.flatMap_map]
  refine ⟨fun _ => rfl,fun _ => rfl,?_⟩
  intro row col bounded
  change actual.operator row col =
    action frame scope.prepared.block.entry.quantum.frame
      (coordinateFibre checked.bindings selected spectators
        (gather row ((WireOrder (spectators.map (·.port))).map scope.interval.before.quantum.frame.idxOf)) joint)
      (gather row (scope.prepared.block.entry.quantum.frame.map scope.interval.before.quantum.frame.idxOf)) col
  rw [represented col row bounded,entry,inputFibre_coordinate _ _ _ _ _ disjoint,spectatorAxes,actualAxes]

/-- The paired history starts at the actual child argument assignment and
checked sparse owner frame, before reading either original operation list. -/
def NamedHistoryEntry {dependencies program block} : Step dependencies program block → Prop
  | .named (start := start) (count := count) (before := before) (ordinary := ordinary) _ scope body _ boundary _ _ =>
    ∃ input : RuntimeOwnerMap.Checked (SourceTypes.SourceRuntimeScope.Subject.whole body).initialRoles
        scope.prepared.block.entry,
    ∃ assigned : Map,
      RuntimeInterval.Computed (RuntimeSourceBoundary.bindings
        (SourceTypes.SourceRuntimeScope.Subject.whole body).initialRoles
        ((scope.selected.zip (boundary.input.ordered.map (·.owner))).map fun (port,role) =>
          (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner))) assigned ∧
      RuntimeInterval.Computed (RuntimePureBody.reordered
        (SourceTypes.SourceRuntimeScope.Subject.whole body).initialRoles scope.prepared.block.entry assigned) input ∧
      carrierOwners input.bindings = carrierOwners boundary.input.ordered ∧
      ∀ {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before)
        (parent : Frame checked.bindings), checked.bindings = before.bindings →
        ∃ frame : Frame input.bindings,
        ∀ (joint : Nat → Nat → ℂ) (actual : History),
          Represents parent scope.interval.before actual joint →
          let selected := boundary.input.ordered
          let spectators := RuntimeSelectionPartition.complement checked.bindings selected
          let localHistory := inputHistory frame scope.prepared.block.entry.quantum.frame checked.bindings selected
            spectators joint actual
          Agrees scope.interval.before.quantum.reference scope.prepared.block.entry.quantum.reference
            (spectators.map (·.port)) actual localHistory ∧
          (∀ high, Represents frame scope.prepared.block.entry (localHistory high)
            (coordinateFibre checked.bindings selected spectators high joint)) ∧
          (∀ ordinals, RuntimeOrdinarySSA.Agreement
            (RuntimeOrdinaryBody.valuation ordinals ordinary.measurements actual.values) actual.values ordinary.table →
            ∀ high, RuntimeOrdinarySSA.Agreement
              (RuntimeOrdinaryBody.valuation ordinals scope.visible.ssa.measurements (localHistory high).values)
              (localHistory high).values scope.visible.ssa.table) ∧
          ∀ {parentEvents : List Event} {parents : List History},
            readOps block.fuel scope.interval.before.quantum.reference ((block.operations.drop start).take count) =
              some (scope.interval.after.quantum.reference,parentEvents) →
            run dependencies block.fuel parentEvents actual = some parents →
            ∃ childEvents children, CheckedCallRun scope (spectators.map (·.port)) actual localHistory
              parentEvents childEvents parents children
  | _ => True

theorem actual_named_history_entry {artifact root execution fuel program block step}
    (call : @ChildRun artifact root execution
      (runBlockCore artifact root execution (fuel+1)) program block step) :
    NamedHistoryEntry step := by
  have entry := actual_named_entry call
  cases call with
  | @named start count inputs caller before ordinary event scope body bodyRead
      rootOwner rootName path request plan assigned result receipts boundary
      beforeInput afterInput afterChild inputRead childRead =>
    obtain ⟨input,assigned,assignedRead,ordered,aliases,source⟩ := entry
    refine ⟨input,assigned,assignedRead,ordered,aliases,?_⟩
    intro roles checked parent same
    obtain ⟨frame,law⟩ := source checked parent same
    refine ⟨frame,?_⟩
    intro joint actual represented
    have paired := original_child_history scope boundary checked same parent frame actual joint represented (law joint)
    refine ⟨paired,fun _ _ _ _ => rfl,fun ordinals agrees => visible_child_input scope ordinals actual _
      paired.values agrees,?_⟩
    intro parentEvents parents read executed
    exact original_call_run scope boundary checked same actual _ paired read executed

#print axioms inputFibre_coordinate
#print axioms actual_named_history_entry
end Qleisli.RuntimeCallHistory
