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
open Qleisli.RuntimeSemanticForest (Frame action product frame_exists)
open Qleisli.RuntimeSparseNamedBoundary (inputFibre actual_named_entry)
open Qleisli.RuntimeSparseBlockEncoding (available_carriers coefficient coefficient_scatter sparse_caller_input)
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

/-- Produce each child history from the original ordered ports and the
caller's complete history, which may contain earlier classical values. -/
private theorem child_history_from_partition
    {dependencies program block start count childProgram}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (prepared : RuntimeInterval.Prepared dependencies childProgram)
    (selected spectators : Map)
    {roles bindings} (checked : RuntimeOwnerMap.Checked roles interval.before)
    (geometry : (selected ++ spectators).Perm checked.bindings)
    (selectedFrame : prepared.block.entry.quantum.frame = WireOrder (selected.map (·.port)))
    (parent : Frame checked.bindings) (frame : Frame bindings)
    (actual : History) (joint : Nat → Nat → ℂ)
    (represented : Represents parent interval.before actual joint)
    (entry : ∀ row col, action parent interval.before.quantum.frame joint row col =
      action frame prepared.block.entry.quantum.frame
        (inputFibre checked.bindings selected spectators interval.before.quantum.frame
          (forestAxes interval.before.quantum.frame selected) row joint)
        (gather row (forestAxes interval.before.quantum.frame selected)) col) :
    let localHistory := inputHistory frame prepared.block.entry.quantum.frame checked.bindings selected
      spectators joint actual
    Agrees interval.before.quantum.reference prepared.block.entry.quantum.reference
      (spectators.map (·.port)) actual localHistory := by
  intro localHistory
  have apart := RuntimeNamedBlockSpectators.partition_axes_disjoint checked interval.history.1
    selected spectators geometry
  have actualAxes : forestAxes interval.before.quantum.frame selected =
      prepared.block.entry.quantum.frame.map interval.before.quantum.frame.idxOf := by
    rw [selectedFrame]
    simp only [forestAxes,List.flatMap_map]
  have spectatorAxes : forestAxes interval.before.quantum.frame spectators =
      (WireOrder (spectators.map (·.port))).map interval.before.quantum.frame.idxOf := by
    simp only [forestAxes,List.flatMap_map]
  refine ⟨fun _ => rfl,fun _ => rfl,?_⟩
  intro row col bounded
  change actual.operator row col =
    action frame prepared.block.entry.quantum.frame
      (coordinateFibre checked.bindings selected spectators
        (gather row ((WireOrder (spectators.map (·.port))).map interval.before.quantum.frame.idxOf)) joint)
      (gather row (prepared.block.entry.quantum.frame.map interval.before.quantum.frame.idxOf)) col
  rw [represented col row bounded,entry,inputFibre_coordinate _ _ _ _ _ apart,spectatorAxes,actualAxes]

theorem prepared_partition_history
    {dependencies program block start count childProgram}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (prepared : RuntimeInterval.Prepared dependencies childProgram)
    (selected spectators : Map) {roles childBindings}
    (checked : RuntimeOwnerMap.Checked roles interval.before)
    (geometry : (selected ++ spectators).Perm checked.bindings)
    (ports : childProgram.inputs = selected.map (·.port))
    (sameCarriers : carrierOwners childBindings = carrierOwners selected)
    (parent : Frame checked.bindings) (actual : History) (joint : Nat → Nat → ℂ)
    (represented : Represents parent interval.before actual joint) :
    ∃ frame : Frame childBindings,
      Agrees interval.before.quantum.reference prepared.block.entry.quantum.reference
        (spectators.map (·.port)) actual
        (inputHistory frame prepared.block.entry.quantum.frame checked.bindings selected spectators joint actual) := by
  have initial := RuntimeNamedFrameAxes.initialized prepared.inputRead
  have childValid := Raw.Ownership.valid _ initial.2.1
  have selectedAvailable : Qleisli.RuntimeSemanticForest.Available selected :=
    fun binding member => parent.available binding (geometry.subset (List.mem_append_left _ member))
  obtain ⟨frame⟩ := frame_exists (available_carriers sameCarriers selectedAvailable)
  have localFrame := congrArg Semantics.RawTrace.Interface.frame initial.1
  change prepared.block.entry.quantum.frame = WireOrder childProgram.inputs at localFrame
  rw [ports] at localFrame
  have actionEq := sparse_caller_input checked parent interval.history.1 geometry frame sameCarriers
    prepared.block.entry.quantum.frame (by simpa only [List.flatMap_map] using localFrame) childValid.frame joint
  exact ⟨frame,child_history_from_partition interval prepared selected spectators checked geometry
    localFrame parent frame actual joint represented actionEq⟩

/-- Lift the native prepared input's original ports and the checked source
carrier order to the paired history of the actual call. -/
theorem prepared_child_history
    {dependencies program block start count childProgram inputs sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (prepared : RuntimeInterval.Prepared dependencies childProgram)
    (boundary : RuntimeNamedBoundary.Checked interval inputs event before child retired value)
    (ports : childProgram.inputs = boundary.input.ordered.map (·.port))
    {roles childBindings} (checked : RuntimeOwnerMap.Checked roles interval.before)
    (sameBindings : checked.bindings = before.bindings)
    (sameCarriers : carrierOwners childBindings = carrierOwners boundary.input.ordered)
    (parent : Frame checked.bindings) (actual : History) (joint : Nat → Nat → ℂ)
    (represented : Represents parent interval.before actual joint) :
    let selected := boundary.input.ordered
    let spectators := RuntimeSelectionPartition.complement checked.bindings selected
    ∃ frame : Frame childBindings,
      Agrees interval.before.quantum.reference prepared.block.entry.quantum.reference
        (spectators.map (·.port)) actual
        (inputHistory frame prepared.block.entry.quantum.frame checked.bindings selected spectators joint actual) := by
  intro selected spectators
  have initial := RuntimeNamedFrameAxes.initialized prepared.inputRead
  have childValid := Raw.Ownership.valid _ initial.2.1
  have initialPorts : prepared.block.entry.quantum.live = childProgram.inputs :=
    congrArg Semantics.RawTrace.Interface.live initial.1
  have tokens := childValid.owners
  change (prepared.block.entry.quantum.live.map (·.token)).Nodup at tokens
  rw [initialPorts,ports,List.map_map] at tokens
  exact prepared_partition_history prepared selected spectators checked
    (RuntimeNamedBlockEncoding.named_partition_geometry boundary checked sameBindings tokens)
    ports sameCarriers parent actual joint represented

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

theorem named_history_entry_of_entry {dependencies program block start count args ordinary sources caller before child retired}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    {scope : @RuntimeCallScope.Checked dependencies program block start count args ordinary event.effect}
    {body : SourceTypes.SourceRuntimeTrace.Body event.target.signature}
    {bodyRead : SourceTypes.SourceRuntimeTrace.NamedRead event body}
    {boundary : RuntimeNamedBoundary.Checked scope.interval args event before child retired body.checked.summary.value}
    {finalOrdinary} {steps : RuntimePureBody.Steps dependencies scope.program scope.prepared.block}
    (entry : Qleisli.RuntimeSparseNamedBoundary.NamedEntry (.named event scope body bodyRead boundary finalOrdinary steps)) :
    NamedHistoryEntry (.named event scope body bodyRead boundary finalOrdinary steps) := by
  simp only [Qleisli.RuntimeSparseNamedBoundary.NamedEntry] at entry
  obtain ⟨input,assigned,assignedRead,ordered,aliases,source⟩ := entry
  refine ⟨input,assigned,assignedRead,ordered,aliases,?_⟩
  intro roles checked parent same
  obtain ⟨frame,law⟩ := source checked parent same
  refine ⟨frame,?_⟩
  intro joint actual represented
  have geometry := RuntimeNamedBlockEncoding.original_named_partition_geometry scope boundary checked same
  have frameRead := congrArg Semantics.RawTrace.Interface.frame (RuntimeNamedFrameAxes.mixedAxes_input scope).2.2.1
  have selectedFrame : scope.prepared.block.entry.quantum.frame = WireOrder (boundary.input.ordered.map (·.port)) := by
    change scope.prepared.block.entry.quantum.frame = scope.selected.flatMap (·.wires) at frameRead
    simpa only [RuntimeNamedFrameAxes.mixed_bound_ports scope boundary] using frameRead
  have entry := law joint
  rw [(RuntimeNamedFrameAxes.mixed_bound_axes scope boundary).2.2] at entry
  have paired := child_history_from_partition scope.interval scope.prepared boundary.input.ordered
    (RuntimeSelectionPartition.complement checked.bindings boundary.input.ordered) checked geometry
    selectedFrame parent frame actual joint represented entry
  refine ⟨paired,fun _ _ _ _ => rfl,fun ordinals agrees => visible_child_input scope ordinals actual _
    paired.values agrees,?_⟩
  intro parentEvents parents read executed
  exact original_call_run scope boundary checked same actual _ paired read executed

theorem actual_named_history_entry {artifact root execution fuel program block step}
    (call : @ChildRun artifact root execution
      (runBlockCore artifact root execution (fuel+1)) program block step) :
    NamedHistoryEntry step := by
  have entry := actual_named_entry call
  cases call
  exact named_history_entry_of_entry entry

#print axioms inputFibre_coordinate
#print axioms child_history_from_partition
#print axioms prepared_partition_history
#print axioms prepared_child_history
#print axioms actual_named_history_entry
end Qleisli.RuntimeCallHistory
