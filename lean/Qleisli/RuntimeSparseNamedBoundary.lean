import Qleisli.RuntimeSparseBlockEncoding
import Qleisli.RuntimeLiteralHistory
import Qleisli.RuntimeNamedSelectionReturnOrder
import Qleisli.RuntimeSparseSelectionOutput

/-! The actual named child starts on the caller's ordered argument carriers.
Independent sparse frames interpret its input and return with every spectator
and reference amplitude retained.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeSparseNamedBoundary
open QleisliKernel QleisliKernel.Qirf
open Semantics.Finite (gather scatter)
open RuntimeOwnerMap (Map)
open RuntimeForestCode (carrierOwners forestAxes)
open RuntimePureBody (Step runBlockCore)
open RuntimeNamedPrimitiveInputs (bindings_roles reordered_original named_input_carriers)
open Qleisli.RuntimeNamedChildRuns (ChildRun core_flow)
open Qleisli.RuntimeSemanticForest (Frame action product frame_exists)
open Qleisli.RuntimeSparseBlockEncoding (available_carriers blockJoint coefficient sparse_caller_input)
open Qleisli.RuntimeNamedHeadCoefficients (fibre)
open Qleisli.RuntimeForestRegroup (sourceDimension)
open Qleisli.MixedRadix (recode)
open Qleisli.RuntimeLiteralHistory (Agrees)
open Qleisli.RuntimeObservingPrefix (Issued checkOps_reference_with_writes)
open Qleisli.RuntimeObservingValueRetention (Supports run_values)
open Qleisli.Semantics.ObservingAction (History run)
open Semantics.Observation (readOps)

noncomputable def inputFibre {Reference : Type}
    (incoming selected spectators : Map) (physicalFrame axes : List Nat) (row : Nat)
    (joint : Nat → Reference → ℂ) : Nat → Reference → ℂ :=
  fibre (product selected).labels.length (product spectators).labels.length
    (coefficient spectators physicalFrame (scatter row axes 0))
    (fun logical ref => joint (recode (selected++spectators) incoming (sourceDimension incoming) logical) ref)

/-- The whole parent encoding agrees with the child encoding for each
physical spectator row and external reference. The child's source binding
order and physical frame come from the original checked input. -/
def NamedEntry {dependencies program block} : Step dependencies program block → Prop
  | .named (before := before) _ scope body _ boundary _ _ =>
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
        ∀ {Reference : Type} (joint : Nat → Reference → ℂ) row ref,
          action parent scope.interval.before.quantum.frame joint row ref =
            action frame scope.prepared.block.entry.quantum.frame
              (inputFibre checked.bindings boundary.input.ordered
                (RuntimeSelectionPartition.complement checked.bindings boundary.input.ordered)
                scope.interval.before.quantum.frame (RuntimeNamedFrameAxes.mixedAxes scope) row joint)
              (gather row (RuntimeNamedFrameAxes.mixedAxes scope)) ref
  | _ => True

/-- The actual child receipt supplies the argument assignment and reordering.
Its full carriers determine the sparse frame, including dimension-one owners.
The input correspondence holds for any correlated caller state. -/
theorem actual_named_entry {artifact root execution fuel program block step}
    (call : @ChildRun artifact root execution
      (runBlockCore artifact root execution (fuel+1)) program block step) :
    NamedEntry step := by
  cases call with
  | @named start count inputs caller before ordinary event scope body bodyRead
      rootOwner rootName path request plan assigned result receipts boundary
      beforeInput afterInput afterChild inputRead childRead =>
    obtain ⟨input,inputOrdered,_,_,_⟩ := core_flow artifact root execution fuel
      .localScope (.whole body) path scope.program request plan _ scope.visible.ssa
      scope.prepared.block (result,receipts) ⟨afterInput,afterChild,childRead⟩
    have read : RuntimeInterval.Computed _ assigned := ⟨beforeInput,afterInput,inputRead⟩
    have aliases := RuntimeBoundaryOwnerEvidence.bindings_carriers read
    have ordered := reordered_original (bindings_roles read) input inputOrdered
    have same : carrierOwners input.bindings = carrierOwners boundary.input.ordered := by
      rw [ordered,aliases,named_input_carriers scope boundary]
    have framePorts := congrArg Semantics.RawTrace.Interface.frame
      (RuntimeNamedFrameAxes.mixedAxes_input scope).2.2.1
    have localFrame : scope.prepared.block.entry.quantum.frame =
        boundary.input.ordered.flatMap (·.port.wires) := by
      have wires := congrArg (List.flatMap (fun port : Semantics.Raw.Port => port.wires))
        (RuntimeNamedFrameAxes.mixed_bound_ports scope boundary)
      exact framePorts.trans (by simpa only [List.flatMap_map] using wires)
    have axes := (RuntimeNamedFrameAxes.mixed_bound_axes scope boundary).2.2
    have unique : scope.prepared.block.entry.quantum.frame.Nodup := by
      have distinct := (RuntimeNamedFrameAxes.mixedAxes_bounds scope).1
      rw [axes] at distinct
      rw [localFrame]
      exact List.Pairwise.of_map scope.interval.before.quantum.frame.idxOf
        (fun _ _ different equal => different (congrArg scope.interval.before.quantum.frame.idxOf equal)) distinct
    have originalRoles := (RuntimeNamedFrameAxes.mixed_bound_axes scope boundary).1
    refine ⟨input,assigned,?_,inputOrdered,same,?_⟩
    · simpa only [originalRoles] using read
    intro roles checked parent sameBindings
    have partition := RuntimeNamedBlockEncoding.original_named_partition_geometry scope boundary checked sameBindings
    have selectedAvailable : Qleisli.RuntimeSemanticForest.Available boundary.input.ordered :=
      fun binding member => parent.available binding (partition.subset (List.mem_append_left _ member))
    obtain ⟨frame⟩ := frame_exists (available_carriers same selectedAvailable)
    refine ⟨frame,?_⟩
    intro Reference joint row ref
    have law := sparse_caller_input checked parent scope.interval.history.1 partition
      frame same _ localFrame unique joint row ref
    rw [← axes] at law
    exact law

/-- Visible child expressions use the caller's existing measurement keys and
values, including earlier values needed by a visible phi expression. -/
theorem visible_entry_agreement {dependencies program block start count args old effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count args old effect)
    (inputs : List Nat) (history : History)
    (agrees : Agrees inputs scope.interval.before old history) :
    RuntimeOrdinarySSA.Agreement
      (RuntimeOrdinaryBody.valuation inputs scope.visible.ssa.measurements history.values)
      history.values scope.visible.ssa.table := by
  intro id expression member
  change (id,expression) ∈ scope.visible.table at member
  rw [scope.visible.original] at member
  exact agrees.1 id expression (List.mem_filter.mp member).1

/-- The original child trace retains inherited values. Any value in a result
is covered by the parent entry or the child's own checked issued set. -/
theorem actual_child_values {dependencies program block start count args old effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count args old effect)
    (history : History) (supported : Supports (Issued scope.interval.before) history) :
    ∃ events, readOps scope.prepared.block.fuel scope.prepared.block.entry.quantum.reference
        scope.prepared.block.operations = some (scope.localAfter.quantum.reference,events) ∧
      ∀ {results}, run dependencies scope.prepared.block.fuel events history = some results →
        ∀ result ∈ results, Semantics.OrdinaryValue.Extends history.values result.values ∧
          Supports (fun id => Issued scope.interval.before id ∨ Issued scope.localAfter id) result := by
  obtain ⟨work,left,checked⟩ := scope.nativeRead
  obtain ⟨_,events,read,writes⟩ :=
    checkOps_reference_with_writes dependencies 65 _ _ _ work left checked
  have entry := RuntimeNamedFrameAxes.mixedAxes_input scope
  refine ⟨events,?_,?_⟩
  · change readOps 65 scope.prepared.block.entry.quantum.reference
      ((block.operations.drop start).take count) = some (scope.localAfter.quantum.reference,events)
    rw [entry.2.2.1,← entry.2.1]
    exact read
  · intro results executed
    exact run_values dependencies 65 events history _ (writes.mono (fun _ issued => Or.inr issued))
      (fun _ member => Or.inl (supported member)) executed

/-- Every final child axis has an original position in the full caller
frame. This follows from the actual returned ports, even when the child
changes the shape or number of its owners. -/
theorem actual_exit_axes
    {dependencies program block start count inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value) :
    child.bindings.flatMap (·.port.wires) ⊆ scope.localAfter.quantum.frame ∧
      scope.localAfter.quantum.frame ⊆ scope.interval.after.quantum.frame ∧
      (scope.localAfter.quantum.frame.map scope.interval.after.quantum.frame.idxOf).Nodup ∧
      scope.localAfter.quantum.frame.Perm (boundary.mapped.flatMap (·.port.wires)) ∧
      child.bindings.Nodup := by
  obtain ⟨work,left,checked⟩ := scope.nativeRead
  have localValid := Raw.Ownership.valid _
    (Raw.Observation.checkOps_invariants _ _ _ _ _ work left checked).1
  have parentValid := Raw.Ownership.valid _ scope.interval.history.2.2.1
  have aliases := RuntimeNamedCodeTransport.returned_carriers boundary
  have ports : boundary.mapped.map (·.port) = child.bindings.map (·.port) := by
    have same := congrArg (List.map Semantics.CarrierInterface.Owner.port) aliases
    simpa only [carrierOwners,List.map_map,Function.comp_def] using same
  have sourcePorts := boundary.returnRead.trans ports
  have originalPorts := RuntimeNamedReturnAxes.mixed_ports scope boundary
  have localPorts : (child.bindings.map (·.port)).Perm scope.localAfter.quantum.live :=
    (List.Perm.of_eq sourcePorts.symm).trans (originalPorts.trans (List.Perm.of_eq scope.complete))
  have tokens : (child.bindings.map (·.port.token)).Nodup := by
    simpa only [List.map_map,Function.comp_def] using
      (localPorts.map Semantics.Raw.Port.token).nodup_iff.mpr localValid.owners
  have childUnique : child.bindings.Nodup :=
    List.Pairwise.of_map (fun b : RuntimeOwnerMap.Binding => b.port.token)
      (fun _ _ different equal => different (congrArg (fun b : RuntimeOwnerMap.Binding => b.port.token) equal))
      tokens
  have wires := localPorts.flatMap_right (fun port => port.wires)
  simp only [List.flatMap_map] at wires
  have inside : child.bindings.flatMap (·.port.wires) ⊆ scope.localAfter.quantum.frame :=
    fun wire member => localValid.covered wire (wires.mem_iff.mp member)
  obtain ⟨ordered,permutation,sublist⟩ := List.subperm_iff.mp
    ((wires.nodup_iff.mpr localValid.exclusive).subperm inside)
  have same := sublist.eq_of_length ((wires.length_eq.trans localValid.count).trans permutation.length_eq.symm)
  have complete : (child.bindings.flatMap (·.port.wires)).Perm scope.localAfter.quantum.frame :=
    same ▸ permutation
  have sameWires := RuntimeNamedCarrierEncoding.carrier_wires aliases
  have parent : scope.localAfter.quantum.frame ⊆ scope.interval.after.quantum.frame := by
    intro wire member
    have mapped : wire ∈ boundary.mapped.flatMap (·.port.wires) :=
      sameWires.symm ▸ complete.mem_iff.mpr member
    obtain ⟨binding,found,wireMember⟩ := List.mem_flatMap.mp mapped
    have after : binding ∈ boundary.afterFrame.bindings := by
      rw [boundary.sameAfter,boundary.afterBindings]
      exact List.mem_append_right _ found
    have live := boundary.afterFrame.complete.mem_iff.mp (List.mem_map_of_mem after)
    exact parentValid.covered wire (List.mem_flatMap.mpr ⟨binding.port,live,wireMember⟩)
  exact ⟨inside,parent,List.Nodup.map_on
    (fun wire member _ _ equal => (List.idxOf_inj (parent member)).mp equal) localValid.frame,
    complete.symm.trans (List.Perm.of_eq sameWires.symm),childUnique⟩

/-- Assemble the original caller's return frame from the child's written
return bindings and the untouched spectator layouts. -/
theorem caller_return_frame
    {dependencies program block start count inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before)
    (parent : Frame checked.bindings) (sameBindings : checked.bindings = before.bindings)
    (returned : Frame child.bindings) :
    Nonempty (Frame boundary.afterFrame.bindings) ∧
      (forestAxes scope.interval.after.quantum.frame
        (RuntimeSelectionPartition.complement checked.bindings boundary.input.ordered)).Disjoint
        (scope.localAfter.quantum.frame.map scope.interval.after.quantum.frame.idxOf) := by
  let spectators := RuntimeSelectionPartition.complement checked.bindings boundary.input.ordered
  have inputOrder := RuntimeNamedBlockEncoding.original_named_partition_geometry scope boundary checked sameBindings
  obtain ⟨outputOrder,outputPerm⟩ :=
    RuntimeNamedSelectionReturnOrder.caller_after_order scope boundary checked sameBindings
  have mapped := available_carriers (RuntimeNamedCodeTransport.returned_carriers boundary) returned.available
  constructor
  · apply frame_exists
    intro binding member
    rw [outputOrder] at member
    rcases List.mem_append.mp member with spectator | chosen
    · exact parent.available binding (inputOrder.subset (List.mem_append_right _ spectator))
    · exact mapped binding chosen
  · have disjoint := RuntimeNamedBlockSpectators.partition_axes_disjoint boundary.afterFrame
      scope.interval.history.2.2.1 boundary.mapped spectators outputPerm
    have axes := (actual_exit_axes scope boundary).2.2.2.1.map scope.interval.after.quantum.frame.idxOf
    exact List.disjoint_left.mpr (fun axis spectator selected =>
      List.disjoint_left.mp disjoint spectator (axes.mem_iff.mp selected))

/-- Encode an arbitrary child return family on the exact caller axes. The
child's amplitudes may depend on every spectator and reference coordinate. -/
theorem caller_return_action
    {dependencies program block start count inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before)
    (parent : Frame checked.bindings) (sameBindings : checked.bindings = before.bindings)
    (returned : Frame child.bindings) :
    let spectators := RuntimeSelectionPartition.complement checked.bindings boundary.input.ordered
    let order := boundary.mapped++spectators
    let physicalFrame := scope.interval.after.quantum.frame
    let childFrame := scope.localAfter.quantum.frame
    let axes := childFrame.map physicalFrame.idxOf
    ∃ output : Frame boundary.afterFrame.bindings,
      ∀ {Reference : Type} (joint : Nat → Nat → Reference → ℂ) row ref,
        action output physicalFrame
          (fun logical ref => blockJoint (product boundary.mapped).labels.length
            (fun digit high ref => joint (recode child.bindings child.bindings (sourceDimension child.bindings) digit)
              high ref)
            (recode boundary.afterFrame.bindings order (sourceDimension order) logical) ref) row ref =
        action returned childFrame
          (fun digit ref => ((List.range (product spectators).labels.length).map fun high =>
            coefficient spectators physicalFrame row high * joint digit high ref).sum) (gather row axes) ref := by
  intro spectators order physicalFrame childFrame axes
  have outputOrder := (RuntimeNamedSelectionReturnOrder.caller_after_order scope boundary checked sameBindings).2
  obtain ⟨⟨output⟩,_⟩ := caller_return_frame scope boundary checked parent sameBindings returned
  obtain ⟨ordered⟩ := frame_exists (fun b member => output.available b (outputOrder.subset member))
  obtain ⟨inside,_,unique,_,childUnique⟩ := actual_exit_axes scope boundary
  have carriers := RuntimeNamedCodeTransport.returned_carriers boundary
  have outputUnique : boundary.afterFrame.bindings.Nodup :=
    List.Pairwise.of_map (fun b : RuntimeOwnerMap.Binding => b.port.token)
      (fun _ _ different equal => different (congrArg (fun b : RuntimeOwnerMap.Binding => b.port.token) equal))
      boundary.afterFrame.tokensDistinct
  refine ⟨output,?_⟩
  intro Reference joint row ref
  rw [← Qleisli.RuntimeSemanticForest.regroup_action ordered output outputOrder
    (outputOrder.nodup_iff.mpr outputUnique)]
  have law := Qleisli.RuntimeSparseSelectionOutput.regrouped_output returned returned ordered
    (.refl _) childUnique carriers childFrame physicalFrame axes rfl unique inside
    joint row (gather row axes) ref
  rw [RuntimeScatterTransport.scatter_gather row axes unique] at law
  exact law

#print axioms actual_named_entry
#print axioms visible_entry_agreement
#print axioms actual_child_values
#print axioms actual_exit_axes
#print axioms caller_return_frame
#print axioms caller_return_action
end Qleisli.RuntimeSparseNamedBoundary
