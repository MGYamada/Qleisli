import Qleisli.RuntimeCallHistoryReturn
import Qleisli.RuntimeOwnerBindingFacts
import QleisliKernel.Qirf.RuntimeExclusiveAction

/-! Reconstruct the original caller's sparse operator from its returned
selected and spectator histories, before literal owner reinsertion.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open Semantics.Finite (gather)
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode (carrierOwners forestAxes)
open RuntimeCallTraceFrames (Partition WireOrder native_wires)
open RuntimeSemanticForest (Frame action product regroup_action)
open RuntimeStructuralHistory (Represents)
open RuntimeSparseBlockEncoding (coefficient)
open RuntimeForestProduct (gather_bound)
open Qleisli.Semantics.ObservingAction (History)

private theorem selected_frame_consumed (initial ordered : Map) (tokens : List Nat) (roles : List RuntimeOwnerMap.Owner)
    (distinct : (initial.map (fun b => b.port.token)).Nodup)
    (inside : ordered ⊆ initial.filter (fun b => tokens.contains b.port.token))
    (tokenOrder : ordered.map (fun binding => binding.port.token) = tokens)
    (roleOrder : ordered.map (·.owner) = roles) :
    (initial.filter (fun binding => tokens.contains binding.port.token)).filter
      (fun binding => !roles.contains binding.owner) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro binding member
  obtain ⟨original,chosen⟩ := List.mem_filter.mp member
  have marked : binding.port.token ∈ tokens := List.contains_iff_mem.mp chosen
  have found : binding.port.token ∈ ordered.map (fun b => b.port.token) :=
    (congrArg (fun keys => binding.port.token ∈ keys) tokenOrder).mpr marked
  obtain ⟨assigned,used,sameToken⟩ := List.mem_map.mp found
  have same := Qleisli.RuntimeOwnerTransitionAction.map_unique (fun b : Binding => b.port.token)
    initial distinct assigned (List.mem_filter.mp (inside used)).1 binding original sameToken
  have originalOwner : assigned.owner ∈ roles := roleOrder ▸ List.mem_map_of_mem used
  have owner : binding.owner ∈ roles := congrArg RuntimeOwnerMap.Binding.owner same ▸ originalOwner
  have contains := List.contains_iff_mem.mpr owner
  intro impossible
  simp only [contains,Bool.not_true,Bool.false_eq_true] at impossible

/-- The projected named boundary owns exactly the selected bindings.
Parked owners can reappear only through their own checked Raw phis. -/
theorem projected_named_map {sources caller dependencies program block offset access suspended before ordinary
    childHistory childRetired value}
    {actual : @RuntimeInterval.Branch dependencies program block offset}
    (opening : @RuntimeExclusiveAction.Opened sources caller dependencies program block offset 1
      access actual.interval suspended before)
    (frame : RuntimeBranchProjection.Checked actual opening.frame (opening.route.selected.map (·.token)) ordinary)
    (child : RuntimeInterval.Branch frame.prepared.block 0)
    (event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller)
    (boundary : RuntimeNamedBoundary.Checked child.interval (opening.route.selected.map (·.token)) event
      (RuntimeExclusiveAction.selectedState opening) childHistory childRetired value) :
    boundary.after.bindings = boundary.mapped := by
  let selected := RuntimeExclusiveAction.selectedState opening
  let tokens := opening.route.selected.map (·.token)
  let ordered : Map := boundary.input.ordered
  obtain ⟨inside,roles⟩ := RuntimeSelectionPartition.order_values selected.bindings event.inputOwners
    ordered boundary.input.orderRead
  change ordered ⊆ opening.initial.bindings.filter (fun b : Binding => tokens.contains b.port.token) at inside
  have distinct : (opening.initial.bindings.map (fun b : Binding => b.port.token)).Nodup :=
    opening.nativeBindings ▸ opening.frame.tokensDistinct
  have tokenOrder : ordered.map (fun binding => binding.port.token) = tokens := by
    simpa only [List.map_map] using boundary.input.sameTokens
  have consumed := selected_frame_consumed opening.initial.bindings ordered tokens
    event.inputOwners distinct inside tokenOrder roles
  exact boundary.afterBindings.trans (congrArg (· ++ boundary.mapped) consumed)

/-- The actual input ports select the source-ordered callee owners and the
parked owners in the exact order of the checked original phis. -/
theorem routed_input_geometry {dependencies program block sources caller}
    (access : @RuntimePureBody.RoutedAccess dependencies program block sources caller) :
    let selected := access.boundary.input.ordered
    let parked := access.frame.moves.map (·.2.original.thenBinding)
    selected.map (·.port) = access.frame.selected ∧
      (selected ++ parked).Perm access.opening.frame.bindings := by
  intro selected parked
  let input := access.opening.frame
  let live := access.actual.interval.before.quantum.live
  let both := selected ++ parked
  have selectedInside : selected ⊆ input.bindings := by
    intro binding present
    have found := (RuntimeSelectionPartition.order_values
      (RuntimeExclusiveAction.selectedState access.opening).bindings access.event.inputOwners
      selected access.boundary.input.orderRead).1 present
    change binding ∈ access.opening.initial.bindings.filter _ at found
    exact access.opening.nativeBindings.symm ▸ List.mem_of_mem_filter found
  have liveInput : (input.bindings.map (·.port)).Perm live := input.complete
  have selectedRead := RuntimeStructuralWires.ports_read access.actual.interval.before.quantum.reference
    (selected.map (·.port)) (Raw.Ownership.valid _ access.actual.interval.history.1).owners
    (fun port member => by
      obtain ⟨binding,present,rfl⟩ := List.mem_map.mp member
      exact liveInput.mem_iff.mp (List.mem_map_of_mem (selectedInside present)))
  change PureInterval.ports access.actual.interval.before ((selected.map (·.port)).map (·.token)) =
    some (selected.map (·.port)) at selectedRead
  rw [access.boundary.input.sameTokens] at selectedRead
  have selectedPorts := Option.some.inj (selectedRead.symm.trans access.frame.atEntry)
  have portOrder : (both.map (·.port)).Perm (input.bindings.map (·.port)) := by
    simpa only [both,parked,List.map_append,List.map_map,Function.comp_def,selectedPorts] using
      access.frame.completeEntry.trans liveInput.symm
  have parkedInside : parked ⊆ input.bindings := by
    intro binding present
    obtain ⟨move,_,rfl⟩ := List.mem_map.mp present
    exact List.mem_of_mem_filter move.2.original.thenMember
  have bothInside : both ⊆ input.bindings := fun _ member =>
    (List.mem_append.mp member).elim (fun inside => selectedInside inside) (fun inside => parkedInside inside)
  have tokens := portOrder.map Semantics.Raw.Port.token
  simp only [List.map_map,Function.comp_def] at tokens
  have noDuplicates (bindings : Map) (distinct : (bindings.map (fun b : Binding => b.port.token)).Nodup) :
      bindings.Nodup :=
    List.Pairwise.of_map (fun b : Binding => b.port.token)
      (fun _ _ different same => different (congrArg (fun b : Binding => b.port.token) same)) distinct
  refine ⟨selectedPorts,(List.perm_ext_iff_of_nodup
    (noDuplicates both (tokens.nodup_iff.mpr input.tokensDistinct))
    (noDuplicates input.bindings input.tokensDistinct)).mpr ?_⟩
  intro binding
  refine ⟨fun present => bothInside present,fun present => ?_⟩
  obtain ⟨found,member,same⟩ := List.mem_map.mp
    (portOrder.mem_iff.mpr (List.mem_map_of_mem present) : binding.port ∈ both.map (·.port))
  have equal := RuntimeOwnerTransitionAction.map_unique (fun b : Binding => b.port.token)
    input.bindings input.tokensDistinct found (bothInside member) binding present
    (congrArg Semantics.Raw.Port.token same)
  exact equal ▸ member

/-- The projected program receives exactly the typed, selected input owners.
The sparse input keeps a separate correlated slice for each ordered parked
coordinate, including the coordinate of a zero-width owner. -/
theorem prepared_routed_history {dependencies program block sources caller}
    (access : @RuntimePureBody.RoutedAccess dependencies program block sources caller)
    (input : RuntimeOwnerMap.Checked (SourceTypes.SourceRuntimeScope.Subject.whole access.source).initialRoles
      access.frame.prepared.block.entry)
    (assigned : Map)
    (assignedRead : RuntimeInterval.Computed (RuntimeSourceBoundary.bindings
      (SourceTypes.SourceRuntimeScope.Subject.whole access.source).initialRoles
      ((access.frame.selected.zip (access.boundary.input.ordered.map (·.owner))).map fun (port,role) =>
        (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner))) assigned)
    (ordered : RuntimeInterval.Computed
      (RuntimePureBody.reordered (SourceTypes.SourceRuntimeScope.Subject.whole access.source).initialRoles
        access.frame.prepared.block.entry assigned) input)
    {roles} (checked : RuntimeOwnerMap.Checked roles access.actual.interval.before)
    (sameBindings : checked.bindings = access.opening.frame.bindings)
    (parent : Frame checked.bindings) (actual : History) (joint : Nat → Nat → ℂ)
    (represented : Represents parent access.actual.interval.before actual joint) :
    let selected := access.boundary.input.ordered
    let parked := access.frame.moves.map (·.2.original.thenBinding)
    ∃ frame : Frame input.bindings,
      Agrees access.actual.interval.before.quantum.reference access.frame.prepared.block.entry.quantum.reference
        (parked.map (·.port)) actual
        (inputHistory frame access.frame.prepared.block.entry.quantum.frame checked.bindings selected parked joint actual) := by
  intro selected parked
  obtain ⟨ports,geometry⟩ := routed_input_geometry access
  have readOrder := RuntimeNamedPrimitiveInputs.reordered_original
    (RuntimeNamedPrimitiveInputs.bindings_roles assignedRead) input ordered
  have owners := (RuntimeSelectionPartition.order_values
    (RuntimeExclusiveAction.selectedState access.opening).bindings access.event.inputOwners
    selected access.boundary.input.orderRead).2
  have carriers : carrierOwners input.bindings = carrierOwners selected := by
    rw [readOrder,RuntimeBoundaryOwnerEvidence.bindings_carriers assignedRead,owners]
    exact RuntimeNamedPrimitiveInputs.named_input_carriers_on access.boundary ports.symm
  exact prepared_partition_history access.frame.prepared selected parked checked
    (sameBindings.symm ▸ geometry) ports.symm carriers parent actual joint represented

/-- The returned physical spectator ports select the same logical slice
used by the selected child. The complete caller frame reassembles each
column of an arbitrary entangled input using the existing sparse encoding. -/
theorem routed_operator_return {parent child : RuntimeInterval.State}
    {selected mapped spectators output : Map} {selectedRoles}
    (childFrame : Frame selected) (full : Frame output) (ordered : Frame (mapped++spectators))
    (joined : (mapped++spectators).Perm output) (unique : output.Nodup)
    (cValid : Raw.stateValid child.quantum = true)
    (selectedChecked : RuntimeOwnerMap.Checked selectedRoles child)
    (sameSelected : selectedChecked.bindings = selected)
    (carriers : carrierOwners mapped = carrierOwners selected)
    (partition : Partition parent.quantum.reference child.quantum.reference (spectators.map (·.port)))
    (history : History) (localResults : Nat → History) (joint : Nat → Nat → Nat → ℂ)
    (paired : Agrees parent.quantum.reference child.quantum.reference (spectators.map (·.port))
      history localResults)
    (refinesChild : ∀ high, Represents childFrame child (localResults high) (returnFibre spectators high joint)) :
    Represents full parent history (returnedOperator selected output mapped spectators joint) := by
  intro column row bounded
  let axes := child.quantum.frame.map parent.quantum.frame.idxOf
  let low := project parent.quantum.reference child.quantum.frame row
  let high := project parent.quantum.reference (WireOrder (spectators.map (·.port))) row
  have lowBound : low < 2^child.quantum.frame.length := by
    change gather row axes < 2^child.quantum.frame.length
    simpa only [axes,List.length_map] using gather_bound row axes
  have highEq : high = gather row (forestAxes parent.quantum.frame spectators) := by
    simp only [high,project,Semantics.RawTrace.axes,forestAxes,List.flatMap_map]
    rfl
  have fibreEq : returnFibre spectators high joint =
      fun digit ref => ((List.range (product spectators).labels.length).map fun h =>
        coefficient spectators parent.quantum.frame row h * joint digit h ref).sum := by
    rw [highEq]
    rfl
  have parentContains : child.quantum.frame ⊆ parent.quantum.frame := fun wire present =>
    partition.frame.symm.subset (List.mem_append_left _ present)
  have axesDistinct : axes.Nodup := List.Nodup.map_on
    (fun _ present _ _ equal => (List.idxOf_inj (parentContains present)).mp equal)
    (Raw.Ownership.valid _ cValid).frame
  have selectedDistinct : selected.Nodup := by
    rw [← sameSelected]
    exact List.Pairwise.of_map (fun binding : Binding => binding.port.token)
      (fun _ _ different equal => different (congrArg (fun b : Binding => b.port.token) equal))
      selectedChecked.tokensDistinct
  have selectedInside : selected.flatMap (·.port.wires) ⊆ child.quantum.frame := by
    have ports := selectedChecked.complete
    rw [sameSelected] at ports
    have wires := (ports.flatMap_right Semantics.Raw.Port.wires).trans (native_wires child.quantum cValid)
    simpa only [List.flatMap_map] using wires.subset
  have regrouped := Qleisli.RuntimeSparseSelectionOutput.regrouped_output childFrame childFrame ordered
    (.refl _) selectedDistinct carriers child.quantum.frame parent.quantum.frame axes rfl axesDistinct selectedInside
    joint row (gather row axes) column
  rw [RuntimeScatterTransport.scatter_gather row axes axesDistinct] at regrouped
  calc
    history.operator row column = (localResults high).operator low column :=
      paired.operator row column bounded
    _ = action childFrame child.quantum.frame (returnFibre spectators high joint) low column :=
      refinesChild high column low lowBound
    _ = action full parent.quantum.frame (returnedOperator selected output mapped spectators joint) row column := by
      rw [fibreEq]
      unfold returnedOperator
      rw [← regroup_action ordered full joined (joined.nodup_iff.mpr unique)]
      exact regrouped.symm

#print axioms routed_operator_return
#print axioms projected_named_map
#print axioms routed_input_geometry
#print axioms prepared_routed_history
end Qleisli.RuntimeCallHistory
