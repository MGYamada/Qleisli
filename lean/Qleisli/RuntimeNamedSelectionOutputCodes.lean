import Qleisli.RuntimeNamedSelectionReturnOrder

/-! Transport the actual child output code to the returned caller owners and
physical coordinates, including distinct zero-width owners.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedSelectionOutputCodes
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Finite (gather scatter bit)
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.RuntimeForestOrderedProduct Qleisli.RuntimeNamedBlockEncoding
open Qleisli.RuntimeNamedCarrierEncoding Qleisli.Semantics.Exact

theorem gather_scatter_wires (childFrame parentFrame wires axes : List Nat)
    (coordinates : childFrame.map parentFrame.idxOf = axes) (unique : axes.Nodup)
    (inside : wires ⊆ childFrame) (base physical : Nat) :
    gather (scatter base axes physical) (wires.map parentFrame.idxOf) =
      gather physical (wires.map childFrame.idxOf) := by
  simp only [gather,List.zipIdx_map,List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair member
  change bit (scatter base axes physical) (parentFrame.idxOf pair.1) * 2^pair.2 =
    bit physical (childFrame.idxOf pair.1) * 2^pair.2
  have present : pair.1 ∈ wires := by
    have retained : pair.1 ∈ wires.zipIdx.map Prod.fst := List.mem_map_of_mem member
    simpa only [List.zipIdx_map_fst] using retained
  have found := inside present
  have bound : childFrame.idxOf pair.1 < axes.length := by
    rw [← coordinates,List.length_map]
    exact List.idxOf_lt_length_of_mem found
  have lookup : axes[childFrame.idxOf pair.1]? = some (parentFrame.idxOf pair.1) := by
    rw [← coordinates,List.getElem?_map,RuntimeNamedFrameAxes.wireLookup childFrame found]
    rfl
  have slot := Option.some.inj ((List.getElem?_eq_getElem bound).symm.trans lookup)
  rw [← slot,RuntimeScatterTransport.scatter_at base physical axes unique _ bound]

theorem mapped_coefficients {child mapped : Map} (childCodes : OwnerCodes child) (mappedCodes : OwnerCodes mapped)
    (same : carrierOwners mapped = carrierOwners child)
    (childFrame parentFrame axes : List Nat)
    (coordinates : childFrame.map parentFrame.idxOf = axes) (unique : axes.Nodup)
    (inside : child.flatMap (fun b => b.port.wires) ⊆ childFrame) :
    (sparseProduct mappedCodes).dimension = (sparseProduct childCodes).dimension ∧
    ∀ base physical logical, logical < (sparseProduct childCodes).dimension →
      coefficients parentFrame mappedCodes (scatter base axes physical) logical =
        coefficients childFrame childCodes physical logical := by
  have layout : layoutProduct mappedCodes = layoutProduct childCodes := by
    unfold layoutProduct
    rw [carrier_layouts childCodes mappedCodes same]
  have dimension : (sparseProduct mappedCodes).dimension = (sparseProduct childCodes).dimension := by
    rw [(product_agrees mappedCodes).dimension,(product_agrees childCodes).dimension,layout]
  refine ⟨dimension,?_⟩
  intro base physical logical bound
  have mappedBound : logical < (sparseProduct mappedCodes).dimension := by rwa [dimension]
  rw [← product_coefficient _ _ _ _ mappedBound,← product_coefficient _ _ _ _ bound,layout]
  unfold forestAxes
  rw [carrier_wires same,gather_scatter_wires childFrame parentFrame _ axes coordinates unique inside]

def CallOutputCodes
    {dependencies program block callStart callCount inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    {childRoles childState childChecked} (actual : @Frame childRoles childState childChecked)
    (output : Frame boundary.afterFrame) (spectators : Map) : Prop :=
  ∃ returnedCodes : OwnerCodes child.bindings,
    reindex actual.owners child.bindings = some returnedCodes ∧
    ∃ mappedCodes : OwnerCodes boundary.mapped, ∃ spectatorCodes : OwnerCodes spectators,
      reindex output.owners (boundary.mapped++spectators) = some (append mappedCodes spectatorCodes) ∧
      (sparseProduct mappedCodes).dimension = (sparseProduct returnedCodes).dimension ∧
      ∀ base physical logical, logical < (sparseProduct returnedCodes).dimension →
        coefficients scope.interval.after.quantum.frame mappedCodes
          (scatter base (RuntimeNamedFrameAxes.mixedAxes scope) physical) logical =
        coefficients childState.quantum.frame returnedCodes physical logical

/-- The actual final return order determines the selected output coefficients
of this same caller after-frame. The caller retains the actual spectators. -/
theorem call_output_codes
    {dependencies program block callStart callCount inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    {first size localInputs outputs roles}
    (frame : RuntimePureInterval.Checked scope.prepared.block 2 first size localInputs outputs roles)
    (starts : first = 0) (covers : size = ((block.operations.drop callStart).take callCount).length)
    {selectorBits targetBits retained restricted beforeRoles afterRoles beforeChecked afterChecked}
    (literal : @RuntimeLocalEvents.Literal dependencies scope.program scope.prepared.block first size localInputs outputs roles
      frame selectorBits targetBits retained restricted beforeRoles afterRoles beforeChecked afterChecked)
    (returned : child.bindings.Perm afterChecked.bindings)
    (output : Frame boundary.afterFrame) (spectators : Map)
    (order : (boundary.mapped++spectators).Perm boundary.afterFrame.bindings) :
    CallOutputCodes scope boundary literal.outputCode output spectators := by
  obtain ⟨returnedCodes,returnedRead⟩ := reindex_exists literal.outputCode.owners child.bindings returned.subset
  obtain ⟨all,kept⟩ := reindex_exists output.owners _ order.subset
  obtain ⟨mappedCodes,spectatorCodes,split⟩ := append_exists _ _ all
  rw [split] at kept
  obtain ⟨_events,_trace,_action,geometry⟩ := RuntimeNamedSelectionParent.parent_action scope frame starts covers literal
  have inside : child.bindings.flatMap (fun b => b.port.wires) ⊆ frame.interval.after.quantum.frame := by
    intro wire member
    obtain ⟨b,returnedMember,wireMember⟩ := List.mem_flatMap.mp member
    have native := afterChecked.complete.mem_iff.mp (List.mem_map_of_mem (returned.subset returnedMember))
    exact (Raw.Ownership.valid _ frame.interval.history.2.2.1).covered wire
      (List.mem_flatMap.mpr ⟨b.port,native,wireMember⟩)
  have action := mapped_coefficients returnedCodes mappedCodes (RuntimeNamedCodeTransport.returned_carriers boundary)
    _ _ _ geometry.2.2 (RuntimeNamedFrameAxes.mixedAxes_bounds scope).1 inside
  exact ⟨returnedCodes,returnedRead,mappedCodes,spectatorCodes,kept,action⟩

#print axioms gather_scatter_wires
#print axioms mapped_coefficients
#print axioms call_output_codes
end Qleisli.RuntimeNamedSelectionOutputCodes
