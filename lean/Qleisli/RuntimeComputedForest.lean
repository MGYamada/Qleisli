import Qleisli.RuntimeComputedGeometry
import Qleisli.RuntimeComputedProtectedAction

/-! The protected computation leaves the complete encoding in place. Its
logical phase is selected by the original owner's digit, with all other
owners and reference columns retained.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeComputedForest
open QleisliKernel QleisliKernel.Qirf
open RuntimeOwnerMap (Binding Map)
open RuntimeComputedPredicate (ProtectedInterval)
open RuntimeSemanticForest (Frame Available ownerLayout)
open RuntimeForestCode (forestBasis forestAxes embed)
open Semantics.Finite (gather)
open Qleisli.Semantics.Exact (scalar)
open Qleisli.RuntimeForestRegroup (sourceDimension)
open Qleisli.MixedRadix (decode)

private def rebind (owner : RuntimeOwnerMap.Owner) (port : Semantics.Raw.Port) (binding : Binding) : Binding :=
  if binding.owner == owner then ⟨owner,port⟩ else binding

private theorem rebind_owner (owner : RuntimeOwnerMap.Owner) (port : Semantics.Raw.Port) (binding : Binding) :
    (rebind owner port binding).owner = binding.owner := by
  unfold rebind
  split
  · rename_i same
    exact (beq_iff_eq.mp same).symm
  · rfl

private theorem rebind_wires (selected : Binding) (port : Semantics.Raw.Port) (bindings : Map)
    (present : selected ∈ bindings) (distinct : (bindings.map (·.owner.ordinal)).Nodup)
    (wires : port.wires = selected.port.wires) (binding : Binding) (member : binding ∈ bindings) :
    (rebind selected.owner port binding).port.wires = binding.port.wires := by
  unfold rebind
  split
  · rename_i same
    have ordinal : binding.owner.ordinal = selected.owner.ordinal :=
      congrArg (·.ordinal) (beq_iff_eq.mp same)
    have equal := RuntimeOwnerTransitionAction.map_unique (fun b : Binding => b.owner.ordinal) _ distinct
      binding member selected present ordinal
    simpa only [equal] using wires
  · rfl

/-- Only the selected SSA token changes. The original ordered source basis,
physical wires and all entries of the encoding are therefore identical. -/
theorem rebound_encoding_of_ports {before after : Raw.Observation.State}
    {bindings : Map} {roles : List RuntimeOwnerMap.Owner} {owner : RuntimeOwnerMap.Owner}
    (inputPort : RuntimePrimitiveSource.PortAt owner bindings) (outputPort : Semantics.Raw.Port)
    (beforeMap : RuntimeOwnerMap.Checked (bindings.map (·.owner)) before)
    (afterMap : RuntimeOwnerMap.Checked roles after)
    (afterBindings : afterMap.bindings = bindings.map (rebind owner outputPort))
    (wires : outputPort.wires = inputPort.port.wires)
    (sameFrame : after.quantum.frame = before.quantum.frame)
    (valid : Raw.stateValid after.quantum = true)
    (input : Frame bindings) :
    ∃ output : Frame afterMap.bindings, ∀ {R : Type} (joint : Nat → R → ℂ) (row : Nat) (reference : R),
      RuntimeSemanticForest.action output after.quantum.frame joint row reference =
        RuntimeSemanticForest.action input before.quantum.frame joint row reference := by
  let selected : Binding := ⟨owner,inputPort.port⟩
  let replace := rebind selected.owner outputPort
  have present : selected ∈ bindings := RuntimeBasisOwnerGeometry.selected_binding inputPort
  have distinct : (bindings.map (·.owner.ordinal)).Nodup := by
    simpa only [List.map_map,Function.comp_def] using beforeMap.ownersDistinct
  have returnedWires (binding : Binding) (member : binding ∈ bindings) :
      (replace binding).port.wires = binding.port.wires :=
    rebind_wires selected outputPort bindings present distinct wires binding member
  have sameBindings : afterMap.bindings = bindings.map replace := afterBindings
  have basis : forestBasis afterMap.bindings = forestBasis bindings := by
    unfold forestBasis
    rw [RuntimeSelectionCodes.forest_by_bases,RuntimeSelectionCodes.forest_by_bases,sameBindings]
    simp only [RuntimeForestCode.carrierOwners,List.map_map,Function.comp_def,rebind_owner,replace]
  have available : Available afterMap.bindings := by
    intro binding member
    rw [sameBindings] at member
    obtain ⟨original,present,equal⟩ := List.mem_map.mp member
    subst binding
    obtain ⟨layout⟩ := input.available original present
    have wires := returnedWires original present
    have selectedAfter : replace original ∈ afterMap.bindings := by
      rw [sameBindings]
      exact List.mem_map.mpr ⟨original,present,rfl⟩
    have live := afterMap.complete.mem_iff.mp (List.mem_map.mpr ⟨_,selectedAfter,rfl⟩)
    have portBits := ((Raw.Ownership.valid _ valid).ports _ live).1
    exact ⟨⟨layout.layout,by simpa only [replace,rebind_owner] using layout.reference,
      portBits.trans (congrArg List.length wires |>.trans layout.wires),
      (congrArg List.length wires).trans layout.wires⟩⟩
  have axes : forestAxes after.quantum.frame afterMap.bindings =
      forestAxes before.quantum.frame bindings := by
    rw [sameFrame,sameBindings]
    unfold forestAxes
    have wireLists : (bindings.map replace).map (·.port.wires) =
        bindings.map (·.port.wires) := by
      rw [List.map_map]
      exact List.map_congr_left returnedWires
    have flatten := congrArg (List.flatMap id) wireLists
    simp only [List.flatMap_map,id_eq] at flatten
    rw [List.flatMap_map,flatten]
  let output : Frame afterMap.bindings := ⟨input.code,by rw [basis]; exact input.original,available⟩
  refine ⟨output,?_⟩
  intro R joint row reference
  simp only [RuntimeSemanticForest.action,output,embed,axes]

theorem rebound_encoding {sources caller dependencies program block start count event source interval before}
    (checked : @ProtectedInterval sources caller dependencies program block start count event source interval before)
    (input : Frame before.bindings) :
    ∃ output : Frame checked.after.bindings, ∀ {R : Type} (joint : Nat → R → ℂ) (row : Nat) (reference : R),
      RuntimeSemanticForest.action output interval.after.quantum.frame joint row reference =
        RuntimeSemanticForest.action input interval.before.quantum.frame joint row reference :=
  rebound_encoding_of_ports checked.input checked.output checked.frame checked.after checked.afterBindings checked.wires
    (RuntimeComputedGeometry.literal_geometry checked).1 interval.history.2.2.1 input

#print axioms rebound_encoding
end Qleisli.RuntimeComputedForest
