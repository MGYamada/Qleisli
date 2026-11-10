import Qleisli.NominalSectorAction
import Qleisli.RawActionLocality
import Qleisli.RuntimeSelectionTraceEvidence
import Qleisli.RuntimeSelectionCodes
import Qleisli.RuntimeSemanticForest

/-! The source's sparse embedding through an actual coherent selection.
Original layout and wire facts suffice for the whole forest; there is no
bounded carrier read for unrelated spectators or reconstruction of a matrix.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeSemanticSelectionGeometry
open QleisliKernel QleisliKernel.Qirf
open RuntimeOwnerMap (Binding Map)
open QleisliKernel.Semantics.Finite (scatter gather width)
open QleisliKernel.FiniteRestriction (pack SectorEvaluationBinding)
open Qleisli.Semantics.Exact (action)
open Qleisli.Semantics.RawAction (events circuit)
open RuntimeForestCode (forestBasis forestAxes embed)
open Qleisli.RuntimeSemanticForest (Frame Available)

private theorem forest_by_bases (owners : List Semantics.CarrierInterface.Owner) :
    Semantics.CarrierInterface.forest owners =
      match owners.map (·.basis) with
      | [] => [.unit]
      | [basis] => basis
      | [first,second] => .pair :: first ++ second
      | bases => .tuple bases.length :: bases.flatMap id := by
  cases owners with
  | nil => rfl
  | cons first rest => cases rest with
    | nil => rfl
    | cons second rest => cases rest with
      | nil => rfl
      | cons third rest =>
        simp only [Semantics.CarrierInterface.forest,List.map_cons,List.length_cons,List.flatMap_cons]
        rw [List.length_map,List.flatMap_map]
        rfl

private theorem forest_eq {before after : Map}
    (owners : after.map Binding.owner = before.map Binding.owner) :
    forestBasis after = forestBasis before := by
  unfold forestBasis
  rw [forest_by_bases,forest_by_bases]
  have bases := congrArg (List.map (fun owner : RuntimeOwnerMap.Owner => owner.basis)) owners
  have same : (RuntimeForestCode.carrierOwners after).map (·.basis) =
      (RuntimeForestCode.carrierOwners before).map (·.basis) := by
    simpa only [RuntimeForestCode.carrierOwners,List.map_map,Function.comp_def] using bases
  rw [same]

/-- The actual checked selection transports the complete semantic frame
through fresh tokens. Every spectator, nominal basis and zero-width owner
keeps its original coordinate, with no bounded forest reader premise. -/
theorem semantic_frames
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained)
    (before : Frame source.before.bindings) :
    ∃ _trace : Qleisli.RuntimeSelectionTraceEvidence.TraceEvidence frame source selectorBits targetBits retained restricted,
    ∃ after : Frame source.transport.after.bindings,
      after.code = before.code ∧
      ∀ physical logical,
        embed frame.interval.after.quantum.frame source.transport.after.bindings after.code physical logical =
          embed frame.interval.before.quantum.frame source.before.bindings before.code physical logical := by
  obtain ⟨trace⟩ := Qleisli.RuntimeSelectionTraceEvidence.trace_of_source frame source restricted
  have wires := Qleisli.RuntimeSelectionCodes.selection_wires_of_read frame source restricted
  have available : Available source.transport.after.bindings := by
    intro binding member
    let pair := fun b : Binding => (b.owner,b.port.wires)
    have found : pair binding ∈ source.before.bindings.map pair :=
      wires ▸ List.mem_map_of_mem member
    obtain ⟨original,originalMember,same⟩ := List.mem_map.mp found
    obtain ⟨layout⟩ := before.available original originalMember
    have basis : original.owner.basis = binding.owner.basis :=
      congrArg (fun pair : RuntimeOwnerMap.Owner × List Nat => pair.1.basis) same
    have wires := congrArg Prod.snd same
    have live : binding.port ∈ frame.interval.after.quantum.live :=
      source.transport.after.complete.mem_iff.mp (List.mem_map_of_mem member)
    have bitCount := ((Raw.Ownership.valid _ frame.interval.history.2.2.1).ports binding.port live).1
    have wireCount : binding.port.wires.length = layout.layout.bits :=
      (congrArg List.length wires).symm.trans layout.wires
    exact ⟨⟨layout.layout,basis ▸ layout.reference,bitCount.trans wireCount,wireCount⟩⟩
  have sameForest := forest_eq source.transport.after.ordered
  let after : Frame source.transport.after.bindings :=
    ⟨before.code,sameForest.symm ▸ before.original,available⟩
  refine ⟨trace,after,rfl,?_⟩
  intro physical logical
  have wireOrder := congrArg (List.flatMap (fun pair : RuntimeOwnerMap.Owner × List Nat => pair.2)) wires
  simp only [List.flatMap_map] at wireOrder
  unfold embed forestAxes
  rw [trace.preservedFrame,wireOrder]

/-- The selected pair's original axes are the same axes at its actual return. -/
theorem returned_axes
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    (trace : Qleisli.RuntimeSelectionTraceEvidence.TraceEvidence frame source selectorBits targetBits retained restricted) :
    forestAxes frame.interval.before.quantum.frame trace.selection.selected =
      forestAxes frame.interval.after.quantum.frame source.returned.toList := by
  have selectedPorts := trace.selectedPorts.trans (RuntimeSelectionPartition.source_ports frame source).1
  have selectedWires := congrArg (List.flatMap (fun port : Semantics.Raw.Port => port.wires)) selectedPorts
  have returnedWires := congrArg (List.flatMap (fun pair : RuntimeOwnerMap.Owner × List Nat => pair.2))
    (RuntimeSelectionWires.source_boundary_of_read frame source restricted).1
  simp only [List.flatMap_map] at selectedWires returnedWires
  unfold forestAxes
  rw [trace.preservedFrame,returnedWires,selectedWires]
  rfl

/-- Localize the original caller events on the returned pair. The arbitrary
spectator/reference coefficients use the same complete sparse embedding,
without a native forest witness or a joined operator matrix. -/
theorem semantic_local_action
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained)
    (before : Frame source.before.bindings) :
    ∃ trace : Qleisli.RuntimeSelectionTraceEvidence.TraceEvidence frame source selectorBits targetBits retained restricted,
    ∃ after : Frame source.transport.after.bindings,
    ∀ {Reference : Type} (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference),
      let axes := forestAxes frame.interval.after.quantum.frame source.returned.toList
      events dependencies trace.traceResult.events
        (fun row => Qleisli.RuntimeSemanticForest.action before frame.interval.before.quantum.frame joint row reference)
        physical =
      circuit dependencies retained.steps
        (fun row => Qleisli.RuntimeSemanticForest.action after frame.interval.after.quantum.frame
          joint (scatter physical axes row) reference) (gather physical axes) := by
  obtain ⟨trace,after,sameCode,sameEmbedding⟩ := semantic_frames frame source restricted before
  refine ⟨trace,after,?_⟩
  intro Reference joint physical reference axes
  have same (row : Nat) :
      Qleisli.RuntimeSemanticForest.action before frame.interval.before.quantum.frame joint row reference =
      Qleisli.RuntimeSemanticForest.action after frame.interval.after.quantum.frame joint row reference := by
    unfold Qleisli.RuntimeSemanticForest.action
    rw [sameCode]
    apply Qleisli.Exact.sum_map_congr
    intro logical _
    have entry := sameEmbedding row logical
    rw [sameCode] at entry
    rw [entry]
  have pairAxes := returned_axes frame source trace
  rw [trace.literal]
  simp_rw [same]
  have action := Qleisli.Semantics.RawAction.Locality.events_output dependencies
    frame.interval.before.quantum.frame.length
    (forestAxes frame.interval.before.quantum.frame trace.selection.selected)
    trace.selection.distinct trace.chunks (RuntimeLocalEvents.bounds_controls trace.bounded)
    (RuntimeLocalEvents.bounds_targets trace.bounded)
    (fun row => Qleisli.RuntimeSemanticForest.action after frame.interval.after.quantum.frame joint row reference)
    physical
  simpa only [trace.localSteps, Qleisli.Semantics.RawAction.Locality.pull, pairAxes, axes] using action

/-- The original global events at a physical label equal its own retained
sector, acting on the encoded fibre of the actual caller. This keeps the
exact sector matrix and arbitrary references without a joined matrix. -/
theorem semantic_sector_action
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained)
    (before : Frame source.before.bindings) :
    ∃ trace : Qleisli.RuntimeSelectionTraceEvidence.TraceEvidence frame source selectorBits targetBits retained restricted,
    ∃ after : Frame source.transport.after.bindings,
    ∀ {Reference : Type} (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference)
      {label row : Nat} {sector : Semantics.Exact.Matrix},
      retained.sectors[label]? = some sector → row < sector.rows →
      let axes := forestAxes frame.interval.after.quantum.frame source.returned.toList
      gather physical axes = pack selectorBits label row →
      events dependencies trace.traceResult.events
        (fun input => Qleisli.RuntimeSemanticForest.action before frame.interval.before.quantum.frame joint input reference)
        physical =
      action sector
        (fun input ref => Qleisli.RuntimeSemanticForest.action after frame.interval.after.quantum.frame
          joint (scatter physical axes (pack selectorBits label input)) ref) row reference := by
  obtain ⟨trace,after,locality⟩ := semantic_local_action frame source restricted before
  obtain ⟨work,left,read⟩ := restricted
  have retainedRead := Raw.Sector.read_bound dependencies [.bits selectorBits] [.bits targetBits]
    (RuntimePureInterval.fragment frame.selected frame.operations outputs) retained work left read
  have sectors : Exact.ListRel
      (SectorEvaluationBinding dependencies selectorBits [.bits targetBits] retained.steps)
      (List.range (2^selectorBits)) retained.sectors := by
    simpa only [width,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using retainedRead.2.2.2.2.2.2.2
  refine ⟨trace,after,?_⟩
  intro Reference joint physical reference label row sector found bounded axes coordinate
  rw [locality joint physical reference]
  change circuit dependencies retained.steps
      (fun input => Qleisli.RuntimeSemanticForest.action after frame.interval.after.quantum.frame
        joint (scatter physical axes input) reference) (gather physical axes) = _
  rw [coordinate]
  exact Qleisli.Semantics.RawAction.Sector.sector_binding_action dependencies selectorBits [.bits targetBits]
    retained.steps label sector (Qleisli.NominalSector.indexed_sector sectors found)
    (fun input ref => Qleisli.RuntimeSemanticForest.action after frame.interval.after.quantum.frame
      joint (scatter physical axes input) ref) row reference bounded

#print axioms semantic_frames
#print axioms semantic_sector_action
#print axioms semantic_local_action
end Qleisli.RuntimeSemanticSelectionGeometry
