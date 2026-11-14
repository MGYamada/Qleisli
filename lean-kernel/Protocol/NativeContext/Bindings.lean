import Protocol.NativeContext

/-! Preservation through the actual pure native context dispatcher. These lemmas
retain existing original-packet, compared-view and scoped-root proof premises;
they neither admit new guarantees nor prove source, native IO or runtime behavior.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.NativeContext
open ExecutionView

theorem run_qmatch_binding (product : String) (bytes : ByteArray)
    (decision : Decision .qmatchSource) (work left : Nat)
    (ok : (run .qmatchSource product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .execution ∧
      Nonempty (CheckedQmatch.Binding input.original input.graph decision.value work left) := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ (by decide) ok
  exact CheckedQmatch.run_binding bytes decision.value work left checked

theorem run_qmatch_v5_binding (product : String) (bytes : ByteArray)
    (decision : Decision .qmatchSourceV5) (work left : Nat)
    (ok : (run .qmatchSourceV5 product bytes).run work = (.ok decision,left)) :
    Packet.read bytes = .ok decision.value.1 ∧ decision.value.1.scope = .execution ∧
      Nonempty (CheckedQmatchV5.Binding decision.value.1.original decision.value.1.graph
        decision.value.2 work left) := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ (by decide) ok
  exact CheckedQmatchV5.run_binding bytes decision.value work left checked

theorem run_openqasm_placement_binding (product : String) (bytes : ByteArray)
    (decision : Decision .openQasmPlacement) (work left : Nat)
    (ok : (run .openQasmPlacement product bytes).run work = (.ok decision,left)) :
    ∃ checked : CheckedQmatchV5.PlacementPacket.Checked bytes,
      (CheckedQmatchV5.PlacementPacket.check bytes).run work = (.ok checked,left) ∧
      product = productVersion ∧ decision = ⟨checked.source.1.edition,.execution,⟨bytes,checked⟩⟩ := by
  change (do
    Gate.guard (product == productVersion) .version
    let checked ← check .openQasmPlacement bytes
    pure ⟨checked.2.source.1.edition,.execution,checked⟩ : Gate.CheckM (Decision .openQasmPlacement)).run work =
      (.ok decision,left) at ok
  obtain ⟨_,start,version,rest⟩ := Gate.bind_success _ _ _ _ _ ok
  have ⟨productCheck, budget⟩ := Gate.guard_success _ _ _ _ version
  subst start
  obtain ⟨value,remaining,verified,returned⟩ := Gate.bind_success _ _ _ _ _ rest
  unfold check at verified
  obtain ⟨checked,after,placed,packed⟩ := Gate.bind_success _ _ _ _ _ verified
  cases packed
  cases returned
  exact ⟨checked,placed,beq_iff_eq.mp productCheck,rfl⟩

/-- Relate the executable reply to the counts recovered from the original
OpenQASM bytes and to the source workspace width those counts cover. -/
theorem run_openqasm_placement_resources (product : String) (bytes : ByteArray)
    (decision : Decision .openQasmPlacement) (work left : Nat)
    (ok : (run .openQasmPlacement product bytes).run work = (.ok decision,left)) :
    ∃ checked : CheckedQmatchV5.PlacementPacket.Checked bytes,
      let counts := checked.target.circuit.counts
      CheckedQmatchV5.PlacementPacket.split bytes = .ok checked.parts ∧
      (Target.CanonicalOpenQasmResources.decode checked.parts.target).map
        Target.CanonicalOpenQasmResources.Circuit.counts = some counts ∧
      checked.placement.trace.recorded.trace.peakWires ≤ counts.reserved ∧
      counts.reserved ≤ checked.proposal.capacity ∧
      (reply .openQasmPlacement work (.ok decision) left).lines.drop 6 =
        [work-left,counts.reserved,counts.reset,counts.gates,counts.swaps,
          counts.tGates,counts.measurements].map toString := by
  obtain ⟨checked,_,_,rfl⟩ := run_openqasm_placement_binding product bytes decision work left ok
  exact ⟨checked,checked.framed,checked.target_counts,checked.covers_workspace_peak,
    checked.target.capacityBound,rfl⟩

#print axioms run_openqasm_placement_resources

theorem run_typed_ordinary_binding (product : String) (bytes : ByteArray)
    (decision : Decision .ordinaryRoot) (work left : Nat)
    (ok : (run .ordinaryRoot product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .execution ∧
      Nonempty (CheckedOrdinaryRoot.Binding input.original input.graph decision.value work left) := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ (by decide) ok
  exact CheckedOrdinaryRoot.run_binding bytes decision.value work left checked

theorem run_typed_runtime_binding (product : String) (bytes : ByteArray)
    (decision : Decision .runtimeRoot) (work left : Nat)
    (ok : (run .runtimeRoot product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .execution ∧
      Nonempty (CheckedRuntimeRoot.Binding input.original input.graph decision.value work left) := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ (by decide) ok
  exact CheckedRuntimeRoot.run_binding bytes decision.value work left checked

theorem run_carrier_binding (product : String) (bytes : ByteArray)
    (decision : Decision .carrierPure) (work left : Nat)
    (ok : (run .carrierPure product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .execution ∧
      Nonempty (CheckedCarrier.Binding input.original input.graph decision.value work left) := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ (by decide) ok
  exact CheckedCarrier.run_binding bytes decision.value work left checked

theorem run_ordinary_root_safe (product : String) (bytes : ByteArray)
    (decision : Decision .ordinary) (work left : Nat)
    (ok : (run .ordinary product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧
      ∃ coreLeft, ∃ binding : Validity.Acceptance input.original decision.value.requested work coreLeft,
        ∃ program, binding.artifact.programs[binding.artifact.root]? = some program ∧
          Semantics.Ownership.OwnershipSafe program ∧ Semantics.ClassicalScope.ScopeSafe program := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ (by decide) ok
  exact Native.ordinary_root_safe bytes decision.value work left checked

theorem run_contract_binding (product : String) (bytes : ByteArray)
    (decision : Decision .contract) (work left : Nat)
    (ok : (run .contract product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ decision.value.1 = input.scope ∧
      (Native.contractInput input).run work = (.ok decision.value.2,left) := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ (by decide) ok
  exact Native.contract_binding bytes decision.value work left checked

theorem run_hierarchy_binding (mode : CheckedHierarchy.Modes.Mode) (product : String) (bytes : ByteArray)
    (decision : Decision (.hierarchy mode)) (work left : Nat)
    (ok : (run (.hierarchy mode) product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ decision.value.1 = input.scope ∧
      (Native.hierarchyInput mode input).run work = (.ok decision.value.2,left) := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ Mode.noConfusion ok
  exact Native.hierarchy_binding mode bytes decision.value work left checked

theorem run_engineering_pure_binding (product : String) (bytes : ByteArray)
    (decision : Decision .engineeringPure) (work left : Nat)
    (ok : (run .engineeringPure product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .execution ∧
      Nonempty (CheckedEngineeringPure.Binding input.original input.graph decision.value work left) := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ (by decide) ok
  exact CheckedEngineeringPure.run_binding bytes decision.value work left checked

theorem run_engineering_tensor_binding (product : String) (bytes : ByteArray)
    (decision : Decision .engineeringPureTensor) (work left : Nat)
    (ok : (run .engineeringPureTensor product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .execution ∧
      Nonempty (CheckedEngineeringPureTensor.Binding input.original input.graph decision.value work left) := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ (by decide) ok
  exact CheckedEngineeringPureTensor.run_binding bytes decision.value work left checked

theorem run_engineering_instrument_binding (product : String) (bytes : ByteArray)
    (decision : Decision .engineeringInstrument) (work left : Nat)
    (ok : (run .engineeringInstrument product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .execution ∧
      Nonempty (CheckedEngineeringInstrument.Binding input.original input.graph decision.value work left) := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ (by decide) ok
  exact Native.engineeringInstrument_binding bytes decision.value work left checked

theorem run_engineering_target_binding (product : String) (bytes : ByteArray)
    (decision : Decision .engineeringOpenQasm) (work left : Nat)
    (ok : (run .engineeringOpenQasm product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .execution ∧
      Nonempty (CheckedEngineeringOpenQasm.Binding input.original input.graph decision.value work left) := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ (by decide) ok
  exact CheckedEngineeringOpenQasm.run_binding bytes decision.value work left checked

theorem run_readout_binding (product : String) (bytes : ByteArray)
    (decision : Decision .readout) (work left : Nat)
    (ok : (run .readout product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .inspection ∧
      Protocol.Hierarchical.parseReadout input.original = .ok decision.value.packet ∧
      Hierarchical.Readout.check decision.value.packet.request decision.value.packet.packet
        decision.value.packet.budget = .ok decision.value.checked ∧ left = work := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ (by decide) ok
  exact check_readout_binding bytes decision.value work left checked

theorem run_preparation_binding (product : String) (bytes : ByteArray)
    (decision : Decision .preparation) (work left : Nat)
    (ok : (run .preparation product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .inspection ∧
      Protocol.Hierarchical.parsePreparation input.original = .ok decision.value.packet ∧
      Hierarchical.Preparation.check decision.value.packet.request decision.value.packet.packet
        decision.value.packet.budget = .ok decision.value.checked ∧ left = work := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ (by decide) ok
  exact check_preparation_binding bytes decision.value work left checked

end QleisliKernel.Protocol.NativeContext
