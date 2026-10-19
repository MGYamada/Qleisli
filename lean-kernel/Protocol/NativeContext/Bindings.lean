import Protocol.NativeContext

/-! Preservation through the actual pure native context dispatcher. These lemmas
retain existing original-packet, compared-view and scoped-root proof premises;
they neither admit new guarantees nor prove source, native IO or runtime behavior.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.NativeContext
open ExecutionView

theorem run_ordinary_root_safe (product : String) (bytes : ByteArray)
    (decision : Decision .ordinary) (work left : Nat)
    (ok : (run .ordinary product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧
      ∃ coreLeft, ∃ binding : Validity.Acceptance input.original decision.value.requested work coreLeft,
        ∃ program, binding.artifact.programs[binding.artifact.root]? = some program ∧
          Semantics.Ownership.OwnershipSafe program ∧ Semantics.ClassicalScope.ScopeSafe program := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ ok
  exact Native.ordinary_root_safe bytes decision.value work left checked

theorem run_contract_binding (product : String) (bytes : ByteArray)
    (decision : Decision .contract) (work left : Nat)
    (ok : (run .contract product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ decision.value.1 = input.scope ∧
      (Native.contractInput input).run work = (.ok decision.value.2,left) := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ ok
  exact Native.contract_binding bytes decision.value work left checked

theorem run_hierarchy_binding (mode : CheckedHierarchy.Modes.Mode) (product : String) (bytes : ByteArray)
    (decision : Decision (.hierarchy mode)) (work left : Nat)
    (ok : (run (.hierarchy mode) product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ decision.value.1 = input.scope ∧
      (Native.hierarchyInput mode input).run work = (.ok decision.value.2,left) := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ ok
  exact Native.hierarchy_binding mode bytes decision.value work left checked

theorem run_engineering_pure_binding (product : String) (bytes : ByteArray)
    (decision : Decision .engineeringPure) (work left : Nat)
    (ok : (run .engineeringPure product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .execution ∧
      Nonempty (CheckedEngineeringPure.Binding input.original input.graph decision.value work left) := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ ok
  exact CheckedEngineeringPure.run_binding bytes decision.value work left checked

theorem run_engineering_tensor_binding (product : String) (bytes : ByteArray)
    (decision : Decision .engineeringPureTensor) (work left : Nat)
    (ok : (run .engineeringPureTensor product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .execution ∧
      Nonempty (CheckedEngineeringPureTensor.Binding input.original input.graph decision.value work left) := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ ok
  exact CheckedEngineeringPureTensor.run_binding bytes decision.value work left checked

theorem run_engineering_instrument_binding (product : String) (bytes : ByteArray)
    (decision : Decision .engineeringInstrument) (work left : Nat)
    (ok : (run .engineeringInstrument product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .execution ∧
      Nonempty (CheckedEngineeringInstrument.Binding input.original input.graph decision.value work left) := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ ok
  exact Native.engineeringInstrument_binding bytes decision.value work left checked

theorem run_engineering_target_binding (product : String) (bytes : ByteArray)
    (decision : Decision .engineeringOpenQasm) (work left : Nat)
    (ok : (run .engineeringOpenQasm product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .execution ∧
      Nonempty (CheckedEngineeringOpenQasm.Binding input.original input.graph decision.value work left) := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ ok
  exact CheckedEngineeringOpenQasm.run_binding bytes decision.value work left checked

theorem run_readout_binding (product : String) (bytes : ByteArray)
    (decision : Decision .readout) (work left : Nat)
    (ok : (run .readout product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .inspection ∧
      Protocol.Hierarchical.parseReadout input.original = .ok decision.value.packet ∧
      Hierarchical.Readout.check decision.value.packet.request decision.value.packet.packet
        decision.value.packet.budget = .ok decision.value.checked ∧ left = work := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ ok
  exact check_readout_binding bytes decision.value work left checked

theorem run_preparation_binding (product : String) (bytes : ByteArray)
    (decision : Decision .preparation) (work left : Nat)
    (ok : (run .preparation product bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .inspection ∧
      Protocol.Hierarchical.parsePreparation input.original = .ok decision.value.packet ∧
      Hierarchical.Preparation.check decision.value.packet.request decision.value.packet.packet
        decision.value.packet.budget = .ok decision.value.checked ∧ left = work := by
  obtain ⟨_,_,_,_,_,checked,_⟩ := run_binding _ _ _ _ _ _ ok
  exact check_preparation_binding bytes decision.value work left checked

end QleisliKernel.Protocol.NativeContext
