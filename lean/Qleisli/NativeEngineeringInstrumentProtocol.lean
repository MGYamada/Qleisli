import Qleisli.NativeEngineeringInstrument
import Protocol.ExecutionView.CheckedEngineeringInstrument
import Protocol.ExecutionView.Native

/-! The actual engineering instrument invocation retains both original bodies,
complete requested signatures, identities, Kraus completeness and public-output
projection, and compares its typed execution view exactly with the host view.
The complete reference-safe inequality supplies no exact cross-body equality,
coherent control, cleanup, target resources or constitutional admission.
Source/IR lowering, wire-decoder and native compiler/runtime preservation remain
separate obligations; this proves the executable Lean definition's meaning.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.NativeEngineeringInstrumentProtocol
open QleisliKernel
open QleisliKernel.Protocol.ExecutionView

/-- The subjects of the complete instrument bound are precisely the original
graphs and typed context retained by this successful outer native computation. -/
theorem run_meaning (bytes : ByteArray) (checked : CheckedEngineeringInstrument.Checked)
    (work left : Nat)
    (ok : (Native.engineeringInstrument bytes).run work = (.ok checked,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .execution ∧
      ∃ _binding : CheckedEngineeringInstrument.Binding input.original input.graph checked work left,
        Protocol.EngineeringInstrument.PreparedBinding input.original checked.prepared ∧
          ∃ projection, Qleisli.NativeEngineeringInstrument.Meaning checked.request checked.checked projection := by
  obtain ⟨input,parsed,scope,⟨binding⟩⟩ := Native.engineeringInstrument_binding _ _ _ _ ok
  have original := binding.original
  obtain ⟨_,_,afterExpected,_,_,_,accepted⟩ := original.stages
  exact ⟨input,parsed,scope,binding,Protocol.EngineeringInstrument.prepare_bound _ _ original.prepared,
    Qleisli.NativeEngineeringInstrument.check_meaning _ _ afterExpected binding.afterCore accepted⟩

end Qleisli.NativeEngineeringInstrumentProtocol
