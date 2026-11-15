import Qleisli.NativeEngineeringOpenQasm
import Protocol.ExecutionView.CheckedEngineeringOpenQasm

/-! Actual execution-only target-native binding: original target bytes,
independent ordered word, generated actual graph, freshly decoded ideal graph,
complete typed request and exact compared QDV1 view. The complete-adjoint bound
is engineering-only, including at zero. The optional literal gate budget has
the same target identity and engineering scope.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.NativeEngineeringOpenQasmProtocol
open QleisliKernel
open QleisliKernel.Protocol.ExecutionView

/-- Success links the exact original packet and execution-view comparison to
the same decoded target bytes and complete original-body instrument meanings. -/
theorem run_meaning (bytes : ByteArray) (checked : CheckedEngineeringOpenQasm.Checked)
    (work left : Nat)
    (ok : (CheckedEngineeringOpenQasm.run bytes).run work = (.ok checked,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .execution ∧
      ∃ _binding : CheckedEngineeringOpenQasm.Binding input.original input.graph checked work left,
        Protocol.EngineeringOpenQasm.PreparedBinding input.original checked.prepared ∧
          Qleisli.NativeEngineeringOpenQasm.Meaning checked.request checked.checked := by
  obtain ⟨input,parsed,scope,⟨binding⟩⟩ := CheckedEngineeringOpenQasm.run_binding _ _ _ _ ok
  have original := binding.original
  obtain ⟨_,afterExpected,afterInstrument,_,_,accepted,_⟩ := original.stages
  exact ⟨input,parsed,scope,binding,Protocol.EngineeringInstrument.prepare_bound _ _ original.prepared,
    Qleisli.NativeEngineeringOpenQasm.check_meaning _ _ afterExpected afterInstrument accepted⟩

/-- CompleteAdjointBound quantifies every finite reference and every joint
observable. Its literal budget is the caller's decoded epsilon; the subjects
are the target-generated actual and freshly checked original ideal instrument. -/
theorem run_complete_adjoint_bound (bytes : ByteArray) (checked : CheckedEngineeringOpenQasm.Checked)
    (work left : Nat)
    (ok : (CheckedEngineeringOpenQasm.run bytes).run work = (.ok checked,left)) :
    ∃ projection : Semantics.InstrumentContract.Projection,
      Qleisli.Semantics.EngineeringInstrument.CompleteAdjointBound
        (Qleisli.NativeEngineeringInstrument.originalOperators
          (2^checked.checked.instrument.actualInstrument.structureCheck.state.quantum.frame.length)
          (2^checked.checked.instrument.actualInstrument.structureCheck.prepared.inputBits)
          projection.classicalBits checked.checked.instrument.actual.program.classicalOutputs
          checked.checked.instrument.actualInstrument.histories)
        (Qleisli.NativeEngineeringInstrument.originalOperators
          (2^checked.checked.instrument.actualInstrument.structureCheck.state.quantum.frame.length)
          (2^checked.checked.instrument.actualInstrument.structureCheck.prepared.inputBits)
          projection.classicalBits checked.checked.instrument.expected.program.classicalOutputs
          checked.checked.instrument.expectedInstrument.histories)
        (Qleisli.Semantics.Exact.rational checked.decoded.epsilon : ℝ) := by
  obtain ⟨_,_,_,_,_,meaning⟩ := run_meaning _ _ _ _ ok
  obtain ⟨projection,instrument⟩ := meaning.instrument
  exact ⟨projection,instrument.bound⟩

/-- The resource-bearing execution checks the budgets on the literal target
used for the instrument comparison. It cannot count a separate word. -/
theorem run_literal_gate_limits (bytes : ByteArray) (checked : CheckedEngineeringOpenQasm.Checked)
    (work left : Nat) (limits : Target.CanonicalOpenQasm.GateCounts)
    (requested : checked.decoded.limits = some limits)
    (ok : (CheckedEngineeringOpenQasm.run bytes).run work = (.ok checked,left)) :
    checked.checked.target.original = checked.prepared.body ∧
      checked.checked.target.gateCounts.within limits = true := by
  obtain ⟨_,_,_,_,_,meaning⟩ := run_meaning _ _ _ _ ok
  have bound := checked.resourceBound
  rw [requested] at bound
  exact ⟨meaning.originalTarget,bound⟩

end Qleisli.NativeEngineeringOpenQasmProtocol
