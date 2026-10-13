import Qleisli.NativeEngineeringPure
import Protocol.ExecutionView.CheckedEngineeringPure

/-! The actual engineering native entry point retains its original byte
decodings, both checked bodies, typed context and exact host-view comparison.
This establishes the pure engineering inequality only. It grants no exact
cross-body equality, execution capability, resource bound or ledger admission.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.NativeEngineeringPureProtocol
open QleisliKernel
open QleisliKernel.Protocol.ExecutionView

/-- The semantic subjects are precisely the request and checked bodies returned
by this native computation, with its original packet and view binding. -/
theorem run_meaning (bytes : ByteArray) (checked : CheckedEngineeringPure.Checked) (work left : Nat)
    (ok : (CheckedEngineeringPure.run bytes).run work = (.ok checked,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .execution ∧
      ∃ _binding : CheckedEngineeringPure.Binding input.original input.graph checked work left,
        Protocol.EngineeringPure.PreparedBinding input.original checked.prepared ∧
          Qleisli.NativeEngineeringPure.Meaning checked.request checked.checked := by
  obtain ⟨input,parsed,scope,⟨binding⟩⟩ := CheckedEngineeringPure.run_binding _ _ _ _ ok
  have original := binding.original
  obtain ⟨_,_,afterIdeal,_,_,_,accepted⟩ := original.stages
  exact ⟨input,parsed,scope,binding,Protocol.EngineeringPure.prepare_bound _ _ original.prepared,
    Qleisli.NativeEngineeringPure.check_meaning _ _ afterIdeal binding.afterCore accepted⟩

open scoped BigOperators in
/-- The bound from the actual decoded invocation holds on arbitrary finite
joint inputs, without a separability premise or a reference-size factor. -/
theorem run_reference_square {R : Type} [Fintype R]
    (bytes : ByteArray) (checked : CheckedEngineeringPure.Checked) (work left : Nat)
    (ok : (CheckedEngineeringPure.run bytes).run work = (.ok checked,left))
    (joint : Fin checked.decoded.actual.required.cols → R → ℂ) :
    (∑ reference, ∑ row : Fin checked.decoded.actual.required.rows, Complex.normSq
      (∑ col : Fin checked.decoded.actual.required.cols,
        Qleisli.Semantics.EngineeringPure.gapMatrix checked.decoded.actual.required.rows
          checked.decoded.actual.required.cols checked.decoded.actual.required
            checked.decoded.ideal.required row col * joint col reference)) ≤
      (Qleisli.Semantics.Exact.rational checked.decoded.epsilon : ℝ) ^ 2 *
        ∑ reference, ∑ col : Fin checked.decoded.actual.required.cols,
          Complex.normSq (joint col reference) := by
  obtain ⟨_,_,_,⟨binding⟩⟩ := CheckedEngineeringPure.run_binding _ _ _ _ ok
  obtain ⟨_,_,afterIdeal,_,_,_,accepted⟩ := binding.original.stages
  exact Qleisli.NativeEngineeringPure.check_reference_square checked.request checked.checked
    afterIdeal binding.afterCore accepted joint

end Qleisli.NativeEngineeringPureProtocol
