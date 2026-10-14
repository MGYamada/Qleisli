import Qleisli.NativeEngineeringPureTensor
import Protocol.ExecutionView.CheckedEngineeringPureTensor

/-! The actual tensor invocation retains all six original byte decodings,
complete typed context and exact compared execution view. The bound uses the
caller's literal total budget, checked against the exact component sum. This
remains engineering evidence at zero and grants no exact/capability/cleanup,
source/target preservation, resource or constitutional authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.NativeEngineeringPureTensorProtocol
open QleisliKernel
open QleisliKernel.Protocol.ExecutionView
open Qleisli.EngineeringPureComposition

/-- The semantic subjects are precisely the six original bodies and typed
request retained by this actual execution-only native computation. -/
theorem run_meaning (bytes : ByteArray) (checked : CheckedEngineeringPureTensor.Checked) (work left : Nat)
    (ok : (CheckedEngineeringPureTensor.run bytes).run work = (.ok checked,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .execution ∧
      ∃ _binding : CheckedEngineeringPureTensor.Binding input.original input.graph checked work left,
        Protocol.EngineeringPureTensor.PreparedBinding input.original checked.prepared ∧
          Qleisli.NativeEngineeringPureTensor.Meaning checked.request checked.checked ∧
          checked.checked.epsilon = checked.decoded.epsilon := by
  obtain ⟨input,parsed,scope,⟨binding⟩⟩ := CheckedEngineeringPureTensor.run_binding _ _ _ _ ok
  have original := binding.original
  obtain ⟨_,_,_,_,_,_,afterRightIdeal,_,_,_,_,_,_,_,accepted⟩ := original.stages
  have facts := Qirf.EngineeringPureTensor.check_postcondition _ _ _ _ accepted
  exact ⟨input,parsed,scope,binding,Protocol.EngineeringPure.prepare_bound _ _ original.prepared,
    Qleisli.NativeEngineeringPureTensor.check_meaning _ _ afterRightIdeal binding.afterCore accepted,
    facts.requestedBudget⟩

/-- Arbitrary finite external references preserve the declared total budget.
This is the genuine additive tensor checker, not a parent Frobenius check.
No product-state or reference-dimension assumption weakens the result. -/
theorem run_reference_bound {R : Type} [Fintype R]
    (bytes : ByteArray) (checked : CheckedEngineeringPureTensor.Checked) (work left : Nat)
    (ok : (CheckedEngineeringPureTensor.run bytes).run work = (.ok checked,left)) :
    ‖operator (liftLeft (R := R)
      (matrixAt checked.decoded.actual.required.rows checked.decoded.actual.required.cols
        checked.decoded.actual.required -
        matrixAt checked.decoded.actual.required.rows checked.decoded.actual.required.cols
        checked.decoded.ideal.required))‖ ≤
      (Qleisli.Semantics.Exact.rational checked.decoded.epsilon : ℝ) := by
  obtain ⟨_,_,_,⟨binding⟩⟩ := CheckedEngineeringPureTensor.run_binding _ _ _ _ ok
  obtain ⟨_,_,_,_,_,_,afterRightIdeal,_,_,_,_,_,_,_,accepted⟩ := binding.original.stages
  have bound := Qleisli.NativeEngineeringPureTensor.checked_reference_bound (R := R)
    checked.request checked.checked afterRightIdeal binding.afterCore accepted
  have facts := Qirf.EngineeringPureTensor.check_postcondition _ _ _ _ accepted
  rw [facts.requestedBudget] at bound
  exact bound

end Qleisli.NativeEngineeringPureTensorProtocol
