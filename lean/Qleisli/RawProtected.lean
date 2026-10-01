import QleisliKernel.Raw.Protected
import Qleisli.Semantics.Protected

/-! Non-dense exact clean release from actual executable protected dispatch.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Raw
open QleisliKernel.Semantics.Raw QleisliKernel.Semantics.Finite
open QleisliKernel.Raw Qleisli.Semantics.Protected

theorem uses_valid_diagonal (sourceBits ancillaBits targets : Nat) (uses : List Use)
    (valid : usesValid sourceBits ancillaBits targets uses = true) :
    ∀ use ∈ uses, DiagonalProtected use := by
  intro use member
  cases use with
  | protectedGate location gate => exact uses_diagonal _ _ _ _ valid location gate member
  | targetGate _ _ _ | phase _ _ => trivial

/-- The actual original constructor's successful dispatch is sufficient for
exact zero return on arbitrary correlated complex amplitudes, at every width.
The statement retains original uses and has no finite extraction premise. -/
theorem accepted_protected_clean {R : Type} (dependencies : List Basis) (state : State)
    (input output : Nat) (targets : List Target) (ancilla function : List Nat) (uses : List Use)
    (result : Transition)
    (ok : dispatch dependencies state (.computeUseUncompute input output targets ancilla function uses) = .ok result)
    (ψ : Logical R) :
    ∃ source next ordered,
      take state input = .ok (source,next) ∧
      result.events = [.protectedComputed state.frame.length ordered source.bits ancilla.length function uses] ∧
      compute (fun source => function[source]?.getD 0)
          (run uses (compute (fun source => function[source]?.getD 0) (zero ψ))) =
        zero (logical (fun source => function[source]?.getD 0) uses ψ) := by
  rcases dispatch_protected_conditions _ _ _ _ _ _ _ _ _ ok with ⟨source,next,ordered,ht,hv,he⟩
  exact ⟨source,next,ordered,ht,he,clean_factorization _ _ (uses_valid_diagonal _ _ _ _ hv) ψ⟩

end Qleisli.Raw
