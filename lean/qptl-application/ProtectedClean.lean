import Qleisli.RawProtected
import QPTL.Clean
import Mathlib.CategoryTheory.Types.Basic

/-! Apply QPTL's clean square to the actual protected Raw dispatch. The
original predicate table, uses and emitted event are retained. The computed
image equation is derived from the existing independent block semantics,
without assuming the final clean equation or constructing a dense matrix.
This proves no general source, CPTP-marginal or quantitative resource claim.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Raw.ProtectedClean
open CategoryTheory
open QleisliKernel.Semantics.Raw QleisliKernel.Semantics.Finite
open QleisliKernel.Raw Qleisli.Semantics.Protected

private theorem compute_inverse {R : Type} (function : Nat → Nat) :
    TypeCat.ofHom (compute (R := R) function) ≫ TypeCat.ofHom (compute function) =
      𝟙 (Physical R) := by
  apply ConcreteCategory.hom_ext
  intro ψ
  change compute function (compute function ψ) = ψ
  funext source ancilla target reference
  simp only [compute,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]

private theorem computed_intertwines {R : Type} (function : Nat → Nat) (uses : List Use)
    (valid : ∀ use ∈ uses, DiagonalProtected use) (ψ : Logical R) :
    run uses (compute function (zero ψ)) = compute function (zero (logical function uses ψ)) := by
  funext source ancilla target reference
  rw [run_blocks uses valid]
  have supported : compute function (zero ψ) source ancilla =
      (fun target reference => if ancilla ^^^ function source = 0 then ψ source target reference else 0) := rfl
  rw [supported]
  by_cases clean : ancilla ^^^ function source = 0
  · have same : ancilla = function source := by
      have canceled := congrArg (fun value => value ^^^ function source) clean
      simpa only [Nat.xor_assoc,Nat.xor_self,Nat.xor_zero,Nat.zero_xor] using canceled
    subst ancilla
    simp [compute,zero,logical]
  · simp only [compute,zero,if_neg clean,blocks_zero]

/-- The original supported use acts on the computed image with its full
complex phase. The arbitrary reference coordinate is untouched. -/
theorem computed_square {R : Type} (function : Nat → Nat) (uses : List Use)
    (valid : ∀ use ∈ uses, DiagonalProtected use) :
    CommSq (TypeCat.ofHom (logical (R := R) function uses))
      (TypeCat.ofHom zero ≫ TypeCat.ofHom (compute function))
      (TypeCat.ofHom zero ≫ TypeCat.ofHom (compute function))
      (TypeCat.ofHom (run uses)) := by
  refine ⟨?_⟩
  apply ConcreteCategory.hom_ext
  intro ψ
  change compute function (zero (logical function uses ψ)) = run uses (compute function (zero ψ))
  exact (computed_intertwines function uses valid ψ).symm

/-- Success of the actual constructor supplies all protected-use premises.
The result is a composable exact square for the original compute/use/inverse
compute, with the same zero encoding on both sides. Names, Unitary annotations
and source claims supply none of its evidence. -/
theorem accepted_clean_square {R : Type} (dependencies : List Basis) (state : State)
    (input output : Nat) (targets : List Target) (ancilla function : List Nat) (uses : List Use)
    (result : Transition)
    (ok : dispatch dependencies state (.computeUseUncompute input output targets ancilla function uses) = .ok result) :
    ∃ source next ordered,
      take state input = .ok (source,next) ∧
      result.events = [.protectedComputed state.frame.length ordered source.bits ancilla.length function uses] ∧
      CommSq (TypeCat.ofHom (logical (R := R) (fun source => function[source]?.getD 0) uses))
        (TypeCat.ofHom zero) (TypeCat.ofHom zero)
        (TypeCat.ofHom (compute (fun source => function[source]?.getD 0)) ≫
          TypeCat.ofHom (run uses) ≫ TypeCat.ofHom (compute (fun source => function[source]?.getD 0))) := by
  obtain ⟨source,next,ordered,taken,valid,events⟩ :=
    dispatch_protected_conditions _ _ _ _ _ _ _ _ _ ok
  refine ⟨source,next,ordered,taken,events,?_⟩
  exact QPTL.uncompute_square
    (computed_square _ uses (uses_valid_diagonal _ _ _ _ valid)) (compute_inverse _)

/-- Evaluate the accepted square on any correlated amplitude family. This
recovers the existing exact clean contract through the QPTL transport law;
no normalized branch, product-state premise or discarded coordinate is used. -/
theorem accepted_clean_action {R : Type} (dependencies : List Basis) (state : State)
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
  obtain ⟨source,next,ordered,taken,events,square⟩ :=
    accepted_clean_square (R := R) dependencies state input output targets ancilla function uses result ok
  refine ⟨source,next,ordered,taken,events,?_⟩
  exact (ConcreteCategory.congr_hom square.w ψ).symm

#print axioms computed_square
#print axioms accepted_clean_square
#print axioms accepted_clean_action
end Qleisli.Raw.ProtectedClean
