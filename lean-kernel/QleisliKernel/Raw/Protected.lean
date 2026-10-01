import QleisliKernel.Raw.Structure
import QleisliKernel.Semantics.Protected

/-! Actual protected dispatch exposes the clean-return checking obligation.
No finite expansion or assumed producer validity is used in these theorems.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw
open Semantics.Raw Semantics.Finite

theorem uses_diagonal (sourceBits ancillaBits targets : Nat) (uses : List Use)
    (valid : usesValid sourceBits ancillaBits targets uses = true) :
    ∀ location gate, Use.protectedGate location gate ∈ uses → gate = .z ∨ gate = .t := by
  intro location gate member
  have localValid := (List.all_eq_true.mp valid) _ member
  simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at localValid
  exact localValid.2

/-- The clean-return restriction is extracted from the executable original
constructor, including the source width actually consumed by the checker. -/
theorem dispatch_protected_conditions (dependencies : List Basis) (state : State)
    (input output : Nat) (targets : List Target) (ancilla function : List Nat) (uses : List Use)
    (result : Transition)
    (ok : dispatch dependencies state (.computeUseUncompute input output targets ancilla function uses) = .ok result) :
    ∃ source next ordered,
      take state input = .ok (source,next) ∧
      usesValid source.bits ancilla.length targets.length uses = true ∧
      result.events = [.protectedComputed state.frame.length ordered source.bits ancilla.length function uses] := by
  obtain ⟨⟨source,next⟩,ht,h⟩ := Finite.except_bind_success _ _ _ ok
  obtain ⟨⟨ports,after⟩,_,h⟩ := Finite.except_bind_success _ _ _ h
  obtain ⟨_,hg,h⟩ := Finite.except_bind_success _ _ _ h
  obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
  obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
  obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
  simp only [pure,Except.pure,Except.ok.injEq] at h
  subst result
  have good := require_success _ hg
  simp only [Bool.and_eq_true] at good
  exact ⟨source,next,_,ht,good.2,rfl⟩

end QleisliKernel.Raw
