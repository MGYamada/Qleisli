import QleisliKernel.Raw.Pure
import Qleisli.RawFunction
import Qleisli.RawProtected
import Qleisli.Semantics.RawAction
import Qleisli.Semantics.RawPure

/-! Complete straight-line pure extraction, fresh evidence and scope semantics.
This boundary preserves the literal complex action of all original events.
The general source soundness/production authority gates remain separate.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Raw.Pure
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Raw
open QleisliKernel.Semantics.Function QleisliKernel.Raw QleisliKernel.Raw.Pure QleisliKernel.Finite
open Qleisli.Semantics.Protected Qleisli.Semantics.Raw

theorem event_cleanup (dependencies : List Dependency) (event : Event) (work left : Nat)
    (ok : (eventCheck dependencies event).run work = (.ok (),left)) : CleanupMeaning dependencies event := by
  cases event with
  | circuit _ _ | init0 _ | liftBasis _ _ _ _ _ | reorder _ _ => trivial
  | computed bits axes sourceBits ancillaBits function uses logicalSteps =>
    obtain ⟨logical,middle,hc,_⟩ := bind_success _ _ _ _ _ ok
    exact ⟨logical,clean_denotes _ _ _ _ _ _ _ _ _ _ hc⟩
  | protectedComputed bits axes sourceBits ancillaBits function uses =>
    have valid := (guard_success _ _ _ _ ok).1
    simp only [Bool.and_eq_true] at valid
    intro R ψ
    exact clean_factorization _ _ (uses_valid_diagonal _ _ _ _ valid.2) ψ

/-- Every original pure constructor preserves its full phase-sensitive complex
action at the Rust/Lean boundary, including wide frames and scalar Unit actions.
The proof uses actual checking/extraction, not Rust verification or a supplied
extracted trace. Broad and protected cleanup have their own obligations below. -/
theorem verify_complex_denotation (dependencies : List Dependency) (body : Program) (prepared : Prepared)
    (work left : Nat) (ok : (verify dependencies body).run work = (.ok prepared,left)) (ψ : Nat → ℂ) :
    Qleisli.Semantics.RawAction.program dependencies body ψ =
      some (Qleisli.Semantics.RawAction.events dependencies prepared.events ψ) := by
  have original := (verify_conditions _ _ _ _ _ ok).2.1
  simp [Qleisli.Semantics.RawAction.program,original,Prepared.reference]

theorem verify_scopes (dependencies : List Dependency) (body : Program) (prepared : Prepared)
    (work left : Nat) (ok : (verify dependencies body).run work = (.ok prepared,left)) :
    ∀ event ∈ prepared.events, CleanupMeaning dependencies event := by
  intro event member
  rcases (verify_conditions _ _ _ _ _ ok).2.2 event member with ⟨a,b,checked⟩
  exact event_cleanup _ _ _ _ checked

/-- Complete general pure acceptance starts from raw dependencies and separate
attachments, proves every fresh body and preserves the original operator and
all auxiliary release scopes. No externally supplied receipt is trusted. -/
theorem inspect_semantics (inputs : List Input) (bindings : List Binding) (body : Program)
    (checked : Checked) (work left : Nat)
    (ok : (inspect inputs bindings body).run work = (.ok checked,left)) :
    checked.program = body ∧ Function.GraphMeaning checked.receipts ∧
    checked.receipts.map (·.input) = inputs ∧ inputs = bindings ∧
    (∀ ψ : Nat → ℂ, Qleisli.Semantics.RawAction.program (checked.receipts.map Receipt.dependency) body ψ =
      some (Qleisli.Semantics.RawAction.events (checked.receipts.map Receipt.dependency) checked.prepared.events ψ)) ∧
    (∀ event ∈ checked.prepared.events, CleanupMeaning (checked.receipts.map Receipt.dependency) event) := by
  rcases inspect_fresh _ _ _ _ _ _ ok with ⟨bodyEq,a,b,c,d,hf,hp⟩
  rcases Function.checkAll_semantics _ _ _ _ _ hf with ⟨graph,identities,bindings⟩
  exact ⟨bodyEq,graph,identities,bindings,verify_complex_denotation _ _ _ _ _ hp,verify_scopes _ _ _ _ _ hp⟩

end Qleisli.Raw.Pure
