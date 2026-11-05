import Qleisli.Semantics.RawInstrument

/-! Sequential composition of the independent instrument judgment. Every
intermediate history family is retained, including zero-weight and hidden
outcomes; no normalization or bounded evaluator reassociation is involved.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.RawInstrument
open QleisliKernel.Semantics.Observation

theorem Run.append {dependencies : List QleisliKernel.Semantics.Finite.Dependency}
    {first rest : List Event} {initial middle final : List History}
    (left : Run dependencies first initial middle) (right : Run dependencies rest middle final) :
    Run dependencies (first ++ rest) initial final := by
  induction first generalizing initial middle with
  | nil => cases left; exact right
  | cons event events ih =>
    cases left with
    | cons _ _ _ groups _ localActions tail =>
      exact .cons event (events ++ rest) initial groups final localActions (ih tail right)

theorem Run.append_iff {dependencies : List QleisliKernel.Semantics.Finite.Dependency}
    (first rest : List Event) (initial final : List History) :
    Run dependencies (first ++ rest) initial final ↔
      ∃ middle, Run dependencies first initial middle ∧ Run dependencies rest middle final := by
  constructor
  · intro original
    induction first generalizing initial with
    | nil => exact ⟨initial,.nil _,original⟩
    | cons event events ih =>
      cases original with
      | cons _ _ _ groups _ localActions tail =>
        obtain ⟨middle,left,right⟩ := ih groups.flatten tail
        exact ⟨middle,.cons event events initial groups middle localActions left,right⟩
  · rintro ⟨middle,left,right⟩
    exact left.append right

#print axioms Run.append
#print axioms Run.append_iff
end Qleisli.Semantics.RawInstrument
