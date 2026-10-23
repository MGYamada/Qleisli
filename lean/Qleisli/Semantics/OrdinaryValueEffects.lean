import Qleisli.Semantics.OrdinaryValue

/-! Existing ordinary values across actual quantum events.
These are facts about the original unnormalized RawInstrument histories. An
observing event retains every outcome; it is not converted to a pure event.
The lemmas do not authorize a native request or prove source preservation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.OrdinaryValue
open QleisliKernel.Semantics
open QleisliKernel.Semantics.OrdinaryValue
open RawInstrument

private theorem related_before {A B : Type} {relation : A → B → Prop}
    {xs : List A} {ys : List B} (related : List.Forall₂ relation xs ys)
    {after : B} (member : after ∈ ys) : ∃ before ∈ xs, relation before after := by
  induction related with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | member
    · subst after
      exact ⟨_,List.mem_cons_self,head⟩
    · obtain ⟨before,held,related⟩ := ih member
      exact ⟨before,List.mem_cons_of_mem _ held,related⟩

/-- A quantum operation changes its complete operator, while existing ordinary
bindings retain their values. No separability premise is used. -/
theorem pure_preserves_existing {basis logical storage event initial next}
    {dependencies : List QleisliKernel.Semantics.Finite.Dependency}
    (represented : Represents initial.values basis logical storage)
    (acted : Action dependencies (.pure event) initial next) :
    ∀ after ∈ next, Represents after.values basis logical storage := by
  cases acted with
  | pure event initial operator map meaning composition =>
    intro after member
    have same := List.mem_singleton.mp member
    subst after
    exact represented

/-- Every actual erasure outcome keeps old ordinary bindings. Hidden outcomes
and the quantum operator are retained as the original Erased relation states;
this is not a purity or identity-action theorem. -/
theorem erase_preserves_existing {basis logical storage bits axes output initial next}
    {dependencies : List QleisliKernel.Semantics.Finite.Dependency}
    (represented : Represents initial.values basis logical storage)
    (acted : Action dependencies (.erase bits axes output) initial next) :
    ∀ after ∈ next, Represents after.values basis logical storage := by
  cases acted with
  | erase bits axes output initial next allOutcomes =>
    intro after member
    obtain ⟨outcome,_,erased⟩ := related_before allOutcomes member
    rw [erased.2.1]
    cases output with
    | none => exact represented
    | some id => exact represented.extends (append_extends _ _)

/-- When an actual erasure exposes a fresh classical output, every retained
history represents the exact Bool written by that original event. The theorem
does not claim a measurement width, source typing or a probability guarantee. -/
theorem erase_fresh_bit {bits axes output initial next}
    {dependencies : List QleisliKernel.Semantics.Finite.Dependency}
    (acted : Action dependencies (.erase bits axes (some output)) initial next)
    (fresh : lookup initial.values output = none) :
    ∀ after ∈ next, ∃ outcome ∈ List.range (2^axes.length),
      after.hidden = initial.hidden ++ [outcome] ∧
      Represents after.values [.bit] (.bit (outcome == 1)) (.bit output) := by
  cases acted with
  | erase bits axes output initial next allOutcomes =>
    intro after member
    obtain ⟨outcome,held,erased⟩ := related_before allOutcomes member
    refine ⟨outcome,held,erased.1,?_⟩
    rw [erased.2.1]
    exact .bit _ _ (lookup_append_fresh _ fresh)

end Qleisli.Semantics.OrdinaryValue
