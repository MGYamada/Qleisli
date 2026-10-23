import Qleisli.Semantics.OrdinaryValuePhi

/-! Conditional composition of actual branch runs and ordinary phi transport.
Arm meanings are independent logical relations. Each arm must prove its
preservation contract for actual Runs and represented inputs. The branch rule
derives the actual selected Bool and applies that contract to the selected Run;
it never assumes a representation of the requested merged output.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Semantics.OrdinaryValue
open QleisliKernel.Semantics
open QleisliKernel.Semantics.OrdinaryValue
open RawInstrument

/-- A compositional obligation for one actual arm, quantified over its complete
Run. `ready` records explicit caller obligations such as fresh event outputs.
`meaning` relates logical input/output values and contains no acceptance result.
The contract supplies an existential result for every actual arm history, rather
than assuming a caller's requested output value or merged storage representation.
It is a hypothesis to discharge for an arm, not a general source theorem. -/
def ArmRunPreserves (dependencies : List Finite.Dependency)
    (events : List Observation.Event) (ready : History → Prop)
    (inputBasis : FiniteCarrier.Basis) (inputStorage : Storage)
    (outputBasis : FiniteCarrier.Basis) (outputStorage : Storage)
    (meaning : Value → Value → Prop) : Prop :=
  ∀ (initial : History) (input : Value) (final : List History),
    ready initial → Represents initial.values inputBasis input inputStorage →
    Run dependencies events [initial] final →
    ∀ history ∈ final, ∃ result,
      meaning input result ∧ Represents history.values outputBasis result outputStorage

private theorem forall₂_strengthen_left {α β : Type} {relation stronger : α → β → Prop}
    {xs : List α} {ys : List β} (related : List.Forall₂ relation xs ys)
    (step : ∀ x ∈ xs, ∀ y, relation x y → stronger x y) :
    List.Forall₂ stronger xs ys := by
  revert step
  induction related with
  | nil => intro _; exact .nil
  | @cons x y xs ys head tail ih =>
    intro step
    exact .cons (step x List.mem_cons_self y head)
      (ih (fun x member y fact => step x (List.mem_cons_of_mem _ member) y fact))

/-- The actual condition chooses the actual arm Run. Its established logical
results move through actual simultaneous phis or unchanged identities into the
common output tree. The full ordered family is retained, and each output keeps
the selected arm history's complete hidden outcomes and unnormalized operator.

Freshness and uniqueness are explicit Raw obligations, not inferred here from
an accepted handle. The theorem does not prove source-site, enum-match predicate,
member/privacy, source/native binding or whole-program preservation. -/
theorem branch_transports_of_run_preservation
    (dependencies : List Finite.Dependency)
    (condition : Nat) (thenEvents elseEvents : List Observation.Event)
    (phis : List Observation.ClassicalPhi)
    (inputBasis outputBasis : FiniteCarrier.Basis)
    (inputStorage target : Storage) (armStorage : Bool → Storage)
    (meaning : Bool → Value → Value → Prop) (ready : History → Prop)
    (initial : History) (input : Value) (choice : Bool) (next : List History)
    (readyInitial : ready initial)
    (represented : Represents initial.values inputBasis input inputStorage)
    (conditionRepresented : Represents initial.values [.bit] (.bit choice) (.bit condition))
    (arms : ∀ selected, ArmRunPreserves dependencies
      (if selected then thenEvents else elseEvents) ready
      inputBasis inputStorage outputBasis (armStorage selected) (meaning selected))
    (moved : ∀ selected,
      StorageTransport (KeptOrPhiEdge selected phis) (armStorage selected) target)
    (fresh : ∀ (selected : Bool) (middle : List History),
      Run dependencies (if selected then thenEvents else elseEvents) [initial] middle →
      ∀ before ∈ middle, ∀ phi ∈ phis, lookup before.values phi.output = none)
    (unique : (phis.map Observation.ClassicalPhi.output).Nodup)
    (acted : Action dependencies (.branch condition thenEvents elseEvents phis) initial next) :
    ∃ middle,
      Run dependencies (if choice then thenEvents else elseEvents) [initial] middle ∧
      List.Forall₂ (fun before after => ∃ result,
        meaning choice input result ∧ Represents after.values outputBasis result target ∧
        after.hidden = before.hidden ∧ after.operator = before.operator) middle next := by
  have expected : lookup initial.values condition = some choice := by
    cases conditionRepresented with
    | bit id bit present => exact present
  cases acted with
  | branch condition thenEvents elseEvents phis initial actual middle next selected arm merges =>
    change lookup initial.values condition = some actual at selected
    have same : actual = choice := Option.some.inj (selected.symm.trans expected)
    subst actual
    refine ⟨middle,arm,?_⟩
    have results := arms choice initial input middle readyInitial represented arm
    apply forall₂_strengthen_left merges
    intro before member after merged
    obtain ⟨result,meaningResult,armRepresented⟩ := results before member
    have transported := merged_transports_kept before after choice phis armRepresented
      (moved choice) merged (fresh choice middle arm before member) unique
    exact ⟨result,meaningResult,transported.1,transported.2.1,transported.2.2⟩

end Qleisli.Semantics.OrdinaryValue
