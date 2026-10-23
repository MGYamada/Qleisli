import Qleisli.Semantics.OrdinaryValueEffects

/-! Controls for the actual Raw quantum/erase actions.
Physical map meanings and compositions are explicit independent obligations;
these examples do not calculate matrices or assume target representations.
The erasure controls construct both original one-axis outcomes, not a selected
outcome. No native acceptance, source preservation or typed replay is claimed.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Semantics.OrdinaryValue.EffectsExamples
open QleisliKernel.Semantics
open QleisliKernel.Semantics.Exact
open QleisliKernel.Semantics.OrdinaryValue
open Qleisli.Semantics.RawInstrument

private theorem zero_width_pair {values : Valuation}
    (present : lookup values 0 = some false) :
    Represents values [.pair,.unit,.bit] (.pair .unit (.bit false)) (.pair .unit (.bit 0)) :=
  .pair [.unit] [.bit] .unit (.bit false) .unit (.bit 0) .unit (.bit 0 false present)

/-- Pure-event preservation applies to the complete ordinary tree even when
its Unit child uses no classical coordinate. The operator may change. -/
theorem pure_keeps_zero_width_tree
    (dependencies : List Finite.Dependency) (before : History)
    (event : QleisliKernel.Semantics.Raw.Event) (next map : Matrix)
    (values : before.values = [(0,false)])
    (meaning : Qleisli.Semantics.Raw.EventMeaning dependencies event map)
    (composition : Qleisli.Semantics.Raw.Composition map before.operator next) :
    let after : History := {before with operator := next}
    Action dependencies (.pure event) before [after] ∧
      Represents after.values [.pair,.unit,.bit]
        (.pair .unit (.bit false)) (.pair .unit (.bit 0)) ∧
      after.hidden = before.hidden ∧ after.operator = next := by
  dsimp only
  have represented := zero_width_pair (values := before.values) (by rw [values]; rfl)
  have acted := Action.pure event before next map meaning composition
  exact ⟨acted,pure_preserves_existing represented acted
    ({before with operator := next} : History) (by simp),rfl,rfl⟩

private def erasedHistory (before : History) (output : Option Nat)
    (outcome : Nat) (operator : Matrix) : History :=
  { values := match output with
      | none => before.values
      | some id => before.values ++ [(id,outcome == 1)]
    hidden := before.hidden ++ [outcome]
    operator := operator }

/-- Construct the full actual one-axis erasure action from its two independent
physical meanings and compositions. Both histories occur, in outcome order. -/
theorem two_outcome_action
    (dependencies : List Finite.Dependency) (before : History) (output : Option Nat)
    (operator0 operator1 map0 map1 : Matrix)
    (meaning0 : ErasureMeaning 1 [0] 0 map0)
    (composition0 : Qleisli.Semantics.Raw.Composition map0 before.operator operator0)
    (meaning1 : ErasureMeaning 1 [0] 1 map1)
    (composition1 : Qleisli.Semantics.Raw.Composition map1 before.operator operator1) :
    Action dependencies (.erase 1 [0] output) before
      [erasedHistory before output 0 operator0,erasedHistory before output 1 operator1] := by
  apply Action.erase
  change List.Forall₂ (Erased 1 [0] output before) [0,1]
    [erasedHistory before output 0 operator0,erasedHistory before output 1 operator1]
  exact .cons ⟨rfl,rfl,map0,meaning0,composition0⟩
    (.cons ⟨rfl,rfl,map1,meaning1,composition1⟩ .nil)

/-- Every original erasure outcome preserves the zero-width ordinary child
and the old Bit, while its fresh output is exactly the original event's Bool. -/
theorem fresh_measurement_keeps_both_outcomes
    (dependencies : List Finite.Dependency) (before : History)
    (operator0 operator1 map0 map1 : Matrix)
    (values : before.values = [(0,false)])
    (meaning0 : ErasureMeaning 1 [0] 0 map0)
    (composition0 : Qleisli.Semantics.Raw.Composition map0 before.operator operator0)
    (meaning1 : ErasureMeaning 1 [0] 1 map1)
    (composition1 : Qleisli.Semantics.Raw.Composition map1 before.operator operator1) :
    let histories := [erasedHistory before (some 1) 0 operator0,
      erasedHistory before (some 1) 1 operator1]
    Action dependencies (.erase 1 [0] (some 1)) before histories ∧
      ∀ after ∈ histories,
        Represents after.values [.pair,.unit,.bit]
          (.pair .unit (.bit false)) (.pair .unit (.bit 0)) ∧
        ∃ outcome ∈ List.range (2 ^ ([0] : List Nat).length),
          after.hidden = before.hidden ++ [outcome] ∧
          Represents after.values [.bit] (.bit (outcome == 1)) (.bit 1) := by
  dsimp only
  have acted := two_outcome_action dependencies before (some 1)
    operator0 operator1 map0 map1 meaning0 composition0 meaning1 composition1
  have represented := zero_width_pair (values := before.values) (by rw [values]; rfl)
  have fresh : lookup before.values 1 = none := by rw [values]; rfl
  refine ⟨acted,?_⟩
  intro after member
  exact ⟨erase_preserves_existing represented acted after member,
    erase_fresh_bit acted fresh after member⟩

/-- No-output erasure still retains both hidden outcomes and the complete old
ordinary tree. It supplies no new classical Bit. -/
theorem discard_keeps_zero_width_tree
    (dependencies : List Finite.Dependency) (before : History)
    (operator0 operator1 map0 map1 : Matrix)
    (values : before.values = [(0,false)])
    (meaning0 : ErasureMeaning 1 [0] 0 map0)
    (composition0 : Qleisli.Semantics.Raw.Composition map0 before.operator operator0)
    (meaning1 : ErasureMeaning 1 [0] 1 map1)
    (composition1 : Qleisli.Semantics.Raw.Composition map1 before.operator operator1) :
    let histories := [erasedHistory before none 0 operator0,erasedHistory before none 1 operator1]
    Action dependencies (.erase 1 [0] none) before histories ∧
      ∀ after ∈ histories, Represents after.values [.pair,.unit,.bit]
        (.pair .unit (.bit false)) (.pair .unit (.bit 0)) := by
  dsimp only
  have acted := two_outcome_action dependencies before none
    operator0 operator1 map0 map1 meaning0 composition0 meaning1 composition1
  have represented := zero_width_pair (values := before.values) (by rw [values]; rfl)
  exact ⟨acted,erase_preserves_existing represented acted⟩

/-- Dropping either outcome cannot satisfy the actual one-axis erase action. -/
theorem postselection_is_not_an_erase
    (dependencies : List Finite.Dependency) (before after : History) (output : Option Nat) :
    ¬ Action dependencies (.erase 1 [0] output) before [after] := by
  intro acted
  cases acted with
  | erase bits axes output initial next allOutcomes =>
    have size := allOutcomes.length_eq
    simp at size

/-- An incoming binding is not fresh merely because an erase appends the same ID. -/
theorem reused_output_is_not_fresh (before : History)
    (values : before.values = [(0,false)]) : lookup before.values 0 ≠ none := by
  rw [values]
  decide

/-- At outcome 1 an appended true value still cannot replace an old false
binding. This is an actual Erased history, conditional only on its physical map. -/
theorem collision_preserves_old_and_rejects_new
    (before : History) (operator map : Matrix)
    (values : before.values = [(0,false)])
    (meaning : ErasureMeaning 1 [0] 1 map)
    (composition : Qleisli.Semantics.Raw.Composition map before.operator operator) :
    Erased 1 [0] (some 0) before 1 (erasedHistory before (some 0) 1 operator) ∧
      Represents (erasedHistory before (some 0) 1 operator).values [.bit] (.bit false) (.bit 0) ∧
      ¬ Represents (erasedHistory before (some 0) 1 operator).values [.bit] (.bit true) (.bit 0) := by
  refine ⟨⟨rfl,rfl,map,meaning,composition⟩,.bit 0 false ?_,?_⟩
  · simp [erasedHistory,values,lookup]
  · intro represented
    cases represented with
    | bit id bit present => simp [erasedHistory,values,lookup] at present

end Qleisli.Semantics.OrdinaryValue.EffectsExamples
