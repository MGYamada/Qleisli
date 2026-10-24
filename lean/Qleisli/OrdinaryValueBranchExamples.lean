import Qleisli.Semantics.OrdinaryValueBranch

/-! Uncompiled controls for actual branch/arm composition. Constant-arm
preservation is proved from Run inversion, not an assumed output Represents.
All hidden histories and operators remain arbitrary. No acceptance is claimed.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Semantics.OrdinaryValue.BranchExamples
open QleisliKernel.Semantics
open QleisliKernel.Semantics.OrdinaryValue
open RawInstrument

private theorem constant_run_result (dependencies : List Finite.Dependency)
    (initial : History) (output : Nat) (bit : Bool) (final : List History)
    (run : Run dependencies [.classical (.constant bit) output] [initial] final) :
    final = [{initial with values := initial.values ++ [(output,bit)]}] := by
  cases run with
  | cons event events initial groups final localActions rest =>
    cases localActions with
    | cons event initial produced remaining groups head tail =>
      cases tail
      cases head with
      | classical expr output initial result evaluated =>
        have same : result = bit := Option.some.inj evaluated.symm
        subst result
        cases rest
        rfl

/-- A concrete non-identity arm contract. The logical result is forced by the
original constant event, for every actual Run from a ready represented input. -/
theorem constant_arm_preserves (dependencies : List Finite.Dependency)
    (output : Nat) (bit : Bool) (ready : History → Prop)
    (fresh : ∀ initial, ready initial → lookup initial.values output = none) :
    ArmRunPreserves dependencies [.classical (.constant bit) output] ready
      [.unit] .unit [.bit] (.bit output) (fun _ result => result = .bit bit) := by
  intro initial input final readyInitial _ run
  have sameFinal := constant_run_result dependencies initial output bit final run
  subst final
  intro after member
  have same := List.mem_singleton.mp member
  subst after
  exact ⟨.bit bit,rfl,.bit output bit (lookup_append_fresh bit (fresh initial readyInitial))⟩

/-- Both arm contracts are discharged from their real classical Runs. The
branch theorem then derives the selected logical Bit at the actual phi output.
No output representation, matrix equality, normalized probability or purity
premise is supplied by this example. -/
theorem constant_branches_derive_selected_value
    (dependencies : List Finite.Dependency) (initial : History) (choice : Bool)
    (next : List History) (values : initial.values = [(0,choice)])
    (acted : Action dependencies
      (.branch 0 [.classical (.constant true) 1] [.classical (.constant false) 2]
        [⟨1,2,3⟩]) initial next) :
    ∃ middle,
      Run dependencies
        (if choice then [.classical (.constant true) 1] else [.classical (.constant false) 2])
        [initial] middle ∧
      List.Forall₂ (fun before after => ∃ result,
        result = .bit choice ∧ Represents after.values [.bit] result (.bit 3) ∧
        after.hidden = before.hidden ∧ after.operator = before.operator) middle next := by
  let ready : History → Prop := fun history =>
    lookup history.values 1 = none ∧ lookup history.values 2 = none
  have readyInitial : ready initial := by
    constructor <;> change lookup initial.values _ = none <;> rw [values] <;> rfl
  have arms : ∀ selected, ArmRunPreserves dependencies
      (if selected then [.classical (.constant true) 1] else [.classical (.constant false) 2])
      ready [.unit] .unit [.bit] (.bit (if selected then 1 else 2))
      (fun _ result => result = .bit selected) := by
    intro selected
    cases selected with
    | false => exact constant_arm_preserves dependencies 2 false ready (fun _ h => h.2)
    | true => exact constant_arm_preserves dependencies 1 true ready (fun _ h => h.1)
  have moved : ∀ selected, StorageTransport (KeptOrPhiEdge selected [⟨1,2,3⟩])
      (.bit (if selected then 1 else 2)) (.bit 3) := by
    intro selected
    refine .bit _ _ (Or.inr ?_)
    exact ⟨⟨1,2,3⟩,List.mem_cons_self,rfl,rfl⟩
  have fresh : ∀ (selected : Bool) (middle : List History),
      Run dependencies
        (if selected then [.classical (.constant true) 1] else [.classical (.constant false) 2])
        [initial] middle → ∀ before ∈ middle,
      ∀ phi ∈ ([⟨1,2,3⟩] : List Observation.ClassicalPhi), lookup before.values phi.output = none := by
    intro selected middle run before member phi held
    have samePhi := List.mem_singleton.mp held
    subst phi
    cases selected with
    | false =>
      have same := constant_run_result dependencies initial 2 false middle run
      subst middle
      have same := List.mem_singleton.mp member
      subst before
      change lookup (initial.values ++ [(2,false)]) 3 = none
      rw [values]
      rfl
    | true =>
      have same := constant_run_result dependencies initial 1 true middle run
      subst middle
      have same := List.mem_singleton.mp member
      subst before
      change lookup (initial.values ++ [(1,true)]) 3 = none
      rw [values]
      rfl
  exact branch_transports_of_run_preservation dependencies 0
    [.classical (.constant true) 1] [.classical (.constant false) 2] [⟨1,2,3⟩]
    [.unit] [.bit] .unit (.bit 3) (fun selected => .bit (if selected then 1 else 2))
    (fun selected _ result => result = .bit selected) ready initial .unit choice next
    readyInitial .unit (.bit 0 choice (by rw [values]; rfl)) arms moved fresh (by decide) acted

/-- A false stored condition cannot supply the opposite represented choice. -/
theorem wrong_condition_representation :
    ¬ Represents [(0,false)] [.bit] (.bit true) (.bit 0) := by
  intro represented
  cases represented with
  | bit id bit present => simp [lookup,List.find?] at present

/-- A generic branch contract must not change the logical value established
by its arm. The two distinct constant results cannot satisfy one another. -/
theorem opposite_constant_is_not_selected :
    ¬ ((Value.bit false) = Value.bit true) := by
  intro same
  cases same

/-- Even permissive identity edges cannot erase a zero-width tree child. -/
theorem dropped_unit_cannot_supply_transport :
    ¬ StorageTransport (fun _ _ => True) (.pair .unit (.bit 1)) (.bit 3) := by
  intro moved
  cases moved

/-- The conclusion pairs complete families; a two-history selected arm cannot
be replaced by one retained output, regardless of their operators. -/
theorem dropped_history_cannot_supply_family (first second after : History) :
    ¬ List.Forall₂ (fun (_ _ : History) => True) [first,second] [after] := by
  intro paired
  have length := paired.length_eq
  simp at length

#check @ArmRunPreserves
#check @branch_transports_of_run_preservation
#print axioms branch_transports_of_run_preservation
#print axioms constant_arm_preserves
#print axioms constant_branches_derive_selected_value

end Qleisli.Semantics.OrdinaryValue.BranchExamples
