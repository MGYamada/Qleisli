import QleisliKernel.Hierarchical.Finite

/-! Reuse actual complete-artifact typing when matching ordinary proof rules.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
This entry alone is not acceptance: its soundness requires the actual typing
pass on the same immutable artifact. No serialized typed flag is an input. -/

namespace QleisliKernel.Hierarchical.TypedRule
open Artifact

def Context (artifact : Artifact) : Prop :=
  (∀ (i : Nat) (d : Definition), artifact.definitions[i]? = some d → NodeTyping.conditions artifact d = true) ∧
  (∀ (i : Nat) (m : Meaning), artifact.meanings[i]? = some m → ContractTyping.meaningConditions artifact m = true)

theorem context_of_checkAll (artifact : Artifact) (order : Array Nat) (typed : ContractTyping.Typed)
    (accepted : ContractTyping.checkAll artifact order = .ok typed) : Context artifact := by
  have facts := ContractTyping.checkAll_conditions artifact order typed accepted
  constructor
  · intro i d found
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    obtain ⟨other,foundOther,checked⟩ :=
      (NodeTyping.checkAll_conditions artifact order typed.nodes facts.1).2.2.2 i inside
    have same := Option.some.inj (found.symm.trans foundOther)
    simpa [← same] using checked
  · intro i m found
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    obtain ⟨other,foundOther,checked⟩ := ContractTyping.checkAll_meaning artifact order typed i accepted inside
    have same := Option.some.inj (found.symm.trans foundOther)
    simpa [← same] using checked

/-- Compare every equation boundary and ordered premise binding, but do not
repeat already established node/meaning typing or quadratic layout checks. -/
def ordinary (artifact : Artifact) (proof : Proof) : Bool :=
  Rule.plain proof && Power.identityEquation artifact proof && (do
    let physical ← artifact.definitions[proof.implementation]?
    let logical ← artifact.meanings[proof.meaning]?
    let ps ← Rule.premises artifact proof
    return physical.effect == Effect.unitary && NodeTyping.quantumOnly physical.interface &&
      ps.all (Power.identityEquation artifact) && Rule.bodies proof physical logical ps).getD false

theorem ordinary_sound (artifact : Artifact) (context : Context artifact) (proof : Proof)
    (accepted : ordinary artifact proof = true) : Rule.ordinary artifact proof = true := by
  cases hd : artifact.definitions[proof.implementation]? with
  | none => simp [ordinary,hd] at accepted
  | some d =>
    cases hm : artifact.meanings[proof.meaning]? with
    | none => simp [ordinary,hd,hm] at accepted
    | some m =>
      have typedD := context.1 _ _ hd
      have typedM := context.2 _ _ hm
      simpa only [ordinary,Rule.ordinary,hd,hm,bind,Option.bind,typedD,typedM,Bool.and_true] using accepted

/-- Complete equality scans are linear in serialized endpoint fields. All
uniqueness, type-tree and permutation predicates remain in the earlier pass. -/
def sideFields (side : Side) : Nat := Artifact.sideFields side

def check (artifact : Artifact) (index remaining : Nat) : Except Error Rule.Checked :=
  if remaining > Limits.maxVisits then .error .limit else
  match artifact.proofs[index]? with
  | none => .error .invalidIr
  | some proof =>
    match proof.rule with
    | .schema _ => Rule.check artifact index remaining
    | _ =>
      let initial := 32 + Power.proofSize proof + Rule.bodyCharge artifact proof
      if initial > remaining then .error .limit else
      let scan := initial + endpointCost sideScan artifact proof +
        Rule.premiseCost artifact proof sideScan
      if scan > remaining then .error .limit else
      let charge := scan + 8 * (1 + endpointCost sideFields artifact proof +
        Rule.premiseCost artifact proof sideFields + Rule.bodyCharge artifact proof)
      if charge > remaining then .error .limit else
      if ordinary artifact proof then .ok ⟨charge⟩ else .error .contract

theorem check_conditions (artifact : Artifact) (context : Context artifact)
    (index remaining : Nat) (checked : Rule.Checked)
    (accepted : check artifact index remaining = .ok checked) :
    checked.visits ≤ remaining ∧ remaining ≤ 2000000 ∧ Rule.Matches artifact index := by
  unfold check at accepted
  split at accepted
  next exceeded => contradiction
  next bounded =>
    split at accepted
    next absent => contradiction
    next proof found =>
      split at accepted
      next schema => exact Rule.check_conditions artifact index remaining checked accepted
      next ordinaryRule =>
        dsimp only at accepted
        split at accepted
        next exceeded => contradiction
        next sized =>
          split at accepted
          next exceeded => contradiction
          next scanned =>
            split at accepted
            next exceeded => contradiction
            next charged =>
              split at accepted
              next matched =>
                cases Except.ok.inj accepted
                exact ⟨Nat.le_of_not_gt charged,Nat.le_of_not_gt bounded,proof,found,
                  Or.inl (ordinary_sound artifact context proof matched)⟩
              next rejected => contradiction

end QleisliKernel.Hierarchical.TypedRule
