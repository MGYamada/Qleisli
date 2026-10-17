import QleisliKernel.Hierarchical.Finite

/-! Reuse actual complete-artifact typing when matching ordinary proof rules.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
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

/-- Facts from this invocation's complete typing pass. Proof fields are erased
from execution; no serialized flag, hash or foreign artifact can supply them. -/
structure PreparedContext (artifact : Artifact) : Prop where
  typed : Context artifact
  identity : Power.IdentityContext artifact

theorem preparedContext_of_checkAll (artifact : Artifact) (order : Array Nat)
    (typed : ContractTyping.Typed)
    (accepted : ContractTyping.checkAll artifact order = .ok typed) : PreparedContext artifact := by
  refine ⟨context_of_checkAll artifact order typed accepted,?_,?_⟩
  · have nodes := (ContractTyping.checkAll_conditions artifact order typed accepted).1
    exact prepare_proofEndpoints artifact order typed.nodes.prepared
      (NodeTyping.checkAll_conditions artifact order typed.nodes nodes).1
  · intro i encoding found
    obtain ⟨other,otherFound,checked⟩ := ContractTyping.checkAll_encoding artifact order typed i
      accepted (Array.getElem?_eq_some_iff.mp found).1
    have same := Option.some.inj (found.symm.trans otherFound)
    simpa [← same] using checked

/-- The premise array is still collected from its ordered actual proof indices. -/
def preparedOrdinary (artifact : Artifact) (proof : Proof) : Bool :=
  Rule.plain proof && Power.preparedIdentityEquation artifact proof && (do
    let physical ← artifact.definitions[proof.implementation]?
    let logical ← artifact.meanings[proof.meaning]?
    let ps ← Rule.premises artifact proof
    return physical.effect == Effect.unitary && NodeTyping.quantumOnly physical.interface &&
      ps.all (Power.preparedIdentityEquation artifact) && Rule.bodies proof physical logical ps).getD false

private theorem list_mapM_member {A B : Type} (f : A → Option B) (xs : List A) (ys : List B)
    (computed : xs.mapM f = some ys) :
    ∀ y ∈ ys, ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil =>
    have same : ys = [] := by simpa using computed.symm
    subst ys
    simp
  | cons head rest ih =>
    cases hh : f head with
    | none => simp [List.mapM_cons,hh] at computed
    | some value =>
      cases ht : rest.mapM f with
      | none => simp [List.mapM_cons,hh,ht] at computed
      | some values =>
        have same : ys = value::values := by simpa [List.mapM_cons,hh,ht] using computed.symm
        subst ys
        intro y member
        rcases List.mem_cons.mp member with same | member
        · subst y
          exact ⟨head,by simp,hh⟩
        · obtain ⟨x,inside,found⟩ := ih values ht y member
          exact ⟨x,List.mem_cons_of_mem head inside,found⟩

private theorem preparedPremises_eq (artifact : Artifact) (context : PreparedContext artifact)
    (proof : Proof) (ps : Array Proof) (found : Rule.premises artifact proof = some ps) :
    ps.all (Power.preparedIdentityEquation artifact) = ps.all (Power.identityEquation artifact) := by
  have mapped : proof.premises.toList.mapM (fun index => artifact.proofs[index]?) = some ps.toList := by
    rw [← Array.toList_mapM]
    change Array.toList <$> Rule.premises artifact proof = _
    rw [found]
    rfl
  have same : ∀ premise ∈ ps.toList,
      Power.preparedIdentityEquation artifact premise = Power.identityEquation artifact premise := by
    intro premise member
    obtain ⟨index,_,indexed⟩ := list_mapM_member _ _ _ mapped premise member
    exact Power.preparedIdentityEquation_eq artifact context.identity index premise indexed
  rw [Bool.eq_iff_iff,← Array.all_toList,← Array.all_toList,List.all_eq_true,List.all_eq_true]
  constructor
  · intro all premise member
    rw [← same premise member]
    exact all premise member
  · intro all premise member
    rw [same premise member]
    exact all premise member

/-- Own and premise equations are equivalent to the original predicate only
through their actual indexed objects, not a shape-only or arbitrary proof value. -/
theorem preparedOrdinary_eq (artifact : Artifact) (context : PreparedContext artifact)
    (index : Nat) (proof : Proof) (found : artifact.proofs[index]? = some proof) :
    preparedOrdinary artifact proof = ordinary artifact proof := by
  have own := Power.preparedIdentityEquation_eq artifact context.identity index proof found
  cases hd : artifact.definitions[proof.implementation]? with
  | none => simp [preparedOrdinary,ordinary,own,hd]
  | some physical =>
    cases hm : artifact.meanings[proof.meaning]? with
    | none => simp [preparedOrdinary,ordinary,own,hd,hm]
    | some logical =>
      cases hp : Rule.premises artifact proof with
      | none => simp [preparedOrdinary,ordinary,own,hd,hm,hp]
      | some ps =>
        have premises := preparedPremises_eq artifact context proof ps hp
        simp [preparedOrdinary,ordinary,own,hd,hm,hp,premises]

/-- Only lengths and actual proof-table lookups remain here. Full endpoint
scans are charged and executed once in Artifact.projectProof, and identity-side
comparison once in ContractTyping; this function does not repeat those scans. -/
def preparedPremiseMetadata (artifact : Artifact) (proof : Proof) : Nat :=
  proof.premises.foldl (fun sum index => sum + 1 +
    (artifact.proofs[index]?.map Power.proofSize).getD 0) 0

/-- Same ordinary rule with a proved same-artifact reuse path. Precharge the
premise scan before collecting it; 16 units per own/premise equation retain its
two encoding lookups and exact body-tag/kind checks. The existing metadata/body
factor remains. Schema rules take the unchanged standalone checker directly. -/
def checkPrepared (artifact : Artifact) (_context : PreparedContext artifact)
    (index remaining : Nat) : Except Error Rule.Checked :=
  if remaining > Limits.maxVisits then .error .limit else
  match artifact.proofs[index]? with
  | none => .error .invalidIr
  | some proof =>
    match proof.rule with
    | .schema _ => Rule.check artifact index remaining
    | _ =>
      let initial := 32 + Power.proofSize proof + Rule.bodyCharge artifact proof
      if initial > remaining then .error .limit else
      let scan := initial + 16 * proof.premises.size
      if scan > remaining then .error .limit else
      let metadata := preparedPremiseMetadata artifact proof
      let charge := scan + metadata + 8 * (1 + metadata + Rule.bodyCharge artifact proof) +
        16 * (1 + proof.premises.size)
      if charge > remaining then .error .limit else
      if preparedOrdinary artifact proof then .ok ⟨charge⟩ else .error .contract

theorem checkPrepared_conditions (artifact : Artifact) (context : PreparedContext artifact)
    (index remaining : Nat) (checked : Rule.Checked)
    (accepted : checkPrepared artifact context index remaining = .ok checked) :
    checked.visits ≤ remaining ∧ remaining ≤ 2000000 ∧ Rule.Matches artifact index := by
  unfold checkPrepared at accepted
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
                have original : ordinary artifact proof = true := by
                  simpa only [preparedOrdinary_eq artifact context index proof found] using matched
                exact ⟨Nat.le_of_not_gt charged,Nat.le_of_not_gt bounded,proof,found,
                  Or.inl (ordinary_sound artifact context.typed proof original)⟩
              next rejected => contradiction

end QleisliKernel.Hierarchical.TypedRule
