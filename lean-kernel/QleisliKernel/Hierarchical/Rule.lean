import QleisliKernel.Hierarchical.Power

/-! Exact local rule matching for whole-space unitary provider equations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Matching alone is not a derivation: every premise must be established on the
same artifact. Finite payloads and unsupported rules reject in this first pass. -/

namespace QleisliKernel.Hierarchical.Rule
open Artifact

def plain (proof : Proof) : Bool :=
  proof.witness.templateVersion == 1 && proof.witness.parameters.isEmpty &&
    proof.witness.references.isEmpty

def premisePair (proof : Proof) : Nat × Nat := (proof.implementation,proof.meaning)

def premises (artifact : Artifact) (proof : Proof) : Option (Array Proof) :=
  proof.premises.mapM (fun index => artifact.proofs[index]?)

def sameMap (physical logical : PortMap) : Bool :=
  physical.owners == logical.owners && physical.axes == logical.axes &&
    physical.classical == logical.classical

def identityMap (interface : Interface) (map : PortMap) : Bool :=
  interface.inputs == interface.outputs &&
    map.owners == Array.range interface.inputs.quantum.size &&
    map.axes == Array.range (wires interface.inputs).size && map.classical.isEmpty

/-- Ordered actual children must be exactly those of the premise equations.
An equal-size array, shared name or declaration annotation is insufficient. -/
def children (ps : Array Proof) (physical logical : Array Nat) : Bool :=
  physical == ps.map Proof.implementation && logical == ps.map Proof.meaning

def bodies (proof : Proof) (physical : Definition) (logical : Meaning)
    (ps : Array Proof) : Bool :=
  match proof.rule, physical.body, logical.body with
  | .rewire, .rewire p, .rewire m => ps.isEmpty && sameMap p m
  | .rewire, .rewire p, .identity => ps.isEmpty && identityMap physical.interface p
  | .structural, .structural p, .structural m => ps.isEmpty && p == m
  | .phase, .dyadicPhase _ j k, .phase l h => ps.isEmpty && j == l && k == h
  | .sequence, .sequence p, .sequence m => children ps p m
  | .tensor, .tensor p q, .tensor m n => children ps #[p,q] #[m,n]
  | .inverse, .inverse p, .inverse m => children ps #[p] #[m]
  | .control, .control p b, .control m c => b == c && children ps #[p] #[m]
  | .repeatOp, .repeatOp n p, .power m k => n == k && children ps #[p] #[m]
  | _, _, _ => false

def ordinary (artifact : Artifact) (proof : Proof) : Bool :=
  plain proof && Power.identityEquation artifact proof && (do
    let physical ← artifact.definitions[proof.implementation]?
    let logical ← artifact.meanings[proof.meaning]?
    let ps ← premises artifact proof
    return physical.effect == Effect.unitary && NodeTyping.quantumOnly physical.interface &&
      NodeTyping.conditions artifact physical && ContractTyping.meaningConditions artifact logical &&
      ps.all (Power.identityEquation artifact) && bodies proof physical logical ps).getD false

/-- Precharge array lengths before traversal, then full endpoint comparisons.
This includes premise metadata and body-array matching, without circuit expansion. -/
def bodyCharge (artifact : Artifact) (proof : Proof) : Nat :=
  (artifact.definitions[proof.implementation]?.map (fun d => d.body.charge)).getD 0 +
    (artifact.meanings[proof.meaning]?.map (fun m => m.body.charge)).getD 0

def premiseCost (artifact : Artifact) (proof : Proof) (cost : Side → Nat) : Nat :=
  proof.premises.foldl (fun sum index => sum + 1 +
    (artifact.proofs[index]?.map (fun p => Power.proofSize p + endpointCost cost artifact p)).getD 0) 0

def actualHeaders (artifact : Artifact) (proof : Proof) (cost : Side → Nat) : Nat :=
  (artifact.definitions[proof.implementation]?.map (NodeTyping.headerCost cost artifact)).getD 0 +
    (artifact.meanings[proof.meaning]?.map (fun m =>
      ContractTyping.Subject.headerCost cost artifact (.meaning m))).getD 0

structure Checked where
  visits : Nat
  deriving Repr

def check (artifact : Artifact) (index remaining : Nat) : Except Error Checked :=
  if remaining > Limits.maxVisits then .error .limit else
  match artifact.proofs[index]? with
  | none => .error .invalidIr
  | some proof =>
    let initial := 64 + Power.proofSize proof + bodyCharge artifact proof
    if initial > remaining then .error .limit else
    let scan := initial + endpointCost sideScan artifact proof + premiseCost artifact proof sideScan +
      actualHeaders artifact proof sideScan
    if scan > remaining then .error .limit else
    let charge := scan + 32 * (1 + bodyCharge artifact proof + endpointCost sideCharge artifact proof +
      premiseCost artifact proof sideCharge + actualHeaders artifact proof sideCharge)
    if charge > remaining then .error .limit else
    match proof.rule with
    | .schema "controlled-power/1" =>
      match proof.witness.parameters[0]?, proof.witness.parameters[1]? with
      | some exponent, some provider =>
        match Power.inspect artifact index exponent provider (remaining - charge) with
        | .error kind => .error kind
        | .ok pending => .ok ⟨charge + pending.visits⟩
      | _, _ => .error .contract
    | _ => if ordinary artifact proof then .ok ⟨charge⟩ else .error .contract

/-- A local rule's exact predicate, including actual schema projection. This
does not assume or establish any premise equations. -/
def Matches (artifact : Artifact) (index : Nat) : Prop :=
  ∃ proof, artifact.proofs[index]? = some proof ∧
    (ordinary artifact proof = true ∨ ∃ exponent provider remaining pending,
      Power.inspect artifact index exponent provider remaining = .ok pending)

theorem check_conditions (artifact : Artifact) (index remaining : Nat) (checked : Checked)
    (accepted : check artifact index remaining = .ok checked) :
    checked.visits ≤ remaining ∧ remaining ≤ 2000000 ∧ Matches artifact index := by
  unfold check at accepted
  split at accepted
  next outside => contradiction
  next capacity =>
    cases hp : artifact.proofs[index]? with
    | none => simp [hp] at accepted
    | some proof =>
      simp only [hp] at accepted
      split at accepted
      next exceeded => contradiction
      next initial =>
        split at accepted
        next exceeded => contradiction
        next scanned =>
          split at accepted
          next exceeded => contradiction
          next charged =>
            split at accepted
            next schema =>
              split at accepted
              next exponent provider hk hv =>
                split at accepted
                next error hi => contradiction
                next pending hi =>
                  cases Except.ok.inj accepted
                  obtain ⟨_,_,_,_,_,_,cost,_⟩ := Power.inspect_binding artifact index exponent provider _ pending hi
                  refine ⟨by dsimp only; omega,Nat.le_of_not_gt capacity,proof,hp,Or.inr ?_⟩
                  exact ⟨exponent,provider,_,pending,hi⟩
              next => contradiction
            next other =>
              split at accepted
              next matched =>
                cases Except.ok.inj accepted
                exact ⟨Nat.le_of_not_gt charged,Nat.le_of_not_gt capacity,proof,hp,Or.inl matched⟩
              next rejected => contradiction

end QleisliKernel.Hierarchical.Rule
