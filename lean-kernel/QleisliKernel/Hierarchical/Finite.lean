import QleisliKernel.Hierarchical.Rule

/-! Bind finite unitary reconstruction requests to the actual artifact.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Pending requests are data, never evidence. The transitional Rust adapter must
reconstruct their complete bytes and independently check their exact equation. -/

namespace QleisliKernel.Hierarchical.Finite
open Artifact

deriving instance ReflBEq, LawfulBEq for Layout.TypeAtom, QuantumPort, ClassicalPort,
  Side, Interface, Rule

structure Request where
  index : Nat
  proof : Proof
  physical : Definition
  logical : Meaning
  program : ByteArray
  description : ByteArray
  deriving Repr

/-- Read full actual bodies; no hash, pointer or success flag is an input. -/
def project (artifact : Artifact) (index : Nat) : Option Request :=
  match artifact.proofs[index]? with
  | none => none
  | some proof =>
    match artifact.definitions[proof.implementation]?, artifact.meanings[proof.meaning]? with
    | some physical, some logical =>
      match physical.body, logical.body with
      | .leaf program, .finite description =>
        some ⟨index,proof,physical,logical,program,description⟩
      | _, _ => none
    | _, _ => none

def Bound (artifact : Artifact) (index : Nat) (request : Request) : Prop :=
  request.index = index ∧ artifact.proofs[index]? = some request.proof ∧
    artifact.definitions[request.proof.implementation]? = some request.physical ∧
    artifact.meanings[request.proof.meaning]? = some request.logical ∧
    request.physical.body = .leaf request.program ∧
    request.logical.body = .finite request.description

theorem project_binding (artifact : Artifact) (index : Nat) (request : Request)
    (projected : project artifact index = some request) : Bound artifact index request := by
  unfold project at projected
  split at projected
  next absent => contradiction
  next proof hp =>
    split at projected
    next physical logical hd hm =>
      split at projected
      next program description hb hl =>
        cases Option.some.inj projected
        exact ⟨rfl,hp,hd,hm,hb,hl⟩
      next => contradiction
    next => contradiction

theorem project_unique (artifact : Artifact) (index : Nat) (first second : Request)
    (left : project artifact index = some first)
    (right : project artifact index = some second) : first = second := by
  exact Option.some.inj (left.symm.trans right)

/-- Bits requires an explicit structural adapter; a width is not a type tree. -/
def legacy (basis : Basis) : Bool := basis.all fun atom => match atom with
  | .bits _ => false
  | _ => true

def unary (interface : Interface) : Bool :=
  NodeTyping.quantumOnly interface && interface.inputs.quantum.size == 1 &&
    interface.outputs.quantum.size == 1 && (do
      let input : QuantumPort ← interface.inputs.quantum[0]?
      let output : QuantumPort ← interface.outputs.quantum[0]?
      return input.basis == output.basis && legacy input.basis &&
        input.axes.size ≤ 6 && output.axes.size ≤ 6).getD false

/-- Only header and binding obligations; opaque bytes still require decoding. -/
def conditions (artifact : Artifact) (request : Request) : Bool :=
  request.proof.rule == Rule.finite && Rule.plain request.proof &&
    request.proof.premises.isEmpty && Power.identityEquation artifact request.proof &&
    request.physical.effect == Effect.unitary &&
    NodeTyping.conditions artifact request.physical &&
    ContractTyping.meaningConditions artifact request.logical &&
    request.physical.interface == request.logical.interface && unary request.physical.interface

structure Pending where
  request : Request
  visits : Nat
  deriving Repr

/-- Charge before traversing headers. Payload access uses complete immutable
arrays without parsing them; the actual finite checker separately charges that
work. Whole-artifact preparation additionally enforces aggregate byte limits. -/
def inspect (artifact : Artifact) (index remaining : Nat) : Except Error Pending :=
  if remaining > 2000000 then .error .limit else
  match artifact.proofs[index]? with
  | none => .error .invalidIr
  | some proof =>
    let initial := 64 + Power.proofSize proof + Rule.bodyCharge artifact proof
    if initial > remaining then .error .limit else
    let scan := initial + endpointCost sideScan artifact proof +
      Rule.actualHeaders artifact proof sideScan
    if scan > remaining then .error .limit else
    let charge := scan + 32 * (1 + endpointCost sideCharge artifact proof +
      Rule.actualHeaders artifact proof sideCharge)
    if charge > remaining then .error .limit else
    match project artifact index with
    | none => .error .contract
    | some request =>
      if request.program.size + request.description.size > 16777216 then .error .limit else
      if !conditions artifact request then .error .contract else .ok ⟨request,charge⟩

theorem inspect_conditions (artifact : Artifact) (index remaining : Nat) (pending : Pending)
    (accepted : inspect artifact index remaining = .ok pending) :
    pending.visits ≤ remaining ∧ remaining ≤ 2000000 ∧
    project artifact index = some pending.request ∧ Bound artifact index pending.request ∧
    conditions artifact pending.request = true ∧
    pending.request.program.size + pending.request.description.size ≤ 16777216 := by
  unfold inspect at accepted
  split at accepted
  next exceeded => contradiction
  next bounded =>
    split at accepted
    next absent => contradiction
    next proof hp =>
      dsimp only at accepted
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
            next absent => contradiction
            next request projected =>
              split at accepted
              next exceeded => contradiction
              next bytes =>
                split at accepted
                next rejected => contradiction
                next valid =>
                  cases Except.ok.inj accepted
                  exact ⟨Nat.le_of_not_gt charged,Nat.le_of_not_gt bounded,projected,
                    project_binding artifact index request projected,by simpa using valid,
                    Nat.le_of_not_gt bytes⟩

/-- Each successful result retains the actual full identity-encoding obligation.
No premise list may be omitted or hidden behind a finite receipt. -/
theorem inspect_identity (artifact : Artifact) (index remaining : Nat) (pending : Pending)
    (accepted : inspect artifact index remaining = .ok pending) :
    pending.request.proof.rule = .finite ∧ pending.request.proof.premises.isEmpty = true ∧
    Power.identityEquation artifact pending.request.proof = true ∧
    pending.request.physical.interface = pending.request.logical.interface := by
  have checked := (inspect_conditions artifact index remaining pending accepted).2.2.2.2.1
  simp only [conditions,Bool.and_eq_true,beq_iff_eq] at checked
  exact ⟨checked.1.1.1.1.1.1.1.1,checked.1.1.1.1.1.1.2,
    checked.1.1.1.1.1.2,checked.1.2⟩

end QleisliKernel.Hierarchical.Finite
