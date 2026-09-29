import QleisliKernel.Hierarchical.ContractTyping
import QleisliKernel.Schema

/-! Bind a controlled-power component to actual four-table artifact data.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
The result retains a required provider proof, not a semantic evidence seal.
Finite reconstruction and generic derivation checking remain separate. -/

namespace QleisliKernel.Hierarchical.Power
open Artifact

/-- Read only actual implementation bodies. The local control is the leading
Bit checked by the surrounding complete-interface condition. -/
def implementationStage (artifact : Artifact) (index : Nat) : Option ControlledPowers.Stage := do
  let root ← artifact.definitions[index]?
  let .control child polarity := root.body | none
  let repeated ← artifact.definitions[child]?
  let .repeatOp count provider := repeated.body | none
  return ⟨0,provider,count,polarity⟩

structure LogicalStage where
  provider : Nat
  count : Nat
  polarity : Bool
  deriving BEq, DecidableEq, Repr

/-- A meaning reference is a different domain from an implementation reference. -/
def meaningStage (artifact : Artifact) (index : Nat) : Option LogicalStage := do
  let root ← artifact.meanings[index]?
  let .control child polarity := root.body | none
  let powered ← artifact.meanings[child]?
  let .power provider count := powered.body | none
  return ⟨provider,count,polarity⟩

/-- Only these whole-space boundaries are admitted by this direct schema.
Restricted-range control needs its own two-sector derivation. -/
def identityEquation (artifact : Artifact) (proof : Proof) : Bool :=
  (do
    let input ← artifact.encodings[proof.inputEncoding]?
    let output ← artifact.encodings[proof.outputEncoding]?
    let .identity := input.body | none
    let .identity := output.body | none
    return proof.kind == Kind.equation && proof.bounded && endpoints artifact proof &&
      input.logical == input.physical && output.logical == output.physical).getD false

/-- Header work includes the root, its immediate repeat/power nodes, provider,
and both premise encodings. Body contents remain for the whole-artifact pass. -/
def stageHeaders (artifact : Artifact) (proof : Proof) : Array Ref :=
  let base := #[⟨.definition,proof.implementation⟩,⟨.meaning,proof.meaning⟩,
    ⟨.encoding,proof.inputEncoding⟩,⟨.encoding,proof.outputEncoding⟩]
  let defs := (do
    let root ← artifact.definitions[proof.implementation]?
    let .control child _ := root.body | none
    let repeated ← artifact.definitions[child]?
    let .repeatOp _ provider := repeated.body | none
    return (#[⟨Table.definition,child⟩,⟨Table.definition,provider⟩] : Array Ref)).getD #[]
  let meanings := (do
    let root ← artifact.meanings[proof.meaning]?
    let .control child _ := root.body | none
    let powered ← artifact.meanings[child]?
    let .power provider _ := powered.body | none
    return (#[⟨Table.meaning,child⟩,⟨Table.meaning,provider⟩] : Array Ref)).getD #[]
  base ++ defs ++ meanings

def proofSize (proof : Proof) : Nat :=
  1 + proof.premises.size + proof.witness.parameters.size + proof.witness.references.size

def headerCost (cost : Side → Nat) (artifact : Artifact) (root premise : Proof) : Nat :=
  (stageHeaders artifact root ++ stageHeaders artifact premise).foldl
    (fun n ref => n + 1 + NodeTyping.refCost cost artifact ref) 0

def providerBinding (premise : Proof) (actual : ControlledPowers.Stage) (logical : LogicalStage) : Bool :=
  premise.implementation == actual.targetDefinition && premise.meaning == logical.provider &&
    actual.count == logical.count && actual.whenOne == logical.polarity

/-- Recheck the small fixed shape and exact endpoints. These conditions do not
establish the provider premise's semantic equation, even if its rule is finite. -/
def shape (artifact : Artifact) (root premise : Proof)
    (actual : ControlledPowers.Stage) (logical : LogicalStage) : Bool :=
  providerBinding premise actual logical && (do
    let d ← artifact.definitions[root.implementation]?
    let .control repeatedIndex _ := d.body | none
    let repeated ← artifact.definitions[repeatedIndex]?
    let provider ← artifact.definitions[actual.targetDefinition]?
    let m ← artifact.meanings[root.meaning]?
    let .control poweredIndex _ := m.body | none
    let powered ← artifact.meanings[poweredIndex]?
    let meaning ← artifact.meanings[logical.provider]?
    return identityEquation artifact root && identityEquation artifact premise &&
      NodeTyping.closed provider && ContractTyping.pureMeaning meaning &&
      meaning.interface.inputs == meaning.interface.outputs &&
      NodeTyping.conditions artifact d && NodeTyping.conditions artifact repeated &&
      ContractTyping.meaningConditions artifact m && ContractTyping.meaningConditions artifact powered).getD false

structure Pending where
  root : Proof
  actual : ControlledPowers.Stage
  logical : LogicalStage
  providerProofIndex : Nat
  providerProof : Proof
  visits : Nat
  deriving Repr

def proposal (root : Proof) (actual : ControlledPowers.Stage) : Schema.Proposal :=
  let id := match root.rule with | .schema id => id | _ => ""
  ⟨id,root.witness.templateVersion,root.witness.parameters.toList,.power actual⟩

def finish (artifact : Artifact) (root premise : Proof) (premiseIndex : Nat)
    (actual : ControlledPowers.Stage) (logical : LogicalStage)
    (exponent provider initial remaining : Nat) : Except Error Pending :=
  let scan := initial + proofSize premise + headerCost sideScan artifact root premise
  if scan > remaining then .error .limit else
  let charge := scan + 32 * (1 + headerCost sideCharge artifact root premise)
  if charge > remaining then .error .limit else
  if !shape artifact root premise actual logical then .error .contract else
  if (Schema.check (.power exponent provider) (proposal root actual)).isNone then .error .contract else
  .ok ⟨root,actual,logical,premiseIndex,premise,charge⟩

/-- This local entry does not check arbitrary premise derivations. The caller
must discharge the returned provider proof on the same immutable artifact. -/
def inspect (artifact : Artifact) (index exponent provider remaining : Nat) : Except Error Pending :=
  if remaining > 2000000 || exponent > 12 || !u32 provider then .error .limit else
  match artifact.proofs[index]? with
  | none => .error .invalidIr
  | some root =>
    let initial := 64 + proofSize root
    if initial > remaining then .error .limit else
    if root.premises.size != 1 || !root.witness.references.isEmpty then .error .contract else
    match root.premises[0]? with
    | none => .error .contract
    | some premiseIndex =>
      if premiseIndex == index then .error .contract else
      match artifact.proofs[premiseIndex]?, implementationStage artifact root.implementation,
          meaningStage artifact root.meaning with
      | some premise, some actual, some logical =>
        finish artifact root premise premiseIndex actual logical exponent provider initial remaining
      | _, _, _ => .error .contract

theorem finish_binding (artifact : Artifact) (root premise : Proof) (premiseIndex : Nat)
    (actual : ControlledPowers.Stage) (logical : LogicalStage)
    (exponent provider initial remaining : Nat) (pending : Pending)
    (accepted : finish artifact root premise premiseIndex actual logical exponent provider initial remaining = .ok pending) :
    ∃ charge, pending = ⟨root,actual,logical,premiseIndex,premise,charge⟩ ∧ charge ≤ remaining ∧
    shape artifact root premise actual logical = true ∧
    ∃ receipt, Schema.check (.power exponent provider) (proposal root actual) = some receipt := by
  unfold finish at accepted
  dsimp only at accepted
  split at accepted
  next invalid => contradiction
  next scanned =>
    split at accepted
    next invalid => contradiction
    next charged =>
      split at accepted
      next invalid => contradiction
      next valid =>
        split at accepted
        next rejected => contradiction
        next component =>
          cases Except.ok.inj accepted
          refine ⟨_,rfl,Nat.le_of_not_gt charged,by simpa using valid,?_⟩
          cases hc : Schema.check (.power exponent provider) (proposal root actual) with
          | none => simp [hc] at component
          | some receipt => exact ⟨receipt,rfl⟩

theorem singleton_premise (entries : Array Nat) (index : Nat)
    (size : entries.size = 1) (found : entries[0]? = some index) : entries = #[index] := by
  apply Array.ext
  · simpa using size
  · intro i hi hj
    have zero : i = 0 := by omega
    subst i
    obtain ⟨inside,equal⟩ := Array.getElem?_eq_some_iff.mp found
    exact equal

/-- The actual indexed objects and the required premise are retained. Neither
same names nor a producer-supplied Stage can replace these lookups. -/
theorem inspect_binding (artifact : Artifact) (index exponent provider remaining : Nat)
    (pending : Pending)
    (accepted : inspect artifact index exponent provider remaining = .ok pending) :
    artifact.proofs[index]? = some pending.root ∧
    pending.root.premises = #[pending.providerProofIndex] ∧
    artifact.proofs[pending.providerProofIndex]? = some pending.providerProof ∧
    implementationStage artifact pending.root.implementation = some pending.actual ∧
    meaningStage artifact pending.root.meaning = some pending.logical ∧
    shape artifact pending.root pending.providerProof pending.actual pending.logical = true ∧
    pending.visits ≤ remaining ∧ remaining ≤ 2000000 ∧
    ∃ receipt, Schema.check (.power exponent provider) (proposal pending.root pending.actual) = some receipt := by
  unfold inspect at accepted
  split at accepted
  next invalid => contradiction
  next bounded =>
    have limit : remaining ≤ 2000000 := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at bounded
      exact Nat.le_of_not_gt bounded.1.1
    cases hr : artifact.proofs[index]? with
    | none => simp only [hr] at accepted; contradiction
    | some root =>
      simp only [hr] at accepted
      split at accepted
      next invalid => contradiction
      next initial =>
        split at accepted
        next invalid => contradiction
        next arity =>
          have size : root.premises.size = 1 := by
            simp only [Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne,
              not_or] at arity
            exact Decidable.byContradiction arity.1
          cases hp : root.premises[0]? with
          | none => simp only [hp] at accepted; contradiction
          | some premiseIndex =>
            simp only [hp] at accepted
            split at accepted
            next cyclic => contradiction
            next separate =>
              cases he : artifact.proofs[premiseIndex]? with
              | none => simp only [he] at accepted; contradiction
              | some premise =>
                cases ha : implementationStage artifact root.implementation with
                | none => simp only [he,ha] at accepted; contradiction
                | some actual =>
                  cases hl : meaningStage artifact root.meaning with
                  | none => simp only [he,ha,hl] at accepted; contradiction
                  | some logical =>
                    simp only [he,ha,hl] at accepted
                    obtain ⟨charge,same,charged,valid,component⟩ :=
                      finish_binding artifact root premise premiseIndex actual logical exponent provider _ remaining pending accepted
                    subst pending
                    exact ⟨rfl,singleton_premise root.premises premiseIndex size hp,he,ha,hl,valid,charged,limit,component⟩


theorem shape_provider (artifact : Artifact) (root premise : Proof)
    (actual : ControlledPowers.Stage) (logical : LogicalStage)
    (accepted : shape artifact root premise actual logical = true) :
    premise.implementation = actual.targetDefinition ∧ premise.meaning = logical.provider ∧
    actual.count = logical.count ∧ actual.whenOne = logical.polarity := by
  have links : providerBinding premise actual logical = true := by
    have conditions := accepted
    simp only [shape, Bool.and_eq_true] at conditions
    exact conditions.1
  simp only [providerBinding, Bool.and_eq_true, beq_iff_eq] at links
  exact ⟨links.1.1.1,links.1.1.2,links.1.2,links.2⟩

theorem inspect_stage (artifact : Artifact) (index exponent provider remaining : Nat)
    (pending : Pending)
    (accepted : inspect artifact index exponent provider remaining = .ok pending) :
    ControlledPowers.checkSingle exponent provider pending.actual = true := by
  obtain ⟨_,_,_,_,_,_,_,_,receipt,component⟩ :=
    inspect_binding artifact index exponent provider remaining pending accepted
  obtain ⟨stage,projected,_,checked⟩ := Schema.check_power exponent provider _ receipt component
  change Schema.Witness.power pending.actual = Schema.Witness.power stage at projected
  rw [Schema.Witness.power.inj projected]
  exact checked

structure Inspection where
  typed : ContractTyping.Typed
  pending : Pending
  totalVisits : Nat
  deriving Repr

/-- Whole structural checking precedes local projection, using only its remaining
budget. The returned provider proof must still be semantically discharged. -/
def inspectEntry (artifact : Artifact) (order : Array Nat) (exponent provider : Nat) :
    Except Failure Inspection :=
  match ContractTyping.checkAll artifact order with
  | .error failure => .error failure
  | .ok typed =>
    match inspect artifact artifact.entry.proof exponent provider (2000000 - typed.totalVisits) with
    | .error kind => .error ⟨kind,some ⟨.proof,artifact.entry.proof⟩⟩
    | .ok pending =>
      if pending.root.implementation != artifact.entry.implementation then
        .error ⟨.contract,some ⟨.proof,artifact.entry.proof⟩⟩
      else if typed.totalVisits + pending.visits > 2000000 then
        .error ⟨.limit,some ⟨.proof,artifact.entry.proof⟩⟩
      else .ok ⟨typed,pending,typed.totalVisits + pending.visits⟩

theorem inspectEntry_binding (artifact : Artifact) (order : Array Nat) (exponent provider : Nat)
    (result : Inspection) (accepted : inspectEntry artifact order exponent provider = .ok result) :
    ContractTyping.checkAll artifact order = .ok result.typed ∧
    inspect artifact artifact.entry.proof exponent provider (2000000 - result.typed.totalVisits) = .ok result.pending ∧
    result.pending.root.implementation = artifact.entry.implementation ∧
    result.totalVisits = result.typed.totalVisits + result.pending.visits ∧ result.totalVisits ≤ 2000000 := by
  unfold inspectEntry at accepted
  cases ht : ContractTyping.checkAll artifact order with
  | error failure => simp [ht] at accepted
  | ok typed =>
    simp only [ht] at accepted
    cases hi : inspect artifact artifact.entry.proof exponent provider (2000000 - typed.totalVisits) with
    | error failure => simp [hi] at accepted
    | ok pending =>
      simp only [hi] at accepted
      split at accepted
      next wrong => contradiction
      next bound =>
        split at accepted
        next exceeded => contradiction
        next capacity =>
          cases Except.ok.inj accepted
          exact ⟨rfl,hi,by simpa using bound,rfl,Nat.le_of_not_gt capacity⟩

end QleisliKernel.Hierarchical.Power
