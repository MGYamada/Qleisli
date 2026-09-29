import QleisliKernel.Qpe

/-! Closed component-schema dispatch with independently supplied requests.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
This validates internal witnesses, not external IR projection or finite-provider
evidence. No production wire profile is enabled by this module alone. -/

namespace QleisliKernel.Schema

inductive Request where
  | qft (width : Nat)
  | power (exponent provider : Nat)
  | qpe (targetWidth precision provider : Nat)
  deriving BEq, DecidableEq, Repr

def Request.rule : Request → String
  | .qft _ => "qft-dyadic8/1"
  | .power _ _ => "controlled-power/1"
  | .qpe _ _ _ => "qpe-instrument/1"

def Request.parameters : Request → List Nat
  | .qft width => [width]
  | .power exponent provider => [exponent, provider]
  | .qpe targetWidth precision provider => [targetWidth, precision, provider]

inductive Witness where
  | qft (definitions : List QftGraph.Definition) (entry : Nat)
  | power (stage : ControlledPowers.Stage)
  | qpe (plan : Qpe.Plan)
  deriving Repr

structure Proposal where
  rule : String
  templateVersion : Nat
  parameters : List Nat
  witness : Witness
  deriving Repr

inductive Receipt where
  | qft (circuit : QftGraph.Receipt)
  | power
  | qpe (circuit : QftGraph.Receipt)
  deriving Repr

/-- All witness integers are ordinary data. IDs resolve only to the fixed
branches below; artifacts cannot name Lean declarations or load proof code. -/
def metadata (request : Request) (proposal : Proposal) : Bool :=
  proposal.rule == request.rule && proposal.templateVersion == 1 &&
  proposal.parameters == request.parameters

/-- Provider references use the external profile's u32 domain. The enclosing
IR verifier must additionally check the referenced provider and its evidence. -/
def referenceBound : Request → Bool
  | .qft _ => true
  | .power _ provider | .qpe _ _ provider => provider ≤ 4294967295

def check (request : Request) (proposal : Proposal) : Option Receipt :=
  if !referenceBound request || !metadata request proposal then none
  else match request, proposal.witness with
    | .qft width, .qft definitions entry =>
      (QftGraph.check definitions entry width).map Receipt.qft
    | .power exponent provider, .power stage =>
      if ControlledPowers.checkSingle exponent provider stage then some .power else none
    | .qpe targetWidth precision provider, .qpe plan =>
      (Qpe.check targetWidth precision provider plan).map Receipt.qpe
    | _, _ => none

theorem check_metadata (request : Request) (proposal : Proposal) (receipt : Receipt)
    (accepted : check request proposal = some receipt) :
    proposal.rule = request.rule ∧ proposal.templateVersion = 1 ∧
      proposal.parameters = request.parameters ∧ referenceBound request = true := by
  unfold check at accepted
  split at accepted
  next invalid => contradiction
  next valid =>
    have guard : referenceBound request = true ∧ metadata request proposal = true := by
      simpa using valid
    have fields := guard.2
    simp [metadata] at fields
    exact ⟨fields.1.1, fields.1.2, fields.2, guard.1⟩

theorem check_qft (width : Nat) (proposal : Proposal) (receipt : Receipt)
    (accepted : check (.qft width) proposal = some receipt) :
    ∃ definitions entry circuit,
      proposal.witness = .qft definitions entry ∧ receipt = .qft circuit ∧
      QftGraph.check definitions entry width = some circuit := by
  unfold check at accepted
  split at accepted
  next invalid => contradiction
  next valid =>
    cases h : proposal.witness with
    | qft definitions entry =>
      cases hc : QftGraph.check definitions entry width with
      | none => simp [h, hc] at accepted
      | some circuit =>
        exact ⟨definitions, entry, circuit, rfl, by simpa [h, hc] using accepted.symm, hc⟩
    | power stage => simp [h] at accepted
    | qpe plan => simp [h] at accepted

theorem check_power (exponent provider : Nat) (proposal : Proposal) (receipt : Receipt)
    (accepted : check (.power exponent provider) proposal = some receipt) :
    ∃ stage, proposal.witness = .power stage ∧ receipt = .power ∧
      ControlledPowers.checkSingle exponent provider stage = true := by
  unfold check at accepted
  split at accepted
  next invalid => contradiction
  next valid =>
    cases h : proposal.witness with
    | qft definitions entry => simp [h] at accepted
    | power stage =>
      by_cases hc : ControlledPowers.checkSingle exponent provider stage = true
      · exact ⟨stage, rfl, by simpa [h, hc] using accepted.symm, hc⟩
      · simp [h, hc] at accepted
    | qpe plan => simp [h] at accepted

theorem check_qpe (targetWidth precision provider : Nat) (proposal : Proposal) (receipt : Receipt)
    (accepted : check (.qpe targetWidth precision provider) proposal = some receipt) :
    ∃ plan circuit, proposal.witness = .qpe plan ∧ receipt = .qpe circuit ∧
      Qpe.check targetWidth precision provider plan = some circuit := by
  unfold check at accepted
  split at accepted
  next invalid => contradiction
  next valid =>
    cases h : proposal.witness with
    | qft definitions entry => simp [h] at accepted
    | power stage => simp [h] at accepted
    | qpe plan =>
      cases hc : Qpe.check targetWidth precision provider plan with
      | none => simp [h, hc] at accepted
      | some circuit =>
        exact ⟨plan, circuit, rfl, by simpa [h, hc] using accepted.symm, hc⟩

end QleisliKernel.Schema
