import QleisliKernel.Hierarchical.QpeSchedule
import QleisliKernel.Hierarchical.Root

/-! One fresh check of a coherent QPE circuit and its independent provider.
Finite reconstruction, preparation and readout remain separate obligations.
All passes share the unchanged structural work allowance.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Hierarchical.QpeRoot
open Artifact

structure Request where
  circuit : QpeSchedule.Request
  provider : Root.Request
  deriving Repr

structure Packet where
  artifact : Artifact
  order : Array Nat
  providerProof : Nat
  pairs : Array Root.Pair
  pairOrder : Array Nat
  candidate : QpeSchedule.Candidate
  deriving Repr

def providerArtifact (request : Request) (packet : Packet) : Artifact :=
  {packet.artifact with entry := ⟨request.circuit.provider,packet.providerProof⟩}

def boundary (request : Request) : Bool :=
  decide (request.provider.kind = Kind.equation) &&
    decide (request.provider.effect = Effect.unitary) &&
    request.provider.interface.inputs == request.provider.interface.outputs &&
    ContractTyping.onePort request.provider.interface.inputs #[.bits request.circuit.target.size] &&
    NodeTyping.quantumOnly request.provider.interface

def charge (request : Request) : Nat := 64 + 16 * request.provider.interface.charge

structure Pending where
  artifact : Conditional.Pending
  provider : Root.Pending
  schedule : QpeSchedule.Pending
  visits : Nat
  deriving Repr

/-- The fresh proof cache supplies the provider proof. It cannot be a submitted
success bit. Root pairing then binds that exact provider to its independent
meaning before the actual QPE schedule is inspected. -/
def assemble (request : Request) (packet : Packet) (checked : Conditional.Pending) : Except Failure Pending :=
  let previous := checked.state.visits + charge request
  if previous > 2000000 then .error ⟨.limit,none⟩ else
  if !boundary request || checked.state.cache[packet.providerProof]? != some true then .error ⟨.contract,none⟩ else
  match Root.inspect (providerArtifact request packet) request.provider packet.pairs packet.pairOrder
    (2000000-previous) with
  | .error e => .error ⟨e,none⟩
  | .ok provider =>
    match QpeSchedule.inspect packet.artifact request.circuit packet.candidate
      (2000000-previous-provider.visits) with
    | .error e => .error ⟨e,none⟩
    | .ok schedule => .ok ⟨checked,provider,schedule,previous+provider.visits+schedule.visits⟩

def checkAll (request : Request) (packet : Packet) : Except Failure Pending := do
  let checked ← Conditional.checkAll packet.artifact packet.order
  assemble request packet checked

theorem assemble_conditions (request : Request) (packet : Packet) (checked : Conditional.Pending)
    (pending : Pending) (accepted : assemble request packet checked = .ok pending) :
    pending.artifact = checked ∧ boundary request = true ∧
      checked.state.cache[packet.providerProof]? = some true ∧
      Root.inspect (providerArtifact request packet) request.provider packet.pairs packet.pairOrder
        (2000000-checked.state.visits-charge request) = .ok pending.provider ∧
      QpeSchedule.inspect packet.artifact request.circuit packet.candidate
        (2000000-checked.state.visits-charge request-pending.provider.visits) = .ok pending.schedule ∧
      pending.visits = checked.state.visits+charge request+pending.provider.visits+pending.schedule.visits ∧
      pending.visits ≤ 2000000 := by
  unfold assemble at accepted
  dsimp only at accepted
  split at accepted
  next exceeded => contradiction
  next budget =>
    split at accepted
    next invalid => contradiction
    next ready =>
      split at accepted
      next failed => contradiction
      next provider checkedProvider =>
        split at accepted
        next failed => contradiction
        next schedule checkedSchedule =>
          cases Except.ok.inj accepted
          have pb := (Root.inspect_conditions _ _ _ _ _ _ checkedProvider).1
          have sb := (QpeSchedule.inspect_conditions _ _ _ _ _ checkedSchedule).2.2.2.2.2.2.2.2.2.2.1
          simp only [Bool.or_eq_true,Bool.not_eq_true',bne_iff_ne,not_or,Classical.not_not] at ready
          exact ⟨rfl,by simpa using ready.1,ready.2,by simpa only [Nat.sub_sub] using checkedProvider,
            by simpa only [Nat.sub_sub] using checkedSchedule,rfl,by dsimp only; omega⟩

theorem checkAll_conditions (request : Request) (packet : Packet) (pending : Pending)
    (accepted : checkAll request packet = .ok pending) :
    Conditional.checkAll packet.artifact packet.order = .ok pending.artifact ∧
      assemble request packet pending.artifact = .ok pending := by
  unfold checkAll at accepted
  cases hc : Conditional.checkAll packet.artifact packet.order with
  | error failure => simp [hc,bind,Except.bind] at accepted
  | ok checked =>
    have rest : assemble request packet checked = .ok pending := by simpa [hc,bind,Except.bind] using accepted
    have same := (assemble_conditions request packet checked pending rest).1
    subst checked
    exact ⟨rfl,rest⟩

theorem checkAll_budget (request : Request) (packet : Packet) (pending : Pending)
    (accepted : checkAll request packet = .ok pending) : pending.visits ≤ 2000000 :=
  (assemble_conditions request packet pending.artifact pending
    (checkAll_conditions request packet pending accepted).2).2.2.2.2.2.2

end QleisliKernel.Hierarchical.QpeRoot
