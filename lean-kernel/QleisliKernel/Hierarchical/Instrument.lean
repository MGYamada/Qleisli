import QleisliKernel.Hierarchical.Preparation
import QleisliKernel.Hierarchical.Readout
import QleisliKernel.Hierarchical.Root

/-! Composition of actual initialization, independently requested pure meaning
and readout, under one work budget. Finite implementation/meaning obligations
remain those of the exact same Root.Checked value; this is a pending result,
not an external schema receipt or source-preservation proof.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Hierarchical.Instrument
open Artifact

structure Request where
  preparation : Preparation.Request
  circuit : Root.Request
  readout : Readout.Request
  outputs : Side
  deriving Repr

structure Packet where
  preparation : Preparation.Packet
  artifact : Artifact
  order : Array Nat
  pairs : Array Root.Pair
  pairOrder : Array Nat
  readout : Readout.Packet
  deriving Repr

def boundary (request : Request) (packet : Packet) : Bool :=
  decide (request.circuit.kind = Kind.equation) &&
  decide (request.circuit.effect = Effect.unitary) &&
  decide (packet.preparation.outputs = request.circuit.interface.inputs) &&
  decide (request.readout.inputs = request.circuit.interface.outputs) &&
  decide (packet.readout.outputs = request.outputs)

def boundaryScan (request : Request) (packet : Packet) : Nat :=
  32 * (1 + sideScan packet.preparation.outputs +
    request.circuit.interface.scan + sideScan request.readout.inputs +
    sideScan packet.readout.outputs + sideScan request.outputs)

def boundaryCharge (request : Request) (packet : Packet) : Nat :=
  boundaryScan request packet + 16 * (1 + sideCharge packet.preparation.outputs +
    request.circuit.interface.charge + sideCharge request.readout.inputs +
    sideCharge packet.readout.outputs + sideCharge request.outputs)

def circuitWork (checked : Root.Checked) : Nat :=
  checked.artifact.state.visits + checked.binding.visits

structure Pending where
  circuit : Root.Checked
  preparation : Preparation.Checked
  readout : Readout.Checked
  visits : Nat
  deriving Repr

def assemble (request : Request) (packet : Packet) (circuit : Root.Checked) :
    Except Failure Pending :=
  let previous := circuitWork circuit
  if previous + boundaryScan request packet > 2000000 then .error ⟨.limit,none⟩ else
  let used := previous + boundaryCharge request packet
  if used > 2000000 then .error ⟨.limit,none⟩ else
  if !boundary request packet then .error ⟨.contract,none⟩ else
  match Preparation.check request.preparation packet.preparation (2000000-used) with
  | .error kind => .error ⟨kind,none⟩
  | .ok preparation =>
    match Readout.check request.readout packet.readout (2000000-used-preparation.visits) with
    | .error kind => .error ⟨kind,none⟩
    | .ok readout => .ok ⟨circuit,preparation,readout,used+preparation.visits+readout.visits⟩

/-- The pure graph is freshly checked against the independent request first.
No producer success flags or previously checked component values are inputs. -/
def checkAll (request : Request) (packet : Packet) : Except Failure Pending := do
  let circuit ← Root.checkAll packet.artifact packet.order request.circuit packet.pairs packet.pairOrder
  assemble request packet circuit

theorem assemble_conditions (request : Request) (packet : Packet)
    (circuit : Root.Checked) (pending : Pending)
    (accepted : assemble request packet circuit = .ok pending) :
    pending.circuit = circuit ∧ boundary request packet = true ∧
    let used := circuitWork circuit + boundaryCharge request packet
    used ≤ 2000000 ∧
    Preparation.check request.preparation packet.preparation (2000000-used) = .ok pending.preparation ∧
    Readout.check request.readout packet.readout (2000000-used-pending.preparation.visits) = .ok pending.readout ∧
    pending.visits = used+pending.preparation.visits+pending.readout.visits ∧ pending.visits ≤ 2000000 := by
  unfold assemble at accepted
  dsimp only at accepted
  split at accepted
  next exceeded => simp at accepted
  next scanned =>
    split at accepted
    next exceeded => simp at accepted
    next charged =>
      split at accepted
      next rejected => simp at accepted
      next linked =>
        cases hp : Preparation.check request.preparation packet.preparation
            (2000000-(circuitWork circuit+boundaryCharge request packet)) with
        | error error => simp [hp] at accepted
        | ok preparation =>
          simp only [hp] at accepted
          cases hr : Readout.check request.readout packet.readout
              (2000000-(circuitWork circuit+boundaryCharge request packet)-preparation.visits) with
          | error error => simp [hr] at accepted
          | ok readout =>
            have same : (⟨circuit,preparation,readout,
                circuitWork circuit+boundaryCharge request packet+preparation.visits+readout.visits⟩ : Pending) = pending := by
              simpa [hr] using accepted
            subst pending
            have initBound := (Preparation.check_conditions _ _ _ _ hp).1
            have readBound := (Readout.check_conditions _ _ _ _ hr).1
            exact ⟨rfl,by simpa using linked,by omega,hp,hr,rfl,by dsimp only; omega⟩

theorem checkAll_stages (request : Request) (packet : Packet) (pending : Pending)
    (accepted : checkAll request packet = .ok pending) :
    Root.checkAll packet.artifact packet.order request.circuit packet.pairs packet.pairOrder = .ok pending.circuit ∧
    assemble request packet pending.circuit = .ok pending := by
  unfold checkAll at accepted
  cases hc : Root.checkAll packet.artifact packet.order request.circuit packet.pairs packet.pairOrder with
  | error error => simp [hc,bind,Except.bind] at accepted
  | ok circuit =>
    have rest : assemble request packet circuit = .ok pending := by simpa [hc,bind,Except.bind] using accepted
    have same := (assemble_conditions request packet circuit pending rest).1
    subst circuit
    exact ⟨rfl,rest⟩

theorem checkAll_budget (request : Request) (packet : Packet) (pending : Pending)
    (accepted : checkAll request packet = .ok pending) : pending.visits ≤ 2000000 := by
  have stages := checkAll_stages request packet pending accepted
  exact (assemble_conditions request packet pending.circuit pending stages.2).2.2.2.2.2.2

theorem checkAll_boundary (request : Request) (packet : Packet) (pending : Pending)
    (accepted : checkAll request packet = .ok pending) :
    packet.preparation.outputs = request.circuit.interface.inputs ∧
    request.readout.inputs = request.circuit.interface.outputs ∧
    packet.readout.outputs = request.outputs := by
  have stages := checkAll_stages request packet pending accepted
  have linked := (assemble_conditions request packet pending.circuit pending stages.2).2.1
  simp only [boundary,Bool.and_eq_true,decide_eq_true_eq] at linked
  exact ⟨linked.1.1.2,linked.1.2,linked.2⟩

end QleisliKernel.Hierarchical.Instrument
