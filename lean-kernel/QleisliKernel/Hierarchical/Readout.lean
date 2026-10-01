import QleisliKernel.Hierarchical.NodeTyping
import QleisliKernel.Semantics.Readout

/-! Binding actual measurement nodes and classical result assembly.
This additive component checks readout only; it cannot issue a QPE receipt or
justify the preceding initialization, unitary circuit or source translation.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Hierarchical.Readout
open Artifact

structure Request where
  inputs : Side
  owners : Array Nat
  result : Nat
  deriving Repr

structure Packet where
  measurements : Array Definition
  /-- Actual intermediate CBit names, in low-bit-first result order. -/
  pack : Array Nat
  outputs : Side
  deriving Repr

/-- Project the actual body and exact one-bit operand; no names have implicit
meaning and no submitted axis claim is used. -/
def project (definition : Definition) : Option (Nat × Nat × Nat) := do
  let .observeZ owner value := definition.body | none
  let port ← definition.interface.inputs.quantum.find? (fun p => p.owner == owner)
  if port.basis != #[Layout.TypeAtom.bit] || port.axes.size != 1 then none else
    return (owner, value, ← port.axes[0]?)

def requestedAxes (request : Request) : Option (Array Nat) :=
  request.owners.mapM fun owner => do
    let port ← request.inputs.quantum.find? (fun p => p.owner == owner)
    if port.basis != #[Layout.TypeAtom.bit] || port.axes.size != 1 then none else
      port.axes[0]?

def output (request : Request) : Side :=
  ⟨request.inputs.quantum.filter (fun port => !request.owners.contains port.owner),
    request.inputs.classical.push ⟨request.result, #[.bits request.owners.size]⟩⟩

/-- Every intermediate observation is typed and has the exact current frame.
Only the generated local CBit is added, at the end of the classical frame. -/
def step (before : Side) (definition : Definition) : Option Side := do
  let .observeZ owner value := definition.body | none
  if definition.interface.inputs != before || !NodeTyping.conditions
      ⟨#[],#[],#[],#[],⟨0,0⟩⟩ definition then none else
    let after : Side :=
      ⟨before.quantum.filter (fun port => port.owner != owner),
        before.classical.push ⟨value, #[.bit]⟩⟩
    if definition.interface.outputs == after then some after else none

def projected (packet : Packet) : Option (Array (Nat × Nat × Nat)) :=
  packet.measurements.mapM project

/-- Execute the explicit classical pack using actual intermediate value names. -/
def assemble (packet : Packet) (values : Nat → Bool) : Nat :=
  Semantics.Readout.encode (packet.pack.toList.map values)

def valid (request : Request) (packet : Packet) : Bool :=
  request.owners.size ≤ 8 && sideValid request.inputs &&
  decide request.owners.toList.Nodup &&
  !(NodeTyping.valueNames request.inputs).contains request.result &&
  packet.measurements.size == request.owners.size &&
  packet.pack.size == request.owners.size && decide (packet.outputs = output request) &&
  sideValid packet.outputs && (do
    let axes ← requestedAxes request
    let actual ← projected packet
    let _ ← packet.measurements.toList.foldlM step request.inputs
    return actual.map Prod.fst == request.owners &&
      actual.map (fun (p : Nat × Nat × Nat) => p.2.1) == packet.pack &&
      actual.map (fun (p : Nat × Nat × Nat) => p.2.2) == axes).getD false

/-- Charge array headers before inspecting nested content, then all scans and
quadratic uniqueness checks. The selected profile keeps its existing budget. -/
def scanCharge (request : Request) (packet : Packet) : Nat :=
  32 * (1 + request.owners.size + packet.measurements.size + packet.pack.size +
    request.inputs.quantum.size + request.inputs.classical.size +
    packet.outputs.quantum.size + packet.outputs.classical.size)

def headerCharge (request : Request) (packet : Packet) : Nat :=
  scanCharge request packet + 32 * packet.measurements.foldl
    (fun n definition => n + definition.interface.scan) 0

def workCharge (request : Request) (packet : Packet) : Nat :=
  let header := headerCharge request packet
  let requestCost := 1 + sideCharge request.inputs + sideCharge packet.outputs
  let steps := packet.measurements.foldl (fun n definition => n + definition.interface.charge) 0
  let count := 1 + request.owners.size + packet.pack.size
  let original := header + 64 * count * (requestCost + steps)
  -- Keep request-owner lookup, output filtering, owner uniqueness and ordered
  -- pack comparisons under the original count multiplier. Projection and
  -- step checking each scan one actual definition; their complete frame costs
  -- are already summed in `steps`. Keep factor 64 and every original validity
  -- predicate, while avoiding charging every frame once per unrelated step.
  min original (header + 64 * (count * requestCost + steps))

private theorem workCharge_le_original (request : Request) (packet : Packet) :
    workCharge request packet ≤ headerCharge request packet +
      64 * (1 + request.owners.size + packet.pack.size) *
        (1 + sideCharge request.inputs + sideCharge packet.outputs +
          packet.measurements.foldl (fun n definition => n + definition.interface.charge) 0) :=
  Nat.min_le_left _ _

structure Checked where
  visits : Nat
  deriving Repr

def check (request : Request) (packet : Packet) (remaining : Nat) : Except Error Checked :=
  if remaining > Limits.maxVisits || scanCharge request packet > remaining then .error .limit
  else if headerCharge request packet > remaining then .error .limit
  else if workCharge request packet > remaining then .error .limit
  else if valid request packet then .ok ⟨workCharge request packet⟩ else .error .contract

theorem check_conditions (request : Request) (packet : Packet) (remaining : Nat)
    (checked : Checked) (accepted : check request packet remaining = .ok checked) :
    checked.visits ≤ remaining ∧ remaining ≤ 2000000 ∧ valid request packet = true := by
  unfold check at accepted
  split at accepted
  next invalid => contradiction
  next capacity =>
    split at accepted
    next exceeded => contradiction
    next scanned =>
      split at accepted
      next exceeded => contradiction
      next bounded =>
        split at accepted
        next correct =>
          cases Except.ok.inj accepted
          have h : remaining ≤ 2000000 ∧ scanCharge request packet ≤ remaining := by
            simpa only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] using capacity
          exact ⟨Nat.le_of_not_gt bounded, h.1, correct⟩
        next invalid => contradiction

theorem valid_binding (request : Request) (packet : Packet)
    (accepted : valid request packet = true) :
    packet.outputs = output request ∧
    ∃ axes actual, requestedAxes request = some axes ∧ projected packet = some actual ∧
      actual.map Prod.fst = request.owners ∧
      actual.map (fun (p : Nat × Nat × Nat) => p.2.1) = packet.pack ∧
      actual.map (fun (p : Nat × Nat × Nat) => p.2.2) = axes := by
  simp only [valid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at accepted
  refine ⟨accepted.1.1.2, ?_⟩
  obtain ⟨front, success⟩ := accepted
  cases ha : requestedAxes request with
  | none => simp [ha] at success
  | some axes =>
    cases hp : projected packet with
    | none => simp [ha, hp] at success
    | some actual =>
      cases hs : packet.measurements.toList.foldlM step request.inputs with
      | none => simp [ha, hp, hs] at success
      | some after =>
        simp [ha, hp, hs] at success
        exact ⟨axes, actual, rfl, rfl, success.1.1, success.1.2, success.2⟩

theorem check_assembly (request : Request) (packet : Packet) (remaining : Nat)
    (checked : Checked) (accepted : check request packet remaining = .ok checked)
    (values : Nat → Bool) :
    ∃ actual, projected packet = some actual ∧
      assemble packet values = Semantics.Readout.encode
        ((actual.map (fun (p : Nat × Nat × Nat) => p.2.1)).toList.map values) := by
  obtain ⟨_, _, actual, _, hp, _, pack, _⟩ :=
    valid_binding request packet (check_conditions request packet remaining checked accepted).2.2
  exact ⟨actual, hp, by rw [pack]; rfl⟩

/-- Only the requested logical owners are consumed. Every other quantum port,
including its exact type and axes and any zero-width owner, survives unchanged.
The public classical frame adds exactly one correctly sized result. -/
theorem check_boundary (request : Request) (packet : Packet) (remaining : Nat)
    (checked : Checked) (accepted : check request packet remaining = .ok checked) :
    packet.outputs.quantum = request.inputs.quantum.filter
      (fun port => !request.owners.contains port.owner) ∧
    packet.outputs.classical = request.inputs.classical.push
      ⟨request.result, #[.bits request.owners.size]⟩ := by
  have bound := (valid_binding request packet
    (check_conditions request packet remaining checked accepted).2.2).1
  rw [bound]
  exact ⟨rfl, rfl⟩

/-- The actual measured axes give precisely the requested unnormalized
instrument branch, for all residual and reference coordinates and coefficients.
Packing binds the position of each outcome to that same actual measurement. -/
theorem check_reference {Scalar Reference : Type} (request : Request) (packet : Packet)
    (remaining : Nat) (checked : Checked)
    (accepted : check request packet remaining = .ok checked)
    (outcome : Nat → Bool) (input : (Nat → Bool) → Reference → Scalar)
    (residual : Nat → Bool) (reference : Reference) :
    ∃ axes actual, requestedAxes request = some axes ∧ projected packet = some actual ∧
      actual.map (fun (p : Nat × Nat × Nat) => p.2.1) = packet.pack ∧
      Semantics.Readout.sequential (actual.map (fun (p : Nat × Nat × Nat) => p.2.2)).toList outcome input residual reference =
        Semantics.Readout.branch axes.toList outcome input residual reference := by
  obtain ⟨_, axes, actual, ha, hp, _, pack, binding⟩ :=
    valid_binding request packet (check_conditions request packet remaining checked accepted).2.2
  exact ⟨axes, actual, ha, hp, pack, by rw [Semantics.Readout.sequential_branch, binding]⟩

end QleisliKernel.Hierarchical.Readout
