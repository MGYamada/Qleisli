import QleisliKernel.Hierarchical.NodeTyping
import QleisliKernel.Semantics.Preparation

/-! Actual initialization-node binding for the fresh-zero boundary.
This component does not validate a later unitary circuit or full instrument.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Hierarchical.Preparation
open Artifact

structure Request where
  inputs : Side
  fresh : Array QuantumPort
  deriving Repr

structure Packet where
  initializations : Array Definition
  outputs : Side
  deriving Repr

def output (request : Request) : Side :=
  ⟨request.inputs.quantum ++ request.fresh, request.inputs.classical⟩

def project (definition : Definition) : Option QuantumPort := do
  let .init0 owner := definition.body | none
  let port ← definition.interface.outputs.quantum.find? (fun p => p.owner == owner)
  if port.basis != #[Layout.TypeAtom.bit] || port.axes.size != 1 then none else some port

def step (before : Side) (definition : Definition) : Option Side := do
  let port ← project definition
  if definition.interface.inputs != before || !NodeTyping.conditions
      ⟨#[],#[],#[],#[],⟨0,0⟩⟩ definition then none else
    let after : Side := ⟨before.quantum.push port, before.classical⟩
    if definition.interface.outputs == after then some after else none

def valid (request : Request) (packet : Packet) : Bool :=
  request.fresh.size ≤ 16 && sideValid request.inputs && sideValid packet.outputs &&
  packet.initializations.size == request.fresh.size &&
  decide (packet.outputs = output request) &&
  decide (packet.initializations.mapM project = some request.fresh) &&
  decide (packet.initializations.toList.foldlM step request.inputs = some packet.outputs)

def scanCharge (request : Request) (packet : Packet) : Nat :=
  32 * (1 + request.fresh.size + packet.initializations.size +
    sideScan request.inputs + sideScan packet.outputs)

def headerCharge (request : Request) (packet : Packet) : Nat :=
  scanCharge request packet + 32 * packet.initializations.foldl
    (fun n definition => n + definition.interface.scan) 0

def workCharge (request : Request) (packet : Packet) : Nat :=
  let header := headerCharge request packet
  let requestCost := 1 + sideCharge request.inputs + sideCharge packet.outputs +
    request.fresh.foldl (fun n p => n + p.basis.size + p.axes.size) 0
  let steps := packet.initializations.foldl (fun n d => n + d.interface.charge) 0
  let original := header + 64 * (1 + request.fresh.size) * (requestCost + steps)
  -- Each project/step visits its own actual definition; `steps` already sums
  -- all complete input/output frames, including their uniqueness checks.
  -- Retain the old multiplier for request/fresh/output comparisons, and the
  -- conservative factor 64 for every actual frame. No validity check is reused
  -- or omitted. The cap keeps every previously accepted budget boundary.
  min original (header + 64 * ((1 + request.fresh.size) * requestCost + steps))

private theorem workCharge_le_original (request : Request) (packet : Packet) :
    workCharge request packet ≤ headerCharge request packet +
      64 * (1 + request.fresh.size) *
        (1 + sideCharge request.inputs + sideCharge packet.outputs +
          request.fresh.foldl (fun n p => n + p.basis.size + p.axes.size) 0 +
          packet.initializations.foldl (fun n d => n + d.interface.charge) 0) :=
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

theorem check_binding (request : Request) (packet : Packet) (remaining : Nat)
    (checked : Checked) (accepted : check request packet remaining = .ok checked) :
    packet.outputs = output request ∧
    packet.initializations.mapM project = some request.fresh ∧
    packet.initializations.toList.foldlM step request.inputs = some packet.outputs := by
  have h := (check_conditions request packet remaining checked accepted).2.2
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.2, h.1.2, h.2⟩

/-- Exact complete frame: all old ports (including empty owners and classical
values) survive, and precisely the independently requested fresh ports appear. -/
theorem check_boundary (request : Request) (packet : Packet) (remaining : Nat)
    (checked : Checked) (accepted : check request packet remaining = .ok checked) :
    packet.outputs.quantum = request.inputs.quantum ++ request.fresh ∧
    packet.outputs.classical = request.inputs.classical := by
  rw [(check_binding request packet remaining checked accepted).1]
  exact ⟨rfl, rfl⟩

/-- Actual initialization nodes produce exactly the requested zero factors,
including all residual and reference coefficients. No numerical tolerance or
caller-supplied zero-state flag is an acceptance premise. -/
theorem check_reference {Scalar Reference : Type} [OfNat Scalar 0]
    (request : Request) (packet : Packet) (remaining : Nat) (checked : Checked)
    (accepted : check request packet remaining = .ok checked)
    (input : (Nat → Bool) → Reference → Scalar) (state : Nat → Bool) (reference : Reference) :
    ∃ actual, packet.initializations.mapM project = some actual ∧
      Semantics.Preparation.sequential (wires ⟨actual,#[]⟩).toList input state reference =
        Semantics.Preparation.zero (wires ⟨request.fresh,#[]⟩).toList input state reference := by
  exact ⟨request.fresh, (check_binding request packet remaining checked accepted).2.1,
    Semantics.Preparation.sequential_zero _ input state reference⟩

end QleisliKernel.Hierarchical.Preparation
