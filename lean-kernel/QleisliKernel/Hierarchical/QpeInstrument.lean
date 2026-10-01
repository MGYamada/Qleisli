import QleisliKernel.Hierarchical.QpeRoot
import QleisliKernel.Hierarchical.Preparation
import QleisliKernel.Hierarchical.Readout

/-! Fresh named-QPE boundary composition, retaining every finite obligation.
Complete target order, zero preparation, output reversal and classical outcome
order are checked explicitly. No external schema or semantic seal is enabled.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Hierarchical.QpeInstrument
open Artifact

structure Request where
  preparation : Preparation.Request
  circuit : QpeRoot.Request
  readout : Readout.Request
  outputs : Side
  deriving Repr

structure Packet where
  preparation : Preparation.Packet
  circuit : QpeRoot.Packet
  readout : Readout.Packet
  deriving Repr

/-- A missing coordinate is an error, never coordinate zero. -/
def position (axes : Array Nat) (axis : Nat) : Option Nat :=
  (List.range axes.size).find? (fun i => axes[i]? == some axis)

def routeAxes (outputAxes route selected : Array Nat) : Option (Array Nat) :=
  selected.mapM fun axis => do
    let index ← position outputAxes axis
    route[index]?

def coordinates (request : Request) : Bool :=
  let circuit := request.circuit.circuit
  let inputs := wires circuit.interface.inputs
  let outputs := wires circuit.interface.outputs
  (do
    let target ← circuit.target.mapM (fun i => inputs[i]?)
    let phase ← circuit.phase.mapM (fun i => inputs[i]?)
    let measured ← Readout.requestedAxes request.readout
    let phaseOrder ← routeAxes outputs circuit.route measured
    let targetOrder ← routeAxes outputs circuit.route (wires request.outputs)
    return target == wires request.preparation.inputs &&
      decide (phase.toList.Perm (wires ⟨request.preparation.fresh,#[]⟩).toList) &&
      phaseOrder == circuit.phase && targetOrder == circuit.target).getD false

def boundary (request : Request) (packet : Packet) : Bool :=
  let circuit := request.circuit.circuit
  packet.preparation.outputs == circuit.interface.inputs &&
    request.readout.inputs == circuit.interface.outputs && packet.readout.outputs == request.outputs &&
    request.preparation.fresh.size == circuit.phase.size && request.readout.owners.size == circuit.phase.size &&
    ContractTyping.onePort request.preparation.inputs #[.bits circuit.target.size] &&
    request.preparation.inputs.classical.isEmpty &&
    ContractTyping.onePort ⟨request.outputs.quantum,#[]⟩ #[.bits circuit.target.size] &&
    coordinates request

/-- Complete boundaries and bounded coordinate comparisons are charged before
any equality or coordinate projection. Component checks retain their own cost. -/
def charge (request : Request) (packet : Packet) : Nat :=
  64 + 32 * (1 + sideCharge request.preparation.inputs + sideCharge packet.preparation.outputs +
    request.circuit.circuit.interface.charge + sideCharge request.readout.inputs +
    sideCharge packet.readout.outputs + sideCharge request.outputs) +
    32 * (1+request.circuit.circuit.phase.size+request.circuit.circuit.target.size)^2

structure Pending where
  circuit : QpeRoot.Pending
  preparation : Preparation.Checked
  readout : Readout.Checked
  visits : Nat
  deriving Repr

def assemble (request : Request) (packet : Packet) (circuit : QpeRoot.Pending) : Except Failure Pending :=
  let used := circuit.visits + charge request packet
  if used > Limits.maxVisits then .error ⟨.limit,none⟩ else
  match Preparation.check request.preparation packet.preparation (Limits.maxVisits-used) with
  | .error e => .error ⟨e,none⟩
  | .ok preparation =>
    match Readout.check request.readout packet.readout (Limits.maxVisits-used-preparation.visits) with
    | .error e => .error ⟨e,none⟩
    | .ok readout =>
      if !boundary request packet then .error ⟨.contract,none⟩ else
      .ok ⟨circuit,preparation,readout,used+preparation.visits+readout.visits⟩

def checkAll (request : Request) (packet : Packet) : Except Failure Pending := do
  let circuit ← QpeRoot.checkAll request.circuit packet.circuit
  assemble request packet circuit

theorem assemble_conditions (request : Request) (packet : Packet) (circuit : QpeRoot.Pending)
    (pending : Pending) (accepted : assemble request packet circuit = .ok pending) :
    pending.circuit = circuit ∧
      Preparation.check request.preparation packet.preparation (2000000-circuit.visits-charge request packet) = .ok pending.preparation ∧
      Readout.check request.readout packet.readout
        (2000000-circuit.visits-charge request packet-pending.preparation.visits) = .ok pending.readout ∧
      boundary request packet = true ∧
      pending.visits = circuit.visits+charge request packet+pending.preparation.visits+pending.readout.visits ∧
      pending.visits ≤ 2000000 := by
  unfold assemble at accepted
  simp only [Limits.maxVisits] at accepted
  split at accepted
  next exceeded => contradiction
  next budget =>
    split at accepted
    next failed => contradiction
    next preparation checkedPreparation =>
      split at accepted
      next failed => contradiction
      next readout checkedReadout =>
        split at accepted
        next rejected => contradiction
        next valid =>
          cases Except.ok.inj accepted
          have pb := (Preparation.check_conditions _ _ _ _ checkedPreparation).1
          have rb := (Readout.check_conditions _ _ _ _ checkedReadout).1
          exact ⟨rfl,by simpa only [Nat.sub_sub] using checkedPreparation,
            by simpa only [Nat.sub_sub] using checkedReadout,by simpa using valid,rfl,by dsimp only; omega⟩

theorem checkAll_conditions (request : Request) (packet : Packet) (pending : Pending)
    (accepted : checkAll request packet = .ok pending) :
    QpeRoot.checkAll request.circuit packet.circuit = .ok pending.circuit ∧
      assemble request packet pending.circuit = .ok pending := by
  unfold checkAll at accepted
  cases hc : QpeRoot.checkAll request.circuit packet.circuit with
  | error failure => simp [hc,bind,Except.bind] at accepted
  | ok circuit =>
    have rest : assemble request packet circuit = .ok pending := by simpa [hc,bind,Except.bind] using accepted
    have same := (assemble_conditions request packet circuit pending rest).1
    subst circuit
    exact ⟨rfl,rest⟩

theorem checkAll_budget (request : Request) (packet : Packet) (pending : Pending)
    (accepted : checkAll request packet = .ok pending) : pending.visits ≤ 2000000 := by
  have stages := checkAll_conditions request packet pending accepted
  obtain ⟨_,_,_,_,_,budget⟩ := assemble_conditions request packet pending.circuit pending stages.2
  exact budget


theorem position_bound (axes : Array Nat) (axis index : Nat)
    (found : position axes axis = some index) :
    index < axes.size ∧ axes[index]? = some axis := by
  exact ⟨List.mem_range.mp (List.mem_of_find?_eq_some found),by simpa using List.find?_some found⟩

theorem coordinates_fields (request : Request) (accepted : coordinates request = true) :
    ∃ phase measured,
      request.circuit.circuit.target.mapM (fun i => (wires request.circuit.circuit.interface.inputs)[i]?) =
        some (wires request.preparation.inputs) ∧
      request.circuit.circuit.phase.mapM (fun i => (wires request.circuit.circuit.interface.inputs)[i]?) = some phase ∧
      phase.toList.Perm (wires ⟨request.preparation.fresh,#[]⟩).toList ∧
      Readout.requestedAxes request.readout = some measured ∧
      routeAxes (wires request.circuit.circuit.interface.outputs) request.circuit.circuit.route measured =
        some request.circuit.circuit.phase ∧
      routeAxes (wires request.circuit.circuit.interface.outputs) request.circuit.circuit.route (wires request.outputs) =
        some request.circuit.circuit.target := by
  unfold coordinates at accepted
  dsimp only at accepted
  simp only [bind,Option.bind] at accepted
  repeat (split at accepted <;> (try dsimp only at accepted) <;> (try contradiction))
  all_goals
    simp only [pure,Option.getD_some,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at accepted
    obtain ⟨⟨⟨target,phase⟩,phaseOrder⟩,targetOrder⟩ := accepted
    subst_vars
    exact ⟨_,_,by assumption,by assumption,phase,by assumption,by assumption,by assumption⟩

theorem boundary_fields (request : Request) (packet : Packet) (accepted : boundary request packet = true) :
    packet.preparation.outputs = request.circuit.circuit.interface.inputs ∧
      request.readout.inputs = request.circuit.circuit.interface.outputs ∧ packet.readout.outputs = request.outputs ∧
      request.preparation.fresh.size = request.circuit.circuit.phase.size ∧
      request.readout.owners.size = request.circuit.circuit.phase.size ∧
      ContractTyping.onePort request.preparation.inputs #[.bits request.circuit.circuit.target.size] = true ∧
      request.preparation.inputs.classical.isEmpty = true ∧
      ContractTyping.onePort ⟨request.outputs.quantum,#[]⟩ #[.bits request.circuit.circuit.target.size] = true ∧
      coordinates request = true := by
  simpa only [boundary,Bool.and_eq_true,beq_iff_eq,and_assoc] using accepted

private theorem list_mapM_at {A B : Type} (f : A → Option B) (xs : List A) (ys : List B)
    (computed : xs.mapM f = some ys) (i : Nat) (x : A) (found : xs[i]? = some x) :
    ∃ y, ys[i]? = some y ∧ f x = some y := by
  induction xs generalizing ys i with
  | nil => simp at found
  | cons head rest ih =>
    cases hh : f head with
    | none => simp [List.mapM_cons,hh] at computed
    | some value =>
      cases ht : rest.mapM f with
      | none => simp [List.mapM_cons,hh,ht] at computed
      | some values =>
        have same : ys = value::values := by simpa [List.mapM_cons,hh,ht] using computed.symm
        subst ys
        cases i with
        | zero =>
          have same : head = x := by simpa using found
          subst x
          exact ⟨value,rfl,hh⟩
        | succ i =>
          obtain ⟨y,selected,equation⟩ := ih values ht i (by simpa using found)
          exact ⟨y,by simpa using selected,equation⟩

theorem routeAxes_at (axes route selected result : Array Nat)
    (computed : routeAxes axes route selected = some result)
    (i axis : Nat) (found : selected[i]? = some axis) :
    ∃ coordinate index, result[i]? = some coordinate ∧
      position axes axis = some index ∧ route[index]? = some coordinate := by
  have mapped : selected.toList.mapM (fun axis => do
      let index ← position axes axis
      route[index]?) = some result.toList := by
    rw [← Array.toList_mapM]
    change Array.toList <$> routeAxes axes route selected = _
    rw [computed]
    rfl
  obtain ⟨coordinate,hc,step⟩ := list_mapM_at _ selected.toList result.toList mapped i axis (by simpa using found)
  cases hp : position axes axis with
  | none => simp [hp] at step
  | some index =>
    exact ⟨coordinate,index,by simpa using hc,rfl,by simpa [hp] using step⟩

end QleisliKernel.Hierarchical.QpeInstrument
