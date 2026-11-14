import QleisliKernel.Qirf.StructuralComputedUse
import QleisliKernel.Qirf.RuntimeComputedPredicate

/-! Ordered Raw boundary for a protected scope whose predicate is a circuit.
The packet carries its literal forward and inverse circuits. Scratch is a
private issued wire, and no free-standing release is available.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.StructuralComputedRaw
open QleisliKernel Finite Semantics.Finite SourceTypes SourceRuntimeContext
open RuntimePrimitiveSource (PortAt readPort)

structure Packet where
  input : Nat
  output : Nat
  scratch : Nat
  forward : List Step
  inverse : List Step
  uses : List Semantics.Raw.Use
  deriving BEq, DecidableEq, Repr

private def stepFields (step : Step) : Nat := step.controls.length + match step.action with
  | .hadamard _ => 1
  | .monomial axes perm phases => axes.length + perm.length + phases.length
  | .contract axes _ _ => axes.length + 2

private def useFields : Semantics.Raw.Use → Nat
  | .protectedGate .. => 1
  | .targetGate controls .. | .phase controls _ => controls.length + 1

def Packet.fields (packet : Packet) : Nat :=
  4 + (packet.forward.map (fun step => 1 + stepFields step)).sum +
    (packet.inverse.map (fun step => 1 + stepFields step)).sum +
    (packet.uses.map useFields).sum

structure Checked (packet : Packet) (state : Raw.State) where
  input : Semantics.Raw.Port
  taken : Raw.State
  takeRead : Raw.take state packet.input = .ok (input,taken)
  reserved : Raw.State
  reserveRead : Raw.reserve taken [packet.scratch] = .ok reserved
  after : Raw.State
  insertRead : Raw.insert reserved packet.output input.wires = .ok after
  inputValid : Raw.stateValid state = true
  outputValid : Raw.stateValid after = true
  clauses : List (List Control)
  forward : StructuralXor.Checked input.bits clauses packet.forward
  inverse : packet.inverse = packet.forward
  diagonalUses : Raw.usesValid 0 1 0 packet.uses = true

/-- Replay the existing Raw owner transition and check every original circuit
step as an exact phase-free XOR. No truth table, matrix or dependency is read. -/
def read (packet : Packet) (state : Raw.State) : WorkM (Checked packet state) := do
  exactWork (Exact.charge
    (32*(packet.fields+1)*(state.live.length+state.frame.length+state.seenTokens.length+state.seenWires.length+1)^2))
  if inputValid : Raw.stateValid state = true then
    let transition ← lift (Raw.structuralCompute state packet.input packet.output packet.scratch
      packet.forward packet.inverse packet.uses)
    let conditions := Raw.structuralComputeClauses_conditions transition.clausesRead
    let checked : StructuralXor.Checked transition.port.bits transition.clauses packet.forward :=
      ⟨conditions.2.2.1,conditions.2.2.2.1⟩
    if outputValid : Raw.stateValid transition.after = true then
      return ⟨transition.port,transition.taken,transition.takeRead,transition.reserved,
        transition.reserveRead,transition.after,transition.insertRead,inputValid,outputValid,
        transition.clauses,checked,conditions.1,conditions.2.1⟩
    else throw .request
  else throw .request

theorem Checked.returnedPort {packet state} (checked : Checked packet state) :
    ∃ port ∈ checked.after.live, port.token = packet.output ∧ port.wires = checked.input.wires :=
  (Raw.insert_fresh _ _ _ _ checked.insertRead).2.2

theorem Checked.sameFrame {packet state} (checked : Checked packet state) :
    checked.after.frame = state.frame := by
  have takeFrame : checked.taken.frame = state.frame := by
    have taken := checked.takeRead
    unfold Raw.take at taken
    obtain ⟨_,_,result⟩ := Finite.except_bind_success _ _ _ taken
    simp only [pure, Except.pure, Except.ok.injEq] at result
    rw [← (Prod.mk.inj result).2]
  have reservedFrame : checked.reserved.frame = checked.taken.frame := by
    have reserved := checked.reserveRead
    unfold Raw.reserve at reserved
    obtain ⟨_,_,result⟩ := Finite.except_bind_success _ _ _ reserved
    simp only [pure, Except.pure, Except.ok.injEq] at result
    rw [← result]
  have insertedFrame : checked.after.frame = checked.reserved.frame := by
    have inserted := checked.insertRead
    unfold Raw.insert at inserted
    obtain ⟨_,_,result⟩ := Finite.except_bind_success _ _ _ inserted
    simp only [pure, Except.pure, Except.ok.injEq] at result
    rw [← result]
  exact insertedFrame.trans (reservedFrame.trans takeFrame)

theorem Checked.scratchIssued {packet state} (checked : Checked packet state) :
    packet.scratch ∉ state.seenWires ∧ packet.scratch ∈ checked.after.seenWires := by
  have taken := checked.takeRead
  unfold Raw.take at taken
  obtain ⟨_,_,taken⟩ := Finite.except_bind_success _ _ _ taken
  simp only [pure, Except.pure, Except.ok.injEq] at taken
  have reserved := checked.reserveRead
  unfold Raw.reserve at reserved
  obtain ⟨_,req,reserved⟩ := Finite.except_bind_success _ _ _ reserved
  have valid := Raw.require_success _ req
  simp only [pure, Except.pure, Except.ok.injEq] at reserved
  have inserted := checked.insertRead
  unfold Raw.insert at inserted
  obtain ⟨_,_,inserted⟩ := Finite.except_bind_success _ _ _ inserted
  simp only [pure, Except.pure, Except.ok.injEq] at inserted
  have prior : checked.taken.seenWires = state.seenWires := by
    rw [← (Prod.mk.inj taken).2]
  constructor
  · simp only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true] at valid
    simpa [prior] using valid.2.2
  · rw [← inserted, ← reserved]
    simp

theorem Checked.scratchPrivate {packet state} (checked : Checked packet state) :
    packet.scratch ∉ checked.after.frame := by
  rw [checked.sameFrame]
  intro member
  have retained := checked.inputValid
  simp only [Raw.stateValid, Bool.and_eq_true] at retained
  have issued := List.all_eq_true.mp retained.1.1.2 packet.scratch member
  exact checked.scratchIssued.1 (List.contains_iff_mem.mp issued)

structure SourceChecked {sources caller} {event : ComputedEvent sources caller}
    (original : StructuralXorPredicate.Original event) (packet : Packet)
    (before : RuntimeStructuralAction.SourceState) (entry : RuntimeOwnerMap.State) where
  raw : Checked packet entry.quantum
  frame : RuntimeOwnerMap.Checked (before.bindings.map (·.owner)) entry
  sameFrame : frame.bindings = before.bindings
  owner : PortAt event.input before.bindings
  sameInput : owner.port = raw.input
  width : raw.input.bits = original.width
  auxiliaryFresh : event.initial.auxiliary ∉ before.issued
  sameOrdinal : event.nextOrdinal = before.nextOrdinal
  sameData : event.returned.data = event.input
  matched : StructuralComputedUse.Checked original packet.forward packet.inverse packet.uses
  output : Semantics.Raw.Port
  returned : PureInterval.ports {entry with quantum := raw.after} [packet.output] = some [output]
  spectators : PureInterval.spectators entry [raw.input.token] =
    PureInterval.spectators {entry with quantum := raw.after} [packet.output]
  continuation : RuntimeOwnerMap.Checked
    ((RuntimeComputedPredicate.continued event before output).bindings.map (·.owner))
    {entry with quantum := raw.after}
  sameContinuation : continuation.bindings = (RuntimeComputedPredicate.continued event before output).bindings

/-- Bind the exact original ordered role to the same physical port that the
Raw checker consumed. The enclosing body still supplies packet decoding and
the literal occurrence, including the fresh execution view comparison. -/
def readSource {sources caller} {event : ComputedEvent sources caller}
    (original : StructuralXorPredicate.Original event) (packet : Packet)
    (before : RuntimeStructuralAction.SourceState) (entry : RuntimeOwnerMap.State) :
    WorkM (SourceChecked original packet before entry) := do
  let raw ← read packet entry.quantum
  let frame ← RuntimeOwnerMap.checkBindings (before.bindings.map (·.owner)) entry before.bindings
  let owner ← readPort event.input before.bindings
  exactWork (Exact.charge (32*(Raw.OwnerFlow.fields (event.initial.auxiliary :: before.issued)+1)))
  if bound : owner.port = raw.input ∧ raw.input.bits = original.width ∧
      event.initial.auxiliary ∉ before.issued ∧ event.nextOrdinal = before.nextOrdinal ∧
      event.returned.data = event.input then
    let matched ← StructuralComputedUse.read original packet.forward packet.inverse packet.uses
    let exit := {entry with quantum := raw.after}
    match returned : PureInterval.ports exit [packet.output] with
    | some [output] =>
      if spectators : PureInterval.spectators entry [raw.input.token] =
          PureInterval.spectators exit [packet.output] then
        let next := RuntimeComputedPredicate.continued event before output
        let continuation ← RuntimeOwnerMap.checkBindings (next.bindings.map (·.owner)) exit next.bindings
        return ⟨raw,frame.val,frame.property,owner,bound.1,bound.2.1,bound.2.2.1,bound.2.2.2.1,
          bound.2.2.2.2,matched,output,returned,spectators,continuation.val,continuation.property⟩
      else throw .request
    | _ => throw .request
  else throw .request

/-- Select the verifier by the literal operation at this source occurrence.
The body loop cannot reinterpret a malformed structural operation as a table. -/
def isStructuralInterval {dependencies program block start count}
    (_interval : @RuntimeInterval.Checked dependencies program block start count) : Bool :=
  match (block.operations.drop start).take count with
  | [.pure (.structuralCompute ..)] => true
  | _ => false

def Packet.operation (packet : Packet) : Semantics.Raw.Op :=
  .structuralCompute packet.input packet.output packet.scratch packet.forward packet.inverse packet.uses

structure IntervalChecked {sources caller dependencies program block start count}
    (event : ComputedEvent sources caller)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before : RuntimeStructuralAction.SourceState) where
  original : StructuralXorPredicate.Original event
  packet : Packet
  literal : (block.operations.drop start).take count =
    [.pure packet.operation]
  checked : SourceChecked original packet before interval.before
  afterQuantum : checked.raw.after = interval.after.quantum

/-- The source predicate and scratch proof are tied to the exact operation in
the enclosing checker interval and its independently checked exit state. -/
def readInterval {sources caller dependencies program block start count}
    (event : ComputedEvent sources caller)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before : RuntimeStructuralAction.SourceState) : WorkM (IntervalChecked event interval before) := do
  exactWork (Exact.charge (8*(start+count+1)))
  match literal : (block.operations.drop start).take count with
  | [.pure (.structuralCompute input output scratch forward inverse uses)] =>
    let original ← StructuralXorPredicate.read event
    let packet : Packet := ⟨input,output,scratch,forward,inverse,uses⟩
    let checked ← readSource original packet before interval.before
    if same : checked.raw.after = interval.after.quantum then
      return ⟨original,packet,literal,checked,same⟩
    else throw .request
  | _ => throw .request

#print axioms readSource
#print axioms Checked.sameFrame
#print axioms Checked.scratchIssued

end QleisliKernel.Qirf.StructuralComputedRaw
