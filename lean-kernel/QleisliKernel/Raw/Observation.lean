import QleisliKernel.Semantics.Observation
import QleisliKernel.Raw.Pure

/-! VM-26 ownership, effects, global SSA freshness, lexical branches and phis.
All nineteen original raw constructors are checked from original operations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.Observation
open Semantics.Raw Semantics.Observation Semantics.Finite Finite

structure State where
  quantum : Raw.State := {}
  classical : List (Nat × Nat) := []
  active : List Nat := [0]
  scope : Nat := 0
  nextScope : Nat := 1
  observe : Bool := false
  deriving Repr

def visible (state : State) (id : Nat) : Bool :=
  state.classical.any fun (value,scope) => value == id && state.active.contains scope

def visibleArm (state : State) (arm id : Nat) : Bool :=
  state.classical.any fun (value,scope) => value == id && (scope == arm || state.active.contains scope)

def insertClassical (state : State) (id : Nat) : Raw.Check State := do
  Raw.require (id ≤ 4294967295 && !(state.classical.map (·.1)).contains id)
  return {state with classical := state.classical ++ [(id,state.scope)]}

def enter (state : State) : State :=
  {state with scope := state.nextScope,active := state.active ++ [state.nextScope],nextScope := state.nextScope+1}

def leave (parent arm : Nat) (state : State) : State :=
  {state with scope := parent,active := state.active.filter (· != arm)}

def consume (state : State) (token : Nat) : Raw.Check (Port × State) := do
  let (port,next) ← Raw.take state.quantum token
  return (port,{state with quantum := {next with
    frame := next.frame.filter (fun wire => !port.wires.contains wire)}})

def phiValid (left right : Raw.State) (phis : List QuantumPhi) : Bool :=
  Raw.unique (phis.map (·.thenToken)) && Raw.unique (phis.map (·.elseToken)) &&
  phis.length == left.live.length && phis.length == right.live.length &&
  left.live.all (fun port => (phis.map (·.thenToken)).contains port.token) &&
  right.live.all (fun port => (phis.map (·.elseToken)).contains port.token) &&
  phis.all (fun phi => match left.live.find? (fun port => port.token == phi.thenToken),
      right.live.find? (fun port => port.token == phi.elseToken) with
    | some a,some b => a.bits == b.bits && phi.wires.length == a.bits
    | _,_ => false)

/-- Both complete live interfaces, including caller frames and Unit owners,
are required. No arm-local quantum result may be silently dropped. -/
theorem phi_coverage (left right : Raw.State) (phis : List QuantumPhi)
    (ok : phiValid left right phis = true) :
    (∀ port ∈ left.live, port.token ∈ phis.map (·.thenToken)) ∧
    (∀ port ∈ right.live, port.token ∈ phis.map (·.elseToken)) := by
  simp only [phiValid,Bool.and_eq_true,List.all_eq_true,List.contains_iff_mem] at ok
  exact ⟨ok.1.1.2,ok.1.2⟩

/-- Issued identities normally grow by appending. Check that common case in
linear time, retaining the membership check for arbitrary public states. -/
def historySubset {α : Type} [BEq α] (before after : List α) : Bool :=
  if before.isPrefixOf after then true else before.all after.contains

/-- The fast path changes neither acceptance nor the shared work counter. -/
theorem historySubset_eq {α : Type} [BEq α] [LawfulBEq α] (before after : List α) :
    historySubset before after = before.all after.contains := by
  by_cases hprefix : before.isPrefixOf after = true
  · simp only [historySubset,hprefix,↓reduceIte]
    symm
    simp only [List.all_eq_true,List.contains_iff_mem]
    exact (List.isPrefixOf_iff_prefix.mp hprefix).subset
  · simp [historySubset,hprefix]

def history (before after : State) : Bool :=
  historySubset before.quantum.seenTokens after.quantum.seenTokens &&
  historySubset before.quantum.seenWires after.quantum.seenWires &&
  historySubset before.classical after.classical

theorem history_eq (before after : State) : history before after =
    (before.quantum.seenTokens.all after.quantum.seenTokens.contains &&
    before.quantum.seenWires.all after.quantum.seenWires.contains &&
    before.classical.all after.classical.contains) := by
  simp only [history,historySubset_eq]

/-- Arm states share the monotonically growing global identity store. Only
their live quantum frame/effect is restored to the common branch entry. -/
def restore (entry checked : State) : State :=
  let quantum := {entry.quantum with
    seenTokens := checked.quantum.seenTokens
    seenWires := checked.quantum.seenWires}
  {checked with quantum,observe := entry.observe}

/-- Original instruction body, parameterized by checking for nested arms.
Boundary invariants and work charging remain in checkStep. -/
def checkAction (dependencies : List Dependency)
    (recurse : State → List Semantics.Observation.Op → WorkM State)
    (state : State) (op : Semantics.Observation.Op) : WorkM State := do
  match op with
  | .pure operation => do
    exactWork (Exact.charge (Raw.rawFields ⟨[],[operation],[],.unitary⟩))
    let next ← lift (Raw.step (dependencies.map (·.signature)) state.quantum operation)
    let _ ← next.events.foldlM (fun _ event => Raw.Pure.eventCheck dependencies event) ()
    pure {state with quantum := next.state}
  | .measure input output => do
    let (port,next) ← lift (consume state input)
    guard (port.bits == 1)
    let next ← lift (insertClassical next output)
    pure {next with observe := true}
  | .reset input output wire => do
    let (port,next) ← lift (consume state input)
    guard (port.bits == 1)
    let quantum ← lift (Raw.input next.quantum ⟨output,[wire],1⟩)
    pure {next with quantum,observe := true}
  | .discard input => do
    let (_,next) ← lift (consume state input)
    pure {next with observe := true}
  | .constant _ output => lift (insertClassical state output)
  | .not input output => do
    guard (visible state input)
    lift (insertClassical state output)
  | .xor left right output | .and left right output => do
    guard (visible state left && visible state right)
    lift (insertClassical state output)
  | .branch condition thenOps elseOps quantum classical => do
    exactWork (Exact.charge (4*quantum.length + (quantum.map (fun phi => phi.wires.length)).sum + 3*classical.length))
    guard (visible state condition)
    let leftEntry := enter state
    let left ← recurse leftEntry thenOps
    let left := leave state.scope leftEntry.scope left
    let rightEntry := enter (restore state left)
    let right ← recurse rightEntry elseOps
    let right := leave state.scope rightEntry.scope right
    guard (phiValid left.quantum right.quantum quantum)
    -- All phi operands are resolved before ANY phi output is inserted.
    guard (classical.all fun phi => visibleArm right leftEntry.scope phi.thenId &&
      visibleArm right rightEntry.scope phi.elseId)
    let base : Raw.State := {right.quantum with
      live := [],frame := [],iso := left.quantum.iso || right.quantum.iso}
    let merged ← lift (quantum.foldlM (fun q phi => Raw.input q ⟨phi.output,phi.wires,phi.wires.length⟩) base)
    let next := {right with quantum := merged,observe := left.observe || right.observe}
    lift (classical.foldlM (fun next phi => insertClassical next phi.output) next)

/-- One original instruction with its shared work and boundary checks. -/
def checkStep (dependencies : List Dependency)
    (recurse : State → List Semantics.Observation.Op → WorkM State)
    (state : State) (op : Semantics.Observation.Op) : WorkM State := do
  exactWork (Exact.charge 1)
  guard (Raw.stateValid state.quantum)
  let next ← checkAction dependencies recurse state op
  guard (Raw.stateValid next.quantum && history state next)
  pure next

def checkOps (dependencies : List Dependency) (fuel : Nat) : State → List Semantics.Observation.Op → WorkM State :=
  Nat.rec (fun _ _ => throw .limit) (fun _ recurse initial operations => do
    let result ← operations.foldlM (checkStep dependencies recurse) initial
    guard (Raw.stateValid result.quantum && history initial result)
    return result) fuel

def outputValid (program : Semantics.Observation.Program) (state : State) : Bool :=
  Raw.outputValid ⟨program.inputs,[],program.outputs,program.effect⟩ state.quantum &&
  program.classicalOutputs.all (visible state) &&
  (!state.observe || program.effect == .observe) &&
  (program.effect != .unitary || state.quantum.frame.length == (program.inputs.flatMap (·.wires)).length)

structure Checked where
  program : Semantics.Observation.Program
  state : State
  prepared : Semantics.Observation.Prepared

/-- Original interfaces and operations are independently read into literal
instrument events. No Rust checker decision, extracted circuit or result flag
is an input. Retained dependencies must have been freshly reconstructed. -/
def verify (dependencies : List Dependency) (program : Semantics.Observation.Program) : WorkM Checked := do
  exactWork (Exact.charge (program.inputs.length + (program.inputs.map (fun port => port.wires.length)).sum +
    program.classicalInputs.length + program.outputs.length + program.classicalOutputs.length))
  let quantum ← lift (program.inputs.foldlM Raw.input {})
  let initial ← lift (program.classicalInputs.foldlM insertClassical {quantum})
  let state ← checkOps dependencies 65 initial program.operations
  guard (outputValid program state)
  let prepared ← lift (readOption (Semantics.Observation.read program))
  guard (prepared.state.live == state.quantum.live && prepared.state.frame == state.quantum.frame)
  return ⟨program,state,prepared⟩

theorem classical_fresh (state next : State) (id : Nat)
    (ok : insertClassical state id = .ok next) :
    id ∉ state.classical.map (·.1) ∧ next.classical = state.classical ++ [(id,state.scope)] := by
  unfold insertClassical at ok
  obtain ⟨_,checked,h⟩ := except_bind_success _ _ _ ok
  have condition := Raw.require_success _ checked
  have same := Except.ok.inj h
  subst next
  refine ⟨?_,rfl⟩
  simp only [Bool.and_eq_true] at condition
  simpa using condition.2

theorem checkOps_invariants (dependencies : List Dependency) (fuel : Nat) (initial final : State)
    (ops : List Semantics.Observation.Op) (work left : Nat)
    (ok : (checkOps dependencies fuel initial ops).run work = (.ok final,left)) :
    Raw.stateValid final.quantum = true ∧ history initial final = true := by
  cases fuel with
  | zero => cases ok
  | succ fuel =>
    unfold checkOps at ok
    obtain ⟨result,_,_,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨_,_,hg,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst final
    simpa only [Bool.and_eq_true] using (guard_success _ _ _ _ hg).1

/-- Globally issued quantum tokens, wires and classical values survive every
exclusive branch. Consuming an owner never makes its identity fresh again. -/
theorem checkOps_history (dependencies : List Dependency) (fuel : Nat) (initial final : State)
    (ops : List Semantics.Observation.Op) (work left : Nat)
    (ok : (checkOps dependencies fuel initial ops).run work = (.ok final,left)) :
    (∀ id ∈ initial.quantum.seenTokens, id ∈ final.quantum.seenTokens) ∧
    (∀ wire ∈ initial.quantum.seenWires, wire ∈ final.quantum.seenWires) ∧
    (∀ value ∈ initial.classical, value ∈ final.classical) := by
  have preserved := (checkOps_invariants _ _ _ _ _ _ _ ok).2
  simp only [history_eq,Bool.and_eq_true,List.all_eq_true,List.contains_iff_mem] at preserved
  exact ⟨preserved.1.1,preserved.1.2,preserved.2⟩

/-- The actual right-arm entry inherits every ID issued by the complete left
arm. Restoration changes only its live frame/effect, never global freshness. -/
theorem exclusive_arms_history (dependencies : List Dependency) (fuel : Nat)
    (entry left right : State) (ops : List Semantics.Observation.Op) (work remaining : Nat)
    (ok : (checkOps dependencies fuel (enter (restore entry left)) ops).run work = (.ok right,remaining)) :
    (∀ id ∈ left.quantum.seenTokens, id ∈ right.quantum.seenTokens) ∧
    (∀ wire ∈ left.quantum.seenWires, wire ∈ right.quantum.seenWires) ∧
    (∀ value ∈ left.classical, value ∈ right.classical) := by
  simpa only [enter,restore] using checkOps_history _ _ _ _ _ _ _ ok

/-- Structural facts retained for composition with independent denotations.
Independent OwnershipSafe, full EffectSound and quantitative resource bounds
are separate obligations. -/
structure Postcondition (program : Semantics.Observation.Program) (checked : Checked) : Prop where
  original : checked.program = program
  output : outputValid program checked.state = true
  state : Raw.stateValid checked.state.quantum = true
  reader : Semantics.Observation.read program = some checked.prepared
  live : checked.prepared.state.live = checked.state.quantum.live
  frame : checked.prepared.state.frame = checked.state.quantum.frame

theorem verify_postcondition (dependencies : List Dependency) (program : Semantics.Observation.Program)
    (checked : Checked) (work left : Nat)
    (ok : (verify dependencies program).run work = (.ok checked,left)) :
    Postcondition program checked := by
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨initial,a,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨state,b,ops,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,valid,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨prepared,_,read,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,aligned,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst checked
  have original : Semantics.Observation.read program = some prepared := by
    have reader := (lift_success _ _ _ _ read).1
    unfold readOption at reader
    cases source : Semantics.Observation.read program <;> simp_all
  have frames := (guard_success _ _ _ _ aligned).1
  simp only [Bool.and_eq_true,beq_iff_eq] at frames
  exact ⟨rfl,(guard_success _ _ _ _ valid).1,
    (checkOps_invariants dependencies 65 initial state program.operations a b ops).1,
    original,frames.1,frames.2⟩

theorem verify_conditions (dependencies : List Dependency) (program : Semantics.Observation.Program)
    (checked : Checked) (work left : Nat)
    (ok : (verify dependencies program).run work = (.ok checked,left)) :
    checked.program = program ∧ outputValid program checked.state = true ∧
    Semantics.Observation.read program = some checked.prepared := by
  have facts := verify_postcondition _ _ _ _ _ ok
  exact ⟨facts.original,facts.output,facts.reader⟩

end QleisliKernel.Raw.Observation
