import QleisliKernel.Qirf.PureInterval

/-! Literal mixed-runtime blocks inside one original observing program.
Every subblock retains its original slice or branch edge and the actual Raw
entry state, including global issuance and classical scope. Observing bodies
are never converted to pure programs. Source events, SSA expressions, owner
roles and operator equations remain obligations of the enclosing body gate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeInterval
open QleisliKernel QleisliKernel.Finite

abbrev Computed {α : Type} (action : WorkM α) (value : α) : Prop :=
  ∃ before after, action.run before = (.ok value,after)

abbrev State := Raw.Observation.State
abbrev Op := Semantics.Observation.Op
abbrev Program := Semantics.Observation.Program
abbrev Dependency := Semantics.Finite.Dependency

/-- This is exactly the original checker's transition between exclusive arms.
The second arm retains the first arm's issued identities, while restoring the
entry quantum frame and effect. Its lexical scope is fresh. -/
def rightEntry (before left : State) : State :=
  Raw.Observation.enter (Raw.Observation.restore before
    (Raw.Observation.leave before.scope (Raw.Observation.enter before).scope left))

/-- The indices retain the actual operations and entry state of every nested
block. A branch edge decreases the checker's own depth; a literal call slice
keeps that depth. No separate program or dependency snapshot is manufactured. -/
inductive Origin (dependencies : List Dependency) (program : Program) :
    Nat → State → List Op → Type where
  | root {entry : State} (read : Computed (PureInterval.initial program) entry) :
      Origin dependencies program 65 entry program.operations
  | slice {fuel : Nat} {entry before : State} {operations : List Op}
      (parent : Origin dependencies program fuel entry operations) (start count : Nat)
      (range : start+count ≤ operations.length)
      (read : Computed (Raw.Observation.checkOps dependencies fuel entry (operations.take start)) before) :
      Origin dependencies program fuel before ((operations.drop start).take count)
  | thenArm {fuel : Nat} {entry before : State} {operations thenOps elseOps : List Op}
      {condition : Nat} {quantum : List Semantics.Observation.QuantumPhi}
      {classical : List Semantics.Observation.ClassicalPhi}
      (parent : Origin dependencies program (fuel+1) entry operations) (offset : Nat)
      (original : operations[offset]? = some (.branch condition thenOps elseOps quantum classical))
      (read : Computed (Raw.Observation.checkOps dependencies (fuel+1) entry (operations.take offset)) before) :
      Origin dependencies program fuel (Raw.Observation.enter before) thenOps
  | elseArm {fuel : Nat} {entry before left : State} {operations thenOps elseOps : List Op}
      {condition : Nat} {quantum : List Semantics.Observation.QuantumPhi}
      {classical : List Semantics.Observation.ClassicalPhi}
      (parent : Origin dependencies program (fuel+1) entry operations) (offset : Nat)
      (original : operations[offset]? = some (.branch condition thenOps elseOps quantum classical))
      (read : Computed (Raw.Observation.checkOps dependencies (fuel+1) entry (operations.take offset)) before)
      (leftRead : Computed (Raw.Observation.checkOps dependencies fuel
        (Raw.Observation.enter before) thenOps) left) :
      Origin dependencies program fuel (rightEntry before left) elseOps

structure Block (dependencies : List Dependency) (program : Program) where
  fuel : Nat
  entry : State
  operations : List Op
  original : Origin dependencies program fuel entry operations

structure Prepared (dependencies : List Dependency) (program : Program) where
  whole : Raw.Observation.Checked
  verified : Computed (Raw.Observation.verify dependencies program) whole
  entry : State
  inputRead : Computed (PureInterval.initial program) entry

def prepare (dependencies : List Dependency) (program : Program) : WorkM (Prepared dependencies program) := do
  let whole ← SourceTypes.NaturalAffine.witness (Raw.Observation.verify dependencies program)
  let entry ← SourceTypes.NaturalAffine.witness (PureInterval.initial program)
  return ⟨whole.val,by with_reducible exact whole.property,
    entry.val,by with_reducible exact entry.property⟩

def Prepared.block {dependencies program} (prepared : Prepared dependencies program) :
    Block dependencies program :=
  ⟨65,prepared.entry,program.operations,.root prepared.inputRead⟩

structure Checked {dependencies program} (block : Block dependencies program) (start count : Nat) where
  range : start+count ≤ block.operations.length
  before : State
  prefixRead : Computed
    (Raw.Observation.checkOps dependencies block.fuel block.entry (block.operations.take start)) before
  after : State
  intervalRead : Computed (Raw.Observation.checkOps dependencies block.fuel before
    ((block.operations.drop start).take count)) after

def check {dependencies program} (block : Block dependencies program) (start count : Nat) :
    WorkM (Checked block start count) := do
  exactWork (Exact.charge (16*(block.operations.length+start+count+1)))
  if range : start+count ≤ block.operations.length then
    let before ← SourceTypes.NaturalAffine.witness
      (Raw.Observation.checkOps dependencies block.fuel block.entry (block.operations.take start))
    let after ← SourceTypes.NaturalAffine.witness (Raw.Observation.checkOps dependencies block.fuel
      before.val ((block.operations.drop start).take count))
    return ⟨range,before.val,by with_reducible exact before.property,
      after.val,by with_reducible exact after.property⟩
  else throw .request

def Checked.block {dependencies program block start count}
    (checked : @Checked dependencies program block start count) : Block dependencies program :=
  ⟨block.fuel,checked.before,(block.operations.drop start).take count,
    .slice block.original start count checked.range checked.prefixRead⟩

structure Branch {dependencies program} (block : Block dependencies program) (offset : Nat) where
  childFuel : Nat
  depth : block.fuel = childFuel+1
  condition : Nat
  thenOps : List Op
  elseOps : List Op
  quantum : List Semantics.Observation.QuantumPhi
  classical : List Semantics.Observation.ClassicalPhi
  original : block.operations[offset]? = some (.branch condition thenOps elseOps quantum classical)
  interval : Checked block offset 1
  thenState : State
  thenRead : Computed (Raw.Observation.checkOps dependencies childFuel
    (Raw.Observation.enter interval.before) thenOps) thenState
  elseState : State
  elseRead : Computed (Raw.Observation.checkOps dependencies childFuel
    (rightEntry interval.before thenState) elseOps) elseState

/-- Both original arms run the existing Raw checker. A constant condition,
selected simulator outcome or empty arm cannot omit the other arm's reads. -/
def readBranch {dependencies program} (block : Block dependencies program) (offset : Nat) :
    WorkM (Branch block offset) := do
  let interval ← check block offset 1
  match depth : block.fuel with
  | 0 => throw .limit
  | childFuel+1 =>
    match original : block.operations[offset]? with
    | some (.branch condition thenOps elseOps quantum classical) =>
      let thenState ← SourceTypes.NaturalAffine.witness (Raw.Observation.checkOps dependencies childFuel
        (Raw.Observation.enter interval.before) thenOps)
      let elseState ← SourceTypes.NaturalAffine.witness (Raw.Observation.checkOps dependencies childFuel
        (rightEntry interval.before thenState.val) elseOps)
      return ⟨childFuel,depth,condition,thenOps,elseOps,quantum,classical,original,interval,
        thenState.val,by with_reducible exact thenState.property,
        elseState.val,by with_reducible exact elseState.property⟩
    | _ => throw .request

def Branch.thenBlock {dependencies program block offset}
    (branch : @Branch dependencies program block offset) : Block dependencies program := by
  refine ⟨branch.childFuel,Raw.Observation.enter branch.interval.before,branch.thenOps,?_⟩
  have parent : Origin dependencies program (branch.childFuel+1) block.entry block.operations := by
    rw [← branch.depth]
    exact block.original
  have prefix : Computed (Raw.Observation.checkOps dependencies (branch.childFuel+1)
      block.entry (block.operations.take offset)) branch.interval.before := by
    rw [← branch.depth]
    exact branch.interval.prefixRead
  exact .thenArm parent offset branch.original prefix

def Branch.elseBlock {dependencies program block offset}
    (branch : @Branch dependencies program block offset) : Block dependencies program := by
  refine ⟨branch.childFuel,rightEntry branch.interval.before branch.thenState,branch.elseOps,?_⟩
  have parent : Origin dependencies program (branch.childFuel+1) block.entry block.operations := by
    rw [← branch.depth]
    exact block.original
  have prefix : Computed (Raw.Observation.checkOps dependencies (branch.childFuel+1)
      block.entry (block.operations.take offset)) branch.interval.before := by
    rw [← branch.depth]
    exact branch.interval.prefixRead
  exact .elseArm parent offset branch.original prefix branch.thenRead

theorem Prepared.originalRoot {dependencies program} (prepared : Prepared dependencies program) :
    Raw.Observation.Postcondition program prepared.whole := by
  obtain ⟨before,after,read⟩ := prepared.verified
  exact Raw.Observation.verify_postcondition _ _ _ _ _ read

theorem Checked.history {dependencies program block start count}
    (checked : @Checked dependencies program block start count) :
    Raw.stateValid checked.before.quantum = true ∧
    Raw.Observation.history block.entry checked.before = true ∧
    Raw.stateValid checked.after.quantum = true ∧
    Raw.Observation.history checked.before checked.after = true := by
  obtain ⟨a,b,prefix⟩ := checked.prefixRead
  obtain ⟨c,d,interval⟩ := checked.intervalRead
  have before := Raw.Observation.checkOps_invariants _ _ _ _ _ _ _ prefix
  have after := Raw.Observation.checkOps_invariants _ _ _ _ _ _ _ interval
  exact ⟨before.1,before.2,after.1,after.2⟩

theorem Branch.bothHistories {dependencies program block offset}
    (branch : @Branch dependencies program block offset) :
    Raw.Observation.history (Raw.Observation.enter branch.interval.before) branch.thenState = true ∧
    Raw.Observation.history (rightEntry branch.interval.before branch.thenState) branch.elseState = true := by
  obtain ⟨a,b,left⟩ := branch.thenRead
  obtain ⟨c,d,right⟩ := branch.elseRead
  exact ⟨(Raw.Observation.checkOps_invariants _ _ _ _ _ _ _ left).2,
    (Raw.Observation.checkOps_invariants _ _ _ _ _ _ _ right).2⟩

end QleisliKernel.Qirf.RuntimeInterval
