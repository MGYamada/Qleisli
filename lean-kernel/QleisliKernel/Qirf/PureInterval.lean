import QleisliKernel.Qirf.Sector
import QleisliKernel.Raw.OwnerFlow
import QleisliKernel.SourceTypes.NaturalAffine

/-! Literal pure intervals in an original observing root. Full-root checks keep
global ownership, scope and observation history; interval checks cannot sharpen
the root effect. Source occurrence/role binding, code/arm equations, fresh QIRF
dependencies and native/QDV integration remain enclosing obligations. This
component grants no accepted handle and is not a source-preservation theorem.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.PureInterval
open Finite

abbrev Witness {α : Type} (action : WorkM α) :=
  {value : α // ∃ work left, action.run work = (.ok value,left)}

def initial (program : Semantics.Observation.Program) : WorkM Raw.Observation.State := do
  let quantum ← lift (program.inputs.foldlM Raw.input {})
  lift (program.classicalInputs.foldlM Raw.Observation.insertClassical {quantum})

def portsOf (live : List Semantics.Raw.Port) (tokens : List Nat) : Option (List Semantics.Raw.Port) :=
  tokens.mapM fun token => live.find? (fun port => port.token == token)

def ports (state : Raw.Observation.State) (tokens : List Nat) : Option (List Semantics.Raw.Port) :=
  portsOf state.quantum.live tokens

def spectators (state : Raw.Observation.State) (tokens : List Nat) : List Semantics.Raw.Port :=
  state.quantum.live.filter (fun port => !tokens.contains port.token)

structure Slice (program : Semantics.Observation.Program) (start count : Nat) where
  operations : List Semantics.Raw.Op
  original : (program.operations.drop start).take count = operations.map Semantics.Observation.Op.pure

def readSlice (program : Semantics.Observation.Program) (start count : Nat) :
    WorkM (Slice program start count) := do
  match parsed : Sector.pureOps ((program.operations.drop start).take count) with
  | none => throw .request
  | some operations => return ⟨operations,Sector.pureOps_bound _ _ parsed⟩

def fragment {program : Semantics.Observation.Program} {start count : Nat}
    (inputs : List Semantics.Raw.Port) (slice : Slice program start count)
    (outputs : List Nat) : Semantics.Raw.Program := ⟨inputs,slice.operations,outputs,.unitary⟩

end QleisliKernel.Qirf.PureInterval

namespace QleisliKernel.Qirf.PureInterval.Many
open Finite

structure Checked (arity : Nat) (dependencies : List Semantics.Finite.Dependency)
    (program : Semantics.Observation.Program) (start count : Nat) (inputs outputs : List Nat)
    (roles : List Semantics.SourceOwners.Owner) where
  range : start+count ≤ program.operations.length
  arity : inputs.length = arity ∧ outputs.length = arity ∧ roles.length = arity
  whole : Witness (Raw.Observation.verify dependencies program)
  entry : Witness (initial program)
  before : Witness (Raw.Observation.checkOps dependencies 65 entry.val (program.operations.take start))
  slice : Slice program start count
  after : Witness (Raw.Observation.checkOps dependencies 65 before.val
    ((program.operations.drop start).take count))
  selected : List Semantics.Raw.Port
  atEntry : ports before.val inputs = some selected
  pureBody : Witness (Raw.Pure.verify dependencies (fragment selected slice outputs))
  ownerReturn : Semantics.RawOwnerFlow.Returns roles (fragment selected slice outputs) roles
  returned : List Semantics.Raw.Port
  rawExit : portsOf pureBody.val.state.live outputs = some returned
  atExit : ports after.val outputs = some returned
  retainedFrame : spectators before.val inputs = spectators after.val outputs

/-- Both witnesses are indexed by the exact dependencies and original program.
Only a fresh successful execution of the existing checker constructs this root.
No proof of another program, dependency list or source body is substituted. -/
structure Prepared (dependencies : List Semantics.Finite.Dependency)
    (program : Semantics.Observation.Program) where
  whole : Witness (Raw.Observation.verify dependencies program)
  entry : Witness (initial program)

def prepare (dependencies : List Semantics.Finite.Dependency)
    (program : Semantics.Observation.Program) : WorkM (Prepared dependencies program) := do
  let whole ← SourceTypes.NaturalAffine.witness (Raw.Observation.verify dependencies program)
  let entry ← SourceTypes.NaturalAffine.witness (initial program)
  return ⟨whole,entry⟩

/-- The common interval continuation retains every original prefix, slice,
local purity, owner-return, history and spectator-frame check. -/
def finish {arity dependencies program}
    (prepared : Prepared dependencies program) (start count : Nat)
    (inputs outputs : List Nat) (roles : List Semantics.SourceOwners.Owner)
    (bounded : start+count ≤ program.operations.length)
    (arityProof : inputs.length = arity ∧ outputs.length = arity ∧ roles.length = arity) :
    WorkM (Checked arity dependencies program start count inputs outputs roles) := do
  let before ← SourceTypes.NaturalAffine.witness
    (Raw.Observation.checkOps dependencies 65 prepared.entry.val (program.operations.take start))
  let slice ← readSlice program start count
  let after ← SourceTypes.NaturalAffine.witness
    (Raw.Observation.checkOps dependencies 65 before.val ((program.operations.drop start).take count))
  exactWork (Exact.charge (32*(before.val.quantum.live.length+after.val.quantum.live.length+1)))
  match atEntry : ports before.val inputs with
  | none => throw .request
  | some selected =>
    let pureBody ← SourceTypes.NaturalAffine.witness
      (Raw.Pure.verify dependencies (fragment selected slice outputs))
    let ownerReturn ← Raw.OwnerFlow.check roles roles (fragment selected slice outputs)
    match rawExit : portsOf pureBody.val.state.live outputs with
    | none => throw .request
    | some returned =>
      if atExit : ports after.val outputs = some returned then
        if retained : spectators before.val inputs = spectators after.val outputs then
          return ⟨bounded,arityProof,prepared.whole,prepared.entry,before,slice,after,selected,atEntry,pureBody,
            ownerReturn.down,returned,rawExit,atExit,retained⟩
        else throw .request
      else throw .request

/-- A shared fresh root still performs each original range/arity reservation and
all interval checks. Preparation's work is charged once by the enclosing caller. -/
def checkPrepared (arity : Nat) (dependencies : List Semantics.Finite.Dependency)
    (program : Semantics.Observation.Program) (prepared : Prepared dependencies program)
    (start count : Nat) (inputs outputs : List Nat) (roles : List Semantics.SourceOwners.Owner) :
    WorkM (Checked arity dependencies program start count inputs outputs roles) := do
  guard (arity ≤ 128) .limit
  exactWork (Exact.charge (8*(program.operations.length+inputs.length+outputs.length+roles.length+1)))
  if bounded : start+count ≤ program.operations.length then
    if arity : inputs.length = arity ∧ outputs.length = arity ∧ roles.length = arity then
      finish prepared start count inputs outputs roles bounded arity
    else throw .request
  else throw .request

/-- Standalone compatibility entrypoint. Its original order, results, errors
and work are unchanged; it uses the same continuation as checkPrepared. -/
def check (arity : Nat) (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (start count : Nat) (inputs outputs : List Nat) (roles : List Semantics.SourceOwners.Owner) :
    WorkM (Checked arity dependencies program start count inputs outputs roles) := do
  guard (arity ≤ 128) .limit
  exactWork (Exact.charge (8*(program.operations.length+inputs.length+outputs.length+roles.length+1)))
  if bounded : start+count ≤ program.operations.length then
    if arity : inputs.length = arity ∧ outputs.length = arity ∧ roles.length = arity then
      let prepared ← prepare dependencies program
      finish prepared start count inputs outputs roles bounded arity
    else throw .request
  else throw .request

theorem Checked.originalOperations
    {arity dependencies program start count inputs outputs roles}
    (checked : Checked arity dependencies program start count inputs outputs roles) :
    (program.operations.drop start).take count = checked.slice.operations.map Semantics.Observation.Op.pure :=
  checked.slice.original

/-- The complete original program, including its declared observing effect,
remains the subject of the existing root checker. -/
theorem Checked.originalRoot
    {arity dependencies program start count inputs outputs roles}
    (checked : Checked arity dependencies program start count inputs outputs roles) :
    Raw.Observation.Postcondition program checked.whole.val := by
  obtain ⟨work,left,ran⟩ := checked.whole.property
  exact Raw.Observation.verify_postcondition _ _ _ _ _ ran

theorem Checked.boundaryHistory
    {arity dependencies program start count inputs outputs roles}
    (checked : Checked arity dependencies program start count inputs outputs roles) :
    Raw.stateValid checked.before.val.quantum = true ∧
    Raw.Observation.history checked.entry.val checked.before.val = true ∧
    Raw.stateValid checked.after.val.quantum = true ∧
    Raw.Observation.history checked.before.val checked.after.val = true := by
  obtain ⟨a,b,traversed⟩ := checked.before.property
  obtain ⟨c,d,interval⟩ := checked.after.property
  have before := Raw.Observation.checkOps_invariants _ _ _ _ _ _ _ traversed
  have after := Raw.Observation.checkOps_invariants _ _ _ _ _ _ _ interval
  exact ⟨before.1,before.2,after.1,after.2⟩

end QleisliKernel.Qirf.PureInterval.Many

namespace QleisliKernel.Qirf.PureInterval
open Finite

/-- The established two-owner result retains its original public structure. -/
structure Checked (dependencies : List Semantics.Finite.Dependency)
    (program : Semantics.Observation.Program) (start count : Nat) (inputs outputs : List Nat)
    (roles : List Semantics.SourceOwners.Owner) where
  range : start+count ≤ program.operations.length
  arity : inputs.length = 2 ∧ outputs.length = 2 ∧ roles.length = 2
  whole : Witness (Raw.Observation.verify dependencies program)
  entry : Witness (initial program)
  before : Witness (Raw.Observation.checkOps dependencies 65 entry.val (program.operations.take start))
  slice : Slice program start count
  after : Witness (Raw.Observation.checkOps dependencies 65 before.val
    ((program.operations.drop start).take count))
  selected : List Semantics.Raw.Port
  atEntry : ports before.val inputs = some selected
  pureBody : Witness (Raw.Pure.verify dependencies (fragment selected slice outputs))
  ownerReturn : Semantics.RawOwnerFlow.Returns roles (fragment selected slice outputs) roles
  returned : List Semantics.Raw.Port
  rawExit : portsOf pureBody.val.state.live outputs = some returned
  atExit : ports after.val outputs = some returned
  retainedFrame : spectators before.val inputs = spectators after.val outputs

/-- Structural result transport only; all checks run in the common core. -/
def Many.Checked.toOriginal {dependencies program start count inputs outputs roles}
    (checked : Many.Checked 2 dependencies program start count inputs outputs roles) :
    QleisliKernel.Qirf.PureInterval.Checked dependencies program start count inputs outputs roles :=
  ⟨checked.range,checked.arity,checked.whole,checked.entry,checked.before,checked.slice,
    checked.after,checked.selected,checked.atEntry,checked.pureBody,checked.ownerReturn,
    checked.returned,checked.rawExit,checked.atExit,checked.retainedFrame⟩

def Checked.toMany {dependencies program start count inputs outputs roles}
    (checked : Checked dependencies program start count inputs outputs roles) :
    Many.Checked 2 dependencies program start count inputs outputs roles :=
  ⟨checked.range,checked.arity,checked.whole,checked.entry,checked.before,checked.slice,
    checked.after,checked.selected,checked.atEntry,checked.pureBody,checked.ownerReturn,
    checked.returned,checked.rawExit,checked.atExit,checked.retainedFrame⟩

theorem Checked.toMany_toOriginal {dependencies program start count inputs outputs roles}
    (checked : Checked dependencies program start count inputs outputs roles) :
    checked.toMany.toOriginal = checked := rfl

theorem Many.Checked.toOriginal_toMany {dependencies program start count inputs outputs roles}
    (checked : Many.Checked 2 dependencies program start count inputs outputs roles) :
    checked.toOriginal.toMany = checked := rfl

def check (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (start count : Nat) (inputs outputs : List Nat) (roles : List Semantics.SourceOwners.Owner) :
    WorkM (Checked dependencies program start count inputs outputs roles) :=
  (Many.check 2 dependencies program start count inputs outputs roles).map Many.Checked.toOriginal

theorem Checked.originalOperations
    {dependencies program start count inputs outputs roles}
    (checked : Checked dependencies program start count inputs outputs roles) :
    (program.operations.drop start).take count = checked.slice.operations.map Semantics.Observation.Op.pure :=
  checked.slice.original

/-- The complete original program, including its declared observing effect,
remains the subject of the existing root checker. -/
theorem Checked.originalRoot
    {dependencies program start count inputs outputs roles}
    (checked : Checked dependencies program start count inputs outputs roles) :
    Raw.Observation.Postcondition program checked.whole.val := by
  obtain ⟨work,left,ran⟩ := checked.whole.property
  exact Raw.Observation.verify_postcondition _ _ _ _ _ ran

theorem Checked.boundaryHistory
    {dependencies program start count inputs outputs roles}
    (checked : Checked dependencies program start count inputs outputs roles) :
    Raw.stateValid checked.before.val.quantum = true ∧
    Raw.Observation.history checked.entry.val checked.before.val = true ∧
    Raw.stateValid checked.after.val.quantum = true ∧
    Raw.Observation.history checked.before.val checked.after.val = true := by
  obtain ⟨a,b,traversed⟩ := checked.before.property
  obtain ⟨c,d,interval⟩ := checked.after.property
  have before := Raw.Observation.checkOps_invariants _ _ _ _ _ _ _ traversed
  have after := Raw.Observation.checkOps_invariants _ _ _ _ _ _ _ interval
  exact ⟨before.1,before.2,after.1,after.2⟩

end QleisliKernel.Qirf.PureInterval
