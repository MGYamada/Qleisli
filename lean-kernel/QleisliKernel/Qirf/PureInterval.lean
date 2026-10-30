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

/-- Dependencies and roles are not externally trusted: the caller must freshly
bind them to the actual graph and original source. Both whole and local checks
consume one work budget. Unknown source contexts cannot use this as a fallback. -/
def check (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (start count : Nat) (inputs outputs : List Nat) (roles : List Semantics.SourceOwners.Owner) :
    WorkM (Checked dependencies program start count inputs outputs roles) := do
  exactWork (Exact.charge (8*(program.operations.length+inputs.length+outputs.length+roles.length+1)))
  if bounded : start+count ≤ program.operations.length then
    if arity : inputs.length = 2 ∧ outputs.length = 2 ∧ roles.length = 2 then
      let whole ← SourceTypes.NaturalAffine.witness (Raw.Observation.verify dependencies program)
      let entry ← SourceTypes.NaturalAffine.witness (initial program)
      let before ← SourceTypes.NaturalAffine.witness
        (Raw.Observation.checkOps dependencies 65 entry.val (program.operations.take start))
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
              return ⟨bounded,arity,whole,entry,before,slice,after,selected,atEntry,pureBody,
                ownerReturn.down,returned,rawExit,atExit,retained⟩
            else throw .request
          else throw .request
    else throw .request
  else throw .request

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
