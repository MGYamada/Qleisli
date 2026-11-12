import QleisliKernel.Qirf.RuntimeInterval

/-! Pure local actions in authentic mixed-runtime blocks.
The surrounding original root, branch scope and observation history remain in
RuntimeInterval. The selected literal action retains every zero-width owner
and the complete spectator frame; its proof does not sharpen the outer effect.
Source roles, local codes, operator equations and native dispatch are separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimePureInterval
open QleisliKernel QleisliKernel.Finite
open RuntimeInterval (Block Computed)

def fragmentWithEffect (inputs : List Semantics.Raw.Port) (operations : List Semantics.Raw.Op)
    (outputs : List Nat) (effect : Semantics.Raw.Effect) : Semantics.Raw.Program :=
  ⟨inputs,operations,outputs,effect⟩

def fragment (inputs : List Semantics.Raw.Port) (operations : List Semantics.Raw.Op)
    (outputs : List Nat) : Semantics.Raw.Program :=
  ⟨inputs,operations,outputs,.unitary⟩

/-- An actual pure fragment with independently read entry and return ports.
Source owner correspondence is established by the enclosing source event. -/
structure Literal {dependencies program} (block : Block dependencies program)
    (start count : Nat) (inputs outputs : List Nat) (effect : Semantics.Raw.Effect) where
  interval : RuntimeInterval.Checked block start count
  operations : List Semantics.Raw.Op
  literal : (block.operations.drop start).take count = operations.map Semantics.Observation.Op.pure
  selected : List Semantics.Raw.Port
  atEntry : PureInterval.ports interval.before inputs = some selected
  pureBody : Raw.Prepared
  pureRead : Computed (Raw.Pure.verify dependencies
    (fragmentWithEffect selected operations outputs effect)) pureBody
  returned : List Semantics.Raw.Port
  rawExit : PureInterval.portsOf pureBody.state.live outputs = some returned
  atExit : PureInterval.ports interval.after outputs = some returned
  spectators : PureInterval.spectators interval.before inputs = PureInterval.spectators interval.after outputs

structure Checked {dependencies program} (block : Block dependencies program)
    (arity start count : Nat) (inputs outputs : List Nat)
    (roles : List Semantics.SourceOwners.Owner)
    extends Literal block start count inputs outputs .unitary where
  arities : inputs.length = arity ∧ outputs.length = arity ∧ roles.length = arity
  ownerReturn : Semantics.RawOwnerFlow.Returns roles (fragment selected operations outputs) roles

private def checkArity (arity : Nat) (inputs outputs : List Nat)
    (roles : List Semantics.SourceOwners.Owner) :
    WorkM (PLift (inputs.length = arity ∧ outputs.length = arity ∧ roles.length = arity)) := do
  guard (arity ≤ 128) .limit
  exactWork (Exact.charge (16*(inputs.length+outputs.length+roles.length+1)))
  if h : inputs.length = arity ∧ outputs.length = arity ∧ roles.length = arity then return ⟨h⟩
  else throw .request

/-- Reuse the caller's literal interval and the exact ordered ports for any
pure effect. The same proof retains the complete spectator frame. -/
def readLiteral {dependencies program} {block : Block dependencies program}
    {start count}
    (interval : RuntimeInterval.Checked block start count)
    (inputs outputs : List Nat) (effect : Semantics.Raw.Effect) :
    WorkM {frame : Literal block start count inputs outputs effect // frame.interval = interval} := do
  guard (effect != .observe) .request
  match parsed : Sector.pureOps ((block.operations.drop start).take count) with
  | none => throw .request
  | some operations =>
    exactWork (Exact.charge (32*(interval.before.quantum.live.length+interval.after.quantum.live.length+1)))
    match atEntry : PureInterval.ports interval.before inputs with
    | none => throw .request
    | some selected =>
      let pureBody ← SourceTypes.NaturalAffine.witness
        (Raw.Pure.verify dependencies (fragmentWithEffect selected operations outputs effect))
      match rawExit : PureInterval.portsOf pureBody.val.state.live outputs with
      | none => throw .request
      | some returned =>
        if atExit : PureInterval.ports interval.after outputs = some returned then
          if spectators : PureInterval.spectators interval.before inputs =
              PureInterval.spectators interval.after outputs then
            return ⟨⟨interval,operations,Sector.pureOps_bound _ _ parsed,selected,atEntry,
              pureBody.val,by with_reducible exact pureBody.property,
              returned,rawExit,atExit,spectators⟩,rfl⟩
          else throw .request
        else throw .request

private def readPorts {dependencies program} {block : Block dependencies program}
    {arity start count} {inputs outputs : List Nat} {roles : List Semantics.SourceOwners.Owner}
    (interval : RuntimeInterval.Checked block start count)
    (arities : inputs.length = arity ∧ outputs.length = arity ∧ roles.length = arity) :
    WorkM {frame : Checked block arity start count inputs outputs roles // frame.interval = interval} := do
  let frame ← readLiteral interval inputs outputs .unitary
  let ownerReturn ← Raw.OwnerFlow.check roles roles
    (fragment frame.val.selected frame.val.operations outputs)
  return ⟨⟨frame.val,arities,ownerReturn.down⟩,frame.property⟩

/-- Read the local computation in the caller's already checked interval. The
result carries that same interval for the source-owner transition. -/
def checkAt {dependencies program} {block : Block dependencies program} {start count}
    (interval : RuntimeInterval.Checked block start count) (arity : Nat) (inputs outputs : List Nat)
    (roles : List Semantics.SourceOwners.Owner) :
    WorkM {frame : Checked block arity start count inputs outputs roles // frame.interval = interval} := do
  let arities ← checkArity arity inputs outputs roles
  readPorts interval arities.down

/-- The local pure verifier consumes only the literal selected operations.
Both surrounding boundaries are independently checked in their original block
and global issuance/scope state, including inside either observing branch. -/
def check {dependencies program} (block : Block dependencies program)
    (arity start count : Nat) (inputs outputs : List Nat)
    (roles : List Semantics.SourceOwners.Owner) :
    WorkM (Checked block arity start count inputs outputs roles) := do
  let arities ← checkArity arity inputs outputs roles
  let interval ← RuntimeInterval.check block start count
  return (← readPorts interval arities.down).val

theorem Checked.originalOperations {dependencies program block arity start count inputs outputs roles}
    (checked : @Checked dependencies program block arity start count inputs outputs roles) :
    (block.operations.drop start).take count = checked.operations.map Semantics.Observation.Op.pure :=
  checked.literal

theorem Checked.history {dependencies program block arity start count inputs outputs roles}
    (checked : @Checked dependencies program block arity start count inputs outputs roles) :
    Raw.Observation.history block.entry checked.interval.before = true ∧
    Raw.Observation.history checked.interval.before checked.interval.after = true :=
  ⟨checked.interval.history.2.1,checked.interval.history.2.2.2⟩

end QleisliKernel.Qirf.RuntimePureInterval
