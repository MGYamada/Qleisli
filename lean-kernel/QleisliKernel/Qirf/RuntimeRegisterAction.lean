import QleisliKernel.Qirf.RuntimeStructuralAction

/-! Bind the original register index to the literal Raw owner repartition.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeRegisterAction
open QleisliKernel Finite SourceTypes
open RuntimeStructuralAction (SourceState widths)

private def outputTokens (kind : CallName.Primitive) (index : Nat)
    (inputs : List Semantics.Raw.Port) (operations : List Semantics.Raw.Op) : WorkM (List Nat) := do
  match kind,inputs,operations with
  | .takeBit,[port],[.split input front tail leftBits,
      .split next selected suffix selectedBits,.join left right rest] =>
    guard (input == port.token && leftBits == index && next == tail &&
      selectedBits == 1 && left == front && right == suffix) .request
    return [selected,rest]
  | .putBit,[bit,rest],[.split input front suffix leftBits,
      .join left selected head,.join next right output] =>
    guard (input == rest.token && leftBits == index && left == front &&
      selected == bit.token && next == head && right == suffix) .request
    return [output]
  | _,_,_ => throw .request

private def outputWires (kind : CallName.Primitive) (index : Nat)
    (inputs : List Semantics.Raw.Port) : List (List Nat) :=
  match kind,inputs with
  | .takeBit,[port] =>
    [(port.wires.drop index).take 1,port.wires.take index ++ port.wires.drop (index+1)]
  | .putBit,[bit,rest] =>
    [rest.wires.take index ++ bit.wires ++ rest.wires.drop index]
  | _,_ => []

structure Checked {dependencies program sources caller}
    (block : RuntimeInterval.Block dependencies program) (start count : Nat)
    (event : SourceRuntimeContext.RegisterEvent sources caller) (before : SourceState) where
  interval : RuntimeInterval.Checked block start count
  operations : List Semantics.Raw.Op
  literal : (block.operations.drop start).take count = operations.map Semantics.Observation.Op.pure
  inputs : List Semantics.Raw.Port
  inputsRead : RuntimeInterval.Computed
    ((RuntimeOwnerMap.order event.consumed before.bindings).map (·.map (·.port))) inputs
  outputs : List Semantics.Raw.Port
  outputsRead : PureInterval.ports interval.after (outputs.map (·.token)) = some outputs
  index : Nat
  originalIndex : (event.application.arguments.map (·.value))[1]? = some index
  tokenOrder : RuntimeInterval.Computed (outputTokens event.kind index inputs operations) (outputs.map (·.token))
  wireOrder : outputs.map (·.wires) = outputWires event.kind index inputs
  inputWidths : widths inputs event.consumed = true
  outputWidths : widths outputs event.allocated = true
  spectators : PureInterval.spectators interval.before (inputs.map (·.token)) =
    PureInterval.spectators interval.after (outputs.map (·.token))
  after : SourceState
  bindings : after.bindings = before.bindings.filter (fun binding => !event.consumed.contains binding.owner) ++
    (event.allocated.zip outputs).map (fun (owner,port) => ⟨owner,port⟩)
  issued : after.issued = before.issued ++ event.allocated
  ordinal : after.nextOrdinal = event.afterOrdinal
  afterFrame : RuntimeOwnerMap.Checked (after.bindings.map (·.owner)) interval.after
  sameFrame : afterFrame.bindings = after.bindings

def read {dependencies program sources caller} {block : RuntimeInterval.Block dependencies program} {start count}
    (interval : RuntimeInterval.Checked block start count)
    (event : SourceRuntimeContext.RegisterEvent sources caller) (before : SourceState) :
    WorkM (Checked block start count event before) := do
  exactWork (Exact.charge (64*(SourceRuntimeValues.valueFields event.value+
    (event.arguments.map SourceRuntimeValues.valueFields).sum+
    Raw.OwnerFlow.fields before.issued+Raw.OwnerFlow.fields (before.bindings.map (·.owner))+
    block.operations.length+before.issued.length*event.allocated.length+1)))
  guard (before.nextOrdinal == event.nextOrdinal &&
    event.allocated.all (fun owner => !before.issued.any (fun previous => previous.ordinal == owner.ordinal))) .request
  let _ ← RuntimeOwnerMap.checkBindings (before.bindings.map (·.owner)) interval.before before.bindings
  let inputs ← NaturalAffine.witness ((RuntimeOwnerMap.order event.consumed before.bindings).map (·.map (·.port)))
  match originalIndex : (event.application.arguments.map (·.value))[1]? with
  | none => throw .request
  | some axis =>
    match literal : Sector.pureOps ((block.operations.drop start).take count) with
    | none => throw .request
    | some operations =>
      let tokens ← NaturalAffine.witness (outputTokens event.kind axis inputs.val operations)
      let some outputs := PureInterval.ports interval.after tokens.val | throw .request
      if returned : PureInterval.ports interval.after (outputs.map (·.token)) = some outputs ∧
          outputs.map (·.token) = tokens.val ∧ outputs.map (·.wires) = outputWires event.kind axis inputs.val ∧
          widths inputs.val event.consumed = true ∧ widths outputs event.allocated = true ∧
          PureInterval.spectators interval.before (inputs.val.map (·.token)) =
            PureInterval.spectators interval.after (outputs.map (·.token)) then
        let after : SourceState :=
          ⟨before.bindings.filter (fun binding => !event.consumed.contains binding.owner) ++
              (event.allocated.zip outputs).map (fun (owner,port) => ⟨owner,port⟩),
            before.issued ++ event.allocated,event.afterOrdinal⟩
        let frame ← RuntimeOwnerMap.checkBindings (after.bindings.map (·.owner)) interval.after after.bindings
        return ⟨interval,operations,Sector.pureOps_bound _ _ literal,inputs.val,
          by with_reducible exact inputs.property,outputs,returned.1,axis,originalIndex,
          by rw [returned.2.1]; with_reducible exact tokens.property,
          returned.2.2.1,returned.2.2.2.1,returned.2.2.2.2.1,returned.2.2.2.2.2,
          after,rfl,rfl,rfl,frame.val,frame.property⟩
      else throw .request

end QleisliKernel.Qirf.RuntimeRegisterAction
