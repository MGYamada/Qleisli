import QleisliKernel.Qirf.RuntimePrimitiveAction
import QleisliKernel.Qirf.RuntimeSourceBoundary
import QleisliKernel.Qirf.RuntimeContextRequest

/-! Recursive original pure runtime bodies with literal caller frames.
Source parameter/result trees and owner permutations stay intact. A child uses
only its actual literal parent interval; its canonical role namespace is local,
while the parent interval separately retains every caller spectator. This
stage refuses forms whose complete continuations have not yet been connected;
it issues no handle and is not the complete v5 runtime acceptance gate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimePureBody
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open SourceRuntimeValues RuntimeOwnerMap
abbrev Context := RuntimeContextRequest.Context
abbrev Position := SourceSequence.Position

inductive Node (dependencies : List Semantics.Finite.Dependency) where
  | primitive {program : Semantics.Observation.Program} {block : RuntimeInterval.Block dependencies program}
      {start count input output role kind}
      (action : RuntimePrimitiveAction.Checked block start count input output role kind) : Node dependencies
  | named (owner name : String) (offset : Nat) (children : List (Node dependencies)) : Node dependencies

structure Result (dependencies : List Semantics.Finite.Dependency) where
  bindings : Map
  actions : List (Node dependencies)

private def rolePorts (roles : List Owner) (bindings : Map) : WorkM (List Semantics.Raw.Port) := do
  let ordered ← RuntimeOwnerMap.order roles bindings
  return ordered.map (·.port)

/-- Literal Raw transport determines each token's opaque source role. Width or
wire equality never chooses between owners, including separate Unit owners. -/
private def transition {dependencies program block start count}
    (interval : @RuntimeInterval.Checked dependencies program block start count) (before : Map) : WorkM Map := do
  exactWork (Exact.charge (32*(before.length+1)*(block.operations.length+1)))
  let operations ← lift (readOption (Sector.pureOps ((block.operations.drop start).take count)))
  let seeded ← lift (readOption (Semantics.RawOwnerFlow.seed (before.map (·.owner)) (before.map (·.port))))
  let frame ← lift (readOption (operations.foldlM Semantics.RawOwnerFlow.step seeded))
  frame.mapM fun (token,tree) => do
    match tree with
    | .pair .. => throw .request
    | .owner role bits =>
      let some port := interval.after.quantum.live.find? (·.token == token) | throw .request
      guard (port.bits == bits) .request
      return ⟨role,port⟩

private def reordered (roles : List Owner) (state : Raw.Observation.State) (bindings : Map) : WorkM Map := do
  let ordered ← RuntimeOwnerMap.order roles bindings
  let checked ← RuntimeOwnerMap.check roles state ordered
  return checked.bindings

private def singletonOrdinary (value : Value) : Bool := (ordinary value).all fun (basis,_) =>
  Semantics.FiniteCarrier.dimension basis == some 1

/-- Every supported source event consumes exactly its real interval. Empty
identities are valid; an omitted phase or a wrong equal-width role still fails
the actual local equation. Unsupported selections, access trees, basis actions,
observing calls and ordinary branches explicitly refuse until connected. -/
def run (dependencies : List Semantics.Finite.Dependency) : Nat → {sources owner name} →
    SourceRuntimeTrace.Checked sources owner name → Semantics.Observation.Program → Context → Map →
    WorkM (Result dependencies) :=
  Nat.rec (fun {_ _ _} _ _ _ _ => throw .limit)
    (fun _ next {_ _ _} source program request initial => do
      guard (request.sites.isEmpty && request.branches.isEmpty && request.bodies.isEmpty &&
        source.signature.arguments.operations.isEmpty && !source.signature.operations.hasMeaningRequirements) .request
      guard (source.summary.inferredEffect == .unitary &&
        singletonOrdinary source.summary.value && source.summary.parameterValues.all singletonOrdinary &&
        source.summary.allocated.isEmpty && source.summary.consumed.isEmpty &&
        program.classicalInputs.isEmpty && program.classicalOutputs.isEmpty) .request
      let prepared ← RuntimeInterval.prepare dependencies program
      guard (!prepared.whole.state.observe) .request
      let _ ← lift (readOption (Sector.pureOps program.operations))
      let roles := source.summary.parameterValues.flatMap valueOwners
      let initial ← reordered roles prepared.entry initial
      exactWork (Exact.charge (32*(source.events.length+request.positions.length+request.calls.length+1)^2))
      guard (request.positions.map (·.offset) == source.events.map SourceRuntimeContext.Event.offset) .request
      let (bindings,actions,cursor,calls) ← (source.events.zip request.positions).foldlM
        (fun (bindings,actions,cursor,calls) (event,position) => do
          guard (position.start == cursor) .request
          let interval ← RuntimeInterval.check prepared.block position.start position.count
          let bindings ← reordered (bindings.map (·.owner)) interval.before bindings
          let after ← transition interval bindings
          let after ← reordered (bindings.map (·.owner)) interval.after after
          match event with
          | .primitive event =>
            let [[.owner operand]] := event.arguments | throw .request
            let kind ← match event.kind with
              | .h => pure Semantics.PrimitiveOperator.Kind.h
              | .globalPhaseEighth => pure Semantics.PrimitiveOperator.Kind.globalPhaseEighth
              | _ => throw .request
            let [input] ← rolePorts [operand] bindings | throw .request
            let [output] ← rolePorts [operand] after | throw .request
            let action ← RuntimePrimitiveAction.check prepared.block position.start position.count
              input.token output.token operand kind
            return (after,actions ++ [.primitive action],position.start+position.count,calls)
          | .phase event =>
            let [input] ← rolePorts [event.operand] bindings | throw .request
            let [output] ← rolePorts [event.operand] after | throw .request
            let action ← RuntimePrimitiveAction.check prepared.block position.start position.count
              input.token output.token event.operand (.phase event.application.coefficient.exponent)
            return (after,actions ++ [.primitive action],position.start+position.count,calls)
          | .named event =>
            guard (event.effect == .unitary && event.allocated.isEmpty && event.consumed.isEmpty) .request
            let (callPosition,child) :: calls := calls | throw .request
            guard (callPosition == position) .request
            let original ← SourceRuntimeTrace.readNamedBody event
            let inputs ← rolePorts event.inputOwners bindings
            let stableOutputs ← rolePorts event.inputOwners after
            let actualOutputs ← rolePorts (valueOwners event.value) after
            let framed ← RuntimePureInterval.check prepared.block inputs.length position.start position.count
              (inputs.map (·.token)) (stableOutputs.map (·.token)) event.inputOwners
            let fragment := Semantics.Ownership.pureProgram
              (RuntimePureInterval.fragment inputs framed.operations (actualOutputs.map (·.token)))
            let childRoles := original.checked.summary.parameterValues.flatMap valueOwners
            let inputOwners := (inputs.zip event.inputOwners).map fun (port,role) =>
              (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)
            let childInitial ← RuntimeSourceBoundary.bindings childRoles inputOwners
            let nested ← next original.checked fragment child childInitial
            let childOutputs ← rolePorts (valueOwners original.checked.summary.value) nested.bindings
            guard (childOutputs.map (·.token) == actualOutputs.map (·.token)) .request
            return (after,actions ++ [.named event.target.resolution.moduleName
              event.target.resolution.declaration.name event.call.calleeOffset nested.actions],
              position.start+position.count,calls)
          | _ => throw .request) (initial,[],0,request.calls)
      guard (cursor == program.operations.length && calls.isEmpty) .request
      let bindings ← reordered (valueOwners source.summary.value) prepared.whole.state bindings
      let outputs ← rolePorts (valueOwners source.summary.value) bindings
      guard (outputs.map (·.token) == program.outputs) .request
      return ⟨bindings,actions⟩)

structure Checked {sources owner name signature}
    (body : @SourceRuntimeTrace.Body sources owner name signature)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (request : Context) (initial : Map) where
  result : Result dependencies
  checked : RuntimeInterval.Computed (run dependencies 128 body.checked program request initial) result

def check {sources owner name signature}
    (body : @SourceRuntimeTrace.Body sources owner name signature)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (request : Context) (initial : Map) : WorkM (Checked body dependencies program request initial) := do
  let checked ← NaturalAffine.witness (run dependencies 128 body.checked program request initial)
  return ⟨checked.val,by with_reducible exact checked.property⟩

end QleisliKernel.Qirf.RuntimePureBody
