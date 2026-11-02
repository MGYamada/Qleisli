import QleisliKernel.Qirf.RuntimePrimitiveAction
import QleisliKernel.Qirf.RuntimeSourceBoundary
import QleisliKernel.Qirf.RuntimeContextRequest
import QleisliKernel.Qirf.RuntimeOperationPaths
import QleisliKernel.Qirf.OperationIRMeaning
import QleisliKernel.Qirf.SectorArm
import QleisliKernel.SourceTypes.QuantumArms

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
  | operation {program : Semantics.Observation.Program} {block : RuntimeInterval.Block dependencies program}
      {arity start count inputs outputs roles}
      (frame : RuntimePureInterval.Checked block arity start count inputs outputs roles)
      (inputCode outputCode physical expected : Semantics.Exact.Matrix)
      (inputRead : RuntimeInterval.Computed
        (Carrier.ownerCode ((frame.selected.zip roles).map fun (port,role) => ⟨port,role.basis⟩)) inputCode)
      (outputRead : RuntimeInterval.Computed
        (Carrier.ownerCode ((frame.returned.zip roles).map fun (port,role) => ⟨port,role.basis⟩)) outputCode)
      (physicalRead : RuntimeInterval.Computed (Raw.ProtectedEvaluation.reconstruct dependencies
        (RuntimePureInterval.fragment frame.selected frame.operations outputs)) physical)
      (action : CodeSpace.Map inputCode outputCode physical) (equation : action.logical = expected) : Node dependencies
  | selection {program : Semantics.Observation.Program} {block : RuntimeInterval.Block dependencies program}
      {start count inputs outputs roles}
      (frame : RuntimePureInterval.Checked block 2 start count inputs outputs roles)
      (selectorBits targetBits : Nat) (restriction : Raw.Sector.Retained)
      (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
        (RuntimePureInterval.fragment frame.selected frame.operations outputs)) restriction)
      (inputCode outputCode : Semantics.Exact.Matrix) (labels : List Nat)
      (expected logical : List Semantics.Exact.Matrix)
      (equations : RuntimeInterval.Computed
        (NominalSector.checkLogicals inputCode outputCode restriction.sectors labels expected) logical) : Node dependencies

structure Result (dependencies : List Semantics.Finite.Dependency) where
  bindings : Map
  actions : List (Node dependencies)
  obligations : List (Node dependencies) := []

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
the actual local equation. Selection providers re-enter this same source body
reader before their arm equations are used. Basis actions, observing calls,
ordinary branches and demanded source transformations remain incomplete. -/
def run (artifact : Artifact) (root : Validity.Root) : Nat → {owner name : String} →
    SourceRuntimeTrace.Checked artifact.sources owner name → Semantics.Observation.Program → Context → Map →
    WorkM (Result root.dependencies) :=
  Nat.rec (fun {_ _} _ _ _ _ => throw .limit)
    (fun _ next {_ _} source program request initial => do
      let dependencies := root.dependencies
      guard (request.branches.isEmpty && !source.signature.operations.hasMeaningRequirements) .request
      guard (source.summary.inferredEffect == .unitary &&
        singletonOrdinary source.summary.value && source.summary.parameterValues.all singletonOrdinary &&
        source.summary.allocated.isEmpty && source.summary.consumed.isEmpty &&
        program.classicalInputs.isEmpty && program.classicalOutputs.isEmpty) .request
      let prepared ← RuntimeInterval.prepare dependencies program
      guard (!prepared.whole.state.observe) .request
      let _ ← lift (readOption (Sector.pureOps program.operations))
      let roles := source.summary.parameterValues.flatMap valueOwners
      let initial ← reordered roles prepared.entry initial
      let checkOperation {context description}
          (graph : StaticOperation.CheckedGraph artifact.sources context description)
          (requested : StaticOperation.Paths) (requests : List RuntimeProviderHeader.Request) :
          WorkM (Semantics.Exact.Matrix × List (Node dependencies)) := do
        let paths ← RuntimeOperationPaths.read graph root requested requests
        let children ← paths.bodies.mapM fun {_} {headerRequest} header _ native => do
          let body := header.original.body.checked
          let canonical := body.summary.parameterValues.flatMap valueOwners
          let owner := (⟨native.ir.original.prepared.ports.input,native.ir.original.prepared.ports.domain⟩ :
            Semantics.CarrierInterface.Owner)
          let bindings ← RuntimeSourceBoundary.bindings canonical [owner]
          let checked ← next body native.ir.original.program headerRequest.2 bindings
          pure (checked.actions ++ checked.obligations)
        let logical ← OperationIRMeaning.compute graph paths.bodies.logicals
        pure (logical,children.flatten)
      let consumeOperation {context description}
          (graph : StaticOperation.CheckedGraph artifact.sources context description)
          (requested : StaticOperation.Paths) (requests : List RuntimeProviderHeader.Request) :
          WorkM (Semantics.Exact.Matrix × List (Node dependencies) × List RuntimeProviderHeader.Request) := do
        let occurrences ← StaticOperation.readOccurrences description
        let count := (RuntimeProviderHeaders.providerIndices description occurrences).length
        guard (count ≤ requests.length) .request
        let (logical,checked) ← checkOperation graph requested (requests.take count)
        pure (logical,checked,requests.drop count)
      let required := fun (argument : String) => match source.signature.instantiation with
        | .closed _ => OperationAccess.empty
        | .static _ environment _ =>
          (⟨environment.numeric.original.header.access.contains (.applicable,argument),
            environment.numeric.original.header.access.contains (.adjointable,argument),
            environment.numeric.original.header.access.contains (.controllable,argument)⟩ : StaticOperation.Paths)
      let actuals ← RuntimeProviderHeaders.originalActuals source.signature.operations
      let (obligations,bodies) ← actuals.foldlM
        (fun (obligations,bodies) actual => do
          let (_,checked,rest) ← consumeOperation actual.2.graph (required actual.1.1) bodies
          pure (obligations ++ checked,rest)) ([],request.bodies)
      exactWork (Exact.charge (32*(source.events.length+request.positions.length+request.calls.length+1)^2))
      guard (request.positions.map (·.offset) == source.events.map SourceRuntimeContext.Event.offset) .request
      let (bindings,actions,obligations,cursor,calls,sites,bodies) ← (source.events.zip request.positions).foldlM
        (fun (bindings,actions,obligations,cursor,calls,sites,bodies) (event,position) => do
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
            return (after,actions ++ [.primitive action],obligations,position.start+position.count,calls,sites,bodies)
          | .phase event =>
            let [input] ← rolePorts [event.operand] bindings | throw .request
            let [output] ← rolePorts [event.operand] after | throw .request
            let action ← RuntimePrimitiveAction.check prepared.block position.start position.count
              input.token output.token event.operand (.phase event.application.coefficient.exponent)
            return (after,actions ++ [.primitive action],obligations,position.start+position.count,calls,sites,bodies)
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
              obligations ++ nested.obligations,position.start+position.count,calls,sites,bodies)
          | .operation event =>
            guard (event.operation.graph.root.input == event.operation.graph.root.output &&
              event.allocated.isEmpty && event.consumed.isEmpty) .request
            let (callPosition,child) :: calls := calls | throw .request
            guard (callPosition == position && child.positions.isEmpty && child.sites.isEmpty &&
              child.calls.isEmpty && child.branches.isEmpty) .request
            let (expected,children) ← checkOperation event.operation.graph OperationAccess.applicable child.bodies
            let inputs ← rolePorts event.inputOwners bindings
            let outputs ← rolePorts event.inputOwners after
            let frame ← RuntimePureInterval.check prepared.block inputs.length position.start position.count
              (inputs.map (·.token)) (outputs.map (·.token)) event.inputOwners
            let inputCode ← NaturalAffine.witness
              (Carrier.ownerCode ((frame.selected.zip event.inputOwners).map fun (port,role) => ⟨port,role.basis⟩))
            let outputCode ← NaturalAffine.witness
              (Carrier.ownerCode ((frame.returned.zip event.inputOwners).map fun (port,role) => ⟨port,role.basis⟩))
            let physical ← NaturalAffine.witness (Raw.ProtectedEvaluation.reconstruct dependencies
              (RuntimePureInterval.fragment frame.selected frame.operations (outputs.map (·.token))))
            let action ← CodeSpace.readMap inputCode.val outputCode.val physical.val
            exactWork (Exact.charge (action.logical.entries.length+expected.entries.length+1))
            if equation : action.logical = expected then
              pure (after,actions ++ [.operation frame inputCode.val outputCode.val physical.val expected
                (by with_reducible exact inputCode.property) (by with_reducible exact outputCode.property)
                (by with_reducible exact physical.property) action equation],
                obligations ++ children,position.start+position.count,calls,sites,bodies)
            else throw .equation
          | .selection _ parsed _ selector target scope naturals .. =>
            let site :: sites := sites | throw .request
            guard (site.position == position) .request
            let table ← QuantumArms.readArmsWithInstantiation source.signature.original source.signature.instantiation
              source.signature.supply parsed.keyword.span.startByte selector.basis target.basis (some naturals) scope
            guard (table.arms.length == site.arms.length) .request
            let [si,ti] ← rolePorts [selector,target] bindings | throw .request
            let [so,to] ← rolePorts [selector,target] after | throw .request
            let expectedInterface : Semantics.CarrierInterface.Interface :=
              ⟨[⟨si,selector.basis⟩,⟨ti,target.basis⟩],[⟨so,selector.basis⟩,⟨to,target.basis⟩],.unitary⟩
            guard (site.attached == expectedInterface && site.required == expectedInterface) .request
            let inputCode ← Carrier.ownerCode [⟨ti,target.basis⟩]
            let outputCode ← Carrier.ownerCode [⟨to,target.basis⟩]
            let selectorLayout ← FiniteCarrier.read selector.basis
            let targetLayout ← FiniteCarrier.read target.basis
            let (meanings,checked,bodies) ← (table.arms.zip site.arms).foldlM
              (fun (meanings,checked,bodies) (arm,subject) => do
                let (logical,children,rest) ← consumeOperation arm.operation.graph OperationAccess.controllable bodies
                let reference : SectorArm.Reference := ⟨arm.label.ordinal,target.basis,.unitary,
                  subject.implementation,subject.controlled⟩
                let actual ← SectorArm.read artifact dependencies target.basis targetLayout.bits inputCode outputCode reference
                exactWork (Exact.charge (logical.entries.length+actual.logical.entries.length+1))
                guard (actual.logical == logical) .equation
                pure (meanings ++ [(arm.label.ordinal,logical)],checked ++ children,rest)) ([],[],bodies)
            let expected ← (List.range selectorLayout.labels.length).mapM fun ordinal => do
              let some (_,logical) := meanings.find? (·.1 == ordinal) | throw .request
              pure logical
            let frame ← RuntimePureInterval.check prepared.block 2 position.start position.count
              [si.token,ti.token] [so.token,to.token] [selector,target]
            let restriction ← NaturalAffine.witness (Raw.Sector.read dependencies [.bits selectorLayout.bits]
              [.bits targetLayout.bits] (RuntimePureInterval.fragment frame.selected frame.operations [so.token,to.token]))
            let logical ← NaturalAffine.witness (NominalSector.checkLogicals inputCode outputCode restriction.val.sectors
              selectorLayout.labels expected)
            pure (after,actions ++ [.selection frame selectorLayout.bits targetLayout.bits restriction.val
              (by with_reducible exact restriction.property) inputCode outputCode selectorLayout.labels expected logical.val
              (by with_reducible exact logical.property)],obligations ++ checked,position.start+position.count,calls,sites,bodies)
          | _ => throw .request) (initial,[],obligations,0,request.calls,request.sites,bodies)
      guard (cursor == program.operations.length && calls.isEmpty && sites.isEmpty && bodies.isEmpty) .request
      let bindings ← reordered (valueOwners source.summary.value) prepared.whole.state bindings
      let outputs ← rolePorts (valueOwners source.summary.value) bindings
      guard (outputs.map (·.token) == program.outputs) .request
      return ⟨bindings,actions,obligations⟩)

structure Checked (artifact : Artifact) (root : Validity.Root) {owner name signature}
    (body : @SourceRuntimeTrace.Body artifact.sources owner name signature)
    (program : Semantics.Observation.Program) (request : Context) (initial : Map) where
  result : Result root.dependencies
  checked : RuntimeInterval.Computed (run artifact root 128 body.checked program request initial) result

def check (artifact : Artifact) (root : Validity.Root) {owner name signature}
    (body : @SourceRuntimeTrace.Body artifact.sources owner name signature)
    (program : Semantics.Observation.Program) (request : Context) (initial : Map) :
    WorkM (Checked artifact root body program request initial) := do
  let checked ← NaturalAffine.witness (run artifact root 128 body.checked program request initial)
  return ⟨checked.val,by with_reducible exact checked.property⟩

end QleisliKernel.Qirf.RuntimePureBody
