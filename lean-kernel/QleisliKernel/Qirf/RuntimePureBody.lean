import QleisliKernel.Qirf.RuntimePrimitiveAction
import QleisliKernel.Qirf.RuntimeStructuralAction
import QleisliKernel.Qirf.RuntimeNamedBoundary
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

inductive OutputBoundary where
  | rootOrder
  | localScope

def rolePorts (roles : List Owner) (bindings : Map) : WorkM (List Semantics.Raw.Port) := do
  let ordered ← RuntimeOwnerMap.order roles bindings
  return ordered.map (·.port)

mutual
inductive Node (dependencies : List Semantics.Finite.Dependency) :
    (program : Semantics.Observation.Program) → RuntimeInterval.Block dependencies program → Type where
  | primitive {program : Semantics.Observation.Program} {block : RuntimeInterval.Block dependencies program}
      {start count input output role kind}
      (action : RuntimePrimitiveAction.Checked block start count input output role kind) : Node dependencies program block
  | structural {program : Semantics.Observation.Program} {block : RuntimeInterval.Block dependencies program}
      {start count sources caller event before}
      (action : RuntimeStructuralAction.Checked (sources := sources) (caller := caller) block start count event before) :
      Node dependencies program block
  | named {program : Semantics.Observation.Program} {block : RuntimeInterval.Block dependencies program}
      {start count inputs} {sources : Sources} {caller : String} {before childHistory childRetired}
      (event : SourceRuntimeContext.NamedEvent sources caller)
      (frame : RuntimeCallInterval.Checked block start count inputs)
      (source : SourceRuntimeTrace.Body event.target.signature)
      (sourceRead : RuntimeInterval.Computed (SourceRuntimeTrace.readNamedBody event) source)
      (childBlock : RuntimeInterval.Block dependencies frame.program)
      (boundary : RuntimeNamedBoundary.Checked frame event before childHistory childRetired source.checked.summary.value)
      (children : Nodes dependencies frame.program childBlock) : Node dependencies program block
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
      (action : CodeSpace.Map inputCode outputCode physical) (equation : action.logical = expected) : Node dependencies program block
  | selection {program : Semantics.Observation.Program} {block : RuntimeInterval.Block dependencies program}
      {start count inputs outputs roles}
      (frame : RuntimePureInterval.Checked block 2 start count inputs outputs roles)
      (selectorBits targetBits : Nat) (restriction : Raw.Sector.Retained)
      (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
        (RuntimePureInterval.fragment frame.selected frame.operations outputs)) restriction)
      (inputCode outputCode : Semantics.Exact.Matrix) (labels : List Nat)
      (expected logical : List Semantics.Exact.Matrix)
      (equations : RuntimeInterval.Computed
        (NominalSector.checkLogicals inputCode outputCode restriction.sectors labels expected) logical) : Node dependencies program block

inductive Nodes (dependencies : List Semantics.Finite.Dependency) :
    (program : Semantics.Observation.Program) → RuntimeInterval.Block dependencies program → Type where
  | nil {program block} : Nodes dependencies program block
  | cons {program block} (first : Node dependencies program block)
      (rest : Nodes dependencies program block) : Nodes dependencies program block
end

def Nodes.ofList {dependencies program block} (nodes : List (Node dependencies program block)) :
    Nodes dependencies program block := nodes.foldr Nodes.cons Nodes.nil

abbrev Island (dependencies : List Semantics.Finite.Dependency) :=
  (program : Semantics.Observation.Program) ×
    (block : RuntimeInterval.Block dependencies program) × Node dependencies program block

structure Result (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program) where
  prepared : RuntimeInterval.Prepared dependencies program
  history : RuntimeStructuralAction.SourceState
  retired : List Owner
  actions : List (Node dependencies program prepared.block)
  obligations : List (Island dependencies) := []

def Result.bindings {dependencies program} (result : Result dependencies program) : Map := result.history.bindings

def Result.islands {dependencies program} (result : Result dependencies program) : List (Island dependencies) :=
  result.actions.map (fun node => ⟨program,result.prepared.block,node⟩) ++ result.obligations

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
def run (artifact : Artifact) (root : Validity.Root) : Nat → OutputBoundary → {owner name : String} →
    {signature : SourceRuntimeContext.Signature artifact.sources owner name} →
    SourceRuntimeTrace.Body signature → (program : Semantics.Observation.Program) → Context → Map →
    WorkM (Result root.dependencies program) :=
  Nat.rec (fun _ {_ _ _} _ _ _ _ => throw .limit)
    (fun _ next outputBoundary {_ _ _} body program request initial => do
      let source := body.checked
      let dependencies := root.dependencies
      guard (request.branches.isEmpty && !source.signature.operations.hasMeaningRequirements) .request
      guard (source.summary.inferredEffect == .unitary &&
        singletonOrdinary source.summary.value && source.summary.parameterValues.all singletonOrdinary &&
        program.classicalInputs.isEmpty && program.classicalOutputs.isEmpty) .request
      let prepared ← RuntimeInterval.prepare dependencies program
      guard (!prepared.whole.state.observe) .request
      let _ ← lift (readOption (Sector.pureOps program.operations))
      let roles := source.summary.parameterValues.flatMap valueOwners
      let initial ← reordered roles prepared.entry initial
      let initialHistory : RuntimeStructuralAction.SourceState := ⟨initial,roles,source.summary.nextOwner⟩
      let checkOperation {context description}
          (graph : StaticOperation.CheckedGraph artifact.sources context description)
          (requested : StaticOperation.Paths) (requests : List RuntimeProviderHeader.Request) :
          WorkM (Semantics.Exact.Matrix × List (Island dependencies)) := do
        let paths ← RuntimeOperationPaths.read graph root requested requests
        let children ← paths.bodies.mapM fun {_} {headerRequest} header _ native => do
          let body := header.original.body
          let canonical := body.checked.summary.parameterValues.flatMap valueOwners
          let owner := (⟨native.ir.original.prepared.ports.input,native.ir.original.prepared.ports.domain⟩ :
            Semantics.CarrierInterface.Owner)
          let bindings ← RuntimeSourceBoundary.bindings canonical [owner]
          let checked ← next .rootOrder body native.ir.original.program headerRequest.2 bindings
          pure checked.islands
        let logical ← OperationIRMeaning.compute graph paths.bodies.logicals
        pure (logical,children.flatten)
      let consumeOperation {context description}
          (graph : StaticOperation.CheckedGraph artifact.sources context description)
          (requested : StaticOperation.Paths) (requests : List RuntimeProviderHeader.Request) :
          WorkM (Semantics.Exact.Matrix × List (Island dependencies) × List RuntimeProviderHeader.Request) := do
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
      let (history,retired,actions,obligations,cursor,calls,sites,bodies) ← (source.events.zip request.positions).foldlM
        (fun (history,retired,actions,obligations,cursor,calls,sites,bodies) (event,position) => do
          guard (position.start == cursor) .request
          let interval ← RuntimeInterval.check prepared.block position.start position.count
          let bindings ← reordered (history.bindings.map (·.owner)) interval.before history.bindings
          let before : RuntimeStructuralAction.SourceState := {history with bindings}
          let structural := match event with
            | .primitive event => ([.join,.split,.unit,.finish] : List CallName.Primitive).contains event.kind
            | _ => false
          let separatelyBound := structural || match event with | .named _ => true | _ => false
          let after : Map ← if separatelyBound then pure bindings else do
            let changed ← transition interval bindings
            reordered (bindings.map (·.owner)) interval.after changed
          let continued : RuntimeStructuralAction.SourceState := {before with bindings := after}
          match event with
          | .primitive event =>
            if structural then
              let action ← RuntimeStructuralAction.read prepared.block position.start position.count event before
              return (action.after,retired ++ action.inputRoles,actions ++ [.structural action],
                obligations,position.start+position.count,calls,sites,bodies)
            else do
              guard (event.allocated.isEmpty && event.consumed.isEmpty && event.nextOrdinal == before.nextOrdinal) .request
              let [[.owner operand]] := event.arguments | throw .request
              let kind ← match event.kind with
                | .h => pure Semantics.PrimitiveOperator.Kind.h
                | .globalPhaseEighth => pure Semantics.PrimitiveOperator.Kind.globalPhaseEighth
                | _ => throw .request
              let [input] ← rolePorts [operand] bindings | throw .request
              let [output] ← rolePorts [operand] after | throw .request
              let action ← RuntimePrimitiveAction.check prepared.block position.start position.count
                input.token output.token operand kind
              return (continued,retired,actions ++ [.primitive action],obligations,position.start+position.count,calls,sites,bodies)
          | .phase event =>
            let [input] ← rolePorts [event.operand] bindings | throw .request
            let [output] ← rolePorts [event.operand] after | throw .request
            let action ← RuntimePrimitiveAction.check prepared.block position.start position.count
              input.token output.token event.operand (.phase event.application.coefficient.exponent)
            return (continued,retired,actions ++ [.primitive action],obligations,position.start+position.count,calls,sites,bodies)
          | .named event =>
            guard (event.effect == .unitary) .request
            let (callPosition,child) :: calls := calls | throw .request
            guard (callPosition == position) .request
            let originalRead ← NaturalAffine.witness (SourceRuntimeTrace.readNamedBody event)
            let original := originalRead.val
            let inputs ← rolePorts event.inputOwners bindings
            let frame ← RuntimeCallInterval.read prepared.block position.start position.count (inputs.map (·.token))
            let childRoles := original.checked.summary.parameterValues.flatMap valueOwners
            let inputOwners := (frame.selected.zip event.inputOwners).map fun (port,role) =>
              (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)
            let childInitial ← RuntimeSourceBoundary.bindings childRoles inputOwners
            let nested ← next .localScope original frame.program child childInitial
            let boundary ← RuntimeNamedBoundary.read frame event before nested.history nested.retired original.checked.summary.value
            return (boundary.after,retired ++ event.consumed,actions ++
              [.named event frame original (by with_reducible exact originalRead.property)
                nested.prepared.block boundary (Nodes.ofList nested.actions)],
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
              pure (continued,retired,actions ++ [.operation frame inputCode.val outputCode.val physical.val expected
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
            pure (continued,retired,actions ++ [.selection frame selectorLayout.bits targetLayout.bits restriction.val
              (by with_reducible exact restriction.property) inputCode outputCode selectorLayout.labels expected logical.val
              (by with_reducible exact logical.property)],obligations ++ checked,position.start+position.count,calls,sites,bodies)
          | _ => throw .request) (initialHistory,([] : List Owner),([] : List (Node dependencies program prepared.block)),
            obligations,0,request.calls,request.sites,bodies)
      guard (cursor == program.operations.length && calls.isEmpty && sites.isEmpty && bodies.isEmpty) .request
      guard (history.issued == roles ++ source.summary.allocated && retired == source.summary.consumed &&
        history.nextOrdinal == source.summary.nextOrdinal) .request
      let bindings ← reordered (valueOwners source.summary.value) prepared.whole.state history.bindings
      let outputs ← rolePorts (valueOwners source.summary.value) bindings
      guard (match outputBoundary with
        | .rootOrder => outputs.map (·.token) == program.outputs
        | .localScope => decide ((outputs.map (·.token)).Perm program.outputs)) .request
      return ⟨prepared,{history with bindings},retired,actions,obligations⟩)

structure Checked (artifact : Artifact) (root : Validity.Root) {owner name signature}
    (body : @SourceRuntimeTrace.Body artifact.sources owner name signature)
    (program : Semantics.Observation.Program) (request : Context) (initial : Map) where
  result : Result root.dependencies program
  checked : RuntimeInterval.Computed (run artifact root 128 .rootOrder body program request initial) result

def check (artifact : Artifact) (root : Validity.Root) {owner name signature}
    (body : @SourceRuntimeTrace.Body artifact.sources owner name signature)
    (program : Semantics.Observation.Program) (request : Context) (initial : Map) :
    WorkM (Checked artifact root body program request initial) := do
  let checked ← NaturalAffine.witness (run artifact root 128 .rootOrder body program request initial)
  return ⟨checked.val,by with_reducible exact checked.property⟩

end QleisliKernel.Qirf.RuntimePureBody
