import QleisliKernel.Qirf.RuntimeOwnerTransition
import QleisliKernel.Qirf.RuntimePrimitiveAction
import QleisliKernel.Qirf.RuntimeStructuralAction
import QleisliKernel.Qirf.RuntimeStaticPrimitive
import QleisliKernel.Qirf.RuntimeNamedBoundary
import QleisliKernel.Qirf.RuntimeCallScope
import QleisliKernel.Qirf.RuntimeOrdinaryInputs
import QleisliKernel.Qirf.RuntimeSourceBoundary
import QleisliKernel.Qirf.RuntimeContextRequest
import QleisliKernel.Qirf.RuntimeOperationPaths
import QleisliKernel.Qirf.OperationIRMeaning
import QleisliKernel.Qirf.SectorArm
import QleisliKernel.SourceTypes.QuantumArms

/-! One original runtime-body loop with literal caller frames.
Source parameter/result trees and owner permutations stay intact. A child uses
only its actual literal parent interval; its canonical role namespace is local,
while the parent interval separately retains every caller spectator. Pure
islands and actual ordinary/observing steps remain distinct checked data. This
stage refuses forms whose continuations have not yet been connected; complete
instrument/code and ordinary history/storage obligations remain open. It issues
no handle and is not the complete v5 runtime acceptance gate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimePureBody
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open SourceRuntimeValues RuntimeOwnerMap
abbrev Context := RuntimeContextRequest.Context
abbrev Position := SourceSequence.Position

inductive OutputBoundary where
  | rootOrder
  | localScope

inductive Mode where
  | pureBody
  | runtimeBody

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
      (boundary : RuntimeNamedBoundary.Checked frame.interval inputs event before childHistory childRetired source.checked.summary.value)
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
        (NominalSector.checkLogicals inputCode outputCode restriction.sectors labels expected) logical)
      (owners : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles) : Node dependencies program block

inductive Nodes (dependencies : List Semantics.Finite.Dependency) :
    (program : Semantics.Observation.Program) → RuntimeInterval.Block dependencies program → Type where
  | nil {program block} : Nodes dependencies program block
  | cons {program block} (first : Node dependencies program block)
      (rest : Nodes dependencies program block) : Nodes dependencies program block
end

def Nodes.ofList {dependencies program block} (nodes : List (Node dependencies program block)) :
    Nodes dependencies program block := nodes.foldr Nodes.cons Nodes.nil

def staticNodes {dependencies program block start count} :
    (action : RuntimeStaticPrimitive.Action) →
      @RuntimeStaticPrimitive.Bound dependencies program block start count action →
        List (Node dependencies program block)
  | _,.identity _ => []
  | _,.primitive checked => [.primitive checked]

mutual
/-- The common loop records every actual mixed interval. Pure composition
continues to consume only its pure islands and requires complete pure coverage;
an observation or classical gap cannot acquire a fabricated pure equation. -/
inductive Step (dependencies : List Semantics.Finite.Dependency) :
    (program : Semantics.Observation.Program) → RuntimeInterval.Block dependencies program → Type where
  | pure {program block} (node : Node dependencies program block) : Step dependencies program block
  | gap {program block start count before ordinary}
      (checked : RuntimeOrdinaryBody.Gap block start count before ordinary) : Step dependencies program block
  | observation {program block sources rootOwner rootName caller functionName path event position before ordinary}
      (checked : @RuntimeOrdinaryBody.Observation sources rootOwner rootName caller functionName dependencies program
        path event block position before ordinary) : Step dependencies program block
  | named {program block start count inputs sources caller before childHistory childRetired ordinary}
      (event : SourceRuntimeContext.NamedEvent sources caller)
      (frame : RuntimeCallScope.Checked block start count inputs ordinary event.effect)
      (source : SourceRuntimeTrace.Body event.target.signature)
      (sourceRead : RuntimeInterval.Computed (SourceRuntimeTrace.readNamedBody event) source)
      (childBlock : RuntimeInterval.Block dependencies frame.program)
      (boundary : RuntimeNamedBoundary.Checked frame.interval inputs event before childHistory childRetired source.checked.summary.value)
      (finalOrdinary : RuntimeOrdinaryBody.State)
      (children : Steps dependencies frame.program childBlock) : Step dependencies program block

inductive Steps (dependencies : List Semantics.Finite.Dependency) :
    (program : Semantics.Observation.Program) → RuntimeInterval.Block dependencies program → Type where
  | nil {program block} : Steps dependencies program block
  | cons {program block} (first : Step dependencies program block)
      (rest : Steps dependencies program block) : Steps dependencies program block
end

def Steps.ofList {dependencies program block} (steps : List (Step dependencies program block)) :
    Steps dependencies program block := steps.foldr Steps.cons Steps.nil

abbrev Island (dependencies : List Semantics.Finite.Dependency) :=
  (program : Semantics.Observation.Program) ×
    (block : RuntimeInterval.Block dependencies program) × Node dependencies program block

structure Result (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program) where
  prepared : RuntimeInterval.Prepared dependencies program
  history : RuntimeStructuralAction.SourceState
  retired : List Owner
  actions : List (Node dependencies program prepared.block)
  steps : List (Step dependencies program prepared.block)
  ordinary : RuntimeOrdinaryBody.State
  obligations : List (Island dependencies) := []

def Result.bindings {dependencies program} (result : Result dependencies program) : Map := result.history.bindings

def Result.islands {dependencies program} (result : Result dependencies program) : List (Island dependencies) :=
  result.actions.map (fun node => ⟨program,result.prepared.block,node⟩) ++ result.obligations


/-- One state and one event handler are shared by enclosing and selected
static sequences. Context cursors and source history are never reconstructed. -/
abbrev LoopState (dependencies : List Semantics.Finite.Dependency)
    (program : Semantics.Observation.Program) (block : RuntimeInterval.Block dependencies program) :=
  RuntimeStructuralAction.SourceState × List Owner × RuntimeOrdinaryBody.State ×
    List (Node dependencies program block) × List (Step dependencies program block) × List (Island dependencies) ×
    Nat × List (Position × Context) × List RuntimeContextRequest.Site × List RuntimeProviderHeader.Request

private def reordered (roles : List Owner) (state : Raw.Observation.State) (bindings : Map) :
    WorkM (RuntimeOwnerMap.Checked roles state) := do
  let ordered ← RuntimeOwnerMap.order roles bindings
  RuntimeOwnerMap.check roles state ordered

private def singletonOrdinary (value : Value) : Bool := (ordinary value).all fun (basis,_) =>
  Semantics.FiniteCarrier.dimension basis == some 1

/-- Every supported source event consumes exactly its real interval. Empty
identities are valid; an omitted phase or a wrong equal-width role still fails
the actual local equation. Selection providers re-enter this same source body
reader before their arm equations are used. Classical-only gaps and destructive
primitives use the ordinary companion on this same body/block. Complete ordinary
histories/storage, basis actions, ordinary branches and
demanded source transformations remain incomplete. -/
def run (artifact : Artifact) (root : Validity.Root) : Nat → Mode → OutputBoundary →
    {rootOwner rootName owner name : String} →
    {signature : SourceRuntimeContext.Signature artifact.sources owner name} →
    (body : SourceRuntimeTrace.Body signature) →
    RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name →
    (program : Semantics.Observation.Program) → Context → Map → RuntimeOrdinaryBody.State →
    RuntimeInterval.Prepared root.dependencies program →
    WorkM (Result root.dependencies program) :=
  Nat.rec (fun _ _ {_ _ _ _ _} _ _ _ _ _ _ _ => throw .limit)
    (fun _ next mode outputBoundary {rootOwner rootName owner name _} body path program request initial initialOrdinary prepared => do
      let source := body.checked
      let dependencies := root.dependencies
      guard (request.branches.isEmpty && !source.signature.operations.hasMeaningRequirements) .request
      match mode with
      | .pureBody =>
        guard (source.summary.inferredEffect == .unitary &&
          singletonOrdinary source.summary.value && source.summary.parameterValues.all singletonOrdinary &&
          program.classicalInputs.isEmpty && program.classicalOutputs.isEmpty &&
          !prepared.whole.state.observe) .request
        let _ ← lift (readOption (Sector.pureOps program.operations))
        pure ()
      | .runtimeBody =>
        guard (SourceEffect.permits (some program.effect) source.summary.inferredEffect) .request
      let roles := source.summary.parameterValues.flatMap valueOwners
      let initial ← reordered roles prepared.entry initial
      let initialHistory : RuntimeStructuralAction.SourceState := ⟨initial.bindings,roles,source.summary.nextOwner⟩
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
          let prepared ← RuntimeInterval.prepare dependencies native.ir.original.program
          let checked ← next .pureBody .rootOrder body (.root body)
            native.ir.original.program headerRequest.2 bindings {} prepared
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
      let advance : LoopState dependencies program prepared.block → Nat →
          WorkM (LoopState dependencies program prepared.block) :=
        fun (history,retired,ordinary,actions,steps,obligations,cursor,calls,sites,bodies) start => do
          guard (cursor ≤ start) .request
          if cursor == start then
            return (history,retired,ordinary,actions,steps,obligations,cursor,calls,sites,bodies)
          else
            let gap ← RuntimeOrdinaryBody.readGap prepared.block cursor (start-cursor) history ordinary
            return (history,retired,gap.ssa,actions,steps ++ [.gap gap],obligations,start,calls,sites,bodies)
      let step : LoopState dependencies program prepared.block →
          (SourceRuntimeContext.Event artifact.sources owner × Position) →
            WorkM (LoopState dependencies program prepared.block) := fun state (event,position) => do
          let (history,retired,ordinary,actions,steps,obligations,_cursor,calls,sites,bodies) ← advance state position.start
          let interval ← RuntimeInterval.check prepared.block position.start position.count
          let callerFrame ← reordered (history.bindings.map (·.owner)) interval.before history.bindings
          let bindings := callerFrame.bindings
          let before : RuntimeStructuralAction.SourceState := {history with bindings}
          let structural := match event with
            | .primitive event => ([.join,.split,.unit,.finish] : List CallName.Primitive).contains event.kind
            | _ => false
          let observing := match event with
            | .primitive event => ([.measureZ,.discard] : List CallName.Primitive).contains event.kind
            | _ => false
          let readOwners := RuntimeOwnerTransition.read interval callerFrame.bindings
          let continuation (owners : RuntimeOwnerTransition.Checked interval callerFrame.bindings) :
              RuntimeStructuralAction.SourceState := {before with bindings := owners.after.bindings}
          match event with
          | .primitive event =>
            if structural then
              let action ← RuntimeStructuralAction.read prepared.block position.start position.count event before
              let node : Node dependencies program prepared.block := .structural action
              return (action.after,retired ++ action.inputRoles,ordinary,actions ++ [node],steps ++ [.pure node],
                obligations,position.start+position.count,calls,sites,bodies)
            else if observing then
              match mode with
              | .pureBody => throw .request
              | .runtimeBody =>
                let action ← RuntimeOrdinaryBody.readObservation path event prepared.block position before ordinary
                return (action.after,retired ++ action.retired,action.ordinary,actions,steps ++ [.observation action],
                  obligations,position.start+position.count,calls,sites,bodies)
            else do
              let owners ← readOwners
              guard (event.allocated.isEmpty && event.consumed.isEmpty && event.nextOrdinal == before.nextOrdinal) .request
              let [[.owner operand]] := event.arguments | throw .request
              let kind ← match event.kind with
                | .h => pure Semantics.PrimitiveOperator.Kind.h
                | .globalPhaseEighth => pure Semantics.PrimitiveOperator.Kind.globalPhaseEighth
                | _ => throw .request
              let [input] ← rolePorts [operand] bindings | throw .request
              let [output] ← rolePorts [operand] owners.after.bindings | throw .request
              let action ← RuntimePrimitiveAction.check prepared.block position.start position.count
                input.token output.token operand kind
              let node : Node dependencies program prepared.block := .primitive action
              return (continuation owners,retired,ordinary,actions ++ [node],steps ++ [.pure node],
                obligations,position.start+position.count,calls,sites,bodies)
          | .phase event =>
            let owners ← readOwners
            let [input] ← rolePorts [event.operand] bindings | throw .request
            let [output] ← rolePorts [event.operand] owners.after.bindings | throw .request
            let action ← RuntimePrimitiveAction.check prepared.block position.start position.count
              input.token output.token event.operand (.phase event.application.coefficient.exponent)
            let node : Node dependencies program prepared.block := .primitive action
            return (continuation owners,retired,ordinary,actions ++ [node],steps ++ [.pure node],
              obligations,position.start+position.count,calls,sites,bodies)
          | .named event =>
            let (callPosition,child) :: calls := calls | throw .request
            guard (callPosition == position) .request
            let originalRead ← NaturalAffine.witness (SourceRuntimeTrace.readNamedBody event)
            let original := originalRead.val
            let inputs ← rolePorts event.inputOwners bindings
            let childRoles := original.checked.summary.parameterValues.flatMap valueOwners
            if callerName : event.target.callerName = name then
              let parent : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner event.target.callerName := by
                simpa only [callerName] using path
              let childPath := RuntimeOrdinaryBody.CallPath.named event original
                (by with_reducible exact originalRead.property) parent
              match mode with
              | .pureBody =>
                guard (event.effect == .unitary) .request
                let frame ← RuntimeCallInterval.read prepared.block position.start position.count (inputs.map (·.token))
                let inputOwners := (frame.selected.zip event.inputOwners).map fun (port,role) =>
                  (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)
                let childInitial ← RuntimeSourceBoundary.bindings childRoles inputOwners
                let nested ← next .pureBody .localScope original childPath frame.program child childInitial ordinary frame.prepared
                let boundary ← RuntimeNamedBoundary.read frame.interval (inputs.map (·.token))
                  event before nested.history nested.retired original.checked.summary.value
                let node : Node dependencies program prepared.block := .named event frame original
                  (by with_reducible exact originalRead.property) nested.prepared.block boundary (Nodes.ofList nested.actions)
                return (boundary.after,retired ++ event.consumed,nested.ordinary,actions ++ [node],steps ++ [.pure node],
                  obligations ++ nested.obligations,position.start+position.count,calls,sites,bodies)
              | .runtimeBody =>
                let frame ← RuntimeCallScope.read prepared.block position.start position.count
                  (inputs.map (·.token)) ordinary event.effect
                let inputOwners := (frame.selected.zip event.inputOwners).map fun (port,role) =>
                  (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)
                let childInitial ← RuntimeSourceBoundary.bindings childRoles inputOwners
                let nested ← next .runtimeBody .localScope original childPath frame.program child childInitial
                  frame.visible.ssa frame.prepared
                let boundary ← RuntimeNamedBoundary.read frame.interval (inputs.map (·.token))
                  event before nested.history nested.retired original.checked.summary.value
                let step : Step dependencies program prepared.block := .named event frame original
                  (by with_reducible exact originalRead.property) nested.prepared.block boundary nested.ordinary (Steps.ofList nested.steps)
                return (boundary.after,retired ++ event.consumed,nested.ordinary,actions,steps ++ [step],
                  obligations ++ nested.obligations,position.start+position.count,calls,sites,bodies)
            else throw .request
          | .operation event =>
            let owners ← readOwners
            guard (event.operation.graph.root.input == event.operation.graph.root.output &&
              event.allocated.isEmpty && event.consumed.isEmpty) .request
            let (callPosition,child) :: calls := calls | throw .request
            guard (callPosition == position && child.positions.isEmpty && child.sites.isEmpty &&
              child.calls.isEmpty && child.branches.isEmpty) .request
            let (expected,children) ← checkOperation event.operation.graph OperationAccess.applicable child.bodies
            let inputs ← rolePorts event.inputOwners bindings
            let outputs ← rolePorts event.inputOwners owners.after.bindings
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
              let node : Node dependencies program prepared.block := .operation frame inputCode.val outputCode.val physical.val expected
                (by with_reducible exact inputCode.property) (by with_reducible exact outputCode.property)
                (by with_reducible exact physical.property) action equation
              pure (continuation owners,retired,ordinary,actions ++ [node],steps ++ [.pure node],
                obligations ++ children,position.start+position.count,calls,sites,bodies)
            else throw .equation
          | .selection _ parsed _ selector target scope naturals .. =>
            let owners ← RuntimeOwnerTransition.read interval callerFrame.bindings
            let site :: sites := sites | throw .request
            guard (site.position == position) .request
            let table ← QuantumArms.readArmsWithInstantiation source.signature.original source.signature.instantiation
              source.signature.supply parsed.keyword.span.startByte selector.basis target.basis (some naturals) scope
            guard (table.arms.length == site.arms.length) .request
            let entry ← RuntimeOwnerTransition.readPair [selector,target] callerFrame.bindings
            let exit ← RuntimeOwnerTransition.readPair [selector,target] owners.after.bindings
            let si := entry.first.port
            let ti := entry.second.port
            let so := exit.first.port
            let to := exit.second.port
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
            let attached ← RuntimePureInterval.checkAt interval 2 [si.token,ti.token] [so.token,to.token] [selector,target]
            let frame := attached.val
            let sourcePorts : RuntimeOwnerTransition.Selection interval [si.token,ti.token] [so.token,to.token] [selector,target] :=
              ⟨_,callerFrame,owners,entry,exit,rfl,rfl⟩
            let restriction ← NaturalAffine.witness (Raw.Sector.read dependencies [.bits selectorLayout.bits]
              [.bits targetLayout.bits] (RuntimePureInterval.fragment frame.selected frame.operations [so.token,to.token]))
            let logical ← NaturalAffine.witness (NominalSector.checkLogicals inputCode outputCode restriction.val.sectors
              selectorLayout.labels expected)
            let node : Node dependencies program prepared.block := .selection frame selectorLayout.bits targetLayout.bits restriction.val
              (by with_reducible exact restriction.property) inputCode outputCode selectorLayout.labels expected logical.val
              (by with_reducible exact logical.property) (attached.property.symm ▸ sourcePorts)
            pure ({before with bindings := owners.after.bindings},retired,ordinary,actions ++ [node],steps ++ [.pure node],
              obligations ++ checked,position.start+position.count,calls,sites,bodies)
          | _ =>
            let _ ← readOwners
            throw .request
      let (history,retired,ordinary,actions,steps,obligations,cursor,calls,sites,bodies) ←
        (source.events.zip request.positions).foldlM
        (fun state (event,position) => do
          match event with
          | .staticConditional event _ =>
            let sequence : RuntimeStaticPrimitive.Continuation event ← (match mode with
              | .pureBody => do
                  let source ← RuntimeStaticPrimitive.readSequence event
                  pure (.unchanged source)
              | .runtimeBody => RuntimeStaticPrimitive.readContinuation event)
            let positions ← sequence.positions position
            guard (positions.length == sequence.selected.result.events.length) .request
            let state ← advance state position.start
            let (history,retired,ordinary,actions,steps,obligations,cursor,calls,sites,bodies) := state
            let interval ← RuntimeInterval.check prepared.block position.start position.count
            let bindings := (← reordered (history.bindings.map (·.owner)) interval.before history.bindings).bindings
            let before : RuntimeStructuralAction.SourceState := {history with bindings}
            let _ ← RuntimeStaticPrimitive.readContinuationBefore sequence interval before
            let count := sequence.selected.result.events.length
            -- The genuine shared fold appends the actual pure or mixed steps
            -- to the existing prefixes. Charge those copies and comparisons.
            exactWork (Exact.charge (32*(count+1)*(actions.length+steps.length+obligations.length+count+1)+
              32*(Raw.OwnerFlow.fields retired+1)))
            let initial : LoopState dependencies program prepared.block :=
              (before,retired,ordinary,actions,steps,obligations,cursor,calls,sites,bodies)
            let result ← (sequence.selected.result.events.zip positions).foldlM step initial
            let (after,afterRetired,_ordinary,_actions,_steps,_obligations,afterCursor,_calls,_sites,_bodies) := result
            guard (afterCursor == position.start+position.count) .request
            let _ ← RuntimeStaticPrimitive.readContinuationAfter sequence interval before after retired afterRetired
            return result
          | _ => step state (event,position)) (initialHistory,([] : List Owner),initialOrdinary,
            ([] : List (Node dependencies program prepared.block)),([] : List (Step dependencies program prepared.block)),
            obligations,0,request.calls,request.sites,bodies)
      guard (cursor ≤ program.operations.length && calls.isEmpty && sites.isEmpty && bodies.isEmpty) .request
      let (ordinary,steps) ← if cursor == program.operations.length then pure (ordinary,steps) else do
        let gap ← RuntimeOrdinaryBody.readGap prepared.block cursor (program.operations.length-cursor) history ordinary
        pure (gap.ssa,steps ++ [.gap gap])
      guard (history.issued == roles ++ source.summary.allocated && retired == source.summary.consumed &&
        history.nextOrdinal == source.summary.nextOrdinal) .request
      let bindings := (← reordered (valueOwners source.summary.value) prepared.whole.state history.bindings).bindings
      let outputs ← rolePorts (valueOwners source.summary.value) bindings
      guard (match outputBoundary with
        | .rootOrder => outputs.map (·.token) == program.outputs
        | .localScope => decide ((outputs.map (·.token)).Perm program.outputs)) .request
      return ⟨prepared,{history with bindings},retired,actions,steps,ordinary,obligations⟩)

structure Checked (artifact : Artifact) (root : Validity.Root) {owner name signature}
    (body : @SourceRuntimeTrace.Body artifact.sources owner name signature)
    (program : Semantics.Observation.Program) (request : Context) (initial : Map) where
  prepared : RuntimeInterval.Prepared root.dependencies program
  result : Result root.dependencies program
  checked : RuntimeInterval.Computed
    (run artifact root 128 .pureBody .rootOrder body (.root body) program request initial {} prepared) result

def checkPrepared (artifact : Artifact) (root : Validity.Root) {owner name signature}
    (body : @SourceRuntimeTrace.Body artifact.sources owner name signature)
    (program : Semantics.Observation.Program) (request : Context) (initial : Map)
    (prepared : RuntimeInterval.Prepared root.dependencies program) :
    WorkM (Checked artifact root body program request initial) := do
  let checked ← NaturalAffine.witness
    (run artifact root 128 .pureBody .rootOrder body (.root body) program request initial {} prepared)
  return ⟨prepared,checked.val,by with_reducible exact checked.property⟩

def check (artifact : Artifact) (root : Validity.Root) {owner name signature}
    (body : @SourceRuntimeTrace.Body artifact.sources owner name signature)
    (program : Semantics.Observation.Program) (request : Context) (initial : Map) :
    WorkM (Checked artifact root body program request initial) := do
  let prepared ← RuntimeInterval.prepare root.dependencies program
  checkPrepared artifact root body program request initial prepared

structure RuntimeChecked (artifact : Artifact) (root : Validity.Root) {owner name signature}
    (body : @SourceRuntimeTrace.Body artifact.sources owner name signature)
    (request : Context) (runtime : RuntimeFamily.Request)
    (prepared : RuntimeInterval.Prepared root.dependencies root.program)
    (inputs : RuntimeSourceBoundary.Inputs body prepared runtime.inputStorage)
    (ordinary : RuntimeOrdinaryInputs.Checked body prepared runtime inputs) where
  result : Result root.dependencies root.program
  checked : RuntimeInterval.Computed
    (run artifact root 128 .runtimeBody .rootOrder body (.root body) root.program request
      inputs.owners.bindings ordinary.ssa prepared) result

/-- The general preparation receives only an independently derived initial SSA
state on the same body/root/storage/preparation. Complete actual history and
final ordinary storage correspondence, branch continuations and code/instrument
composition remain necessary before any production acceptance can use it. -/
def checkRuntime (artifact : Artifact) (root : Validity.Root) {owner name signature}
    (body : @SourceRuntimeTrace.Body artifact.sources owner name signature)
    (request : Context) (runtime : RuntimeFamily.Request)
    (prepared : RuntimeInterval.Prepared root.dependencies root.program)
    (inputs : RuntimeSourceBoundary.Inputs body prepared runtime.inputStorage)
    (ordinary : RuntimeOrdinaryInputs.Checked body prepared runtime inputs) :
    WorkM (RuntimeChecked artifact root body request runtime prepared inputs ordinary) := do
  let checked ← NaturalAffine.witness
    (run artifact root 128 .runtimeBody .rootOrder body (.root body) root.program request
      inputs.owners.bindings ordinary.ssa prepared)
  return ⟨checked.val,by with_reducible exact checked.property⟩

end QleisliKernel.Qirf.RuntimePureBody
