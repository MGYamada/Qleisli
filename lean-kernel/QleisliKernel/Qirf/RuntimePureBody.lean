import QleisliKernel.Qirf.RuntimeOwnerTransition
import QleisliKernel.Qirf.RuntimePrimitiveAction
import QleisliKernel.Qirf.RuntimeStructuralAction
import QleisliKernel.Qirf.RuntimeStaticPrimitive
import QleisliKernel.Qirf.RuntimeNamedBoundary
import QleisliKernel.Qirf.RuntimeCallScope
import QleisliKernel.Qirf.RuntimeOrdinaryInputs
import QleisliKernel.Qirf.RuntimeBranchAction
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
  | frame

inductive Mode where
  | pureBody
  | runtimeBody

def rolePorts (roles : List Owner) (bindings : Map) : WorkM (List Semantics.Raw.Port) := do
  let ordered ← RuntimeOwnerMap.order roles bindings
  return ordered.map (·.port)

/-- The native reads that supplied both widths and the exact selector label
order. A caller cannot infer all-arm coverage from the list length alone. -/
structure SelectionLayouts (selector target : Semantics.FiniteCarrier.Basis)
    (selectorBits targetBits : Nat) (labels : List Nat) : Prop where
  selectorRead : RuntimeInterval.Computed (FiniteCarrier.read selector) ⟨selectorBits,labels⟩
  targetRead : ∃ targetLabels, RuntimeInterval.Computed (FiniteCarrier.read target) ⟨targetBits,targetLabels⟩

/-- On two original Bit ports the same source layout and successful matrix
checks bind the logical results at 0 and 1, in canonical selector order. -/
theorem SelectionLayouts.bit_bindings {selector target selectorBits targetBits labels}
    (layouts : SelectionLayouts selector target selectorBits targetBits labels)
    (selectorBasis : selector = [.bit]) (targetBasis : target = [.bit])
    {inputCode outputCode sectors expected logical}
    (equations : RuntimeInterval.Computed
      (NominalSector.checkLogicals inputCode outputCode sectors labels expected) logical) :
    selectorBits = 1 ∧ targetBits = 1 ∧ labels = [0,1] ∧ ∃ zero one,
      expected = [zero,one] ∧ logical = [zero,one] ∧
      NominalSector.LogicalBinding inputCode outputCode sectors (0,zero) zero ∧
      NominalSector.LogicalBinding inputCode outputCode sectors (1,one) one := by
  obtain ⟨a,b,sel⟩ := layouts.selectorRead
  obtain ⟨targetLabels,c,d,tgt⟩ := layouts.targetRead
  have selectorLayout := FiniteCarrier.read_reference _ _ _ _ sel
  have targetLayout := FiniteCarrier.read_reference _ _ _ _ tgt
  rw [selectorBasis] at selectorLayout
  rw [targetBasis] at targetLayout
  change some (⟨1,[0,1]⟩ : Semantics.FiniteCarrier.Layout) = some ⟨selectorBits,labels⟩ at selectorLayout
  change some (⟨1,[0,1]⟩ : Semantics.FiniteCarrier.Layout) = some ⟨targetBits,targetLabels⟩ at targetLayout
  have labelsEq := congrArg Semantics.FiniteCarrier.Layout.labels (Option.some.inj selectorLayout).symm
  have sBits := congrArg Semantics.FiniteCarrier.Layout.bits (Option.some.inj selectorLayout).symm
  have tBits := congrArg Semantics.FiniteCarrier.Layout.bits (Option.some.inj targetLayout).symm
  change labels = [0,1] at labelsEq
  refine ⟨sBits,tBits,labelsEq,?_⟩
  obtain ⟨work,left,ran⟩ := equations
  obtain ⟨count,each⟩ := NominalSector.checkLogicals_bound _ _ _ _ _ _ work left ran
  rw [labelsEq] at count each
  have two (xs : List Semantics.Exact.Matrix) (length : xs.length = 2) : ∃ a b,xs = [a,b] :=
    ⟨_,_,List.eq_getElem_of_length_eq_two xs length⟩
  obtain ⟨zero,one,rfl⟩ := two expected count
  have actualCount := QleisliKernel.Exact.listRel_length _ _ _ each
  obtain ⟨first,second,rfl⟩ := two logical actualCount
  have boundZero : NominalSector.LogicalBinding inputCode outputCode sectors (0,zero) first := each.1
  have boundOne : NominalSector.LogicalBinding inputCode outputCode sectors (1,one) second := each.2.1
  have zeroEq : first = zero := boundZero.1
  have oneEq : second = one := boundOne.1
  subst first second
  exact ⟨zero,one,rfl,rfl,boundZero,boundOne⟩

/-- The sector equations use the encodings read from the actual target owner
at entry and return. Matching dimensions alone would also admit zero codes. -/
structure SelectionCodes {dependencies program block start count}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (inputs outputs : List Nat) (selector target : Owner) (inputCode outputCode : Semantics.Exact.Matrix) where
  owners : RuntimeOwnerTransition.Selection interval inputs outputs [selector,target]
  inputRead : RuntimeInterval.Computed
    (Carrier.ownerCode [⟨owners.selected.second.port,target.basis⟩]) inputCode
  outputRead : RuntimeInterval.Computed
    (Carrier.ownerCode [⟨owners.returned.second.port,target.basis⟩]) outputCode

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
      {start count inputs outputs} {selector target : Owner}
      (frame : RuntimePureInterval.Checked block 2 start count inputs outputs [selector,target])
      (selectorBits targetBits : Nat) (restriction : Raw.Sector.Retained)
      (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
        (RuntimePureInterval.fragment frame.selected frame.operations outputs)) restriction)
      (inputCode outputCode : Semantics.Exact.Matrix) (labels : List Nat)
      (expected logical : List Semantics.Exact.Matrix)
      (equations : RuntimeInterval.Computed
        (NominalSector.checkLogicals inputCode outputCode restriction.sectors labels expected) logical)
      (codes : SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
      (layouts : SelectionLayouts selector.basis target.basis selectorBits targetBits labels) : Node dependencies program block

inductive Nodes (dependencies : List Semantics.Finite.Dependency) :
    (program : Semantics.Observation.Program) → RuntimeInterval.Block dependencies program → Type where
  | nil {program block} : Nodes dependencies program block
  | cons {program block} (first : Node dependencies program block)
      (rest : Nodes dependencies program block) : Nodes dependencies program block
end

/-- Check the literal caller interval on the original owners in their source
order. The operation graph supplies its independently checked expected action. -/
def operationNode {dependencies program} (block : RuntimeInterval.Block dependencies program)
    (position : Position) (roles : List Owner) (before after : Map)
    (expected : Semantics.Exact.Matrix) : WorkM (Node dependencies program block) := do
  let inputs ← rolePorts roles before
  let outputs ← rolePorts roles after
  let frame ← RuntimePureInterval.check block inputs.length position.start position.count
    (inputs.map (·.token)) (outputs.map (·.token)) roles
  let inputCode ← NaturalAffine.witness
    (Carrier.ownerCode ((frame.selected.zip roles).map fun (port,role) => ⟨port,role.basis⟩))
  let outputCode ← NaturalAffine.witness
    (Carrier.ownerCode ((frame.returned.zip roles).map fun (port,role) => ⟨port,role.basis⟩))
  let physical ← NaturalAffine.witness (Raw.ProtectedEvaluation.reconstruct dependencies
    (RuntimePureInterval.fragment frame.selected frame.operations (outputs.map (·.token))))
  let action ← CodeSpace.readMap inputCode.val outputCode.val physical.val
  exactWork (Exact.charge (action.logical.entries.length+expected.entries.length+1))
  if equation : action.logical = expected then
    return .operation frame inputCode.val outputCode.val physical.val expected
      (by with_reducible exact inputCode.property) (by with_reducible exact outputCode.property)
      (by with_reducible exact physical.property) action equation
  else throw .equation

/-- One original owner-preserving primitive in its actual interval. The
enclosing traversal supplies the current complete history and checked native
frame. Only the existing h/global-phase/closed-phase cases are handled here;
this helper does not select source events or provide a whole-body equation. -/
def primitiveAt {sources caller dependencies program block start count}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (history : RuntimeStructuralAction.SourceState)
    (callerFrame : RuntimeOwnerMap.Checked (history.bindings.map (·.owner)) interval.before)
    (event : SourceRuntimeContext.Event sources caller) :
    WorkM (RuntimeStructuralAction.SourceState × Node dependencies program block) := do
  let before : RuntimeStructuralAction.SourceState := {history with bindings := callerFrame.bindings}
  let owners ← RuntimeOwnerTransition.read interval callerFrame.bindings
  match event with
  | .primitive event =>
    guard (event.allocated.isEmpty && event.consumed.isEmpty && event.nextOrdinal == before.nextOrdinal) .request
    let [[.owner operand]] := event.arguments | throw .request
    let kind ← match event.kind with
      | .h => pure Semantics.PrimitiveOperator.Kind.h
      | .globalPhaseEighth => pure Semantics.PrimitiveOperator.Kind.globalPhaseEighth
      | _ => throw .request
    let [input] ← rolePorts [operand] callerFrame.bindings | throw .request
    let [output] ← rolePorts [operand] owners.after.bindings | throw .request
    let action ← RuntimePrimitiveAction.check block start count input.token output.token operand kind
    return ({before with bindings := owners.after.bindings},.primitive action)
  | .phase event =>
    let [input] ← rolePorts [event.operand] callerFrame.bindings | throw .request
    let [output] ← rolePorts [event.operand] owners.after.bindings | throw .request
    let action ← RuntimePrimitiveAction.check block start count input.token output.token event.operand
      (.phase event.application.coefficient.exponent)
    return ({before with bindings := owners.after.bindings},.primitive action)
  | _ => throw .request

/-- Verify every literal arm and the complete selector partition with the
actual ordered source owners and their encodings. The enclosing traversal
supplies a source realization at each index of this exact arm table. -/
def selectionNode {α : Type} (artifact : Artifact) {dependencies program block start count roles}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (callerFrame : RuntimeOwnerMap.Checked roles interval.before)
    (owners : RuntimeOwnerTransition.Checked interval callerFrame.bindings)
    (selector target : Owner) {moduleName name offset}
    (table : QuantumArms.Table artifact.sources moduleName name offset selector.basis target.basis)
    (site : RuntimeContextRequest.Site) (initial : α)
    (realize : Fin table.arms.length → QuantumArms.BoundArm artifact.sources moduleName selector.basis target.basis →
      α → WorkM (Semantics.Exact.Matrix × α)) : WorkM (Node dependencies program block × α) := do
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
  let inputCode ← NaturalAffine.witness (Carrier.ownerCode [⟨ti,target.basis⟩])
  let outputCode ← NaturalAffine.witness (Carrier.ownerCode [⟨to,target.basis⟩])
  let selectorRead ← NaturalAffine.witness (FiniteCarrier.read selector.basis)
  let targetRead ← NaturalAffine.witness (FiniteCarrier.read target.basis)
  let selectorLayout := selectorRead.val
  let targetLayout := targetRead.val
  let arms := table.arms.mapFinIdx fun index arm valid => ((⟨index,valid⟩ : Fin table.arms.length),arm)
  let (meanings,remaining) ← (arms.zip site.arms).foldlM
    (fun (meanings,current) ((index,arm),subject) => do
      let (logical,next) ← realize index arm current
      let reference : SectorArm.Reference := ⟨arm.label.ordinal,target.basis,.unitary,
        subject.implementation,subject.controlled⟩
      let actual ← SectorArm.read artifact dependencies target.basis targetLayout.bits inputCode.val outputCode.val reference
      exactWork (Exact.charge (logical.entries.length+actual.logical.entries.length+1))
      guard (actual.logical == logical) .equation
      pure (meanings ++ [(arm.label.ordinal,logical)],next)) ([],initial)
  let expected ← (List.range selectorLayout.labels.length).mapM fun ordinal => do
    let some (_,logical) := meanings.find? (·.1 == ordinal) | throw .request
    pure logical
  let attached ← RuntimePureInterval.checkAt interval 2 [si.token,ti.token] [so.token,to.token] [selector,target]
  let frame := attached.val
  let sourcePorts : RuntimeOwnerTransition.Selection interval [si.token,ti.token] [so.token,to.token] [selector,target] :=
    ⟨_,callerFrame,owners,entry,exit,rfl,rfl⟩
  let codes : SelectionCodes interval [si.token,ti.token] [so.token,to.token] selector target inputCode.val outputCode.val :=
    ⟨sourcePorts,by with_reducible exact inputCode.property,by with_reducible exact outputCode.property⟩
  let restriction ← NaturalAffine.witness (Raw.Sector.read dependencies [.bits selectorLayout.bits]
    [.bits targetLayout.bits] (RuntimePureInterval.fragment frame.selected frame.operations [so.token,to.token]))
  let logical ← NaturalAffine.witness (NominalSector.checkLogicals inputCode.val outputCode.val restriction.val.sectors
    selectorLayout.labels expected)
  let node : Node dependencies program block := .selection frame selectorLayout.bits targetLayout.bits restriction.val
    (by with_reducible exact restriction.property) inputCode.val outputCode.val selectorLayout.labels expected logical.val
    (by with_reducible exact logical.property) (attached.property.symm ▸ codes)
    ⟨by with_reducible exact selectorRead.property,
      ⟨targetLayout.labels,by with_reducible exact targetRead.property⟩⟩
  return (node,remaining)

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
  | conditional {program block offset sources rootOwner rootName caller name}
      (path : RuntimeOrdinaryBody.CallPath sources rootOwner rootName caller name)
      (event : SourceRuntimeContext.BranchEvent sources caller)
      (source : RuntimeBranchAction.Source event)
      (actual : @RuntimeInterval.Branch dependencies program block offset)
      (actualRead : RuntimeInterval.Computed (RuntimeInterval.readBranch block offset) actual)
      {before left right ordinary leftOrdinary rightOrdinary}
      (action : RuntimeBranchAction.Checked path event source actual before left right ordinary leftOrdinary rightOrdinary)
      (thenSteps : Steps dependencies program actual.thenBlock)
      (elseSteps : Steps dependencies program actual.elseBlock) : Step dependencies program block

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

/-- Every recursive arm remains indexed by its genuine literal block. A whole
function is wrapped with its existing Prepared object only at the public edge. -/
structure BlockResult (dependencies : List Semantics.Finite.Dependency)
    (program : Semantics.Observation.Program) (block : RuntimeInterval.Block dependencies program) where
  history : RuntimeStructuralAction.SourceState
  retired : List Owner
  actions : List (Node dependencies program block)
  steps : List (Step dependencies program block)
  ordinary : RuntimeOrdinaryBody.State
  obligations : List (Island dependencies) := []

def BlockResult.islands {dependencies program block} (result : BlockResult dependencies program block) :
    List (Island dependencies) :=
  result.actions.map (fun node => ⟨program,block,node⟩) ++ result.obligations

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
    Nat × List (Position × Context) × List RuntimeContextRequest.Site ×
    List (Position × Context × Context) × List RuntimeProviderHeader.Request

private def reordered (roles : List Owner) (state : Raw.Observation.State) (bindings : Map) :
    WorkM (RuntimeOwnerMap.Checked roles state) := do
  let ordered ← RuntimeOwnerMap.order roles bindings
  RuntimeOwnerMap.check roles state ordered

private def singletonOrdinary (value : Value) : Bool := (ordinary value).all fun (basis,_) =>
  Semantics.FiniteCarrier.dimension basis == some 1

/-- One structural recursion checks whole functions and both authentic arm
blocks. Source scopes supply original outcomes; only the genuine Block supplies
native operations, scope and issuance history. No alternative body evaluator,
shortened program or invented signature is used for a branch. -/
def runBlock (artifact : Artifact) (root : Validity.Root) : Nat → Mode → OutputBoundary →
    {rootOwner rootName owner name : String} →
    SourceRuntimeScope.Subject artifact.sources owner name →
    RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name →
    (program : Semantics.Observation.Program) → Context → RuntimeStructuralAction.SourceState →
    RuntimeOrdinaryBody.State → (block : RuntimeInterval.Block root.dependencies program) →
    WorkM (BlockResult root.dependencies program block) :=
  Nat.rec (fun _ _ {_ _ _ _} _ _ _ _ _ _ _ => throw .limit)
    (fun _ next mode outputBoundary {rootOwner rootName owner name} source path program request initialHistory initialOrdinary block => do
      let dependencies := root.dependencies
      guard (!source.signature.operations.hasMeaningRequirements) .request
      match mode with
      | .pureBody =>
        guard (source.effect == .unitary && singletonOrdinary source.value &&
          source.parameterValues.all singletonOrdinary &&
          program.classicalInputs.isEmpty && program.classicalOutputs.isEmpty) .request
        let _ ← lift (readOption (Sector.pureOps block.operations))
        pure ()
      | .runtimeBody =>
        guard (SourceEffect.permits (some program.effect) source.effect) .request
      guard (initialHistory.nextOrdinal == source.initialOrdinal) .request
      let initial ← reordered source.initialRoles block.entry initialHistory.bindings
      let initialHistory := {initialHistory with bindings := initial.bindings}
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
          let initial : RuntimeStructuralAction.SourceState :=
            ⟨bindings,canonical,body.checked.summary.nextOwner⟩
          let checked ← next .pureBody .rootOrder (.whole body) (.root body)
            native.ir.original.program headerRequest.2 initial {} prepared.block
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
      let actuals ← if source.prefixRequired then
        RuntimeProviderHeaders.originalActuals source.signature.operations else pure []
      let (obligations,bodies) ← actuals.foldlM
        (fun (obligations,bodies) actual => do
          let (_,checked,rest) ← consumeOperation actual.2.graph (required actual.1.1) bodies
          pure (obligations ++ checked,rest)) ([],request.bodies)
      exactWork (Exact.charge (32*(source.events.length+request.positions.length+request.calls.length+1)^2))
      guard (request.positions.map (·.offset) == source.events.map SourceRuntimeContext.Event.offset) .request
      let advance : LoopState dependencies program block → Nat →
          WorkM (LoopState dependencies program block) :=
        fun (history,retired,ordinary,actions,steps,obligations,cursor,calls,sites,branches,bodies) start => do
          guard (cursor ≤ start) .request
          if cursor == start then
            return (history,retired,ordinary,actions,steps,obligations,cursor,calls,sites,branches,bodies)
          else
            let gap ← RuntimeOrdinaryBody.readGap block cursor (start-cursor) history ordinary
            return (history,retired,gap.ssa,actions,steps ++ [.gap gap],obligations,start,calls,sites,branches,bodies)
      let step : LoopState dependencies program block →
          (SourceRuntimeContext.Event artifact.sources owner × Position) →
            WorkM (LoopState dependencies program block) := fun state (event,position) => do
          let (history,retired,ordinary,actions,steps,obligations,_cursor,calls,sites,branches,bodies) ← advance state position.start
          let interval ← RuntimeInterval.check block position.start position.count
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
              let action ← RuntimeStructuralAction.read block position.start position.count event before
              let node : Node dependencies program block := .structural action
              return (action.after,retired ++ action.inputRoles,ordinary,actions ++ [node],steps ++ [.pure node],
                obligations,position.start+position.count,calls,sites,branches,bodies)
            else if observing then
              match mode with
              | .pureBody => throw .request
              | .runtimeBody =>
                let action ← RuntimeOrdinaryBody.readObservation path event block position before ordinary
                return (action.after,retired ++ action.retired,action.ordinary,actions,steps ++ [.observation action],
                  obligations,position.start+position.count,calls,sites,branches,bodies)
            else do
              let (after,node) ← primitiveAt interval history callerFrame (.primitive event)
              return (after,retired,ordinary,actions ++ [node],steps ++ [.pure node],
                obligations,position.start+position.count,calls,sites,branches,bodies)
          | .phase event =>
            let (after,node) ← primitiveAt interval history callerFrame (.phase event)
            return (after,retired,ordinary,actions ++ [node],steps ++ [.pure node],
              obligations,position.start+position.count,calls,sites,branches,bodies)
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
                let frame ← RuntimeCallInterval.read block position.start position.count (inputs.map (·.token))
                let inputOwners := (frame.selected.zip event.inputOwners).map fun (port,role) =>
                  (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)
                let childInitial ← RuntimeSourceBoundary.bindings childRoles inputOwners
                let childHistory : RuntimeStructuralAction.SourceState :=
                  ⟨childInitial,childRoles,original.checked.summary.nextOwner⟩
                let nested ← next .pureBody .localScope (.whole original) childPath frame.program child childHistory
                  ordinary frame.prepared.block
                let boundary ← RuntimeNamedBoundary.read frame.interval (inputs.map (·.token))
                  event before nested.history nested.retired original.checked.summary.value
                let node : Node dependencies program block := .named event frame original
                  (by with_reducible exact originalRead.property) frame.prepared.block boundary (Nodes.ofList nested.actions)
                return (boundary.after,retired ++ event.consumed,nested.ordinary,actions ++ [node],steps ++ [.pure node],
                  obligations ++ nested.obligations,position.start+position.count,calls,sites,branches,bodies)
              | .runtimeBody =>
                let frame ← RuntimeCallScope.read block position.start position.count
                  (inputs.map (·.token)) ordinary event.effect
                let inputOwners := (frame.selected.zip event.inputOwners).map fun (port,role) =>
                  (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)
                let childInitial ← RuntimeSourceBoundary.bindings childRoles inputOwners
                let childHistory : RuntimeStructuralAction.SourceState :=
                  ⟨childInitial,childRoles,original.checked.summary.nextOwner⟩
                let nested ← next .runtimeBody .localScope (.whole original) childPath frame.program child childHistory
                  frame.visible.ssa frame.prepared.block
                let boundary ← RuntimeNamedBoundary.read frame.interval (inputs.map (·.token))
                  event before nested.history nested.retired original.checked.summary.value
                let step : Step dependencies program block := .named event frame original
                  (by with_reducible exact originalRead.property) frame.prepared.block boundary nested.ordinary (Steps.ofList nested.steps)
                return (boundary.after,retired ++ event.consumed,nested.ordinary,actions,steps ++ [step],
                  obligations ++ nested.obligations,position.start+position.count,calls,sites,branches,bodies)
            else throw .request
          | .conditional event _ _ =>
            match mode with
            | .pureBody => throw .request
            | .runtimeBody =>
              let (branchPosition,thenContext,elseContext) :: branches := branches | throw .request
              guard (branchPosition == position && position.count == 1) .request
              let actualRead ← NaturalAffine.witness (RuntimeInterval.readBranch block position.start)
              let actual := actualRead.val
              let selected ← RuntimeBranchAction.readSource event
              if sameName : event.callerName = name then
                let thenSource : SourceRuntimeScope.Subject artifact.sources owner name :=
                  .arm event sameName selected.bodies selected.original true
                let elseSource : SourceRuntimeScope.Subject artifact.sources owner name :=
                  .arm event sameName selected.bodies selected.original false
                let left ← next .runtimeBody .frame thenSource path program thenContext before ordinary actual.thenBlock
                let right ← next .runtimeBody .frame elseSource path program elseContext before ordinary actual.elseBlock
                let action ← RuntimeBranchAction.read path event selected actual before left.history right.history
                  ordinary left.ordinary right.ordinary
                let branchStep : Step dependencies program block := .conditional path event selected actual
                  (by with_reducible exact actualRead.property) action (Steps.ofList left.steps) (Steps.ofList right.steps)
                return (action.next,retired ++ action.retired,action.ordinaryAfter,actions,steps ++ [branchStep],
                  obligations ++ left.islands ++ right.islands,position.start+position.count,calls,sites,branches,bodies)
              else throw .request
          | .operation event =>
            let owners ← readOwners
            guard (event.operation.graph.root.input == event.operation.graph.root.output &&
              event.allocated.isEmpty && event.consumed.isEmpty) .request
            let (callPosition,child) :: calls := calls | throw .request
            guard (callPosition == position && child.positions.isEmpty && child.sites.isEmpty &&
              child.calls.isEmpty && child.branches.isEmpty) .request
            let (expected,children) ← checkOperation event.operation.graph OperationAccess.applicable child.bodies
            let node ← operationNode block position event.inputOwners bindings owners.after.bindings expected
            pure (continuation owners,retired,ordinary,actions ++ [node],steps ++ [.pure node],
              obligations ++ children,position.start+position.count,calls,sites,branches,bodies)
          | .selection _ parsed _ selector target scope naturals .. =>
            let owners ← RuntimeOwnerTransition.read interval callerFrame.bindings
            let site :: sites := sites | throw .request
            guard (site.position == position) .request
            let table ← QuantumArms.readArmsWithInstantiation source.signature.original source.signature.instantiation
              source.signature.supply parsed.keyword.span.startByte selector.basis target.basis (some naturals) scope
            let (node,checked,bodies) ← selectionNode artifact interval callerFrame owners selector target table
              site (([] : List (Island dependencies)),bodies) fun _ arm (checked,bodies) => do
                let (logical,children,rest) ← consumeOperation arm.operation.graph OperationAccess.controllable bodies
                return (logical,checked ++ children,rest)
            pure ({before with bindings := owners.after.bindings},retired,ordinary,actions ++ [node],steps ++ [.pure node],
              obligations ++ checked,position.start+position.count,calls,sites,branches,bodies)
          | _ =>
            let _ ← readOwners
            throw .request
      let (history,retired,ordinary,actions,steps,obligations,cursor,calls,sites,branches,bodies) ←
        (source.events.zip request.positions).foldlM
        (fun state (event,position) => do
          match event with
          | .staticConditional event _ =>
            let sequence : RuntimeStaticPrimitive.Continuation event ← (match mode with
              | .pureBody => do
                  let source ← RuntimeStaticPrimitive.readSequence event
                  pure (.unchanged source)
              | .runtimeBody => RuntimeStaticPrimitive.readContinuation event)
            let state ← advance state position.start
            let (history,retired,ordinary,actions,steps,obligations,cursor,calls,sites,branches,bodies) := state
            let positions ← sequence.positions position (calls.map (·.1))
            guard (positions.length == sequence.selected.result.events.length) .request
            let interval ← RuntimeInterval.check block position.start position.count
            let bindings := (← reordered (history.bindings.map (·.owner)) interval.before history.bindings).bindings
            let before : RuntimeStructuralAction.SourceState := {history with bindings}
            let _ ← RuntimeStaticPrimitive.readContinuationBefore sequence interval before
            let count := sequence.selected.result.events.length
            -- The genuine shared fold appends the actual pure or mixed steps
            -- to the existing prefixes. Charge those copies and comparisons.
            exactWork (Exact.charge (32*(count+1)*(actions.length+steps.length+obligations.length+count+1)+
              32*(Raw.OwnerFlow.fields retired+1)))
            let initial : LoopState dependencies program block :=
              (before,retired,ordinary,actions,steps,obligations,cursor,calls,sites,branches,bodies)
            let result ← (sequence.selected.result.events.zip positions).foldlM step initial
            let (after,afterRetired,_ordinary,_actions,_steps,_obligations,afterCursor,_calls,_sites,_branches,_bodies) := result
            guard (afterCursor == position.start+position.count) .request
            let _ ← RuntimeStaticPrimitive.readContinuationAfter sequence interval before after retired afterRetired
            return result
          | _ => step state (event,position)) (initialHistory,([] : List Owner),initialOrdinary,
            ([] : List (Node dependencies program block)),([] : List (Step dependencies program block)),
            obligations,0,request.calls,request.sites,request.branches,bodies)
      guard (cursor ≤ block.operations.length && calls.isEmpty && sites.isEmpty && branches.isEmpty && bodies.isEmpty) .request
      let (ordinary,steps) ← if cursor == block.operations.length then pure (ordinary,steps) else do
        let gap ← RuntimeOrdinaryBody.readGap block cursor (block.operations.length-cursor) history ordinary
        pure (gap.ssa,steps ++ [.gap gap])
      guard (history.issued == initialHistory.issued ++ source.allocated && retired == source.consumed &&
        history.nextOrdinal == source.nextOrdinal) .request
      let final ← RuntimeInterval.check block block.operations.length 0
      match mode with
      | .pureBody => guard (!final.after.observe) .request
      | .runtimeBody => pure ()
      let bindings := (← reordered source.outputRoles final.after history.bindings).bindings
      let outputs ← rolePorts source.outputRoles bindings
      guard (match outputBoundary with
        | .rootOrder => outputs.map (·.token) == program.outputs
        | .localScope => decide ((outputs.map (·.token)).Perm program.outputs)
        | .frame => true) .request
      return ⟨{history with bindings},retired,actions,steps,ordinary,obligations⟩)

/-- Whole-body callers retain the same exact Body, Prepared object and public
run interface. The shared block walk also owns all recursive branch/call steps. -/
def run (artifact : Artifact) (root : Validity.Root) (fuel : Nat) (mode : Mode) (outputBoundary : OutputBoundary)
    {rootOwner rootName owner name : String}
    {signature : SourceRuntimeContext.Signature artifact.sources owner name}
    (body : SourceRuntimeTrace.Body signature)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name)
    (program : Semantics.Observation.Program) (request : Context) (initial : Map)
    (ordinary : RuntimeOrdinaryBody.State) (prepared : RuntimeInterval.Prepared root.dependencies program) :
    WorkM (Result root.dependencies program) := do
  let initialHistory : RuntimeStructuralAction.SourceState :=
    ⟨initial,body.checked.summary.parameterValues.flatMap valueOwners,body.checked.summary.nextOwner⟩
  let result ← runBlock artifact root fuel mode outputBoundary (.whole body) path program request initialHistory
    ordinary prepared.block
  return ⟨prepared,result.history,result.retired,result.actions,result.steps,result.ordinary,result.obligations⟩

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
