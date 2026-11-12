import QleisliKernel.Qirf.RuntimeProviderHeaders
import QleisliKernel.Qirf.RuntimeOrdinaryBody
import QleisliKernel.Qirf.RuntimeStructuredRoot
import QleisliKernel.SourceTypes.OperationAccess
import QleisliKernel.SourceTypes.QuantumArms
import QleisliKernel.SourceTypes.SourceOperationApplication

/-! Typed continuations for the common original runtime traversal.
Every request retains its actual graph, demanded paths and ordered provider and
Meaning slots. The concrete enclosing reader fixes the evidence family and its
executable reader; untrusted request data cannot select one. These continuations
issue no handle and do not close the all-original source duty queue.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeGraphOperation
open QleisliKernel Finite SourceTypes
abbrev BodyRequest := RuntimeProviderHeader.Request

def suppliedActual {sources caller} (event : SourceRuntimeContext.NamedEvent sources caller)
    (index : Fin event.target.operationActuals.sourceActuals.length) :=
  event.target.operationActuals.sourceActuals[index].native

/-- Every located graph keeps its exact original occurrence. Unlocated
requests supply no original assertion coverage. -/
inductive Origin {sources : Sources} : {context : StaticOperation.Context} →
    {description : OperationDescription.Description} →
    StaticOperation.CheckedGraph sources context description → Type where
  | unlocated {context description} {graph : StaticOperation.CheckedGraph sources context description} : Origin graph
  | arm {owner tokens} (operation : QuantumArms.Operation sources owner tokens) : Origin operation.graph
  | application {owner} (event : SourceOperationApplication.Event sources owner) : Origin event.operation.graph
  | supplying {caller} (event : SourceRuntimeContext.NamedEvent sources caller)
      (index : Fin event.target.operationActuals.sourceActuals.length) : Origin (suppliedActual event index).2.graph

def Origin.isStandaloneMeaning {sources context description graph}
    (origin : @Origin sources context description graph) : Bool :=
  match origin with
  | .application _ | .supplying .. => true
  | _ => false

def Origin.isSupplying {sources context description graph}
    (origin : @Origin sources context description graph) : Bool :=
  match origin with
  | .supplying .. => true
  | _ => false

inductive Incoming (sources : Sources) : {owner name : String} →
    SourceRuntimeContext.Signature sources owner name → Type where
  | named {caller} (event : SourceRuntimeContext.NamedEvent sources caller)
      {signature : SourceRuntimeContext.Signature sources event.target.resolution.moduleName event.target.resolution.declaration.name}
      (original : signature = event.target.signature) : Incoming sources signature

private def originalSupplying {sources caller} (event : SourceRuntimeContext.NamedEvent sources caller)
    (actual : Sigma (StaticOperation.Actual sources (.source caller)))
    (present : actual ∈ event.target.operationActuals.sourceActuals.map SourceOperation.ActualSource.native) :
    WorkM (Origin actual.2.graph) := do
  let slots := event.target.operationActuals.sourceActuals
  let names := slots.map (·.name)
  let slotName := fun index : Fin slots.length => slots[index].name
  exactWork (Exact.charge (16*((names.map String.utf8ByteSize).sum+
    (slots.length+1)*(slots.length+actual.1.1.utf8ByteSize+1))))
  match found : (List.finRange slots.length).filter (fun index => slotName index == actual.1.1) with
  | [index] =>
    have same : suppliedActual event index = actual := by
      obtain ⟨source,atSlot,projected⟩ := List.mem_map.mp present
      obtain ⟨i,valid,original⟩ := List.mem_iff_getElem.mp atSlot
      let other : Fin slots.length := ⟨i,valid⟩
      have exactActual : suppliedActual event other = actual :=
        (congrArg SourceOperation.ActualSource.native original).trans projected
      have sameName : (slotName other == actual.1.1) = true :=
        beq_iff_eq.mpr (congrArg (fun slot => slot.1.1) exactActual)
      have member : other ∈ (List.finRange slots.length).filter (fun i => slotName i == actual.1.1) :=
        List.mem_filter.mpr ⟨List.mem_finRange other,sameName⟩
      have identical : other = index := by simpa only [found,List.mem_singleton] using member
      simpa only [identical] using exactActual
    return same ▸ Origin.supplying event index
  | _ => throw .request

private def supplyingFromContext {sources caller context} (event : SourceRuntimeContext.NamedEvent sources caller)
    (actuals : List (Sigma (StaticOperation.Actual sources context)))
    (sameContext : context = .source caller)
    (sameActuals : HEq actuals (event.target.operationActuals.sourceActuals.map SourceOperation.ActualSource.native))
    (actual : Sigma (StaticOperation.Actual sources context)) (present : actual ∈ actuals) :
    WorkM (Origin actual.2.graph) := by
  subst context
  exact originalSupplying event actual ((eq_of_heq sameActuals) ▸ present)

/-- Retain the same argument occurrence as the checked callee header. The
formal's name selects the unique original slot, including unused suppliers. -/
def Incoming.origin {sources owner name} {signature : SourceRuntimeContext.Signature sources owner name}
    (incoming : Incoming sources signature)
    (actual : Sigma (StaticOperation.Actual sources signature.context))
    (present : actual ∈ signature.operations.actuals) : WorkM (Origin actual.2.graph) := by
  cases incoming with
  | @named caller event signature original =>
    subst signature
    exact supplyingFromContext event _ event.target.supplierContext event.target.originalOperationActuals actual present

structure Request (artifact : Artifact) where
  context : StaticOperation.Context
  description : OperationDescription.Description
  graph : StaticOperation.CheckedGraph artifact.sources context description
  requested : StaticOperation.Paths
  implementations : List BodyRequest
  references : List (List BodyRequest)
  origin : Origin graph

/-- An arm belongs to the table of the current function at this exact index.
Other graph requests retain their invocation without a local arm site. -/
inductive Site {sources : Sources} (owner name : String) :
    {context : StaticOperation.Context} → {description : OperationDescription.Description} →
    {graph : StaticOperation.CheckedGraph sources context description} → Origin graph → Type where
  | unlocated {context description} {graph : StaticOperation.CheckedGraph sources context description} :
      Site owner name (.unlocated (graph := graph))
  | arm {offset selector target} (table : QuantumArms.Table sources owner name offset selector target)
      (index : Fin table.arms.length) : Site owner name (.arm (table.arms[index]).operation)
  | application (event : SourceOperationApplication.Event sources owner) (caller : event.callerName = name) :
      Site owner name (.application event)
  | supplying (event : SourceRuntimeContext.NamedEvent sources owner)
      (index : Fin event.target.operationActuals.sourceActuals.length) (caller : event.target.callerName = name) :
      Site owner name (.supplying event index)

/-- Capture the actual source call chain at graph consumption. Every named
edge retains its event, supplied arguments and successful callee body read. -/
structure Location {artifact : Artifact} (request : Request artifact) where
  rootOwner : String
  rootName : String
  owner : String
  name : String
  path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name
  site : Site owner name request.origin

abbrev LocatedSite {sources rootOwner rootName context description}
    {graph : StaticOperation.CheckedGraph sources context description} (origin : Origin graph) :=
  Σ owner : String, Σ name : String,
    RuntimeOrdinaryBody.CallPath sources rootOwner rootName owner name × Site owner name origin

/-- A supplying assertion is written in the parent, even though its graph
is consumed in the child's prefix. Bind it to that original parent path. -/
def prefixSite {sources rootOwner rootName owner name context description}
    {graph : StaticOperation.CheckedGraph sources context description} (origin : Origin graph)
    (path : RuntimeOrdinaryBody.CallPath sources rootOwner rootName owner name) :
    WorkM (LocatedSite (rootOwner := rootOwner) (rootName := rootName) origin) := do
  match origin with
  | .unlocated => return ⟨owner,name,path,.unlocated⟩
  | .supplying (caller := caller) event index =>
    match path with
    | .root _ => throw .request
    | .named (caller := actualCaller) active _ _ parent =>
      let callerArguments := active.target.callerSignature.arguments
      let writtenArguments := event.target.callerSignature.arguments
      let activeArguments := active.target.signature.arguments
      let suppliedArguments := event.target.signature.arguments
      exactWork (Exact.charge (16*(SourceTrace.Meter.tokenFields (active.tokens ++ event.tokens)+
        SourceTrace.Meter.nameFields (active.scope ++ event.scope)+
        RuntimeStructuredRoot.argumentFields callerArguments+RuntimeStructuredRoot.argumentFields writtenArguments+
        RuntimeStructuredRoot.argumentFields activeArguments+RuntimeStructuredRoot.argumentFields suppliedArguments+
        actualCaller.utf8ByteSize+caller.utf8ByteSize+active.target.callerName.utf8ByteSize+
        event.target.callerName.utf8ByteSize+owner.utf8ByteSize+name.utf8ByteSize+1)))
      if sameOwner : actualCaller = caller then
        if sameName : active.target.callerName = event.target.callerName then
          guard (active.call.calleeOffset == event.call.calleeOffset && active.tokens == event.tokens &&
            active.scope == event.scope && active.target.resolution.moduleName == event.target.resolution.moduleName &&
            active.target.resolution.declaration.name == event.target.resolution.declaration.name &&
            callerArguments == writtenArguments && activeArguments == suppliedArguments) .request
          let writtenPath : RuntimeOrdinaryBody.CallPath sources rootOwner rootName caller event.target.callerName :=
            sameName ▸ (sameOwner ▸ parent)
          return ⟨caller,event.target.callerName,writtenPath,.supplying event index rfl⟩
        else throw .request
      else throw .request
  | _ => throw .request

structure Preparation (artifact : Artifact) where
  Evidence : Request artifact → Type
  read : (request : Request artifact) → WorkM (Evidence request)
  rows : {request : Request artifact} → Evidence request → List SourceRows.Row
  roots : {request : Request artifact} → Evidence request → List Nat

structure PreparedReceipt {artifact} (continuation : Preparation artifact) where
  request : Request artifact
  evidence : continuation.Evidence request
  consumed : RuntimeInterval.Computed (continuation.read request) evidence

structure Consumption (artifact : Artifact) (root : Validity.Root) (Obligation : Type) where
  Evidence : Request artifact → Type
  read : (request : Request artifact) → WorkM (Evidence request)
  action : {request : Request artifact} → Evidence request → Semantics.Exact.Matrix
  obligations : {request : Request artifact} → Evidence request → List Obligation

structure CheckedReceipt {artifact root Obligation}
    (continuation : Consumption artifact root Obligation) where
  request : Request artifact
  location : Location request
  evidence : continuation.Evidence request
  consumed : RuntimeInterval.Computed (continuation.read request) evidence

/-- The exact source-preparation value is an index of the final-root reader.
No descriptor comparison or graph transport selects a prepared value. -/
structure StagedConsumption {artifact : Artifact} (preparation : Preparation artifact)
    (root : Validity.Root) (Obligation : Type) where
  Evidence : (request : Request artifact) → preparation.Evidence request → Type
  read : (request : Request artifact) → (prepared : preparation.Evidence request) →
    WorkM (Evidence request prepared)
  action : {request : Request artifact} → {prepared : preparation.Evidence request} →
    Evidence request prepared → Semantics.Exact.Matrix
  obligations : {request : Request artifact} → {prepared : preparation.Evidence request} →
    Evidence request prepared → List Obligation

structure StagedReceipt {artifact preparation root Obligation}
    (continuation : @StagedConsumption artifact preparation root Obligation) where
  request : Request artifact
  location : Location request
  prepared : preparation.Evidence request
  preparedRead : RuntimeInterval.Computed (preparation.read request) prepared
  evidence : continuation.Evidence request prepared
  consumed : RuntimeInterval.Computed (continuation.read request prepared) evidence

/-- Prefix access follows the original mixed header, including unused actuals.
Available capabilities do not sharpen a written formal's demands. -/
def required {sources owner name} (signature : SourceRuntimeContext.Signature sources owner name)
    (argument : String) : StaticOperation.Paths :=
  match signature.instantiation with
  | .closed _ => OperationAccess.empty
  | .static _ environment _ =>
    ⟨environment.numeric.original.header.access.contains (.applicable,argument),
      environment.numeric.original.header.access.contains (.adjointable,argument),
      environment.numeric.original.header.access.contains (.controllable,argument)⟩

end QleisliKernel.Qirf.RuntimeGraphOperation
