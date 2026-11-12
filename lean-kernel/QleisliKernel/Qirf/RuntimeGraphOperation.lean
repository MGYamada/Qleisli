import QleisliKernel.Qirf.RuntimeProviderHeaders
import QleisliKernel.Qirf.RuntimeOrdinaryBody
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

/-- Arms and operation applications retain their original source and exact
graph. Unlocated requests supply no original assertion coverage. -/
inductive Origin {sources : Sources} : {context : StaticOperation.Context} →
    {description : OperationDescription.Description} →
    StaticOperation.CheckedGraph sources context description → Type where
  | unlocated {context description} {graph : StaticOperation.CheckedGraph sources context description} : Origin graph
  | arm {owner tokens} (operation : QuantumArms.Operation sources owner tokens) : Origin operation.graph
  | application {owner} (event : SourceOperationApplication.Event sources owner) : Origin event.operation.graph

def Origin.isApplication {sources context description graph}
    (origin : @Origin sources context description graph) : Bool :=
  match origin with
  | .application _ => true
  | _ => false

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

/-- Capture the actual source call chain at graph consumption. Every named
edge retains its event, supplied arguments and successful callee body read. -/
structure Location {artifact : Artifact} (request : Request artifact) where
  rootOwner : String
  rootName : String
  owner : String
  name : String
  path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name
  site : Site owner name request.origin

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
