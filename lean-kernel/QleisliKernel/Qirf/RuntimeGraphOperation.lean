import QleisliKernel.Qirf.RuntimeProviderHeaders
import QleisliKernel.SourceTypes.OperationAccess

/-! Typed continuations for the common original runtime traversal.
Every request retains its actual graph, demanded paths and ordered provider and
Meaning slots. The concrete enclosing reader fixes the evidence family and its
executable reader; untrusted request data cannot select one. These continuations
issue no handle and do not close the all-original source duty queue.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeGraphOperation
open QleisliKernel Finite SourceTypes
abbrev BodyRequest := RuntimeProviderHeader.Request

structure Request (artifact : Artifact) where
  context : StaticOperation.Context
  description : OperationDescription.Description
  graph : StaticOperation.CheckedGraph artifact.sources context description
  requested : StaticOperation.Paths
  implementations : List BodyRequest
  references : List (List BodyRequest)

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
  evidence : continuation.Evidence request
  consumed : RuntimeInterval.Computed (continuation.read request) evidence

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
