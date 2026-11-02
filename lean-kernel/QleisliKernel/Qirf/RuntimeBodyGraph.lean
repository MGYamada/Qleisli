import QleisliKernel.Qirf.RuntimeBodyDiscovery
import QleisliKernel.Qirf.RuntimePureBody
import QleisliKernel.Qirf.RuntimePureComposition
import QleisliKernel.Qirf.RuntimeStructuredRoot

/-! Connect original discovery, local body checks and the same typed root.
The original catalogue/signature/body are read before the sole fresh graph.
All continuations retain those objects and that graph's dependencies. This
preparation does not issue a handle: full structural code/action composition,
ordinary instruments and outstanding scoped obligations remain required.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeBodyGraph
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
abbrev Context := RuntimeContextRequest.Context

structure Prepared (artifact : Artifact) (order : Array Nat) (owner name : String)
    (arguments : StaticTypes.Arguments) (request : Context) (runtime : RuntimeFamily.Request) where
  headers : RuntimeBodyDiscovery.Headers artifact owner name arguments request
  fresh : RuntimeBodyDiscovery.Fresh order headers
  rootBody : RuntimeInterval.Prepared fresh.root.dependencies fresh.root.program
  inputs : RuntimeSourceBoundary.Inputs headers.source.body rootBody runtime.inputStorage
  derivation : RuntimePureBody.Checked artifact fresh.root headers.source.body fresh.root.program request inputs.owners.bindings
  structural : RuntimePureComposition.Prepared artifact fresh.root headers.source.body request inputs.owners.bindings derivation
  boundary : RuntimeStructuredRoot.Boundary headers.source.body fresh.root rootBody runtime

/-- Forward-only pure contexts use the same actual typed runtime request.
Unsupported local source forms refuse in the recursive checker; no dense-root
fallback or earlier runtime handle can replace its remaining obligations. -/
def prepare (artifact : Artifact) (order : Array Nat) (owner name : String)
    (arguments : StaticTypes.Arguments) (request : Context) (runtime : RuntimeFamily.Request) :
    WorkM (Prepared artifact order owner name arguments request runtime) := do
  exactWork (Exact.charge (16*(owner.utf8ByteSize+name.utf8ByteSize+
    runtime.moduleName.utf8ByteSize+runtime.declarationName.utf8ByteSize+1)))
  guard (runtime.moduleName == owner && runtime.declarationName == name && runtime.staticArguments == arguments) .request
  let headers ← RuntimeBodyDiscovery.readHeaders artifact owner name arguments request
  let fresh ← RuntimeBodyDiscovery.prepare order headers
  let rootBody ← RuntimeInterval.prepare fresh.root.dependencies fresh.root.program
  let inputs ← RuntimeSourceBoundary.readInputs headers.source.body rootBody runtime.inputStorage
  let derivation ← RuntimePureBody.checkPrepared artifact fresh.root headers.source.body fresh.root.program request
    inputs.owners.bindings rootBody
  let structural ← RuntimePureComposition.prepare artifact fresh.root headers.source.body request inputs.owners.bindings derivation
  let boundary ← RuntimeStructuredRoot.readBoundary headers.source.body fresh.root rootBody derivation.result.bindings runtime
  return ⟨headers,fresh,rootBody,inputs,derivation,structural,boundary⟩

theorem Prepared.oneFreshRoot {artifact order owner name arguments request runtime}
    (prepared : Prepared artifact order owner name arguments request runtime) :
    RuntimeInterval.Computed
      (Validity.checkRootFromRoots artifact order prepared.headers.discovered.rows prepared.headers.roots)
      prepared.fresh.root := prepared.fresh.checked

end QleisliKernel.Qirf.RuntimeBodyGraph
