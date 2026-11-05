import QleisliKernel.Qirf.RuntimeBodyDiscovery
import QleisliKernel.Qirf.RuntimePureBody
import QleisliKernel.Qirf.RuntimePureComposition
import QleisliKernel.Qirf.RuntimeStructuredRoot
import QleisliKernel.Qirf.RuntimeOrdinaryHistories

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

structure RuntimePrepared (artifact : Artifact) (order : Array Nat) (owner name : String)
    (arguments : StaticTypes.Arguments) (request : Context) (runtime : RuntimeFamily.Request) where
  headers : RuntimeBodyDiscovery.Headers artifact owner name arguments request
  fresh : RuntimeBodyDiscovery.Fresh order headers
  rootBody : RuntimeInterval.Prepared fresh.root.dependencies fresh.root.program
  inputs : RuntimeSourceBoundary.Inputs headers.source.body rootBody runtime.inputStorage
  initial : RuntimeOrdinaryInputs.Checked headers.source.body rootBody runtime inputs
  derivation : RuntimePureBody.RuntimeChecked artifact fresh.root headers.source.body request runtime rootBody inputs initial
  owners : RuntimeOwnerMap.Checked
    (SourceRuntimeValues.valueOwners (RuntimeSourceBoundary.summary headers.source.body).value) rootBody.whole.state
  outputs : RuntimeSourceBoundary.Outputs (RuntimeSourceBoundary.summary headers.source.body).value
    rootBody.whole.state owners runtime.storage fresh.root.program.outputs
  ordinary : RuntimeOrdinaryHistories.Checked initial derivation.result.ordinary outputs
  boundary : RuntimeStructuredRoot.Boundary headers.source.body fresh.root rootBody runtime

/-- The mixed preparation closes complete ordinary inputs, actual hidden
histories and final storage through the single event loop and one fresh graph.
The same original root remains the quantum/code/instrument composition subject;
this preparation does not replace those obligations or issue a handle. -/
def prepareRuntime (artifact : Artifact) (order : Array Nat) (owner name : String)
    (arguments : StaticTypes.Arguments) (request : Context) (runtime : RuntimeFamily.Request) :
    WorkM (RuntimePrepared artifact order owner name arguments request runtime) := do
  exactWork (Exact.charge (16*(owner.utf8ByteSize+name.utf8ByteSize+
    runtime.moduleName.utf8ByteSize+runtime.declarationName.utf8ByteSize+1)))
  guard (runtime.moduleName == owner && runtime.declarationName == name && runtime.staticArguments == arguments) .request
  let headers ← RuntimeBodyDiscovery.readHeaders artifact owner name arguments request
  let fresh ← RuntimeBodyDiscovery.prepare order headers
  let rootBody ← RuntimeInterval.prepare fresh.root.dependencies fresh.root.program
  let inputs ← RuntimeSourceBoundary.readInputs headers.source.body rootBody runtime.inputStorage
  let initial ← RuntimeOrdinaryInputs.read headers.source.body rootBody runtime inputs
  let derivation ← RuntimePureBody.checkRuntime artifact fresh.root headers.source.body request runtime rootBody inputs initial
  let owners ← RuntimeOwnerMap.check
    (SourceRuntimeValues.valueOwners (RuntimeSourceBoundary.summary headers.source.body).value)
    rootBody.whole.state derivation.result.bindings
  let outputs ← RuntimeSourceBoundary.checkOutputs headers.source.body rootBody.whole.state owners
    runtime.storage fresh.root.program.outputs
  let ordinary ← RuntimeOrdinaryHistories.read initial derivation.result.ordinary outputs
  let boundary ← RuntimeStructuredRoot.readBoundary headers.source.body fresh.root rootBody derivation.result.bindings runtime
  return ⟨headers,fresh,rootBody,inputs,initial,derivation,owners,outputs,ordinary,boundary⟩

theorem RuntimePrepared.oneFreshRoot {artifact order owner name arguments request runtime}
    (prepared : RuntimePrepared artifact order owner name arguments request runtime) :
    RuntimeInterval.Computed
      (Validity.checkRootFromRoots artifact order prepared.headers.discovered.rows prepared.headers.roots)
      prepared.fresh.root := prepared.fresh.checked

end QleisliKernel.Qirf.RuntimeBodyGraph
