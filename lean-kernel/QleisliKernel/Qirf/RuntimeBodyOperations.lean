import QleisliKernel.Qirf.RuntimeOperationTree
import QleisliKernel.Qirf.RuntimeStructuredRoot
import QleisliKernel.Qirf.RuntimeOrdinaryHistories
import QleisliKernel.Qirf.RuntimeReferenceContexts

/-! Original graph/Meaning continuations of the common mixed body loop.
The exact graph preparations precede one fresh native root. Every subsequent
operation uses that root's original provider/body/access/Meaning readers; the
common loop still checks actual selection frames, source calls, observations,
ordinary SSA, complete hidden histories and the typed return, including Unit
owners. The complete original pending duty queue remains explicit. This is a
component preparation, not global source acceptance, a composition theorem,
an execution handle or a public v5 dispatcher.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeBodyOperations
open QleisliKernel Finite SourceTypes
abbrev Context := RuntimeContextRequest.Context

def preparation (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources) :
    RuntimeGraphOperation.Preparation artifact where
  Evidence call := RuntimePreparedOperation.GraphPrepared artifact catalogue call.graph
    call.implementations call.references
  read call := RuntimePreparedOperation.prepareGraph artifact catalogue call.graph call.implementations call.references
  rows checked := checked.rows
  roots checked := checked.roots

/-- A returned action is a projection of the actual checked original tree.
The computation witnesses retain every occurrence and Meaning equation, rather
than a supplied matrix or a producer assertion that checking succeeded. -/
structure Operation (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) (call : RuntimeGraphOperation.Request artifact) where
  prepared : RuntimePreparedOperation.GraphPrepared artifact catalogue call.graph call.implementations call.references
  preparationRead : RuntimeInterval.Computed
    (RuntimePreparedOperation.prepareGraph artifact catalogue call.graph call.implementations call.references) prepared
  checked : RuntimeOperationTree.Checked prepared root call.requested
  checkedRead : RuntimeInterval.Computed (RuntimeOperationTree.read prepared root call.requested) checked

def readOperation (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) (call : RuntimeGraphOperation.Request artifact) : WorkM (Operation artifact catalogue root call) := do
  let prepared ← NaturalAffine.witness
    (RuntimePreparedOperation.prepareGraph artifact catalogue call.graph call.implementations call.references)
  let checked ← NaturalAffine.witness (RuntimeOperationTree.read prepared.val root call.requested)
  return ⟨prepared.val,by with_reducible exact prepared.property,
    checked.val,by with_reducible exact checked.property⟩

/-- Provider body islands are retained as ordinary composition obligations.
Meaning-reference computations remain on the same operation receipt; this
projection is not a claim to enumerate or discharge all semantic obligations. -/
def Operation.providerIslands {artifact catalogue root call}
    (operation : Operation artifact catalogue root call) : List (RuntimePureBody.Island root.dependencies) :=
  operation.checked.providerIslands

def consumption (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources) (root : Validity.Root) :
    RuntimeGraphOperation.Consumption artifact root (RuntimePureBody.Island root.dependencies) where
  Evidence call := Operation artifact catalogue root call
  read call := readOperation artifact catalogue root call
  action operation := operation.checked.action
  obligations operation := operation.providerIslands

/-- The source-prepared graph is an exact index, not selected by comparing a
descriptor or recovering an untyped receipt from a list. Its native tree is
checked freshly under the enclosing root. -/
structure StagedOperation (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) (call : RuntimeGraphOperation.Request artifact)
    (prepared : RuntimePreparedOperation.GraphPrepared artifact catalogue call.graph call.implementations call.references) where
  checked : RuntimeOperationTree.Checked prepared root call.requested
  checkedRead : RuntimeInterval.Computed (RuntimeOperationTree.read prepared root call.requested) checked

def stagedConsumption (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) : RuntimeGraphOperation.StagedConsumption (preparation artifact catalogue)
      root (RuntimePureBody.Island root.dependencies) where
  Evidence call prepared := StagedOperation artifact catalogue root call prepared
  read call prepared := do
    let checked ← NaturalAffine.witness (RuntimeOperationTree.read prepared root call.requested)
    return ⟨checked.val,by with_reducible exact checked.property⟩
  action operation := operation.checked.action
  obligations operation := operation.checked.providerIslands

structure Prepared (artifact : Artifact) (owner name : String) (arguments : StaticTypes.Arguments)
    (request : Context) where
  source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments
  referenceContexts : RuntimeInterval.Computed (RuntimeReferenceContexts.runtime 129 request) ()
  planned : RuntimeBodyDiscovery.Planned (preparation artifact source.catalogue) (.whole source.body) request
  relevance : SourceRows.Retained ([(owner,source.signature.original.source)] ++ planned.discovery.rows)

def Prepared.discovery {artifact owner name arguments request}
    (prepared : Prepared artifact owner name arguments request) : RuntimeBodyDiscovery.Discovery :=
  prepared.planned.discovery

def Prepared.receipts {artifact owner name arguments request}
    (prepared : Prepared artifact owner name arguments request) :
    List (RuntimeGraphOperation.PreparedReceipt (preparation artifact prepared.source.catalogue)) :=
  prepared.planned.receipts

def Prepared.rows {artifact owner name arguments request}
    (prepared : Prepared artifact owner name arguments request) : List SourceRows.Row := prepared.relevance.rows

def Prepared.roots {artifact owner name arguments request}
    (prepared : Prepared artifact owner name arguments request) : List Nat :=
  (artifact.root :: prepared.discovery.roots).eraseDups

/-- Source preparation preserves every original pending assessment. A concrete
Meaning duty is not erased merely because this selected component can read its
local equation. No strict Source or all-original Checked is manufactured. -/
def prepare (artifact : Artifact) (owner name : String) (arguments : StaticTypes.Arguments) (request : Context) :
    WorkM (Prepared artifact owner name arguments request) := do
  let source ← RuntimeBodyDiscovery.prepareSource artifact owner name arguments
  let references ← NaturalAffine.witness (RuntimeReferenceContexts.runtime 129 request)
  have unit : references.val = () := by cases references.val; rfl
  let planned ← RuntimeBodyDiscovery.visitPlanned (preparation artifact source.catalogue) (.whole source.body) request
  let relevance ← SourceRows.read ([(owner,source.signature.original.source)] ++ planned.discovery.rows)
  return ⟨source,by with_reducible simpa only [unit] using references.property,planned,relevance⟩

def initialHistory {artifact owner name arguments request}
    (prepared : Prepared artifact owner name arguments request) {root : Validity.Root}
    (native : RuntimeInterval.Prepared root.dependencies root.program) (runtime : RuntimeFamily.Request)
    (inputs : RuntimeSourceBoundary.Inputs prepared.source.body native runtime.inputStorage) :
    RuntimeStructuralAction.SourceState :=
  ⟨inputs.owners.bindings,prepared.source.body.checked.summary.parameterValues.flatMap SourceRuntimeValues.valueOwners,
    prepared.source.body.checked.summary.nextOwner⟩

structure AtRoot {artifact owner name arguments request}
    (prepared : Prepared artifact owner name arguments request) (root : Validity.Root) (runtime : RuntimeFamily.Request) where
  selection : runtime.moduleName = owner ∧ runtime.declarationName = name ∧ runtime.staticArguments = arguments
  native : RuntimeInterval.Prepared root.dependencies root.program
  nativeRead : RuntimeInterval.Computed (RuntimeInterval.prepare root.dependencies root.program) native
  inputs : RuntimeSourceBoundary.Inputs prepared.source.body native runtime.inputStorage
  inputsRead : RuntimeInterval.Computed
    (RuntimeSourceBoundary.readInputs prepared.source.body native runtime.inputStorage) inputs
  initial : RuntimeOrdinaryInputs.Checked prepared.source.body native runtime inputs
  initialRead : RuntimeInterval.Computed (RuntimeOrdinaryInputs.read prepared.source.body native runtime inputs) initial
  result : RuntimePureBody.BlockResult root.dependencies root.program native.block
  receipts : List (RuntimeGraphOperation.StagedReceipt (stagedConsumption artifact prepared.source.catalogue root))
  traversed : RuntimeInterval.Computed
    (RuntimePureBody.runBlockPlanned artifact root (preparation artifact prepared.source.catalogue)
      (stagedConsumption artifact prepared.source.catalogue root)
      128 .runtimeBody .rootOrder (.whole prepared.source.body) (.root prepared.source.body) root.program request prepared.planned.plan
      (initialHistory prepared native runtime inputs) initial.ssa native.block) (result,receipts)
  owners : RuntimeOwnerMap.Checked (SourceRuntimeValues.valueOwners (RuntimeSourceBoundary.summary prepared.source.body).value)
    native.whole.state
  ownersRead : RuntimeInterval.Computed
    (RuntimeOwnerMap.check (SourceRuntimeValues.valueOwners (RuntimeSourceBoundary.summary prepared.source.body).value)
      native.whole.state result.history.bindings) owners
  outputs : RuntimeSourceBoundary.Outputs (RuntimeSourceBoundary.summary prepared.source.body).value native.whole.state owners
    runtime.storage root.program.outputs
  outputsRead : RuntimeInterval.Computed
    (RuntimeSourceBoundary.checkOutputs prepared.source.body native.whole.state owners runtime.storage root.program.outputs) outputs
  ordinary : RuntimeOrdinaryHistories.Checked initial result.ordinary outputs
  ordinaryRead : RuntimeInterval.Computed (RuntimeOrdinaryHistories.read initial result.ordinary outputs) ordinary
  boundary : RuntimeStructuredRoot.Boundary prepared.source.body root native runtime
  boundaryRead : RuntimeInterval.Computed
    (RuntimeStructuredRoot.readBoundary prepared.source.body root native result.history.bindings runtime) boundary

def readAt {artifact owner name arguments request}
    (prepared : Prepared artifact owner name arguments request) (root : Validity.Root) (runtime : RuntimeFamily.Request) :
    WorkM (AtRoot prepared root runtime) := do
  exactWork (Exact.charge (16*(owner.utf8ByteSize+name.utf8ByteSize+
    runtime.moduleName.utf8ByteSize+runtime.declarationName.utf8ByteSize+1)))
  if selection : runtime.moduleName = owner ∧ runtime.declarationName = name ∧ runtime.staticArguments = arguments then
    let native ← NaturalAffine.witness (RuntimeInterval.prepare root.dependencies root.program)
    let inputs ← NaturalAffine.witness (RuntimeSourceBoundary.readInputs prepared.source.body native.val runtime.inputStorage)
    let initial ← NaturalAffine.witness (RuntimeOrdinaryInputs.read prepared.source.body native.val runtime inputs.val)
    let checked ← NaturalAffine.witness
      (RuntimePureBody.runBlockPlanned artifact root (preparation artifact prepared.source.catalogue)
      (stagedConsumption artifact prepared.source.catalogue root)
        128 .runtimeBody .rootOrder (.whole prepared.source.body) (.root prepared.source.body) root.program request prepared.planned.plan
        (initialHistory prepared native.val runtime inputs.val) initial.val.ssa native.val.block)
    let result := checked.val.1
    let owners ← NaturalAffine.witness (RuntimeOwnerMap.check
      (SourceRuntimeValues.valueOwners (RuntimeSourceBoundary.summary prepared.source.body).value) native.val.whole.state result.history.bindings)
    let outputs ← NaturalAffine.witness (RuntimeSourceBoundary.checkOutputs prepared.source.body native.val.whole.state
      owners.val runtime.storage root.program.outputs)
    let ordinary ← NaturalAffine.witness (RuntimeOrdinaryHistories.read initial.val result.ordinary outputs.val)
    let boundary ← NaturalAffine.witness
      (RuntimeStructuredRoot.readBoundary prepared.source.body root native.val result.history.bindings runtime)
    return ⟨selection,native.val,by with_reducible exact native.property,
      inputs.val,by with_reducible exact inputs.property,initial.val,by with_reducible exact initial.property,
      result,checked.val.2,by with_reducible exact checked.property,owners.val,by with_reducible exact owners.property,
      outputs.val,by with_reducible exact outputs.property,ordinary.val,by with_reducible exact ordinary.property,
      boundary.val,by with_reducible exact boundary.property⟩
  else throw .request

structure Checked {artifact owner name arguments request}
    (prepared : Prepared artifact owner name arguments request) (order : Array Nat) (runtime : RuntimeFamily.Request) where
  root : Validity.Root
  fresh : RuntimeInterval.Computed (Validity.checkRootFromRoots artifact order prepared.rows prepared.roots .qmatch) root
  checked : AtRoot prepared root runtime
  consumed : RuntimeInterval.Computed (readAt prepared root runtime) checked

/-- Exactly one fresh full graph follows discovery. The typed original body,
all local graph receipts and ordinary histories consume that same root. -/
def read {artifact owner name arguments request}
    (prepared : Prepared artifact owner name arguments request) (order : Array Nat) (runtime : RuntimeFamily.Request) :
    WorkM (Checked prepared order runtime) := do
  let bytes := (artifact.sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
  exactWork (Exact.charge (8+(bytes+artifact.sources.size+1)*(prepared.rows.length+1)+
    16*(prepared.roots.length+1)^2))
  let root ← NaturalAffine.witness (Validity.checkRootFromRoots artifact order prepared.rows prepared.roots .qmatch)
  let checked ← NaturalAffine.witness (readAt prepared root.val runtime)
  return ⟨root.val,by with_reducible exact root.property,checked.val,by with_reducible exact checked.property⟩

end QleisliKernel.Qirf.RuntimeBodyOperations
