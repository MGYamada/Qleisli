import QleisliKernel.Qirf.RuntimeContextRequest
import QleisliKernel.Qirf.RuntimeInterval
import QleisliKernel.Qirf.SourceProviderBinding
import QleisliKernel.SourceTypes.SourceRuntimeTrace

/-! Original provider occurrences prepared before the one final graph check.
The selected graph supplies the exact original provider context and every Op
actual receipt. Its same core header becomes the fresh mixed-body signature;
neither the provider module nor an equal descriptor substitutes for the supply.
Source action/Meaning/access equations remain separate native continuations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeProviderHeader
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
abbrev Request := SourceProviderSubject.Subject × RuntimeContextRequest.Context

structure Original {sources context description}
    (graph : StaticOperation.CheckedGraph sources context description) (index : Nat) where
  supplied : StaticOperation.ProviderInstance graph index
  suppliedRead : RuntimeInterval.Computed (StaticOperation.argumentsAt graph index) supplied
  runtime : SourceRuntimeContext.CoreBinding supplied.provider.signature supplied.context supplied.arguments
  body : SourceRuntimeTrace.Body runtime.signature
  traversed : RuntimeInterval.Computed (SourceRuntimeTrace.readBodyWithSignature runtime.signature) body

def readOriginal {sources context description}
    (graph : StaticOperation.CheckedGraph sources context description) (index : Nat) :
    WorkM (Original graph index) := do
  let supplied ← NaturalAffine.witness (StaticOperation.argumentsAt graph index)
  let runtime ← SourceRuntimeContext.fromQuantumCore supplied.val.provider.signature supplied.val.context supplied.val.arguments
  let body ← NaturalAffine.witness (SourceRuntimeTrace.readBodyWithSignature runtime.signature)
  return ⟨supplied.val,by with_reducible exact supplied.property,runtime,body.val,by with_reducible exact body.property⟩

structure Header (artifact : Artifact) {context description}
    (graph : StaticOperation.CheckedGraph artifact.sources context description) (index : Nat) (request : Request) where
  original : Original graph index
  subject : SourceProviderBinding.Bound artifact original.supplied.provider request.1

def read (artifact : Artifact) {context description}
    (graph : StaticOperation.CheckedGraph artifact.sources context description) (index : Nat) (request : Request) :
    WorkM (Header artifact graph index request) := do
  let original ← readOriginal graph index
  let subject ← SourceProviderBinding.read artifact original.supplied.provider request.1
  return ⟨original,subject⟩

def Header.roots {artifact context description graph index request}
    (header : @Header artifact context description graph index request) : List Nat := header.subject.roots

/-- Relevance follows the actual original queries. Nested named/basis/transform
body queries and selection leaves must still be recursively discovered by the
complete worklist before the final graph is checked. -/
def eventRows {sources caller} : Nat → SourceRuntimeContext.Event sources caller → List (String × String)
  | 0,_ => []
  | fuel+1,event => match event with
    | .primitive event => CallName.sourceRows event.candidate
    | .phase event => CallName.sourceRows event.application.candidate ++ event.naturals.sourceRows
    | .selection _ _ _ _ _ _ naturals .. => naturals.sourceRows
    | .named event => event.target.sourceRows ++ event.canonical.staticRows
    | .operation event => event.operation.rows ++ event.operation.graph.sourceRows ++ event.naturals.sourceRows
    | .basis event => event.staticRows
    | .conditional event left right => event.naturals.sourceRows ++ event.thenArm.staticRows ++
        event.elseArm.staticRows ++ left.flatMap (eventRows fuel) ++ right.flatMap (eventRows fuel)
    | .transform event => event.target.sourceRows ++ event.forward.staticRows ++
        event.counts.flatMap (·.checked.rows)
    | .staticConditional event children => event.generic.sourceRows ++
        event.selection.naturals.sourceRows ++ event.selected.2.staticRows ++ children.flatMap (eventRows fuel)
    | .matching event children => event.generic.sourceRows ++ event.naturals.sourceRows ++
        event.labels.labels.sourceRows ++ event.arms.flatMap (·.2.staticRows) ++
        children.flatMap (fun arm => arm.flatMap (eventRows fuel))
    | .computed event children => event.generic.sourceRows ++
        (SourceRuntimeContext.Event.computed event children).staticRows ++ children.flatMap (eventRows fuel)
    | .registerPrimitive event => (SourceRuntimeContext.Event.registerPrimitive event).staticRows

def Header.rows {artifact context description graph index request}
    (header : @Header artifact context description graph index request) : List (String × String) :=
  let body := header.original.body.checked
  graph.sourceRows ++ header.original.supplied.arguments.sourceRows ++
    body.signature.sourceRows ++ body.summary.staticRows ++ body.events.flatMap (eventRows 65)

structure IR {artifact context description graph index request}
    (header : @Header artifact context description graph index request) (root : Validity.Root) where
  original : PureProviderSubject.Checked artifact root header.original.supplied.provider header.subject.programIndex

/-- IR/code facts use exactly this bound subject and final dependency root.
They do not consume body contexts, demanded inverse/control paths or Meaning
requirements; an enclosing accepted result must separately retain those facts.
In particular this function is not a complete provider acceptance gate. -/
def readIR {artifact context description graph index request}
    (header : @Header artifact context description graph index request) (root : Validity.Root) :
    WorkM (IR header root) := do
  return ⟨← SourceProviderBinding.readIR root header.subject⟩

theorem Original.sameSource {sources context description graph index}
    (original : @Original sources context description graph index) :
    original.body.checked.signature.original.source = original.supplied.provider.signature.original.source := by
  rw [original.body.originalSignature]
  exact original.runtime.source

theorem Original.sameSupplier {sources context description graph index}
    (original : @Original sources context description graph index) :
    original.body.checked.signature.context = original.supplied.context := by
  rw [original.body.originalSignature]
  exact original.runtime.sameContext

end QleisliKernel.Qirf.RuntimeProviderHeader
