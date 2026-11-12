import QleisliKernel.Qirf.RuntimeSourceOperationMarkers
import QleisliKernel.Qirf.RuntimeStructuredRoot
import QleisliKernel.SourceTypes.GenericOperation

/-! Check the Meaning from the original queue duty using the reference bodies
of the written native assertion on its already validated dependency root.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeOriginalMeaning
open QleisliKernel Finite SourceTypes

abbrev Basis := Semantics.FiniteCarrier.Basis

structure ReferenceKey where
  caller : String
  owner : String
  source : String
  occurrence : BodyOccurrence
  tokens : List LocatedToken
  inputs : List Basis
  outputs : List Basis
  deriving DecidableEq

inductive ActionKey where
  | reference (function : ReferenceKey) (arguments : StaticTypes.Arguments)
      (effect : Semantics.Raw.Effect) (internal : Bool)
  | permutation (function : ReferenceKey)
  | phase (function : ReferenceKey)
  | compose (left right : Nat)
  | tensor (left right : Nat)
  deriving DecidableEq

structure NodeKey where
  owner : String
  name : String
  source : String
  declaration : Declaration
  tokens : List LocatedToken
  input : Basis
  output : Basis
  action : ActionKey
  deriving DecidableEq

structure GraphKey where
  nodes : List NodeKey
  root : Nat
  input : Basis
  output : Basis
  rows : List SourceRows.Row
  deriving DecidableEq

private def classicalKey {sources} (function : SourceMeaning.ClassicalReference sources) : ReferenceKey :=
  ⟨function.caller,function.resolution.result.moduleName,function.signature.original.source,
    function.signature.original.occurrence,function.tokens,function.signature.inputs,[function.signature.basis]⟩

private def nodeKey {sources} (node : SourceMeaning.Node sources) : NodeKey :=
  let action := match node.action with
    | .reference function => ActionKey.reference
        ⟨function.caller,function.resolution.result.moduleName,function.signature.original.source,
          function.signature.original.occurrence,function.tokens,function.signature.inputs,function.signature.outputs⟩
        function.signature.staticArguments function.expectedEffect function.internalInference
    | .permutation function => .permutation (classicalKey function)
    | .phase function => .phase (classicalKey function)
    | .compose left right => .compose left right
    | .tensor left right => .tensor left right
  ⟨node.owner,node.name,node.original.source,node.original.declaration,node.original.tokens,
    node.input.basis,node.output.basis,action⟩

/-- Keep declaration and reference occurrences, exact ports, ordered edges,
and dependency rows from both original Lean reads over the same source table. -/
def graphKey {sources} (graph : SourceMeaning.Graph sources) : GraphKey :=
  ⟨graph.nodes.map nodeKey,graph.root,graph.input,graph.output,graph.sourceRows⟩

private def rowBytes (values : List SourceRows.Row) : Nat :=
  values.foldl (fun n row => n+row.1.utf8ByteSize+row.2.utf8ByteSize+1) 0

private def portWork (ports : List Basis) : Nat :=
  Raw.OwnerFlow.fields (ports.map (fun basis => ⟨0,basis⟩))

private def referenceWork (function : ReferenceKey) : Nat :=
  function.caller.utf8ByteSize+function.owner.utf8ByteSize+function.source.utf8ByteSize+
    SourceTrace.Meter.tokenFields (function.tokens ++ function.occurrence.header ++ function.occurrence.body)+
    portWork (function.inputs ++ function.outputs)+1

private def graphWork (graph : GraphKey) : Nat :=
  16*(portWork [graph.input,graph.output]+rowBytes graph.rows+
    graph.nodes.foldl (fun total node => total+node.owner.utf8ByteSize+node.name.utf8ByteSize+
      node.source.utf8ByteSize+SourceTrace.Meter.tokenFields node.tokens+portWork [node.input,node.output]+
      match node.action with
      | .reference function arguments .. => referenceWork function+RuntimeStructuredRoot.argumentFields arguments
      | .permutation function | .phase function => referenceWork function
      | .compose .. | .tensor .. => 1) 0+1)

structure RequestMatch {sources} (first second : SourceMeaning.Request sources) : Prop where
  caller : first.caller = second.caller
  moduleName : first.moduleName = second.moduleName
  declarationName : first.declarationName = second.declarationName
  queryRows : first.queryRows = second.queryRows
  graph : graphKey first.meaning.graph = graphKey second.meaning.graph

def readRequestMatch {sources} (first second : SourceMeaning.Request sources) :
    WorkM (PLift (RequestMatch first second)) := do
  let left := graphKey first.meaning.graph
  let right := graphKey second.meaning.graph
  let fields := fun (request : SourceMeaning.Request sources) =>
    (request.caller.map String.utf8ByteSize).getD 0 + request.moduleName.utf8ByteSize +
      request.declarationName.utf8ByteSize + rowBytes request.queryRows
  exactWork (Exact.charge (16*(fields first+fields second+1)+graphWork left+graphWork right))
  if names : first.caller = second.caller ∧ first.moduleName = second.moduleName ∧
      first.declarationName = second.declarationName ∧ first.queryRows = second.queryRows then
    if graph : left = right then
      return ⟨⟨names.1,names.2.1,names.2.2.1,names.2.2.2,graph⟩⟩
    else throw .request
  else throw .request

/-- Equal original graphs share the already evaluated specification and its
actual reference bodies on the same independently validated native root. -/
inductive Specification {artifact catalogue result} {root : Validity.Root} {child : RuntimeOperationTree.Value}
    {native : RuntimePreparedOperation.Requirement artifact catalogue result}
    (equation : RuntimeOperationTree.Meaning child native root)
    (request : SourceMeaning.Request artifact.sources) where
  | shared (original : graphKey request.meaning.graph = graphKey native.request.meaning.graph)
  | fresh (meaning : SourceMeaningAction.Prepared artifact catalogue request.meaning)
      (preparedRead : RuntimeInterval.Computed
        (SourceMeaningAction.prepare artifact catalogue request.meaning native.meaning.requests) meaning)
      (sameRows : meaning.rows = native.meaning.rows) (sameRoots : meaning.roots = native.meaning.roots)
      (specification : SourceMeaningAction.Checked meaning root)
      (evaluated : RuntimeInterval.Computed (SourceMeaningAction.read meaning root) specification)

def Specification.action {artifact catalogue result root child native equation request}
    (specification : @Specification artifact catalogue result root child native equation request) :
    Semantics.Exact.Matrix :=
  match specification with
  | .shared _ => equation.specification.action
  | .fresh _ _ _ _ specification _ => specification.action

private def readSpecification {artifact catalogue result root child native}
    (equation : @RuntimeOperationTree.Meaning artifact catalogue result child native root)
    (request : SourceMeaning.Request artifact.sources) : WorkM (Specification equation request) := do
  let held := native.meaning
  let original := graphKey request.meaning.graph
  let retained := graphKey native.request.meaning.graph
  exactWork (Exact.charge (graphWork original+graphWork retained))
  if same : original = retained then return .shared same
  let meaning ← NaturalAffine.witness (SourceMeaningAction.prepare artifact catalogue request.meaning held.requests)
  let rows := meaning.val.rows
  let roots := meaning.val.roots
  exactWork (Exact.charge (16*(rowBytes rows+rowBytes held.rows+roots.length+held.roots.length+1)))
  if same : rows = held.rows ∧ roots = held.roots then
    let specification ← NaturalAffine.witness (SourceMeaningAction.read meaning.val root)
    return .fresh meaning.val (by with_reducible exact meaning.property) same.1 same.2
      specification.val (by with_reducible exact specification.property)
  else throw .request

structure Checked {artifact catalogue context description graph implementations references prepared root requested caller scope checked marker target}
    (asserted : @RuntimeSourceOperationMarkers.Assertion artifact catalogue context description graph implementations references prepared
      root requested caller scope checked marker target) (duty : GenericOperation.Duty artifact.sources) where
  request : SourceMeaning.Request artifact.sources
  original : duty.requirement = .meaning request
  written : RuntimeSourceOperationMarkers.MeaningOriginal marker request
  specification : Specification asserted.equation request
  evaluated : RuntimeInterval.Computed (readSpecification asserted.equation request) specification
  input : asserted.child.input = request.meaning.graph.input
  output : asserted.child.output = request.meaning.graph.output
  action : asserted.child.action = specification.action

def read {artifact catalogue context description graph implementations references prepared root requested caller scope checked marker target}
    (asserted : @RuntimeSourceOperationMarkers.Assertion artifact catalogue context description graph implementations references prepared
      root requested caller scope checked marker target) (duty : GenericOperation.Duty artifact.sources) :
    WorkM (Checked asserted duty) := do
  match original : duty.requirement with
  | .access _ => throw .request
  | .meaning request =>
    let written ← RuntimeSourceOperationMarkers.readMeaningOriginal marker request
    let specification ← NaturalAffine.witness (readSpecification asserted.equation request)
    exactWork (Exact.charge (16*(Raw.OwnerFlow.fields [⟨0,asserted.child.input⟩,⟨0,asserted.child.output⟩,
      ⟨0,request.meaning.graph.input⟩,⟨0,request.meaning.graph.output⟩]+1)))
    if ports : asserted.child.input = request.meaning.graph.input ∧ asserted.child.output = request.meaning.graph.output then
      exactWork (Exact.charge (asserted.child.action.entries.length+specification.val.action.entries.length+1))
      if action : asserted.child.action = specification.val.action then
        return ⟨request,original,written,specification.val,by with_reducible exact specification.property,
          ports.1,ports.2,action⟩
      else throw .equation
    else throw .request

end QleisliKernel.Qirf.RuntimeOriginalMeaning
