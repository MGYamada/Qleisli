import QleisliKernel.Qirf.RuntimeSourceOperationMarkers
import QleisliKernel.SourceTypes.GenericOperation

/-! Check the Meaning from the original queue duty using the reference bodies
of the written native assertion on its already validated dependency root.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeOriginalMeaning
open QleisliKernel Finite SourceTypes

/-- The complete original inputs to the ordinary leaf interpreter. Both
graphs come from Lean's source reader over the same immutable module table. -/
structure OrdinaryLeaf where
  source : String
  owner : String
  declaration : Declaration
  input : Semantics.FiniteCarrier.Basis
  output : Semantics.FiniteCarrier.Basis
  kind : SourceMeaningOrdinary.Kind
  functionCaller : String
  functionOwner : String
  functionSource : String
  functionOccurrence : BodyOccurrence
  functionTokens : List LocatedToken
  functionInputs : List Semantics.FiniteCarrier.Basis
  functionOutput : Semantics.FiniteCarrier.Basis
  deriving DecidableEq

def ordinaryLeaf {sources} (graph : SourceMeaning.Graph sources) : Option OrdinaryLeaf := do
  let [node] := graph.nodes | none
  let reference := fun kind (function : SourceMeaning.ClassicalReference sources) =>
    if graph.root != 0 || graph.input != node.input.basis || graph.output != node.output.basis then none else
      some ⟨node.original.source,node.owner,node.original.declaration,graph.input,graph.output,kind,
        function.caller,function.resolution.result.moduleName,function.signature.original.source,
        function.signature.original.occurrence,function.tokens,function.signature.inputs,function.signature.basis⟩
  match node.action with
  | .permutation function => reference .permutation function
  | .phase function => reference .phase function
  | _ => none

private def leafWork {sources} (graph : SourceMeaning.Graph sources) : Nat :=
  let reference := fun (node : SourceMeaning.Node sources) (function : SourceMeaning.ClassicalReference sources) =>
    let occurrence := function.signature.original.occurrence
    16*(node.original.source.utf8ByteSize+function.signature.original.source.utf8ByteSize+
      SourceTrace.Meter.tokenFields (function.tokens ++ occurrence.header ++ occurrence.body)+
      Raw.OwnerFlow.fields (([graph.input,graph.output,node.input.basis,node.output.basis,
        function.signature.basis] ++ function.signature.inputs).map (fun basis => ⟨0,basis⟩))+1)
  match graph.nodes with
  | [node] => match node.action with
    | .permutation function | .phase function => reference node function
    | _ => 8
  | _ => 8

/-- Reuse is limited to the identical singleton ordinary interpretation.
Every other graph keeps the complete original reference-body read. -/
inductive Specification {artifact catalogue result} {root : Validity.Root} {child : RuntimeOperationTree.Value}
    {native : RuntimePreparedOperation.Requirement artifact catalogue result}
    (equation : RuntimeOperationTree.Meaning child native root)
    (request : SourceMeaning.Request artifact.sources) where
  | ordinary (leaf : OrdinaryLeaf)
      (original : ordinaryLeaf request.meaning.graph = some leaf)
      (retained : ordinaryLeaf native.request.meaning.graph = some leaf)
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
  | .ordinary .. => equation.specification.action
  | .fresh _ _ _ _ specification _ => specification.action

private def readSpecification {artifact catalogue result root child native}
    (equation : @RuntimeOperationTree.Meaning artifact catalogue result child native root)
    (request : SourceMeaning.Request artifact.sources) : WorkM (Specification equation request) := do
  let held := native.meaning
  let rowBytes (values : List SourceRows.Row) := values.foldl (fun n row => n+row.1.utf8ByteSize+row.2.utf8ByteSize+1) 0
  exactWork (Exact.charge (leafWork request.meaning.graph+leafWork native.request.meaning.graph))
  match original : ordinaryLeaf request.meaning.graph with
  | some leaf =>
    if retained : ordinaryLeaf native.request.meaning.graph = some leaf then
      return .ordinary leaf original retained
  | none => pure ()
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
