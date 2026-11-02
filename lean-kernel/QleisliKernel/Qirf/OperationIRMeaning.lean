import QleisliKernel.SourceTypes.StaticOperation
import QleisliKernel.Qirf.PureInterval
import QleisliKernel.Semantics.PrimitiveOperator

/-! Exact operation-tree evaluation over independently realized provider maps.
This calculation alone accepts neither a source body nor an IR program and
grants no access. Its enclosing caller must bind every provider occurrence to
the original source and actual final-root program, and check the complete
implementation/control/code equations. No dense joined qmatch matrix is built.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.OperationIRMeaning
open QleisliKernel QleisliKernel.SourceTypes Finite Semantics.Exact
open OperationDescription

def controlled (value : Matrix) : WorkM Matrix := do
  guard (value.rows == value.cols) .request
  let dimension := 2*value.rows
  guard (Exact.matrixValid dimension dimension) .limit
  exactWork (Exact.charge (dimension*dimension))
  let entries := (List.range (dimension*dimension)).map fun index =>
    let row := index / dimension
    let column := index % dimension
    if row % 2 != column % 2 then Scalar.zero
    else if row % 2 == 0 then if row / 2 == column / 2 then Scalar.one else Scalar.zero
    else value.entry (row / 2) (column / 2)
  lift (arithmetic (Exact.Matrix.make dimension dimension entries))

/-- All counts, including zero, receive their already checked child map. The
linear precharge precedes recursion; a huge untrusted count cannot make a free
zero-width loop. Source count/profile rules remain separately mandatory. -/
def power (value : Matrix) (count : Nat) : WorkM Matrix := do
  guard (value.rows == value.cols) .request
  exactWork (Exact.charge (8*(count+1)))
  let identity ← lift (arithmetic (Exact.Matrix.identity value.rows))
  let iterate : Nat → Matrix → WorkM Matrix :=
    Nat.rec pure (fun _ next accumulated => do
      let accumulated ← exactWork (Exact.Matrix.composeWork value accumulated)
      next accumulated)
  iterate count identity

def primitive (kind : Primitive) (target : Semantics.FiniteCarrier.Basis) : WorkM Matrix := do
  let layout ← FiniteCarrier.read target
  exactWork (Exact.charge ((layout.labels.length+1)^2))
  let reference := match kind with
    | .h => Semantics.PrimitiveOperator.Kind.h
    | .globalPhaseEighth => Semantics.PrimitiveOperator.Kind.globalPhaseEighth
  lift (readOption (Semantics.PrimitiveOperator.meaning reference target))

private def formalPosition {sources} (metadata : StaticOperation.Result sources)
    (operations : List (String × Nat)) (ordinal : Nat) : WorkM Nat := do
  let provider ← lift (readOption metadata.formal)
  match provider.signature.instantiation with
  | .closed _ => throw .request
  | .static _ environment _ =>
    let formal ← lift (readOption environment.numeric.original.header.formals[ordinal]?)
    guard (formal.ordinal == ordinal) .request
    let position := (operations.map (·.1)).idxOf formal.name
    guard (position < operations.length) .request
    return position

/-- Child values are occurrence values in the node's exact child order.
Repeated node indices never select a globally memoized provider value. -/
def readNode {sources} (metadata : StaticOperation.Result sources) (node : Node)
    (children providers : List Matrix) (nextProvider : Nat) : WorkM (Matrix × Nat) := do
  let (value,nextProvider) ← match node,children with
    | .provider ..,_ => do
      return (← lift (readOption providers[nextProvider]?),nextProvider+1)
    | .formal _ _ _ _ operations ordinal,_ => do
      let position ← formalPosition metadata operations ordinal
      return (← lift (readOption children[position]?),nextProvider)
    | .primitive kind target,[] => do return (← primitive kind target,nextProvider)
    | .requested _ _ _,[value] => pure (value,nextProvider)
    | .inverse _,[value] => do return (← exactWork (Exact.Matrix.adjointWork value),nextProvider)
    | .controlled _,[value] => do return (← controlled value,nextProvider)
    | .power _ count,[value] => do return (← power value count,nextProvider)
    | .thenOp _ _,[first,second] => do
      return (← exactWork (Exact.Matrix.composeWork second first),nextProvider)
    | .tensor _ _,[first,second] => do
      return (← exactWork (Exact.Matrix.tensorWork first second),nextProvider)
    | .conjugate _ _,[outer,middle] => do
      let adjoint ← exactWork (Exact.Matrix.adjointWork outer)
      let inner ← exactWork (Exact.Matrix.composeWork middle adjoint)
      return (← exactWork (Exact.Matrix.composeWork outer inner),nextProvider)
    | _,_ => throw .request
  let input ← FiniteCarrier.read metadata.input
  let output ← FiniteCarrier.read metadata.output
  guard (value.cols == input.labels.length && value.rows == output.labels.length) .request
  return (value,nextProvider)

private def visit {sources context description}
    (graph : StaticOperation.CheckedGraph sources context description) (providers : List Matrix) :
    Nat → Nat → Nat → WorkM (Matrix × Nat)
  | 0,_,_ => throw .limit
  | fuel+1,index,nextProvider => do
    let node ← lift (readOption description.nodes[index]?)
    let metadata ← lift (readOption graph.results[index]?)
    let (children,nextProvider) ← node.children.foldlM (fun (children,nextProvider) child => do
      let (value,nextProvider) ← visit graph providers fuel child nextProvider
      return (children ++ [value],nextProvider)) ([],nextProvider)
    readNode metadata node children providers nextProvider

/-- Every child edge is visited, including shared DAG children, providers in a
zero power and every unused formal actual. The existing 4096-node TREE profile
is checked before expansion, so a compact DAG cannot evade that profile. -/
def compute {sources context description}
    (graph : StaticOperation.CheckedGraph sources context description) (providers : List Matrix) : WorkM Matrix := do
  -- Metadata alone does not discharge any Meaning equation.
  guard (!graph.hasMeaningRequirements) .request
  let occurrences ← StaticOperation.readOccurrences description
  exactWork (Exact.charge (16*(description.nodes.length+graph.results.length+occurrences.length+providers.length+1)^2))
  let requiredProviders := occurrences.foldl (fun count index => match description.nodes[index]? with
    | some (.provider ..) => count+1
    | _ => count) 0
  guard (requiredProviders == providers.length) .request
  let (value,consumed) ← visit graph providers (occurrences.length+1) description.root 0
  guard (consumed == providers.length) .request
  return value

end QleisliKernel.Qirf.OperationIRMeaning
