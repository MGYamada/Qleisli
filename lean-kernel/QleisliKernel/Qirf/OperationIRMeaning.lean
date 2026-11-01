import QleisliKernel.SourceTypes.StaticOperation
import QleisliKernel.Qirf.PureInterval

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
  let dimension := layout.labels.length
  exactWork (Exact.charge (dimension*dimension+1))
  match kind with
  | .h =>
    guard (target == [.bit]) .request
    let negative ← lift (arithmetic (Exact.Scalar.neg halfRoot))
    lift (arithmetic (Exact.Matrix.make 2 2 [halfRoot,halfRoot,halfRoot,negative]))
  | .globalPhaseEighth =>
    let entries := (List.range (dimension*dimension)).map fun index =>
      if index / dimension == index % dimension then Exact.Scalar.phase 1 else Scalar.zero
    lift (arithmetic (Exact.Matrix.make dimension dimension entries))

private def child (values : List Matrix) (index : Nat) : WorkM Matrix := lift (readOption values[index]?)

private def formalChild {sources} (metadata : StaticOperation.Result sources)
    (operations : List (String × Nat)) (ordinal : Nat) : WorkM Nat := do
  let provider ← lift (readOption metadata.formal)
  match provider.signature.instantiation with
  | .closed _ => throw .request
  | .static _ environment _ =>
    let formal ← lift (readOption environment.numeric.original.header.formals[ordinal]?)
    guard (formal.ordinal == ordinal) .request
    let (_,index) ← lift (readOption (operations.find? fun pair => pair.1 == formal.name))
    return index

/-- Tensor places the left owner's axes first (least significant). Conjugation
uses the existing source operation law A B A† and retains distinct A/B ports. -/
def readNode {sources} (metadata : StaticOperation.Result sources) (node : Node)
    (previous providers : List Matrix) (nextProvider : Nat) : WorkM (Matrix × Nat) := do
  let (value,nextProvider) ← match node with
    | .provider .. => do return (← child providers nextProvider,nextProvider+1)
    | .formal _ _ _ _ operations ordinal => do
      let index ← formalChild metadata operations ordinal
      return (← child previous index,nextProvider)
    | .primitive kind target => do return (← primitive kind target,nextProvider)
    | .inverse index => do
      let value ← child previous index
      return (← exactWork (Exact.Matrix.adjointWork value),nextProvider)
    | .controlled index => do return (← controlled (← child previous index),nextProvider)
    | .power index count => do return (← power (← child previous index) count,nextProvider)
    | .thenOp left right => do
      let first ← child previous left
      let second ← child previous right
      return (← exactWork (Exact.Matrix.composeWork second first),nextProvider)
    | .tensor left right => do
      let first ← child previous left
      let second ← child previous right
      return (← exactWork (Exact.Matrix.tensorWork first second),nextProvider)
    | .conjugate outer middle => do
      let outer ← child previous outer
      let middle ← child previous middle
      let adjoint ← exactWork (Exact.Matrix.adjointWork outer)
      let inner ← exactWork (Exact.Matrix.composeWork middle adjoint)
      return (← exactWork (Exact.Matrix.composeWork outer inner),nextProvider)
  let input ← FiniteCarrier.read metadata.input
  let output ← FiniteCarrier.read metadata.output
  guard (value.cols == input.labels.length && value.rows == output.labels.length) .request
  return (value,nextProvider)

/-- Every original node is visited, including providers in a zero power or
an unused formal argument. The input provider spine is consumed exactly once
in the graph's original provider order; no selected runtime arm skips it. -/
def compute {sources context description}
    (graph : StaticOperation.CheckedGraph sources context description) (providers : List Matrix) : WorkM Matrix := do
  exactWork (Exact.charge (16*(description.nodes.length+graph.results.length+providers.length+1)^2))
  guard (providers.length == graph.providers.length && description.nodes.length == graph.results.length) .request
  let (values,consumed) ← (description.nodes.zip graph.results).foldlM
    (fun (values,consumed) (node,metadata) => do
      let (value,consumed) ← readNode metadata node values providers consumed
      return (values ++ [value],consumed)) ([],0)
  guard (consumed == providers.length) .request
  child values description.root

end QleisliKernel.Qirf.OperationIRMeaning
