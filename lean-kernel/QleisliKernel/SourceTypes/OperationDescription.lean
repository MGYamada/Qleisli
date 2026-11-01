import QleisliKernel.Semantics.FiniteCarrier

/-! Untrusted finite operation descriptions. Provider actuals and constructor
children are earlier-node references; every actual, including an unused one,
remains a dependency. No paths, effects, matrices or success flags are supplied.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.OperationDescription
open Semantics.FiniteCarrier

inductive Primitive where
  | h | globalPhaseEighth
  deriving BEq, DecidableEq, Repr

inductive Node where
  | primitive (kind : Primitive) (target : Basis)
  | provider (moduleName declarationName : String) (bases : List (String × Basis))
      (naturals : List (String × Nat)) (operations : List (String × Nat))
  | formal (moduleName declarationName : String) (bases : List (String × Basis))
      (naturals : List (String × Nat)) (operations : List (String × Nat)) (ordinal : Nat)
  | inverse (child : Nat)
  | thenOp (left right : Nat)
  | tensor (left right : Nat)
  | controlled (child : Nat)
  | power (child count : Nat)
  | conjugate (outer middle : Nat)
  deriving BEq, DecidableEq, Repr

def Node.children : Node → List Nat
  | .primitive .. => []
  | .provider _ _ _ _ operations | .formal _ _ _ _ operations _ => operations.map (·.2)
  | .inverse child | .controlled child | .power child _ => [child]
  | .thenOp left right | .tensor left right | .conjugate left right => [left,right]

def Node.remap (mapping : Nat → Nat) : Node → Node
  | .primitive kind target => .primitive kind target
  | .provider owner name bases naturals operations =>
    .provider owner name bases naturals (operations.map fun (name,index) => (name,mapping index))
  | .formal owner name bases naturals operations ordinal =>
    .formal owner name bases naturals (operations.map fun (name,index) => (name,mapping index)) ordinal
  | .inverse child => .inverse (mapping child)
  | .controlled child => .controlled (mapping child)
  | .power child count => .power (mapping child) count
  | .thenOp left right => .thenOp (mapping left) (mapping right)
  | .tensor left right => .tensor (mapping left) (mapping right)
  | .conjugate left right => .conjugate (mapping left) (mapping right)

structure Description where
  nodes : List Node
  root : Nat
  deriving BEq, DecidableEq, Repr

def Description.topological (description : Description) : Bool :=
  !description.nodes.isEmpty && description.nodes.length ≤ 4096 &&
    description.root+1 == description.nodes.length &&
    description.nodes.zipIdx.all (fun (node,index) => node.children.all (· < index))

def Description.reachable (description : Description) (root : Nat) : List Nat :=
  ((description.nodes.zipIdx.reverse).foldl (fun seen (node,index) =>
    if seen.contains index then node.children ++ seen else seen) [root]).eraseDups

def Description.complete (description : Description) : Bool :=
  description.topological &&
    (description.reachable description.root).length == description.nodes.length

/-- Extract an actual child closure while preserving its original node order
and every provider argument. The graph checker independently checks the result;
this operation carries no acceptance or source identity by itself. -/
def Description.select (description : Description) (root : Nat) : Option Description := do
  if !description.topological || root ≥ description.nodes.length then none else do
    let reachable := description.reachable root
    let selected := description.nodes.zipIdx.filter (fun (_,index) => reachable.contains index)
    let indices := selected.map (·.2)
    let result := ⟨selected.map (fun (node,_) => node.remap indices.idxOf),indices.idxOf root⟩
    if result.complete then some result else none

def Description.unary (constructor : Nat → Node) (child : Description) : Description :=
  ⟨child.nodes ++ [constructor child.root],child.nodes.length⟩

def Description.binary (constructor : Nat → Nat → Node) (left right : Description) : Description :=
  let shifted := right.nodes.map (Node.remap (·+left.nodes.length))
  ⟨left.nodes ++ shifted ++ [constructor left.root (right.root+left.nodes.length)],
    left.nodes.length+right.nodes.length⟩

/-- Provider arguments retain their complete graph order even when the
provider never executes that formal. Original argument checking is separate. -/
def provider (owner name : String) (bases : List (String × Basis)) (naturals : List (String × Nat))
    (operations : List (String × Description)) : Description :=
  let (nodes,indices) := operations.foldl (fun (nodes,indices) (name,description) =>
    (nodes ++ description.nodes.map (Node.remap (·+nodes.length)),
      indices ++ [(name,description.root+nodes.length)])) ([],[])
  ⟨nodes ++ [.provider owner name bases naturals indices],nodes.length⟩

def formal (owner name : String) (bases : List (String × Basis)) (naturals : List (String × Nat))
    (operations : List (String × Description)) (ordinal : Nat) : Description :=
  let (nodes,indices) := operations.foldl (fun (nodes,indices) (name,description) =>
    (nodes ++ description.nodes.map (Node.remap (·+nodes.length)),
      indices ++ [(name,description.root+nodes.length)])) ([],[])
  ⟨nodes ++ [.formal owner name bases naturals indices ordinal],nodes.length⟩

end QleisliKernel.SourceTypes.OperationDescription
