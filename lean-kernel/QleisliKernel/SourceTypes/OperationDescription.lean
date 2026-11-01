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
  | requested (child : Nat) (moduleName declarationName : String)
  deriving BEq, DecidableEq, Repr

def Node.children : Node → List Nat
  | .primitive .. => []
  | .provider _ _ _ _ operations | .formal _ _ _ _ operations _ => operations.map (·.2)
  | .inverse child | .controlled child | .power child _ | .requested child _ _ => [child]
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
  | .requested child owner name => .requested (mapping child) owner name

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

private def treeCounts (description : Description) : Except String (List Nat) := do
  if !description.complete then throw "incomplete original operation description"
  description.nodes.foldlM (fun counts node => do
    let count ← node.children.foldlM (fun count index => do
      let some child := counts[index]? | throw "operation child is not earlier"
      if count+child > 4096 then throw "operation expanded tree exceeds existing node budget"
      pure (count+child)) 1
    pure (counts ++ [count])) []

/-- Description occurrences count every child edge, including unused actuals
and zero-power children. Sharing a DAG node cannot evade the tree profile. -/
def Description.treeSize (description : Description) : Except String Nat := do
  let counts ← treeCounts description
  let some count := counts[description.root]? | throw "missing operation root count"
  if count > 4096 then throw "operation expanded tree exceeds existing node budget"
  pure count

private inductive OccurrenceTask where
  | enter (index : Nat)
  | leave (index : Nat)

private def occurrenceLoop (description : Description) :
    Nat → List OccurrenceTask → List Nat → Except String (List Nat) :=
  Nat.rec (fun tasks reversed => if tasks.isEmpty then pure reversed.reverse
      else throw "operation occurrence traversal exhausted")
    (fun _ next tasks reversed => do
      match tasks with
      | [] => pure reversed.reverse
      | .enter index :: rest =>
        let some node := description.nodes[index]? | throw "missing operation occurrence"
        next (node.children.map OccurrenceTask.enter ++ [.leave index] ++ rest) reversed
      | .leave index :: rest => next rest (index :: reversed))

structure Expansion where
  order : List Nat
  bounded : order.length ≤ 4096

def Description.expansion (description : Description) : Except String Expansion := do
  let count ← description.treeSize
  let order ← occurrenceLoop description (2*count+1) [.enter description.root] []
  if order.length != count then throw "incomplete operation occurrence order"
  if bounded : order.length ≤ 4096 then pure ⟨order,bounded⟩
  else throw "operation occurrence order exceeds existing tree budget"

/-- Postorder over child EDGES, preserving duplicate indices and actual order.
This is a bounded source-description traversal, never provider evidence. -/
def Description.occurrences (description : Description) : Except String (List Nat) := do
  pure (← description.expansion).order

theorem Description.occurrences_bound (description : Description) (order : List Nat)
    (read : description.occurrences = .ok order) : order.length ≤ 4096 := by
  unfold Description.occurrences at read
  cases expanded : description.expansion with
  | error error =>
    rw [expanded] at read
    change (Except.error error : Except String (List Nat)) = .ok order at read
    cases read
  | ok expansion =>
    rw [expanded] at read
    change (Except.ok expansion.order : Except String (List Nat)) = .ok order at read
    have same : expansion.order = order := Except.ok.inj read
    rw [← same]
    exact expansion.bounded

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
