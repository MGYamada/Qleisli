import QleisliKernel.Qirf.RuntimePreparedOperation
import QleisliKernel.SourceTypes.SourceOperationProvenance

/-! Exact child-edge addresses in the same prepared native occurrence walk.
The stack follows original postorder, retaining duplicate node indices as
distinct occurrences. Source constructor and mixed-formal edges stay distinct.
This metadata reader checks no Meaning equation and grants no accepted handle;
source-marker, invocation and complete original-duty binding remain required.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeOperationOccurrenceTree
open QleisliKernel Finite SourceTypes
open QleisliKernel.SourceTypes.OperationDescription (Node)

structure Located {artifact catalogue context description graph implementations references}
    (prepared : @RuntimePreparedOperation.GraphPrepared artifact catalogue context description graph implementations references) where
  occurrence : RuntimePreparedOperation.Occurrence artifact catalogue graph prepared.order
  member : occurrence ∈ prepared.occurrences
  node : Node
  original : description.nodes[occurrence.index]? = some node

mutual
inductive Tree {artifact catalogue context description graph implementations references}
    (prepared : @RuntimePreparedOperation.GraphPrepared artifact catalogue context description graph implementations references) : Nat → Type where
  | branch (located : Located prepared) (children : Children prepared located.node.children) :
      Tree prepared located.occurrence.index

inductive Children {artifact catalogue context description graph implementations references}
    (prepared : @RuntimePreparedOperation.GraphPrepared artifact catalogue context description graph implementations references) : List Nat → Type where
  | nil : Children prepared []
  | cons {index indices} (tree : Tree prepared index) (rest : Children prepared indices) :
      Children prepared (index :: indices)
end

def Children.toList {artifact catalogue context description graph implementations references prepared indices}
    (children : @Children artifact catalogue context description graph implementations references prepared indices) :
    List (Sigma (Tree prepared)) :=
  -- Recurse over the index spine only; the trees themselves stay shared.
  WellFounded.fix (measure (List.length (α := Nat))).wf
    (C := fun indices => Children prepared indices → List (Sigma (Tree prepared)))
    (fun _ next children => match children with
      | .nil => []
      | .cons (index := index) (indices := indices) tree rest =>
        ⟨index,tree⟩ :: next indices (by decreasing_tactic) rest) indices children

theorem Children.indices {artifact catalogue context description graph implementations references prepared indices}
    (children : @Children artifact catalogue context description graph implementations references prepared indices) :
    children.toList.map (·.1) = indices := by
  cases children with
  | nil => rw [Children.toList,WellFounded.fix_eq]; rfl
  | cons tree rest =>
    rw [Children.toList,WellFounded.fix_eq]
    exact congrArg (List.cons _) (Children.indices rest)

private def readChildren {artifact catalogue context description graph implementations references prepared}
    (indices : List Nat)
    (trees : List (Sigma (@Tree artifact catalogue context description graph implementations references prepared))) :
    WorkM (Children prepared indices) :=
  -- Use the explicit structural recursor, so the executable has no generated
  -- partial recursion helper. This bound is the actual child-index list length.
  let build : Nat → (indices : List Nat) → List (Sigma (Tree prepared)) → WorkM (Children prepared indices) :=
    Nat.rec
      (fun indices trees => match indices,trees with
        | [],[] => pure .nil
        | _,_ => throw .request)
      (fun _ next indices trees => match indices,trees with
        | [],[] => pure .nil
        | index :: rest,⟨actual,tree⟩ :: trees =>
          if same : actual = index then do
            let tail ← next rest trees
            pure (.cons (same ▸ tree) tail)
          else throw .request
        | _,_ => throw .request)
  build indices.length indices trees

def Tree.located {artifact catalogue context description graph implementations references prepared index}
    (tree : @Tree artifact catalogue context description graph implementations references prepared index) : Located prepared :=
  match tree with | .branch located _ => located

def Tree.children {artifact catalogue context description graph implementations references prepared index}
    (tree : @Tree artifact catalogue context description graph implementations references prepared index) : List (Sigma (Tree prepared)) :=
  match tree with | .branch _ children => children.toList

theorem Tree.index {artifact catalogue context description graph implementations references prepared index}
    (tree : @Tree artifact catalogue context description graph implementations references prepared index) :
    tree.located.occurrence.index = index := by
  cases tree
  rfl

theorem Tree.ordered {artifact catalogue context description graph implementations references prepared index}
    (tree : @Tree artifact catalogue context description graph implementations references prepared index) :
    tree.children.map (·.1) = tree.located.node.children := by
  cases tree with
  | branch located children => exact children.indices

structure Checked {artifact catalogue context description graph implementations references}
    (prepared : @RuntimePreparedOperation.GraphPrepared artifact catalogue context description graph implementations references) where
  index : Nat
  tree : Tree prepared index
  atRoot : index = description.root

/-- Retain the exact prepared occurrences, rather than memoizing node indices.
Every actual child edge consumes its own original stack position. -/
def read {artifact catalogue context description graph implementations references}
    (prepared : @RuntimePreparedOperation.GraphPrepared artifact catalogue context description graph implementations references) :
    WorkM (Checked prepared) := do
  exactWork (Exact.charge (16*(prepared.occurrences.length+description.nodes.length+1)^2))
  let stack ← prepared.occurrences.attach.foldlM (fun (stack : List (Sigma (Tree prepared))) current => do
    let occurrence := current.val
    match original : description.nodes[occurrence.index]? with
    | none => throw .request
    | some node =>
      let splitAt := stack.length-node.children.length
      let remaining := stack.take splitAt
      let children := stack.drop splitAt
      let ordered ← readChildren node.children children
      let located : Located prepared := ⟨occurrence,current.property,node,original⟩
      return remaining ++ [⟨occurrence.index,.branch located ordered⟩]) []
  match stack with
  | [⟨index,tree⟩] =>
    if atRoot : index = description.root then return ⟨index,tree,atRoot⟩
    else throw .request
  | _ => throw .request

private def actualPosition {artifact catalogue context description graph implementations references prepared}
    (located : @Located artifact catalogue context description graph implementations references prepared)
    (ordinal : Nat) : WorkM Nat := do
  let select : WorkM (StaticOperation.Provider artifact.sources × List (String × Nat)) := match located.node with
    | .provider _ _ _ _ operations => do
      pure (← lift (readOption located.occurrence.result.provider),operations)
    | .formal _ _ _ _ operations _ => do
      pure (← lift (readOption located.occurrence.result.formal),operations)
    | _ => throw .request
  let (provider,operations) ← select
  match provider.signature.instantiation with
  | .closed _ => throw .request
  | .static _ environment _ =>
    let formals := environment.numeric.original.header.formals
    exactWork (Exact.charge (16*(formals.length+operations.length+
      (formals.map fun formal => formal.name.utf8ByteSize+1).sum+
      (operations.map fun operation => operation.1.utf8ByteSize+1).sum+1)))
    let formal ← lift (readOption formals[ordinal]?)
    guard (formal.ordinal == ordinal) .request
    let .operation _ := formal.kind | throw .request
    let position := (operations.map (·.1)).idxOf formal.name
    guard (position < operations.length) .request
    return position

private def childPosition (node : Node) (ordinal : Nat) : WorkM Nat := do
  match node with
  | .inverse _ | .controlled _ | .power _ _ | .requested _ _ _ =>
    guard (ordinal == 0) .request
    return ordinal
  | .thenOp _ _ | .tensor _ _ | .conjugate _ _ =>
    guard (ordinal < 2) .request
    return ordinal
  | _ => throw .request

/-- Follow original source constructor edges or actual mixed-formal ordinals.
The actual header determines each provider/formal child position; source names
alone never identify an occurrence, and no formal actual is silently dropped. -/
def follow {artifact catalogue context description graph implementations references prepared}
    (initial : Sigma (@Tree artifact catalogue context description graph implementations references prepared))
    (path : List SourceOperation.Edge) : WorkM (Sigma (Tree prepared)) :=
  let visit : Nat → Sigma (Tree prepared) → List SourceOperation.Edge → WorkM (Sigma (Tree prepared)) :=
    Nat.rec (fun current path => match path with
      | [] => pure current
      | _ :: _ => throw .limit)
    (fun _ next current path => match path with
      | [] => pure current
      | edge :: rest => do
        let tree := current.2
        exactWork (Exact.charge (8*(tree.children.length+1)))
        let position ← match edge with
          | .child ordinal => childPosition tree.located.node ordinal
          | .actual ordinal => actualPosition tree.located ordinal
        let child ← lift (readOption tree.children[position]?)
        next child rest)
  visit path.length initial path

end QleisliKernel.Qirf.RuntimeOperationOccurrenceTree
