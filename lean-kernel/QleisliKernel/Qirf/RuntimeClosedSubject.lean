import QleisliKernel.Qirf.RuntimeNativeSubject
import QleisliKernel.Qirf.RuntimeStructuredRoot
import QleisliKernel.SourceTypes.GenericClosedCorrespondence

/-! Structural correspondence of one checked native child occurrence with an
actual closed generic operation description. Every original child position is
visited in order, including repeated edges and children of a zero power.
Native formal wrappers are followed only by the existing authentic selector;
their exact reader receipts and conserved ports/action remain explicit.
Supplier/lexical-key transport and semantic duty discharge are separate gates.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeClosedSubject
open QleisliKernel Finite SourceTypes
open RuntimeNativeSubject (Cursor Child Formal)
open QleisliKernel.SourceTypes.OperationDescription (Node Description)

abbrev ChildRead {artifact catalogue context description graph implementations references prepared root requested checked}
    (cursor : @Cursor artifact catalogue context description graph implementations references prepared root requested checked)
    (position : Nat) :=
  {child : Child cursor position //
    RuntimeInterval.Computed (RuntimeNativeSubject.readChild cursor position) child}

private def supported : Node → Bool
  | .formal .. => false
  | _ => true

/-- Erase edge indices only. Kind, arity, Basis/Nat values, original provider
names, ordered operation argument names, powers and requested names remain. -/
def shape (node : Node) : Node := node.remap (fun _ => 0)

mutual
inductive Paired {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested)
    (subject : Description) : Nat → Cursor checked → Cursor checked → Type where
  | node {index : Nat} {cursor : Cursor checked} (original : Node)
      (selected : subject.nodes[index]? = some original)
      (supported : RuntimeClosedSubject.supported original = true)
      (same : shape cursor.node = shape original)
      (treeArity : cursor.tree.2.children.length = original.children.length)
      (valueArity : cursor.binding.record.checked.children.length = original.children.length)
      (children : Children checked subject cursor original.children.zipIdx) :
      Paired checked subject index cursor cursor
  | formal {index : Nat} {cursor terminal : Cursor checked} (selected : Formal cursor)
      (original : RuntimeInterval.Computed (RuntimeNativeSubject.readFormal cursor) selected)
      (child : Paired checked subject index selected.child.cursor terminal) :
      Paired checked subject index cursor terminal

inductive Children {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested)
    (subject : Description) : Cursor checked → List (Nat × Nat) → Type where
  | nil {cursor : Cursor checked} : Children checked subject cursor []
  | cons {cursor : Cursor checked} {index position : Nat} {rest : List (Nat × Nat)}
      (child : ChildRead cursor position) (terminal : Cursor checked)
      (paired : Paired checked subject index child.val.cursor terminal)
      (tail : Children checked subject cursor rest) :
      Children checked subject cursor ((index,position) :: rest)
end

/-- The terminal cursor is the actual non-formal node paired with this source
root. Its ports and action equal those of the initial cursor after every
authentically selected formal wrapper has been peeled. -/
structure At {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested)
    (subject : Description) (index : Nat) (cursor : Cursor checked) where
  terminal : Cursor checked
  paired : Paired checked subject index cursor terminal
  ports : terminal.value.input = cursor.value.input ∧ terminal.value.output = cursor.value.output
  action : terminal.value.action = cursor.value.action

theorem Paired.terminalNode {artifact catalogue context description graph implementations references prepared root requested
    checked native index cursor terminal}
    (paired : @Paired artifact catalogue context description graph implementations references prepared root requested
      checked native index cursor terminal) :
    ∃ node, native.nodes[index]? = some node ∧ shape terminal.node = shape node := by
  induction paired using Paired.rec (motive_2 := fun _ _ _ => True) with
  | node node selected _ same _ _ _ _ => exact ⟨node,selected,same⟩
  | formal _ _ _ ih => exact ih
  | nil => trivial
  | cons => trivial
/-- At any paired occurrence, the native terminal has the payload of the
node that the actual generic closure computed at this original index. Its
source child indices retain their order and any duplicates. -/
theorem Paired.originalNode {original : GenericOperation.Description} (closed : GenericOperation.Closed original)
    {artifact catalogue context description graph implementations references prepared root requested checked index cursor terminal}
    (paired : @Paired artifact catalogue context description graph implementations references prepared root requested
      checked closed.data.description index cursor terminal) :
    ∃ node row, original.nodes[index]? = some node ∧ closed.data.nodes[index]? = some row ∧
      (∃ before after,(GenericOperation.readNode node).run before = (.ok row,after)) ∧
      shape terminal.node = shape row.node ∧ row.node.children = node.children := by
  obtain ⟨actual,atIndex,same⟩ := paired.terminalNode
  obtain ⟨node,row,source,atRow,payload,read,children⟩ := closed.originalNodeAt index atIndex
  exact ⟨node,row,source,atRow,read,same.trans (congrArg shape payload.symm),
    (congrArg Node.children payload).trans children⟩

private def nodeFields (node : Node) : Nat :=
  RuntimeStructuredRoot.argumentFields {operations := [("",⟨[node],0⟩)]}

private def visitChildren {artifact catalogue context description graph implementations references prepared root requested checked}
    (subject : Description)
    (next : (index : Nat) →
      (cursor : @Cursor artifact catalogue context description graph implementations references prepared root requested checked) →
      WorkM (At checked subject index cursor))
    (cursor : Cursor checked) (pairs : List (Nat × Nat)) :
    WorkM (Children checked subject cursor pairs) :=
  let walk : Nat → (pairs : List (Nat × Nat)) → WorkM (Children checked subject cursor pairs) :=
    Nat.rec
      (fun pairs => match pairs with | [] => pure .nil | _ :: _ => throw .limit)
      (fun _ rest pairs => match pairs with
        | [] => pure .nil
        | (index,position) :: tail => do
          exactWork (Exact.charge 8)
          let child ← NaturalAffine.witness (RuntimeNativeSubject.readChild cursor position)
          let nested ← next index child.val.cursor
          let read : ChildRead cursor position := ⟨child.val,by with_reducible exact child.property⟩
          let later ← rest tail
          return .cons read nested.terminal nested.paired later)
  walk pairs.length pairs

private def visit {artifact catalogue context description graph implementations references prepared root requested checked}
    (subject : Description) : Nat → (index : Nat) →
    (cursor : @Cursor artifact catalogue context description graph implementations references prepared root requested checked) →
    WorkM (At checked subject index cursor) :=
  Nat.rec
    (fun _ _ => throw .limit)
    (fun _ next index cursor => do
      -- Source node selection is a real linked-list lookup at every visited
      -- occurrence. Native cursor readers retain their own actual work.
      exactWork (Exact.charge (16*(subject.nodes.length+1)))
      match selected : subject.nodes[index]? with
      | none => throw .request
      | some original =>
        match cursor.node with
        | .formal .. =>
          let formal ← NaturalAffine.witness (RuntimeNativeSubject.readFormal cursor)
          let child ← next index formal.val.child.cursor
          return ⟨child.terminal,.formal formal.val (by with_reducible exact formal.property) child.paired,
            ⟨child.ports.1.trans formal.val.ports.1,child.ports.2.trans formal.val.ports.2⟩,
            child.action.trans formal.val.action⟩
        | _ =>
          if supported : RuntimeClosedSubject.supported original = true then
            -- Remapping and equality inspect all retained non-edge payloads,
            -- including complete nominal source identities and argument names.
            exactWork (Exact.charge (32*(nodeFields cursor.node+nodeFields original+1)))
            if same : shape cursor.node = shape original then
              if arity : cursor.tree.2.children.length = original.children.length ∧
                  cursor.binding.record.checked.children.length = original.children.length then
                let children ← visitChildren subject next cursor original.children.zipIdx
                return ⟨cursor,.node original selected supported same arity.1 arity.2 children,
                  ⟨rfl,rfl⟩,rfl⟩
              else throw .request
            else throw .request
          else throw .request)

structure Checked {original : GenericOperation.Description} (closed : GenericOperation.Closed original)
    {artifact catalogue context description graph implementations references prepared root requested checked}
    (cursor : @Cursor artifact catalogue context description graph implementations references prepared root requested checked) where
  matched : At checked closed.data.description closed.data.description.root cursor
  traversed : RuntimeInterval.Computed (visit closed.data.description (prepared.occurrences.length+1)
    closed.data.description.root cursor) matched

/-- Specialize the occurrence theorem to the root of the transported
generic duty itself, using the root returned by the closure computation. -/
theorem Checked.originalRoot {original : GenericOperation.Description} {closed : GenericOperation.Closed original}
    {artifact catalogue context description graph implementations references prepared root requested checked cursor}
    (matched : @Checked original closed artifact catalogue context description graph implementations references
      prepared root requested checked cursor) :
    ∃ node row, original.nodes[original.root]? = some node ∧ closed.data.nodes[original.root]? = some row ∧
      (∃ before after,(GenericOperation.readNode node).run before = (.ok row,after)) ∧
      shape matched.matched.terminal.node = shape row.node ∧ row.node.children = node.children := by
  simpa only [closed.root_eq] using matched.matched.paired.originalNode closed

/-- Fuel comes from the actual native child-edge occurrence count, not a new
depth ceiling. Every recursive call follows a checked native child, including
formal selection; unsupported or incomplete shapes refuse. -/
def read {original : GenericOperation.Description} (closed : GenericOperation.Closed original)
    {artifact catalogue context description graph implementations references prepared root requested checked}
    (cursor : @Cursor artifact catalogue context description graph implementations references prepared root requested checked) :
    WorkM (Checked closed cursor) := do
  -- Sizing the depth allowance traverses the complete retained occurrence
  -- list even when this cursor selects a single-node subtree.
  let count := prepared.occurrences.length
  exactWork (Exact.charge (16*(count+1)))
  let matched ← NaturalAffine.witness (visit closed.data.description (count+1)
    closed.data.description.root cursor)
  return ⟨matched.val,by with_reducible exact matched.property⟩

end QleisliKernel.Qirf.RuntimeClosedSubject
