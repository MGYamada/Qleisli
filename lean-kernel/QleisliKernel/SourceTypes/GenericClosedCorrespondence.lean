import QleisliKernel.SourceTypes.GenericOperation
import QleisliKernel.FiniteRestriction.Check

/-! Node correspondence for the actual successful generic closure.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.GenericOperation
open Finite

/-- Closing a node preserves its ordered outgoing operation indices. -/
theorem readNode_children {node : Node} {row : NodeClosed} {before after : Nat}
    (ran : (readNode node).run before = (.ok row,after)) :
    row.node.children = node.children := by
  cases node <;> simp only [readNode] at ran
  case formal => cases ran
  case primitive =>
    obtain ⟨_,_,_,tail⟩ := bind_success _ _ _ _ _ ran
    rw [(pure_success _ _ _ _ tail).1] <;> rfl
  case provider =>
    obtain ⟨_,_,_,tail⟩ := bind_success _ _ _ _ _ ran
    obtain ⟨_,_,_,tail⟩ := bind_success _ _ _ _ _ tail
    rw [(pure_success _ _ _ _ tail).1] <;> rfl
  case power =>
    obtain ⟨_,_,_,tail⟩ := bind_success _ _ _ _ _ ran
    split at tail
    · obtain ⟨_,_,_,tail⟩ := bind_success _ _ _ _ _ tail
      obtain ⟨_,_,_,tail⟩ := bind_success _ _ _ _ _ tail
      rw [(pure_success _ _ _ _ tail).1] <;> rfl
    · obtain ⟨_,_,_,tail⟩ := bind_success _ _ _ _ _ tail
      rw [(pure_success _ _ _ _ tail).1] <;> rfl
  all_goals rw [(pure_success _ _ _ _ ran).1] <;> rfl

private theorem Closed.trace {original : Description} (closed : Closed original) :
    closed.data.description.root = original.root ∧
    ∃ before after, (original.nodes.mapM readNode).run before = (.ok closed.data.nodes,after) := by
  obtain ⟨_,_,ran⟩ := closed.computed
  unfold readClosedData at ran
  obtain ⟨_,_,_,tail⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨_,_,_,tail⟩ := bind_success _ _ _ _ _ tail
  obtain ⟨_,beforeMap,_,tail⟩ := bind_success _ _ _ _ _ tail
  obtain ⟨rows,afterMap,mapped,tail⟩ := bind_success _ _ _ _ _ tail
  obtain ⟨_,_,_,tail⟩ := bind_success _ _ _ _ _ tail
  obtain ⟨_,_,_,tail⟩ := bind_success _ _ _ _ _ tail
  obtain ⟨_,_,_,tail⟩ := bind_success _ _ _ _ _ tail
  have result := (pure_success _ _ _ _ tail).1
  exact ⟨congrArg (fun data : ClosedData => data.description.root) result,
    ⟨beforeMap,afterMap,by rw [result]; exact mapped⟩⟩

theorem Closed.root_eq {original : Description} (closed : Closed original) :
    closed.data.description.root = original.root := closed.trace.1

private abbrev WasRead (node : Node) (row : NodeClosed) :=
  ∃ before after, (readNode node).run before = (.ok row,after)

private theorem Closed.related {original : Description} (closed : Closed original) :
    Exact.ListRel WasRead original.nodes closed.data.nodes := by
  obtain ⟨before,after,mapped⟩ := closed.trace.2
  exact FiniteRestriction.mapM_relation readNode WasRead
    (fun _ _ start stop ran => ⟨start,stop,ran⟩) _ _ before after mapped

/-- Lookup from the original graph returns the row of the actual closed run. -/
theorem Closed.closedNodeAt {original : Description} (closed : Closed original) (index : Nat)
    {node : Node} (selected : original.nodes[index]? = some node) :
    ∃ row : NodeClosed, closed.data.nodes[index]? = some row ∧
      closed.data.description.nodes[index]? = some row.node ∧
      (∃ before after, (readNode node).run before = (.ok row,after)) ∧
      row.node.children = node.children := by
  obtain ⟨inside,originalEq⟩ := List.getElem?_eq_some_iff.mp selected
  have related := closed.related
  have bound : index < closed.data.nodes.length := by
    rw [Exact.listRel_length _ _ _ related]
    exact inside
  let row := closed.data.nodes[index]'bound
  have selectedRow : closed.data.nodes[index]? = some row := List.getElem?_eq_getElem bound
  have actual : closed.data.description.nodes[index]? = some row.node := by
    rw [← closed.data.retained,List.getElem?_map,selectedRow] <;> rfl
  have ran : WasRead node row := originalEq ▸ Exact.listRel_getElem _ _ _ related index inside
  obtain ⟨before,after,ran⟩ := ran
  exact ⟨row,selectedRow,actual,⟨before,after,ran⟩,readNode_children ran⟩

/-- An interior closed node identifies its original node and its actual closure row
at the same graph index, including repeated or identical subtrees. -/
theorem Closed.originalNodeAt {original : Description} (closed : Closed original) (index : Nat)
    {actual : OperationDescription.Node} (selected : closed.data.description.nodes[index]? = some actual) :
    ∃ (node : Node) (row : NodeClosed), original.nodes[index]? = some node ∧
      closed.data.nodes[index]? = some row ∧ row.node = actual ∧
      (∃ before after, (readNode node).run before = (.ok row,after)) ∧
      actual.children = node.children := by
  obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp selected
  rw [← closed.data.retained,List.length_map,Exact.listRel_length _ _ _ closed.related] at bound
  have originalAt := List.getElem?_eq_getElem bound
  obtain ⟨row,rowAt,rowNodeAt,ran,children⟩ := closed.closedNodeAt index originalAt
  have same := Option.some.inj (rowNodeAt.symm.trans selected)
  exact ⟨_,row,originalAt,rowAt,same,ran,same ▸ children⟩

end QleisliKernel.SourceTypes.GenericOperation
