import QleisliKernel.SourceTypes.GenericProviderEmbedding

/-! Each original child position selects a specific block in the actual
returned subject. An original DAG index can occur in several such blocks.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.GenericOperationSubstitute
open QleisliKernel.SourceTypes.GenericOperation (Node)

def Step.offsetBefore {sources app original} (parent : @Step sources app original)
    (size : Subject sources → Nat) (position : Nat) : Nat :=
  beforeSize (fun index => (parent.previous[index]?.map size).getD 0) parent.node.children position

private theorem one {sources app original parent child position j index ctor}
    {checked : @Checked sources app original} {i : Nat}
    (_parentAt : checked.result.steps[i]? = some parent) (atChild : checked.result.steps[index]? = some child)
    (order : parent.node.children = [j]) (selected : parent.node.children[position]? = some index)
    (build : ∃ row, UnaryChild checked parent j ctor row) :
    Embedded parent.result.subject child.result.subject (parent.offsetBefore nodeSize position) (parent.offsetBefore rowSize position) := by
  rw [order] at selected
  cases position with
  | zero =>
    have h : j = index := Option.some.inj selected
    obtain ⟨row,built⟩ := build
    have same := Option.some.inj (built.child.atIndex.symm.trans (h ▸ atChild : checked.result.steps[j]? = some child))
    subst row
    exact Embedded.unary built
  | succ n => simp at selected

private theorem two {sources app original parent child position j l r ctor}
    {checked : @Checked sources app original} {i : Nat}
    (parentAt : checked.result.steps[i]? = some parent) (atChild : checked.result.steps[j]? = some child)
    (kind : BinaryConstructor ctor) (source : parent.node = ctor l r)
    (selected : parent.node.children[position]? = some j) :
    Embedded parent.result.subject child.result.subject (parent.offsetBefore nodeSize position) (parent.offsetBefore rowSize position) := by
  have order : parent.node.children = [l,r] := by rw [source]; cases kind <;> rfl
  rw [order] at selected
  obtain ⟨left,right,built⟩ := checked.binary_children parentAt kind source
  cases position with
  | zero =>
    have eq : l = j := Option.some.inj selected
    have same : left = child := Option.some.inj (built.left.atIndex.symm.trans (eq ▸ atChild : checked.result.steps[l]? = some child))
    subst child
    exact Embedded.left built
  | succ p =>
    cases p with
    | zero =>
      have eq : r = j := Option.some.inj selected
      have same : right = child := Option.some.inj (built.right.atIndex.symm.trans (eq ▸ atChild : checked.result.steps[r]? = some child))
      subst child
      simpa [Step.offsetBefore,beforeSize,order,built.left.previous,nodeSize,rowSize] using Embedded.right built
    | succ p => simp at selected

private theorem operationSizes {sources app original} {checked : @Checked sources app original}
    {parent : Step app original} (size : Subject sources → Nat) {operations supplied}
    (rel : Exact.ListRel (fun (a : String × Nat) (b : String × Subject sources) => b.1 = a.1 ∧
      ∃ child, UsedChild checked parent a.2 child ∧ child.result.subject = b.2) operations supplied) :
    operations.map (fun a => (parent.previous[a.2]?.map size).getD 0) = supplied.map (fun b => size b.2) := by
  induction operations generalizing supplied with
  | nil => cases supplied <;> first | rfl | contradiction
  | cons a rest ih =>
    cases supplied with
    | nil => contradiction
    | cons b tail =>
      obtain ⟨_,child,used,same⟩ := rel.1
      simp only [List.map_cons,used.previous,Option.map_some,Option.getD_some,same,ih rel.2]

theorem Checked.childEmbedding {sources app original} (checked : @Checked sources app original)
    {i j position : Nat} {parent child : Step app original}
    (parentAt : checked.result.steps[i]? = some parent) (selected : parent.node.children[position]? = some j)
    (atChild : checked.result.steps[j]? = some child) :
    Embedded parent.result.subject child.result.subject (parent.offsetBefore nodeSize position) (parent.offsetBefore rowSize position) := by
  cases source : parent.node with
  | primitive _ _ | formal _ => simp [source,Node.children] at selected
  | inverse index => exact one parentAt atChild (by rw [source,Node.children]) selected (checked.unary_child parentAt .inverse source)
  | controlled index => exact one parentAt atChild (by rw [source,Node.children]) selected (checked.unary_child parentAt .controlled source)
  | requested index owner name =>
    exact one parentAt atChild (by rw [source,Node.children]) selected (checked.unary_child parentAt (.requested owner name) source)
  | power index count =>
    obtain ⟨row,replacement,_,_,built⟩ := checked.power_child parentAt source
    exact one parentAt atChild (by rw [source,Node.children]) selected ⟨row,built⟩
  | thenOp _ _ => exact two parentAt atChild .thenOp source selected
  | tensor _ _ => exact two parentAt atChild .tensor source selected
  | conjugate _ _ => exact two parentAt atChild .conjugate source selected
  | provider owner name bases naturals operations premises =>
    obtain ⟨b,n,ops,built⟩ := checked.provider_children parentAt source
    have offset (size : Subject sources → Nat) : parent.offsetBefore size position = beforeSize size (ops.map Prod.snd) position := by
      have sizes := operationSizes size built.operationsRead
      simpa only [Step.offsetBefore,beforeSize,source,Node.children,List.map_take,List.map_map,Function.comp_def]
        using congrArg (fun xs : List Nat => (xs.take position).sum) sizes
    rw [offset,offset]
    rw [source,Node.children,List.getElem?_map] at selected
    cases loc : operations[position]? with
    | none => simp [loc] at selected
    | some op =>
      obtain ⟨key,index⟩ := op
      have equal : index = j := by simpa only [loc,Option.map_some,Option.some.injEq] using selected
      subst index
      obtain ⟨row,found,used⟩ := built.operation_at loc
      have same := Option.some.inj (used.atIndex.symm.trans atChild)
      subst row
      exact built.embedded found

end QleisliKernel.SourceTypes.GenericOperationSubstitute
