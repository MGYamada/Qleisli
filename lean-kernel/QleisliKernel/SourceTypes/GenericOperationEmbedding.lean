import QleisliKernel.SourceTypes.GenericOperationSubstitute

/-! An output block of an actual substitution assembly. Node offsets index
the assembled graph; row offsets index its ordered supplier list. An input
DAG can share children and need not have contiguous subgraphs.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.GenericOperationSubstitute
open QleisliKernel.SourceTypes.GenericOperation (Node Description)

structure Embedded {sources} (whole part : Subject sources) (nodeOffset rowOffset : Nat) : Prop where
  nodeAt : ∀ {i : Nat} {node : Node}, part.description.nodes[i]? = some node →
    whole.description.nodes[i+nodeOffset]? = some (node.remap (·+nodeOffset))
  originAt : ∀ {row index : Nat} {origin : GenericOperation.Origin sources},
    part.suppliers[row]? = some (index,origin) →
    whole.suppliers[row+rowOffset]? = some (index+nodeOffset,origin)

private theorem pairsAdd (xs : List (String × Nat)) (a b : Nat) :
    (xs.map (fun (name,i) => (name,i+a))).map (fun (name,i) => (name,i+b)) =
      xs.map (fun (name,i) => (name,i+(a+b))) := by
  induction xs with
  | nil => rfl
  | cons p xs ih => obtain ⟨name,i⟩ := p; simp only [List.map_cons,Nat.add_assoc,ih]

private theorem remapId (node : Node) : node.remap (fun i => i) = node := by
  cases node <;> simp [Node.remap]

private theorem remapAdd (node : Node) (a b : Nat) :
    (node.remap (·+a)).remap (·+b) = node.remap (·+(a+b)) := by
  cases node <;> simp only [Node.remap,pairsAdd,Nat.add_assoc]

theorem Embedded.root {sources} (subject : Subject sources) : Embedded subject subject 0 0 where
  nodeAt found := by simpa only [Nat.add_zero,remapId] using found
  originAt found := by simpa only [Nat.add_zero] using found

theorem Embedded.trans {sources whole middle part a b c d}
    (outer : @Embedded sources whole middle b d) (inner : Embedded middle part a c) :
    Embedded whole part (a+b) (c+d) where
  nodeAt found := by simpa only [Nat.add_assoc,remapAdd] using outer.nodeAt (inner.nodeAt found)
  originAt found := by simpa only [Nat.add_assoc] using outer.originAt (inner.originAt found)

private theorem inFirst {α : Type} {block suffix : List α} {i : Nat} {x : α}
    (found : block[i]? = some x) : (block ++ suffix)[i]? = some x :=
  (List.getElem?_append_left ((List.getElem?_eq_some_iff.mp found).choose)).trans found

private theorem inNext {α : Type} {pre block suffix : List α} {i : Nat} {x : α}
    (found : block[i]? = some x) : (pre ++ (block ++ suffix))[i+pre.length]? = some x := by
  rw [List.getElem?_append_right (by omega : pre.length ≤ i+pre.length)]
  simpa only [Nat.add_sub_cancel] using inFirst (suffix := suffix) found

theorem Embedded.unary {sources application original checked parent i ctor child}
    (built : @UnaryChild sources application original checked parent i ctor child) :
    Embedded parent.result.subject child.result.subject 0 0 where
  nodeAt found := by
    rw [built.description]
    simp only [Description.unary,Nat.add_zero,remapId]
    exact inFirst found
  originAt found := by
    rw [built.suppliers]
    exact inFirst found

theorem Embedded.left {sources application original checked parent l r ctor left right}
    (built : @BinaryChildren sources application original checked parent l r ctor left right) :
    Embedded parent.result.subject left.result.subject 0 0 where
  nodeAt found := by
    rw [built.description]
    simp only [Description.binary,List.append_assoc,Nat.add_zero,remapId]
    exact inFirst found
  originAt found := by
    rw [built.suppliers]
    simp only [List.append_assoc,Nat.add_zero]
    exact inFirst found

theorem Embedded.right {sources application original checked parent l r ctor left right}
    (built : @BinaryChildren sources application original checked parent l r ctor left right) :
    Embedded parent.result.subject right.result.subject
      left.result.subject.description.nodes.length left.result.subject.suppliers.length where
  nodeAt found := by
    rw [built.description]
    simp only [Description.binary,List.append_assoc]
    apply inNext
    rw [List.getElem?_map,found,Option.map_some]
  originAt found := by
    rw [built.suppliers]
    simp only [List.append_assoc]
    apply inNext
    rw [List.getElem?_map,found,Option.map_some]

/-- A repeated input index selects one actual fold row twice. The two output
blocks retain both sets of positions and origin rows, with no uniqueness or
equality assumption on the origins themselves. -/
theorem repeated {sources application original} (checked : @Checked sources application original)
    {i j : Nat} {parent : Step application original} {ctor : Nat → Nat → Node}
    (atParent : checked.result.steps[i]? = some parent) (kind : BinaryConstructor ctor)
    (source : parent.node = ctor j j) :
    ∃ child, UsedChild checked parent j child ∧
      Embedded parent.result.subject child.result.subject 0 0 ∧
      Embedded parent.result.subject child.result.subject
        child.result.subject.description.nodes.length child.result.subject.suppliers.length := by
  obtain ⟨left,right,built⟩ := checked.binary_children atParent kind source
  have same : left = right := Option.some.inj (built.left.atIndex.symm.trans built.right.atIndex)
  subst right
  exact ⟨left,built.left,Embedded.left built,Embedded.right built⟩

end QleisliKernel.SourceTypes.GenericOperationSubstitute
