import QleisliKernel.SourceTypes.GenericOperationEmbedding
import QleisliKernel.SourceTypes.GenericProviderChildren

/-! Project a positioned block of the actual provider assembly. Its node
offset and supplier-row offset account for every preceding Op argument.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.GenericOperationSubstitute
open QleisliKernel.SourceTypes.GenericOperation (Node Description)

def beforeSize {α : Type} (size : α → Nat) (items : List α) (position : Nat) : Nat :=
  ((items.take position).map size).sum

private theorem upto {B : Type} {rows suffix : List B} {i : Nat} {x : B} (atIndex : rows[i]? = some x) :
    (rows ++ suffix)[i]? = some x :=
  (List.getElem?_append_left ((List.getElem?_eq_some_iff.mp atIndex).choose)).trans atIndex

private theorem preserved {S A B : Type} (advance : S → A → S) (rows : S → List B)
    (more : ∀ s a, ∃ added, rows (advance s a) = rows s ++ added)
    (items : List A) (s : S) {i : Nat} {x : B} (old : (rows s)[i]? = some x) :
    (rows (items.foldl advance s))[i]? = some x := by
  induction items generalizing s with
  | nil => exact old
  | cons a rest ih =>
    obtain ⟨added,h⟩ := more s a
    apply ih (advance s a)
    rw [h,List.getElem?_append_left ((List.getElem?_eq_some_iff.mp old).choose),old]

private theorem blockAt {S A B : Type} (advance : S → A → S) (rows : S → List B)
    (offset : S → Nat) (width : A → Nat) (block : A → List B) (shift : Nat → B → B)
    (moved : ∀ s a, offset (advance s a) = offset s + width a)
    (appended : ∀ s a, rows (advance s a) = rows s ++ (block a).map (shift (offset s)))
    (items : List A) (s : S) {position i : Nat} {a : A} {x : B}
    (selected : items[position]? = some a) (atRow : (block a)[i]? = some x) :
    (rows (items.foldl advance s))[i+((rows s).length+beforeSize (fun v => (block v).length) items position)]? =
      some (shift (offset s+beforeSize width items position) x) := by
  induction items generalizing s position with
  | nil => simp at selected
  | cons first rest ih =>
    cases position with
    | zero =>
      have same : first = a := Option.some.inj selected
      subst first
      simp only [List.foldl_cons,beforeSize,List.take_zero,List.map_nil,List.sum_nil,Nat.add_zero]
      apply preserved advance rows (fun s a => ⟨_,appended s a⟩) rest
      rw [appended,List.getElem?_append_right (by omega : (rows s).length ≤ i+(rows s).length)]
      simp only [Nat.add_sub_cancel,List.getElem?_map,atRow,Option.map_some]
    | succ p =>
      have shifted := ih (advance s first) selected
      rw [moved,appended,List.length_append,List.length_map] at shifted
      simpa only [List.foldl_cons,beforeSize,List.take_succ_cons,List.map_cons,List.sum_cons,Nat.add_assoc] using shifted

private abbrev GraphState := List Node × List (String × Nat) × List NaturalFrames.Frame

private def addNodes {sources} (s : GraphState) (a : String × Subject sources) : GraphState :=
  let d := a.2.description
  (s.1 ++ d.nodes.map (Node.remap (·+s.1.length)),s.2.1 ++ [(a.1,d.root+s.1.length)],s.2.2 ++ d.nodeFrames)

private def addSuppliers {sources} (s : Nat × List (Nat × GenericOperation.Origin sources)) (a : String × Subject sources) :=
  (s.1+a.2.description.nodes.length,s.2 ++ a.2.suppliers.map (fun (j,origin) => (j+s.1,origin)))

def nodeSize {sources} (s : Subject sources) := s.description.nodes.length
def rowSize {sources} (s : Subject sources) := s.suppliers.length

theorem ProviderChildren.embedded {sources app original checked parent owner name bases naturals operations premises
    basisRows naturalRows supplied}
    (built : @ProviderChildren sources app original checked parent owner name bases naturals operations premises basisRows naturalRows supplied)
    {position : Nat} {arg : String} {part : Subject sources} (atPosition : supplied[position]? = some (arg,part)) :
    Embedded parent.result.subject part (beforeSize nodeSize (supplied.map Prod.snd) position)
      (beforeSize rowSize (supplied.map Prod.snd) position) := by
  have before (size : Subject sources → Nat) :
      beforeSize size (supplied.map Prod.snd) position = beforeSize (fun a => size a.2) supplied position := by
    simp only [beforeSize,List.map_take,List.map_map,Function.comp_def]
  rw [before,before]
  constructor
  · intro i node found
    rw [built.description]
    simp only [GenericOperation.provider,List.foldl_map]
    apply upto
    simpa only [List.length_nil,Nat.zero_add] using blockAt addNodes Prod.fst (fun s => s.1.length)
      (fun a => nodeSize a.2) (fun a => a.2.description.nodes) (fun offset n => n.remap (·+offset))
      (fun s a => by simp [addNodes,nodeSize]) (fun _ _ => rfl) supplied ([],[],[]) atPosition found
  · intro i j origin found
    have inBlock := blockAt addSuppliers Prod.snd Prod.fst (fun a => nodeSize a.2) (fun a => a.2.suppliers)
      (fun offset (v : Nat × GenericOperation.Origin sources) => (v.1+offset,v.2))
      (fun _ _ => rfl) (fun _ _ => rfl) supplied (0,[]) atPosition found
    rw [built.suppliers]
    apply upto
    simpa only [List.length_nil,Nat.zero_add] using inBlock

end QleisliKernel.SourceTypes.GenericOperationSubstitute
