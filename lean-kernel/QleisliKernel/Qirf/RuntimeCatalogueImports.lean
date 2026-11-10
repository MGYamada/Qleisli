import QleisliKernel.SourceTypes.GenericCatalogue
import QleisliKernel.SourceTypes.SourceRows

/-! Keep source rows required by imports that the original catalogue actually
resolved. Only a row already justified by the body or an earlier import may
anchor a path. Copyright 2026 Qleisli Project Contributors.
SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeCatalogueImports
open Finite SourceTypes

abbrev Row := SourceRows.Row
abbrev Edge := Row × Row

def edges {sources} (catalogue : GenericCatalogue.Checked sources) : List Edge :=
  catalogue.auxiliary.flatMap fun item =>
    match item with
    | .imported _ _ resolved _ =>
      match resolved.visited with
      | [] => []
      | first :: rest => rest.map fun target =>
        ((first.moduleName,first.source),(target.moduleName,target.source))
    | _ => []

inductive Reachable (base : List Row) (paths : List Edge) : Row → Prop where
  | body {row} (original : row ∈ base) : Reachable base paths row
  | imported {origin target} (original : (origin,target) ∈ paths)
      (anchor : Reachable base paths origin) : Reachable base paths target

structure Rows (base : List Row) (paths : List Edge) where
  rows : List Row
  reachable : ∀ row, row ∈ rows → Reachable base paths row

private def add {base paths} (held : Rows base paths) (path : {edge // edge ∈ paths}) :
    WorkM (Rows base paths) := do
  let anchor ← NaturalAffine.witness (SourceRows.contains path.val.1 held.rows)
  if found : anchor.val = true then
    let present ← SourceRows.contains path.val.2 held.rows
    if present then return held
    have reached : Reachable base paths path.val.1 := by
      obtain ⟨before,after,ran⟩ := anchor.property
      have yes := SourceRows.contains_value _ _ before after anchor.val ran
      obtain ⟨row,member,equal⟩ := List.any_eq_true.mp (yes.symm.trans found)
      have source : path.val.1 = row := beq_iff_eq.mp equal
      exact source.symm ▸ held.reachable row member
    return ⟨path.val.2 :: held.rows,by
      intro row member
      rcases List.mem_cons.mp member with equal | older
      · subst row
        exact .imported path.property reached
      · exact held.reachable row older⟩
  else return held

private theorem contains_membership (row : Row) (seen : List Row) (before after : Nat)
    (answer : Bool) (ran : (SourceRows.contains row seen).run before = (.ok answer,after)) :
    answer = true ↔ row ∈ seen := by
  rw [SourceRows.contains_value row seen before after answer ran, List.any_eq_true]
  constructor
  · rintro ⟨entry,member,same⟩
    exact (beq_iff_eq.mp same) ▸ member
  · intro member
    exact ⟨row,member,by simp⟩

private theorem add_preserves {base paths} (held output : Rows base paths) (path : {edge // edge ∈ paths})
    (before after : Nat) (ran : (add held path).run before = (.ok output,after)) :
    List.Sublist held.rows output.rows ∧ (path.val.1 ∈ held.rows → path.val.2 ∈ output.rows) := by
  obtain ⟨anchor,middle,_,tail⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨first,last,read⟩ := anchor.property
  have anchorMember := contains_membership path.val.1 held.rows first last anchor.val read
  by_cases found : anchor.val = true
  · simp only [dif_pos found] at tail
    obtain ⟨present,paid,test,rest⟩ := bind_success _ _ _ _ _ tail
    by_cases already : present = true
    · simp only [already,if_true] at rest
      have same := (pure_success _ _ _ _ rest).1
      rw [same]
      exact ⟨List.Sublist.refl _,fun _ =>
        (contains_membership path.val.2 held.rows middle paid present test).mp already⟩
    · simp only [if_neg already] at rest
      have same := (pure_success _ _ _ _ rest).1
      rw [same]
      exact ⟨List.sublist_cons_self _ _,fun _ => List.mem_cons_self⟩
  · simp only [dif_neg found] at tail
    have same := (pure_success _ _ _ _ tail).1
    rw [same]
    exact ⟨List.Sublist.refl _,fun member => False.elim (found (anchorMember.mpr member))⟩

private theorem fold_preserves {base paths} (worklist : List {edge // edge ∈ paths})
    (held output : Rows base paths) (before after : Nat)
    (ran : (worklist.foldlM add held).run before = (.ok output,after)) :
    List.Sublist held.rows output.rows ∧
      ∀ path ∈ worklist, path.val.1 ∈ held.rows → path.val.2 ∈ output.rows := by
  induction worklist generalizing held before with
  | nil =>
    have same := (pure_success held output before after ran).1
    subst output
    exact ⟨List.Sublist.refl _,by simp⟩
  | cons head tail ih =>
    obtain ⟨step,middle,first,last⟩ := bind_success _ _ _ _ _ ran
    obtain ⟨headExtends,headTarget⟩ := add_preserves held step head before middle first
    obtain ⟨tailExtends,tailTargets⟩ := ih step middle last
    refine ⟨headExtends.trans tailExtends,?_⟩
    intro path member anchor
    rcases List.mem_cons.mp member with same | later
    · subst path
      exact tailExtends.subset (headTarget anchor)
    · exact tailTargets path later (headExtends.subset anchor)

private def close {base paths} : Nat → Rows base paths → WorkM (Rows base paths) :=
  Nat.rec (fun _ => throw .limit) fun _ next held => do
    exactWork (Exact.charge (8*(paths.length+held.rows.length+1)))
    let extended ← paths.attach.foldlM add held
    if extended.rows.length == held.rows.length then return extended
    next extended

private theorem close_closed {base paths} (fuel : Nat) (held output : Rows base paths)
    (before after : Nat) (ran : (close fuel held).run before = (.ok output,after)) :
    List.Sublist held.rows output.rows ∧
      ∀ edge ∈ paths, edge.1 ∈ output.rows → edge.2 ∈ output.rows := by
  induction fuel generalizing held before with
  | zero => cases ran
  | succ fuel ih =>
    obtain ⟨_,charged,_,rest⟩ := bind_success _ _ _ _ _ ran
    obtain ⟨extended,paid,folded,finish⟩ := bind_success _ _ _ _ _ rest
    obtain ⟨extension,targets⟩ := fold_preserves paths.attach held extended charged paid folded
    by_cases stopped : (extended.rows.length == held.rows.length) = true
    · simp only [stopped,if_true] at finish
      have same := (pure_success extended output paid after finish).1
      subst output
      have unchanged := extension.eq_of_length (beq_iff_eq.mp stopped).symm
      refine ⟨extension,fun edge member anchor => ?_⟩
      exact targets ⟨edge,member⟩ (List.mem_attach _ _) (unchanged.symm ▸ anchor)
    · simp only [if_neg stopped] at finish
      obtain ⟨later,closed⟩ := ih extended paid finish
      exact ⟨extension.trans later,closed⟩

private def closeOriginal {sources} (catalogue : GenericCatalogue.Checked sources)
    (base : List Row) : WorkM (Rows base (edges catalogue)) := do
  exactWork (Exact.charge (8*(catalogue.auxiliary.length+1)))
  for item in catalogue.auxiliary do
    if let .imported _ _ resolved _ := item then
      exactWork (Exact.charge (8*(resolved.visited.length+1)))
  close (sources.size+1) ⟨base,fun _ member => .body member⟩

/-- The executable import walk returns exactly the rows reachable from the
original seeds. Multiplicity affects the work paid, not which rows qualify. -/
private theorem closeOriginal_exact {sources} (catalogue : GenericCatalogue.Checked sources) (base : List Row)
    (output : Rows base (edges catalogue)) (before after : Nat)
    (ran : (closeOriginal catalogue base).run before = (.ok output,after)) (row : Row) :
    row ∈ output.rows ↔ Reachable base (edges catalogue) row := by
  refine ⟨output.reachable row,?_⟩
  obtain ⟨_,charged,_,rest⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨_,paid,_,closedRun⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨extension,closed⟩ :=
    close_closed (sources.size+1) ⟨base,fun _ member => .body member⟩ output paid after closedRun
  intro original
  induction original with
  | body member => exact extension.subset member
  | imported member _ ih => exact closed _ member ih

private def selectRow (related kept : List Row) (row : Row) : WorkM (List Row) := do
  let includeRow ← SourceRows.contains row related
  return if includeRow then row :: kept else kept

private def selectRows (related original : List Row) : WorkM (List Row) := do
  let kept ← original.foldlM (selectRow related) []
  return kept.reverse

private theorem selectRows_fold (related original kept output : List Row) (before after : Nat)
    (ran : (original.foldlM (selectRow related) kept).run before = (.ok output,after)) (row : Row) :
    row ∈ output ↔ row ∈ kept ∨ (row ∈ original ∧ row ∈ related) := by
  induction original generalizing kept before with
  | nil =>
    have same := (pure_success kept output before after ran).1
    subst output
    simp
  | cons head tail ih =>
    obtain ⟨next,middle,step,rest⟩ := bind_success _ _ _ _ _ ran
    obtain ⟨includeRow,paid,compared,returned⟩ := bind_success _ _ _ _ _ step
    have headMembership := contains_membership head related before paid includeRow compared
    have update := (pure_success (if includeRow then head :: kept else kept) next paid middle returned).1
    subst next
    cases included : includeRow with
    | false =>
      have absent : head ∉ related := fun member => Bool.false_ne_true (included.symm.trans (headMembership.mpr member))
      simp only [included,Bool.false_eq_true,if_false] at rest
      rw [ih kept middle rest]
      simp only [List.mem_cons]
      constructor
      · rintro (prior | ⟨later,linked⟩)
        · exact Or.inl prior
        · exact Or.inr ⟨Or.inr later,linked⟩
      · rintro (prior | ⟨same | later,linked⟩)
        · exact Or.inl prior
        · exact False.elim (absent (same ▸ linked))
        · exact Or.inr ⟨later,linked⟩
    | true =>
      have present := headMembership.mp included
      simp only [included,if_true] at rest
      rw [ih (head :: kept) middle rest]
      simp only [List.mem_cons]
      constructor
      · rintro ((rfl | prior) | ⟨later,linked⟩)
        · exact Or.inr ⟨Or.inl rfl,present⟩
        · exact Or.inl prior
        · exact Or.inr ⟨Or.inr later,linked⟩
      · rintro (prior | ⟨same | later,linked⟩)
        · exact Or.inl (Or.inr prior)
        · exact Or.inl (Or.inl same)
        · exact Or.inr ⟨later,linked⟩

private theorem selectRows_exact (related original output : List Row) (before after : Nat)
    (ran : (selectRows related original).run before = (.ok output,after)) (row : Row) :
    row ∈ output ↔ row ∈ original ∧ row ∈ related := by
  obtain ⟨kept,middle,folded,returned⟩ := bind_success _ _ _ _ _ ran
  have same := (pure_success kept.reverse output middle after returned).1
  subst output
  simpa only [List.mem_reverse,List.not_mem_nil,false_or] using
    selectRows_fold related original [] kept before middle folded row

/-- The graph only queries actual artifact rows. Retain their exact
intersection with the complete closure of the original discoveries. -/
structure Coverage (sources : Sources) (base : List Row) (paths : List Edge) where
  rows : List Row
  original : ∀ row, row ∈ rows ↔ row ∈ sources.toList ∧ Reachable base paths row

def read {sources} (catalogue : GenericCatalogue.Checked sources)
    (base : List Row) : WorkM (Coverage sources base (edges catalogue)) := do
  let closed ← NaturalAffine.witness (closeOriginal catalogue base)
  -- Array traversal and output cells. Exact row comparisons pay in contains.
  exactWork (Exact.charge (8*(sources.size+1)))
  let selected ← NaturalAffine.witness (selectRows closed.val.rows sources.toList)
  return ⟨selected.val,by
    intro row
    obtain ⟨a,b,closedRun⟩ := closed.property
    obtain ⟨c,d,selectedRun⟩ := selected.property
    exact (selectRows_exact _ _ _ c d selectedRun row).trans
      (and_congr_right' (closeOriginal_exact _ _ _ a b closedRun row))⟩

#print axioms read

end QleisliKernel.Qirf.RuntimeCatalogueImports
