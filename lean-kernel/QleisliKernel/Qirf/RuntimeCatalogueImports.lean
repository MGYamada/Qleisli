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

private def close {base paths} : Nat → Rows base paths → WorkM (Rows base paths) :=
  Nat.rec (fun _ => throw .limit) fun _ next held => do
    exactWork (Exact.charge (8*(paths.length+held.rows.length+1)))
    let extended ← paths.attach.foldlM add held
    if extended.rows.length == held.rows.length then return extended
    next extended

def read {sources base} (catalogue : GenericCatalogue.Checked sources)
    (retained : SourceRows.Retained base) : WorkM (Rows base (edges catalogue)) := do
  exactWork (Exact.charge (8*(catalogue.auxiliary.length+1)))
  for item in catalogue.auxiliary do
    if let .imported _ _ resolved _ := item then
      exactWork (Exact.charge (8*(resolved.visited.length+1)))
  close (sources.size+1) ⟨retained.rows,fun row member => .body ((retained.members row).mp member)⟩

end QleisliKernel.Qirf.RuntimeCatalogueImports
