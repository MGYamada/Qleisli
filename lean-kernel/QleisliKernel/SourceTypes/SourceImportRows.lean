import QleisliKernel.SourceTypes.GenericCatalogue
import QleisliKernel.SourceTypes.SourceRows

/-! Selected original import dependencies. The complete catalogue is still
checked first; only imports rooted in actually consulted module rows contribute
relevance. Each edge retains its original resolver execution. No runtime body,
provider, Meaning or access obligation is discharged by this projection.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceImportRows
open Finite
abbrev Row := SourceRows.Row

structure Import {sources} (catalogue : GenericCatalogue.Checked sources) where
  owner : String
  name : String
  resolution : Resolved
  read : ∃ before after,
    (resolveReference sources owner [name]).run before = (.ok resolution,after)
  original : GenericCatalogue.Auxiliary.imported owner name resolution read ∈ catalogue.auxiliary

def Import.rows {sources catalogue} (entry : @Import sources catalogue) : List Row :=
  ResolutionProvenance.sourceRows entry.resolution

/-- The real original import reads, without granting their rows relevance. -/
def imports {sources} (catalogue : GenericCatalogue.Checked sources) : List (Import catalogue) :=
  catalogue.auxiliary.attach.filterMap fun entry => match entry with
    | ⟨.imported owner name resolution read,member⟩ => some ⟨owner,name,resolution,read,member⟩
    | _ => none

inductive Rooted {sources} (catalogue : GenericCatalogue.Checked sources) (seeds : List Row) : Row → Prop where
  | seed {row} (member : row ∈ seeds) : Rooted catalogue seeds row
  | imported {parent row} (reached : Rooted catalogue seeds parent) (entry : Import catalogue)
      (sameOwner : entry.owner = parent.1) (member : row ∈ entry.rows) : Rooted catalogue seeds row

structure Pending {sources} (catalogue : GenericCatalogue.Checked sources) (seeds : List Row) where
  row : Row
  rooted : Rooted catalogue seeds row

structure Module {sources} (catalogue : GenericCatalogue.Checked sources) (seeds : List Row) where
  owner : String
  original : SourceModules.Module sources owner
  read : ∃ before after,
    (SourceModules.lookup catalogue.modulesContext owner).run before = (.ok original,after)
  rooted : Rooted catalogue seeds (owner,original.source)
  selected : List (Import catalogue)
  allImports : selected = (imports catalogue).filter (·.owner == owner)

def Module.row {sources catalogue seeds} (entry : @Module sources catalogue seeds) : Row :=
  (entry.owner,entry.original.source)

def Module.rows {sources catalogue seeds} (entry : @Module sources catalogue seeds) : List Row :=
  entry.selected.flatMap (·.rows)

theorem Module.rows_rooted {sources catalogue seeds} (entry : @Module sources catalogue seeds)
    (row : Row) (member : row ∈ entry.rows) : Rooted catalogue seeds row := by
  obtain ⟨edge,present,member⟩ := List.mem_flatMap.mp member
  have selected : edge ∈ (imports catalogue).filter (·.owner == entry.owner) := by
    rw [← entry.allImports]
    exact present
  have same : edge.owner = entry.owner := beq_iff_eq.mp (List.mem_filter.mp selected).2
  exact .imported entry.rooted edge same member

private def bytes (row : Row) : Nat := row.1.utf8ByteSize + row.2.utf8ByteSize

private def readModule {sources} (catalogue : GenericCatalogue.Checked sources) {seeds}
    (current : Pending catalogue seeds) : WorkM {entry : Module catalogue seeds // entry.row = current.row} := do
  let original ← NaturalAffine.witness (SourceModules.lookup catalogue.modulesContext current.row.1)
  exactWork (Exact.charge (8*(bytes current.row+current.row.1.utf8ByteSize+original.val.source.utf8ByteSize+1)))
  if same : current.row = (current.row.1,original.val.source) then
    exactWork (Exact.charge (16*(catalogue.auxiliary.length+1)))
    let available := imports catalogue
    -- Only owner keys are compared by the filter. Full source comparisons are
    -- charged separately above and when consulting the visited modules.
    exactWork (Exact.charge (8*((available.map fun edge => edge.owner.utf8ByteSize+1).sum+
      (available.length+1)*(current.row.1.utf8ByteSize+1)+1)))
    let selected := available.filter (·.owner == current.row.1)
    pure ⟨⟨current.row.1,original.val,by with_reducible exact original.property,
      same ▸ current.rooted,selected,rfl⟩,same.symm⟩
  else throw .request

private def children {sources catalogue seeds} (entry : @Module sources catalogue seeds) : List (Pending catalogue seeds) :=
  entry.rows.attach.map fun row => ⟨row.val,entry.rows_rooted row.val row.property⟩

/-- Every original seed and every import discovered so far is either
already validated against its original module or still on the work list. -/
private def Covered {sources catalogue seeds} (modules : List (@Module sources catalogue seeds))
    (pending : List (Pending catalogue seeds)) : Prop :=
  ∀ row, row ∈ seeds ++ modules.flatMap Module.rows →
    row ∈ modules.map Module.row ∨ row ∈ pending.map Pending.row

structure Closure {sources} (catalogue : GenericCatalogue.Checked sources) (seeds : List Row) where
  modules : List (Module catalogue seeds)
  complete : ∀ row, row ∈ seeds ++ modules.flatMap Module.rows → row ∈ modules.map Module.row

private theorem skipCovered {sources catalogue seeds} {current : @Pending sources catalogue seeds}
    {rest checked} (invariant : Covered checked (current :: rest))
    (known : current.row ∈ checked.map Module.row) : Covered checked rest := by
  intro row member
  rcases invariant row member with done | pending
  · exact Or.inl done
  · rcases List.mem_cons.mp pending with same | waiting
    · exact Or.inl (same ▸ known)
    · exact Or.inr waiting

private theorem addCovered {sources catalogue seeds} {current : @Pending sources catalogue seeds}
    {rest checked} (invariant : Covered checked (current :: rest)) (entry : Module catalogue seeds)
    (same : entry.row = current.row) : Covered (checked ++ [entry]) (rest ++ children entry) := by
  intro row member
  simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.map_append,List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false] at member ⊢
  have prior (old : row ∈ seeds ++ checked.flatMap Module.rows) :
      (row ∈ checked.map Module.row ∨ row = entry.row) ∨
      (row ∈ rest.map Pending.row ∨ row ∈ (children entry).map Pending.row) := by
    rcases invariant row old with done | waiting
    · exact Or.inl (Or.inl done)
    · rcases List.mem_cons.mp waiting with first | later
      · exact Or.inl (Or.inr (first.trans same.symm))
      · exact Or.inr (Or.inl later)
  rcases member with seed | old | child
  · exact prior (List.mem_append_left _ seed)
  · exact prior (List.mem_append_right _ old)
  · exact Or.inr (Or.inr (by simpa [children,List.map_map,Function.comp_def] using child))

private def finish {sources catalogue seeds} (checked : List (@Module sources catalogue seeds))
    (invariant : Covered checked []) : Closure catalogue seeds :=
  ⟨checked,by intro row h; simpa using invariant row h⟩

private def visit {sources} (catalogue : GenericCatalogue.Checked sources) (seeds : List Row) :
    Nat → (pending : List (Pending catalogue seeds)) → (checked : List (Module catalogue seeds)) →
      Covered checked pending → WorkM (Closure catalogue seeds) :=
  Nat.rec (fun pending checked => match pending with
      | [] => fun invariant => pure (finish checked invariant)
      | _ :: _ => fun _ => throw .limit)
    (fun _ next pending checked invariant => do
      exactWork (Exact.charge (8*(pending.length+checked.length+1)))
      match pending with
      | [] => pure (finish checked invariant)
      | current :: rest =>
        let keys := checked.map Module.row
        let test ← NaturalAffine.witness (SourceRows.contains current.row keys)
        match found : test.val with
        | true =>
          have known : current.row ∈ keys := by
            obtain ⟨before,after,read⟩ := test.property
            have yes := (SourceRows.contains_value current.row keys before after test.val read).symm.trans found
            obtain ⟨key,member,equal⟩ := List.any_eq_true.mp yes
            exact (beq_iff_eq.mp equal) ▸ member
          next rest checked (skipCovered invariant known)
        | false =>
          let entry ← readModule catalogue current
          let more := children entry.val
          exactWork (Exact.charge (8*(rest.length+more.length+checked.length+1)))
          next (rest ++ more) (checked ++ [entry.val]) (addCovered invariant entry.val entry.property))

private def start {sources} (catalogue : GenericCatalogue.Checked sources) (seeds : List Row) :
    WorkM (Closure catalogue seeds) := do
  exactWork (Exact.charge (16*(catalogue.auxiliary.length+seeds.length+1)))
  let fuel := seeds.length+((imports catalogue).map fun edge => edge.rows.length).sum+1
  exactWork (Exact.charge (8*(fuel+1)))
  visit catalogue seeds fuel (seeds.attach.map fun row => ⟨row.val,Rooted.seed row.property⟩) [] (by
    intro row member
    right
    simpa [List.map_map,Function.comp_def] using member)

structure Checked {sources} (catalogue : GenericCatalogue.Checked sources) (seeds : List Row)
    extends Closure catalogue seeds where
  traversal : ∃ before after,(start catalogue seeds).run before = (.ok toClosure,after)

def Checked.rows {sources catalogue seeds} (checked : @Checked sources catalogue seeds) : List Row :=
  checked.modules.map Module.row

theorem Checked.everyRow {sources catalogue seeds} (checked : @Checked sources catalogue seeds)
    (row : Row) (member : row ∈ checked.rows) :
    ∃ entry ∈ checked.modules,row = entry.row := by
  obtain ⟨entry,present,same⟩ := List.mem_map.mp member
  exact ⟨entry,present,same.symm⟩

theorem Checked.rows_rooted {sources catalogue seeds} (checked : @Checked sources catalogue seeds)
    (row : Row) (member : row ∈ checked.rows) : Rooted catalogue seeds row := by
  obtain ⟨entry,_,rfl⟩ := checked.everyRow row member
  exact entry.rooted

def read {sources} (catalogue : GenericCatalogue.Checked sources) (seeds : List Row) :
    WorkM (Checked catalogue seeds) := do
  let result ← NaturalAffine.witness (start catalogue seeds)
  exactWork (Exact.charge (8*(result.val.modules.length+1)))
  pure ⟨result.val,by with_reducible exact result.property⟩

end QleisliKernel.SourceTypes.SourceImportRows
