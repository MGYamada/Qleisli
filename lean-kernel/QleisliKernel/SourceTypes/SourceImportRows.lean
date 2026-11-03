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

private def seen {sources catalogue seeds} (row : Row) (modules : List (@Module sources catalogue seeds)) : WorkM Bool :=
  modules.anyM fun entry => SourceRows.equal row entry.row

private def readModule {sources} (catalogue : GenericCatalogue.Checked sources) {seeds}
    (current : Pending catalogue seeds) : WorkM (Module catalogue seeds) := do
  let original ← NaturalAffine.witness (SourceModules.lookup catalogue.modulesContext current.row.1)
  exactWork (Exact.charge (8*(bytes current.row+current.row.1.utf8ByteSize+original.val.source.utf8ByteSize+1)))
  if same : current.row = (current.row.1,original.val.source) then
    exactWork (Exact.charge (16*(catalogue.auxiliary.length+1)))
    let available := imports catalogue
    -- Only owner keys are compared by the filter. Full source comparisons are
    -- charged separately above and by the row retainer below.
    exactWork (Exact.charge (8*((available.map fun edge => edge.owner.utf8ByteSize+1).sum+
      (available.length+1)*(current.row.1.utf8ByteSize+1)+1)))
    let selected := available.filter (·.owner == current.row.1)
    pure ⟨current.row.1,original.val,by with_reducible exact original.property,
      same ▸ current.rooted,selected,rfl⟩
  else throw .request

private def children {sources catalogue seeds} (entry : @Module sources catalogue seeds) : List (Pending catalogue seeds) :=
  entry.rows.attach.map fun row => ⟨row.val,entry.rows_rooted row.val row.property⟩

private def visit {sources} (catalogue : GenericCatalogue.Checked sources) (seeds : List Row) :
    Nat → List (Pending catalogue seeds) → List (Module catalogue seeds) → WorkM (List (Module catalogue seeds)) :=
  Nat.rec (fun pending selected => if pending.isEmpty then pure selected else throw .limit)
    (fun _ next pending selected => do
      exactWork (Exact.charge (8*(pending.length+selected.length+1)))
      match pending with
      | [] => pure selected
      | current :: rest =>
        if ← seen current.row selected then next rest selected else
          let entry ← readModule catalogue current
          let more := children entry
          exactWork (Exact.charge (8*(rest.length+more.length+selected.length+1)))
          next (rest ++ more) (selected ++ [entry]))

def rawRows {sources catalogue seeds} (modules : List (@Module sources catalogue seeds)) : List Row :=
  seeds ++ modules.flatMap (·.rows)

structure Checked {sources} (catalogue : GenericCatalogue.Checked sources) (seeds : List Row) where
  modules : List (Module catalogue seeds)
  traversal : ∃ before after,
    (visit catalogue seeds (seeds.length+((imports catalogue).map fun edge => edge.rows.length).sum+1)
      (seeds.attach.map fun row => ⟨row.val,Rooted.seed row.property⟩) []).run before = (.ok modules,after)
  relevance : SourceRows.Retained (rawRows modules)
  complete : relevance.rows.all (fun row => modules.any (fun entry => row == entry.row)) = true

def Checked.rows {sources catalogue seeds} (checked : @Checked sources catalogue seeds) : List Row :=
  checked.relevance.rows

theorem Checked.seeds_retained {sources catalogue seeds} (checked : @Checked sources catalogue seeds)
    (row : Row) (member : row ∈ seeds) : row ∈ checked.rows :=
  (checked.relevance.members row).mpr (List.mem_append.mpr (.inl member))

theorem Checked.rows_rooted {sources catalogue seeds} (checked : @Checked sources catalogue seeds)
    (row : Row) (member : row ∈ checked.rows) : Rooted catalogue seeds row := by
  have raw := (checked.relevance.members row).mp member
  rcases List.mem_append.mp raw with seed | imported
  · exact .seed seed
  · obtain ⟨entry,present,member⟩ := List.mem_flatMap.mp imported
    exact entry.rows_rooted row member

/-- Every output row was processed as its complete, exact original module.
Combined with Module.allImports this includes every import of every reachable
module, while rows unrelated to the consulted seeds have no Rooted derivation. -/
theorem Checked.everyRow {sources catalogue seeds} (checked : @Checked sources catalogue seeds)
    (row : Row) (member : row ∈ checked.rows) :
    ∃ entry ∈ checked.modules,row = entry.row := by
  have covered := (List.all_eq_true.mp checked.complete) row member
  obtain ⟨entry,present,same⟩ := List.any_eq_true.mp covered
  exact ⟨entry,present,beq_iff_eq.mp same⟩

/-- Check coverage against the modules reached by the original import traversal.
Each candidate is compared using its module name before reading source bytes. -/
private def covered (available : List Row) (rows : List Row) : WorkM Bool :=
  rows.allM fun row => SourceRows.contains row available

private theorem covered_value (available rows : List Row) (before after : Nat) (answer : Bool)
    (ran : (covered available rows).run before = (.ok answer,after)) :
    answer = rows.all (fun row => available.any (row == ·)) := by
  induction rows generalizing before with
  | nil => exact (pure_success true _ _ _ ran).1
  | cons row rest ih =>
    obtain ⟨found,middle,test,tail⟩ := bind_success _ _ before after answer ran
    have same := SourceRows.contains_value row available before middle found test
    cases found with
    | true => simpa [List.all_cons,← same] using ih middle tail
    | false => simpa [List.all_cons,← same] using (pure_success false _ _ _ tail).1

def read {sources} (catalogue : GenericCatalogue.Checked sources) (seeds : List Row) :
    WorkM (Checked catalogue seeds) := do
  exactWork (Exact.charge (16*(catalogue.auxiliary.length+seeds.length+1)))
  let fuel := seeds.length+((imports catalogue).map fun edge => edge.rows.length).sum+1
  exactWork (Exact.charge (8*(fuel+1)))
  let modules ← NaturalAffine.witness (visit catalogue seeds fuel
    (seeds.attach.map fun row => ⟨row.val,Rooted.seed row.property⟩) [])
  let relevance ← SourceRows.read (rawRows (seeds := seeds) modules.val)
  let available : List Row := modules.val.map Module.row
  let checked ← NaturalAffine.witness (α := Bool) (covered available relevance.rows)
  match complete : checked.val with
  | true =>
    pure ⟨modules.val,by with_reducible exact modules.property,relevance,by
      obtain ⟨before,after,ran⟩ := checked.property
      have members := (covered_value available relevance.rows before after checked.val ran).symm.trans complete
      simpa only [available,List.any_map,Function.comp_def] using members⟩
  | false => throw .request

end QleisliKernel.SourceTypes.SourceImportRows
