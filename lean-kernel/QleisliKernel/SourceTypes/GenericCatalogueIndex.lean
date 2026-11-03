import QleisliKernel.SourceTypes.GenericCatalogue

/-! One ordered index over the exact already-checked original catalogue.
Rows retain actual record indices and full original identities. Selection
compares only the visited immutable keys, then uses original-source equality;
it grants no new body, Meaning, effect, path or native evidence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.GenericCatalogueIndex
open Finite

structure OriginalEntry {sources} (catalogue : GenericCatalogue.RuntimeChecked sources) (owner name : String) where
  original : OrdinarySignature.Original sources owner name
  entry : GenericCatalogue.Entry catalogue original

structure Row {sources} (catalogue : GenericCatalogue.RuntimeChecked sources) where
  owner : String
  name : String
  value : OriginalEntry catalogue owner name

private def readRow {sources} (catalogue : GenericCatalogue.RuntimeChecked sources)
    (index : Fin catalogue.records.length) : WorkM (Row catalogue) := do
  let body := catalogue.records[index.val]'index.isLt
  exactWork (Exact.charge (16*(body.owner.utf8ByteSize+body.name.utf8ByteSize+8)))
  return ⟨body.owner,body.name,⟨body.definition.original.envelope,⟨index,HEq.rfl⟩⟩⟩

private def readRows {sources} (catalogue : GenericCatalogue.RuntimeChecked sources) :
    WorkM (Array (Row catalogue)) := do
  exactWork (Exact.charge (16*(catalogue.records.length+1)))
  return (← (List.finRange catalogue.records.length).mapM (readRow catalogue)).toArray

structure Prepared {sources} (catalogue : GenericCatalogue.RuntimeChecked sources) where
  rows : Array (Row catalogue)
  computed : ∃ before after,(readRows catalogue).run before = (.ok rows,after)
  every : rows.toList.map (fun row => row.value.entry.index) = List.finRange catalogue.records.length

def prepare {sources} (catalogue : GenericCatalogue.RuntimeChecked sources) : WorkM (Prepared catalogue) := do
  let rows ← NaturalAffine.witness (readRows catalogue)
  exactWork (Exact.charge (16*(catalogue.records.length+rows.val.size+1)))
  if every : rows.val.toList.map (fun row => row.value.entry.index) = List.finRange catalogue.records.length then
    return ⟨rows.val,by with_reducible exact rows.property,every⟩
  else throw .request

private def Row.at {sources catalogue owner name} (row : @Row sources catalogue)
    (sameOwner : row.owner = owner) (sameName : row.name = name) : OriginalEntry catalogue owner name := by
  rcases row with ⟨_,_,value⟩
  cases sameOwner
  cases sameName
  exact value

structure Selection {sources catalogue} (prepared : @Prepared sources catalogue) {owner name}
    (original : OrdinarySignature.Original sources owner name) where
  index : Fin prepared.rows.size
  sameOwner : (prepared.rows[index.val]'index.isLt).owner = owner
  sameName : (prepared.rows[index.val]'index.isLt).name = name
  sameOriginal : ((prepared.rows[index.val]'index.isLt).at sameOwner sameName).original = original

def Selection.entry {sources catalogue prepared owner name original}
    (selected : @Selection sources catalogue prepared owner name original) : GenericCatalogue.Entry catalogue original :=
  selected.sameOriginal ▸
    ((prepared.rows[selected.index.val]'selected.index.isLt).at selected.sameOwner selected.sameName).entry

private def search {sources catalogue owner name} (prepared : @Prepared sources catalogue)
    (original : OrdinarySignature.Original sources owner name) :
    List (Fin prepared.rows.size) → WorkM (Selection prepared original)
  | [] => throw .request
  | index :: rest => do
    let row := prepared.rows[index.val]'index.isLt
    exactWork (Exact.charge (16*(row.owner.utf8ByteSize+row.name.utf8ByteSize+
      owner.utf8ByteSize+name.utf8ByteSize+8)))
    if sameOwner : row.owner = owner then
      if sameName : row.name = name then
        return ⟨index,sameOwner,sameName,(row.at sameOwner sameName).original.sameSource original⟩
      else search prepared original rest
    else search prepared original rest

def read {sources catalogue owner name} (prepared : @Prepared sources catalogue)
    (original : OrdinarySignature.Original sources owner name) : WorkM (Selection prepared original) := do
  -- Constructing the ordinal range traverses it once. Each actual key
  -- comparison is then charged separately, before reading the next row.
  exactWork (Exact.charge (8*(prepared.rows.size+1)))
  search prepared original (List.finRange prepared.rows.size)

end QleisliKernel.SourceTypes.GenericCatalogueIndex
