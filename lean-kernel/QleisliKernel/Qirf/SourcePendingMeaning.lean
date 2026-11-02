import QleisliKernel.SourceTypes.GenericCatalogue

/-! Withhold original concrete Meaning assertions until native consumption.
The complete source-indexed occurrence list and its actual symbolic closure
executions are retained. A free original Basis/Nat/Op key is not guessed, and a
closed type or a declaration header does not classify an operation as concrete.
This staged guard proves no Meaning equation or access/body obligation; those
require the same-final-root native continuation before admission is enabled.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourcePendingMeaning
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes

def unconsumed {sources catalogue} (entry : @GenericCatalogue.DutyAt sources catalogue) : Bool :=
  match entry.duty.requirement,entry.status with
  | .meaning _,.closed _ => true
  | _,_ => false

structure Checked {sources} (catalogue : GenericCatalogue.Checked sources) where
  duties : GenericCatalogue.Duties catalogue
  original : ∃ before after,(GenericCatalogue.readDuties catalogue).run before = (.ok duties,after)
  withheld : duties.entries.all (fun entry => !unconsumed entry) = true

/-- Existing legacy and undispatched body preparations share this refusal.
Every concrete Meaning assertion remains unavailable until its actual source
subject and reference equations are consumed. Conditional closures retain their
exact free keys; retained access duties are not claimed discharged here. -/
def read {sources} (catalogue : GenericCatalogue.Checked sources) : WorkM (Checked catalogue) := do
  let duties ← NaturalAffine.witness (GenericCatalogue.readDuties catalogue)
  exactWork (Exact.charge (32*(catalogue.records.length+duties.val.entries.length+1)^2))
  if withheld : duties.val.entries.all (fun entry => !unconsumed entry) = true then
    return ⟨duties.val,by with_reducible exact duties.property,withheld⟩
  else throw .request

end QleisliKernel.Qirf.SourcePendingMeaning
