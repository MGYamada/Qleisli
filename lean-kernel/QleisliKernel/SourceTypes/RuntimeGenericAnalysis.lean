import QleisliKernel.SourceTypes.GenericBodyRecheck

/-! Original generic obligations for runtime bodies. A retained catalogue
provides the original definition and checked callees. Recheck the actual source
tree, preserve its lexical obligations, and collect rows only along this body's
original call references. The no-catalogue entry still performs cold discovery.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.RuntimeGenericAnalysis
open Finite

private def rowsFrom {sources} (records : List (GenericTypeTrace.BodyRecord sources))
    (root : GenericTypeTrace.BodyRecord sources) : WorkM (List (GenericTypeTrace.BodyRecord sources)) := do
  let count := records.foldl (fun n row => n + row.outcome.references.length + 1) 0
  exactWork (Exact.charge (8*(count+root.outcome.references.length+1)))
  GenericCatalogue.selectRecordsWith (·.outcome.references) records (count+1) root.outcome.references [root]

inductive Checked {sources owner name} (original : OrdinarySignature.Original sources owner name) where
  | fresh (checked : GenericTypeTrace.Checked original)
  | retained {catalogue : GenericCatalogue.Checked sources} {tree : SourceSyntax.Tree original.occurrence.body}
      (checked : GenericBodyRecheck.Checked catalogue original tree) (rows : List (GenericTypeTrace.BodyRecord sources))
      (selected : ∃ before after,(rowsFrom catalogue.records checked.root.record).run before = (.ok rows,after))

instance {sources owner name} {original : OrdinarySignature.Original sources owner name} :
    Coe (GenericTypeTrace.Checked original) (Checked original) := ⟨Checked.fresh⟩

def Checked.outcome {sources owner name original} : @Checked sources owner name original → GenericTypeTrace.Outcome sources
  | .fresh checked => checked.root.outcome
  | .retained checked .. => checked.root.outcome

def Checked.inferredEffect {sources owner name original} : @Checked sources owner name original → Semantics.Raw.Effect
  | .fresh checked => checked.inferredEffect
  | .retained checked .. => checked.inferredEffect

def Checked.quantumUse {sources owner name original} : @Checked sources owner name original → Bool
  | .fresh checked => checked.quantumUse
  | .retained checked .. => checked.inferred.quantumUse

def Checked.sourceRows {sources owner name original} : @Checked sources owner name original → List (String × String)
  | .fresh checked => checked.sourceRows
  | .retained _ rows _ => rows.flatMap fun body => body.definition.rows ++ body.outcome.rows

def Checked.basisObligations {sources owner name original} (checked : @Checked sources owner name original) :=
  checked.outcome.basisObligations

def Checked.computedObligations {sources owner name original} (checked : @Checked sources owner name original) :=
  checked.outcome.computedObligations

def Checked.recursiveCalls {sources owner name original} (checked : @Checked sources owner name original) :=
  checked.outcome.recursions

def read {sources owner name original} (instantiation : @StaticInstantiation.Checked sources owner name original)
    (tree : SourceSyntax.Tree original.occurrence.body) (catalogue : Option (GenericCatalogue.Checked sources)) :
    WorkM (Checked original) := do
  match catalogue with
  | none => return .fresh (← GenericTypeTrace.readWithTree instantiation tree)
  | some catalogue =>
    let checked ← GenericBodyRecheck.read catalogue original tree
    let rows ← NaturalAffine.witness (rowsFrom catalogue.records checked.root.record)
    return .retained checked rows.val (by with_reducible exact rows.property)

end QleisliKernel.SourceTypes.RuntimeGenericAnalysis
