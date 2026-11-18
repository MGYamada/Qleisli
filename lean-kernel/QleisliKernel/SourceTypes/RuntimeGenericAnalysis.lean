import QleisliKernel.SourceTypes.GenericBodyRecheck

/-! Original generic obligations for runtime bodies. A retained catalogue
supplies the audited result for the exact canonical parser tree. Arbitrary-tree
callers keep their own recheck. Both collect rows only along original call
references, and the no-catalogue entry still performs cold discovery.
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
  | catalogued {catalogue : GenericCatalogue.Checked sources} {tree : SourceSyntax.Tree original.occurrence.body}
      (entry : GenericCatalogue.Entry catalogue.toRuntimeChecked original)
      (selectedEntry : ∃ before after,(GenericCatalogue.lookup catalogue.toRuntimeChecked original).run before =
        (.ok entry,after))
      (sameTree : HEq entry.body.tree tree)
      (inferred : GenericTypeTrace.Inferred catalogue.records entry.body)
      (sameInference : inferred = entry.inferred)
      (rows : List (GenericTypeTrace.BodyRecord sources))
      (selected : ∃ before after,(rowsFrom catalogue.records entry.body).run before = (.ok rows,after))

instance {sources owner name} {original : OrdinarySignature.Original sources owner name} :
    Coe (GenericTypeTrace.Checked original) (Checked original) := ⟨Checked.fresh⟩

def Checked.outcome {sources owner name original} : @Checked sources owner name original → GenericTypeTrace.Outcome sources
  | .fresh checked => checked.root.outcome
  | .retained checked .. => checked.root.outcome
  | .catalogued entry .. => entry.body.outcome

def Checked.inferredEffect {sources owner name original} : @Checked sources owner name original → Semantics.Raw.Effect
  | .fresh checked => checked.inferredEffect
  | .retained checked .. => checked.inferredEffect
  | .catalogued _ _ _ inferred .. => inferred.inferredEffect

def Checked.quantumUse {sources owner name original} : @Checked sources owner name original → Bool
  | .fresh checked => checked.quantumUse
  | .retained checked .. => checked.inferred.quantumUse
  | .catalogued _ _ _ inferred .. => inferred.quantumUse

def Checked.sourceRows {sources owner name original} : @Checked sources owner name original → List (String × String)
  | .fresh checked => checked.sourceRows
  | .retained _ rows _ => rows.flatMap fun body => body.definition.rows ++ body.outcome.rows
  | .catalogued _ _ _ _ _ rows _ => rows.flatMap fun body => body.definition.rows ++ body.outcome.rows

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

/-- The exact successful source parser permits reuse of the audited symbolic
body. Closed evaluation, original callee reads and native checks run as before. -/
def readParsed {sources owner name original} (instantiation : @StaticInstantiation.Checked sources owner name original)
    (tree : SourceSyntax.Tree original.occurrence.body)
    (parsed : SourceSyntax.read (original.occurrence.body.length+1) 0 true original.occurrence.body = .ok tree)
    (catalogue : Option (GenericCatalogue.Checked sources)) : WorkM (Checked original) := do
  match catalogue with
  | none => return .fresh (← GenericTypeTrace.readWithTree instantiation tree)
  | some catalogue =>
    -- The catalogue has already checked every Meaning reference. This reader
    -- retains the runtime call closure, so it needs only the exact entry here.
    let entry ← NaturalAffine.witness (GenericCatalogue.lookup catalogue.toRuntimeChecked original)
    let same ← entry.val.bindTree tree parsed
    let rows ← NaturalAffine.witness (rowsFrom catalogue.records entry.val.body)
    return .catalogued entry.val (by with_reducible exact entry.property) same.down
      entry.val.inferred rfl rows.val (by with_reducible exact rows.property)

end QleisliKernel.SourceTypes.RuntimeGenericAnalysis
