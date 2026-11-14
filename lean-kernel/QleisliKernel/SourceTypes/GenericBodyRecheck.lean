import QleisliKernel.SourceTypes.GenericCatalogue

/-! Recheck a freshly parsed original body with the same audited definition
table. The root tree and its Needs are checked again; previously audited
original callees supply the complete closed reference/effect world. This is
not a claimed invocation of the cold discovery reader or native body evidence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.GenericBodyRecheck
open Finite

private def definitionOf {sources owner name} (body : GenericTypeTrace.BodyRecord sources)
    (sameOwner : body.owner = owner) (sameName : body.name = name) :
    GenericTypeTrace.Definition sources owner name := by
  rcases body with ⟨_,_,definition,prepared,tree,outcome,checked⟩
  cases sameOwner
  cases sameName
  exact definition

private def preparedOf {sources owner name} (body : GenericTypeTrace.BodyRecord sources)
    (sameOwner : body.owner = owner) (sameName : body.name = name) :
    Option (GenericTypeTrace.PreparedDefinitions (definitionOf body sameOwner sameName).context) := by
  rcases body with ⟨_,_,definition,prepared,tree,outcome,checked⟩
  cases sameOwner
  cases sameName
  exact prepared

private theorem definitionOf_same {sources owner name} (body : GenericTypeTrace.BodyRecord sources)
    (sameOwner : body.owner = owner) (sameName : body.name = name) :
    HEq (definitionOf body sameOwner sameName) body.definition := by
  rcases body with ⟨_,_,definition,prepared,tree,outcome,checked⟩
  cases sameOwner
  cases sameName
  rfl

private theorem preparedOf_same {sources owner name} (body : GenericTypeTrace.BodyRecord sources)
    (sameOwner : body.owner = owner) (sameName : body.name = name) :
    HEq (preparedOf body sameOwner sameName) body.prepared := by
  rcases body with ⟨_,_,definition,prepared,tree,outcome,checked⟩
  cases sameOwner
  cases sameName
  rfl

structure Root {sources owner name} (original : OrdinarySignature.Original sources owner name)
    (tree : SourceSyntax.Tree original.occurrence.body) where
  definition : GenericTypeTrace.Definition sources owner name
  sameOriginal : definition.original.envelope = original
  prepared : Option (GenericTypeTrace.PreparedDefinitions definition.context)
  outcome : GenericTypeTrace.Outcome sources
  checked : ∃ before after,
    (GenericTypeTrace.checkTree definition (GenericTypeTrace.originalTree definition sameOriginal tree) prepared).run
      before = (.ok outcome,after)

def Root.record {sources owner name original tree} (root : @Root sources owner name original tree) :
    GenericTypeTrace.BodyRecord sources :=
  ⟨owner,name,root.definition,root.prepared,
    GenericTypeTrace.originalTree root.definition root.sameOriginal tree,root.outcome,root.checked⟩

private def inferRechecked {sources catalogue owner name original tree}
    (projection : @GenericCatalogue.Projection sources catalogue owner name original)
    (root : Root original tree) : WorkM (GenericTypeTrace.Inferred catalogue.records root.record) :=
  let original := projection.entry.inferred
  match original.cohort with
  | some cohort => GenericTypeTrace.inferFrom catalogue.records root.record original.prepared cohort
  | none => GenericTypeTrace.infer catalogue.records root.record

structure Checked {sources owner name} (catalogue : GenericCatalogue.Checked sources)
    (original : OrdinarySignature.Original sources owner name) (tree : SourceSyntax.Tree original.occurrence.body) where
  projection : GenericCatalogue.Projection catalogue.toRuntimeChecked original
  projectionRead : ∃ before after,
    (GenericCatalogue.project catalogue.toRuntimeChecked original).run before = (.ok projection,after)
  root : Root original tree
  sameDefinition : HEq root.definition projection.entry.body.definition
  samePrepared : HEq root.prepared projection.entry.body.prepared
  effect : root.outcome.effect = projection.entry.body.outcome.effect
  quantum : root.outcome.quantumUse = projection.entry.body.outcome.quantumUse
  references : root.outcome.references = projection.entry.body.outcome.references
  inferred : GenericTypeTrace.Inferred catalogue.records root.record
  inferredRead : ∃ before after,(inferRechecked projection root).run before = (.ok inferred,after)

def Checked.inferredEffect {sources owner name catalogue original tree}
    (checked : @Checked sources owner name catalogue original tree) : Semantics.Raw.Effect :=
  checked.inferred.inferredEffect

def Checked.sourceRows {sources owner name catalogue original tree}
    (checked : @Checked sources owner name catalogue original tree) : List (String × String) :=
  checked.root.definition.rows ++ checked.root.outcome.rows ++ checked.projection.sourceRows

private def referenceFields (references : List SourceEffectClosure.DefId) : Nat :=
  (references.map fun (owner,name) => owner.utf8ByteSize+name.utf8ByteSize+2).sum

/-- The catalogue entry binds the full original source/envelope, not just a
name. Its exact definition/table is reused, while this actual tree and every
fresh Need are independently replayed. Matching effect/reference facts allow
the already checked original callee world to replace a second discovery pass.
The selected projection alone contributes dependency rows. -/
def read {sources : Sources} {owner name : String} (catalogue : GenericCatalogue.Checked sources)
    (original : OrdinarySignature.Original sources owner name)
    (tree : SourceSyntax.Tree original.occurrence.body) : WorkM (Checked catalogue original tree) := do
  let projection ← NaturalAffine.witness (GenericCatalogue.project catalogue.toRuntimeChecked original)
  let body := projection.val.entry.body
  exactWork (Exact.charge (16*(body.owner.utf8ByteSize+body.name.utf8ByteSize+
    owner.utf8ByteSize+name.utf8ByteSize+1)))
  if sameOwner : body.owner = owner then
    if sameName : body.name = name then
      let definition := definitionOf body sameOwner sameName
      let prepared := preparedOf body sameOwner sameName
      have sameOriginal : definition.original.envelope = original :=
        definition.original.envelope.sameSource original
      let outcome ← NaturalAffine.witness (GenericTypeTrace.checkTree definition
        (GenericTypeTrace.originalTree definition sameOriginal tree) prepared)
      exactWork (Exact.charge (16*(referenceFields outcome.val.effect.dependencies+
        referenceFields body.outcome.effect.dependencies+referenceFields outcome.val.references+
        referenceFields body.outcome.references+1)))
      if effect : outcome.val.effect = body.outcome.effect then
        if quantum : outcome.val.quantumUse = body.outcome.quantumUse then
          if references : outcome.val.references = body.outcome.references then
            let root : Root original tree :=
              ⟨definition,sameOriginal,prepared,outcome.val,by with_reducible exact outcome.property⟩
            let inferred ← NaturalAffine.witness (inferRechecked projection.val root)
            pure ⟨projection.val,by with_reducible exact projection.property,root,
              definitionOf_same body sameOwner sameName,preparedOf_same body sameOwner sameName,
              effect,quantum,references,inferred.val,by with_reducible exact inferred.property⟩
          else throw .request
        else throw .request
      else throw .request
    else throw .request
  else throw .request

end QleisliKernel.SourceTypes.GenericBodyRecheck
