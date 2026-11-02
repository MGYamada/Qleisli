import QleisliKernel.SourceTypes.SourceNominalSyntax
import QleisliKernel.SourceTypes.MemberFields
import QleisliKernel.SourceTypes.NaturalAffine

/-! Original nominal expression references. Exact type paths, ordered field
types and privacy come from the original declaring source, including zero-width
members. These references alone neither evaluate a body nor issue a handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceNominal
open QleisliKernel QleisliKernel.SourceTypes Finite Semantics.FiniteCarrier

private def typeFields (basis : Basis) : Nat :=
  (basis.map fun atom => match atom with
    | .enumeration origin names | .record origin names =>
      1+FiniteCarrier.originBytes origin+(names.map String.utf8ByteSize).sum+names.length
    | _ => 1).sum

def unshadowed (scope : List String) (tokens : List LocatedToken) : Bool :=
  match tokens with
  | [token] => !scope.contains token.text
  | _ => true

private def fieldMember (field : MemberFields.Field) (fields : List MemberFields.Field) : Bool :=
  fields.any (fun original => decide (original = field))

private theorem fieldMember_sound (field : MemberFields.Field) (fields : List MemberFields.Field)
    (selected : fieldMember field fields = true) : field ∈ fields := by
  obtain ⟨original,member,same⟩ := List.any_eq_true.mp selected
  have same : original = field := of_decide_eq_true same
  exact same ▸ member

structure Nominal (sources : Sources) (caller : String) (scope : List String) (tokens : List LocatedToken) where
  query : TypeRead sources
  original : ∃ before after,
    (typeExpressionWithSources sources caller (tokens.map (·.text))).run before = (.ok query,after)
  lexical : unshadowed scope tokens = true

def readType (sources : Sources) (caller : String) (scope : List String) (tokens : List LocatedToken) :
    WorkM (Nominal sources caller scope tokens) := do
  exactWork (Exact.charge (16*((tokens.map fun token => token.text.utf8ByteSize+4).sum+
    (scope.map String.utf8ByteSize).sum+1)))
  if lexical : unshadowed scope tokens = true then
    let query ← NaturalAffine.witness (typeExpressionWithSources sources caller (tokens.map (·.text)))
    return ⟨query.val,by with_reducible exact query.property,lexical⟩
  else throw .request

structure Variant (sources : Sources) (caller : String) (scope : List String)
    {tokens : List LocatedToken} (written : SourceNominalSyntax.Variant tokens) where
  nominal : Nominal sources caller scope written.typeTokens
  origin : Origin
  names : List String
  enumeration : nominal.query.basis = [.enumeration origin names]
  ordinal : Nat
  member : names[ordinal]? = some written.member.text

def readVariant (sources : Sources) (caller : String) (scope : List String)
    {tokens : List LocatedToken} (written : SourceNominalSyntax.Variant tokens) :
    WorkM (Variant sources caller scope written) := do
  let nominal ← readType sources caller scope written.typeTokens
  exactWork (Exact.charge (16*(typeFields nominal.query.basis+written.member.text.utf8ByteSize+1)))
  match enumeration : nominal.query.basis with
  | [.enumeration origin names] =>
    let ordinal := names.idxOf written.member.text
    if member : names[ordinal]? = some written.member.text then
      return ⟨nominal,origin,names,enumeration,ordinal,member⟩
    else throw .request
  | _ => throw .request

structure Record (sources : Sources) (caller : String) (scope : List String)
    {tokens : List LocatedToken} (written : SourceNominalSyntax.Record tokens) where
  nominal : Nominal sources caller scope written.typeTokens
  origin : Origin
  names : List String
  tail : Basis
  record : nominal.query.basis = .record origin names :: tail
  definition : MemberFields.Record
  definitionRead : ∃ before after,
    (MemberFields.readOriginalFields sources origin.moduleName origin.declarationName).run before = (.ok definition,after)
  exactType : definition.original.basis = nominal.query.basis
  fields : List MemberFields.Field
  originalOrder : fields.map (·.member.name.text) = written.initializers.map (·.name.text)
  selected : ∀ field ∈ fields,field ∈ definition.fields
  complete : (definition.fields.map (·.member.name.text)).Perm (written.initializers.map (·.name.text))
  unique : (written.initializers.map (·.name.text)).Nodup
  accessible : ∀ field ∈ fields,MemberFields.VisibleFrom caller origin field.member

def readRecord (sources : Sources) (caller : String) (scope : List String)
    {tokens : List LocatedToken} (written : SourceNominalSyntax.Record tokens) :
    WorkM (Record sources caller scope written) := do
  let nominal ← readType sources caller scope written.typeTokens
  exactWork (Exact.charge (32*(typeFields nominal.query.basis+1)*(written.initializers.length+1)))
  match record : nominal.query.basis with
  | .record origin names :: tail =>
    let definition ← NaturalAffine.witness
      (MemberFields.readOriginalFields sources origin.moduleName origin.declarationName)
    if exactType : definition.val.original.basis = nominal.query.basis then
      let fields ← written.initializers.mapM fun initializer => do
        let some field := definition.val.fields.find? (fun field => field.member.name.text == initializer.name.text)
          | throw .request
        return field
      let writtenNames := written.initializers.map (fun initializer => initializer.name.text)
      let declaredNames := definition.val.fields.map (fun field => field.member.name.text)
      if ordered : fields.map (fun field => field.member.name.text) = writtenNames then
        if selected : fields.all (fun field => fieldMember field definition.val.fields) = true then
          if complete : declaredNames.Perm writtenNames then
            if unique : writtenNames.Nodup then
              if accessible : fields.all (fun field => field.member.isPublic || caller == origin.moduleName) = true then
                have originals : ∀ field ∈ fields,field ∈ definition.val.fields := by
                  intro field member
                  exact fieldMember_sound _ _ ((List.all_eq_true.mp selected) field member)
                have permissions : ∀ field ∈ fields,MemberFields.VisibleFrom caller origin field.member := by
                  intro field member
                  have allowed := (List.all_eq_true.mp accessible) field member
                  have alternatives : field.member.isPublic = true ∨ caller = origin.moduleName := by
                    simpa only [Bool.or_eq_true,beq_iff_eq] using allowed
                  rcases alternatives with exported | same
                  · exact Or.inl exported
                  · exact Or.inr same
                return ⟨nominal,origin,names,tail,record,definition.val,by with_reducible exact definition.property,
                  exactType,fields,ordered,originals,complete,unique,permissions⟩
              else throw .request
            else throw .request
          else throw .request
        else throw .request
      else throw .request
    else throw .request
  | _ => throw .request

structure Projection (sources : Sources) (caller : String) (basis : Basis)
    {tokens : List LocatedToken} (written : SourceNominalSyntax.Projection tokens) where
  origin : Origin
  names : List String
  tail : Basis
  record : basis = .record origin names :: tail
  definition : MemberFields.Record
  definitionRead : ∃ before after,
    (MemberFields.readOriginalFields sources origin.moduleName origin.declarationName).run before = (.ok definition,after)
  exactType : definition.original.basis = basis
  index : Nat
  field : MemberFields.Field
  selected : definition.fields[index]? = some field
  named : field.member.name.text = written.member.text
  accessible : MemberFields.VisibleFrom caller origin field.member

def readProjection (sources : Sources) (caller : String) (basis : Basis)
    {tokens : List LocatedToken} (written : SourceNominalSyntax.Projection tokens) :
    WorkM (Projection sources caller basis written) := do
  exactWork (Exact.charge (32*(typeFields basis+written.member.text.utf8ByteSize+1)))
  match record : basis with
  | .record origin names :: tail =>
    let definition ← NaturalAffine.witness
      (MemberFields.readOriginalFields sources origin.moduleName origin.declarationName)
    if exactType : definition.val.original.basis = basis then
      let index := (definition.val.fields.map (·.member.name.text)).idxOf written.member.text
      match selected : definition.val.fields[index]? with
      | none => throw .request
      | some field =>
        if named : field.member.name.text = written.member.text then
          if accessible : field.member.isPublic = true ∨ caller = origin.moduleName then
            return ⟨origin,names,tail,rfl,definition.val,by with_reducible exact definition.property,
              by simpa only [record] using exactType,index,field,selected,named,accessible⟩
          else throw .request
        else throw .request
    else throw .request
  | _ => throw .request

end QleisliKernel.SourceTypes.SourceNominal
