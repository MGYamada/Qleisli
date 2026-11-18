import QleisliKernel.SourceTypes.QuantumSignature
import QleisliKernel.SourceTypes.AccessSyntax
import QleisliKernel.Semantics.RuntimeType

/-! Read complete original runtime type trees, including ordinary fields around
quantum owners. Existing finite source queries retain exact nominal identities
and import paths; their physical layout does not replace the runtime tree.
This metadata component grants no execution or source-body theorem.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.RuntimeSignature
open Finite Semantics.FiniteCarrier

structure Part (sources : Sources) where
  tree : Semantics.RuntimeType.Tree
  queries : List (TypeRead sources)

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

private def bounded {sources} (part : Part sources) : WorkM (Part sources) := do
  -- At most 128 existing finite nodes, with an owner and ordinary tuple node
  -- per leaf in the additional shape. No finite-code capacity is enlarged.
  guard (part.tree.length ≤ 3*128 && (part.queries.map (·.basis.length)).sum ≤ 128) .limit
  pure part

private def forestSize {sources} (parts : List (Part sources)) : Nat × Nat :=
  parts.foldl (fun (nodes,bases) part =>
    (nodes+part.tree.length,bases+(part.queries.map (·.basis.length)).sum)) (0,0)

private def checkForest {sources} (parts : List (Part sources)) (extra : Nat) : WorkM Unit := do
  let (nodes,bases) := forestSize parts
  guard (nodes+extra ≤ 3*128 && bases ≤ 128) .limit
  -- Reserve list copies before flattening the bounded children.
  exactWork (Exact.charge (4*(nodes+bases+parts.length+extra+1)))

private def reader : Nat → (sources : Sources) →
    (String → List String → WorkM (TypeRead sources)) → String → List String → WorkM (Part sources) :=
  Nat.rec (fun _ _ _ _ => throw .limit) (fun _ recurse sources finiteType owner tokens => do
    exactWork (Exact.charge (8*tokens.length+1))
    match tokens with
    | "Q" :: _ =>
      let inner ← adapt (QuantumSignature.quantumTokens tokens)
      let query ← finiteType owner inner
      let _ ← FiniteCarrier.read query.basis
      bounded ⟨Semantics.RuntimeType.owner query.basis,[query]⟩
    | "(" :: rest =>
      guard (rest.getLast? == some ")" && rest.dropLast.getLast? != some ",") .request
      let parts ← adapt (splitMembers rest.dropLast)
      guard (2 ≤ parts.length && parts.length ≤ 64) .limit
      let fields ← parts.mapM (recurse sources finiteType owner)
      checkForest fields 1
      pure ⟨Semantics.RuntimeType.tuple parts.length (fields.map (·.tree)),
        fields.flatMap (·.queries)⟩
    | _ =>
      let query ← finiteType owner tokens
      let _ ← FiniteCarrier.read query.basis
      bounded ⟨Semantics.RuntimeType.ordinary query.basis,[query]⟩)

def readTypeWith (sources : Sources)
    (finiteType : String → List String → WorkM (TypeRead sources))
    (owner : String) (tokens : List String) : WorkM (Part sources) :=
  reader 65 sources finiteType owner tokens

def readTypesWith (sources : Sources)
    (finiteType : String → List String → WorkM (TypeRead sources))
    (owner : String) (tokens : List (List String)) :
    WorkM (List (Part sources)) := do
  guard (tokens.length ≤ 64) .limit
  let result ← tokens.mapM (readTypeWith sources finiteType owner)
  checkForest result 0
  pure result

def readType (sources : Sources) (owner : String) (tokens : List String) :
    WorkM (Part sources) := readTypeWith sources (typeExpressionWithSources sources) owner tokens

def readTypes (sources : Sources) (owner : String) (tokens : List (List String)) :
    WorkM (List (Part sources)) := readTypesWith sources (typeExpressionWithSources sources) owner tokens

structure Conditions {sources owner name} (original : OrdinarySignature.Original sources owner name)
    (parameters : List (Part sources)) (result : Part sources) : Type where
  parameterShapes : ∀ part ∈ parameters, (Semantics.RuntimeType.shape part.tree).isSome = true
  resultShape : (Semantics.RuntimeType.shape result.tree).isSome = true
  classicalHeader : original.parsedHeader.ordinaryOnly = true →
    (parameters.flatMap fun part => (Semantics.RuntimeType.ownerBases part.tree).getD []).isEmpty = true ∧
    (Semantics.RuntimeType.ownerBases result.tree).getD [] = []
  publicEffect : original.declaration.isPublic = true →
    (parameters.any fun part => !((Semantics.RuntimeType.ownerBases part.tree).getD []).isEmpty) = true ∨
      !((Semantics.RuntimeType.ownerBases result.tree).getD []).isEmpty = true →
    original.parsedHeader.effect.isSome = true

def checkConditions {sources owner name} (original : OrdinarySignature.Original sources owner name)
    (parameters : List (Part sources)) (result : Part sources) :
    WorkM (Conditions original parameters result) := do
  let nodes := (forestSize parameters).1+result.tree.length
  exactWork (Exact.charge (16*(nodes+1)^2))
  if shapes : (∀ part ∈ parameters, (Semantics.RuntimeType.shape part.tree).isSome = true) ∧
      (Semantics.RuntimeType.shape result.tree).isSome = true then
    if classical : original.parsedHeader.ordinaryOnly = true →
        (parameters.flatMap fun part => (Semantics.RuntimeType.ownerBases part.tree).getD []).isEmpty = true ∧
        (Semantics.RuntimeType.ownerBases result.tree).getD [] = [] then
      if effect : original.declaration.isPublic = true →
          (parameters.any fun part => !((Semantics.RuntimeType.ownerBases part.tree).getD []).isEmpty) = true ∨
            !((Semantics.RuntimeType.ownerBases result.tree).getD []).isEmpty = true →
          original.parsedHeader.effect.isSome = true then
        return ⟨shapes.1,shapes.2,classical,effect⟩
      else throw .request
    else throw .request
  else throw .request

structure Checked (sources : Sources) (owner name : String) where
  original : OrdinarySignature.Original sources owner name
  parameters : List (Part sources)
  result : Part sources
  parametersRead : ∃ before after,
    (readTypes sources owner original.parsedHeader.parameterTypes).run before = (.ok parameters,after)
  resultRead : ∃ before after,
    (readType sources owner (original.parsedHeader.resultTokens.map (·.text))).run before = (.ok result,after)
  parameterShapes : ∀ part ∈ parameters, (Semantics.RuntimeType.shape part.tree).isSome = true
  resultShape : (Semantics.RuntimeType.shape result.tree).isSome = true
  classicalHeader : original.parsedHeader.ordinaryOnly = true →
    (parameters.flatMap fun part => (Semantics.RuntimeType.ownerBases part.tree).getD []).isEmpty = true ∧
    (Semantics.RuntimeType.ownerBases result.tree).getD [] = []
  publicEffect : original.declaration.isPublic = true →
    (parameters.any fun part => !((Semantics.RuntimeType.ownerBases part.tree).getD []).isEmpty) = true ∨
      !((Semantics.RuntimeType.ownerBases result.tree).getD []).isEmpty = true →
    original.parsedHeader.effect.isSome = true

def read (sources : Sources) (owner name : String) : WorkM (Checked sources owner name) := do
  let original ← OrdinarySignature.readOriginal sources owner name
  let parameters ← NaturalAffine.witness (readTypes sources owner original.parsedHeader.parameterTypes)
  let result ← NaturalAffine.witness
    (readType sources owner (original.parsedHeader.resultTokens.map (·.text)))
  let conditions ← checkConditions original parameters.val result.val
  return ⟨original,parameters.val,result.val,
    by with_reducible exact parameters.property,by with_reducible exact result.property,
    conditions.parameterShapes,conditions.resultShape,conditions.classicalHeader,conditions.publicEffect⟩

def Checked.sourceRows {sources owner name} (checked : Checked sources owner name) :
    List (String × String) :=
  (owner,checked.original.source) ::
    ((checked.parameters.flatMap (·.queries)) ++ checked.result.queries).flatMap TypeRead.sourceRows

/-- Ordered owner types derived from marked original parameter slots. The
owner and marker keep their distinct lexical locations, including for Q<Unit>. -/
structure DeclaredOwner where
  ordinal : Nat
  owner : LocatedToken
  marker : LocatedToken
  role : AccessSyntax.Role
  basis : Basis

private def declaredTypeTokens (parameter : Sigma AccessSyntax.DeclaredParameter) : List String :=
  match parameter.2 with
  | .ordinary _ => parameter.1.typeTokens.map (·.text)
  | .access written => written.typeTokens.map (·.text)

private def readDeclaredOwners {sources} (parameters : List (Sigma AccessSyntax.DeclaredParameter))
    (types : List (Part sources)) : WorkM (List DeclaredOwner) := do
  let nodes := (forestSize types).1
  exactWork (Exact.charge (16*(nodes+parameters.length+1)^2))
  guard (parameters.length == types.length) .request
  let slots ← (parameters.zip types).zipIdx.mapM fun ((parameter,part),ordinal) => do
    let some owners := Semantics.RuntimeType.ownerBases part.tree | throw .request
    match parameter.2 with
    | .ordinary _ =>
      guard owners.isEmpty .request
      return none
    | .access written =>
      guard (part.tree.head? == some .quantum) .request
      let [basis] := owners | throw .request
      return some (⟨ordinal,written.owner,written.marker,written.role,basis⟩ : DeclaredOwner)
  return slots.filterMap id

private def declaredResult (owners : List DeclaredOwner) : Semantics.RuntimeType.Tree :=
  match owners with
  | [] => Semantics.RuntimeType.ordinary [.unit]
  | [owner] => Semantics.RuntimeType.owner owner.basis
  | more => Semantics.RuntimeType.tuple more.length (more.map (Semantics.RuntimeType.owner ∘ DeclaredOwner.basis))

/-- Type-only preparation for a closed original access declaration. The
source result is Unit. The separate hidden result describes the required
owner return for use by a subsequent checked body, never a body result witness. -/
structure DeclaredAccess {sources owner name} (original : OrdinarySignature.Original sources owner name)
    (reader : String → List String → WorkM (TypeRead sources)) where
  headerAllowsUnitary : original.parsedHeader.effect = some .unitary ∨
    (original.declaration.isPublic = false ∧ original.parsedHeader.effect = none)
  written : AccessSyntax.DeclaredParameters original
  syntaxRead : AccessSyntax.readDeclaredParameters original = .ok written
  parameters : List (Part sources)
  parametersRead : ∃ before after,
    (readTypesWith sources reader owner (written.parameters.map declaredTypeTokens)).run before = (.ok parameters,after)
  sourceResult : Part sources
  resultRead : ∃ before after,
    (readTypeWith sources reader owner (original.parsedHeader.resultTokens.map (·.text))).run before =
      (.ok sourceResult,after)
  resultUnit : sourceResult.tree = Semantics.RuntimeType.ordinary [.unit]
  owners : List DeclaredOwner
  ownersRead : ∃ before after,
    (readDeclaredOwners written.parameters parameters).run before = (.ok owners,after)
  marked : owners.isEmpty = false
  returnOrder : Semantics.RuntimeType.ownerBases (declaredResult owners) = some (owners.map (·.basis))

def DeclaredAccess.hiddenResult {sources owner name reader} {original : OrdinarySignature.Original sources owner name}
    (checked : DeclaredAccess original reader) : Semantics.RuntimeType.Tree :=
  declaredResult checked.owners

theorem DeclaredAccess.hiddenOwnerOrder {sources owner name reader}
    {original : OrdinarySignature.Original sources owner name} (checked : DeclaredAccess original reader) :
    Semantics.RuntimeType.ownerBases checked.hiddenResult = some (checked.owners.map (·.basis)) :=
  checked.returnOrder

def DeclaredAccess.sourceRows {sources owner name reader} {original : OrdinarySignature.Original sources owner name}
    (checked : DeclaredAccess original reader) : List (String × String) :=
  (owner,original.source) ::
    ((checked.parameters.flatMap (·.queries)) ++ checked.sourceResult.queries).flatMap TypeRead.sourceRows

def readDeclaredAccessWith {sources owner name} (original : OrdinarySignature.Original sources owner name)
    (reader : String → List String → WorkM (TypeRead sources)) : WorkM (DeclaredAccess original reader) := do
  if effect : original.parsedHeader.effect = some .unitary ∨
      (original.declaration.isPublic = false ∧ original.parsedHeader.effect = none) then
    let headerFields := (original.occurrence.header.map fun token => token.text.utf8ByteSize+1).sum
    exactWork (Exact.charge (64*(headerFields+1)+32*(original.occurrence.header.length+1)^2))
    match syntaxRead : AccessSyntax.readDeclaredParameters original with
    | .error _ => throw .request
    | .ok written =>
      let parameters ← NaturalAffine.witness (readTypesWith sources reader owner (written.parameters.map declaredTypeTokens))
      let sourceResult ← NaturalAffine.witness
        (readTypeWith sources reader owner (original.parsedHeader.resultTokens.map (·.text)))
      if unit : sourceResult.val.tree = Semantics.RuntimeType.ordinary [.unit] then
        let owners ← NaturalAffine.witness (readDeclaredOwners written.parameters parameters.val)
        if present : owners.val.isEmpty = false then
          let nodes := (owners.val.map fun owner => owner.basis.length+1).sum
          exactWork (Exact.charge (16*(nodes+1)^2))
          if order : Semantics.RuntimeType.ownerBases (declaredResult owners.val) = some (owners.val.map (·.basis)) then
            return ⟨effect,written,syntaxRead,parameters.val,by with_reducible exact parameters.property,
              sourceResult.val,by with_reducible exact sourceResult.property,unit,
              owners.val,by with_reducible exact owners.property,present,order⟩
          else throw .request
        else throw .request
      else throw .request
  else throw .request

def readDeclaredAccess {sources owner name} (original : OrdinarySignature.Original sources owner name) :
    WorkM (DeclaredAccess original (typeExpressionWithSources sources)) := do
  guard (original.parsedHeader.staticTokens.isNone && original.parsedHeader.requiresTokens.isNone) .request
  readDeclaredAccessWith original (typeExpressionWithSources sources)

end QleisliKernel.SourceTypes.RuntimeSignature
