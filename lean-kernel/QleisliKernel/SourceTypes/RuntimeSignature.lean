import QleisliKernel.SourceTypes.QuantumSignature
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

private def reader : Nat → (sources : Sources) → String → List String → WorkM (Part sources) :=
  Nat.rec (fun _ _ _ => throw .limit) (fun _ recurse sources owner tokens => do
    exactWork (Exact.charge (8*tokens.length+1))
    match tokens with
    | "Q" :: _ =>
      let inner ← adapt (QuantumSignature.quantumTokens tokens)
      let query ← typeExpressionWithSources sources owner inner
      let _ ← FiniteCarrier.read query.basis
      bounded ⟨Semantics.RuntimeType.owner query.basis,[query]⟩
    | "(" :: rest =>
      guard (rest.getLast? == some ")" && rest.dropLast.getLast? != some ",") .request
      let parts ← adapt (splitMembers rest.dropLast)
      guard (2 ≤ parts.length && parts.length ≤ 64) .limit
      let fields ← parts.mapM (recurse sources owner)
      checkForest fields 1
      pure ⟨Semantics.RuntimeType.tuple parts.length (fields.map (·.tree)),
        fields.flatMap (·.queries)⟩
    | _ =>
      let query ← typeExpressionWithSources sources owner tokens
      let _ ← FiniteCarrier.read query.basis
      bounded ⟨Semantics.RuntimeType.ordinary query.basis,[query]⟩)

def readType (sources : Sources) (owner : String) (tokens : List String) :
    WorkM (Part sources) := reader 65 sources owner tokens

def readTypes (sources : Sources) (owner : String) (tokens : List (List String)) :
    WorkM (List (Part sources)) := do
  guard (tokens.length ≤ 64) .limit
  let result ← tokens.mapM (readType sources owner)
  checkForest result 0
  pure result

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
  -- Shape/reference decoding uses only these bounded prefix nodes. Charge its
  -- repeated structural traversals independently of source parsing above.
  let nodes := (forestSize parameters.val).1+result.val.tree.length
  exactWork (Exact.charge (16*(nodes+1)^2))
  if shapes : (∀ part ∈ parameters.val, (Semantics.RuntimeType.shape part.tree).isSome = true) ∧
      (Semantics.RuntimeType.shape result.val.tree).isSome = true then
    if classical : original.parsedHeader.ordinaryOnly = true →
        (parameters.val.flatMap fun part => (Semantics.RuntimeType.ownerBases part.tree).getD []).isEmpty = true ∧
        (Semantics.RuntimeType.ownerBases result.val.tree).getD [] = [] then
      if effect : original.declaration.isPublic = true →
          (parameters.val.any fun part => !((Semantics.RuntimeType.ownerBases part.tree).getD []).isEmpty) = true ∨
            !((Semantics.RuntimeType.ownerBases result.val.tree).getD []).isEmpty = true →
          original.parsedHeader.effect.isSome = true then
        return ⟨original,parameters.val,result.val,
          by with_reducible exact parameters.property,by with_reducible exact result.property,
          shapes.1,shapes.2,classical,effect⟩
      else throw .request
    else throw .request
  else throw .request

def Checked.sourceRows {sources owner name} (checked : Checked sources owner name) :
    List (String × String) :=
  (owner,checked.original.source) ::
    ((checked.parameters.flatMap (·.queries)) ++ checked.result.queries).flatMap TypeRead.sourceRows

end QleisliKernel.SourceTypes.RuntimeSignature
