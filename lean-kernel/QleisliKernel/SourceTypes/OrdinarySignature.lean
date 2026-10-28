import QleisliKernel.SourceTypes
import QleisliKernel.SourceTypes.LocatedFacts
import QleisliKernel.Semantics.Raw

/-! Original ordinary parameter/result headers. This component binds the
declared result/effect and complete original envelope; it does not establish
source-body preservation or authorize execution by itself.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.OrdinarySignature
open Semantics.FiniteCarrier Semantics.Raw Finite

inductive Selection where
  | project
  | exported
  | internal
  deriving BEq, DecidableEq, Repr

structure Header where
  effect : Option Effect
  ordinaryOnly : Bool
  parameterTypes : List (List String)
  resultTokens : List LocatedToken

private def expect (text : String) (tokens : List LocatedToken) :
    Except String (LocatedToken × List LocatedToken) := do
  let token :: rest := tokens | throw "missing entry header token"
  if token.text != text then throw "unexpected entry header token"
  return (token,rest)

private def parameterClause : Nat → Nat → List LocatedToken → List LocatedToken →
    Except String (List LocatedToken × List LocatedToken) :=
  Nat.rec (fun _ _ _ => throw "incomplete parameter clause") (fun _ next depth tokens reversed => do
    let token :: rest := tokens | throw "missing parameter closing parenthesis"
    if token.text == ")" && depth == 0 then return (reversed.reverse,rest)
    if token.text == "(" then return ← next (depth+1) rest (token :: reversed)
    if token.text == ")" then return ← next (depth-1) rest (token :: reversed)
    next depth rest (token :: reversed))

private def parameterTypes (tokens : List LocatedToken) : Except String (List (List String)) := do
  let parts ← splitMembers (tokens.map (·.text))
  if parts.length > 64 then throw "parameter count exceeds existing bound"
  parts.mapM fun part => do
    let pattern := part.takeWhile (· != ":")
    let ":" :: ty := part.drop pattern.length | throw "missing parameter type"
    if pattern.isEmpty || ty.isEmpty then throw "empty parameter pattern or type"
    return ty

private def header (occurrence : BodyOccurrence) : Except String Header := do
  let tokens ← if occurrence.declaration.isPublic then do
      let (_,rest) ← expect "pub" occurrence.header
      pure rest
    else pure occurrence.header
  let (effect,ordinaryOnly,tokens) := match tokens with
    | effect :: rest => match effect.text with
      | "unitary" => (some Effect.unitary,false,rest)
      | "isometry" | "iso" => (some Effect.iso,false,rest)
      | "observe" => (some Effect.observe,false,rest)
      | "classical" => (some Effect.unitary,true,rest)
      | _ => (none,false,tokens)
    | [] => (none,false,[])
  let (_,tokens) ← expect "fn" tokens
  let (name,tokens) ← expect occurrence.declaration.name tokens
  if name != occurrence.nameToken then throw "entry name occurrence mismatch"
  let (_,tokens) ← expect "(" tokens
  let (parameters,tokens) ← parameterClause (tokens.length+1) 0 tokens []
  let parameters ← parameterTypes parameters
  let (_,tokens) ← expect "-" tokens
  let (_,tokens) ← expect ">" tokens
  if tokens.isEmpty then throw "missing ordinary entry result"
  return ⟨effect,ordinaryOnly,parameters,tokens⟩

def envelope (occurrence : BodyOccurrence) : List LocatedToken :=
  occurrence.header ++ [occurrence.openBrace] ++ occurrence.body ++ [occurrence.closeBrace]

structure Original (sources : Sources) (owner name : String) where
  source : String
  declaration : Declaration
  occurrence : BodyOccurrence
  parsedHeader : Header
  bound : originalBinding sources owner name = .ok (source,declaration)
  function : declaration.kind = "fn"
  catalogue : ∃ scanned, sourceCatalogue source = .ok scanned ∧ occurrence ∈ scanned.bodies
  sameDeclaration : occurrence.declaration = declaration
  parsed : header occurrence = .ok parsedHeader
  bytes : LocatedFacts.OrderedSlices source.toUTF8 0 (envelope occurrence)

private def original (sources : Sources) (owner name : String) :
    Except String (Original sources owner name) := do
  match bound : originalBinding sources owner name with
  | .error message => throw message
  | .ok (source,declaration) =>
    if function : declaration.kind = "fn" then
      match scannedOk : sourceCatalogue source with
      | .error message => throw message
      | .ok scanned =>
        match selected : scanned.bodies.filter (·.declaration == declaration) with
        | [occurrence] =>
          have membership : occurrence ∈ scanned.bodies.filter (·.declaration == declaration) := by
            rw [selected]; exact List.mem_cons_self
          have found := (List.mem_filter.mp membership).1
          have sameDeclaration : occurrence.declaration = declaration :=
            beq_iff_eq.mp (List.mem_filter.mp membership).2
          match parsed : header occurrence with
          | .error message => throw message
          | .ok parsedHeader =>
            if bytes : LocatedFacts.checkOrdered source.toUTF8 0 (envelope occurrence) = true then
              return ⟨source,declaration,occurrence,parsedHeader,bound,function,
                ⟨scanned,scannedOk,found⟩,sameDeclaration,parsed,
                LocatedFacts.checkOrdered_sound _ _ _ bytes⟩
            else throw "original entry byte envelope mismatch"
        | _ => throw "original entry body multiplicity"
    else throw "ordinary entry requires a runtime function"

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

/-- Read each original parameter's complete ordinary finite type. This does
not check parameter-pattern meaning or source-body preservation. -/
def inputTypes (sources : Sources) (owner : String) (tokens : List (List String)) :
    WorkM (List Basis) := do
  guard (tokens.length ≤ 64) .limit
  let inputs ← tokens.mapM fun ty => do
    let basis ← typeExpression sources owner ty
    let _ ← FiniteCarrier.read basis
    pure basis
  guard ((inputs.map List.length).sum ≤ 128) .limit
  return inputs

structure Checked (sources : Sources) (owner name : String) where
  original : Original sources owner name
  inputs : List Basis
  basis : Basis
  inputsRead : ∃ before after,
    (inputTypes sources owner original.parsedHeader.parameterTypes).run before = (.ok inputs,after)
  resultRead : ∃ before after,
    (typeExpression sources owner (original.parsedHeader.resultTokens.map (·.text))).run before =
      (.ok basis,after)

def selectionAllowed {sources : Sources} {owner name : String}
    (selection : Selection) (original : Original sources owner name) : Bool :=
  match selection with
  | .project => owner == "main" && name == "main" && !original.parsedHeader.ordinaryOnly &&
      original.parsedHeader.parameterTypes.isEmpty
  | .exported => original.declaration.isPublic
  | .internal => !original.declaration.isPublic && !(owner == "main" && name == "main")

/-- Project main remains closed. Exported declarations may have ordinary
parameters. Quantum/static binders and general source semantics remain separate. -/
def read (sources : Sources) (selection : Selection) (owner name : String) :
    WorkM (Checked sources owner name) := do
  guard (sources.size ≤ 128) .limit
  let bytes := (sources.toList.map fun row => row.1.utf8ByteSize + row.2.utf8ByteSize).sum
  guard (bytes ≤ 1048576) .limit
  exactWork (Exact.charge (512*(bytes+1)+owner.utf8ByteSize+name.utf8ByteSize+1))
  let original ← adapt (original sources owner name)
  guard (selectionAllowed selection original) .request
  let inputs ← NaturalAffine.witness (inputTypes sources owner original.parsedHeader.parameterTypes)
  let basis ← NaturalAffine.witness
    (typeExpression sources owner (original.parsedHeader.resultTokens.map (·.text)))
  let _ ← FiniteCarrier.read basis.val
  return ⟨original,inputs.val,basis.val,by with_reducible exact inputs.property,
    by with_reducible exact basis.property⟩

theorem read_selection (sources : Sources) (selection : Selection) (owner name : String)
    (checked : Checked sources owner name) (work left : Nat)
    (ok : (read sources selection owner name).run work = (.ok checked,left)) :
    selectionAllowed selection checked.original = true := by
  unfold read at ok
  obtain ⟨_,a,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,b,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,c,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨original,d,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,e,allowed,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨inputs,f,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨basis,g,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,j,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨rfl,rfl⟩ := pure_success _ _ _ _ h
  exact (guard_success _ _ _ _ allowed).1

theorem Checked.bound {sources owner name} (checked : Checked sources owner name) :
    originalBinding sources owner name = .ok (checked.original.source,checked.original.declaration) :=
  checked.original.bound

theorem Checked.byte_envelope {sources owner name} (checked : Checked sources owner name) :
    LocatedFacts.OrderedSlices checked.original.source.toUTF8 0 (envelope checked.original.occurrence) :=
  checked.original.bytes

theorem Checked.parameter_types {sources owner name} (checked : Checked sources owner name) :
    ∃ before after,
      (inputTypes sources owner checked.original.parsedHeader.parameterTypes).run before =
        (.ok checked.inputs,after) := checked.inputsRead

theorem Checked.result_type {sources owner name} (checked : Checked sources owner name) :
    ∃ before after,
      (typeExpression sources owner (checked.original.parsedHeader.resultTokens.map (·.text))).run before =
        (.ok checked.basis,after) := checked.resultRead

end QleisliKernel.SourceTypes.OrdinarySignature
