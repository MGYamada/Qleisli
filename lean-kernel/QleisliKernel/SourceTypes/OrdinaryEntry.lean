import QleisliKernel.SourceTypes
import QleisliKernel.SourceTypes.LocatedFacts
import QleisliKernel.Semantics.Raw

/-! Original closed ordinary-result entry headers. This component binds the
declared result/effect and complete original envelope; it does not establish
source-body preservation or authorize execution by itself.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.OrdinaryEntry
open Semantics.FiniteCarrier Semantics.Raw Finite

inductive Selection where
  | project
  | exported
  deriving BEq, DecidableEq, Repr

structure Header where
  effect : Option Effect
  ordinaryOnly : Bool
  resultTokens : List LocatedToken

private def expect (text : String) (tokens : List LocatedToken) :
    Except String (LocatedToken × List LocatedToken) := do
  let token :: rest := tokens | throw "missing entry header token"
  if token.text != text then throw "unexpected entry header token"
  return (token,rest)

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
  let (_,tokens) ← expect ")" tokens
  let (_,tokens) ← expect "-" tokens
  let (_,tokens) ← expect ">" tokens
  if tokens.isEmpty then throw "missing ordinary entry result"
  return ⟨effect,ordinaryOnly,tokens⟩

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

structure Checked (sources : Sources) (owner name : String) where
  original : Original sources owner name
  basis : Basis

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

/-- Project selection is the literal main::main entry, where private main is
allowed. Selecting another public root requires exported visibility. This
reader currently supports closed, zero-parameter, ordinary-result entries. -/
def read (sources : Sources) (selection : Selection) (owner name : String) :
    WorkM (Checked sources owner name) := do
  guard (sources.size ≤ 128) .limit
  let bytes := (sources.toList.map fun row => row.1.utf8ByteSize + row.2.utf8ByteSize).sum
  guard (bytes ≤ 1048576) .limit
  exactWork (Exact.charge (512*(bytes+1)+owner.utf8ByteSize+name.utf8ByteSize+1))
  let original ← adapt (original sources owner name)
  match selection with
  | .project => guard (owner == "main" && name == "main" && !original.parsedHeader.ordinaryOnly) .request
  | .exported => guard original.declaration.isPublic .request
  let basis ← typeExpression sources owner (original.parsedHeader.resultTokens.map (·.text))
  let _ ← FiniteCarrier.read basis
  return ⟨original,basis⟩

theorem Checked.bound {sources owner name} (checked : Checked sources owner name) :
    originalBinding sources owner name = .ok (checked.original.source,checked.original.declaration) :=
  checked.original.bound

theorem Checked.byte_envelope {sources owner name} (checked : Checked sources owner name) :
    LocatedFacts.OrderedSlices checked.original.source.toUTF8 0 (envelope checked.original.occurrence) :=
  checked.original.bytes

theorem read_result (sources : Sources) (selection : Selection) (owner name : String)
    (checked : Checked sources owner name) (work left : Nat)
    (ok : (read sources selection owner name).run work = (.ok checked,left)) :
    ∃ before after, (typeExpression sources owner
      (checked.original.parsedHeader.resultTokens.map (·.text))).run before = (.ok checked.basis,after) := by
  cases selection
  all_goals
    unfold read at ok
    obtain ⟨_,a,_,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨_,b,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,c,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨original,d,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,e,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨basis,f,typed,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,g,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨rfl,rfl⟩ := pure_success _ _ _ _ h
    exact ⟨e,f,typed⟩

end QleisliKernel.SourceTypes.OrdinaryEntry
