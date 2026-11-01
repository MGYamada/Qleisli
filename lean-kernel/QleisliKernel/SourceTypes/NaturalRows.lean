import QleisliKernel.SourceTypes.LexicalNatural
import QleisliKernel.SourceTypes.CallName

/-! Exact original lookup rows for actual Nat expressions and transitive
helper dependencies. An unused/global helper scan supplies no row permission;
only original expression calls and their original dependencies contribute.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.NaturalRows
open Finite Semantics.SourceNatural

private def route (sources : Sources) (caller : String) (path : Path) (key : NaturalCatalog.Key) :
    WorkM (List (String × String)) := do
  let resolution ← CallName.resolve sources caller (path.intersperse "::")
  guard (resolution.result.moduleName == key.moduleName &&
    resolution.result.declaration.name == key.declarationName &&
    resolution.result.declaration.kind == "static-fn") .request
  pure (ResolutionProvenance.sourceRows resolution.result)

def bindings (sources : Sources) (caller : String) (entries : List NaturalHelpers.Entry)
    (original : List (Path × NaturalCatalog.Key)) : WorkM (List (String × String)) := do
  if original.isEmpty then return []
  let direct ← original.mapM fun (path,key) => route sources caller path key
  let (needed,processed,rows) ← entries.foldlM (fun (needed,processed,rows) entry => do
    let key := entry.original.key
    exactWork (Exact.charge ((key.moduleName.utf8ByteSize+key.declarationName.utf8ByteSize+1)*
      (needed.length+processed.length+1)))
    if !needed.contains key then pure (needed,processed,rows) else do
      guard (!processed.contains key) .request
      let paths ← entry.original.calls.mapM fun (path,key) => route sources entry.original.key.moduleName path key
      pure (entry.original.calls.map (·.2) ++ needed,key :: processed,
        rows ++ [(entry.original.key.moduleName,entry.original.source)] ++ paths.flatten))
    (original.map (·.2),[],direct.flatten)
  exactWork (Exact.charge ((needed.length+1)*(processed.length+1)))
  guard (needed.all processed.contains) .request
  pure rows

def expression (sources : Sources) (caller : String) (entries : List NaturalHelpers.Entry)
    (scope : List String) (original : Expr) : WorkM (List (String × String)) := do
  let calls ← LexicalNatural.originalBindings sources caller entries scope original
  bindings sources caller entries calls

/-- Original finite type readers admit Bits widths as Nat expressions. This
separate dependency pass retains their helper paths without changing the
complete type tree or treating an unused global helper as a query. -/
def typeTokens (sources : Sources) (caller : String) (entries : List NaturalHelpers.Entry)
    (scope : List String) : Nat → List String → WorkM (List (String × String)) :=
  Nat.rec (fun tokens => if tokens.isEmpty then pure [] else throw .limit)
    (fun _ next tokens => do
      match tokens with
      | "Bits" :: "<" :: rest =>
        let (width,ending) := rest.span (· != ">")
        let ">" :: tail := ending | throw .request
        exactWork (Exact.charge (32*(width.length+1)))
        let original ← lift ((NaturalSyntax.read width).mapError fun _ => .request)
        let rows ← expression sources caller entries scope original
        return rows ++ (← next tail)
      | _ :: rest => next rest
      | [] => pure [])

/-- Nominal fields use their own original closed scope. Exact source origins
in an already checked type forest identify those declarations; only actual
field-width helper calls and their dependency routes contribute rows. -/
def nominalOrigins (sources : Sources) (entries : List NaturalHelpers.Entry)
    (basis : Semantics.FiniteCarrier.Basis) : WorkM (List (String × String)) := do
  let bytes := (sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
  let rows ← basis.mapM fun atom => do
    let origin := match atom with
      | .enumeration origin _ | .record origin _ => some origin
      | _ => none
    match origin with
    | none => pure []
    | some origin =>
      exactWork (Exact.charge (32*(bytes+origin.source.utf8ByteSize+1)))
      let (source,declaration) ← lift ((lookup sources origin.moduleName origin.declarationName).mapError fun _ => .request)
      guard (source == origin.source) .request
      let expected := match atom with | .record .. => "struct" | _ => "enum"
      guard (declaration.kind == expected) .request
      let helpers ← if expected == "struct" then
        typeTokens sources origin.moduleName entries [] (declaration.body.length+1) declaration.body
        else pure []
      pure ((origin.moduleName,source) :: helpers)
  pure rows.flatten

def typeRead (sources : Sources) (caller : String) (entries : List NaturalHelpers.Entry)
    (scope tokens : List String) (query : TypeRead sources) : WorkM (List (String × String)) := do
  let direct ← typeTokens sources caller entries scope (tokens.length+1) tokens
  let fields ← nominalOrigins sources entries query.basis
  pure (query.sourceRows ++ direct ++ fields)

end QleisliKernel.SourceTypes.NaturalRows
