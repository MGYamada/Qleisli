import QleisliKernel.SourceTypes.StaticCallPremises
import QleisliKernel.SourceTypes.LexicalNatural
import QleisliKernel.SourceTypes.NaturalRows

/-! Basis actuals in the exact caller lexical/static environment. Original
type tokens, nominal origins, symbolic alias interpretation and closed widths
are checked independently; no selected closed declaration is synthesized.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.StaticBasisActual
open Finite Semantics.FiniteCarrier

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

def expressionSyntax {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (tokens : List LocatedToken) (inner : List String) : Bool :=
  tokens.map (·.text) == ["type","("] ++ inner ++ [")"] ||
    (inner.length == 1 && tokens.map (·.text) == inner &&
      instantiation.arguments.bases.any (fun argument => inner == [argument.1]))

def readType {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources))
    (inner : List String) : WorkM (TypeRead sources) := do
  let parameter (tokens : List String) : WorkM (Option (TypeRead sources)) :=
    match instantiation with
    | .closed _ => pure none
    | .static _ environment _ => StaticTypes.parameter environment tokens
  let natural (tokens : List String) : WorkM Nat := do
    let expression ← adapt (NaturalSyntax.read tokens)
    StaticCallPremises.validateNatural instantiation genericState scope expression
    pure (← LexicalNatural.read sources owner entries environment scope expression).result.value
  let query ← match instantiation.helpers with
    | none => typeExpressionScopedWithSources sources owner natural parameter inner
    | some helpers => typeExpressionScopedWithCheckedHelpers sources helpers owner natural parameter inner
  let _ ← FiniteCarrier.read query.basis
  pure query

def readRows {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources))
    (inner : List String) : WorkM (List (String × String)) := do
  let query ← readType instantiation entries environment scope genericState inner
  NaturalRows.typeRead sources owner entries scope inner query

structure Checked {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken) where
  inner : List String
  parsed : expressionSyntax instantiation tokens inner = true
  genericState : Option (GenericLexicalNatural.SomeEnvironment sources)
  query : TypeRead sources
  original : ∃ before after,(readType instantiation entries environment scope genericState inner).run before = (.ok query,after)
  rows : List (String × String)
  rowsRead : ∃ before after,(readRows instantiation entries environment scope genericState inner).run before = (.ok rows,after)

def read {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources))
    (tokens : List LocatedToken) : WorkM (Checked instantiation entries environment scope tokens) := do
  let texts := tokens.map (·.text)
  let inner := if texts.take 2 == ["type","("] then texts.drop 2 |>.dropLast else texts
  if parsed : expressionSyntax instantiation tokens inner = true then
    let query ← NaturalAffine.witness (readType instantiation entries environment scope genericState inner)
    let rows ← NaturalAffine.witness (readRows instantiation entries environment scope genericState inner)
    pure ⟨inner,parsed,genericState,query.val,by with_reducible exact query.property,
      rows.val,by with_reducible exact rows.property⟩
  else throw .request

end QleisliKernel.SourceTypes.StaticBasisActual
