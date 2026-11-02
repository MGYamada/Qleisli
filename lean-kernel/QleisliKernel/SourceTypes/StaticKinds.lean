import QleisliKernel.SourceTypes.StaticTypes
import QleisliKernel.SourceTypes.GenericLexicalNatural
import QleisliKernel.SourceTypes.LexicalNatural
import QleisliKernel.SourceTypes.NaturalRows

/-! Original operation-kind types resolve only preceding static formals.
Qualified/global type and helper names are resolved normally; matching a later
formal's spelling cannot change their category or supply a forward binding.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.StaticKinds
open Finite Semantics.FiniteCarrier

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

def readType {sources owner name arguments}
    (environment : StaticTypes.Environment sources owner name arguments) (ordinal : Nat) (tokens : List String) :
    WorkM (TypeRead sources) := do
  let formals := environment.numeric.original.header.formals.filter (·.ordinal < ordinal)
  let names := formals.map (·.name)
  let parameter (tokens : List String) : WorkM (Option (TypeRead sources)) := do
    let [name] := tokens | pure none
    exactWork (Exact.charge ((name.utf8ByteSize+1)*(formals.length+arguments.bases.length+1)))
    match formals.find? (·.name == name) with
    | none => pure none
    | some formal =>
      guard (formal.kind == .basis) .request
      let some (_,basis) := arguments.bases.find? (·.1 == name) | throw .request
      pure (some ⟨basis,[]⟩)
  let natural (tokens : List String) : WorkM Nat := do
    let expression ← adapt (NaturalSyntax.read tokens)
    let _ ← GenericLexicalNatural.read environment.numeric (GenericLexicalNatural.initial environment.numeric) names expression
    let lexical := LexicalNatural.ofBindings environment.numeric.helpers arguments.naturals
    let closed ← LexicalNatural.read sources owner environment.numeric.helpers lexical names expression
    pure closed.result.value
  let helpers : NaturalHelpers.Checked sources := ⟨environment.numeric.helpers,environment.numeric.helpersPrepared⟩
  let read ← typeExpressionScopedWithCheckedHelpers sources helpers owner natural parameter tokens
  let _ ← FiniteCarrier.read read.basis
  pure read

def readRows {sources owner name arguments}
    (environment : StaticTypes.Environment sources owner name arguments) (ordinal : Nat) (tokens : List String) :
    WorkM (List (String × String)) := do
  let query ← readType environment ordinal tokens
  let names := (environment.numeric.original.header.formals.filter (·.ordinal < ordinal)).map (·.name)
  NaturalRows.typeRead sources owner environment.numeric.helpers names tokens query

end QleisliKernel.SourceTypes.StaticKinds
