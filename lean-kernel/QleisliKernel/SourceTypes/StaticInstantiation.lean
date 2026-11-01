import QleisliKernel.SourceTypes.StaticTypes
import QleisliKernel.SourceTypes.NaturalRows

/-! Original static environments shared by signature and source-application
readers. These are checked substitutions, not rewritten source declarations.
No body semantics, access path or execution authority is supplied here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.StaticInstantiation
open Finite

inductive Checked {sources owner name}
    (original : OrdinarySignature.Original sources owner name) where
  | closed (noStatics : original.parsedHeader.staticTokens.isNone &&
      original.parsedHeader.requiresTokens.isNone = true)
  | static (arguments : StaticTypes.Arguments)
      (environment : StaticTypes.Environment sources owner name arguments)
      (sameOriginal : environment.numeric.original.envelope = original)

def Checked.arguments {sources owner name original}
    (instantiation : @Checked sources owner name original) : StaticTypes.Arguments :=
  match instantiation with | .closed _ => {} | .static arguments _ _ => arguments

def Checked.names {sources owner name original}
    (instantiation : @Checked sources owner name original) : List String :=
  match instantiation with
  | .closed _ => []
  | .static _ environment _ => environment.numeric.original.header.formals.map (·.name)

def Checked.operationNames {sources owner name original}
    (instantiation : @Checked sources owner name original) : List String :=
  match instantiation with
  | .closed _ => []
  | .static _ environment _ => environment.numeric.original.header.formals.filterMap fun formal =>
      match formal.kind with | .operation _ => some formal.name | _ => none

def readType {sources owner name original}
    (instantiation : @Checked sources owner name original) (tokens : List String) :
    WorkM (TypeRead sources) :=
  match instantiation with
  | .closed _ => typeExpressionWithSources sources owner tokens
  | .static _ environment _ => StaticTypes.readType environment tokens

def readRows {sources owner name original}
    (instantiation : @Checked sources owner name original) : WorkM (List (String × String)) :=
  match instantiation with
  | .closed _ => do
    let tokens := original.parsedHeader.parameterTypes.flatten ++ original.parsedHeader.resultTokens.map (·.text)
    if !tokens.contains "Bits" then pure [] else do
      let helpers ← NaturalHelpers.prepare sources
      NaturalRows.typeTokens sources owner helpers [] (tokens.length+1) tokens
  | .static arguments environment _ => do
    let numeric ← NaturalRows.bindings sources owner environment.numeric.helpers environment.numeric.bindings
    let tokens := original.parsedHeader.parameterTypes.flatten ++ original.parsedHeader.resultTokens.map (·.text)
    let types ← NaturalRows.typeTokens sources owner environment.numeric.helpers instantiation.names (tokens.length+1) tokens
    let actuals ← NaturalRows.nominalOrigins sources environment.numeric.helpers (arguments.bases.flatMap (·.2))
    pure (numeric ++ types ++ actuals)

/-- Retain helper paths from each exact checked input/output type forest.
Nominal field scope remains its original declaration's closed scope. -/
def readRowsWithTypes {sources owner name original}
    (instantiation : @Checked sources owner name original) (forests : List Semantics.FiniteCarrier.Basis) :
    WorkM (List (String × String)) := do
  let original ← readRows instantiation
  let helpers ← match instantiation with
    | .closed _ => NaturalHelpers.prepare sources
    | .static _ environment _ => pure environment.numeric.helpers
  let fields ← forests.mapM (NaturalRows.nominalOrigins sources helpers)
  pure (original ++ fields.flatten)

end QleisliKernel.SourceTypes.StaticInstantiation
