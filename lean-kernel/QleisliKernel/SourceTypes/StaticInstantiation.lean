import QleisliKernel.SourceTypes.StaticTypes

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
    (instance : @Checked sources owner name original) : StaticTypes.Arguments :=
  match instance with | .closed _ => {} | .static arguments _ _ => arguments

def Checked.names {sources owner name original}
    (instance : @Checked sources owner name original) : List String :=
  match instance with
  | .closed _ => []
  | .static _ environment _ => environment.numeric.original.header.formals.map (·.name)

def readType {sources owner name original}
    (instance : @Checked sources owner name original) (tokens : List String) :
    WorkM (TypeRead sources) :=
  match instance with
  | .closed _ => typeExpressionWithSources sources owner tokens
  | .static _ environment _ => StaticTypes.readType environment tokens

end QleisliKernel.SourceTypes.StaticInstantiation
