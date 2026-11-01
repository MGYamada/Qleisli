import QleisliKernel.SourceTypes.QuantumSignature
import QleisliKernel.SourceTypes.StaticApplication
import QleisliKernel.SourceTypes.SourceOperation

/-! Selection of an original generic source provider from its actual caller
environment and checked lexical/module/prelude candidate. Every positional
actual survives even when unused; no closed AST or source text is synthesized.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.QuantumSignature
open Finite

def candidateResolution {sources caller scope tokens}
    (candidate : CallName.Checked sources caller scope tokens) : Option Resolved :=
  match candidate.decision with
  | .named resolution | .prelude _ _ _ _ _ _ _ _ resolution => some resolution.result
  | _ => none

structure InstanceSelected {sources caller callerName}
    (callerSignature : Checked sources caller callerName)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) {tokens : List LocatedToken} (written : StaticApplication.Syntax tokens)
    (candidate : CallName.Checked sources caller scope written.callee) where
  resolution : Resolved
  selected : candidateResolution candidate = some resolution
  operationReader : StaticApplication.OperationReader
  actuals : StaticApplication.Checked callerSignature.instantiation entries environment scope operationReader written
    resolution.moduleName resolution.declaration.name
  signature : Checked sources resolution.moduleName resolution.declaration.name
  arguments : signature.staticArguments = actuals.arguments
  declared : signature.original.source = resolution.source ∧
    signature.original.declaration = resolution.declaration
  originalActuals : actuals.target.envelope.source = signature.original.source ∧
    actuals.target.envelope.declaration = signature.original.declaration

def selectInstance {sources caller callerName}
    (callerSignature : Checked sources caller callerName)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) {tokens : List LocatedToken} (written : StaticApplication.Syntax tokens)
    (candidate : CallName.Checked sources caller scope written.callee) :
    WorkM (InstanceSelected callerSignature entries environment scope written candidate) := do
  match selected : candidateResolution candidate with
  | none => throw .request
  | some resolution =>
    let operationReader := SourceOperation.build callerSignature.toChecked entries environment scope 65
    let actuals ← StaticApplication.read callerSignature.instantiation entries environment scope written
      resolution.moduleName resolution.declaration.name operationReader
    let signature ← readWithArguments sources resolution.moduleName resolution.declaration.name actuals.arguments (.source caller)
    let bytes := (sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
    exactWork (Exact.charge (8*(bytes+tokens.length+1)*
      (actuals.arguments.bases.length+actuals.arguments.naturals.length+1)^2))
    if arguments : signature.staticArguments = actuals.arguments then
      if declared : signature.original.source = resolution.source ∧
          signature.original.declaration = resolution.declaration then
        if originalActuals : actuals.target.envelope.source = signature.original.source ∧
            actuals.target.envelope.declaration = signature.original.declaration then
          return ⟨resolution,selected,operationReader,actuals,signature,arguments,declared,originalActuals⟩
        else throw .request
      else throw .request
    else throw .request

/-- The common operation projection keeps the selected untouched signature;
its source witness distinguishes closed lookup from an original application.
The existential witness is provenance only and grants no body/access claim. -/
structure OperationSelection (sources : Sources) (caller : String) (tokens : List LocatedToken) where
  resolution : Resolved
  signature : Checked sources resolution.moduleName resolution.declaration.name
  declared : signature.original.source = resolution.source ∧
    signature.original.declaration = resolution.declaration
  original :
    (∃ selected : Selected sources caller (tokens.map (·.text)),
      selected.resolution = resolution ∧ HEq selected.signature signature) ∨
    (∃ callerName (callerSignature : Checked sources caller callerName)
      (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
      (scope : List String) (written : StaticApplication.Syntax tokens)
      (candidate : CallName.Checked sources caller scope written.callee)
      (selected : InstanceSelected callerSignature entries environment scope written candidate),
      selected.resolution = resolution ∧ HEq selected.signature signature)

def OperationSelection.closed {sources caller tokens}
    (selected : Selected sources caller (tokens.map (·.text))) :
    OperationSelection sources caller tokens :=
  ⟨selected.resolution,selected.signature,selected.declared,Or.inl ⟨selected,rfl,HEq.rfl⟩⟩

def OperationSelection.instantiated {sources caller callerName tokens}
    (callerSignature : Checked sources caller callerName)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (written : StaticApplication.Syntax tokens)
    (candidate : CallName.Checked sources caller scope written.callee)
    (selected : InstanceSelected callerSignature entries environment scope written candidate) :
    OperationSelection sources caller tokens :=
  ⟨selected.resolution,selected.signature,selected.declared,
    Or.inr ⟨callerName,callerSignature,entries,environment,scope,written,candidate,selected,rfl,HEq.rfl⟩⟩

end QleisliKernel.SourceTypes.QuantumSignature
