import QleisliKernel.SourceTypes.StaticTypes
import QleisliKernel.SourceTypes.RuntimeSignature

/-! Original runtime signature instantiation for Basis and Nat actuals.
The complete original token occurrences, checked actuals and shared shape/effect
conditions remain bound together. This component does not grant host visibility,
operation capabilities, source-body preservation or native execution authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.StaticRuntimeSignature
open Finite

private def finiteType {sources owner name arguments}
    (environment : StaticTypes.Environment sources owner name arguments)
    (current : String) (tokens : List String) : WorkM (TypeRead sources) := do
  guard (current == owner) .request
  StaticTypes.readType environment tokens

def readParameters {sources owner name arguments}
    (environment : StaticTypes.Environment sources owner name arguments) :
    WorkM (List (RuntimeSignature.Part sources)) :=
  RuntimeSignature.readTypesWith sources (finiteType environment) owner
    environment.numeric.original.envelope.parsedHeader.parameterTypes

def readResult {sources owner name arguments}
    (environment : StaticTypes.Environment sources owner name arguments) :
    WorkM (RuntimeSignature.Part sources) :=
  RuntimeSignature.readTypeWith sources (finiteType environment) owner
    (environment.numeric.original.envelope.parsedHeader.resultTokens.map (·.text))

def readTypeRows {sources owner name arguments}
    (environment : StaticTypes.Environment sources owner name arguments)
    (parameters : List (RuntimeSignature.Part sources)) (result : RuntimeSignature.Part sources) :
    WorkM (List (String × String)) :=
  StaticInstantiation.readRowsWithTypes (.static arguments environment rfl)
    (((parameters.flatMap (·.queries)) ++ result.queries).map (·.basis))

structure Checked (sources : Sources) (owner name : String) (arguments : StaticTypes.Arguments) where
  environment : StaticTypes.Environment sources owner name arguments
  parameters : List (RuntimeSignature.Part sources)
  result : RuntimeSignature.Part sources
  parametersRead : ∃ before after,
    (readParameters environment).run before = (.ok parameters,after)
  resultRead : ∃ before after,
    (readResult environment).run before = (.ok result,after)
  conditions : RuntimeSignature.Conditions environment.numeric.original.envelope parameters result
  typeRows : List (String × String)
  typeRowsRead : ∃ before after,(readTypeRows environment parameters result).run before = (.ok typeRows,after)

def Checked.original {sources owner name arguments}
    (checked : Checked sources owner name arguments) : OrdinarySignature.Original sources owner name :=
  checked.environment.numeric.original.envelope

def fromEnvironment {sources owner name arguments}
    (environment : StaticTypes.Environment sources owner name arguments) :
    WorkM (Checked sources owner name arguments) := do
  let parameters ← NaturalAffine.witness (readParameters environment)
  let result ← NaturalAffine.witness (readResult environment)
  let conditions ← RuntimeSignature.checkConditions environment.numeric.original.envelope
    parameters.val result.val
  let typeRows ← NaturalAffine.witness (readTypeRows environment parameters.val result.val)
  return ⟨environment,parameters.val,result.val,
    by with_reducible exact parameters.property,by with_reducible exact result.property,conditions,
    typeRows.val,by with_reducible exact typeRows.property⟩

/-- Type-only preparation for an enclosing caller which separately checks all
operation actuals. The unresolved graph duties remain explicit in environment. -/
def prepareWithArguments (sources : Sources) (owner name : String) (arguments : StaticTypes.Arguments)
    (originals : Option (OrdinarySignature.Originals sources) := none)
    (helpers : Option (NaturalHelpers.Checked sources) := none) :
    WorkM (Checked sources owner name arguments) := do
  fromEnvironment (← StaticTypes.prepareWithObligations sources owner name arguments originals helpers)

/-- Existing runtime type routes stay strict: operation formals cannot pass
without the separate original-operation graph continuation. -/
def read (sources : Sources) (owner name : String) (arguments : StaticTypes.Arguments) :
    WorkM (Checked sources owner name arguments) := do
  fromEnvironment (← StaticTypes.prepare sources owner name arguments)

def Checked.sourceRows {sources owner name arguments}
    (checked : Checked sources owner name arguments) : List (String × String) :=
  let actualRows := arguments.bases.flatMap fun argument => argument.2.filterMap fun atom =>
    match atom with
    | .enumeration origin _ | .record origin _ => some (origin.moduleName,origin.source)
    | _ => none
  (owner,checked.environment.numeric.original.envelope.source) ::
    actualRows ++ ((checked.parameters.flatMap (·.queries)) ++ checked.result.queries).flatMap TypeRead.sourceRows ++ checked.typeRows

end QleisliKernel.SourceTypes.StaticRuntimeSignature
