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

abbrev MarkedSlot := AccessSyntax.MarkedSlot

structure Interface {sources owner name} (original : OrdinarySignature.Original sources owner name)
    (reader : String → List String → WorkM (TypeRead sources)) where
  parameters : List (RuntimeSignature.Part sources)
  result : RuntimeSignature.Part sources
  declared : Option (RuntimeSignature.DeclaredAccess original reader)

/-- The runtime port view of a declared access is available to an original
marked call that supplies the same roles in the same slots. Preserve the
written Unit result in the retained declared interface. -/
def readInterface {sources owner name arguments}
    (environment : StaticTypes.Environment sources owner name arguments)
    (access : List MarkedSlot) : WorkM (Interface environment.numeric.original.envelope (finiteType environment)) := do
  let original := environment.numeric.original.envelope
  if !access.isEmpty && AccessSyntax.hasDeclaredTypes original.parsedHeader.parameterTypes then
    let declared ← RuntimeSignature.readDeclaredAccessWith original (finiteType environment)
    guard (access == declared.written.markedSlots) .request
    return ⟨declared.parameters,⟨declared.hiddenResult,declared.sourceResult.queries⟩,some declared⟩
  else
    return ⟨← readParameters environment,← readResult environment,none⟩

def readTypeRows {sources owner name arguments}
    (environment : StaticTypes.Environment sources owner name arguments)
    (parameters : List (RuntimeSignature.Part sources)) (result : RuntimeSignature.Part sources) :
    WorkM (List (String × String)) :=
  StaticInstantiation.readRowsWithTypes (.static arguments environment rfl)
    (((parameters.flatMap (·.queries)) ++ result.queries).map (·.basis))

structure Checked (sources : Sources) (owner name : String) (arguments : StaticTypes.Arguments) where
  environment : StaticTypes.Environment sources owner name arguments
  access : List MarkedSlot
  portView : Interface environment.numeric.original.envelope (finiteType environment)
  interfaceRead : ∃ before after,
    (readInterface environment access).run before = (.ok portView,after)
  conditions : RuntimeSignature.Conditions environment.numeric.original.envelope portView.parameters portView.result
  typeRows : List (String × String)
  typeRowsRead : ∃ before after,
    (readTypeRows environment portView.parameters portView.result).run before = (.ok typeRows,after)

def Checked.parameters {sources owner name arguments} (checked : Checked sources owner name arguments) :=
  checked.portView.parameters

def Checked.result {sources owner name arguments} (checked : Checked sources owner name arguments) :=
  checked.portView.result

def Checked.original {sources owner name arguments}
    (checked : Checked sources owner name arguments) : OrdinarySignature.Original sources owner name :=
  checked.environment.numeric.original.envelope

def fromEnvironment {sources owner name arguments}
    (environment : StaticTypes.Environment sources owner name arguments)
    (access : List MarkedSlot := []) : WorkM (Checked sources owner name arguments) := do
  let interface ← NaturalAffine.witness (readInterface environment access)
  let conditions ← RuntimeSignature.checkConditions environment.numeric.original.envelope
    interface.val.parameters interface.val.result
  let typeRows ← NaturalAffine.witness (readTypeRows environment interface.val.parameters interface.val.result)
  return ⟨environment,access,interface.val,by with_reducible exact interface.property,conditions,
    typeRows.val,by with_reducible exact typeRows.property⟩

/-- Type-only preparation for an enclosing caller which separately checks all
operation actuals. The unresolved graph duties remain explicit in environment. -/
def prepareWithArguments (sources : Sources) (owner name : String) (arguments : StaticTypes.Arguments)
    (originals : Option (OrdinarySignature.Originals sources) := none)
    (helpers : Option (NaturalHelpers.Checked sources) := none) (access : List MarkedSlot := []) :
    WorkM (Checked sources owner name arguments) := do
  fromEnvironment (← StaticTypes.prepareWithObligations sources owner name arguments originals helpers) access

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
