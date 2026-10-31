import QleisliKernel.Qirf.PureInterval
import QleisliKernel.SourceTypes.QuantumBody

/-! Bind a complete structural source function to its actual qmatch interval.
All original quantum parameters and returned roles remain present, including
spectators and zero-width owners. This first context rule has one qmatch with
structural moves around it; calls, allocation and general control flow require
their own source rules. Arm/code/control equations, fresh graph reconstruction
and paired native/QDV dispatch remain mandatory enclosing checks. No accepted
handle or new source preservation claim is supplied by this component.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceInterval
open Finite Semantics.SourceOwners

def parameterOwners {sources owner name}
    (signature : SourceTypes.QuantumSignature.Checked sources owner name) : List Owner :=
  signature.inputs.zipIdx |>.map fun (basis,index) => ⟨index,basis⟩

def inputTokens (program : Semantics.Observation.Program) (roles : List Owner) : Option (List Nat) :=
  roles.mapM fun role => (program.inputs[role.ordinal]?).map (·.token)

/-- Return positions come from the complete original source result. Token
numbers and physical widths cannot choose between equal-width source owners. -/
def outputTokens (program : Semantics.Observation.Program) (returned selected : List Owner) : Option (List Nat) :=
  if returned.length != program.outputs.length then none else
  selected.mapM fun role =>
    ((returned.zip program.outputs).find? fun pair => pair.1 == role).map Prod.snd

def inputWidths (program : Semantics.Observation.Program) (roles : List Owner) : Bool :=
  program.inputs.length == roles.length && (program.inputs.zip roles).all fun (port,role) =>
    ((Semantics.FiniteCarrier.layout role.basis).map (·.bits)) == some port.bits

def effectMatches (declared : Option Semantics.Raw.Effect) (actual : Semantics.Raw.Effect) : Prop :=
  match declared with | none => actual = .unitary | some effect => actual = effect

instance (declared : Option Semantics.Raw.Effect) (actual : Semantics.Raw.Effect) :
    Decidable (effectMatches declared actual) := by
  cases declared <;> unfold effectMatches <;> infer_instance

structure Prepared {sources owner name offset}
    (site : SourceTypes.QuantumMatch.Site sources owner name offset)
    (selector target : Semantics.FiniteCarrier.Basis) where
  operands : SourceTypes.QuantumOperands.Checked site selector target
  body : SourceTypes.QuantumBody.Checked operands

def read {sources owner name offset}
    (site : SourceTypes.QuantumMatch.Site sources owner name offset)
    (selector target : Semantics.FiniteCarrier.Basis) : WorkM (Prepared site selector target) := do
  let operands ← SourceTypes.QuantumOperands.read site selector target
  let body ← SourceTypes.QuantumBody.read operands
  return ⟨operands,body⟩

structure Checked {sources owner name offset}
    (site : SourceTypes.QuantumMatch.Site sources owner name offset)
    (selector target : Semantics.FiniteCarrier.Basis) (dependencies : List Semantics.Finite.Dependency)
    (program : Semantics.Observation.Program) where
  operands : SourceTypes.QuantumOperands.Checked site selector target
  body : SourceTypes.QuantumBody.Checked operands
  effect : effectMatches operands.signature.original.parsedHeader.effect program.effect
  noClassical : program.classicalInputs = [] ∧ program.classicalOutputs = []
  widths : inputWidths program (parameterOwners operands.signature) = true
  inputs : List Nat
  inputBinding : inputTokens program [operands.selector,operands.target] = some inputs
  outputs : List Nat
  outputBinding : outputTokens program (valueOwners body.outcome.value)
    [operands.selector,operands.target] = some outputs
  interval : PureInterval.Checked dependencies program 0 program.operations.length inputs outputs
    [operands.selector,operands.target]
  allOwners : Semantics.RawOwnerFlow.Returns (parameterOwners operands.signature)
    ⟨program.inputs,interval.slice.operations,program.outputs,.unitary⟩ (valueOwners body.outcome.value)

/-- A structural source body emits only its focused operation: the original
complete operation list is the interval. There is no producer-selected offset,
invented source wrapper, skipped prefix or selected subset of return owners. -/
def checkFrom {sources owner name offset selector target}
    {site : SourceTypes.QuantumMatch.Site sources owner name offset}
    (source : Prepared site selector target) (dependencies : List Semantics.Finite.Dependency)
    (program : Semantics.Observation.Program) : WorkM (Checked site selector target dependencies program) := do
  let operands := source.operands
  let body := source.body
  let allInputs := parameterOwners operands.signature
  let allOutputs := valueOwners body.outcome.value
  -- Charge complete source identities before lookup/equality and physical layouts.
  exactWork (Exact.charge (32*(Raw.OwnerFlow.fields allInputs+Raw.OwnerFlow.fields allOutputs+1)*
    (allInputs.length+allOutputs.length+1)^2))
  if effect : effectMatches operands.signature.original.parsedHeader.effect program.effect then
    if noClassical : program.classicalInputs = [] ∧ program.classicalOutputs = [] then
      if widths : inputWidths program allInputs = true then
        match inputBinding : inputTokens program [operands.selector,operands.target] with
        | none => throw .request
        | some inputs =>
          match outputBinding : outputTokens program allOutputs [operands.selector,operands.target] with
          | none => throw .request
          | some outputs =>
            let interval ← PureInterval.check dependencies program 0 program.operations.length inputs outputs
              [operands.selector,operands.target]
            let allOwners ← Raw.OwnerFlow.check allInputs allOutputs
              ⟨program.inputs,interval.slice.operations,program.outputs,.unitary⟩
            return ⟨operands,body,effect,noClassical,widths,inputs,inputBinding,outputs,outputBinding,
              interval,allOwners.down⟩
      else throw .request
    else throw .request
  else throw .request

def check {sources owner name offset}
    (site : SourceTypes.QuantumMatch.Site sources owner name offset)
    (selector target : Semantics.FiniteCarrier.Basis) (dependencies : List Semantics.Finite.Dependency)
    (program : Semantics.Observation.Program) : WorkM (Checked site selector target dependencies program) := do
  let source ← read site selector target
  checkFrom source dependencies program

theorem Checked.originalBody {sources owner name offset selector target dependencies program}
    {site : SourceTypes.QuantumMatch.Site sources owner name offset}
    (checked : Checked site selector target dependencies program) :
    site.original.occurrence.body = site.leading ++ site.parsed.tokens ++ site.suffix :=
  checked.body.originalBody

theorem Checked.completeOperations {sources owner name offset selector target dependencies program}
    {site : SourceTypes.QuantumMatch.Site sources owner name offset}
    (checked : Checked site selector target dependencies program) :
    program.operations = checked.interval.slice.operations.map Semantics.Observation.Op.pure := by
  simpa using checked.interval.originalOperations

/-- Public Observe/Isometry remains the outer label even though the selected
interval is pure. An internal component cannot sharpen that public contract. -/
theorem Checked.publicEffect {sources owner name offset selector target dependencies program}
    {site : SourceTypes.QuantumMatch.Site sources owner name offset}
    (checked : Checked site selector target dependencies program)
    (isPublic : checked.operands.signature.original.declaration.isPublic = true) :
    checked.operands.signature.original.parsedHeader.effect = some program.effect := by
  have present := checked.operands.signature.publicEffect isPublic
  have effect := checked.effect
  cases h : checked.operands.signature.original.parsedHeader.effect with
  | none => simp [h] at present
  | some declared =>
    simp only [effectMatches,h] at effect
    simp only [effect]

end QleisliKernel.Qirf.SourceInterval
