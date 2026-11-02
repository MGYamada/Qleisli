import QleisliKernel.SourceTypes.StaticOperation

/-! Original quantum signatures with independently checked operation-actual
graphs. The type-only core keeps exact original tokens and static premises;
this layer discharges complete formal/actual graph obligations. Original body,
inverse/control and constructed-body equations still belong to native gates.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.QuantumSignature
open Semantics.FiniteCarrier Semantics.Raw Finite

abbrev ResultParts := QuantumSignatureCore.ResultParts
abbrev ResultParts.clauses := QuantumSignatureCore.ResultParts.clauses
abbrev Instantiation := @QuantumSignatureCore.Instantiation
abbrev quantumTokens := QuantumSignatureCore.quantumTokens
abbrev resultParts := QuantumSignatureCore.resultParts
abbrev readType := QuantumSignatureCore.readType
abbrev readTypes := QuantumSignatureCore.readTypes
abbrev readTypeWith := @QuantumSignatureCore.readTypeWith
abbrev readQuantumTypes := @QuantumSignatureCore.readQuantumTypes
abbrev TypePostcondition := QuantumSignatureCore.TypePostcondition
abbrev readType_bound := QuantumSignatureCore.readType_bound

structure Checked (sources : Sources) (owner name : String) extends
    QuantumSignatureCore.Checked sources owner name where
  context : StaticOperation.Context
  operations : StaticOperation.ArgumentsChecked toChecked context
  staticRows : List (String × String)
  staticRowsRead : ∃ before after,
    (StaticInstantiation.readRowsWithTypes toChecked.instantiation (toChecked.inputs ++ toChecked.outputs)).run before = (.ok staticRows,after)

def Checked.staticArguments {sources owner name} (checked : Checked sources owner name) : StaticTypes.Arguments :=
  checked.toChecked.staticArguments

def Checked.staticNames {sources owner name} (checked : Checked sources owner name) : List String :=
  checked.toChecked.staticNames

def Checked.operationNames {sources owner name} (checked : Checked sources owner name) : List String :=
  checked.instantiation.operationNames

def Checked.inputs {sources owner name} (checked : Checked sources owner name) : List Basis :=
  checked.toChecked.inputs

def Checked.outputs {sources owner name} (checked : Checked sources owner name) : List Basis :=
  checked.toChecked.outputs

def Checked.sourceRows {sources owner name} (checked : Checked sources owner name) : List (String × String) :=
  checked.toChecked.sourceRows ++ checked.staticRows ++ checked.operations.sourceRows

structure WithCore {sources owner name} (signature : QuantumSignatureCore.Checked sources owner name) where
  checked : Checked sources owner name
  originalCore : checked.toChecked = signature

/-- Complete a type-only original signature without rereading or substituting
its source envelope. The native provider-body continuation receives that exact
core plus all checked actuals and original numeric lookup dependencies. -/
def fromCore {sources owner name} (signature : QuantumSignatureCore.Checked sources owner name)
    (context : StaticOperation.Context) (catalogue : Option (GenericCatalogue.Checked sources) := none) : WorkM (WithCore signature) := do
  let operations ← StaticOperation.checkArguments signature context catalogue
  let rows ← NaturalAffine.witness (StaticInstantiation.readRowsWithTypes signature.instantiation (signature.inputs ++ signature.outputs))
  return ⟨⟨signature,context,operations,rows.val,by with_reducible exact rows.property⟩,rfl⟩

/-- Reuse original checked argument receipts at a provider/call boundary.
The original core is unchanged, and no child is reread in the callee module. -/
def fromCoreWithArguments {sources owner name} (signature : QuantumSignatureCore.Checked sources owner name)
    (context : StaticOperation.Context) (operations : StaticOperation.ArgumentsChecked signature context) :
    WorkM (WithCore signature) := do
  let rows ← NaturalAffine.witness (StaticInstantiation.readRowsWithTypes signature.instantiation (signature.inputs ++ signature.outputs))
  pure ⟨⟨signature,context,operations,rows.val,by with_reducible exact rows.property⟩,rfl⟩

def Checked.supply {sources owner name} (signature : Checked sources owner name) :
    StaticOperation.Supply signature.instantiation := ⟨signature.context,signature.operations⟩

def read (sources : Sources) (owner name : String) : WorkM (Checked sources owner name) := do
  let signature ← QuantumSignatureCore.read sources owner name
  return (← fromCore signature .external).checked

/-- The untouched header is prepared before checking every operation actual.
Existing closed callers cannot obtain an unresolved operation formal. Source
applications pass their original module context; host selections stay external. -/
def readWithArguments (sources : Sources) (owner name : String) (arguments : StaticTypes.Arguments)
    (context : StaticOperation.Context := .external) (catalogue : Option (GenericCatalogue.Checked sources) := none) :
    WorkM (Checked sources owner name) := do
  let signature ← QuantumSignatureCore.prepareWithArguments sources owner name arguments
  return (← fromCore signature context catalogue).checked

structure ResolvedSelection (sources : Sources) (resolution : Resolved) where
  signature : Checked sources resolution.moduleName resolution.declaration.name
  declared : signature.original.source = resolution.source ∧
    signature.original.declaration = resolution.declaration

def fromResolution {sources caller tokens}
    (resolution : CallName.Resolution sources caller tokens) (arguments : StaticTypes.Arguments) :
    WorkM (ResolvedSelection sources resolution.result) := do
  let signature ← readWithArguments sources resolution.result.moduleName resolution.result.declaration.name
    arguments (.source caller)
  if declared : signature.original.source = resolution.result.source ∧
      signature.original.declaration = resolution.result.declaration then
    return ⟨signature,declared⟩
  else throw .request

structure Selected (sources : Sources) (caller : String) (tokens : List String) where
  resolution : Resolved
  signature : Checked sources resolution.moduleName resolution.declaration.name
  resolved : ∃ before after,
    (ResolutionProvenance.read sources caller tokens).run before = (.ok resolution,after)
  declared : signature.original.source = resolution.source ∧
    signature.original.declaration = resolution.declaration

def select (sources : Sources) (caller : String) (tokens : List String) :
    WorkM (Selected sources caller tokens) := do
  guard (sources.size ≤ 128) .limit
  guard ((sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum ≤ 1048576) .limit
  let resolution ← NaturalAffine.witness (ResolutionProvenance.read sources caller tokens)
  let signature ← read sources resolution.val.moduleName resolution.val.declaration.name
  if same : signature.original.source = resolution.val.source ∧
      signature.original.declaration = resolution.val.declaration then
    return ⟨resolution.val,signature,by with_reducible exact resolution.property,same⟩
  else throw .request

theorem Selected.query {sources caller tokens} (checked : Selected sources caller tokens) :
    Semantics.SourceResolution.Query sources caller tokens checked.resolution.visited
      (ResolutionTrace.resolvedView checked.resolution) ∧
      ResolutionTrace.OriginalLookups sources checked.resolution.visited := by
  obtain ⟨before,after,ran⟩ := checked.resolved
  exact ResolutionProvenance.read_query _ _ _ _ _ _ ran

end QleisliKernel.SourceTypes.QuantumSignature
