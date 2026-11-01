import QleisliKernel.SourceTypes.StaticInstantiation
import QleisliKernel.SourceTypes.CallName

/-! Original quantum parameter/result forests and public effect metadata.
This informed component does not prove body lowering, create control access or
issue an accepted handle. Original site/arm and native/QDV binding remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.QuantumSignatureCore
open Semantics.FiniteCarrier Semantics.Raw Finite

inductive ResultParts where
  | owner (tokens : List String)
  | tuple (parts : List (List String))
  deriving BEq, DecidableEq, Repr

private def flattenClauses : Nat → List String → List (List String) :=
  Nat.rec (fun tokens => [tokens]) (fun _ next tokens =>
    if tokens.head? == some "Q" then [tokens]
    else match tokens with
    | "(" :: rest =>
      if rest.getLast? == some ")" then
        match splitMembers rest.dropLast with
        | .ok parts => if parts.length ≥ 2 then parts.flatMap next else [tokens]
        | .error _ => [tokens]
      else [tokens]
    | _ => [tokens])

/-- Flatten only the owner forest; `parts` keeps the original outer/nested
tuple clauses for the independent exact result-shape judgment. Malformed
children remain attempted owner clauses and cannot silently disappear. -/
def ResultParts.clauses : ResultParts → List (List String)
  | .owner tokens => [tokens]
  | .tuple parts => parts.flatMap (flattenClauses 65)

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

def quantumTokens (tokens : List String) : Except String (List String) := do
  let "Q" :: "<" :: rest := tokens | throw "expected one quantum owner"
  if rest.getLast? != some ">" || rest.dropLast.isEmpty then throw "incomplete quantum owner"
  return rest.dropLast

def resultParts (tokens : List String) : Except String ResultParts := do
  if tokens.head? == some "Q" then return .owner tokens
  let "(" :: rest := tokens | throw "expected quantum result owner or tuple"
  if rest.getLast? != some ")" then throw "incomplete quantum result tuple"
  return .tuple (← splitMembers rest.dropLast)

def readType (sources : Sources) (owner : String) (tokens : List String) :
    WorkM (TypeRead sources) := do
  let inner ← adapt (quantumTokens tokens)
  let result ← typeExpressionWithSources sources owner inner
  let _ ← FiniteCarrier.read result.basis
  return result

def readTypes (sources : Sources) (owner : String) (tokens : List (List String)) :
    WorkM (List (TypeRead sources)) := do
  guard (tokens.length ≤ 64) .limit
  let result ← tokens.mapM (readType sources owner)
  guard ((result.map fun ty => ty.basis.length).sum ≤ 128) .limit
  return result

/-- A closed header and an instantiated original header have different read
obligations. Neither alternative replaces the original declaration or tokens. -/
abbrev Instantiation {sources owner name}
    (original : OrdinarySignature.Original sources owner name) := StaticInstantiation.Checked original

def Instantiation.arguments {sources owner name original}
    (instantiation : @Instantiation sources owner name original) : StaticTypes.Arguments :=
  StaticInstantiation.Checked.arguments instantiation

def Instantiation.names {sources owner name original}
    (instantiation : @Instantiation sources owner name original) : List String :=
  StaticInstantiation.Checked.names instantiation

def readTypeWith {sources owner name original}
    (instantiation : @Instantiation sources owner name original) (tokens : List String) :
    WorkM (TypeRead sources) :=
  StaticInstantiation.readType instantiation tokens

def readQuantumTypes {sources owner name original}
    (instantiation : @Instantiation sources owner name original) (tokens : List (List String)) :
    WorkM (List (TypeRead sources)) :=
  match instantiation with
  | .closed _ => readTypes sources owner tokens
  | .static _ environment _ => do
    guard (tokens.length ≤ 64) .limit
    let result ← tokens.mapM fun tokens => do
      let inner ← adapt (quantumTokens tokens)
      StaticTypes.readType environment inner
    guard ((result.map fun ty => ty.basis.length).sum ≤ 128) .limit
    pure result

structure Checked (sources : Sources) (owner name : String) where
  original : OrdinarySignature.Original sources owner name
  instantiation : Instantiation original
  parts : ResultParts
  parameterReads : List (TypeRead sources)
  resultReads : List (TypeRead sources)
  quantum : original.parsedHeader.ordinaryOnly = false
  publicEffect : original.declaration.isPublic = true → original.parsedHeader.effect.isSome = true
  resultPartsRead : resultParts (original.parsedHeader.resultTokens.map (·.text)) = .ok parts
  inputsRead : ∃ before after,
    (readQuantumTypes instantiation original.parsedHeader.parameterTypes).run before = (.ok parameterReads,after)
  outputsRead : ∃ before after,
    (readQuantumTypes instantiation parts.clauses).run before = (.ok resultReads,after)

def Checked.staticArguments {sources owner name} (checked : Checked sources owner name) :
    StaticTypes.Arguments := checked.instantiation.arguments

def Checked.staticNames {sources owner name} (checked : Checked sources owner name) : List String :=
  checked.instantiation.names

def Checked.inputs {sources owner name} (checked : Checked sources owner name) : List Basis :=
  checked.parameterReads.map (·.basis)

def Checked.outputs {sources owner name} (checked : Checked sources owner name) : List Basis :=
  checked.resultReads.map (·.basis)

/-- Type queries retain exact recursive import/reexport routes. The function
row is justified separately by the original declaration lookup and envelope. -/
def Checked.sourceRows {sources owner name} (checked : Checked sources owner name) : List (String × String) :=
  let actualRows := checked.staticArguments.bases.flatMap fun argument => argument.2.filterMap fun atom =>
    match atom with
    | .enumeration origin _ | .record origin _ => some (origin.moduleName,origin.source)
    | _ => none
  (owner,checked.original.source) ::
    actualRows ++ (checked.parameterReads ++ checked.resultReads).flatMap TypeRead.sourceRows

def read (sources : Sources) (owner name : String) : WorkM (Checked sources owner name) := do
  let original ← OrdinarySignature.readOriginal sources owner name
  let instantiation ← if noStatics : original.parsedHeader.staticTokens.isNone &&
      original.parsedHeader.requiresTokens.isNone = true then
    pure (StaticInstantiation.Checked.closed noStatics)
    else throw .request
  if ordinary : original.parsedHeader.ordinaryOnly = false then
    if effect : original.declaration.isPublic = true → original.parsedHeader.effect.isSome = true then
      let tokens := original.parsedHeader.resultTokens.map (·.text)
      match parsed : resultParts tokens with
      | .error _ => throw .request
      | .ok parts =>
        let inputs ← NaturalAffine.witness (readQuantumTypes instantiation original.parsedHeader.parameterTypes)
        let outputs ← NaturalAffine.witness (readQuantumTypes instantiation parts.clauses)
        return ⟨original,instantiation,parts,inputs.val,outputs.val,ordinary,effect,parsed,
          by with_reducible exact inputs.property,by with_reducible exact outputs.property⟩
    else throw .request
  else throw .request

/-- Complete checked actuals close types on the untouched source envelope.
Unused actuals and the original ordered numeric premises are checked by the
shared StaticTypes environment before any parameter or result read. -/
def prepareWithArguments (sources : Sources) (owner name : String) (arguments : StaticTypes.Arguments) :
    WorkM (Checked sources owner name) := do
  let environment ← StaticTypes.prepareWithObligations sources owner name arguments
  let original := environment.numeric.original.envelope
  let instantiation := StaticInstantiation.Checked.static arguments environment rfl
  if ordinary : original.parsedHeader.ordinaryOnly = false then
    if effect : original.declaration.isPublic = true → original.parsedHeader.effect.isSome = true then
      match parsed : resultParts (original.parsedHeader.resultTokens.map (·.text)) with
      | .error _ => throw .request
      | .ok parts =>
        let inputs ← NaturalAffine.witness (readQuantumTypes instantiation original.parsedHeader.parameterTypes)
        let outputs ← NaturalAffine.witness (readQuantumTypes instantiation parts.clauses)
        return ⟨original,instantiation,parts,inputs.val,outputs.val,ordinary,effect,parsed,
          by with_reducible exact inputs.property,by with_reducible exact outputs.property⟩
    else throw .request
  else throw .request

structure ResolvedSelection (sources : Sources) (resolution : Resolved) where
  signature : Checked sources resolution.moduleName resolution.declaration.name
  declared : signature.original.source = resolution.source ∧
    signature.original.declaration = resolution.declaration

/-- Reuse a checked lexical/module/prelude candidate instead of resolving a
new spelling after static specialization. Candidate lookup still grants no
body effect, access path, source interval or execution authority. -/
def fromResolution {sources caller tokens}
    (resolution : CallName.Resolution sources caller tokens) (arguments : StaticTypes.Arguments) :
    WorkM (ResolvedSelection sources resolution.result) := do
  let signature ← prepareWithArguments sources resolution.result.moduleName resolution.result.declaration.name arguments
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
  guard ((sources.toList.map fun row => row.1.utf8ByteSize + row.2.utf8ByteSize).sum ≤ 1048576) .limit
  let resolution ← NaturalAffine.witness (ResolutionProvenance.read sources caller tokens)
  let signature ← read sources resolution.val.moduleName resolution.val.declaration.name
  if same : signature.original.source = resolution.val.source ∧
      signature.original.declaration = resolution.val.declaration then
    return ⟨resolution.val,signature,by with_reducible exact resolution.property,same⟩
  else throw .request

/-- The caller must still bind its query to an actual source-site occurrence.
The retained route is fresh lookup evidence, not a caller authentication token. -/
theorem Selected.query {sources caller tokens} (checked : Selected sources caller tokens) :
    Semantics.SourceResolution.Query sources caller tokens checked.resolution.visited
      (ResolutionTrace.resolvedView checked.resolution) ∧
      ResolutionTrace.OriginalLookups sources checked.resolution.visited := by
  obtain ⟨before,after,ran⟩ := checked.resolved
  exact ResolutionProvenance.read_query _ _ _ _ _ _ ran

structure TypePostcondition (sources : Sources) (owner : String) (tokens : List String)
    (result : TypeRead sources) : Prop where
  originalTokens : ∃ inner, quantumTokens tokens = .ok inner ∧ ∃ before after,
    (typeExpressionWithSources sources owner inner).run before = (.ok result,after)
  layout : ∃ layout, Semantics.FiniteCarrier.layout result.basis = some layout

theorem readType_bound (sources : Sources) (owner : String) (tokens : List String)
    (result : TypeRead sources) (work left : Nat)
    (ok : (readType sources owner tokens).run work = (.ok result,left)) :
    TypePostcondition sources owner tokens result := by
  obtain ⟨inner,w₁,ht,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨read,w₂,hr,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨layout,w₃,hl,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst result
  have parsed := (lift_success _ _ _ _ ht).1
  have original : quantumTokens tokens = .ok inner := by
    cases decoded : quantumTokens tokens <;> simp_all [adapt,Except.mapError]
  exact ⟨⟨inner,original,w₁,w₂,hr⟩,⟨layout,FiniteCarrier.read_reference _ _ _ _ hl⟩⟩

end QleisliKernel.SourceTypes.QuantumSignatureCore
