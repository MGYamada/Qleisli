import QleisliKernel.SourceTypes.GenericValues
import QleisliKernel.SourceTypes.SourceSyntax
import QleisliKernel.SourceTypes.SourceNominal
import QleisliKernel.SourceTypes.SourceRuntimeTransformSyntax
import QleisliKernel.SourceTypes.SourceOperationSyntax
import QleisliKernel.SourceTypes.OperationPaths
import QleisliKernel.SourceTypes.ParameterPatterns
import QleisliKernel.SourceTypes.QuantumLabels
import QleisliKernel.SourceTypes.SourceMeaning
import QleisliKernel.SourceTypes.SourceEffectClosure
import QleisliKernel.SourceTypes.SourceComputedSyntax
import QleisliKernel.SourceTypes.SourceModules
import QleisliKernel.SourceTypes.GenericOperation

/-! Whole original-body symbolic obligations before closing static actuals.
The same checked source tree is traversed with opaque declaration/ordinal Basis
identities and original affine Nat guards. Finite injection, provider bodies,
Meaning equations and actual inverse/control implementations remain explicit
later obligations; selected values never repair this traversal's type/effect.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.GenericTypeTrace
open Finite GenericValues Semantics.SymbolicBasis Semantics.SourceAffine
open SourceEffectClosure

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

def join (a b : Formula) : Formula :=
  ⟨SourceEffect.join a.direct b.direct,a.dependencies ++ b.dependencies⟩

def direct (effect : Semantics.Raw.Effect := .unitary) : Formula := ⟨effect,[]⟩

structure Need where
  effect : Formula
  ceiling : Semantics.Raw.Effect
  classical : Bool := false

structure Operation (sources : Sources) where
  input : Code
  output : Code
  effect : Formula
  paths : OperationPaths.Paths
  references : List DefId := []
  needs : List Need := []
  meanings : List (SourceMeaning.Request sources) := []
  rows : List (String × String) := []
  subject : GenericOperation.Description
  origin : GenericOperation.Origin sources
  suppliers : List (Nat × GenericOperation.Origin sources) := []
  activities : List (GenericOperation.Activity sources) := []

def Operation.duties {sources} (operation : Operation sources) : List (GenericOperation.Duty sources) :=
  operation.activities.filterMap GenericOperation.Activity.duty?

def Operation.applications {sources} (operation : Operation sources) : List (GenericOperation.ApplicationSource sources) :=
  operation.activities.filterMap GenericOperation.Activity.application?

/-- Immutable inputs for original signature setup. No selected actual or body
outcome belongs to this context. -/
structure DefinitionContext (sources : Sources) where
  helpers : NaturalHelpers.Checked sources
  originals : Option (OrdinarySignature.Originals sources)
  modules : Option (SourceModules.Prepared sources)
  meanings : Option (SourceMeaning.Prepared sources)

structure Definition (sources : Sources) (owner name : String) where
  original : StaticHeaders.Original sources owner name
  state : GenericLexicalNatural.SomeEnvironment sources
  stateOriginal : HEq state.prepared.original original
  parameters : List Value
  result : Value
  operations : List (String × Operation sources)
  rows : List (String × String)
  context : DefinitionContext sources

def Definition.modules {sources owner name} (definition : Definition sources owner name) :=
  definition.context.modules

def Definition.meanings {sources owner name} (definition : Definition sources owner name) :=
  definition.context.meanings

private def paths (header : StaticHeaders.Parsed) (name : String) : OperationPaths.Paths :=
  ⟨header.access.contains (.applicable,name),header.access.contains (.adjointable,name),
    header.access.contains (.controllable,name)⟩

private def meets (actual required : OperationPaths.Paths) : Bool :=
  (!required.applicable || actual.applicable) && (!required.adjointable || actual.adjointable) &&
    (!required.controllable || actual.controllable)

private def meet (a b : OperationPaths.Paths) : OperationPaths.Paths := a.meet b

private def formalOperation {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (formal : StaticHeaders.Formal) (meanings : Option (SourceMeaning.Prepared sources) := none) :
    WorkM (Operation sources) := do
  let .operation tokens := formal.kind | throw .request
  let parsed ← adapt (OperationPorts.read tokens)
  let scope := (state.prepared.original.header.formals.filter (·.ordinal < formal.ordinal)).map (·.name)
  let ports ← SymbolicTypes.readPorts state scope formal.ordinal parsed.input parsed.output
  let access := paths state.prepared.original.header formal.name
  guard (!access.controllable || ports.same.isSome) .request
  let effect := if ports.same.isSome || access.adjointable || access.controllable then
      Semantics.Raw.Effect.unitary else .iso
  let meanings ← match parsed.meaning with
    | none => pure []
    | some tokens => do
      let selected ← SourceMeaning.select sources state.owner scope tokens meanings
      let _ ← SymbolicTypes.checkRefinement state scope formal.ordinal parsed.input parsed.output
        selected.meaning.graph.input selected.meaning.graph.output
      pure [selected.request]
  let rows := ports.input.result.rows ++ ports.output.result.rows ++ meanings.flatMap (·.sourceRows)
  let origin ← GenericOperation.readOrigin state scope
    state.prepared.original.envelope.occurrence.header rows
  let subject := GenericOperation.Description.singleton (StaticHeaders.frame state.prepared.original)
    (.formal ⟨state.owner,state.name,formal.ordinal⟩)
  let key : Parameter := ⟨state.owner,state.name,formal.ordinal⟩
  let meaningDuties := meanings.map fun request =>
    (⟨origin,subject,.meaning request,.formalMeaning key,[],[(0,origin)],none⟩ : GenericOperation.Duty sources)
  let accessDuties := if access.any then
    [(⟨origin,subject,.access access,.formalAccess key,[],[(0,origin)],none⟩ : GenericOperation.Duty sources)]
    else []
  let duties := meaningDuties ++ accessDuties
  pure ⟨ports.input.result.code,ports.output.result.code,direct effect,access,[],[],meanings,
    rows,subject,origin,[(0,origin)],duties.map GenericOperation.Activity.duty⟩

/-- The shared executable setup reads only the untouched original header,
opaque types, original premises and formal operation requirements. -/
def prepareDefinition {sources owner name} (original : StaticHeaders.Original sources owner name)
    (context : DefinitionContext sources) :
    WorkM {definition : Definition sources owner name //
      definition.original = original ∧ definition.context = context} := do
  let numeric ← StaticNatural.prepareOriginalWithHelpers original ["0"] context.helpers context.originals
  let state : GenericLexicalNatural.SomeEnvironment sources :=
    ⟨owner,name,numeric.prepared,GenericLexicalNatural.initial numeric.prepared⟩
  let parameters ← original.envelope.parsedHeader.parameterTypes.mapM (GenericValues.readType state 65)
  let result ← GenericValues.readType state 65 (original.envelope.parsedHeader.resultTokens.map (·.text))
  let operations ← original.header.formals.mapM fun formal => do
    match formal.kind with
    | .operation _ => pure [(formal.name,← formalOperation state formal context.meanings)]
    | _ => pure []
  let rows ← NaturalRows.bindings sources owner state.prepared.helpers state.prepared.bindings
  pure ⟨⟨original,state,by
      change HEq numeric.prepared.original original
      rw [numeric.originalHeader],parameters.map (·.value),result.value,operations.flatten,
    (owner,original.envelope.source) :: rows ++ parameters.flatMap (·.rows) ++ result.rows ++
      operations.flatten.flatMap (fun (_,operation) => operation.rows),context⟩,rfl,rfl⟩

def readDefinitionOriginal {sources owner name} (original : StaticHeaders.Original sources owner name)
    (helpers : Option (NaturalHelpers.Checked sources) := none)
    (originals : Option (OrdinarySignature.Originals sources) := none)
    (modules : Option (SourceModules.Prepared sources) := none)
    (meanings : Option (SourceMeaning.Prepared sources) := none) :
    WorkM {definition : Definition sources owner name // definition.original = original} := do
  let helpers ← match helpers with | some helpers => pure helpers | none => NaturalHelpers.read sources
  let prepared ← prepareDefinition original ⟨helpers,originals,modules,meanings⟩
  pure ⟨prepared.val,prepared.property.1⟩

def readDefinition (sources : Sources) (owner name : String)
    (helpers : Option (NaturalHelpers.Checked sources) := none)
    (originals : Option (OrdinarySignature.Originals sources) := none)
    (modules : Option (SourceModules.Prepared sources) := none)
    (meanings : Option (SourceMeaning.Prepared sources) := none) : WorkM (Definition sources owner name) := do
  pure (← readDefinitionOriginal (← StaticHeaders.read sources owner name originals) helpers originals modules meanings).val

structure PreparedDefinition {sources} (context : DefinitionContext sources) (owner name : String) where
  original : StaticHeaders.Original sources owner name
  value : Definition sources owner name
  sameOriginal : value.original = original
  sameContext : value.context = context
  computed : ∃ before after,(prepareDefinition original context).run before =
    (.ok ⟨value,sameOriginal,sameContext⟩,after)

/-- This is full original-source identity, independent of chosen actuals,
matrices, public labels or the spelling used to find this retained row. -/
theorem PreparedDefinition.sameEnvelope {sources context owner name}
    (prepared : @PreparedDefinition sources context owner name)
    (original : OrdinarySignature.Original sources owner name) :
    prepared.value.original.envelope = original :=
  prepared.value.original.envelope.sameSource original

private def readPreparedHeader {sources owner name} (context : DefinitionContext sources)
    (original : StaticHeaders.Original sources owner name) : WorkM (PreparedDefinition context owner name) := do
  let checked ← NaturalAffine.witness (prepareDefinition original context)
  pure ⟨original,checked.val.val,checked.val.property.1,checked.val.property.2,
    by with_reducible exact checked.property⟩

structure PackedDefinition {sources} (context : DefinitionContext sources) where
  owner : String
  name : String
  prepared : PreparedDefinition context owner name

private def readPreparedOriginal {sources} (context : DefinitionContext sources)
    (original : OrdinarySignature.PackedOriginal sources) : WorkM (PackedDefinition context) := do
  let header ← StaticHeaders.readOriginal original.original
  pure ⟨original.owner,original.name,← readPreparedHeader context header⟩

structure PreparedDefinitions {sources} (context : DefinitionContext sources) where
  originals : OrdinarySignature.Originals sources
  supplied : context.originals = some originals
  entries : List (PackedDefinition context)
  computed : ∃ before after,(originals.mapM (readPreparedOriginal context)).run before = (.ok entries,after)
  every : entries.map (fun entry => (entry.owner,entry.name)) = originals.map (fun original => (original.owner,original.name))

/-- Prepare each original signature once. Every original body and every call
occurrence is still parsed and traversed separately by the reader below. -/
def prepareDefinitions {sources} (context : DefinitionContext sources) : WorkM (PreparedDefinitions context) := do
  match supplied : context.originals with
  | none => throw .request
  | some originals =>
    let fields := (originals.map fun original => original.owner.utf8ByteSize+original.name.utf8ByteSize+2).sum
    -- Retained rows are persistent values; this covers list/key construction
    -- and the complete ordered coverage comparison, not unread source copies.
    exactWork (Exact.charge (16*(3*fields+4*originals.length+1)))
    let entries ← NaturalAffine.witness (originals.mapM (readPreparedOriginal context))
    if every : entries.val.map (fun entry => (entry.owner,entry.name)) =
        originals.map (fun original => (original.owner,original.name)) then
      pure ⟨originals,(by first | exact supplied | rfl),entries.val,
        by with_reducible exact entries.property,every⟩
    else throw .request

private def PackedDefinition.at {sources context owner name} (entry : @PackedDefinition sources context)
    (sameOwner : entry.owner = owner) (sameName : entry.name = name) : PreparedDefinition context owner name := by
  rcases entry with ⟨_,_,prepared⟩
  cases sameOwner
  cases sameName
  exact prepared

def lookupDefinition {sources context} (prepared : @PreparedDefinitions sources context)
    (owner name : String) : WorkM (PreparedDefinition context owner name) := do
  let fields := (prepared.entries.map fun entry => entry.owner.utf8ByteSize+entry.name.utf8ByteSize+2).sum
  exactWork (Exact.charge (16*(fields+(prepared.entries.length+1)*
    (owner.utf8ByteSize+name.utf8ByteSize+2)+1)))
  let some entry := prepared.entries.find? (fun entry => entry.owner == owner && entry.name == name) | throw .request
  if sameOwner : entry.owner = owner then
    if sameName : entry.name = name then pure (entry.at sameOwner sameName) else throw .request
  else throw .request

/-- The table is separate from Definition, so cached setup cannot recursively
contain itself. Its type fixes every immutable setup input exactly. -/
structure DefinitionReader (sources : Sources) where
  context : DefinitionContext sources
  prepared : Option (PreparedDefinitions context)

private def DefinitionReader.fromState {sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (modules : Option (SourceModules.Prepared sources)) (meanings : Option (SourceMeaning.Prepared sources)) :
    DefinitionReader sources :=
  ⟨⟨⟨state.prepared.helpers,state.prepared.helpersPrepared⟩,state.prepared.originals,modules,meanings⟩,none⟩

private def readDefinitionUsing {sources} (reader : DefinitionReader sources) (owner name : String) :
    WorkM (PreparedDefinition reader.context owner name) := do
  match reader.prepared with
  | none =>
    let original ← StaticHeaders.read sources owner name reader.context.originals
    readPreparedHeader reader.context original
  | some prepared => lookupDefinition prepared owner name

private def functionEffect {sources owner name} (caller : String) (definition : Definition sources owner name) : Formula :=
  if caller == owner then ⟨.unitary,[(owner,name)]⟩
  else direct (definition.original.envelope.parsedHeader.effect.getD .unitary)

private def basisActual {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (tokens : List LocatedToken) : WorkM SymbolicTypes.Read := do
  let texts := tokens.map (·.text)
  let inner := if texts.take 2 == ["type","("] then texts.drop 2 |>.dropLast else texts
  let parameter := match inner with
    | [name] => state.prepared.original.header.formals.any
      (fun formal => formal.name == name && formal.kind == .basis)
    | _ => false
  guard (texts == ["type","("] ++ inner ++ [")"] || (texts == inner && parameter)) .request
  if inner.length == 1 && scope.contains (inner.headD "") && !parameter then throw .request
  pure (← SymbolicTypes.read state scope scope.length inner).result

def decreasing {sources : Sources} {owner name : String} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (target : StaticHeaders.Original sources owner name)
    (forms : List (StaticCallPremises.Known state)) : WorkM Unit := do
  let strict ← target.header.formals.foldlM (fun strict formal => do
    if formal.kind != .natural then pure strict else
      let some actual := forms[formal.ordinal]? | throw .request
      let previous ← GenericLexicalNatural.read state.prepared state.environment scope (.name [formal.name])
      let _ ← NaturalPredicates.implies state.environment.context actual.form .le previous.normalized.form
      let smaller ← try
          let _ ← NaturalPredicates.implies state.environment.context actual.form .lt previous.normalized.form
          pure true
        catch error => match error with | .request => pure false | error => throw error
      pure (strict || smaller)) false
  guard strict .request

structure Recursion (sources : Sources) where
  state : GenericLexicalNatural.SomeEnvironment sources
  scope : List String
  owner : String
  name : String
  target : StaticHeaders.Original sources owner name
  callee : List LocatedToken
  written : StaticApplication.Syntax callee
  transfer : StaticCallPremises.InState state scope target written.arguments
  sameKey : owner = state.owner ∧ name = state.name
  sameOriginal : target.envelope.source = state.prepared.original.envelope.source ∧
    target.envelope.declaration = state.prepared.original.envelope.declaration
  decreased : ∃ before after,(decreasing state scope target transfer.forms).run before = (.ok (),after)

structure Application (sources : Sources) where
  owner : String
  name : String
  definition : Definition sources owner name
  parameters : List Value
  result : Value
  operations : List (String × Operation sources)
  recursion : Option (Recursion sources)
  references : List DefId
  needs : List Need
  meanings : List (SourceMeaning.Request sources)
  rows : List (String × String)
  subject : GenericOperation.Description
  origin : GenericOperation.Origin sources
  suppliers : List (Nat × GenericOperation.Origin sources)
  activities : List (GenericOperation.Activity sources)

def Application.duties {sources} (application : Application sources) : List (GenericOperation.Duty sources) :=
  application.activities.filterMap GenericOperation.Activity.duty?

def Application.applications {sources} (application : Application sources) : List (GenericOperation.ApplicationSource sources) :=
  application.activities.filterMap GenericOperation.Activity.application?

private def instantiateWithReader {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) {tokens} (written : StaticApplication.Syntax tokens) (owner name : String)
    (operationReader : List LocatedToken → WorkM (Operation sources)) (runtimeRecursion : Bool)
    (reader : DefinitionReader sources) : WorkM (Application sources) := do
  let prepared ← readDefinitionUsing reader owner name
  let definition := prepared.value
  let target := definition.original
  guard (written.arguments.length == target.header.formals.length) .request
  let transfer ← StaticCallPremises.readInState state scope target written.arguments
  let recursion ← if sameKey : owner = state.owner ∧ name = state.name then do
      guard (runtimeRecursion && !state.prepared.original.envelope.parsedHeader.ordinaryOnly) .request
      let decrease ← NaturalAffine.witness (decreasing state scope target transfer.forms)
      have unit : decrease.val = () := by cases decrease.val; rfl
      if sameOriginal : target.envelope.source = state.prepared.original.envelope.source ∧
          target.envelope.declaration = state.prepared.original.envelope.declaration then
        pure (some (⟨state,scope,owner,name,target,tokens,written,transfer,sameKey,sameOriginal,
          by with_reducible simpa only [unit] using decrease.property⟩ : Recursion sources))
      else throw .request
    else pure none
  let actuals ← (target.header.formals.zip written.arguments).mapM fun (formal,argument) => do
    match formal.kind with
    | .basis =>
      let basis ← basisActual state scope argument.tokens
      pure ([(⟨owner,name,formal.ordinal⟩,basis.code)],[],basis.rows)
    | .natural =>
      let expression ← adapt (StaticBindings.natural argument.tokens)
      let rows ← NaturalRows.expression sources state.owner state.prepared.helpers scope expression.expression
      pure ([],[],rows)
    | .operation _ =>
      let operation ← operationReader argument.tokens
      pure ([],[(formal.name,operation)],operation.rows)
  let bases := actuals.flatMap (·.1)
  let operations := actuals.flatMap (·.2.1)
  let variables := (StaticHeaders.frame state.prepared.original).binders.length
  let naturals := NaturalFrames.replacements (StaticHeaders.frame transfer.callee.original) (transfer.forms.map (·.form))
  let parameters ← definition.parameters.mapM (GenericValues.substitute variables bases naturals)
  let result ← GenericValues.substitute variables bases naturals definition.result
  let _ ← definition.operations.mapM fun (formalName,required) => do
    let some (_,actual) := operations.find? (·.1 == formalName) | throw .request
    let input ← SymbolicTypes.substitute variables bases naturals required.input
    let output ← SymbolicTypes.substitute variables bases naturals required.output
    let _ ← SymbolicTypes.equate state actual.input input.code
    let _ ← SymbolicTypes.equate state actual.output output.code
    guard (meets actual.paths required.paths) .request
    pure ()
  let needs := operations.flatMap (fun (_,operation) => operation.needs) ++
    definition.operations.map (fun (formalName,required) =>
      let actual := operations.find? (·.1 == formalName) |>.map (·.2)
      ⟨actual.map (·.effect) |>.getD (direct .observe),required.effect.direct,false⟩)
  let rows := definition.rows ++ actuals.flatMap (·.2.2) ++
    operations.flatMap (fun (_,operation) => operation.rows)
  let origin ← GenericOperation.readOrigin state scope tokens rows
  let operationActuals ← operations.mapM fun (formalName,actual) => do
    let some formal := target.header.formals.find? (·.name == formalName) | throw .request
    pure (⟨⟨owner,name,formal.ordinal⟩,actual.subject,actual.suppliers⟩ : GenericOperation.ActualOperation sources)
  let occurrence : GenericOperation.ApplicationSource sources :=
    ⟨state,scope,tokens,owner,name,target,written,transfer,bases,naturals,operationActuals⟩
  let supplied ← operations.mapM fun (formalName,actual) => do
    let some formal := target.header.formals.find? (·.name == formalName) | throw .request
    let some (_,argument) := (target.header.formals.zip written.arguments).find?
      (fun (formal,_) => formal.name == formalName) | throw .request
    let actualOrigin ← GenericOperation.readOrigin state scope argument.tokens actual.rows
    let binding : GenericOperation.Binding sources := ⟨owner,name,target,formal,actualOrigin,some occurrence⟩
    let inherited : List (GenericOperation.Activity sources) := actual.activities.map fun activity => match activity with
      | .duty duty => .duty {duty with bindings := duty.bindings ++ [binding]}
      | .application call => .application call
    let some (_,required) := definition.operations.find? (·.1 == formalName) | throw .request
    let meanings := required.meanings.map fun request =>
      (⟨required.origin,actual.subject,.meaning request,.formalMeaning ⟨owner,name,formal.ordinal⟩,[binding],actual.suppliers,none⟩ : GenericOperation.Duty sources)
    let access := if required.paths.applicable || required.paths.adjointable || required.paths.controllable then
      [(⟨required.origin,actual.subject,.access required.paths,.formalAccess ⟨owner,name,formal.ordinal⟩,[binding],actual.suppliers,none⟩ : GenericOperation.Duty sources)]
      else []
    pure (inherited,(meanings ++ access).map GenericOperation.Activity.duty)
  let basisArguments ← target.header.formals.foldlM (fun arguments formal => do
    match formal.kind with
    | .basis =>
      let some (_,code) := bases.find? (·.1 == ⟨owner,name,formal.ordinal⟩) | throw .request
      pure (arguments ++ [(formal.name,code)])
    | _ => pure arguments) []
  let naturalArguments ← target.header.formals.foldlM (fun arguments formal => do
    match formal.kind with
    | .natural =>
      let some value := transfer.forms[formal.ordinal]? | throw .request
      pure (arguments ++ [(formal.name,value.form)])
    | _ => pure arguments) []
  let frame := StaticHeaders.frame state.prepared.original
  guard (operations.all fun (_,operation) => operation.subject.frame.binders == frame.binders) .request
  let subject := GenericOperation.provider frame owner name basisArguments naturalArguments
    (operations.map fun (name,operation) => (name,operation.subject))
    (definition.operations.map fun (name,operation) => (name,operation.paths))
  let (_,suppliers) := operations.foldl (fun (offset,suppliers) (_,operation) =>
    (offset+operation.subject.nodes.length,
      suppliers ++ operation.suppliers.map (fun (index,origin) => (index+offset,origin)))) (0,[])
  let suppliers := suppliers ++ [(subject.root,origin)]
  pure ⟨owner,name,definition,parameters,result,operations,recursion,
    (owner,name) :: operations.flatMap (fun (_,operation) => operation.references),needs,
    operations.flatMap (fun (_,operation) => operation.meanings) ++ definition.operations.flatMap (fun (_,operation) => operation.meanings),
    rows,subject,origin,suppliers,
    supplied.flatMap (·.1) ++ supplied.flatMap (·.2) ++ [.application occurrence]⟩

/-- Fresh component entry point. Shared body traversal supplies its exact
prepared reader only to the same executable instantiation below. -/
def instantiate {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) {tokens} (written : StaticApplication.Syntax tokens) (owner name : String)
    (operationReader : List LocatedToken → WorkM (Operation sources)) (runtimeRecursion : Bool)
    (modules : Option (SourceModules.Prepared sources) := none)
    (meanings : Option (SourceMeaning.Prepared sources) := none) : WorkM (Application sources) :=
  instantiateWithReader state scope written owner name operationReader runtimeRecursion
    (DefinitionReader.fromState state modules meanings)

private def named {sources : Sources} (modules : Option (SourceModules.Prepared sources)) (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (tokens : List LocatedToken) : WorkM (Resolved × List (String × String)) := do
  let candidate ← CallName.readWithModules sources modules state.owner scope tokens
  let some resolution := CallName.candidateResolution candidate | throw .request
  pure (resolution,CallName.sourceRows candidate)

private def combineOperation {sources} (a b : Operation sources) (input output : Code)
    (effect : Formula) (paths : OperationPaths.Paths) (origin : GenericOperation.Origin sources)
    (constructor : Nat → Nat → GenericOperation.Node) : WorkM (Operation sources) := do
  guard (a.subject.frame.binders == b.subject.frame.binders) .request
  return ⟨input,output,effect,paths,a.references ++ b.references,a.needs ++ b.needs,
    a.meanings ++ b.meanings,a.rows ++ b.rows,a.subject.binary b.subject constructor,origin,
    a.suppliers ++ b.suppliers.map (fun (index,origin) =>
      (index+a.subject.nodes.length,origin)),a.activities ++ b.activities⟩

private def operationCount {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (tokens : List LocatedToken) : WorkM (GenericOperation.Count × List (String × String)) := do
  let texts := tokens.map (·.text)
  let powerTwo := texts.take 2 == ["2","^"]
  let tokens := if powerTwo then tokens.drop 2 else tokens
  let expression ← adapt (StaticBindings.natural tokens)
  let checked ← GenericLexicalNatural.read state.prepared state.environment scope expression.expression
  let rows ← NaturalRows.expression sources state.owner state.prepared.helpers scope expression.expression
  pure (⟨checked.normalized.form,powerTwo⟩,rows)

private def operationWithModules {sources : Sources} (reader : DefinitionReader sources)
    (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (formals : List (String × Operation sources)) :
    Nat → Option Code → List LocatedToken → WorkM (Operation sources) :=
  Nat.rec (fun _ _ => throw .limit) (fun _ next primitiveTarget tokens => do
    let modules := reader.context.modules
    let meanings := reader.context.meanings
    exactWork (Exact.charge (32*((tokens.map fun token => token.text.utf8ByteSize+4).sum+1)))
    let origin ← GenericOperation.readOrigin state scope tokens []
    if tokens.getLast?.map (·.text) == some ")" then
      let call ← adapt (CallSyntax.read tokens)
      match call.call.callee.map (·.text),call.call.arguments with
      | ["adjoint"],[child] =>
        let child ← next none child.tokens
        guard child.paths.adjointable .request
        pure {child with
          input := child.output,output := child.input,
          effect := direct .unitary,paths := ⟨child.paths.adjointable,child.paths.applicable,child.paths.controllable⟩,
          needs := child.needs ++ [⟨child.effect,.unitary,false⟩],
          subject := child.subject.unary .inverse,origin := {origin with rows := child.rows},
          activities := child.activities ++ [.duty ⟨origin,child.subject,.access ⟨false,true,false⟩,.inverseFormation,[],child.suppliers,none⟩]}
      | ["controlled"],[child] =>
        let child ← next none child.tokens
        let _ ← SymbolicTypes.equate state child.input child.output
        let basis := .fixed .pair :: .fixed .bit :: child.input
        pure {child with
          input := basis,output := basis,effect := direct .unitary,
          paths := ⟨child.paths.controllable,child.paths.controllable,child.paths.controllable⟩,
          needs := child.needs ++ [⟨child.effect,.unitary,false⟩],
          subject := child.subject.unary .controlled,origin := {origin with rows := child.rows}}
      | ["power"],[child,count] =>
        let child ← next none child.tokens
        let _ ← SymbolicTypes.equate state child.input child.output
        let (count,rows) ← operationCount state scope count.tokens
        pure {child with
          rows := child.rows ++ rows,subject := child.subject.unary (fun index => .power index count),
          origin := {origin with rows := child.rows ++ rows}}
      | ["then_op"],[left,right] =>
        let left ← next none left.tokens
        let right ← next none right.tokens
        let _ ← SymbolicTypes.equate state left.output right.input
        combineOperation left right left.input right.output (join left.effect right.effect) (meet left.paths right.paths)
          {origin with rows := left.rows ++ right.rows} .thenOp
      | ["tensor_op"],[left,right] =>
        let left ← next none left.tokens
        let right ← next none right.tokens
        combineOperation left right (.fixed .pair :: left.input ++ right.input)
          (.fixed .pair :: left.output ++ right.output) (join left.effect right.effect) (meet left.paths right.paths)
          {origin with rows := left.rows ++ right.rows} .tensor
      | ["conjugate_op"],[outer,middle] =>
        let outer ← next none outer.tokens
        let middle ← next none middle.tokens
        let _ ← SymbolicTypes.equate state outer.input middle.input
        let _ ← SymbolicTypes.equate state middle.input middle.output
        let result ← combineOperation outer middle outer.output outer.output (join outer.effect middle.effect)
          ⟨outer.paths.applicable && outer.paths.adjointable && middle.paths.applicable,
            outer.paths.applicable && outer.paths.adjointable && middle.paths.adjointable,
            outer.paths.applicable && outer.paths.adjointable && middle.paths.controllable⟩
          {origin with rows := outer.rows ++ middle.rows} .conjugate
        pure {result with needs := result.needs ++ [⟨outer.effect,.unitary,false⟩]}
      | ["checked_op"],[child,meaning] =>
        let _ ← adapt (CallName.readName child.tokens)
        let child ← next none child.tokens
        let selected ← SourceMeaning.select sources state.owner scope (meaning.tokens.map (·.text)) meanings
        let input ← SymbolicTypes.ofClosed (StaticHeaders.frame state.prepared.original).binders.length selected.meaning.graph.input
        let output ← SymbolicTypes.ofClosed (StaticHeaders.frame state.prepared.original).binders.length selected.meaning.graph.output
        let _ ← SymbolicTypes.equate state child.input input.code
        let _ ← SymbolicTypes.equate state child.output output.code
        let origin := {origin with rows := child.rows ++ selected.request.sourceRows}
        pure {child with
          meanings := child.meanings ++ [selected.request],rows := child.rows ++ selected.queryRows,
          subject := child.subject.unary (fun index =>
            .requested index selected.request.moduleName selected.request.declarationName),origin,
          activities := child.activities ++ [.duty ⟨origin,child.subject,.meaning selected.request,.checkedMeaning,[],child.suppliers,none⟩]}
      | _,_ => throw .request
    else
      let written ← adapt (StaticApplication.readSyntax tokens)
      let candidate ← CallName.readWithModules sources modules state.owner scope written.callee
      match candidate.decision with
      | .lexical name .. =>
        guard written.arguments.isEmpty .request
        let some (_,formal) := formals.find? (·.1 == name) | throw .request
        -- The original header premise is retained once by the definition.
        -- A lexical use borrows it; only a written checked_op or path demand
        -- creates another occurrence in the activity stream.
        pure {formal with origin := {origin with rows := formal.rows},activities := []}
      | .primitive _ _ _ _ _ _ kind _ =>
        guard written.arguments.isEmpty .request
        let some target := primitiveTarget | throw .request
        match kind with
        | .h =>
          let _ ← SymbolicTypes.equate state target [.fixed .bit]
          pure ⟨target,target,direct .unitary,⟨true,true,true⟩,[],[],[],CallName.sourceRows candidate,
            .singleton (StaticHeaders.frame state.prepared.original) (.primitive .h target),
            {origin with rows := CallName.sourceRows candidate},[],[]⟩
        | .globalPhaseEighth =>
          pure ⟨target,target,direct .unitary,⟨true,true,true⟩,[],[],[],CallName.sourceRows candidate,
            .singleton (StaticHeaders.frame state.prepared.original) (.primitive .globalPhaseEighth target),
            {origin with rows := CallName.sourceRows candidate},[],[]⟩
        | _ => throw .request
      | _ =>
        let some resolution := CallName.candidateResolution candidate | throw .request
        let application ← instantiateWithReader state scope written resolution.moduleName resolution.declaration.name
          (next none) false reader
        let [[.owner input]] := application.parameters | throw .request
        let [.owner output] := application.result | throw .request
        let reverse := application.operations.all fun (_,actual) => actual.paths.applicable && actual.paths.adjointable
        let control := application.operations.all fun (_,actual) =>
          actual.paths.applicable && actual.paths.adjointable && actual.paths.controllable
        let same ← SymbolicTypes.optionalEquality state input output
        let effect := functionEffect state.owner application.definition
        pure ⟨input,output,effect,⟨true,reverse,control && same.isSome⟩,application.references,
          application.needs ++ [⟨effect,.iso,false⟩],application.meanings,CallName.sourceRows candidate ++ application.rows,
          application.subject,{application.origin with rows := CallName.sourceRows candidate ++ application.rows},
          application.suppliers,application.activities⟩)

structure BasisObligation (sources : Sources) where
  owner : String
  name : String
  offset : Nat
  state : GenericLexicalNatural.SomeEnvironment sources
  input : Code
  output : Code

/-- Component callers without a prepared original table retain the fresh
candidate reader; contextual body traversal uses the same operation checker. -/
def operation {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (formals : List (String × Operation sources)) :
    Nat → Option Code → List LocatedToken → WorkM (Operation sources) :=
  operationWithModules (DefinitionReader.fromState state none none) state scope formals

/-- Total classical declarations and basis expressions keep their existing
restricted expression grammar. Quantum-use inference alone cannot authorize a
normal runtime call, statements, static specialization or scoped construction.
This traverses the same original tree before its independent typed traversal. -/
private def checkClassicalTree {sources} (modules : Option (SourceModules.Prepared sources))
    (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) : Nat → {tokens : List LocatedToken} → SourceSyntax.Tree tokens → WorkM Unit :=
  Nat.rec (fun {_} _ => throw .limit) (fun _ next {tokens} tree => do
    exactWork (Exact.charge (8*((tokens.map fun token => token.text.utf8ByteSize+4).sum+1)))
    let children (trees : List (Sigma SourceSyntax.Tree)) : WorkM Unit := do
      for child in trees do next child.2
    match tree with
    | .literal .. | .move .. | .variant _ => pure ()
    | .group _ trees => children trees.trees
    | .boolean _ trees => children trees.trees
    | .record _ trees => children trees.trees
    | .projection _ receiver => next receiver
    | .conditional _ condition thenBody elseBody => do
      next condition
      next thenBody
      next elseBody
    | .matching written scrutinee trees => do
      guard (written.parts.arms.all fun arm => arm.body.opening.isNone && arm.body.closing.isNone) .request
      next scrutinee
      children trees.trees
    | .call call trees => do
      let .name _ ← adapt (StaticApplication.readSyntax call.call.callee) | throw .request
      let candidate ← CallName.readWithModules sources modules state.owner scope call.call.callee
      match candidate.decision with
      | .primitive _ _ _ _ _ _ .emptyBits _ => guard call.call.arguments.isEmpty .request
      | _ =>
        let some resolution := CallName.candidateResolution candidate | throw .request
        let original ← StaticHeaders.read sources resolution.moduleName resolution.declaration.name state.prepared.originals
        guard original.envelope.parsedHeader.ordinaryOnly .request
      children trees.trees
    | _ => throw .request)

structure ComputedPredicate (sources : Sources) where
  resolution : Resolved
  definition : Definition sources resolution.moduleName resolution.declaration.name
  original : definition.original.envelope.source = resolution.source ∧
    definition.original.envelope.declaration = resolution.declaration
  rows : List (String × String)

private def computedPredicate {sources} (reader : DefinitionReader sources)
    (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (input : Code) (reference : SourceComputedSyntax.Reference) :
    WorkM (ComputedPredicate sources) := do
  let (resolution,rows) ← named reader.context.modules state scope reference.argument.tokens
  let prepared ← readDefinitionUsing reader resolution.moduleName resolution.declaration.name
  let definition := prepared.value
  guard (definition.original.header.formals.isEmpty &&
    definition.original.envelope.parsedHeader.ordinaryOnly) .request
  let [parameter] := definition.parameters | throw .request
  GenericValues.expect state parameter (← adapt (GenericValues.ordinaryValue input))
  GenericValues.expect state definition.result [.ordinary [.fixed .bit]]
  if original : definition.original.envelope.source = resolution.source ∧
      definition.original.envelope.declaration = resolution.declaration then
    pure ⟨resolution,definition,original,rows ++ definition.rows⟩
  else throw .request

/-- Original scoped typing is retained separately from the actual finite
protected/certified cleanup equation. A dormant concrete scope still needs
that native equation; no name, type or effect label discharges it. -/
structure ComputedObligation (sources : Sources) where
  owner : String
  name : String
  offset : Nat
  state : GenericLexicalNatural.SomeEnvironment sources
  input : Code
  tokens : List LocatedToken
  written : SourceComputedSyntax.Checked tokens
  predicate : ComputedPredicate sources
  logical : Option (Operation sources)

structure Outcome (sources : Sources) where
  value : Value
  remaining : Environment
  effect : Formula := ⟨.unitary,[]⟩
  quantumUse : Bool := false
  references : List DefId := []
  recursions : List (Recursion sources) := []
  needs : List Need := []
  meanings : List (SourceMeaning.Request sources) := []
  activities : List (GenericOperation.Activity sources) := []
  basisObligations : List (BasisObligation sources) := []
  computedObligations : List (ComputedObligation sources) := []
  rows : List (String × String) := []

def Outcome.duties {sources} (outcome : Outcome sources) : List (GenericOperation.Duty sources) :=
  outcome.activities.filterMap GenericOperation.Activity.duty?

def Outcome.applications {sources} (outcome : Outcome sources) : List (GenericOperation.ApplicationSource sources) :=
  outcome.activities.filterMap GenericOperation.Activity.application?

def append {sources} (first last : Outcome sources) : Outcome sources :=
  {last with
    effect := join first.effect last.effect,quantumUse := first.quantumUse || last.quantumUse,
    references := first.references ++ last.references,needs := first.needs ++ last.needs,
    recursions := first.recursions ++ last.recursions,
    meanings := first.meanings ++ last.meanings,basisObligations := first.basisObligations ++ last.basisObligations,
    activities := first.activities ++ last.activities,
    computedObligations := first.computedObligations ++ last.computedObligations,
    rows := first.rows ++ last.rows}

private def ordinaryCodeNode : Nat → Value → WorkM (Code × Value) :=
  Nat.rec (fun _ => throw .limit) (fun _ next value => do
    match value with
    | .ordinary code :: rest => pure (code,rest)
    | .tuple count :: rest =>
      guard (2 ≤ count && count ≤ 64) .request
      let (children,rest) ← (List.range count).foldlM (fun (codes,rest) _ => do
        let (code,rest) ← next rest
        pure (codes ++ code,rest)) ([],rest)
      pure (.fixed (if count == 2 then .pair else .tuple count) :: children,rest)
    | _ => throw .request)

def ordinaryCode (value : Value) : WorkM Code := do
  let (code,rest) ← ordinaryCodeNode (value.length+1) value
  guard rest.isEmpty .request
  pure code

private def width {sources} (state : GenericLexicalNatural.SomeEnvironment sources) (code : Code) :
    WorkM (Option Form) := do
  let variables := (StaticHeaders.frame state.prepared.original).binders.length
  let zero ← NaturalAffine.witness (NaturalAffine.constant variables 0)
  code.foldlM (fun sum atom => do
    match sum,atom with
    | none,_ => pure none
    | some sum,.bits form => pure (some (← NaturalAffine.witness (NaturalAffine.add sum form)).val)
    | some sum,.fixed .bit =>
      let one ← NaturalAffine.witness (NaturalAffine.constant variables 1)
      pure (some (← NaturalAffine.witness (NaturalAffine.add sum one.val)).val)
    | some sum,.fixed .unit | some sum,.fixed .pair | some sum,.fixed (.tuple _) => pure (some sum)
    | _,_ => pure none) (some zero.val)

private def basisEffect {sources} (state : GenericLexicalNatural.SomeEnvironment sources) (input output : Code) :
    WorkM Semantics.Raw.Effect := do
  if (← SymbolicTypes.optionalEquality state input output).isSome then pure .unitary else
    match ← width state input,← width state output with
    | some a,some b =>
      try
        let _ ← NaturalPredicates.implies state.environment.context a .eq b
        pure .unitary
      catch error => match error with | .request => pure .iso | error => throw error
    | _,_ => pure .iso

private def scalarLabelBasis {sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (code : Code) (count : Nat) : WorkM Semantics.FiniteCarrier.Basis := do
  match code with
  | [.fixed .unit] => guard (count == 1) .request; pure [.unit]
  | [.fixed .bit] => guard (count == 2) .request; pure [.bit]
  | [.fixed (.enumeration origin names)] => guard (count == names.length) .request; pure [.enumeration origin names]
  | [.bits _] =>
    let some bits := (List.range 7).find? (fun bits => 2^bits == count) | throw .request
    let closed ← SymbolicTypes.ofClosed (StaticHeaders.frame state.prepared.original).binders.length [.bits bits]
    let _ ← SymbolicTypes.equate state code closed.code
    pure [.bits bits]
  | _ => throw .request

private def selection {sources} (reader : DefinitionReader sources)
    (state : GenericLexicalNatural.SomeEnvironment sources) (scope : List String)
    (formals : List (String × Operation sources)) (parsed : QuantumMatch.Parsed)
    (selector target : Value) (remaining : Environment) : WorkM (Outcome sources) := do
  let [.owner selector] := selector | throw .request
  let [.owner target] := target | throw .request
  if parsed.keyword.text == "qif" then
    let _ ← SymbolicTypes.equate state selector [.fixed .bit]
  let labelBasis ← scalarLabelBasis state selector parsed.arms.length
  let arms ← parsed.arms.mapM fun arm => do
    let label ← QuantumLabels.read sources state.owner labelBasis arm.label
    let operation ← operationWithModules reader state scope formals 65 (some target) arm.operation
    let _ ← SymbolicTypes.equate state operation.input target
    let _ ← SymbolicTypes.equate state operation.output target
    guard operation.paths.controllable .request
    pure (label,operation)
  let labels := arms.map (·.1.ordinal)
  guard (labels.all (· < arms.length) && labels.eraseDups.length == labels.length) .request
  pure {
    value := [.tuple 2,.owner selector,.owner target],remaining,quantumUse := true,
    effect := direct .unitary,references := arms.flatMap (·.2.references),
    needs := arms.flatMap (fun (_,operation) => operation.needs ++ [⟨operation.effect,.unitary,false⟩]),
    meanings := arms.flatMap (·.2.meanings),
    activities := arms.flatMap (fun (_,operation) => operation.activities ++
      [.duty ⟨operation.origin,operation.subject,.access ⟨false,false,true⟩,.selectionControl,[],operation.suppliers,none⟩]),
    rows := arms.flatMap (fun (label,operation) => label.sourceRows ++ operation.rows)}

private def expectEnvironment {sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (actual expected : Environment) : WorkM Unit := do
  guard (actual.map (fun cell => (cell.name,cell.binding)) == expected.map (fun cell => (cell.name,cell.binding))) .request
  for (a,b) in actual.zip expected do GenericValues.expect state a.value b.value

private def branchEnvironment (before after : Environment) : WorkM Environment := do
  guard (after.all fun cell => !hasOwner cell.value || before.any
    (fun original => original.name == cell.name && original.binding == cell.binding)) .request
  pure (before.filterMap fun cell => if hasOwner cell.value then
    after.find? (fun other => other.name == cell.name && other.binding == cell.binding) else some cell)

private def branches {sources} (leftState rightState : GenericLexicalNatural.SomeEnvironment sources)
    (before : Environment) (left right : Outcome sources) : WorkM (Outcome sources) := do
  let leftRemaining ← branchEnvironment before left.remaining
  let rightRemaining ← branchEnvironment before right.remaining
  let candidate ← try
      GenericValues.expect rightState right.value left.value
      expectEnvironment rightState rightRemaining leftRemaining
      pure (left.value,leftRemaining)
    catch error => match error with
      | .request =>
        GenericValues.expect leftState left.value right.value
        expectEnvironment leftState leftRemaining rightRemaining
        pure (right.value,rightRemaining)
      | error => throw error
  pure {append left right with value := candidate.1,remaining := candidate.2}

private def primitive {sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (kind : CallName.Primitive) (arguments : List Value) (remaining : Environment) : WorkM (Outcome sources) := do
  let unit := [.ordinary [.fixed .unit]]
  let outcome ← match kind,arguments with
    | .h,[[.owner basis]] =>
      GenericValues.expect state [.owner basis] [.owner [.fixed .bit]]
      pure ([.owner basis],Semantics.Raw.Effect.unitary)
    | .globalPhaseEighth,[[.owner basis]] => pure ([.owner basis],.unitary)
    | .measureZ,[[.owner basis]] =>
      GenericValues.expect state [.owner basis] [.owner [.fixed .bit]]
      pure ([.ordinary [.fixed .bit]],.observe)
    | .discard,[[.owner _]] => pure (unit,.observe)
    | .unit,[value] =>
      GenericValues.expect state value unit
      pure ([.owner [.fixed .unit]],.unitary)
    | .finish,[[.owner basis]] =>
      GenericValues.expect state [.owner basis] [.owner [.fixed .unit]]
      pure (unit,.unitary)
    | .split,[[.owner basis]] =>
      let (a,b) ← adapt (GenericValues.pairCodes basis)
      pure ([.tuple 2,.owner a,.owner b],.unitary)
    | .join,[[.owner a],[.owner b]] => pure ([.owner (.fixed .pair :: a ++ b)],.unitary)
    | _,_ => throw .request
  pure {value := outcome.1,remaining,effect := direct outcome.2,quantumUse := true}

private def primitiveNatural {sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (argument : CallSyntax.Argument) : WorkM (Form × List (String × String)) := do
  let expression ← adapt (StaticBindings.natural argument.tokens)
  let checked ← GenericLexicalNatural.read state.prepared state.environment scope expression.expression
  let rows ← NaturalRows.expression sources state.owner state.prepared.helpers scope expression.expression
  pure (checked.normalized.form,rows)

private def primitiveApplication {sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (kind : CallName.Primitive) (actuals : List CallSyntax.Argument)
    (arguments : List Value) (remaining : Environment) : WorkM (Outcome sources) := do
  let variables := (StaticHeaders.frame state.prepared.original).binders.length
  match kind with
  | .emptyBits =>
    guard (actuals.isEmpty && arguments.isEmpty) .request
    let zero ← NaturalAffine.constant variables 0
    pure {value := [.ordinary [.bits zero]],remaining}
  | .prependBit =>
    let [amount] := actuals | throw .request
    let [head,tail] := arguments | throw .request
    let (width,rows) ← primitiveNatural state scope amount
    GenericValues.expect state head [.ordinary [.fixed .bit]]
    GenericValues.expect state tail [.ordinary [.bits width]]
    let one ← NaturalAffine.constant variables 1
    let output ← NaturalAffine.add width one
    pure {value := [.ordinary [.bits output]],remaining,rows}
  | .takeBit | .putBit =>
    let [amount,index] := actuals | throw .request
    let (width,widthRows) ← primitiveNatural state scope amount
    let (index,indexRows) ← primitiveNatural state scope index
    let one ← NaturalAffine.constant variables 1
    let _ ← NaturalPredicates.implies state.environment.context one .le width
    let _ ← NaturalPredicates.implies state.environment.context index .lt width
    let shortened ← NaturalAffine.sub width one
    let value ← if kind == .takeBit then do
        let [input] := arguments | throw .request
        GenericValues.expect state input [.owner [.bits width]]
        pure [.tuple 2,.owner [.fixed .bit],.owner [.bits shortened]]
      else do
        let [head,tail] := arguments | throw .request
        GenericValues.expect state head [.owner [.fixed .bit]]
        GenericValues.expect state tail [.owner [.bits shortened]]
        pure [.owner [.bits width]]
    pure {value,remaining,quantumUse := true,rows := widthRows ++ indexRows}
  | _ =>
    guard actuals.isEmpty .request
    primitive state kind arguments remaining

private def applyOperation {sources} (reader : DefinitionReader sources)
    (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (formals : List (String × Operation sources)) (tokens : List LocatedToken)
    (arguments : List Value) (remaining : Environment) : WorkM (Outcome sources) := do
  let op ← operationWithModules reader state scope formals 65 none tokens
  guard op.paths.applicable .request
  let value ← if SourceOperationSyntax.controlled tokens then do
      let [[.owner control],[.owner target]] := arguments | throw .request
      let (inputControl,inputTarget) ← adapt (GenericValues.pairCodes op.input)
      let (outputControl,outputTarget) ← adapt (GenericValues.pairCodes op.output)
      GenericValues.expect state [.owner control] [.owner inputControl]
      GenericValues.expect state [.owner target] [.owner inputTarget]
      GenericValues.expect state [.owner outputControl] [.owner inputControl]
      pure [.tuple 2,.owner outputControl,.owner outputTarget]
    else do
      let [argument] := arguments | throw .request
      GenericValues.expect state argument [.owner op.input]
      pure [.owner op.output]
  pure {
    value,remaining,effect := op.effect,quantumUse := true,references := op.references,
    needs := op.needs,meanings := op.meanings,rows := op.rows,
    activities := op.activities ++ [.duty ⟨op.origin,op.subject,.access ⟨true,false,false⟩,.application,[],op.suppliers,none⟩]}

private def quantumGroup (value : Value) : Bool :=
  hasOwner value && value.all (fun atom => match atom with | .ordinary _ => false | _ => true)

private def runtimeTransform {sources} (reader : DefinitionReader sources)
    (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (formals : List (String × Operation sources)) {tokens}
    (written : SourceRuntimeTransformSyntax.Checked tokens) (arguments : List Value) (remaining : Environment) :
    WorkM (Outcome sources) := do
  let base := written.base
  let candidate ← CallName.readWithModules sources reader.context.modules state.owner scope base.2.callee
  let counts ← written.counts.mapM (fun count => operationCount state scope count.tokens)
  let rows := counts.map (·.2)
  match candidate.decision with
  | .primitive _ _ _ _ _ _ kind _ =>
    guard (written.counts.isEmpty && (kind == .h || kind == .globalPhaseEighth)) .request
    let (control,target) ← if written.access == .controlled then
        match arguments with
        | [[.owner control],[.owner target]] =>
          GenericValues.expect state [.owner control] [.owner [.fixed .bit]]
          pure (some control,target)
        | _ => throw .request
      else match arguments with | [[.owner target]] => pure (none,target) | _ => throw .request
    if kind == .h then GenericValues.expect state [.owner target] [.owner [.fixed .bit]]
    let value := match control with | none => [.owner target] | some control => [.tuple 2,.owner control,.owner target]
    pure {value,remaining,quantumUse := true,rows := rows.flatten ++ CallName.sourceRows candidate}
  | _ =>
    let some resolution := CallName.candidateResolution candidate | throw .request
    let application ← instantiateWithReader state scope base.2 resolution.moduleName resolution.declaration.name
      (operationWithModules reader state scope formals 65 none) true reader
    let input ← match application.parameters with
      | [] => throw .request
      | [single] => pure single
      | parameters => pure (.tuple parameters.length :: parameters.flatten)
    guard (quantumGroup input && quantumGroup application.result) .request
    let swapped := written.access == .adjoint && application.parameters.length == 1 && written.counts.isEmpty &&
      (match input,application.result with | [.owner _],[.owner _] => true | _,_ => false)
    if !swapped then GenericValues.expect state input application.result
    let inputPort := if swapped then application.result else input
    let outputPort := if swapped then input else application.result
    let value ← if written.access == .controlled then do
        let [[.owner control],target] := arguments | throw .request
        GenericValues.expect state [.owner control] [.owner [.fixed .bit]]
        GenericValues.expect state target inputPort
        pure (.tuple 2 :: .owner control :: outputPort)
      else do
        let [target] := arguments | throw .request
        GenericValues.expect state target inputPort
        pure outputPort
    let access ← match written.access with
      | .forward => pure (application.operations.all fun (_,actual) => actual.paths.applicable)
      | .adjoint => pure (application.operations.all fun (_,actual) => actual.paths.applicable && actual.paths.adjointable)
      | .controlled => pure (application.operations.all fun (_,actual) =>
        actual.paths.applicable && actual.paths.adjointable && actual.paths.controllable)
    guard access .request
    let effect := functionEffect state.owner application.definition
    let origin ← GenericOperation.readOrigin state scope tokens
      (CallName.sourceRows candidate ++ rows.flatten ++ application.rows)
    let subject := counts.foldl (fun subject (count,_) =>
      subject.unary (fun child => .power child count)) application.subject
    let requested : OperationPaths.Paths := match written.access with
      | .forward => ⟨true,false,false⟩
      | .adjoint => ⟨false,true,false⟩
      | .controlled => ⟨false,false,true⟩
    let some occurrence := application.applications.getLast? | throw .request
    pure {
      value,remaining,effect := direct .unitary,quantumUse := true,references := application.references,
      recursions := application.recursion.toList,
      needs := application.needs ++ [⟨effect,.unitary,false⟩],meanings := application.meanings,
      rows := CallName.sourceRows candidate ++ rows.flatten ++ application.rows,
      activities := application.activities ++
        [.duty ⟨origin,subject,.access requested,.runtimeTransform,[],application.suppliers,some occurrence⟩]}

private def bindingNames (tokens : List LocatedToken) : WorkM (List String) := do
  let pattern ← adapt (QuantumMoves.parsePattern 65 (tokens.map (·.text)))
  pure (pattern.filterMap fun atom => match atom with | .name name => some name | _ => none)

private def typedNominal {sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (basis : Semantics.FiniteCarrier.Basis) : WorkM Value := do
  let closed ← SymbolicTypes.ofClosed (StaticHeaders.frame state.prepared.original).binders.length basis
  adapt (GenericValues.ordinaryValue closed.code)

private def evaluator {sources owner name} (definition : Definition sources owner name)
    (prepared : Option (PreparedDefinitions definition.context)) :
    Nat → GenericLexicalNatural.SomeEnvironment sources → List String → Environment →
    {tokens : List LocatedToken} → SourceSyntax.Tree tokens → WorkM (Outcome sources) :=
  Nat.rec (fun _ _ _ {_} _ => throw .limit) (fun _ next state scope environment {tokens} tree => do
    let reader : DefinitionReader sources := ⟨definition.context,prepared⟩
    exactWork (Exact.charge (16*((tokens.map fun token => token.text.utf8ByteSize+4).sum+
      (environment.map fun cell => cell.name.utf8ByteSize+valueFields cell.value+1).sum+1)))
    let staticNames := definition.original.header.formals.map (·.name)
    let children (trees : List (Sigma SourceSyntax.Tree)) : WorkM (List Value × Outcome sources) :=
      trees.foldlM (fun (values,previous) child => do
        let result ← next state scope previous.remaining child.2
        pure (values ++ [result.value],append previous result))
        ([],{value := [],remaining := environment})
    match tree with
    | .empty .. => pure {value := [.ordinary [.fixed .unit]],remaining := environment}
    | .literal .. => pure {value := [.ordinary [.fixed .bit]],remaining := environment}
    | .move _ term _ =>
      let (value,remaining) ← adapt (GenericValues.move term environment)
      pure {value,remaining}
    | .binding statement expression rest =>
      let first ← next state scope environment expression
      let names ← bindingNames statement.statement.pattern
      guard (names.all fun name => !staticNames.contains name) .request
      let remaining ← adapt (GenericValues.bind (statement.statement.pattern.map (·.text)) first.value first.remaining
        (statement.statement.keyword.span.startByte+1))
      pure (append first (← next state (names ++ scope) remaining rest))
    | .staticBindings leading _ rest =>
      let (state,scope,rows) ← leading.bindings.foldlM (fun (state,scope,rows) binding => do
        let nextState ← GenericLexicalNatural.bind state owner scope binding.name.text binding.natural.expression
        let selected ← NaturalRows.expression sources owner state.prepared.helpers scope binding.natural.expression
        pure (nextState,binding.name.text :: scope,rows ++ selected)) (state,scope,[])
      let result ← next state scope environment rest
      pure {result with rows := rows ++ result.rows}
    | .sequence _ expression rest =>
      let first ← next state scope environment expression
      guard (!hasOwner first.value) .request
      pure (append first (← next state scope first.remaining rest))
    | .group written trees =>
      let (values,result) ← children trees.trees
      let value := if values.isEmpty then [.ordinary [.fixed .unit]] else
        if values.length == 1 && (written.group.arguments.head?.bind (·.followingComma)).isNone then values.flatten
        else .tuple values.length :: values.flatten
      pure {result with value}
    | .boolean _ trees =>
      let (values,result) ← children trees.trees
      for value in values do GenericValues.expect state value [.ordinary [.fixed .bit]]
      pure {result with value := [.ordinary [.fixed .bit]]}
    | .conditional _ condition thenBody elseBody =>
      let condition ← next state scope environment condition
      GenericValues.expect state condition.value [.ordinary [.fixed .bit]]
      let left ← next state scope condition.remaining thenBody
      let right ← next state scope condition.remaining elseBody
      pure (append condition (← branches state state condition.remaining left right))
    | .matching written scrutinee trees =>
      let selected ← next state scope environment scrutinee
      let code ← ordinaryCode selected.value
      let [.fixed (.enumeration _ variants)] := code | throw .request
      guard (written.parts.arms.length == trees.trees.length) .request
      let arms ← (written.parts.arms.zip trees.trees).mapM fun (arm,body) => do
        let label ← SourceNominal.readVariant sources owner scope arm.label
        GenericValues.expect state selected.value (← typedNominal state label.nominal.query.basis)
        let rows ← NaturalRows.typeRead sources owner state.prepared.helpers [] (arm.label.typeTokens.map (·.text))
          label.nominal.query
        let result ← next state scope selected.remaining body.2
        pure (label.ordinal,{result with rows := rows ++ result.rows})
      let ordinals := arms.map (·.1)
      guard (ordinals.length == variants.length && ordinals.all (· < variants.length) &&
        ordinals.eraseDups.length == ordinals.length) .request
      let some first := arms.head? | throw .request
      let result ← arms.tail.foldlM (fun previous (_,arm) =>
        branches state state selected.remaining previous arm) first.2
      pure (append selected result)
    | .staticConditional written thenBody elseBody =>
      let condition ← GenericLexicalNatural.readPredicate state.prepared state.environment scope written.predicate
      let guardOrigin : GenericLexicalNatural.GuardOrigin written.predicate :=
        ⟨written.parts.keyword,written.written.marker,written.parts.condition,written.predicateRead⟩
      let leftEnvironment ← GenericLexicalNatural.underPredicate condition true (some guardOrigin)
      let rightEnvironment ← GenericLexicalNatural.underPredicate condition false (some guardOrigin)
      let leftState := {state with environment := leftEnvironment}
      let rightState := {state with environment := rightEnvironment}
      let left ← next leftState scope environment thenBody
      let right ← next rightState scope environment elseBody
      let rows ← NaturalRows.bindings sources owner state.prepared.helpers condition.bindings
      let result ← branches leftState rightState environment left right
      pure {result with rows := rows ++ result.rows}
    | .selection _ parsed _ =>
      let selector ← adapt (QuantumMoves.parse 65 (parsed.selector.map (·.text)))
      let target ← adapt (QuantumMoves.parse 65 (parsed.target.map (·.text)))
      let (selector,remaining) ← adapt (GenericValues.move selector environment)
      let (target,remaining) ← adapt (GenericValues.move target remaining)
      selection reader state scope definition.operations parsed selector target remaining
    | .selectionExpression _ parsed _ selector target =>
      let first ← next state scope environment selector
      let last ← next state scope first.remaining target
      let result ← selection reader state scope definition.operations parsed first.value last.value last.remaining
      pure (append first (append last result))
    | .basis written input body =>
      let input ← next state scope environment input
      let [.owner inputBasis] := input.value | throw .request
      let bound ← adapt (GenericValues.ordinaryValue inputBasis)
      let ordinary := input.remaining.filter (fun cell => !hasOwner cell.value)
      let names ← bindingNames written.parts.pattern
      guard (names.all fun name => !staticNames.contains name) .request
      let initial ← adapt (GenericValues.bind (written.parts.pattern.map (·.text)) bound ordinary
        (written.parts.keyword.span.startByte+1))
      checkClassicalTree definition.modules state (names ++ scope) (written.parts.body.length+1) body
      let body ← next state (names ++ scope) initial body
      guard (!body.quantumUse && !hasOwner body.value) .request
      let outputBasis ← ordinaryCode body.value
      let effect ← basisEffect state inputBasis outputBasis
      let obligation : BasisObligation sources := ⟨owner,name,written.parts.keyword.span.startByte,state,inputBasis,outputBasis⟩
      let result : Outcome sources := {body with
        value := [.owner outputBasis],remaining := input.remaining,
        effect := direct effect,quantumUse := true,needs := body.needs ++ [⟨body.effect,.unitary,true⟩],
        basisObligations := body.basisObligations ++ [obligation]}
      pure (append input result)
    | .computed written input body =>
      let input ← next state scope environment input
      let [.owner inputBasis] := input.value | throw .request
      let predicate ← computedPredicate reader state scope inputBasis written.parts.predicate
      let predicateEffect := functionEffect state.owner predicate.definition
      let (logical,initial,names,expected) ← match written.parts.logical,written.parts.data with
        | none,none =>
          pure (none,input.remaining.filter (fun cell => !hasOwner cell.value),
            [written.parts.auxiliary.text],[.owner [.fixed .bit]])
        | some reference,some data => do
          let logical ← operationWithModules reader state scope definition.operations 65 (some inputBasis) reference.argument.tokens
          guard logical.paths.applicable .request
          let _ ← SymbolicTypes.equate state logical.input inputBasis
          let _ ← SymbolicTypes.equate state logical.output inputBasis
          let initial ← adapt (GenericValues.bind [data.text] [.owner inputBasis] [] (data.span.startByte+1))
          pure (some logical,initial,[data.text,written.parts.auxiliary.text],
            [.tuple 2,.owner inputBasis,.owner [.fixed .bit]])
        | _,_ => throw .request
      guard (names.all fun name => !staticNames.contains name) .request
      let initial ← adapt (GenericValues.bind [written.parts.auxiliary.text] [.owner [.fixed .bit]] initial
        (written.parts.auxiliary.span.startByte+1))
      let region ← next state (names ++ scope) initial body
      guard (region.remaining.all fun cell => !hasOwner cell.value) .request
      GenericValues.expect state region.value expected
      let [keyword] := written.parts.header.call.callee | throw .request
      let offset := keyword.span.startByte
      let obligation : ComputedObligation sources :=
        ⟨owner,name,offset,state,inputBasis,tokens,written,predicate,logical⟩
      let result : Outcome sources := {region with
        value := [.owner inputBasis],remaining := input.remaining,effect := direct .unitary,quantumUse := true,
        references := region.references ++ [(predicate.resolution.moduleName,predicate.resolution.declaration.name)] ++
          (logical.toList.flatMap (·.references)),
        needs := region.needs ++ [⟨predicateEffect,.unitary,true⟩,⟨region.effect,.unitary,false⟩] ++
          logical.toList.flatMap (fun operation => operation.needs ++ [⟨operation.effect,.unitary,false⟩]),
        meanings := region.meanings ++ logical.toList.flatMap (·.meanings),
        activities := logical.toList.flatMap (fun operation => operation.activities ++
          [.duty ⟨operation.origin,operation.subject,.access ⟨true,false,false⟩,.computedLogical,[],operation.suppliers,none⟩]) ++
          region.activities,
        computedObligations := region.computedObligations ++ [obligation],
        rows := predicate.rows ++ logical.toList.flatMap (·.rows) ++ region.rows}
      pure (append input result)
    | .variant written =>
      let reference ← SourceNominal.readVariant sources owner scope written
      let value ← typedNominal state reference.nominal.query.basis
      let rows ← NaturalRows.typeRead sources owner state.prepared.helpers [] (written.typeTokens.map (·.text))
        reference.nominal.query
      pure {value,remaining := environment,rows}
    | .record written trees =>
      let reference ← SourceNominal.readRecord sources owner scope written
      let (values,result) ← children trees.trees
      guard (values.length == reference.fields.length) .request
      for (value,field) in values.zip reference.fields do
        GenericValues.expect state value (← typedNominal state field.basis)
      let value ← typedNominal state reference.nominal.query.basis
      let rows ← NaturalRows.typeRead sources owner state.prepared.helpers [] (written.typeTokens.map (·.text))
        reference.nominal.query
      pure {result with value,rows := result.rows ++ rows}
    | .projection written receiver =>
      let result ← next state scope environment receiver
      let code ← ordinaryCode result.value
      let .fixed (.record origin _) :: _ := code | throw .request
      let fields ← MemberFields.readOriginalFields sources origin.moduleName origin.declarationName
      let reference ← SourceNominal.readProjection sources owner fields.original.basis written
      GenericValues.expect state result.value (← typedNominal state fields.original.basis)
      let value ← typedNominal state reference.field.basis
      let rows ← NaturalRows.nominalOrigins sources state.prepared.helpers fields.original.basis
      pure {result with value,rows := result.rows ++ rows}
    | .call call trees =>
      let (values,arguments) ← children trees.trees
      let transformed ← adapt (SourceRuntimeTransformSyntax.read call.call.callee)
      let transformedNamed ← match transformed with
        | none => pure false
        | some transformed =>
          let base := transformed.base
          let candidate ← CallName.readWithModules sources definition.modules owner scope base.2.callee
          pure (match candidate.decision with | .lexical .. => false | _ => true)
      if transformedNamed then
        let some transformed := transformed | throw .request
        pure (append arguments (← runtimeTransform reader state scope definition.operations transformed values arguments.remaining))
      else if SourceOperationSyntax.selected (definition.operations.map (·.1)) call.call.callee then
        pure (append arguments (← applyOperation reader state scope definition.operations call.call.callee values arguments.remaining))
      else
        let written ← adapt (StaticApplication.readSyntax call.call.callee)
        let candidate ← CallName.readWithModules sources definition.modules owner scope written.callee
        match candidate.decision with
        | .primitive _ _ _ _ _ _ .phase _ =>
          let .application staticCall := written | throw .request
          guard (staticCall.call.arguments.length == 2) .request
          let rows ← staticCall.call.arguments.mapM fun argument => do
            let expression ← adapt (StaticBindings.natural argument.tokens)
            let _ ← GenericLexicalNatural.read state.prepared state.environment scope expression.expression
            NaturalRows.expression sources owner state.prepared.helpers scope expression.expression
          let [value] := values | throw .request
          GenericValues.expect state value [.owner [.fixed .bit]]
          pure (append arguments {
            value,remaining := arguments.remaining,quantumUse := true,
            rows := CallName.sourceRows candidate ++ rows.flatten})
        | .primitive _ _ _ _ _ _ kind _ =>
          let result ← primitiveApplication state scope kind written.arguments values arguments.remaining
          pure (append arguments {result with rows := CallName.sourceRows candidate ++ result.rows})
        | _ =>
          let some resolution := CallName.candidateResolution candidate | throw .request
          let application ← instantiateWithReader state scope written resolution.moduleName resolution.declaration.name
            (operationWithModules reader state scope definition.operations 65 none) true reader
          guard (values.length == application.parameters.length) .request
          for (actual,expected) in values.zip application.parameters do GenericValues.expect state actual expected
          let externalPermission := owner != application.owner &&
            !application.definition.original.envelope.parsedHeader.ordinaryOnly &&
            application.definition.original.envelope.parsedHeader.effect.isSome
          let result : Outcome sources := {
            value := application.result,remaining := arguments.remaining,
            effect := functionEffect owner application.definition,quantumUse := externalPermission,
            references := application.references,needs := application.needs,meanings := application.meanings,
            activities := application.activities,
            recursions := application.recursion.toList,
            rows := CallName.sourceRows candidate ++ application.rows}
          pure (append arguments result))

def checkTree {sources owner name} (definition : Definition sources owner name)
    (tree : SourceSyntax.Tree definition.original.envelope.occurrence.body)
    (prepared : Option (PreparedDefinitions definition.context) := none) : WorkM (Outcome sources) := do
  let patterns ← adapt (ParameterPatterns.read definition.original.envelope)
  let initial ← adapt (GenericValues.seed patterns definition.parameters)
  let staticNames := definition.original.header.formals.map (·.name)
  guard (initial.all fun cell => !staticNames.contains cell.name) .request
  if definition.original.envelope.parsedHeader.ordinaryOnly then
    checkClassicalTree definition.modules definition.state (staticNames ++ initial.map (·.name))
      (definition.original.envelope.occurrence.body.length+1) tree
  let result ← evaluator definition prepared (definition.original.envelope.occurrence.body.length+1)
    definition.state (staticNames ++ initial.map (·.name)) initial tree
  guard (result.remaining.all fun cell => !hasOwner cell.value) .request
  GenericValues.expect definition.state result.value definition.result
  pure result

structure BodyRecord (sources : Sources) where
  owner : String
  name : String
  definition : Definition sources owner name
  prepared : Option (PreparedDefinitions definition.context)
  tree : SourceSyntax.Tree definition.original.envelope.occurrence.body
  outcome : Outcome sources
  checked : ∃ before after,(checkTree definition tree prepared).run before = (.ok outcome,after)

def BodyRecord.id {sources} (body : BodyRecord sources) : DefId := (body.owner,body.name)

def BodyRecord.entry {sources} (body : BodyRecord sources) : Entry := ⟨body.id,body.outcome.effect⟩

def BodyRecord.quantumDirect {sources} (body : BodyRecord sources) : Bool :=
  body.outcome.quantumUse || body.definition.parameters.any hasOwner || hasOwner body.definition.result ||
    !body.definition.operations.isEmpty

def readBody (sources : Sources) (owner name : String)
    (helpers : Option (NaturalHelpers.Checked sources) := none)
    (originals : Option (OrdinarySignature.Originals sources) := none)
    (modules : Option (SourceModules.Prepared sources) := none)
    (meanings : Option (SourceMeaning.Prepared sources) := none) : WorkM (BodyRecord sources) := do
  let definition ← readDefinition sources owner name helpers originals modules meanings
  let tokens := definition.original.envelope.occurrence.body
  let tree ← adapt (SourceSyntax.read (tokens.length+1) 0 true tokens)
  let result ← NaturalAffine.witness (checkTree definition tree)
  pure ⟨owner,name,definition,none,tree,result.val,by with_reducible exact result.property⟩

/-- Reuse only exact original setup. Parsing and symbolic evaluation of this
body run here, and retain their genuine prepared-reader argument. -/
def readBodyPrepared {sources context} (prepared : @PreparedDefinitions sources context)
    (owner name : String) : WorkM (BodyRecord sources) := do
  let selected ← lookupDefinition prepared owner name
  let definition := selected.value
  let table : PreparedDefinitions definition.context := selected.sameContext.symm ▸ prepared
  let tokens := definition.original.envelope.occurrence.body
  let tree ← adapt (SourceSyntax.read (tokens.length+1) 0 true tokens)
  let result ← NaturalAffine.witness (checkTree definition tree (some table))
  pure ⟨owner,name,definition,some table,tree,result.val,by with_reducible exact result.property⟩

def discover (sources : Sources) (fuel : Nat) (pending : List DefId) (visited : List (BodyRecord sources))
    (helpers : Option (NaturalHelpers.Checked sources) := none)
    (originals : Option (OrdinarySignature.Originals sources) := none)
    (modules : Option (SourceModules.Prepared sources) := none)
    (meanings : Option (SourceMeaning.Prepared sources) := none) : WorkM (List (BodyRecord sources)) :=
  (Nat.rec
    (motive := fun _ => List DefId → List (BodyRecord sources) → WorkM (List (BodyRecord sources)))
    (fun (pending : List DefId) (visited : List (BodyRecord sources)) =>
      if pending.isEmpty then pure visited else throw .limit)
    (fun (_ : Nat)
        (next : List DefId → List (BodyRecord sources) → WorkM (List (BodyRecord sources)))
        (pending : List DefId) (visited : List (BodyRecord sources)) => do
      exactWork (Exact.charge (16*((pending.map fun (owner,name) => owner.utf8ByteSize+name.utf8ByteSize+1).sum+
        (visited.map fun body => body.owner.utf8ByteSize+body.name.utf8ByteSize+1).sum+1)))
      match pending with
      | [] => pure visited
      | (owner,name) :: rest =>
        if visited.any (fun body => body.id == (owner,name)) then next rest visited else
          let body ← readBody sources owner name helpers originals modules meanings
          next (rest ++ body.outcome.references) (visited ++ [body])) fuel) pending visited

private def effectEntries {sources} (records : List (BodyRecord sources)) : List Entry := records.map (·.entry)

private theorem effectEntryIds {sources} (records : List (BodyRecord sources)) :
    (effectEntries records).map Entry.id = records.map BodyRecord.id := by
  induction records with
  | nil => rfl
  | cons body rest ih =>
    change body.id :: (effectEntries rest).map Entry.id = body.id :: rest.map BodyRecord.id
    exact congrArg (List.cons body.id) ih

private def directQuantum {sources} (records : List (BodyRecord sources)) (id : DefId) : Bool :=
  records.find? (·.id == id) |>.map (·.quantumDirect) |>.getD true

def formulaEffect {sources} (records : List (BodyRecord sources)) (formula : Formula) : WorkM (Semantics.Raw.Effect × Bool) := do
  formula.dependencies.foldlM (fun (effect,quantum) id => do
    let inferred ← SourceEffectClosure.read (effectEntries records) id
    pure (SourceEffect.join effect inferred.inferred,quantum || inferred.quantumUse (directQuantum records)))
    (formula.direct,false)

def checkNeeds {sources} (records : List (BodyRecord sources)) (needs : List Need) : WorkM Unit := do
  for need in needs do
    let (effect,quantum) ← formulaEffect records need.effect
    guard (SourceEffect.rank effect ≤ SourceEffect.rank need.ceiling && (!need.classical || !quantum)) .request

private def formulaEffectPrepared {sources} (records : List (BodyRecord sources))
    (prepared : SourceEffectClosure.Prepared (effectEntries records)) (formula : Formula) :
    WorkM (Semantics.Raw.Effect × Bool) := do
  formula.dependencies.foldlM (fun (effect,quantum) id => do
    let inferred ← SourceEffectClosure.readPrepared prepared id
    pure (SourceEffect.join effect inferred.inferred,quantum || inferred.quantumUse (directQuantum records)))
    (formula.direct,false)

private def formulaEffectCohort {sources} (records : List (BodyRecord sources))
    (prepared : SourceEffectClosure.Prepared (effectEntries records))
    (cohort : Option (SourceEffectClosure.Cohort prepared)) (formula : Formula) :
    WorkM (Semantics.Raw.Effect × Bool) := do
  match cohort with
  | none => formulaEffectPrepared records prepared formula
  | some cohort =>
    formula.dependencies.foldlM (fun (effect,quantum) id => do
      let selected ← SourceEffectClosure.lookup cohort id
      let inferred := selected.value.checked
      pure (SourceEffect.join effect inferred.inferred,quantum || inferred.quantumUse (directQuantum records)))
      (formula.direct,false)

private def checkNeedsPrepared {sources} (records : List (BodyRecord sources))
    (prepared : SourceEffectClosure.Prepared (effectEntries records)) (needs : List Need)
    (cohort : Option (SourceEffectClosure.Cohort prepared) := none) : WorkM Unit := do
  for need in needs do
    let (effect,quantum) ← formulaEffectCohort records prepared cohort need.effect
    guard (SourceEffect.rank effect ≤ SourceEffect.rank need.ceiling && (!need.classical || !quantum)) .request

structure Inferred {sources} (records : List (BodyRecord sources)) (body : BodyRecord sources) where
  prepared : SourceEffectClosure.Prepared (effectEntries records)
  cohort : Option (SourceEffectClosure.Cohort prepared)
  closure : SourceEffectClosure.Checked (effectEntries records) body.id
  closureOriginal : ∃ before after,
    (SourceEffectClosure.readPrepared prepared body.id).run before = (.ok closure,after)
  effectBound : SourceEffect.permits body.definition.original.envelope.parsedHeader.effect closure.inferred = true
  classical : body.definition.original.envelope.parsedHeader.ordinaryOnly = true →
    closure.quantumUse (directQuantum records) = false
  publicPermission : body.definition.original.envelope.declaration.isPublic = true →
    closure.quantumUse (directQuantum records) = true → body.definition.original.envelope.parsedHeader.effect.isSome = true
  needs : ∃ before after,(checkNeedsPrepared records prepared body.outcome.needs cohort).run before = (.ok (),after)

private def inferClosure {sources} (records : List (BodyRecord sources))
    (prepared : SourceEffectClosure.Prepared (effectEntries records))
    (cohort : Option (SourceEffectClosure.Cohort prepared)) (body : BodyRecord sources)
    (selected : SourceEffectClosure.Closure prepared body.id) :
    WorkM (Inferred records body) := do
  let closure := selected.checked
  if effectBound : SourceEffect.permits body.definition.original.envelope.parsedHeader.effect closure.inferred = true then
    if classical : body.definition.original.envelope.parsedHeader.ordinaryOnly = true →
        closure.quantumUse (directQuantum records) = false then
      if publicPermission : body.definition.original.envelope.declaration.isPublic = true →
          closure.quantumUse (directQuantum records) = true → body.definition.original.envelope.parsedHeader.effect.isSome = true then
        let needs ← NaturalAffine.witness (checkNeedsPrepared records prepared body.outcome.needs cohort)
        have unit : needs.val = () := by cases needs.val; rfl
        pure ⟨prepared,cohort,closure,selected.original,effectBound,classical,publicPermission,
          by with_reducible simpa only [unit] using needs.property⟩
      else throw .request
    else throw .request
  else throw .request

private def inferPrepared {sources} (records : List (BodyRecord sources))
    (prepared : SourceEffectClosure.Prepared (effectEntries records)) (body : BodyRecord sources) :
    WorkM (Inferred records body) := do
  inferClosure records prepared none body (← SourceEffectClosure.readClosure prepared body.id)

def infer {sources} (records : List (BodyRecord sources)) (body : BodyRecord sources) : WorkM (Inferred records body) := do
  inferPrepared records (← SourceEffectClosure.prepare (effectEntries records)) body

inductive AllInferred {sources} (records : List (BodyRecord sources)) : List (BodyRecord sources) → Type where
  | nil : AllInferred records []
  | cons {body rest} (head : Inferred records body) (tail : AllInferred records rest) : AllInferred records (body :: rest)

private def inferAllPrepared {sources} (records : List (BodyRecord sources))
    (prepared : SourceEffectClosure.Prepared (effectEntries records)) :
    (pending : List (BodyRecord sources)) → WorkM (AllInferred records pending)
  | [] => pure .nil
  | body :: rest => do pure (.cons (← inferPrepared records prepared body) (← inferAllPrepared records prepared rest))

private def inferAllCohort {sources} (records : List (BodyRecord sources))
    (prepared : SourceEffectClosure.Prepared (effectEntries records)) (cohort : SourceEffectClosure.Cohort prepared) :
    (pending : List (BodyRecord sources)) → SourceEffectClosure.Closures prepared (pending.map BodyRecord.id) →
      WorkM (AllInferred records pending)
  | [],.nil => pure .nil
  | body :: rest,.cons head tail => do
    pure (.cons (← inferClosure records prepared (some cohort) body head)
      (← inferAllCohort records prepared cohort rest tail))

/-- Every original body root is checked once in its ordered cohort. Each Need
still performs its own exact-root lookup and effect/classical guard. Arbitrary
subset callers keep the prepared traversal rather than checking extra roots. -/
def inferAll {sources} (records : List (BodyRecord sources))
    (pending : List (BodyRecord sources)) : WorkM (AllInferred records pending) := do
  match pending with
  | [] => pure .nil
  | first :: rest =>
    let prepared ← SourceEffectClosure.prepare (effectEntries records)
    let fields := ((first :: rest).map fun body => body.owner.utf8ByteSize+body.name.utf8ByteSize+2).sum+
      (records.map fun body => body.owner.utf8ByteSize+body.name.utf8ByteSize+2).sum
    exactWork (Exact.charge (16*(fields+(first :: rest).length+records.length+1)))
    if same : (first :: rest).map BodyRecord.id = records.map BodyRecord.id then
      let cohort ← SourceEffectClosure.readCohort prepared
      let originalCells : SourceEffectClosure.Closures prepared (records.map BodyRecord.id) :=
        effectEntryIds records ▸ cohort.closures
      let cells : SourceEffectClosure.Closures prepared ((first :: rest).map BodyRecord.id) := same.symm ▸ originalCells
      inferAllCohort records prepared cohort (first :: rest) cells
    else inferAllPrepared records prepared (first :: rest)

def AllInferred.get {sources} {records : List (BodyRecord sources)} :
    {pending : List (BodyRecord sources)} → AllInferred records pending → (index : Fin pending.length) →
      Inferred records (pending[index.val]'index.isLt)
  | [],.nil,index => False.elim (Nat.not_lt_zero index.val index.isLt)
  | _ :: _,.cons head _,⟨0,_⟩ => head
  | _ :: _,.cons _ tail,⟨index+1,bound⟩ => tail.get ⟨index,Nat.lt_of_succ_lt_succ bound⟩

def Inferred.inferredEffect {sources records body} (inferred : @Inferred sources records body) : Semantics.Raw.Effect :=
  inferred.closure.inferred

def Inferred.quantumUse {sources records body} (inferred : @Inferred sources records body) : Bool :=
  inferred.closure.quantumUse (directQuantum records)

private def rejectCycleFrom {sources} (records : List (BodyRecord sources)) (root : DefId) :
    Nat → List DefId → List DefId → WorkM Unit :=
  Nat.rec (fun pending _ => if pending.isEmpty then pure () else throw .limit)
    (fun _ next pending visited => do
      exactWork (Exact.charge (16*(records.length+pending.length+visited.length+1)))
      match pending with
      | [] => pure ()
      | first :: rest =>
        guard (first != root) .request
        if visited.contains first then next rest visited else
          let some body := records.find? (·.id == first) | throw .request
          next (rest ++ body.outcome.references.filter (· != body.id)) (first :: visited))

def checkCycles {sources} (records : List (BodyRecord sources)) : WorkM Unit := do
  let fuel := records.length+(records.map fun body => body.outcome.references.length).sum+1
  for body in records do
    rejectCycleFrom records body.id fuel (body.outcome.references.filter (· != body.id)) []

def originalTree {sources owner name} {original : OrdinarySignature.Original sources owner name}
    (definition : Definition sources owner name) (same : definition.original.envelope = original)
    (tree : SourceSyntax.Tree original.occurrence.body) : SourceSyntax.Tree definition.original.envelope.occurrence.body :=
  (congrArg (fun envelope : OrdinarySignature.Original sources owner name => envelope.occurrence.body) same).symm ▸ tree

structure Root {sources owner name} (original : OrdinarySignature.Original sources owner name)
    (tree : SourceSyntax.Tree original.occurrence.body) where
  definition : Definition sources owner name
  sameOriginal : definition.original.envelope = original
  outcome : Outcome sources
  checked : ∃ before after,(checkTree definition (originalTree definition sameOriginal tree)).run before = (.ok outcome,after)

def Root.record {sources owner name original tree} (root : @Root sources owner name original tree) : BodyRecord sources :=
  ⟨owner,name,root.definition,none,originalTree root.definition root.sameOriginal tree,root.outcome,root.checked⟩

structure Checked {sources owner name} (original : OrdinarySignature.Original sources owner name) where
  tree : SourceSyntax.Tree original.occurrence.body
  root : Root original tree
  helpers : NaturalHelpers.Checked sources
  originals : Option (OrdinarySignature.Originals sources)
  modules : Option (SourceModules.Prepared sources)
  meanings : Option (SourceMeaning.Prepared sources)
  records : List (BodyRecord sources)
  discovered : ∃ before after,
    (discover sources ((sources.toList.map fun row => row.2.utf8ByteSize+1).sum+1)
      root.outcome.references [root.record] (some helpers) originals modules meanings).run before = (.ok records,after)
  all : AllInferred records records
  inferred : Inferred records root.record

def Checked.inferredEffect {sources owner name original} (checked : @Checked sources owner name original) : Semantics.Raw.Effect :=
  checked.inferred.closure.inferred

def Checked.quantumUse {sources owner name original} (checked : @Checked sources owner name original) : Bool :=
  checked.inferred.closure.quantumUse (directQuantum checked.records)

def Checked.basisObligations {sources owner name original} (checked : @Checked sources owner name original) :=
  checked.root.outcome.basisObligations

def Checked.recursiveCalls {sources owner name original} (checked : @Checked sources owner name original) :=
  checked.root.outcome.recursions

def Checked.computedObligations {sources owner name original} (checked : @Checked sources owner name original) :=
  checked.root.outcome.computedObligations

def Checked.sourceRows {sources owner name original} (checked : @Checked sources owner name original) : List (String × String) :=
  checked.records.flatMap fun body => body.definition.rows ++ body.outcome.rows

def readOriginalWithTree {sources owner name}
    (original : OrdinarySignature.Original sources owner name)
    (tree : SourceSyntax.Tree original.occurrence.body)
    (providedHelpers : Option (NaturalHelpers.Checked sources) := none)
    (originals : Option (OrdinarySignature.Originals sources) := none)
    (modules : Option (SourceModules.Prepared sources) := none)
    (meanings : Option (SourceMeaning.Prepared sources) := none) : WorkM (Checked original) := do
  match parsed : StaticHeaders.parse original.parsedHeader with
  | .error _ => throw .request
  | .ok header =>
    let header : StaticHeaders.Original sources owner name := ⟨original,header,parsed⟩
    let helpers ← match providedHelpers with | some helpers => pure helpers | none => NaturalHelpers.read sources
    let definition ← readDefinitionOriginal header (some helpers) originals modules meanings
    have same : definition.val.original.envelope = original := congrArg (fun h => h.envelope) definition.property
    let result ← NaturalAffine.witness (checkTree definition.val (originalTree definition.val same tree))
    let root : Root original tree := ⟨definition.val,same,result.val,by with_reducible exact result.property⟩
    let records ← NaturalAffine.witness (discover sources ((sources.toList.map fun row => row.2.utf8ByteSize+1).sum+1)
      root.outcome.references [root.record] (some helpers) originals modules meanings)
    checkCycles records.val
    let prepared ← SourceEffectClosure.prepare (effectEntries records.val)
    let cohort ← SourceEffectClosure.readCohort prepared
    let cells : SourceEffectClosure.Closures prepared (records.val.map BodyRecord.id) :=
      effectEntryIds records.val ▸ cohort.closures
    let all ← inferAllCohort records.val prepared cohort records.val cells
    let selected ← SourceEffectClosure.lookup cohort root.record.id
    let inferred ← inferClosure records.val prepared (some cohort) root.record selected.value
    pure ⟨tree,root,helpers,originals,modules,meanings,records.val,by with_reducible exact records.property,all,inferred⟩

def readWithTree {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (tree : SourceSyntax.Tree original.occurrence.body)
    (modules : Option (SourceModules.Prepared sources) := none)
    (meanings : Option (SourceMeaning.Prepared sources) := none) : WorkM (Checked original) :=
  match instantiation with
  | .closed _ => readOriginalWithTree original tree none none modules meanings
  | .static _ environment _ =>
    readOriginalWithTree original tree (some ⟨environment.numeric.helpers,environment.numeric.helpersPrepared⟩)
      environment.numeric.originals modules meanings

def readOriginal {sources owner name} (original : OrdinarySignature.Original sources owner name)
    (modules : Option (SourceModules.Prepared sources) := none)
    (meanings : Option (SourceMeaning.Prepared sources) := none) : WorkM (Checked original) := do
  let tokens := original.occurrence.body
  let tree ← adapt (SourceSyntax.read (tokens.length+1) 0 true tokens)
  readOriginalWithTree original tree none none modules meanings

def readWithInstantiation {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (modules : Option (SourceModules.Prepared sources) := none)
    (meanings : Option (SourceMeaning.Prepared sources) := none) : WorkM (Checked original) := do
  let tokens := original.occurrence.body
  let tree ← adapt (SourceSyntax.read (tokens.length+1) 0 true tokens)
  readWithTree instantiation tree modules meanings

end QleisliKernel.SourceTypes.GenericTypeTrace
