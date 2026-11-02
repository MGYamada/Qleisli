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

structure Definition (sources : Sources) (owner name : String) where
  original : StaticHeaders.Original sources owner name
  state : GenericLexicalNatural.SomeEnvironment sources
  stateOriginal : HEq state.prepared.original original
  parameters : List Value
  result : Value
  operations : List (String × Operation sources)
  rows : List (String × String)

private def paths (header : StaticHeaders.Parsed) (name : String) : OperationPaths.Paths :=
  ⟨header.access.contains (.applicable,name),header.access.contains (.adjointable,name),
    header.access.contains (.controllable,name)⟩

private def meets (actual required : OperationPaths.Paths) : Bool :=
  (!required.applicable || actual.applicable) && (!required.adjointable || actual.adjointable) &&
    (!required.controllable || actual.controllable)

private def meet (a b : OperationPaths.Paths) : OperationPaths.Paths := a.meet b

private def formalOperation {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (formal : StaticHeaders.Formal) : WorkM (Operation sources) := do
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
      let selected ← SourceMeaning.select sources state.owner scope tokens
      let _ ← SymbolicTypes.checkRefinement state scope formal.ordinal parsed.input parsed.output
        selected.meaning.graph.input selected.meaning.graph.output
      pure [selected.request]
  pure ⟨ports.input.result.code,ports.output.result.code,direct effect,access,[],[],meanings,
    ports.input.result.rows ++ ports.output.result.rows ++ meanings.flatMap (·.sourceRows)⟩

def readDefinitionOriginal {sources owner name} (original : StaticHeaders.Original sources owner name)
    (helpers : Option (NaturalHelpers.Checked sources) := none)
    (originals : Option (OrdinarySignature.Originals sources) := none) :
    WorkM {definition : Definition sources owner name // definition.original = original} := do
  let helpers ← match helpers with | some helpers => pure helpers | none => NaturalHelpers.read sources
  let numeric ← StaticNatural.prepareOriginalWithHelpers original ["0"] helpers originals
  let state : GenericLexicalNatural.SomeEnvironment sources :=
    ⟨owner,name,numeric.prepared,GenericLexicalNatural.initial numeric.prepared⟩
  let parameters ← original.envelope.parsedHeader.parameterTypes.mapM (GenericValues.readType state 65)
  let result ← GenericValues.readType state 65 (original.envelope.parsedHeader.resultTokens.map (·.text))
  let operations ← original.header.formals.mapM fun formal => do
    match formal.kind with
    | .operation _ => pure [(formal.name,← formalOperation state formal)]
    | _ => pure []
  let rows ← NaturalRows.bindings sources owner state.prepared.helpers state.prepared.bindings
  pure ⟨⟨original,state,by
      change HEq numeric.prepared.original original
      rw [numeric.originalHeader],parameters.map (·.value),result.value,operations.flatten,
    (owner,original.envelope.source) :: rows ++ parameters.flatMap (·.rows) ++ result.rows ++
      operations.flatten.flatMap (fun (_,operation) => operation.rows)⟩,rfl⟩

def readDefinition (sources : Sources) (owner name : String)
    (helpers : Option (NaturalHelpers.Checked sources) := none)
    (originals : Option (OrdinarySignature.Originals sources) := none) : WorkM (Definition sources owner name) := do
  pure (← readDefinitionOriginal (← StaticHeaders.read sources owner name originals) helpers originals).val

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

def instantiate {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) {tokens} (written : StaticApplication.Syntax tokens) (owner name : String)
    (operationReader : List LocatedToken → WorkM (Operation sources)) (runtimeRecursion : Bool) :
    WorkM (Application sources) := do
  let helpers : NaturalHelpers.Checked sources := ⟨state.prepared.helpers,state.prepared.helpersPrepared⟩
  let definition ← readDefinition sources owner name (some helpers) state.prepared.originals
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
  pure ⟨owner,name,definition,parameters,result,operations,recursion,
    (owner,name) :: operations.flatMap (fun (_,operation) => operation.references),needs,
    operations.flatMap (fun (_,operation) => operation.meanings) ++ definition.operations.flatMap (fun (_,operation) => operation.meanings),
    definition.rows ++ actuals.flatMap (·.2.2) ++ operations.flatMap (fun (_,operation) => operation.rows)⟩

private def named {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (tokens : List LocatedToken) : WorkM (Resolved × List (String × String)) := do
  let candidate ← CallName.read sources state.owner scope tokens
  let some resolution := CallName.candidateResolution candidate | throw .request
  pure (resolution,CallName.sourceRows candidate)

private def combineOperation {sources} (a b : Operation sources) (input output : Code)
    (effect : Formula) (paths : OperationPaths.Paths) : Operation sources :=
  ⟨input,output,effect,paths,a.references ++ b.references,a.needs ++ b.needs,
    a.meanings ++ b.meanings,a.rows ++ b.rows⟩

private def validateCount {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (tokens : List LocatedToken) : WorkM (List (String × String)) := do
  let texts := tokens.map (·.text)
  let tokens := if texts.take 2 == ["2","^"] then tokens.drop 2 else tokens
  let expression ← adapt (StaticBindings.natural tokens)
  let _ ← GenericLexicalNatural.read state.prepared state.environment scope expression.expression
  NaturalRows.expression sources state.owner state.prepared.helpers scope expression.expression

def operation {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (formals : List (String × Operation sources)) :
    Nat → Option Code → List LocatedToken → WorkM (Operation sources) :=
  Nat.rec (fun _ _ => throw .limit) (fun _ next primitiveTarget tokens => do
    exactWork (Exact.charge (32*((tokens.map fun token => token.text.utf8ByteSize+4).sum+1)))
    if tokens.getLast?.map (·.text) == some ")" then
      let call ← adapt (CallSyntax.read tokens)
      match call.call.callee.map (·.text),call.call.arguments with
      | ["adjoint"],[child] =>
        let child ← next none child.tokens
        guard child.paths.adjointable .request
        pure {child with
          input := child.output,output := child.input,
          effect := direct .unitary,paths := ⟨child.paths.adjointable,child.paths.applicable,child.paths.controllable⟩,
          needs := child.needs ++ [⟨child.effect,.unitary,false⟩]}
      | ["controlled"],[child] =>
        let child ← next none child.tokens
        let _ ← SymbolicTypes.equate state child.input child.output
        let basis := .fixed .pair :: .fixed .bit :: child.input
        pure {child with
          input := basis,output := basis,effect := direct .unitary,
          paths := ⟨child.paths.controllable,child.paths.controllable,child.paths.controllable⟩,
          needs := child.needs ++ [⟨child.effect,.unitary,false⟩]}
      | ["power"],[child,count] =>
        let child ← next none child.tokens
        let _ ← SymbolicTypes.equate state child.input child.output
        let rows ← validateCount state scope count.tokens
        pure {child with rows := child.rows ++ rows}
      | ["then_op"],[left,right] =>
        let left ← next none left.tokens
        let right ← next none right.tokens
        let _ ← SymbolicTypes.equate state left.output right.input
        pure (combineOperation left right left.input right.output (join left.effect right.effect) (meet left.paths right.paths))
      | ["tensor_op"],[left,right] =>
        let left ← next none left.tokens
        let right ← next none right.tokens
        pure (combineOperation left right (.fixed .pair :: left.input ++ right.input)
          (.fixed .pair :: left.output ++ right.output) (join left.effect right.effect) (meet left.paths right.paths))
      | ["conjugate_op"],[outer,middle] =>
        let outer ← next none outer.tokens
        let middle ← next none middle.tokens
        let _ ← SymbolicTypes.equate state outer.input middle.input
        let _ ← SymbolicTypes.equate state middle.input middle.output
        let result := combineOperation outer middle outer.output outer.output (join outer.effect middle.effect)
          ⟨outer.paths.applicable && outer.paths.adjointable && middle.paths.applicable,
            outer.paths.applicable && outer.paths.adjointable && middle.paths.adjointable,
            outer.paths.applicable && outer.paths.adjointable && middle.paths.controllable⟩
        pure {result with needs := result.needs ++ [⟨outer.effect,.unitary,false⟩]}
      | ["checked_op"],[child,meaning] =>
        let _ ← adapt (CallName.readName child.tokens)
        let child ← next none child.tokens
        let selected ← SourceMeaning.select sources state.owner scope (meaning.tokens.map (·.text))
        let input ← SymbolicTypes.ofClosed (StaticHeaders.frame state.prepared.original).binders.length selected.meaning.graph.input
        let output ← SymbolicTypes.ofClosed (StaticHeaders.frame state.prepared.original).binders.length selected.meaning.graph.output
        let _ ← SymbolicTypes.equate state child.input input.code
        let _ ← SymbolicTypes.equate state child.output output.code
        pure {child with meanings := child.meanings ++ [selected.request],rows := child.rows ++ selected.queryRows}
      | _,_ => throw .request
    else
      let written ← adapt (StaticApplication.readSyntax tokens)
      let candidate ← CallName.read sources state.owner scope written.callee
      match candidate.decision with
      | .lexical name .. =>
        guard written.arguments.isEmpty .request
        let some (_,formal) := formals.find? (·.1 == name) | throw .request
        pure formal
      | .primitive _ _ _ _ _ _ kind _ =>
        guard written.arguments.isEmpty .request
        let some target := primitiveTarget | throw .request
        match kind with
        | .h =>
          let _ ← SymbolicTypes.equate state target [.fixed .bit]
          pure ⟨target,target,direct .unitary,⟨true,true,true⟩,[],[],[],CallName.sourceRows candidate⟩
        | .globalPhaseEighth => pure ⟨target,target,direct .unitary,⟨true,true,true⟩,[],[],[],CallName.sourceRows candidate⟩
        | _ => throw .request
      | _ =>
        let some resolution := CallName.candidateResolution candidate | throw .request
        let application ← instantiate state scope written resolution.moduleName resolution.declaration.name (next none) false
        let [[.owner input]] := application.parameters | throw .request
        let [.owner output] := application.result | throw .request
        let reverse := application.operations.all fun (_,actual) => actual.paths.applicable && actual.paths.adjointable
        let control := application.operations.all fun (_,actual) =>
          actual.paths.applicable && actual.paths.adjointable && actual.paths.controllable
        let same ← SymbolicTypes.optionalEquality state input output
        let effect := functionEffect state.owner application.definition
        pure ⟨input,output,effect,⟨true,reverse,control && same.isSome⟩,application.references,
          application.needs ++ [⟨effect,.iso,false⟩],application.meanings,CallName.sourceRows candidate ++ application.rows⟩)

structure BasisObligation (sources : Sources) where
  owner : String
  name : String
  offset : Nat
  state : GenericLexicalNatural.SomeEnvironment sources
  input : Code
  output : Code

structure ComputedPredicate (sources : Sources) where
  resolution : Resolved
  definition : Definition sources resolution.moduleName resolution.declaration.name
  original : definition.original.envelope.source = resolution.source ∧
    definition.original.envelope.declaration = resolution.declaration
  rows : List (String × String)

private def computedPredicate {sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (input : Code) (reference : SourceComputedSyntax.Reference) :
    WorkM (ComputedPredicate sources) := do
  let (resolution,rows) ← named state scope reference.argument.tokens
  let helpers : NaturalHelpers.Checked sources := ⟨state.prepared.helpers,state.prepared.helpersPrepared⟩
  let definition ← readDefinition sources resolution.moduleName resolution.declaration.name (some helpers)
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
  basisObligations : List (BasisObligation sources) := []
  computedObligations : List (ComputedObligation sources) := []
  rows : List (String × String) := []

def append {sources} (first last : Outcome sources) : Outcome sources :=
  {last with
    effect := join first.effect last.effect,quantumUse := first.quantumUse || last.quantumUse,
    references := first.references ++ last.references,needs := first.needs ++ last.needs,
    recursions := first.recursions ++ last.recursions,
    meanings := first.meanings ++ last.meanings,basisObligations := first.basisObligations ++ last.basisObligations,
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

private def selection {sources} (state : GenericLexicalNatural.SomeEnvironment sources) (scope : List String)
    (formals : List (String × Operation sources)) (parsed : QuantumMatch.Parsed)
    (selector target : Value) (remaining : Environment) : WorkM (Outcome sources) := do
  let [.owner selector] := selector | throw .request
  let [.owner target] := target | throw .request
  if parsed.keyword.text == "qif" then
    let _ ← SymbolicTypes.equate state selector [.fixed .bit]
  let labelBasis ← scalarLabelBasis state selector parsed.arms.length
  let arms ← parsed.arms.mapM fun arm => do
    let label ← QuantumLabels.read sources state.owner labelBasis arm.label
    let operation ← operation state scope formals 65 (some target) arm.operation
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

private def applyOperation {sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (formals : List (String × Operation sources)) (tokens : List LocatedToken)
    (arguments : List Value) (remaining : Environment) : WorkM (Outcome sources) := do
  let op ← operation state scope formals 65 none tokens
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
    needs := op.needs,meanings := op.meanings,rows := op.rows}

private def quantumGroup (value : Value) : Bool :=
  hasOwner value && value.all (fun atom => match atom with | .ordinary _ => false | _ => true)

private def runtimeTransform {sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (formals : List (String × Operation sources)) {tokens}
    (written : SourceRuntimeTransformSyntax.Checked tokens) (arguments : List Value) (remaining : Environment) :
    WorkM (Outcome sources) := do
  let base := written.base
  let candidate ← CallName.read sources state.owner scope base.2.callee
  let rows ← written.counts.mapM (fun count => validateCount state scope count.tokens)
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
    let application ← instantiate state scope base.2 resolution.moduleName resolution.declaration.name
      (operation state scope formals 65 none) true
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
    pure {
      value,remaining,effect := direct .unitary,quantumUse := true,references := application.references,
      recursions := application.recursion.toList,
      needs := application.needs ++ [⟨effect,.unitary,false⟩],meanings := application.meanings,
      rows := CallName.sourceRows candidate ++ rows.flatten ++ application.rows}

private def bindingNames (tokens : List LocatedToken) : WorkM (List String) := do
  let pattern ← adapt (QuantumMoves.parse 65 (tokens.map (·.text)))
  pure (pattern.filterMap fun atom => match atom with | .name name => some name | _ => none)

private def typedNominal {sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (basis : Semantics.FiniteCarrier.Basis) : WorkM Value := do
  let closed ← SymbolicTypes.ofClosed (StaticHeaders.frame state.prepared.original).binders.length basis
  adapt (GenericValues.ordinaryValue closed.code)

private def evaluator {sources owner name} (definition : Definition sources owner name) :
    Nat → GenericLexicalNatural.SomeEnvironment sources → List String → Environment →
    {tokens : List LocatedToken} → SourceSyntax.Tree tokens → WorkM (Outcome sources) :=
  Nat.rec (fun _ _ _ {_} _ => throw .limit) (fun _ next state scope environment {tokens} tree => do
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
      let leftEnvironment ← GenericLexicalNatural.underPredicate condition true
      let rightEnvironment ← GenericLexicalNatural.underPredicate condition false
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
      selection state scope definition.operations parsed selector target remaining
    | .selectionExpression _ parsed _ selector target =>
      let first ← next state scope environment selector
      let last ← next state scope first.remaining target
      let result ← selection state scope definition.operations parsed first.value last.value last.remaining
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
      let predicate ← computedPredicate state scope inputBasis written.parts.predicate
      let predicateEffect := functionEffect state.owner predicate.definition
      let (logical,initial,names,expected) ← match written.parts.logical,written.parts.data with
        | none,none =>
          pure (none,input.remaining.filter (fun cell => !hasOwner cell.value),
            [written.parts.auxiliary.text],[.owner [.fixed .bit]])
        | some reference,some data => do
          let logical ← operation state scope definition.operations 65 (some inputBasis) reference.argument.tokens
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
          let candidate ← CallName.read sources owner scope base.2.callee
          pure (match candidate.decision with | .lexical .. => false | _ => true)
      if transformedNamed then
        let some transformed := transformed | throw .request
        pure (append arguments (← runtimeTransform state scope definition.operations transformed values arguments.remaining))
      else if SourceOperationSyntax.selected (definition.operations.map (·.1)) call.call.callee then
        pure (append arguments (← applyOperation state scope definition.operations call.call.callee values arguments.remaining))
      else
        let written ← adapt (StaticApplication.readSyntax call.call.callee)
        let candidate ← CallName.read sources owner scope written.callee
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
          guard written.arguments.isEmpty .request
          let result ← primitive state kind values arguments.remaining
          pure (append arguments {result with rows := CallName.sourceRows candidate ++ result.rows})
        | _ =>
          let some resolution := CallName.candidateResolution candidate | throw .request
          let application ← instantiate state scope written resolution.moduleName resolution.declaration.name
            (operation state scope definition.operations 65 none) true
          guard (values.length == application.parameters.length) .request
          for (actual,expected) in values.zip application.parameters do GenericValues.expect state actual expected
          let externalPermission := owner != application.owner &&
            application.definition.original.envelope.parsedHeader.effect.isSome
          let result : Outcome sources := {
            value := application.result,remaining := arguments.remaining,
            effect := functionEffect owner application.definition,quantumUse := externalPermission,
            references := application.references,needs := application.needs,meanings := application.meanings,
            recursions := application.recursion.toList,
            rows := CallName.sourceRows candidate ++ application.rows}
          pure (append arguments result))

def checkTree {sources owner name} (definition : Definition sources owner name)
    (tree : SourceSyntax.Tree definition.original.envelope.occurrence.body) : WorkM (Outcome sources) := do
  let patterns ← adapt (ParameterPatterns.read definition.original.envelope)
  let initial ← adapt (GenericValues.seed patterns definition.parameters)
  let staticNames := definition.original.header.formals.map (·.name)
  guard (initial.all fun cell => !staticNames.contains cell.name) .request
  let result ← evaluator definition (definition.original.envelope.occurrence.body.length+1)
    definition.state (staticNames ++ initial.map (·.name)) initial tree
  guard (result.remaining.all fun cell => !hasOwner cell.value) .request
  GenericValues.expect definition.state result.value definition.result
  pure result

structure BodyRecord (sources : Sources) where
  owner : String
  name : String
  definition : Definition sources owner name
  tree : SourceSyntax.Tree definition.original.envelope.occurrence.body
  outcome : Outcome sources
  checked : ∃ before after,(checkTree definition tree).run before = (.ok outcome,after)

def BodyRecord.id {sources} (body : BodyRecord sources) : DefId := (body.owner,body.name)

def BodyRecord.entry {sources} (body : BodyRecord sources) : Entry := ⟨body.id,body.outcome.effect⟩

def BodyRecord.quantumDirect {sources} (body : BodyRecord sources) : Bool :=
  body.outcome.quantumUse || body.definition.parameters.any hasOwner || hasOwner body.definition.result ||
    !body.definition.operations.isEmpty

def readBody (sources : Sources) (owner name : String)
    (helpers : Option (NaturalHelpers.Checked sources) := none)
    (originals : Option (OrdinarySignature.Originals sources) := none) : WorkM (BodyRecord sources) := do
  let definition ← readDefinition sources owner name helpers originals
  let tokens := definition.original.envelope.occurrence.body
  let tree ← adapt (SourceSyntax.read (tokens.length+1) 0 true tokens)
  let result ← NaturalAffine.witness (checkTree definition tree)
  pure ⟨owner,name,definition,tree,result.val,by with_reducible exact result.property⟩

def discover (sources : Sources) (fuel : Nat) (pending : List DefId) (visited : List (BodyRecord sources))
    (helpers : Option (NaturalHelpers.Checked sources) := none)
    (originals : Option (OrdinarySignature.Originals sources) := none) : WorkM (List (BodyRecord sources)) :=
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
          let body ← readBody sources owner name helpers originals
          next (rest ++ body.outcome.references) (visited ++ [body])) fuel) pending visited

private def effectEntries {sources} (records : List (BodyRecord sources)) : List Entry := records.map (·.entry)

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

structure Inferred {sources} (records : List (BodyRecord sources)) (body : BodyRecord sources) where
  closure : SourceEffectClosure.Checked (effectEntries records) body.id
  effectBound : SourceEffect.permits body.definition.original.envelope.parsedHeader.effect closure.inferred = true
  classical : body.definition.original.envelope.parsedHeader.ordinaryOnly = true →
    closure.quantumUse (directQuantum records) = false
  publicPermission : body.definition.original.envelope.declaration.isPublic = true →
    closure.quantumUse (directQuantum records) = true → body.definition.original.envelope.parsedHeader.effect.isSome = true
  needs : ∃ before after,(checkNeeds records body.outcome.needs).run before = (.ok (),after)

def infer {sources} (records : List (BodyRecord sources)) (body : BodyRecord sources) : WorkM (Inferred records body) := do
  let closure ← SourceEffectClosure.read (effectEntries records) body.id
  if effectBound : SourceEffect.permits body.definition.original.envelope.parsedHeader.effect closure.inferred = true then
    if classical : body.definition.original.envelope.parsedHeader.ordinaryOnly = true →
        closure.quantumUse (directQuantum records) = false then
      if publicPermission : body.definition.original.envelope.declaration.isPublic = true →
          closure.quantumUse (directQuantum records) = true → body.definition.original.envelope.parsedHeader.effect.isSome = true then
        let needs ← NaturalAffine.witness (checkNeeds records body.outcome.needs)
        have unit : needs.val = () := by cases needs.val; rfl
        pure ⟨closure,effectBound,classical,publicPermission,
          by with_reducible simpa only [unit] using needs.property⟩
      else throw .request
    else throw .request
  else throw .request

inductive AllInferred {sources} (records : List (BodyRecord sources)) : List (BodyRecord sources) → Type where
  | nil : AllInferred records []
  | cons {body rest} (head : Inferred records body) (tail : AllInferred records rest) : AllInferred records (body :: rest)

def inferAll {sources} (records : List (BodyRecord sources)) :
    (pending : List (BodyRecord sources)) → WorkM (AllInferred records pending)
  | [] => pure .nil
  | body :: rest => do pure (.cons (← infer records body) (← inferAll records rest))

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
  ⟨owner,name,root.definition,originalTree root.definition root.sameOriginal tree,root.outcome,root.checked⟩

structure Checked {sources owner name} (original : OrdinarySignature.Original sources owner name) where
  tree : SourceSyntax.Tree original.occurrence.body
  root : Root original tree
  helpers : NaturalHelpers.Checked sources
  originals : Option (OrdinarySignature.Originals sources)
  records : List (BodyRecord sources)
  discovered : ∃ before after,
    (discover sources ((sources.toList.map fun row => row.2.utf8ByteSize+1).sum+1)
      root.outcome.references [root.record] (some helpers) originals).run before = (.ok records,after)
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
    (originals : Option (OrdinarySignature.Originals sources) := none) : WorkM (Checked original) := do
  match parsed : StaticHeaders.parse original.parsedHeader with
  | .error _ => throw .request
  | .ok header =>
    let header : StaticHeaders.Original sources owner name := ⟨original,header,parsed⟩
    let helpers ← match providedHelpers with | some helpers => pure helpers | none => NaturalHelpers.read sources
    let definition ← readDefinitionOriginal header (some helpers) originals
    have same : definition.val.original.envelope = original := congrArg (fun h => h.envelope) definition.property
    let result ← NaturalAffine.witness (checkTree definition.val (originalTree definition.val same tree))
    let root : Root original tree := ⟨definition.val,same,result.val,by with_reducible exact result.property⟩
    let records ← NaturalAffine.witness (discover sources ((sources.toList.map fun row => row.2.utf8ByteSize+1).sum+1)
      root.outcome.references [root.record] (some helpers) originals)
    checkCycles records.val
    let all ← inferAll records.val records.val
    let inferred ← infer records.val root.record
    pure ⟨tree,root,helpers,originals,records.val,by with_reducible exact records.property,all,inferred⟩

def readWithTree {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (tree : SourceSyntax.Tree original.occurrence.body) : WorkM (Checked original) :=
  match instantiation with
  | .closed _ => readOriginalWithTree original tree
  | .static _ environment _ =>
    readOriginalWithTree original tree (some ⟨environment.numeric.helpers,environment.numeric.helpersPrepared⟩)
      environment.numeric.originals

def readOriginal {sources owner name} (original : OrdinarySignature.Original sources owner name) : WorkM (Checked original) := do
  let tokens := original.occurrence.body
  let tree ← adapt (SourceSyntax.read (tokens.length+1) 0 true tokens)
  readOriginalWithTree original tree

def readWithInstantiation {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original) : WorkM (Checked original) := do
  let tokens := original.occurrence.body
  let tree ← adapt (SourceSyntax.read (tokens.length+1) 0 true tokens)
  readWithTree instantiation tree

end QleisliKernel.SourceTypes.GenericTypeTrace
