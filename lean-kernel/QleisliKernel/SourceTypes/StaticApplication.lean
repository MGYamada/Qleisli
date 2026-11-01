import QleisliKernel.SourceTypes.StaticInstantiation
import QleisliKernel.SourceTypes.LexicalNatural
import QleisliKernel.SourceTypes.StaticBindings
import QleisliKernel.SourceTypes.CallSyntax
import QleisliKernel.SourceTypes.CallName

/-! Complete positional actuals from original source applications. Each actual
retains its original formal ordinal/category and its original expression. Exact
Basis/Nat values are read under the caller's checked environment; these are
substitutions, never replacement declaration tokens or operation capabilities.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.StaticApplication
open Finite Semantics.FiniteCarrier

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

abbrev OperationReader := List LocatedToken → WorkM OperationDescription.Description

def noOperations : OperationReader := fun _ => throw .request

inductive Syntax (tokens : List LocatedToken) where
  | name (parsed : CallName.Name tokens)
  | application (parsed : CallSyntax.StaticChecked tokens)

def Syntax.callee {tokens} : Syntax tokens → List LocatedToken
  | .name _ => tokens
  | .application parsed => parsed.call.callee

def Syntax.arguments {tokens} : Syntax tokens → List CallSyntax.Argument
  | .name _ => []
  | .application parsed => parsed.call.arguments

def readSyntax (tokens : List LocatedToken) : Except String (Syntax tokens) := do
  if tokens.getLast?.map (·.text) == some "]" then
    return .application (← CallSyntax.readStatic tokens)
  else return .name (← CallName.readName tokens)

private def basisSyntax {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (tokens : List LocatedToken) (inner : List String) : Bool :=
  tokens.map (·.text) == ["type","("] ++ inner ++ [")"] ||
    (inner.length == 1 && tokens.map (·.text) == inner &&
      instantiation.arguments.bases.any (fun argument => inner == [argument.1]))

structure BasisExpression {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original) (tokens : List LocatedToken) where
  inner : List String
  parsed : basisSyntax instantiation tokens inner = true
  query : TypeRead sources
  read : ∃ before after,
    (StaticInstantiation.readType instantiation inner).run before = (.ok query,after)

def readBasis {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original) (tokens : List LocatedToken) :
    WorkM (BasisExpression instantiation tokens) := do
  let texts := tokens.map (·.text)
  let inner := if texts.take 2 == ["type","("] then texts.drop 2 |>.dropLast else texts
  if parsed : basisSyntax instantiation tokens inner = true then
    let query ← NaturalAffine.witness (StaticInstantiation.readType instantiation inner)
    return ⟨inner,parsed,query.val,by with_reducible exact query.property⟩
  else throw .request

inductive Value {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (operationReader : OperationReader) (tokens : List LocatedToken) : StaticHeaders.Kind → Type where
  | basis (expression : BasisExpression instantiation tokens) :
      Value instantiation entries environment scope operationReader tokens .basis
  | natural (expression : StaticBindings.Natural tokens)
      (checked : LexicalNatural.Checked sources owner entries environment scope expression.expression) :
      Value instantiation entries environment scope operationReader tokens .natural
  | operation (description : OperationDescription.Description) (kindTokens : List String)
      (read : ∃ before after, (operationReader tokens).run before = (.ok description,after)) :
      Value instantiation entries environment scope operationReader tokens (.operation kindTokens)

structure Actual {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (operationReader : OperationReader) where
  formal : StaticHeaders.Formal
  argument : CallSyntax.Argument
  value : Value instantiation entries environment scope operationReader argument.tokens formal.kind

def Value.bases {sources owner name original instantiation entries environment scope operationReader tokens kind}
    (value : @Value sources owner name original instantiation entries environment scope operationReader tokens kind) : List Basis :=
  match value with
  | .basis expression => [expression.query.basis]
  | .natural .. => []
  | .operation .. => []

def Value.naturals {sources owner name original instantiation entries environment scope operationReader tokens kind}
    (value : @Value sources owner name original instantiation entries environment scope operationReader tokens kind) : List Nat :=
  match value with
  | .basis .. => []
  | .natural _ checked => [checked.result.value]
  | .operation .. => []

def Value.operations {sources owner name original instantiation entries environment scope operationReader tokens kind}
    (value : @Value sources owner name original instantiation entries environment scope operationReader tokens kind) :
    List OperationDescription.Description :=
  match value with
  | .basis .. | .natural .. => []
  | .operation description _ _ => [description]

def Value.sourceRows {sources owner name original instantiation entries environment scope operationReader tokens kind}
    (value : @Value sources owner name original instantiation entries environment scope operationReader tokens kind) : List (String × String) :=
  match value with
  | .basis expression => expression.query.sourceRows
  | .natural .. => []
  | .operation .. => []

def Actual.bases {sources owner name original instantiation entries environment scope operationReader}
    (actual : @Actual sources owner name original instantiation entries environment scope operationReader) : List (String × Basis) :=
  actual.value.bases.map (actual.formal.name,·)

def Actual.naturals {sources owner name original instantiation entries environment scope operationReader}
    (actual : @Actual sources owner name original instantiation entries environment scope operationReader) : List (String × Nat) :=
  actual.value.naturals.map (actual.formal.name,·)

def Actual.operations {sources owner name original instantiation entries environment scope operationReader}
    (actual : @Actual sources owner name original instantiation entries environment scope operationReader) :
    List (String × OperationDescription.Description) :=
  actual.value.operations.map (actual.formal.name,·)

def Actual.sourceRows {sources owner name original instantiation entries environment scope operationReader}
    (actual : @Actual sources owner name original instantiation entries environment scope operationReader) : List (String × String) :=
  actual.value.sourceRows

private def readActual {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (operationReader : OperationReader)
    (formal : StaticHeaders.Formal) (argument : CallSyntax.Argument) :
    WorkM (Actual instantiation entries environment scope operationReader) := do
  match kind : formal.kind with
  | .basis =>
    let expression ← readBasis instantiation argument.tokens
    return ⟨formal,argument,by rw [kind]; exact .basis expression⟩
  | .natural =>
    let expression ← adapt (StaticBindings.natural argument.tokens)
    let checked ← LexicalNatural.read sources owner entries environment scope expression.expression
    return ⟨formal,argument,by rw [kind]; exact .natural expression checked⟩
  | .operation tokens =>
    let description ← NaturalAffine.witness (operationReader argument.tokens)
    return ⟨formal,argument,by
      rw [kind]
      exact .operation description.val tokens (by with_reducible exact description.property)⟩

structure Checked {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (operationReader : OperationReader) {tokens : List LocatedToken} (written : Syntax tokens)
    (targetOwner targetName : String) where
  target : StaticHeaders.Original sources targetOwner targetName
  actuals : List (Actual instantiation entries environment scope operationReader)
  complete : target.header.formals.length = written.arguments.length
  ordered : actuals.map (fun actual => (actual.formal,actual.argument)) =
    target.header.formals.zip written.arguments

def Checked.arguments {sources owner name original instantiation entries environment scope operationReader tokens written targetOwner targetName}
    (checked : @Checked sources owner name original instantiation entries environment scope operationReader tokens written targetOwner targetName) :
    StaticTypes.Arguments :=
  {bases := checked.actuals.flatMap Actual.bases,naturals := checked.actuals.flatMap Actual.naturals,
    operations := checked.actuals.flatMap Actual.operations}

def read {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) {tokens : List LocatedToken} (written : Syntax tokens)
    (targetOwner targetName : String) (operationReader : OperationReader := noOperations) :
    WorkM (Checked instantiation entries environment scope operationReader written targetOwner targetName) := do
  let target ← StaticHeaders.read sources targetOwner targetName
  guard (written.arguments.length ≤ 32) .limit
  exactWork (Exact.charge (64*(tokens.length+1)*(target.header.formals.length+1)))
  if complete : target.header.formals.length = written.arguments.length then
    let actuals ← (target.header.formals.zip written.arguments).mapM fun (formal,argument) =>
      readActual instantiation entries environment scope operationReader formal argument
    if ordered : actuals.map (fun actual => (actual.formal,actual.argument)) =
        target.header.formals.zip written.arguments then
      return ⟨target,actuals,complete,ordered⟩
    else throw .request
  else throw .request

end QleisliKernel.SourceTypes.StaticApplication
