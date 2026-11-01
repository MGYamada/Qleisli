import QleisliKernel.SourceTypes.StaticOperation
import QleisliKernel.SourceTypes.StaticApplication

/-! Original static operation-expression transfer. Constructor syntax, counts,
formal ordinals and all provider actuals produce a retained descriptor which is
independently checked. No wrapper source declaration or closed AST is invented.
Body/control equations remain mandatory at the enclosing native source gate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceOperation
open Finite OperationDescription

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

private def candidateResolution {sources caller scope tokens}
    (candidate : CallName.Checked sources caller scope tokens) : Option Resolved :=
  match candidate.decision with
  | .named resolution | .prelude _ _ _ _ _ _ _ _ resolution => some resolution.result
  | _ => none

private def count (sources : Sources) (caller : String) (entries : List NaturalHelpers.Entry)
    (environment : LexicalNatural.Environment entries) (scope : List String)
    (validate : Semantics.SourceNatural.Expr → WorkM Unit)
    (tokens : List LocatedToken) : WorkM Nat := do
  if (tokens.take 2).map (·.text) == ["2","^"] then
    let expression ← adapt (StaticBindings.natural (tokens.drop 2))
    validate expression.expression
    let exponent ← LexicalNatural.read sources caller entries environment scope expression.expression
    guard (exponent.result.value ≤ 31) .limit
    pure (2^exponent.result.value)
  else
    let expression ← adapt (StaticBindings.natural tokens)
    validate expression.expression
    pure (← LexicalNatural.read sources caller entries environment scope expression.expression).result.value

/-- Every constructor child is visited before its graph is assembled, including
zero-power children and unused actuals of a provider. The same callback handles
operation arguments recursively; it is never a producer-supplied path flag. -/
def buildWithInstantiation {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources)) :
    Nat → List LocatedToken → WorkM Description :=
  Nat.rec (fun _ => throw .limit) (fun _ next tokens => do
    let bytes := (sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
    exactWork (Exact.charge (32*(bytes+(tokens.map fun token => token.text.utf8ByteSize+4).sum+1)))
    let description ← if tokens.getLast?.map (·.text) == some ")" then do
        let call ← adapt (CallSyntax.read tokens)
        let [constructor] := call.call.callee.map (·.text) | throw .request
        match constructor,call.call.arguments with
        | "adjoint",[child] => return (← next child.tokens).unary .inverse
        | "controlled",[child] => return (← next child.tokens).unary .controlled
        | "power",[child,amount] =>
          let child ← next child.tokens
          let count ← count sources caller entries environment scope
            (StaticApplication.validateNatural instantiation genericState scope) amount.tokens
          return child.unary (fun index => .power index count)
        | "then_op",[left,right] => return Description.binary .thenOp (← next left.tokens) (← next right.tokens)
        | "tensor_op",[left,right] => return Description.binary .tensor (← next left.tokens) (← next right.tokens)
        | "conjugate_op",[outer,middle] =>
          return Description.binary .conjugate (← next outer.tokens) (← next middle.tokens)
        | _,_ => throw .request
      else do
        let written ← adapt (StaticApplication.readSyntax tokens)
        let candidate ← CallName.read sources caller scope written.callee
        match candidate.decision with
        | .lexical name _ _ =>
          guard written.arguments.isEmpty .request
          match instantiation with
          | .closed _ => throw .request
          | .static arguments staticEnvironment _ =>
            let some formal := staticEnvironment.numeric.original.header.formals.find? (·.name == name)
              | throw .request
            let .operation _ := formal.kind | throw .request
            pure (OperationDescription.formal caller callerName arguments.bases arguments.naturals
              arguments.operations formal.ordinal)
        | _ =>
          let some resolution := candidateResolution candidate | throw .request
          let actuals ← StaticApplication.read instantiation entries environment scope written
            resolution.moduleName resolution.declaration.name next genericState
          pure (OperationDescription.provider resolution.moduleName resolution.declaration.name
            actuals.arguments.bases actuals.arguments.naturals actuals.arguments.operations)
    guard (description.nodes.length ≤ 4096) .limit
    exactWork (Exact.charge (16*(description.nodes.length+1)^2))
    guard description.complete .request
    pure description)

def buildWithGeneric {sources caller callerName}
    (signature : QuantumSignatureCore.Checked sources caller callerName)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources)) :
    Nat → List LocatedToken → WorkM Description :=
  buildWithInstantiation signature.instantiation entries environment scope genericState

def build {sources caller callerName}
    (signature : QuantumSignatureCore.Checked sources caller callerName)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) : Nat → List LocatedToken → WorkM Description :=
  buildWithGeneric signature entries environment scope none

/-- Retain exact source lookup and type-actual routes in addition to the
canonical descriptor. Reexports used only to select a provider or an unused
Basis actual remain relevant; canonical names alone cannot cover those rows. -/
def readRowsWithInstantiation {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources)) :
    Nat → List LocatedToken → WorkM (List (String × String)) :=
  Nat.rec (fun _ => throw .limit) (fun _ next tokens => do
    let bytes := (sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
    exactWork (Exact.charge (32*(bytes+(tokens.map fun token => token.text.utf8ByteSize+4).sum+1)))
    if tokens.getLast?.map (·.text) == some ")" then
      let call ← adapt (CallSyntax.read tokens)
      let [constructor] := call.call.callee.map (·.text) | throw .request
      match constructor,call.call.arguments with
      | "adjoint",[child] | "controlled",[child] | "power",[child,_] => next child.tokens
      | "then_op",[left,right] | "tensor_op",[left,right] | "conjugate_op",[left,right] =>
        return (← next left.tokens) ++ (← next right.tokens)
      | _,_ => throw .request
    else
      let written ← adapt (StaticApplication.readSyntax tokens)
      let candidate ← CallName.read sources caller scope written.callee
      match candidate.decision with
      | .lexical .. => pure (CallName.sourceRows candidate)
      | _ =>
        let some resolution := candidateResolution candidate | throw .request
        let actuals ← StaticApplication.read instantiation entries environment scope written
          resolution.moduleName resolution.declaration.name
          (buildWithInstantiation instantiation entries environment scope genericState 65) genericState
        let children ← actuals.actuals.mapM fun actual => do
          match actual.formal.kind with
          | .operation _ => next actual.argument.tokens
          | _ => pure []
        return CallName.sourceRows candidate ++ actuals.actuals.flatMap StaticApplication.Actual.sourceRows ++ children.flatten)

structure CheckedWithInstantiation {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken) where
  description : Description
  genericState : Option (GenericLexicalNatural.SomeEnvironment sources)
  original : ∃ before after,
    (buildWithInstantiation instantiation entries environment scope genericState 65 tokens).run before = (.ok description,after)
  graph : StaticOperation.CheckedGraph sources (.source caller) description
  rows : List (String × String)
  rowsRead : ∃ before after,
    (readRowsWithInstantiation instantiation entries environment scope genericState 65 tokens).run before = (.ok rows,after)

def readWithInstantiation {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken)
    (genericState : Option (GenericLexicalNatural.SomeEnvironment sources) := none) :
    WorkM (CheckedWithInstantiation instantiation entries environment scope tokens) := do
  let description ← NaturalAffine.witness (buildWithInstantiation instantiation entries environment scope genericState 65 tokens)
  let graph ← StaticOperation.check sources (.source caller) description.val
  let rows ← NaturalAffine.witness (readRowsWithInstantiation instantiation entries environment scope genericState 65 tokens)
  pure ⟨description.val,genericState,by with_reducible exact description.property,graph,rows.val,
    by with_reducible exact rows.property⟩

abbrev Checked {sources caller callerName} (signature : QuantumSignatureCore.Checked sources caller callerName)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken) :=
  CheckedWithInstantiation signature.instantiation entries environment scope tokens

def read {sources caller callerName} (signature : QuantumSignatureCore.Checked sources caller callerName)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken)
    (genericState : Option (GenericLexicalNatural.SomeEnvironment sources) := none) :
    WorkM (Checked signature entries environment scope tokens) :=
  readWithInstantiation signature.instantiation entries environment scope tokens genericState

end QleisliKernel.SourceTypes.SourceOperation
