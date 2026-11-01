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
    (tokens : List LocatedToken) : WorkM Nat := do
  if (tokens.take 2).map (·.text) == ["2","^"] then
    let expression ← adapt (StaticBindings.natural (tokens.drop 2))
    let exponent ← LexicalNatural.read sources caller entries environment scope expression.expression
    guard (exponent.result.value ≤ 31) .limit
    pure (2^exponent.result.value)
  else
    let expression ← adapt (StaticBindings.natural tokens)
    pure (← LexicalNatural.read sources caller entries environment scope expression.expression).result.value

/-- Every constructor child is visited before its graph is assembled, including
zero-power children and unused actuals of a provider. The same callback handles
operation arguments recursively; it is never a producer-supplied path flag. -/
def build {sources caller callerName}
    (signature : QuantumSignatureCore.Checked sources caller callerName)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) : Nat → List LocatedToken → WorkM Description :=
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
          let count ← count sources caller entries environment scope amount.tokens
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
          match signature.instantiation with
          | .closed _ => throw .request
          | .static arguments staticEnvironment _ =>
            let some formal := staticEnvironment.numeric.original.header.formals.find? (·.name == name)
              | throw .request
            let .operation _ := formal.kind | throw .request
            pure (OperationDescription.formal caller callerName arguments.bases arguments.naturals
              arguments.operations formal.ordinal)
        | _ =>
          let some resolution := candidateResolution candidate | throw .request
          let actuals ← StaticApplication.read signature.instantiation entries environment scope written
            resolution.moduleName resolution.declaration.name next
          pure (OperationDescription.provider resolution.moduleName resolution.declaration.name
            actuals.arguments.bases actuals.arguments.naturals actuals.arguments.operations)
    guard (description.nodes.length ≤ 4096) .limit
    exactWork (Exact.charge (16*(description.nodes.length+1)^2))
    guard description.complete .request
    pure description)

structure Checked {sources caller callerName}
    (signature : QuantumSignatureCore.Checked sources caller callerName)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken) where
  description : Description
  original : ∃ before after,
    (build signature entries environment scope 65 tokens).run before = (.ok description,after)
  graph : StaticOperation.CheckedGraph sources (.source caller) description

def read {sources caller callerName}
    (signature : QuantumSignatureCore.Checked sources caller callerName)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken) :
    WorkM (Checked signature entries environment scope tokens) := do
  let description ← NaturalAffine.witness (build signature entries environment scope 65 tokens)
  let graph ← StaticOperation.check sources (.source caller) description.val
  pure ⟨description.val,by with_reducible exact description.property,graph⟩

end QleisliKernel.SourceTypes.SourceOperation
