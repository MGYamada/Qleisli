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

def countValue {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources))
    (tokens : List LocatedToken) : WorkM Nat :=
  count sources caller entries environment scope
    (StaticApplication.validateNatural instantiation genericState scope) tokens

def countRows (sources : Sources) (caller : String) (entries : List NaturalHelpers.Entry)
    (scope : List String) (tokens : List LocatedToken) : WorkM (List (String × String)) := do
  let texts := if (tokens.take 2).map (·.text) == ["2","^"] then tokens.drop 2 else tokens
  let expression ← adapt (StaticBindings.natural texts)
  NaturalRows.expression sources caller entries scope expression.expression

structure Count {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken) where
  value : Nat
  genericState : Option (GenericLexicalNatural.SomeEnvironment sources)
  original : ∃ before after,
    (countValue instantiation entries environment scope genericState tokens).run before = (.ok value,after)
  rows : List (String × String)
  rowsRead : ∃ before after,(countRows sources caller entries scope tokens).run before = (.ok rows,after)

/-- Shared original count reader for static descriptions and direct runtime
group transforms. Zero counts still retain their original syntax/helper rows;
operand traversal and requested access remain the enclosing rule's duties. -/
def readCount {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken)
    (genericState : Option (GenericLexicalNatural.SomeEnvironment sources) := none) :
    WorkM (Count instantiation entries environment scope tokens) := do
  let value ← NaturalAffine.witness (countValue instantiation entries environment scope genericState tokens)
  let rows ← NaturalAffine.witness (countRows sources caller entries scope tokens)
  pure ⟨value.val,genericState,by with_reducible exact value.property,rows.val,by with_reducible exact rows.property⟩

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
          let count ← countValue instantiation entries environment scope genericState amount.tokens
          return child.unary (fun index => .power index count)
        | "then_op",[left,right] => return Description.binary .thenOp (← next left.tokens) (← next right.tokens)
        | "tensor_op",[left,right] => return Description.binary .tensor (← next left.tokens) (← next right.tokens)
        | "conjugate_op",[outer,middle] =>
          return Description.binary .conjugate (← next outer.tokens) (← next middle.tokens)
        | "checked_op",[child,meaning] =>
          let _ ← adapt (CallName.readName child.tokens)
          let child ← next child.tokens
          let selected ← SourceMeaning.selectName sources caller scope (meaning.tokens.map (·.text))
          return child.unary (fun index => .requested index selected.resolution.moduleName selected.resolution.declaration.name)
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

def primitiveKind {sources caller scope tokens}
    (candidate : CallName.Checked sources caller scope tokens) : Option OperationDescription.Primitive :=
  match candidate.decision with
  | .primitive _ _ _ _ _ _ .h _ => some .h
  | .primitive _ _ _ _ _ _ .globalPhaseEighth _ => some .globalPhaseEighth
  | _ => none

/-- Existing direct runtime adjoint/control accepts sealed unary gates using
the actual complete target type. Static provider arguments and nested static
constructor leaves do not gain this contextual exception. -/
private def runtimePrimitive (sources : Sources) (caller : String) (scope : List String)
    (target : Semantics.FiniteCarrier.Basis) (tokens : List LocatedToken) :
    WorkM (Option (Description × List (String × String))) := do
  match CallSyntax.read tokens with
  | .error _ => pure none
  | .ok call =>
    match call.call.callee.map (·.text),call.call.arguments with
    | [constructor],[argument] =>
      if constructor != "adjoint" && constructor != "controlled" then pure none else
        match CallName.readName argument.tokens with
        | .error _ => pure none
        | .ok _ => do
          let candidate ← CallName.read sources caller scope argument.tokens
          match primitiveKind candidate with
          | none => pure none
          | some kind =>
            guard (kind == .globalPhaseEighth || target == [.bit]) .request
            let child : Description := ⟨[.primitive kind target],0⟩
            let description := if constructor == "adjoint" then child.unary .inverse else child.unary .controlled
            pure (some (description,CallName.sourceRows candidate))
    | _,_ => pure none

def proposalWithInstantiation {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources))
    (target : Option Semantics.FiniteCarrier.Basis) (tokens : List LocatedToken) : WorkM Description := do
  let primitive ← match target with
    | none => pure none
    | some basis => runtimePrimitive sources caller scope basis tokens
  match primitive with
  | some (description,_) => pure description
  | none => buildWithInstantiation instantiation entries environment scope genericState 65 tokens

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
      | "checked_op",[child,meaning] =>
        let _ ← adapt (CallName.readName child.tokens)
        let selected ← SourceMeaning.selectName sources caller scope (meaning.tokens.map (·.text))
        return (← next child.tokens) ++ selected.queryRows
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

def proposalRowsWithInstantiation {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources))
    (target : Option Semantics.FiniteCarrier.Basis) (tokens : List LocatedToken) : WorkM (List (String × String)) := do
  let primitive ← match target with
    | none => pure none
    | some basis => runtimePrimitive sources caller scope basis tokens
  match primitive with
  | some (_,rows) => pure rows
  | none => readRowsWithInstantiation instantiation entries environment scope genericState 65 tokens

structure CheckedWithInstantiation {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken) where
  description : Description
  genericState : Option (GenericLexicalNatural.SomeEnvironment sources)
  target : Option Semantics.FiniteCarrier.Basis
  supply : Option (StaticOperation.Supply instantiation)
  original : ∃ before after,
    (proposalWithInstantiation instantiation entries environment scope genericState target tokens).run before = (.ok description,after)
  graph : StaticOperation.CheckedGraph sources (.source caller) description
  rows : List (String × String)
  rowsRead : ∃ before after,
    (proposalRowsWithInstantiation instantiation entries environment scope genericState target tokens).run before = (.ok rows,after)

def readWithInstantiation {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken)
    (genericState : Option (GenericLexicalNatural.SomeEnvironment sources) := none)
    (target : Option Semantics.FiniteCarrier.Basis := none)
    (supply : Option (StaticOperation.Supply instantiation) := none) :
    WorkM (CheckedWithInstantiation instantiation entries environment scope tokens) := do
  let description ← NaturalAffine.witness (proposalWithInstantiation instantiation entries environment scope genericState target tokens)
  let graph ← match supply with
    | none => StaticOperation.check sources (.source caller) description.val
    | some supply => StaticOperation.checkWithSupply supply description.val
  let rows ← NaturalAffine.witness (proposalRowsWithInstantiation instantiation entries environment scope genericState target tokens)
  pure ⟨description.val,genericState,target,supply,by with_reducible exact description.property,graph,rows.val,
    by with_reducible exact rows.property⟩

abbrev Checked {sources caller callerName} (signature : QuantumSignatureCore.Checked sources caller callerName)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken) :=
  CheckedWithInstantiation signature.instantiation entries environment scope tokens

def read {sources caller callerName} (signature : QuantumSignatureCore.Checked sources caller callerName)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken)
    (genericState : Option (GenericLexicalNatural.SomeEnvironment sources) := none)
    (target : Option Semantics.FiniteCarrier.Basis := none)
    (supply : Option (StaticOperation.Supply signature.instantiation) := none) :
    WorkM (Checked signature entries environment scope tokens) :=
  readWithInstantiation signature.instantiation entries environment scope tokens genericState target supply

def readApplicationActuals {sources caller callerName original entries environment scope operationReader tokens written targetOwner targetName}
    {instantiation : @StaticInstantiation.Checked sources caller callerName original}
    (application : @StaticApplication.Checked sources caller callerName original instantiation entries environment scope
      operationReader tokens written targetOwner targetName)
    (supply : StaticOperation.Supply instantiation) :
    WorkM (List (Sigma (StaticOperation.Actual sources (.source caller))) × List (String × String)) := do
  let read ← application.actuals.mapM fun actual => do
    match actual.operations with
    | [] => pure ([],[])
    | [(name,description)] =>
      let checked ← readWithInstantiation instantiation entries environment scope actual.argument.tokens
        application.genericState none (some supply)
      guard (checked.description == description) .request
      let actual : Sigma (StaticOperation.Actual sources (.source caller)) :=
        ⟨(name,checked.description),⟨checked.graph⟩⟩
      pure ([actual],checked.rows)
    | _ => throw .request
  pure (read.flatMap (·.1),read.flatMap (·.2))

/-- Original application tokens authenticate these graph receipts and routes;
the callee's original binding check independently verifies all exact ports,
access demands and Meaning requirements. -/
structure ApplicationActuals {sources caller callerName original entries environment scope operationReader tokens written targetOwner targetName}
    {instantiation : @StaticInstantiation.Checked sources caller callerName original}
    (application : @StaticApplication.Checked sources caller callerName original instantiation entries environment scope
      operationReader tokens written targetOwner targetName)
    (supply : StaticOperation.Supply instantiation) where
  actuals : List (Sigma (StaticOperation.Actual sources (.source caller)))
  rows : List (String × String)
  original : ∃ before after,(readApplicationActuals application supply).run before = (.ok (actuals,rows),after)

def checkApplicationActuals {sources caller callerName original entries environment scope operationReader tokens written targetOwner targetName}
    {instantiation : @StaticInstantiation.Checked sources caller callerName original}
    (application : @StaticApplication.Checked sources caller callerName original instantiation entries environment scope
      operationReader tokens written targetOwner targetName)
    (supply : StaticOperation.Supply instantiation) : WorkM (ApplicationActuals application supply) := do
  let checked ← NaturalAffine.witness (readApplicationActuals application supply)
  pure ⟨checked.val.1,checked.val.2,by with_reducible exact checked.property⟩

end QleisliKernel.SourceTypes.SourceOperation
