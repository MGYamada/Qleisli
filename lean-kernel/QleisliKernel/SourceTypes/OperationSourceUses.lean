import QleisliKernel.SourceTypes.SourceOperation

/-! Located formal uses inside original operation expressions. Constructor
children and provider actuals use the same parser and edge convention as
SourceOperation. Each path retains its original parsed slices; a formal's
header identity never replaces its distinct use-site tokens. This reader
supplies no native occurrence, supplier transport or operation equation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.OperationSourceUses
open Finite
open QleisliKernel.Semantics.SymbolicBasis (Parameter)

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

/-- Constructor argument order is the source descriptor's child-edge order.
The count and Meaning arguments remain original arguments, not extra children. -/
inductive Shape (call : CallSyntax.Call) where
  | inverse (child : CallSyntax.Argument)
      (callee : call.callee.map (·.text) = ["adjoint"])
      (arguments : call.arguments = [child])
  | controlled (child : CallSyntax.Argument)
      (callee : call.callee.map (·.text) = ["controlled"])
      (arguments : call.arguments = [child])
  | power (child amount : CallSyntax.Argument)
      (callee : call.callee.map (·.text) = ["power"])
      (arguments : call.arguments = [child,amount])
  | thenOp (left right : CallSyntax.Argument)
      (callee : call.callee.map (·.text) = ["then_op"])
      (arguments : call.arguments = [left,right])
  | tensor (left right : CallSyntax.Argument)
      (callee : call.callee.map (·.text) = ["tensor_op"])
      (arguments : call.arguments = [left,right])
  | conjugate (outer middle : CallSyntax.Argument)
      (callee : call.callee.map (·.text) = ["conjugate_op"])
      (arguments : call.arguments = [outer,middle])
  | requested (child meaning : CallSyntax.Argument)
      (callee : call.callee.map (·.text) = ["checked_op"])
      (arguments : call.arguments = [child,meaning])
      (childName : CallName.Name child.tokens)

def Shape.children {call} : Shape call → List CallSyntax.Argument
  | .inverse child .. | .controlled child .. | .power child ..
      | .requested child .. => [child]
  | .thenOp left right .. | .tensor left right ..
      | .conjugate left right .. => [left,right]

structure Compound (tokens : List LocatedToken) where
  parsed : CallSyntax.Checked tokens
  shape : Shape parsed.call

def readCompound (tokens : List LocatedToken) : Except String (Compound tokens) := do
  let parsed ← CallSyntax.read tokens
  match callee : parsed.call.callee.map (·.text),arguments : parsed.call.arguments with
  | ["adjoint"],[child] => pure ⟨parsed,.inverse child callee arguments⟩
  | ["controlled"],[child] => pure ⟨parsed,.controlled child callee arguments⟩
  | ["power"],[child,amount] => pure ⟨parsed,.power child amount callee arguments⟩
  | ["then_op"],[left,right] => pure ⟨parsed,.thenOp left right callee arguments⟩
  | ["tensor_op"],[left,right] => pure ⟨parsed,.tensor left right callee arguments⟩
  | ["conjugate_op"],[outer,middle] => pure ⟨parsed,.conjugate outer middle callee arguments⟩
  | ["checked_op"],[child,meaning] =>
    pure ⟨parsed,.requested child meaning callee arguments (← CallName.readName child.tokens)⟩
  | _,_ => throw "unsupported original operation constructor"

structure Child (tokens : List LocatedToken) (ordinal : Nat) (childTokens : List LocatedToken) where
  compound : Compound tokens
  argument : CallSyntax.Argument
  selected : compound.shape.children[ordinal]? = some argument
  original : argument.tokens = childTokens

/-- The original supplying header is shared from the actual instantiation.
Lexical resolution and the full use-site expression remain separate fields. -/
structure Formal {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (scope : List String) (tokens : List LocatedToken) where
  written : StaticApplication.Syntax tokens
  candidate : CallName.Checked sources caller scope written.callee
  candidateRead : ∃ before after,
    (CallName.read sources caller scope written.callee).run before = (.ok candidate,after)
  name : String
  spelling : written.callee.map (·.text) = [name]
  bound : name ∈ scope
  lexical : candidate.decision = .lexical name spelling bound
  noArguments : written.arguments = []
  header : StaticHeaders.Original sources caller callerName
  sameOriginal : header.envelope = original
  headerFormal : StaticHeaders.Formal
  selected : header.header.formals.find? (·.name == name) = some headerFormal
  sameName : headerFormal.name = name
  kindTokens : List String
  operation : headerFormal.kind = .operation kindTokens

def Formal.key {sources caller callerName original instantiation scope tokens}
    (formal : @Formal sources caller callerName original instantiation scope tokens) : Parameter :=
  ⟨caller,callerName,formal.headerFormal.ordinal⟩

/-- This is the same operation-argument callback used by the original builder.
It validates every actual while the source-use traversal preserves its slices. -/
def operationReader {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources)) :
    StaticApplication.OperationReader :=
  SourceOperation.buildWithInstantiation instantiation entries environment scope genericState 65

structure Actual {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources))
    (tokens : List LocatedToken) (mixedOrdinal : Nat) (childTokens : List LocatedToken) where
  written : StaticApplication.Syntax tokens
  candidate : CallName.Checked sources caller scope written.callee
  candidateRead : ∃ before after,
    (CallName.read sources caller scope written.callee).run before = (.ok candidate,after)
  target : Resolved
  resolved : CallName.candidateResolution candidate = some target
  application : StaticApplication.Checked instantiation entries environment scope
    (operationReader instantiation entries environment scope genericState) written
    target.moduleName target.declaration.name
  applicationRead : ∃ before after,
    (StaticApplication.read instantiation entries environment scope written target.moduleName
      target.declaration.name (operationReader instantiation entries environment scope genericState)
      genericState).run before = (.ok application,after)
  index : Fin application.actuals.length
  actual : StaticApplication.Actual instantiation entries environment scope
    (operationReader instantiation entries environment scope genericState)
  atIndex : application.actuals[index.val]? = some actual
  mixed : actual.formal.ordinal = mixedOrdinal
  kindTokens : List String
  operation : actual.formal.kind = .operation kindTokens
  original : actual.argument.tokens = childTokens

/-- Each edge retains the actual parser-selected child, including a provider's
original mixed ordinal. Paths distinguish repeated uses of the same formal. -/
inductive Path {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources)) :
    List LocatedToken → List SourceOperation.Edge → List LocatedToken → Type where
  | here {tokens} : Path instantiation entries environment scope genericState tokens [] tokens
  | child {tokens ordinal childTokens rest selectedTokens}
      (step : Child tokens ordinal childTokens)
      (tail : Path instantiation entries environment scope genericState childTokens rest selectedTokens) :
      Path instantiation entries environment scope genericState tokens (.child ordinal :: rest) selectedTokens
  | actual {tokens mixedOrdinal childTokens rest selectedTokens}
      (step : Actual instantiation entries environment scope genericState tokens mixedOrdinal childTokens)
      (tail : Path instantiation entries environment scope genericState childTokens rest selectedTokens) :
      Path instantiation entries environment scope genericState tokens (.actual mixedOrdinal :: rest) selectedTokens

structure Use {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources))
    (rootTokens : List LocatedToken) where
  path : List SourceOperation.Edge
  tokens : List LocatedToken
  located : Path instantiation entries environment scope genericState rootTokens path tokens
  formal : Formal instantiation scope tokens

def Use.underChild {sources caller callerName original instantiation entries environment scope genericState
    tokens ordinal childTokens}
    (step : Child tokens ordinal childTokens)
    (use : @Use sources caller callerName original instantiation entries environment scope genericState childTokens) :
    Use instantiation entries environment scope genericState tokens :=
  ⟨.child ordinal :: use.path,use.tokens,.child step use.located,use.formal⟩

def Use.underActual {sources caller callerName original instantiation entries environment scope genericState
    tokens mixedOrdinal childTokens}
    (step : Actual instantiation entries environment scope genericState tokens mixedOrdinal childTokens)
    (use : @Use sources caller callerName original instantiation entries environment scope genericState childTokens) :
    Use instantiation entries environment scope genericState tokens :=
  ⟨.actual mixedOrdinal :: use.path,use.tokens,.actual step use.located,use.formal⟩

private def tokenFields (tokens : List LocatedToken) : Nat :=
  tokens.foldl (fun fields token => fields + token.text.utf8ByteSize + 8) 0

/-- Follow all constructor edges and all Op actuals in original order. The
existing builder's 65-step depth is reused; no zero count erases its child. -/
def readUses {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources)) :
    Nat → (tokens : List LocatedToken) → WorkM (List (Use instantiation entries environment scope genericState tokens)) :=
  Nat.rec (fun _ => throw .limit) (fun _ next tokens => do
    -- The balanced parser traverses token and delimiter lists. Pay for that
    -- work and text comparisons before reading this particular expression.
    exactWork (Exact.charge (16*(tokens.length+1)*(tokenFields tokens+1)))
    if tokens.getLast?.map (·.text) == some ")" then
      let compound ← adapt (readCompound tokens)
      exactWork (Exact.charge (16*(compound.shape.children.length+1)^2))
      let groups ← (List.finRange compound.shape.children.length).mapM
          fun (index : Fin compound.shape.children.length) => do
        let argument : CallSyntax.Argument := compound.shape.children[index.val]'index.isLt
        let uses ← next argument.tokens
        exactWork (Exact.charge (8*(uses.length+1)))
        let step : Child tokens index.val argument.tokens :=
          ⟨compound,argument,List.getElem?_eq_getElem index.isLt,rfl⟩
        pure (uses.map (Use.underChild step))
      exactWork (Exact.charge (8*((groups.map (·.length)).sum+groups.length+1)))
      pure groups.flatten
    else
      let written ← adapt (StaticApplication.readSyntax tokens)
      let candidate ← NaturalAffine.witness (CallName.read sources caller scope written.callee)
      match lexical : candidate.val.decision with
      | .lexical name spelling bound =>
        if noArguments : written.arguments = [] then
          match instantiation with
          | .closed _ => throw .request
          | .static _ staticEnvironment sameOriginal =>
            let header := staticEnvironment.numeric.original
            exactWork (Exact.charge (16*(header.header.formals.length+1)*(name.utf8ByteSize+1)))
            match selected : header.header.formals.find? (·.name == name) with
            | none => throw .request
            | some headerFormal =>
              match operation : headerFormal.kind with
              | .basis | .natural => throw .request
              | .operation kindTokens =>
                if sameName : headerFormal.name = name then
                  let formal : Formal (.static _ staticEnvironment sameOriginal) scope tokens :=
                    ⟨written,candidate.val,by with_reducible exact candidate.property,name,spelling,bound,
                      lexical,noArguments,header,sameOriginal,headerFormal,selected,sameName,kindTokens,operation⟩
                  pure [⟨[],tokens,.here,formal⟩]
                else throw .request
        else throw .request
      | _ =>
        match resolved : CallName.candidateResolution candidate.val with
        | none => throw .request
        | some target =>
          let application ← NaturalAffine.witness
            (StaticApplication.read instantiation entries environment scope written target.moduleName
              target.declaration.name (operationReader instantiation entries environment scope genericState) genericState)
          exactWork (Exact.charge (16*(application.val.actuals.length+1)^2))
          let groups ← (List.finRange application.val.actuals.length).mapM
              fun (index : Fin application.val.actuals.length) => do
            let actual : StaticApplication.Actual instantiation entries environment scope
                (operationReader instantiation entries environment scope genericState) :=
              application.val.actuals[index.val]'index.isLt
            match operation : actual.formal.kind with
            | .basis | .natural => pure []
            | .operation kindTokens =>
              let uses ← next actual.argument.tokens
              exactWork (Exact.charge (8*(uses.length+1)))
              let step : Actual instantiation entries environment scope genericState tokens
                  actual.formal.ordinal actual.argument.tokens :=
                ⟨written,candidate.val,by with_reducible exact candidate.property,target,resolved,
                  application.val,by with_reducible exact application.property,index,actual,
                  List.getElem?_eq_getElem index.isLt,rfl,kindTokens,operation,rfl⟩
              pure (uses.map (Use.underActual step))
          exactWork (Exact.charge (8*((groups.map (·.length)).sum+groups.length+1)))
          pure groups.flatten)

structure Checked {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (genericState : Option (GenericLexicalNatural.SomeEnvironment sources))
    (tokens : List LocatedToken) where
  uses : List (Use instantiation entries environment scope genericState tokens)
  original : ∃ before after,
    (readUses instantiation entries environment scope genericState 65 tokens).run before = (.ok uses,after)

def read {sources caller callerName original}
    (instantiation : @StaticInstantiation.Checked sources caller callerName original)
    (entries : List NaturalHelpers.Entry) (environment : LexicalNatural.Environment entries)
    (scope : List String) (tokens : List LocatedToken)
    (genericState : Option (GenericLexicalNatural.SomeEnvironment sources) := none) :
    WorkM (Checked instantiation entries environment scope genericState tokens) := do
  let uses ← NaturalAffine.witness (readUses instantiation entries environment scope genericState 65 tokens)
  pure ⟨uses.val,by with_reducible exact uses.property⟩

/-- Reuse only the actual source context. The reader runs with exactly the
stored symbolic state and returns its own genuine source-traversal receipt. -/
def readChecked {sources caller callerName original instantiation entries environment scope tokens}
    (source : @SourceOperation.CheckedWithInstantiation sources caller callerName original instantiation
      entries environment scope tokens) :
    WorkM (Checked instantiation entries environment scope source.genericState tokens) :=
  read instantiation entries environment scope tokens source.genericState

end QleisliKernel.SourceTypes.OperationSourceUses
