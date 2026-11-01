import QleisliKernel.SourceTypes.SourceRuntimeValues
import QleisliKernel.SourceTypes.SourceTrace
import QleisliKernel.SourceTypes.StaticRuntimeSignature
import QleisliKernel.SourceTypes.SourceOperationApplication

/-! Original mixed runtime signatures, call targets and owner/effect histories.
Runtime metadata grants no native execution or qmatch arm capability. The actual
body traversal and native history/equation continuations remain distinct.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceRuntimeContext
open QleisliKernel QleisliKernel.SourceTypes
open SourceRuntimeValues

structure Signature (sources : Sources) (owner name : String) where
  arguments : StaticTypes.Arguments
  checked : StaticRuntimeSignature.Checked sources owner name arguments
  context : StaticOperation.Context
  operations : StaticOperation.ArgumentsCheckedWithInstantiation
    (.static arguments checked.environment rfl) context

def Signature.original {sources owner name} (signature : Signature sources owner name) :=
  signature.checked.original

def Signature.parameters {sources owner name} (signature : Signature sources owner name) :=
  signature.checked.parameters

def Signature.result {sources owner name} (signature : Signature sources owner name) :=
  signature.checked.result

def Signature.staticNames {sources owner name} (signature : Signature sources owner name) : List String :=
  signature.checked.environment.numeric.original.header.formals.map (·.name)

def Signature.instantiation {sources owner name} (signature : Signature sources owner name) :
    StaticInstantiation.Checked signature.original :=
  .static signature.arguments signature.checked.environment rfl

def Signature.naturals {sources owner name} (signature : Signature sources owner name) :
    Finite.WorkM (PhaseApplication.Naturals sources) :=
  PhaseApplication.prepareWithInstantiation signature.instantiation

def Signature.operationNames {sources owner name} (signature : Signature sources owner name) : List String :=
  signature.instantiation.operationNames

def readSignature (sources : Sources) (owner name : String) (arguments : StaticTypes.Arguments)
    (context : StaticOperation.Context := .external) :
    Finite.WorkM (Signature sources owner name) := do
  let checked ← StaticRuntimeSignature.read sources owner name arguments
  let instantiation : StaticInstantiation.Checked checked.original := .static arguments checked.environment rfl
  let operations ← StaticOperation.checkArgumentsWithInstantiation instantiation context
  return ⟨arguments,checked,context,operations⟩

structure Target (sources : Sources) (caller : String) (scope : List String)
    (tokens : List LocatedToken) where
  callerName : String
  callerSignature : Signature sources caller callerName
  naturals : PhaseApplication.Naturals sources
  written : StaticApplication.Syntax tokens
  candidate : CallName.Checked sources caller scope written.callee
  resolution : Resolved
  selected : QuantumSignature.candidateResolution candidate = some resolution
  operationReader : StaticApplication.OperationReader
  actuals : StaticApplication.Checked callerSignature.instantiation naturals.helpers.val
    naturals.environment scope operationReader written resolution.moduleName resolution.declaration.name
  signature : Signature sources resolution.moduleName resolution.declaration.name
  arguments : signature.arguments = actuals.arguments
  original : signature.original.source = resolution.source ∧
    signature.original.declaration = resolution.declaration

def readTarget {sources caller callerName scope tokens}
    (callerSignature : Signature sources caller callerName) (naturals : PhaseApplication.Naturals sources)
    (written : StaticApplication.Syntax tokens)
    (candidate : CallName.Checked sources caller scope written.callee) :
    Finite.WorkM (Target sources caller scope tokens) := do
  match selected : QuantumSignature.candidateResolution candidate with
  | none => throw .request
  | some resolution =>
    let operationReader := SourceOperation.buildWithInstantiation callerSignature.instantiation
      naturals.helpers.val naturals.environment scope naturals.generic 65
    let actuals ← StaticApplication.read callerSignature.instantiation naturals.helpers.val
      naturals.environment scope written resolution.moduleName resolution.declaration.name operationReader naturals.generic
    let signature ← readSignature sources resolution.moduleName resolution.declaration.name actuals.arguments (.source caller)
    if arguments : signature.arguments = actuals.arguments then
      if original : signature.original.source = resolution.source ∧
          signature.original.declaration = resolution.declaration then
        return ⟨callerName,callerSignature,naturals,written,candidate,resolution,selected,
          operationReader,actuals,signature,arguments,original⟩
      else throw .request
    else throw .request

structure Summary {sources owner name} (signature : Signature sources owner name) where
  patterns : List (List String)
  parameters : QuantumOperands.parameterPatterns signature.original = .ok patterns
  parameterValues : List Value
  nextOwner : Nat
  nextOrdinary : Nat
  valuesRead : seedValues signature.parameters = .ok (parameterValues,nextOwner,nextOrdinary)
  initial : Environment
  seeded : seed patterns parameterValues = .ok initial
  tree : SourceSyntax.Tree signature.original.occurrence.body
  parsed : SourceSyntax.read (signature.original.occurrence.body.length+1) 0 true
    signature.original.occurrence.body = .ok tree
  value : Value
  remaining : Environment
  allocated : List Semantics.SourceOwners.Owner
  consumed : List Semantics.SourceOwners.Owner
  nextOrdinal : Nat
  issued : allocated.map (·.ordinal) = (List.range allocated.length).map (nextOwner+·)
  ordinalCount : nextOrdinal = nextOwner+allocated.length
  complete : owners remaining = []
  balanced : (owners initial ++ allocated).Perm (valueOwners value ++ consumed)
  typed : typeOf value = signature.result.tree
  inferredEffect : Semantics.Raw.Effect
  asserted : SourceEffect.permits signature.original.parsedHeader.effect inferredEffect = true
  quantumUse : Bool
  publicQuantum : signature.original.declaration.isPublic = true → quantumUse = true →
    signature.original.parsedHeader.effect.isSome = true

structure NamedEvent (sources : Sources) (caller : String) where
  tokens : List LocatedToken
  call : CallSyntax.Checked tokens
  scope : List String
  target : Target sources caller scope call.call.callee
  canonical : Summary target.signature
  arguments : List Value
  matched : arguments.map typeOf = target.signature.parameters.map (·.tree)
  inputOwners : List Semantics.SourceOwners.Owner
  inputs : inputOwners = arguments.flatMap valueOwners
  allocated : List Semantics.SourceOwners.Owner
  ownerMap : List Semantics.SourceOwners.Owner
  mapping : ownerMap = inputOwners ++ allocated
  value : Value
  transported : transport ⟨caller,target.callerName,call.calleeOffset⟩ ownerMap
    (arguments.flatMap ordinary) canonical.value = .ok value
  consumed : List Semantics.SourceOwners.Owner
  consumedRead : canonical.consumed.mapM (mappedOwner ownerMap) = .ok consumed
  held : List Semantics.SourceOwners.Owner
  remaining : Environment

def NamedEvent.effect {sources caller} (event : NamedEvent sources caller) : Semantics.Raw.Effect :=
  SourceEffect.visible caller event.target.resolution.moduleName
    event.target.signature.original.declaration.isPublic
    event.target.signature.original.parsedHeader.effect event.canonical.inferredEffect

def primitive {sources caller scope tokens}
    (candidate : CallName.Checked sources caller scope tokens) : Option CallName.Primitive :=
  match candidate.decision with | .primitive _ _ _ _ _ _ kind _ => some kind | _ => none

def primitiveEffect : CallName.Primitive → Semantics.Raw.Effect
  | .measureZ | .discard => .observe
  | _ => .unitary

structure PrimitiveEvent (sources : Sources) (caller : String) where
  tokens : List LocatedToken
  call : CallSyntax.Checked tokens
  scope : List String
  written : StaticApplication.Syntax call.call.callee
  candidate : CallName.Checked sources caller scope written.callee
  kind : CallName.Primitive
  selected : primitive candidate = some kind
  arguments : List Value
  value : Value
  allocated : List Semantics.SourceOwners.Owner
  consumed : List Semantics.SourceOwners.Owner
  nextOrdinal : Nat
  held : List Semantics.SourceOwners.Owner
  remaining : Environment

structure PhaseEvent (sources : Sources) (caller : String) where
  tokens : List LocatedToken
  call : CallSyntax.Checked tokens
  scope : List String
  naturals : PhaseApplication.Naturals sources
  application : PhaseApplication.Checked sources caller naturals scope call
  operand : Semantics.SourceOwners.Owner
  bit : operand.basis = [.bit]
  held : List Semantics.SourceOwners.Owner
  remaining : Environment

inductive Event (sources : Sources) (caller : String) where
  | selection (tokens : List LocatedToken) (parsed : QuantumMatch.Parsed)
      (original : QuantumMatch.parse tokens = .ok (parsed,[]))
      (selector target : Semantics.SourceOwners.Owner) (scope : List String)
      (naturals : PhaseApplication.Naturals sources)
      (held : List Semantics.SourceOwners.Owner) (remaining : Environment)
  | primitive (event : PrimitiveEvent sources caller)
  | phase (event : PhaseEvent sources caller)
  | named (event : NamedEvent sources caller)
  | operation (event : SourceOperationApplication.Event sources caller)

def Event.callOffset {sources caller} : Event sources caller → Option Nat
  | .selection .. => none
  | .primitive event => some event.call.calleeOffset
  | .phase event => some event.call.calleeOffset
  | .named event => some event.call.calleeOffset
  | .operation event => some event.call.calleeOffset

def Event.qmatchOffset {sources caller} : Event sources caller → Option Nat
  | .selection _ parsed .. => some parsed.keyword.span.startByte
  | _ => none

def Event.effect {sources caller} : Event sources caller → Semantics.Raw.Effect
  | .primitive event => primitiveEffect event.kind
  | .named event => event.effect
  | .operation event => event.effect
  | _ => .unitary

def Event.quantumUse {sources caller} : Event sources caller → Bool
  | .named event =>
    if caller != event.target.resolution.moduleName && event.target.signature.original.declaration.isPublic then
      (!event.target.signature.original.parsedHeader.ordinaryOnly &&
        event.target.signature.original.parsedHeader.effect.isSome) || event.canonical.quantumUse
    else event.canonical.quantumUse
  | _ => true

def inferredEffect {sources caller} (events : List (Event sources caller)) : Semantics.Raw.Effect :=
  events.foldl (fun effect event => SourceEffect.join effect event.effect) .unitary

structure Outcome (sources : Sources) (caller : String) (before : Environment) where
  value : Value
  remaining : Environment
  allocated : List Semantics.SourceOwners.Owner
  consumed : List Semantics.SourceOwners.Owner
  nextOrdinal : Nat
  events : List (Event sources caller)
  balanced : (owners before ++ allocated).Perm (valueOwners value ++ owners remaining ++ consumed)

structure Evaluated {sources owner name} (signature : Signature sources owner name) where
  summary : Summary signature
  events : List (Event sources owner)
  inferred : inferredEffect events = summary.inferredEffect

end QleisliKernel.SourceTypes.SourceRuntimeContext
