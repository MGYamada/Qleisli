import QleisliKernel.SourceTypes.SourceRuntimeValues
import QleisliKernel.SourceTypes.SourceTrace
import QleisliKernel.SourceTypes.StaticRuntimeSignature
import QleisliKernel.SourceTypes.SourceOperationApplication
import QleisliKernel.SourceTypes.SourceBasisFunction
import QleisliKernel.SourceTypes.SourceRuntimeBranches

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
  let checked ← StaticRuntimeSignature.prepareWithArguments sources owner name arguments
  let instantiation : StaticInstantiation.Checked checked.original := .static arguments checked.environment rfl
  let operations ← StaticOperation.checkArgumentsWithInstantiation instantiation context
  return ⟨arguments,checked,context,operations⟩

def Signature.sourceRows {sources owner name} (signature : Signature sources owner name) :
    List (String × String) := signature.checked.sourceRows ++ signature.operations.sourceRows

/-- The supply context comes from the original source/host selection. It is
never replaced by the provider's module merely to recheck its body. -/
structure CoreBinding {sources owner name} (core : QuantumSignatureCore.Checked sources owner name)
    (context : StaticOperation.Context)
    (supply : StaticOperation.ArgumentsCheckedWithInstantiation core.instantiation context) where
  signature : Signature sources owner name
  source : signature.original.source = core.original.source
  declaration : signature.original.declaration = core.original.declaration
  header : signature.original.occurrence.header = core.original.occurrence.header
  body : signature.original.occurrence.body = core.original.occurrence.body
  opening : signature.original.occurrence.openBrace = core.original.occurrence.openBrace
  closing : signature.original.occurrence.closeBrace = core.original.occurrence.closeBrace
  bases : signature.arguments.bases = core.staticArguments.bases
  naturals : signature.arguments.naturals = core.staticArguments.naturals
  operations : signature.arguments.operations = core.staticArguments.operations
  inputTrees : signature.parameters.map (·.tree) = core.inputs.map Semantics.RuntimeType.owner
  outputOwners : Semantics.RuntimeType.ownerBases signature.result.tree = some core.outputs
  sameContext : signature.context = context

def fromQuantumCore {sources owner name} (core : QuantumSignatureCore.Checked sources owner name)
    (context : StaticOperation.Context)
    (supply : StaticOperation.ArgumentsCheckedWithInstantiation core.instantiation context) :
    Finite.WorkM (CoreBinding core context supply) := do
  let signature ← readSignature sources owner name core.staticArguments context
  Finite.exactWork (Exact.charge (16*(core.original.source.utf8ByteSize+
    signature.original.source.utf8ByteSize+
    SourceTrace.Meter.tokenFields core.original.occurrence.header+
    SourceTrace.Meter.tokenFields core.original.occurrence.body+
    Raw.OwnerFlow.fields (core.inputs.zipIdx.map fun (basis,index) => ⟨index,basis⟩)+
    Raw.OwnerFlow.fields (core.outputs.zipIdx.map fun (basis,index) => ⟨index,basis⟩)+1)))
  if same : signature.original.source = core.original.source ∧
      signature.original.declaration = core.original.declaration ∧
      signature.original.occurrence.header = core.original.occurrence.header ∧
      signature.original.occurrence.body = core.original.occurrence.body ∧
      signature.original.occurrence.openBrace = core.original.occurrence.openBrace ∧
      signature.original.occurrence.closeBrace = core.original.occurrence.closeBrace ∧
      signature.arguments.bases = core.staticArguments.bases ∧
      signature.arguments.naturals = core.staticArguments.naturals ∧
      signature.arguments.operations = core.staticArguments.operations ∧
      signature.parameters.map (·.tree) = core.inputs.map Semantics.RuntimeType.owner ∧
      Semantics.RuntimeType.ownerBases signature.result.tree = some core.outputs ∧
      signature.context = context then
    let ⟨source,declaration,header,body,opening,closing,bases,naturals,operations,inputTrees,outputOwners,sameContext⟩ := same
    return ⟨signature,source,declaration,header,body,opening,closing,bases,naturals,operations,
      inputTrees,outputOwners,sameContext⟩
  else throw .request

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
  staticRows : List (String × String)

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

structure BasisEvent (sources : Sources) (caller : String) where
  tokens : List LocatedToken
  written : SourceControlSyntax.CheckedBasis tokens
  callerName : String
  signature : Signature sources caller callerName
  naturals : PhaseApplication.Naturals sources
  scope : List String
  input : Semantics.SourceOwners.Owner
  ordinaryBefore : Environment
  bodyInitial : Environment
  bodyOrdinal : Nat
  bodyTree : SourceSyntax.Tree written.parts.body
  bodyValue : Value
  inputTypes : List Semantics.FiniteCarrier.Basis
  outputBasis : Semantics.FiniteCarrier.Basis
  function : SourceBasisFunction.Checked input.basis outputBasis inputTypes bodyValue
  bodySeeded : SourceRuntimeValues.bind (written.parts.pattern.map (·.text)) function.bound ordinaryBefore
    (.basis written.parts.keyword.span.startByte) = .ok bodyInitial
  bodyCalls : List Nat
  originalCalls : bodyTree.calls = .ok bodyCalls
  bodyEffect : Semantics.Raw.Effect
  pureBody : bodyEffect = .unitary
  bodyQuantum : Bool
  classicalBody : bodyQuantum = false
  output : Semantics.SourceOwners.Owner
  held : List Semantics.SourceOwners.Owner
  remaining : Environment
  staticRows : List (String × String)

structure Arm (sources : Sources) (caller : String) (before : Environment) (tokens : List LocatedToken) where
  tree : SourceSyntax.Tree tokens
  value : Value
  remaining : Environment
  allocated : List Semantics.SourceOwners.Owner
  consumed : List Semantics.SourceOwners.Owner
  nextOrdinal : Nat
  balanced : (owners before ++ allocated).Perm (valueOwners value ++ owners remaining ++ consumed)
  inferredEffect : Semantics.Raw.Effect
  quantumUse : Bool
  staticRows : List (String × String)
  calls : List Nat
  originalCalls : tree.calls = .ok calls

structure BranchEvent (sources : Sources) (caller : String) where
  tokens : List LocatedToken
  written : SourceControlSyntax.CheckedConditional tokens
  callerName : String
  signature : Signature sources caller callerName
  naturals : PhaseApplication.Naturals sources
  scope : List String
  condition : Expression
  before : Environment
  nextOrdinal : Nat
  thenArm : Arm sources caller before written.parts.thenBody
  elseArm : Arm sources caller before written.parts.elseBody
  remaining : Environment
  thenOuter : SourceRuntimeBranches.outer before thenArm.remaining = .ok remaining
  elseOuter : SourceRuntimeBranches.outer before elseArm.remaining = .ok remaining
  value : Value
  phis : List SourceRuntimeBranches.Phi
  merged : SourceRuntimeBranches.merge condition thenArm.value elseArm.value elseArm.nextOrdinal = .ok (value,phis)
  held : List Semantics.SourceOwners.Owner

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
  | basis (event : BasisEvent sources caller)
  | conditional (event : BranchEvent sources caller) (thenEvents elseEvents : List (Event sources caller))

def Event.callOffset {sources caller} : Event sources caller → Option Nat
  | .selection .. => none
  | .primitive event => some event.call.calleeOffset
  | .phase event => some event.call.calleeOffset
  | .named event => some event.call.calleeOffset
  | .operation event => some event.call.calleeOffset
  | .basis _ => none
  | .conditional .. => none

def Event.callOffsets {sources caller} (event : Event sources caller) : List Nat :=
  match event with
  | .basis event => event.bodyCalls
  | .conditional event .. => event.thenArm.calls ++ event.elseArm.calls
  | _ => event.callOffset.toList

def Event.qmatchOffset {sources caller} : Event sources caller → Option Nat
  | .selection _ parsed .. => some parsed.keyword.span.startByte
  | _ => none

def Event.qmatchOffsets {sources caller} (event : Event sources caller) : List Nat :=
  match event with
  | .conditional event .. => QuantumSequence.originalOffsets event.written.parts.thenBody ++
      QuantumSequence.originalOffsets event.written.parts.elseBody
  | _ => event.qmatchOffset.toList

def Event.offset {sources caller} : Event sources caller → Nat
  | .selection _ parsed .. => parsed.keyword.span.startByte
  | .primitive event => event.call.calleeOffset
  | .phase event => event.call.calleeOffset
  | .named event => event.call.calleeOffset
  | .operation event => event.call.calleeOffset
  | .basis event => event.written.parts.keyword.span.startByte
  | .conditional event .. => event.written.parts.keyword.span.startByte

def Event.effect {sources caller} : Event sources caller → Semantics.Raw.Effect
  | .primitive event => primitiveEffect event.kind
  | .named event => event.effect
  | .operation event => event.effect
  | .basis event => event.function.effect
  | .conditional event .. => SourceEffect.join event.thenArm.inferredEffect event.elseArm.inferredEffect
  | _ => .unitary

def Event.quantumUse {sources caller} : Event sources caller → Bool
  | .named event =>
    if caller != event.target.resolution.moduleName && event.target.signature.original.declaration.isPublic then
      (!event.target.signature.original.parsedHeader.ordinaryOnly &&
        event.target.signature.original.parsedHeader.effect.isSome) || event.canonical.quantumUse
    else event.canonical.quantumUse
  | .conditional event .. => event.thenArm.quantumUse || event.elseArm.quantumUse
  | _ => true

def Event.staticRows {sources caller} : Event sources caller → List (String × String)
  | .selection _ _ _ _ _ _ naturals .. => naturals.sourceRows
  | .primitive _ => []
  | .phase event => event.naturals.sourceRows
  | .named event => event.canonical.staticRows
  | .operation event => event.naturals.sourceRows ++ event.operation.rows
  | .basis event => event.staticRows
  | .conditional event .. => event.naturals.sourceRows ++ event.thenArm.staticRows ++ event.elseArm.staticRows

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
  staticRows : List (String × String)

structure Evaluated {sources owner name} (signature : Signature sources owner name) where
  summary : Summary signature
  events : List (Event sources owner)
  inferred : inferredEffect events = summary.inferredEffect

end QleisliKernel.SourceTypes.SourceRuntimeContext
