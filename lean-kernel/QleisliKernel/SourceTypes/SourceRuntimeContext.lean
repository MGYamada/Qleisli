import QleisliKernel.SourceTypes.SourceRuntimeValues
import QleisliKernel.SourceTypes.SourceTrace
import QleisliKernel.SourceTypes.StaticRuntimeSignature
import QleisliKernel.SourceTypes.SourceOperationApplication
import QleisliKernel.SourceTypes.SourceBasisFunction
import QleisliKernel.SourceTypes.SourceRuntimeBranches
import QleisliKernel.SourceTypes.SourceRuntimeTransformPorts
import QleisliKernel.SourceTypes.SourceBasisBindings
import QleisliKernel.SourceTypes.SourceStaticSelection
import QleisliKernel.SourceTypes.SourceMatchLabels
import QleisliKernel.SourceTypes.SourceRuntimeMatching

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

def Signature.supply {sources owner name} (signature : Signature sources owner name) :
    StaticOperation.Supply signature.instantiation := ⟨signature.context,signature.operations⟩

structure WithPrepared {sources owner name arguments}
    (checked : StaticRuntimeSignature.Checked sources owner name arguments) (context : StaticOperation.Context)
    (actuals : List (Sigma (StaticOperation.Actual sources context))) where
  signature : Signature sources owner name
  originalArguments : signature.arguments = arguments
  originalChecked : HEq signature.checked checked
  originalContext : signature.context = context
  originalActuals : HEq signature.operations.actuals actuals

/-- Rebind the original formal obligations to the same checked actual receipts.
Their per-occurrence supply authority is never reconstructed in the callee. -/
def fromPreparedWithArguments {sources owner name arguments}
    (checked : StaticRuntimeSignature.Checked sources owner name arguments) (context : StaticOperation.Context)
    (actuals : List (Sigma (StaticOperation.Actual sources context))) :
    Finite.WorkM (WithPrepared checked context actuals) := do
  let instantiation : StaticInstantiation.Checked checked.original := .static arguments checked.environment rfl
  let operations ← StaticOperation.checkArgumentsFromWithActuals instantiation context actuals
  let signature : Signature sources owner name := ⟨arguments,checked,context,operations.val⟩
  return ⟨signature,rfl,HEq.rfl,rfl,heq_of_eq operations.property⟩

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
  sameActuals : HEq signature.operations.actuals supply.actuals

def fromQuantumCore {sources owner name} (core : QuantumSignatureCore.Checked sources owner name)
    (context : StaticOperation.Context)
    (supply : StaticOperation.ArgumentsCheckedWithInstantiation core.instantiation context) :
    Finite.WorkM (CoreBinding core context supply) := do
  let checked ← StaticRuntimeSignature.prepareWithArguments sources owner name core.staticArguments
  let prepared ← fromPreparedWithArguments checked context supply.actuals
  let signature := prepared.signature
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
      inputTrees,outputOwners,sameContext,prepared.originalActuals⟩
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
  operationActuals : SourceOperation.ApplicationActuals actuals callerSignature.supply
  signature : Signature sources resolution.moduleName resolution.declaration.name
  arguments : signature.arguments = actuals.arguments
  original : signature.original.source = resolution.source ∧
    signature.original.declaration = resolution.declaration
  originalActuals : actuals.target.envelope.source = signature.original.source ∧
    actuals.target.envelope.declaration = signature.original.declaration

structure WithWritten {sources caller scope tokens} (written : StaticApplication.Syntax tokens) where
  target : Target sources caller scope tokens
  originalWritten : target.written = written

def readTargetWithWritten {sources caller callerName scope tokens}
    (callerSignature : Signature sources caller callerName) (naturals : PhaseApplication.Naturals sources)
    (written : StaticApplication.Syntax tokens)
    (candidate : CallName.Checked sources caller scope written.callee) :
    Finite.WorkM (WithWritten (sources := sources) (caller := caller) (scope := scope) written) := do
  match selected : QuantumSignature.candidateResolution candidate with
  | none => throw .request
  | some resolution =>
    let operationReader := SourceOperation.buildWithInstantiation callerSignature.instantiation
      naturals.helpers.val naturals.environment scope naturals.generic 65
    let actuals ← StaticApplication.read callerSignature.instantiation naturals.helpers.val
      naturals.environment scope written resolution.moduleName resolution.declaration.name operationReader naturals.generic
    let operationActuals ← SourceOperation.checkApplicationActuals actuals callerSignature.supply
    let checked ← StaticRuntimeSignature.prepareWithArguments sources resolution.moduleName resolution.declaration.name actuals.arguments
    let prepared ← fromPreparedWithArguments checked (.source caller) operationActuals.actuals
    let signature := prepared.signature
    if arguments : signature.arguments = actuals.arguments then
      if original : signature.original.source = resolution.source ∧
          signature.original.declaration = resolution.declaration then
        if originalActuals : actuals.target.envelope.source = signature.original.source ∧
            actuals.target.envelope.declaration = signature.original.declaration then
          return ⟨⟨callerName,callerSignature,naturals,written,candidate,resolution,selected,
            operationReader,actuals,operationActuals,signature,arguments,original,originalActuals⟩,rfl⟩
        else throw .request
      else throw .request
    else throw .request

def readTarget {sources caller callerName scope tokens}
    (callerSignature : Signature sources caller callerName) (naturals : PhaseApplication.Naturals sources)
    (written : StaticApplication.Syntax tokens)
    (candidate : CallName.Checked sources caller scope written.callee) :
    Finite.WorkM (Target sources caller scope tokens) := do
  return (← readTargetWithWritten callerSignature naturals written candidate).target

def Target.sourceRows {sources caller scope tokens} (target : Target sources caller scope tokens) :
    List (String × String) :=
  target.naturals.sourceRows ++ target.signature.sourceRows ++ target.operationActuals.rows ++
    target.actuals.actuals.flatMap (·.sourceRows) ++ ResolutionProvenance.sourceRows target.resolution

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
  generic : GenericTypeTrace.Checked signature.original
  genericRead : ∃ before after,
    (GenericTypeTrace.readWithTree signature.instantiation tree).run before = (.ok generic,after)
  originalAsserted : SourceEffect.permits signature.original.parsedHeader.effect generic.inferredEffect = true
  basis : SourceBasisBindings.Checked signature.instantiation generic.basisObligations
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
    event.target.signature.original.parsedHeader.effect event.canonical.generic.inferredEffect

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
  generic : GenericTypeTrace.Checked signature.original
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
  binding : SourceBasisBindings.ActiveAt signature.instantiation generic.basisObligations written.parts.keyword.span.startByte
  inputType : binding.ports.input = input.basis
  outputType : binding.ports.output = outputBasis
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
  basisOffsets : List Nat

structure BranchEvent (sources : Sources) (caller : String) where
  tokens : List LocatedToken
  written : SourceControlSyntax.CheckedConditional tokens
  callerName : String
  signature : Signature sources caller callerName
  generic : GenericTypeTrace.Checked signature.original
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

structure StaticEvent (sources : Sources) (caller : String) where
  tokens : List LocatedToken
  written : SourceStaticControlSyntax.Checked tokens
  callerName : String
  signature : Signature sources caller callerName
  generic : GenericTypeTrace.Checked signature.original
  naturals : PhaseApplication.Naturals sources
  scope : List String
  selection : SourceStaticSelection.Checked sources caller naturals scope written
  thenTree : SourceSyntax.Tree written.parts.thenBody
  elseTree : SourceSyntax.Tree written.parts.elseBody
  thenCalls : List Nat
  thenCallsRead : thenTree.calls = .ok thenCalls
  elseCalls : List Nat
  elseCallsRead : elseTree.calls = .ok elseCalls
  before : Environment
  nextOrdinal : Nat
  selected : Sigma (Arm sources caller before)
  selectedTokens : selected.1 = if selection.selected then written.parts.thenBody else written.parts.elseBody
  remaining : Environment
  projected : SourceRuntimeBranches.outer before selected.2.remaining = .ok remaining
  held : List Semantics.SourceOwners.Owner

structure MatchEvent (sources : Sources) (caller : String) where
  tokens : List LocatedToken
  written : SourceMatchSyntax.Checked tokens
  callerName : String
  signature : Signature sources caller callerName
  generic : GenericTypeTrace.Checked signature.original
  naturals : PhaseApplication.Naturals sources
  scope : List String
  basis : Semantics.FiniteCarrier.Basis
  condition : Expression
  labels : SourceMatchLabels.Checked sources caller scope written basis
  before : Environment
  nextOrdinal : Nat
  arms : List (Sigma (Arm sources caller before))
  originalBodies : arms.map (·.1) = written.parts.arms.map (·.body.tokens)
  remaining : Environment
  projected : ∀ arm ∈ arms,SourceRuntimeBranches.outer before arm.2.remaining = .ok remaining
  afterArms : Nat
  value : Value
  phis : List SourceRuntimeMatching.Phi
  merged : SourceRuntimeMatching.merge condition labels.labels.ordinals (arms.map (·.2.value)) afterArms = .ok (value,phis)
  held : List Semantics.SourceOwners.Owner

structure TransformCount {sources caller callerName}
    (signature : Signature sources caller callerName) (naturals : PhaseApplication.Naturals sources)
    (scope : List String) where
  argument : CallSyntax.Argument
  checked : SourceOperation.Count signature.instantiation naturals.helpers.val naturals.environment scope argument.tokens

structure TransformEvent (sources : Sources) (caller : String) where
  tokens : List LocatedToken
  call : CallSyntax.Checked tokens
  callerName : String
  signature : Signature sources caller callerName
  naturals : PhaseApplication.Naturals sources
  scope : List String
  written : SourceRuntimeTransformSyntax.Checked call.call.callee
  target : Target sources caller scope written.base.1
  sameBase : target.written = written.base.2
  forward : Summary target.signature
  visibleUnitary : SourceEffect.visible caller target.resolution.moduleName target.signature.original.declaration.isPublic
    target.signature.original.parsedHeader.effect forward.generic.inferredEffect = .unitary
  counts : List (TransformCount signature naturals scope)
  originalCounts : counts.map (·.argument) = written.counts
  copies : Nat
  multiplied : SourceRuntimeTransformPorts.product (counts.map (·.checked.value)) = .ok copies
  access : (match written.access with
    | .forward => true
    | .adjoint => target.signature.operations.actuals.all (fun actual =>
        actual.2.graph.root.paths.applicable && actual.2.graph.root.paths.adjointable)
    | .controlled => target.signature.operations.actuals.all (fun actual =>
        actual.2.graph.root.paths.applicable && actual.2.graph.root.paths.adjointable &&
          actual.2.graph.root.paths.controllable)) = true
  ports : SourceRuntimeTransformPorts.Ports
  portsRead : SourceRuntimeTransformPorts.read (target.signature.parameters.map (·.tree))
    target.signature.result.tree written.access (!written.counts.isEmpty) = .ok ports
  arguments : List Value
  nextOrdinal : Nat
  value : Value
  allocated : List Semantics.SourceOwners.Owner
  consumed : List Semantics.SourceOwners.Owner
  afterOrdinal : Nat
  applied : SourceRuntimeTransformPorts.apply ports written.access arguments nextOrdinal =
    .ok (value,allocated,consumed,afterOrdinal)
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
  | basis (event : BasisEvent sources caller)
  | conditional (event : BranchEvent sources caller) (thenEvents elseEvents : List (Event sources caller))
  | transform (event : TransformEvent sources caller)
  | staticConditional (event : StaticEvent sources caller) (events : List (Event sources caller))
  | matching (event : MatchEvent sources caller) (arms : List (List (Event sources caller)))

def Event.callOffset {sources caller} : Event sources caller → Option Nat
  | .selection .. => none
  | .primitive event => some event.call.calleeOffset
  | .phase event => some event.call.calleeOffset
  | .named event => some event.call.calleeOffset
  | .operation event => some event.call.calleeOffset
  | .basis _ => none
  | .conditional .. => none
  | .transform event => some event.call.calleeOffset
  | .staticConditional .. => none
  | .matching .. => none

def Event.callOffsets {sources caller} (event : Event sources caller) : List Nat :=
  match event with
  | .basis event => event.bodyCalls
  | .conditional event .. => event.thenArm.calls ++ event.elseArm.calls
  | .staticConditional event .. => event.thenCalls ++ event.elseCalls
  | .matching event .. => event.arms.flatMap (·.2.calls)
  | _ => event.callOffset.toList

def Event.qmatchOffset {sources caller} : Event sources caller → Option Nat
  | .selection _ parsed .. => some parsed.keyword.span.startByte
  | _ => none

def Event.qmatchOffsets {sources caller} (event : Event sources caller) : List Nat :=
  match event with
  | .conditional event .. => QuantumSequence.originalOffsets event.written.parts.thenBody ++
      QuantumSequence.originalOffsets event.written.parts.elseBody
  | .staticConditional event .. => QuantumSequence.originalOffsets event.written.parts.thenBody ++
      QuantumSequence.originalOffsets event.written.parts.elseBody
  | .matching event .. => event.written.parts.arms.flatMap (fun arm => QuantumSequence.originalOffsets arm.body.tokens)
  | _ => event.qmatchOffset.toList

def Event.basisOffsets {sources caller} : Event sources caller → List Nat
  | .basis event => [event.written.parts.keyword.span.startByte]
  | .conditional event .. => event.thenArm.basisOffsets ++ event.elseArm.basisOffsets
  | .staticConditional event .. => event.selected.2.basisOffsets
  | .matching event .. => event.arms.flatMap (·.2.basisOffsets)
  | _ => []

def Event.offset {sources caller} : Event sources caller → Nat
  | .selection _ parsed .. => parsed.keyword.span.startByte
  | .primitive event => event.call.calleeOffset
  | .phase event => event.call.calleeOffset
  | .named event => event.call.calleeOffset
  | .operation event => event.call.calleeOffset
  | .basis event => event.written.parts.keyword.span.startByte
  | .conditional event .. => event.written.parts.keyword.span.startByte
  | .transform event => event.call.calleeOffset
  | .staticConditional event .. => event.written.parts.keyword.span.startByte
  | .matching event .. => event.written.parts.keyword.span.startByte

def Event.effect {sources caller} : Event sources caller → Semantics.Raw.Effect
  | .primitive event => primitiveEffect event.kind
  | .named event => event.effect
  | .operation event => event.effect
  | .basis event => event.function.effect
  | .conditional event .. => SourceEffect.join event.thenArm.inferredEffect event.elseArm.inferredEffect
  | .transform _ => .unitary
  | .staticConditional event .. => event.selected.2.inferredEffect
  | .matching event .. => event.arms.foldl (fun effect arm => SourceEffect.join effect arm.2.inferredEffect) .unitary
  | _ => .unitary

def Event.quantumUse {sources caller} : Event sources caller → Bool
  | .named event =>
    if caller != event.target.resolution.moduleName && event.target.signature.original.declaration.isPublic then
      (!event.target.signature.original.parsedHeader.ordinaryOnly &&
        event.target.signature.original.parsedHeader.effect.isSome) || event.canonical.generic.quantumUse
    else event.canonical.generic.quantumUse
  | .conditional event .. => event.thenArm.quantumUse || event.elseArm.quantumUse
  | .staticConditional event .. => event.selected.2.quantumUse
  | .matching event .. => event.arms.any (·.2.quantumUse)
  | _ => true

def Event.staticRows {sources caller} : Event sources caller → List (String × String)
  | .selection _ _ _ _ _ _ naturals .. => naturals.sourceRows
  | .primitive _ => []
  | .phase event => event.naturals.sourceRows
  | .named event => event.target.sourceRows ++ event.canonical.staticRows
  | .operation event => event.naturals.sourceRows ++ event.operation.rows
  | .basis event => event.staticRows
  | .conditional event .. => event.naturals.sourceRows ++ event.thenArm.staticRows ++ event.elseArm.staticRows
  | .transform event => event.target.sourceRows ++ event.forward.staticRows ++
      event.counts.flatMap (·.checked.rows)
  | .staticConditional event .. => event.selection.naturals.sourceRows ++ event.selected.2.staticRows
  | .matching event .. => event.naturals.sourceRows ++ event.labels.labels.sourceRows ++ event.arms.flatMap (·.2.staticRows)

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

/-- Actual data compared when a native continuation freshly recovers an
original arm. Proof fields are retained by the arm and outcome themselves. -/
structure ArmDescription where
  value : Value
  remaining : Environment
  allocated : List Semantics.SourceOwners.Owner
  consumed : List Semantics.SourceOwners.Owner
  nextOrdinal : Nat
  inferredEffect : Semantics.Raw.Effect
  quantumUse : Bool
  staticRows : List (String × String)
  calls : List Nat
  qmatches : List Nat
  basis : List Nat
  deriving DecidableEq, Repr

def Arm.description {sources caller before tokens} (arm : Arm sources caller before tokens) : ArmDescription :=
  ⟨arm.value,arm.remaining,arm.allocated,arm.consumed,arm.nextOrdinal,arm.inferredEffect,
    arm.quantumUse,arm.staticRows,arm.calls,QuantumSequence.originalOffsets tokens,arm.basisOffsets⟩

def Outcome.description {sources caller before} (result : Outcome sources caller before) : ArmDescription :=
  ⟨result.value,result.remaining,result.allocated,result.consumed,result.nextOrdinal,inferredEffect result.events,
    result.events.any Event.quantumUse,result.staticRows,result.events.flatMap Event.callOffsets,
    result.events.flatMap Event.qmatchOffsets,result.events.flatMap Event.basisOffsets⟩

structure Evaluated {sources owner name} (signature : Signature sources owner name) where
  summary : Summary signature
  events : List (Event sources owner)
  inferred : inferredEffect events = summary.inferredEffect
  basisCovered : summary.basis.covered (events.flatMap Event.basisOffsets) = true

end QleisliKernel.SourceTypes.SourceRuntimeContext
