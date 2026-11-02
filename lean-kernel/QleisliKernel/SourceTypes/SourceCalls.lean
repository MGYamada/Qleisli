import QleisliKernel.SourceTypes.SourceSyntax
import QleisliKernel.SourceTypes.QuantumOperands
import QleisliKernel.SourceTypes.QuantumBody
import QleisliKernel.SourceTypes.SourceContext
import QleisliKernel.SourceTypes.SourceEffect
import QleisliKernel.SourceTypes.GenericTypeTrace
import QleisliKernel.SourceTypes.StaticSelection
import QleisliKernel.SourceTypes.PhaseApplication

/-! Original named-call metadata and exact logical owner transport.
The common body evaluator computes the canonical return value before transport.
Equal widths, declaration annotations and a supplied permutation cannot select it.
This component alone grants no body theorem, operation access or native handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceCalls
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Semantics.SourceOwners

def resolution {sources caller scope tokens}
    (candidate : CallName.Checked sources caller scope tokens) : Option Resolved :=
  match candidate.decision with
  | .named resolved => some resolved.result
  | .prelude _ _ _ _ _ _ _ _ resolved => some resolved.result
  | _ => none

structure Target (sources : Sources) (caller : String) (scope : List String)
    (tokens : List LocatedToken) where
  callerName : String
  callerSignature : QuantumSignature.Checked sources caller callerName
  naturals : PhaseApplication.Naturals sources
  written : StaticApplication.Syntax tokens
  candidate : CallName.Checked sources caller scope written.callee
  selected : QuantumSignature.InstanceSelected callerSignature naturals.helpers.val
    naturals.environment scope written candidate

def Target.resolved {sources caller scope tokens} (target : Target sources caller scope tokens) : Resolved :=
  target.selected.resolution

def Target.signature {sources caller scope tokens} (target : Target sources caller scope tokens) :
    QuantumSignature.Checked sources target.resolved.moduleName target.resolved.declaration.name :=
  target.selected.signature

def readTarget {sources caller callerName scope tokens}
    (callerSignature : QuantumSignature.Checked sources caller callerName)
    (naturals : PhaseApplication.Naturals sources) (written : StaticApplication.Syntax tokens)
    (candidate : CallName.Checked sources caller scope written.callee) :
    Finite.WorkM (Target sources caller scope tokens) := do
  let selected ← QuantumSignature.selectInstance callerSignature naturals.helpers.val
    naturals.environment scope written candidate naturals.generic
  return ⟨callerName,callerSignature,naturals,written,candidate,selected⟩

def argumentOwners (inputs : List Semantics.FiniteCarrier.Basis) (arguments : List Value) :
    Except String (List Owner) := do
  if inputs.length != arguments.length then throw "original call argument count"
  (inputs.zip arguments).mapM fun (basis,value) => do
    let [.owner owner] := value | throw "quantum call requires one owner per original parameter"
    if owner.basis != basis then throw "original call argument nominal type"
    return owner

/-- Canonical ordinals select the actual evaluated arguments. The full basis is
checked again at each occurrence, including zero-width and nominal owners. -/
def transport (arguments : List Owner) (value : Value) : Except String Value :=
  value.mapM fun atom => match atom with
    | .tuple arity => pure (.tuple arity)
    | .owner canonical => do
      let some actual := arguments[canonical.ordinal]? | throw "call owner ordinal"
      if actual.basis != canonical.basis then throw "call owner nominal transport"
      return .owner actual

structure Canonical {sources owner name}
    (signature : QuantumSignature.Checked sources owner name) where
  patterns : List (List String)
  parameters : QuantumOperands.parameterPatterns signature.original = .ok patterns
  initial : Environment
  seeded : QuantumOperands.seed signature patterns = .ok initial
  tree : SourceSyntax.Tree signature.original.occurrence.body
  parsed : SourceSyntax.read (signature.original.occurrence.body.length+1) 0 true
    signature.original.occurrence.body = .ok tree
  generic : GenericTypeTrace.Checked signature.original
  genericRead : ∃ before after,
    (GenericTypeTrace.readWithTree signature.instantiation tree
      (signature.operations.catalogue.map (·.modulesContext))
      (signature.operations.catalogue.map (·.meaningsContext))).run before = (.ok generic,after)
  originalAsserted : SourceEffect.permits signature.original.parsedHeader.effect generic.inferredEffect = true
  value : Value
  remaining : Environment
  complete : owners remaining = []
  returned : (owners initial).Perm (valueOwners value)
  shape : QuantumBody.resultShape signature.parts value = true
  resultTypes : (valueOwners value).map (·.basis) = signature.outputs
  inferredEffect : Semantics.Raw.Effect
  asserted : SourceEffect.permits signature.original.parsedHeader.effect inferredEffect = true
  staticRows : List (String × String)

structure Event (sources : Sources) (caller : String) where
  tokens : List LocatedToken
  call : CallSyntax.Checked tokens
  scope : List String
  target : Target sources caller scope call.call.callee
  canonical : Canonical target.signature
  arguments : List Value
  inputOwners : List Owner
  matched : argumentOwners target.signature.inputs arguments = .ok inputOwners
  value : Value
  transported : transport inputOwners canonical.value = .ok value
  held : List Owner
  before : Environment
  remaining : Environment
  frame : (held ++ owners before).Perm (inputOwners ++ held ++ owners remaining)

def Event.moduleName {sources caller} (event : Event sources caller) : String :=
  event.target.resolved.moduleName

def Event.functionName {sources caller} (event : Event sources caller) : String :=
  event.target.resolved.declaration.name

def Event.signature {sources caller} (event : Event sources caller) :
    QuantumSignature.Checked sources event.moduleName event.functionName := event.target.signature

def Event.outputOwners {sources caller} (event : Event sources caller) : List Owner :=
  valueOwners event.value

def Event.effect {sources caller} (event : Event sources caller) : Semantics.Raw.Effect :=
  SourceEffect.visible caller event.moduleName event.signature.original.declaration.isPublic
    event.signature.original.parsedHeader.effect event.canonical.generic.inferredEffect

theorem Event.originalTokens {sources caller} (event : Event sources caller) :
    event.call.call.render = event.tokens := event.call.original

end QleisliKernel.SourceTypes.SourceCalls
