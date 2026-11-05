import QleisliKernel.SourceTypes.SourceRuntimeTrace

/-! Authentic source scopes for the common runtime block traversal.
A branch arm is the actual outcome of the existing original branch reader,
not a fabricated function signature, Body or shortened source program. The
original event, both arm reads and their execution receipt remain retained.
These views grant no native, effect, ownership or semantic acceptance.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceRuntimeScope
open QleisliKernel QleisliKernel.Finite SourceRuntimeValues SourceRuntimeContext

inductive Subject (sources : Sources) (owner name : String) : Type where
  | whole {signature : Signature sources owner name} (body : SourceRuntimeTrace.Body signature)
  | arm (event : BranchEvent sources owner) (sameName : event.callerName = name)
      (bodies : SourceRuntimeTrace.BranchBodies event)
      (original : ∃ before after,
        (SourceRuntimeTrace.readBranchSource event).run before = (.ok bodies,after))
      (choice : Bool)

def Subject.signature {sources owner name} : Subject sources owner name → Signature sources owner name
  | .whole body => body.checked.signature
  | .arm event sameName _ _ _ => sameName ▸ event.signature

def Subject.events {sources owner name} : Subject sources owner name → List (Event sources owner)
  | .whole body => body.checked.events
  | .arm _ _ bodies _ choice => if choice then bodies.thenResult.events else bodies.elseResult.events

def Subject.initial {sources owner name} : Subject sources owner name → Environment
  | .whole body => body.checked.summary.initial
  | .arm event _ _ _ _ => event.before

def Subject.held {sources owner name} : Subject sources owner name → List Semantics.SourceOwners.Owner
  | .whole _ => []
  | .arm event _ _ _ _ => event.held

def Subject.parameterValues {sources owner name} : Subject sources owner name → List Value
  | .whole body => body.checked.summary.parameterValues
  | .arm _ _ _ _ _ => []

def Subject.initialRoles {sources owner name} (subject : Subject sources owner name) : List Semantics.SourceOwners.Owner :=
  match subject with
  | .whole body => body.checked.summary.parameterValues.flatMap valueOwners
  | .arm event _ _ _ _ => event.held ++ owners event.before

def Subject.initialOrdinal {sources owner name} : Subject sources owner name → Nat
  | .whole body => body.checked.summary.nextOwner
  | .arm event _ _ _ _ => event.nextOrdinal

def Subject.value {sources owner name} : Subject sources owner name → Value
  | .whole body => body.checked.summary.value
  | .arm _ _ bodies _ choice => if choice then bodies.thenResult.value else bodies.elseResult.value

def Subject.remaining {sources owner name} : Subject sources owner name → Environment
  | .whole body => body.checked.summary.remaining
  | .arm _ _ bodies _ choice => if choice then bodies.thenResult.remaining else bodies.elseResult.remaining

def Subject.allocated {sources owner name} : Subject sources owner name → List Semantics.SourceOwners.Owner
  | .whole body => body.checked.summary.allocated
  | .arm _ _ bodies _ choice => if choice then bodies.thenResult.allocated else bodies.elseResult.allocated

def Subject.consumed {sources owner name} : Subject sources owner name → List Semantics.SourceOwners.Owner
  | .whole body => body.checked.summary.consumed
  | .arm _ _ bodies _ choice => if choice then bodies.thenResult.consumed else bodies.elseResult.consumed

def Subject.nextOrdinal {sources owner name} : Subject sources owner name → Nat
  | .whole body => body.checked.summary.nextOrdinal
  | .arm _ _ bodies _ choice => if choice then bodies.thenResult.nextOrdinal else bodies.elseResult.nextOrdinal

def Subject.effect {sources owner name} : Subject sources owner name → Semantics.Raw.Effect
  | .whole body => body.checked.summary.inferredEffect
  | .arm _ _ bodies _ choice =>
      SourceRuntimeContext.inferredEffect (if choice then bodies.thenResult.events else bodies.elseResult.events)

def Subject.prefixRequired {sources owner name} : Subject sources owner name → Bool
  | .whole _ => true
  | .arm _ _ _ _ _ => false

def Subject.outputRoles {sources owner name} (subject : Subject sources owner name) : List Semantics.SourceOwners.Owner :=
  subject.held ++ valueOwners subject.value ++ owners subject.remaining

end QleisliKernel.SourceTypes.SourceRuntimeScope
