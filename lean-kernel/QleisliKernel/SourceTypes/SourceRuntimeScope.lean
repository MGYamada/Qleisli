import QleisliKernel.SourceTypes.SourceRuntimeTrace
import QleisliKernel.SourceTypes.OperationAccess

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
      (controlled : Bool := false)
  | arm (event : BranchEvent sources owner) (sameName : event.callerName = name)
      (bodies : SourceRuntimeTrace.BranchBodies event)
      (original : ∃ before after,
        (SourceRuntimeTrace.readBranchSource event).run before = (.ok bodies,after))
      (choice : Bool) (controlled : Bool := false)
  | coherentArm {site : SelectionEvent sources owner} {index : Nat}
      (sameName : site.callerName = name) (arm : SourceRuntimeTrace.InlineArmBody site index)
      (original : ∃ before after,
        (SourceRuntimeTrace.readInlineArmBody site index).run before = (.ok arm,after))

def Subject.signature {sources owner name} : Subject sources owner name → Signature sources owner name
  | .whole body _ => body.checked.signature
  | .arm event sameName _ _ _ _ => sameName ▸ event.signature
  | .coherentArm (site := site) sameName _ _ => sameName ▸ site.signature

def Subject.events {sources owner name} : Subject sources owner name → List (Event sources owner)
  | .whole body _ => body.checked.events
  | .arm _ _ bodies _ choice _ => if choice then bodies.thenResult.events else bodies.elseResult.events
  | .coherentArm _ replay _ => replay.result.events

def Subject.initial {sources owner name} : Subject sources owner name → Environment
  | .whole body _ => body.checked.summary.initial
  | .arm event _ _ _ _ _ => event.before
  | .coherentArm (site := site) _ replay _ => SourceRuntimeTrace.inlineFrame replay.arm site.target

def Subject.held {sources owner name} : Subject sources owner name → List Semantics.SourceOwners.Owner
  | .whole _ _ => []
  | .arm event _ _ _ _ _ => event.held
  | .coherentArm .. => []

/-- The containing selector and other live parent owners retain their original
identity in source replay. They have no ports in the isolated arm program. -/
def Subject.suspended {sources owner name} : Subject sources owner name → List Semantics.SourceOwners.Owner
  | .coherentArm (site := site) .. => site.selector :: site.held ++ owners site.remaining
  | _ => []

def Subject.parameterValues {sources owner name} : Subject sources owner name → List Value
  | .whole body _ => body.checked.summary.parameterValues
  | .arm _ _ _ _ _ _ => []
  | .coherentArm (site := site) .. => [[.owner site.target]]

def Subject.initialRoles {sources owner name} (subject : Subject sources owner name) : List Semantics.SourceOwners.Owner :=
  match subject with
  | .whole body _ => body.checked.summary.parameterValues.flatMap valueOwners
  | .arm event _ _ _ _ _ => event.held ++ owners event.before
  | .coherentArm (site := site) .. => [site.target]

def Subject.initialOrdinal {sources owner name} : Subject sources owner name → Nat
  | .whole body _ => body.checked.summary.nextOwner
  | .arm event _ _ _ _ _ => event.nextOrdinal
  | .coherentArm (site := site) .. => site.nextOrdinal

def Subject.value {sources owner name} : Subject sources owner name → Value
  | .whole body _ => body.checked.summary.value
  | .arm _ _ bodies _ choice _ => if choice then bodies.thenResult.value else bodies.elseResult.value
  | .coherentArm _ replay _ => replay.result.value

def Subject.remaining {sources owner name} : Subject sources owner name → Environment
  | .whole body _ => body.checked.summary.remaining
  | .arm _ _ bodies _ choice _ => if choice then bodies.thenResult.remaining else bodies.elseResult.remaining
  | .coherentArm _ replay _ => replay.result.remaining

def Subject.allocated {sources owner name} : Subject sources owner name → List Semantics.SourceOwners.Owner
  | .whole body _ => body.checked.summary.allocated
  | .arm _ _ bodies _ choice _ => if choice then bodies.thenResult.allocated else bodies.elseResult.allocated
  | .coherentArm _ replay _ => replay.result.allocated

def Subject.consumed {sources owner name} : Subject sources owner name → List Semantics.SourceOwners.Owner
  | .whole body _ => body.checked.summary.consumed
  | .arm _ _ bodies _ choice _ => if choice then bodies.thenResult.consumed else bodies.elseResult.consumed
  | .coherentArm _ replay _ => replay.result.consumed

def Subject.nextOrdinal {sources owner name} : Subject sources owner name → Nat
  | .whole body _ => body.checked.summary.nextOrdinal
  | .arm _ _ bodies _ choice _ => if choice then bodies.thenResult.nextOrdinal else bodies.elseResult.nextOrdinal
  | .coherentArm _ replay _ => replay.result.nextOrdinal

def Subject.effect {sources owner name} : Subject sources owner name → Semantics.Raw.Effect
  | .whole body _ => body.checked.summary.inferredEffect
  | .arm _ _ bodies _ choice _ =>
      SourceRuntimeContext.inferredEffect (if choice then bodies.thenResult.events else bodies.elseResult.events)
  | .coherentArm _ replay _ => SourceRuntimeContext.inferredEffect replay.result.events

def Subject.staticRows {sources owner name} : Subject sources owner name → List SourceRows.Row
  | .whole body _ => body.checked.summary.staticRows
  | .arm _ _ bodies _ choice _ => if choice then bodies.thenResult.staticRows else bodies.elseResult.staticRows
  | .coherentArm _ replay _ => replay.result.staticRows

def Subject.prefixRequired {sources owner name} : Subject sources owner name → Bool
  | .whole _ _ => true
  | .arm _ _ _ _ _ _ => false
  | .coherentArm .. => false

/-- The need to control an operation comes from its original enclosing
coherent arm and follows calls and branches inside that arm. -/
def Subject.requiresControl {sources owner name} : Subject sources owner name → Bool
  | .whole _ controlled | .arm _ _ _ _ _ controlled => controlled
  | .coherentArm .. => true

def applicationDemand (controlled : Bool) : StaticOperation.Paths :=
  if controlled then OperationAccess.join OperationAccess.applicable OperationAccess.controllable
  else OperationAccess.applicable

def Subject.outputRoles {sources owner name} (subject : Subject sources owner name) : List Semantics.SourceOwners.Owner :=
  subject.held ++ valueOwners subject.value ++ owners subject.remaining

end QleisliKernel.SourceTypes.SourceRuntimeScope
