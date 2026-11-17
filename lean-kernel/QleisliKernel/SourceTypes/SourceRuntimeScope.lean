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
  | coherentArm {signature : Signature sources owner name} {body : SourceRuntimeTrace.Body signature}
      {site : Fin body.checked.events.length} {index : Nat}
      (arm : SourceRuntimeTrace.InlineArmBody body site index)
      (original : ∃ before after,
        (SourceRuntimeTrace.readInlineArmBody body site index).run before = (.ok arm,after))

def Subject.signature {sources owner name} : Subject sources owner name → Signature sources owner name
  | .whole body => body.checked.signature
  | .arm event sameName _ _ _ => sameName ▸ event.signature
  | @coherentArm _ _ _ _ body _ _ _ _ => body.checked.signature

def Subject.events {sources owner name} : Subject sources owner name → List (Event sources owner)
  | .whole body => body.checked.events
  | .arm _ _ bodies _ choice => if choice then bodies.thenResult.events else bodies.elseResult.events
  | .coherentArm replay _ => replay.result.events

def Subject.initial {sources owner name} : Subject sources owner name → Environment
  | .whole body => body.checked.summary.initial
  | .arm event _ _ _ _ => event.before
  | .coherentArm replay _ => SourceRuntimeTrace.inlineFrame replay.arm replay.target

def Subject.held {sources owner name} : Subject sources owner name → List Semantics.SourceOwners.Owner
  | .whole _ => []
  | .arm event _ _ _ _ => event.held
  | .coherentArm _ _ => []

def Subject.parameterValues {sources owner name} : Subject sources owner name → List Value
  | .whole body => body.checked.summary.parameterValues
  | .arm _ _ _ _ _ => []
  | .coherentArm replay _ => [[.owner replay.target]]

def Subject.initialRoles {sources owner name} (subject : Subject sources owner name) : List Semantics.SourceOwners.Owner :=
  match subject with
  | .whole body => body.checked.summary.parameterValues.flatMap valueOwners
  | .arm event _ _ _ _ => event.held ++ owners event.before
  | .coherentArm replay _ => [replay.target]

def Subject.initialOrdinal {sources owner name} : Subject sources owner name → Nat
  | .whole body => body.checked.summary.nextOwner
  | .arm event _ _ _ _ => event.nextOrdinal
  | @coherentArm _ _ _ _ body _ _ _ _ => body.checked.summary.nextOrdinal

def Subject.value {sources owner name} : Subject sources owner name → Value
  | .whole body => body.checked.summary.value
  | .arm _ _ bodies _ choice => if choice then bodies.thenResult.value else bodies.elseResult.value
  | .coherentArm replay _ => replay.result.value

def Subject.remaining {sources owner name} : Subject sources owner name → Environment
  | .whole body => body.checked.summary.remaining
  | .arm _ _ bodies _ choice => if choice then bodies.thenResult.remaining else bodies.elseResult.remaining
  | .coherentArm replay _ => replay.result.remaining

def Subject.allocated {sources owner name} : Subject sources owner name → List Semantics.SourceOwners.Owner
  | .whole body => body.checked.summary.allocated
  | .arm _ _ bodies _ choice => if choice then bodies.thenResult.allocated else bodies.elseResult.allocated
  | .coherentArm replay _ => replay.result.allocated

def Subject.consumed {sources owner name} : Subject sources owner name → List Semantics.SourceOwners.Owner
  | .whole body => body.checked.summary.consumed
  | .arm _ _ bodies _ choice => if choice then bodies.thenResult.consumed else bodies.elseResult.consumed
  | .coherentArm replay _ => replay.result.consumed

def Subject.nextOrdinal {sources owner name} : Subject sources owner name → Nat
  | .whole body => body.checked.summary.nextOrdinal
  | .arm _ _ bodies _ choice => if choice then bodies.thenResult.nextOrdinal else bodies.elseResult.nextOrdinal
  | .coherentArm replay _ => replay.result.nextOrdinal

def Subject.effect {sources owner name} : Subject sources owner name → Semantics.Raw.Effect
  | .whole body => body.checked.summary.inferredEffect
  | .arm _ _ bodies _ choice =>
      SourceRuntimeContext.inferredEffect (if choice then bodies.thenResult.events else bodies.elseResult.events)
  | .coherentArm replay _ => SourceRuntimeContext.inferredEffect replay.result.events

def Subject.staticRows {sources owner name} : Subject sources owner name → List SourceRows.Row
  | .whole body => body.checked.summary.staticRows
  | .arm _ _ bodies _ choice => if choice then bodies.thenResult.staticRows else bodies.elseResult.staticRows
  | .coherentArm replay _ => replay.result.staticRows

def Subject.prefixRequired {sources owner name} : Subject sources owner name → Bool
  | .whole _ => true
  | .arm _ _ _ _ _ => false
  | .coherentArm _ _ => false

def Subject.outputRoles {sources owner name} (subject : Subject sources owner name) : List Semantics.SourceOwners.Owner :=
  subject.held ++ valueOwners subject.value ++ owners subject.remaining

end QleisliKernel.SourceTypes.SourceRuntimeScope
