import QleisliKernel.Qirf.RuntimeStaticPrimitive

/-! An original static fold shares the enclosing Raw block and event handlers.
The explicit partition covers every emitted operation, in iteration order.
Owner-only operations and empty folds still retain their source boundaries.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeStaticFold
open QleisliKernel Finite SourceTypes SourceRuntimeValues
open RuntimeStaticPrimitive (Owner Frame readFrame)
open SourceSequence (Position)

private def advance (expected : Nat) (position : Position) : Option Nat :=
  if position.start == expected then some (expected+position.count) else none

def contiguous (parent : Position) (positions : List Position) : Bool :=
  positions.foldlM advance parent.start == some (parent.start+parent.count)

inductive Ordered : Nat → List Position → Nat → Prop where
  | empty (cursor : Nat) : Ordered cursor [] cursor
  | next {cursor child rest finish} (start : child.start = cursor)
      (after : Ordered (cursor+child.count) rest finish) :
      Ordered cursor (child :: rest) finish

theorem Ordered.le_finish {start positions finish} (ordered : Ordered start positions finish) :
    start ≤ finish := by
  induction ordered with
  | empty => exact Nat.le_refl _
  | next _ _ next => exact Nat.le_trans (Nat.le_add_right ..) next

theorem Ordered.contains {start positions finish} (ordered : Ordered start positions finish)
    {position : Position} (member : position ∈ positions) :
    start ≤ position.start ∧ position.start+position.count ≤ finish := by
  induction ordered with
  | empty => cases member
  | @next cursor child rest finish equal next ih =>
    rcases List.mem_cons.mp member with same | later
    · subst position
      exact ⟨Nat.le_of_eq equal.symm,by rw [equal]; exact next.le_finish⟩
    · obtain ⟨lower,upper⟩ := ih later
      exact ⟨Nat.le_trans (Nat.le_add_right ..) lower,upper⟩

private theorem ordered_of_fold {positions : List Position} {cursor finish : Nat}
    (read : positions.foldlM advance cursor = some finish) : Ordered cursor positions finish := by
  induction positions generalizing cursor with
  | nil =>
    have same : cursor = finish := Option.some.inj read
    subst finish
    exact .empty cursor
  | cons child rest ih =>
    change (advance cursor child >>= rest.foldlM advance) = some finish at read
    by_cases start : child.start = cursor
    · have tail : rest.foldlM advance (cursor+child.count) = some finish := by
        simp [advance,start] at read
        exact read
      exact .next start (ih tail)
    · simp [advance,start] at read

structure Partition {sources caller} (event : SourceRuntimeContext.FoldEvent sources caller)
    (iterations : List (List (SourceRuntimeContext.Event sources caller))) (parent : Position) where
  positions : List Position
  offset : parent.offset = event.written.parts.keyword.span.startByte
  iterationCount : iterations.length = event.iterations.length
  count : positions.length = iterations.flatten.length
  offsets : positions.map (·.offset) = iterations.flatten.map SourceRuntimeContext.Event.offset
  coverage : Ordered parent.start positions (parent.start+parent.count)

def readPartition {sources caller} (event : SourceRuntimeContext.FoldEvent sources caller)
    (iterations : List (List (SourceRuntimeContext.Event sources caller))) (parent : Position)
    (claimed : Option (List Position)) : WorkM (Partition event iterations parent) := do
  let some positions := claimed | throw .request
  exactWork (Exact.charge (16*(iterations.length+positions.length+(iterations.map List.length).sum+1)))
  if offset : parent.offset = event.written.parts.keyword.span.startByte then
    if checked : iterations.length = event.iterations.length ∧ positions.length = iterations.flatten.length ∧
        positions.map (·.offset) = iterations.flatten.map SourceRuntimeContext.Event.offset ∧
        contiguous parent positions = true then
      let ⟨iterations,count,offsets,coverage⟩ := checked
      return ⟨positions,offset,iterations,count,offsets,ordered_of_fold (beq_iff_eq.mp coverage)⟩
    else throw .request
  else throw .request

def spectators {sources caller} (event : SourceRuntimeContext.FoldEvent sources caller)
    (suspended : List Owner) : List Owner :=
  event.held.filter (fun owner => !suspended.contains owner) ++ owners event.outer

structure Before {sources caller dependencies program block start count}
    (event : SourceRuntimeContext.FoldEvent sources caller)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before : RuntimeStructuralAction.SourceState) (suspended : List Owner) where
  ordinal : before.nextOrdinal = event.nextOrdinal
  suspendedIssued : suspended.all (fun owner => before.issued.contains owner) = true
  suspendedHeld : suspended.all (fun owner => event.held.contains owner) = true
  frame : Frame (spectators event suspended ++ valueOwners event.initial) interval.before before.bindings

def readBefore {sources caller dependencies program block start count}
    (event : SourceRuntimeContext.FoldEvent sources caller)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before : RuntimeStructuralAction.SourceState) (suspended : List Owner) :
    WorkM (Before event interval before suspended) := do
  exactWork (Exact.charge (16*(suspended.length+1)*
    (Raw.OwnerFlow.fields (suspended ++ event.held ++ before.issued)+1)))
  if history : before.nextOrdinal = event.nextOrdinal ∧
      suspended.all (fun owner => before.issued.contains owner) = true ∧
      suspended.all (fun owner => event.held.contains owner) = true then
    let frame ← readFrame (spectators event suspended ++ valueOwners event.initial) interval.before before.bindings
    return ⟨history.1,history.2.1,history.2.2,frame⟩
  else throw .request

structure After {sources caller dependencies program block start count}
    (event : SourceRuntimeContext.FoldEvent sources caller)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before after : RuntimeStructuralAction.SourceState) (beforeRetired afterRetired suspended : List Owner) where
  ordinal : after.nextOrdinal = event.finalOrdinal
  issued : after.issued = before.issued ++ event.allocated
  retired : afterRetired = beforeRetired ++ event.consumed
  frame : Frame (spectators event suspended ++ valueOwners event.value) interval.after after.bindings
  preserved : ∀ owner ∈ spectators event suspended,
    RuntimeOwnerMap.byOwner before.bindings owner = RuntimeOwnerMap.byOwner after.bindings owner

def readAfter {sources caller dependencies program block start count}
    (event : SourceRuntimeContext.FoldEvent sources caller)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before after : RuntimeStructuralAction.SourceState) (beforeRetired afterRetired suspended : List Owner) :
    WorkM (After event interval before after beforeRetired afterRetired suspended) := do
  let spectators := spectators event suspended
  exactWork (Exact.charge (32*(Raw.OwnerFlow.fields
    (before.issued ++ after.issued ++ event.allocated ++ beforeRetired ++ afterRetired ++ event.consumed)+
    after.nextOrdinal+event.finalOrdinal+1) +
    64*(Raw.OwnerFlow.fields spectators+1)*(before.bindings.length+after.bindings.length+1)))
  if history : after.nextOrdinal = event.finalOrdinal ∧ after.issued = before.issued ++ event.allocated ∧
      afterRetired = beforeRetired ++ event.consumed then
    let frame ← readFrame (spectators ++ valueOwners event.value) interval.after after.bindings
    if preserved : ∀ owner ∈ spectators,
        RuntimeOwnerMap.byOwner before.bindings owner = RuntimeOwnerMap.byOwner after.bindings owner then
      return ⟨history.1,history.2.1,history.2.2,frame,preserved⟩
    else throw .request
  else throw .request

end QleisliKernel.Qirf.RuntimeStaticFold
