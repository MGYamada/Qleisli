import Init.Data.List.Zip
import QleisliKernel.Qirf.SourceSequence
import QleisliKernel.Qirf.RuntimeInterval
import QleisliKernel.SourceTypes.SourceRuntimeScope

/-! A source occurrence retains its original ordered event and request
position. A selected static child is indexed in its own original body.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeSourceEvent
open QleisliKernel Finite SourceTypes
open SourceSequence (Position)

/-- The ordinal distinguishes equal-valued events and repeated offsets. The
lookup is an erased proof derived from the actual current head, not a new
runtime getElem? or a search by event/position values. -/
structure At {sources caller} (pairs : List (SourceRuntimeContext.Event sources caller × Position))
    (event : SourceRuntimeContext.Event sources caller) (position : Position) where
  ordinal : Nat
  selected : pairs[ordinal]? = some (event,position)

theorem At.inRange {sources caller pairs event position} (entry : @At sources caller pairs event position) :
    entry.ordinal < pairs.length := by
  obtain ⟨bounded,_⟩ := List.getElem?_eq_some_iff.mp entry.selected
  exact bounded

theorem At.eventAt {sources : Sources} {caller : String}
    {events : List (SourceRuntimeContext.Event sources caller)} {positions : List Position}
    {event : SourceRuntimeContext.Event sources caller} {position : Position}
    (entry : @At sources caller (events.zip positions) event position) :
    events[entry.ordinal]? = some event := (List.getElem?_zip_eq_some.mp entry.selected).1

theorem At.positionAt {sources : Sources} {caller : String}
    {events : List (SourceRuntimeContext.Event sources caller)} {positions : List Position}
    {event : SourceRuntimeContext.Event sources caller} {position : Position}
    (entry : @At sources caller (events.zip positions) event position) :
    positions[entry.ordinal]? = some position := (List.getElem?_zip_eq_some.mp entry.selected).2

inductive Origin {sources caller} (event : SourceRuntimeContext.Event sources caller)
    (position : Position) : Type where
  | direct {name} (source : SourceRuntimeScope.Subject sources caller name) (positions : List Position)
      (atEvent : At (source.events.zip positions) event position) : Origin event position
  | selected {name} (source : SourceRuntimeScope.Subject sources caller name) (outerPositions : List Position)
      {parentEvent : SourceRuntimeContext.StaticEvent sources caller}
      {children : List (SourceRuntimeContext.Event sources caller)} {outerPosition : Position}
      (parent : At (source.events.zip outerPositions) (.staticConditional parentEvent children) outerPosition)
      (body : SourceRuntimeTrace.StaticBody parentEvent)
      (original : RuntimeInterval.Computed (SourceRuntimeTrace.readStaticSource parentEvent) body)
      (positions : List Position) (count : positions.length = body.result.events.length)
      (atEvent : At (body.result.events.zip positions) event position) : Origin event position

/-- The original source event belongs to exactly this literal native interval. -/
structure Location {sources caller} (event : SourceRuntimeContext.Event sources caller) (start size : Nat) where
  position : Position
  startAt : position.start = start
  sizeAt : position.count = size
  origin : Origin event position

end QleisliKernel.Qirf.RuntimeSourceEvent
