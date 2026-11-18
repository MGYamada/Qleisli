import QleisliKernel.Qirf.RuntimeContextRequest
import QleisliKernel.Qirf.RuntimeInterval
import QleisliKernel.SourceTypes.SourceRuntimeTrace

/-! Locate one written transform and its single forward-body request.
The literal transformed action and the original forward body still require
independent checking under the same native dependencies.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeTransformRequest
open Finite SourceTypes
abbrev Context := RuntimeContextRequest.Context

def noMeaning (context : Context) : Bool :=
  match context.references with
  | [] | [[]] => true
  | _ => false

structure Checked {sources caller} (event : SourceRuntimeContext.TransformEvent sources caller)
    (position : SourceSequence.Position) (request : Context) where
  offset : position.offset = event.call.calleeOffset
  empty : request.positions.isEmpty = true ∧ request.sites.isEmpty = true ∧
    request.calls.isEmpty = true ∧ request.branches.isEmpty = true
  references : noMeaning request = true
  subject : SourceProviderSubject.Subject
  context : Context
  forward : request.bodies = [(subject,context)]
  source : SourceRuntimeTrace.Body event.target.signature
  original : SourceRuntimeTrace.TransformRead event source

private def readWith {sources caller} (event : SourceRuntimeContext.TransformEvent sources caller)
    (position : SourceSequence.Position) (request : Context)
    (sourceRead : WorkM (Σ source : SourceRuntimeTrace.Body event.target.signature,
      SourceRuntimeTrace.TransformRead event source)) :
    WorkM (Checked event position request) := do
  exactWork (Exact.charge 16)
  if offset : position.offset = event.call.calleeOffset then
    if empty : request.positions.isEmpty = true ∧ request.sites.isEmpty = true ∧
        request.calls.isEmpty = true ∧ request.branches.isEmpty = true then
      if references : noMeaning request = true then
        match forward : request.bodies with
        | [(subject,context)] =>
          let ⟨source,original⟩ ← sourceRead
          return ⟨offset,empty,references,subject,context,forward,source,original⟩
        | _ => throw .request
      else throw .request
    else throw .request
  else throw .request

def read {sources caller} (event : SourceRuntimeContext.TransformEvent sources caller)
    (position : SourceSequence.Position) (request : Context) :
    WorkM (Checked event position request) :=
  readWith event position request do
    let source ← NaturalAffine.witness (SourceRuntimeTrace.readTransformBody event)
    return ⟨source.val,.replayed (by with_reducible exact source.property)⟩

/-- Select the forward body from the actual checked caller occurrence. The
request still undergoes the same position, shape and subject checks. -/
def readRetained {sources caller name} {event : SourceRuntimeContext.TransformEvent sources caller}
    (parent : SourceRuntimeTrace.Checked sources caller name)
    (path : SourceRuntimeContext.RuntimeCalleeTrace.Path parent.events (.transform event))
    (position : SourceSequence.Position) (request : Context) :
    WorkM (Checked event position request) :=
  readWith event position request do
    let source ← NaturalAffine.witness (SourceRuntimeTrace.readRetainedTransform parent path)
    return ⟨source.val,.retained parent path (by with_reducible exact source.property)⟩

/-- The request witness records the reader that actually ran. Either entry
point retains the exact original transform occurrence and forward body. -/
inductive Read {sources caller} (event : SourceRuntimeContext.TransformEvent sources caller)
    (position : SourceSequence.Position) (request : Context) (checked : Checked event position request) : Type where
  | replayed (original : RuntimeInterval.Computed (read event position request) checked) :
      Read event position request checked
  | retained {name : String} (parent : SourceRuntimeTrace.Checked sources caller name)
      (path : SourceRuntimeContext.RuntimeCalleeTrace.Path parent.events (.transform event))
      (original : RuntimeInterval.Computed (readRetained parent path position request) checked) :
      Read event position request checked

end QleisliKernel.Qirf.RuntimeTransformRequest
