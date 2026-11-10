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
  original : RuntimeInterval.Computed (SourceRuntimeTrace.readTransformBody event) source

def read {sources caller} (event : SourceRuntimeContext.TransformEvent sources caller)
    (position : SourceSequence.Position) (request : Context) :
    WorkM (Checked event position request) := do
  exactWork (Exact.charge 16)
  if offset : position.offset = event.call.calleeOffset then
    if empty : request.positions.isEmpty = true ∧ request.sites.isEmpty = true ∧
        request.calls.isEmpty = true ∧ request.branches.isEmpty = true then
      if references : noMeaning request = true then
        match forward : request.bodies with
        | [(subject,context)] =>
          let source ← NaturalAffine.witness (SourceRuntimeTrace.readTransformBody event)
          return ⟨offset,empty,references,subject,context,forward,source.val,
            by with_reducible exact source.property⟩
        | _ => throw .request
      else throw .request
    else throw .request
  else throw .request

end QleisliKernel.Qirf.RuntimeTransformRequest
