import QleisliKernel.Qirf.RuntimeNamedCallsSource
import QleisliKernel.Qirf.RuntimeNamedCallFrame

/-! Ordinary pure named calls inside the same ordered caller. The existing
common body walk checks the authentic literal callee scope and actual source
path. Its returned owner history crosses the existing named boundary; neither
a header effect nor a native output-set probe supplies a callee result order.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNamedOrdinaryLocal
open QleisliKernel Finite SourceTypes
open QleisliKernel.SourceTypes.SourceRuntimeValues (valueOwners)
abbrev SourceState := RuntimeStructuralAction.SourceState

def path {artifact owner name arguments source event position}
    (ordinary : @RuntimeNamedCallsSource.Ordinary artifact owner name arguments source event position) :
    RuntimeOrdinaryBody.CallPath artifact.sources owner name event.target.resolution.moduleName
      event.target.resolution.declaration.name :=
  let parent : RuntimeOrdinaryBody.CallPath artifact.sources owner name owner event.target.callerName := by
    simpa only [ordinary.callerName] using (RuntimeOrdinaryBody.CallPath.root source.body)
  RuntimeOrdinaryBody.CallPath.named event ordinary.body ordinary.bodyRead parent

structure Checked {artifact owner name arguments source event position}
    (ordinary : @RuntimeNamedCallsSource.Ordinary artifact owner name arguments source event position)
    (root : Validity.Root) {program : Semantics.Observation.Program}
    (block : RuntimeInterval.Block root.dependencies program) (before : SourceState) where
  frame : RuntimeNamedCallFrame.Checked event ordinary.body block position before
  frameRead : RuntimeInterval.Computed (RuntimeNamedCallFrame.read event ordinary.body block position before) frame
  initial : SourceState
  initialRead : initial = ⟨frame.initial,ordinary.body.checked.summary.parameterValues.flatMap valueOwners,
    ordinary.body.checked.summary.nextOwner⟩
  nested : RuntimePureBody.BlockResult root.dependencies frame.scope.program frame.scope.prepared.block
  nestedRead : RuntimeInterval.Computed (RuntimePureBody.runBlock artifact root 128 .pureBody .localScope
    (.whole ordinary.body) (path ordinary) frame.scope.program ordinary.context initial {} frame.scope.prepared.block) nested
  boundary : RuntimeNamedBoundary.Checked frame.scope.interval (frame.inputs.map (·.port.token)) event before
    nested.history nested.retired ordinary.body.checked.summary.value
  boundaryRead : RuntimeInterval.Computed (RuntimeNamedBoundary.read frame.scope.interval
    (frame.inputs.map (·.port.token)) event before nested.history nested.retired ordinary.body.checked.summary.value) boundary

def read {artifact owner name arguments source event position}
    (ordinary : @RuntimeNamedCallsSource.Ordinary artifact owner name arguments source event position)
    (root : Validity.Root) {program : Semantics.Observation.Program}
    (block : RuntimeInterval.Block root.dependencies program) (before : SourceState) :
    WorkM (Checked ordinary root block before) := do
  let frame ← NaturalAffine.witness (RuntimeNamedCallFrame.read event ordinary.body block position before)
  let initial : SourceState := ⟨frame.val.initial,ordinary.body.checked.summary.parameterValues.flatMap valueOwners,
    ordinary.body.checked.summary.nextOwner⟩
  let nested ← NaturalAffine.witness (RuntimePureBody.runBlock artifact root 128 .pureBody .localScope
    (.whole ordinary.body) (path ordinary) frame.val.scope.program ordinary.context initial {} frame.val.scope.prepared.block)
  let boundary ← NaturalAffine.witness (RuntimeNamedBoundary.read frame.val.scope.interval
    (frame.val.inputs.map (·.port.token)) event before nested.val.history nested.val.retired ordinary.body.checked.summary.value)
  return ⟨frame.val,by with_reducible exact frame.property,initial,rfl,nested.val,
    by with_reducible exact nested.property,boundary.val,by with_reducible exact boundary.property⟩

def Checked.node {artifact owner name arguments source event position ordinary root program block before}
    (checked : @Checked artifact owner name arguments source event position ordinary root program block before) :
    RuntimePureBody.Node root.dependencies program block :=
  .named event checked.frame.scope ordinary.body ordinary.bodyRead
    checked.boundary (RuntimePureBody.Nodes.ofList checked.nested.actions)

end QleisliKernel.Qirf.RuntimeNamedOrdinaryLocal
