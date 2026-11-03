import QleisliKernel.Qirf.RuntimeNamedSelectionOccurrence
import QleisliKernel.Qirf.RuntimeNamedCallFrame

/-! An original named selection at its genuine internal caller interval.
The surrounding traversal supplies the actual current source/native frame.
Only the selected ports enter the canonical callee program; caller spectators
remain in the parent interval. No whole-caller input, return or singleton-body
claim is manufactured by this local adapter.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNamedSelectionLocal
open QleisliKernel Finite SourceTypes
open QleisliKernel.SourceTypes.SourceRuntimeValues (valueOwners owners)
abbrev Map := RuntimeOwnerMap.Map
abbrev SourceState := RuntimeStructuralAction.SourceState

/-- Both ordinary and selection callees use the same actual current frame.
The original occurrence continues to own the exact event/callee provenance. -/
abbrev Frame {artifact owner name arguments source request}
    (occurrence : @RuntimeNamedSelectionOccurrence.Prepared artifact owner name arguments source request)
    (root : Validity.Root) {program : Semantics.Observation.Program}
    (block : RuntimeInterval.Block root.dependencies program) (before : SourceState) :=
  RuntimeNamedCallFrame.Checked occurrence.parts.event occurrence.call.callee block occurrence.parts.position before

def prepare {artifact owner name arguments source request}
    (occurrence : @RuntimeNamedSelectionOccurrence.Prepared artifact owner name arguments source request)
    (root : Validity.Root) {program : Semantics.Observation.Program}
    (block : RuntimeInterval.Block root.dependencies program) (before : SourceState) :
    WorkM (Frame occurrence root block before) :=
  RuntimeNamedCallFrame.read occurrence.parts.event occurrence.call.callee block occurrence.parts.position before

/-- A source-ordered caller may provide the exact prepared selection call
without a singleton occurrence wrapper. All prefix/body/return checks remain
identical and are indexed by that full original call object. -/
structure CallChecked {artifact owner name arguments source event position context references}
    (call : @RuntimeNamedSelectionSource.Call artifact owner name arguments source event position context references)
    (root : Validity.Root) {program : Semantics.Observation.Program}
    (block : RuntimeInterval.Block root.dependencies program) (before : SourceState) where
  supplies : RuntimeNamedSelectionPrefix.Checked call.supplies root
  suppliesRead : RuntimeInterval.Computed (RuntimeNamedSelectionPrefix.read call.supplies root) supplies
  frame : RuntimeNamedCallFrame.Checked event call.callee block position before
  frameRead : RuntimeInterval.Computed (RuntimeNamedCallFrame.read event call.callee block position before) frame
  child : RuntimeSelectionMeaning.LocalChecked call.selection root frame.scope.prepared frame.initial
  childRead : RuntimeInterval.Computed
    (RuntimeSelectionMeaning.readAt call.selection root frame.scope.prepared frame.initial) child
  boundary : RuntimeNamedBoundary.Checked frame.scope.interval (frame.inputs.map (·.port.token))
    event before child.history child.retired child.value
  boundaryRead : RuntimeInterval.Computed (RuntimeNamedBoundary.read frame.scope.interval
    (frame.inputs.map (·.port.token)) event before child.history child.retired child.value) boundary

def readCall {artifact owner name arguments source event position context references}
    (call : @RuntimeNamedSelectionSource.Call artifact owner name arguments source event position context references)
    (root : Validity.Root) {program : Semantics.Observation.Program}
    (block : RuntimeInterval.Block root.dependencies program) (before : SourceState) :
    WorkM (CallChecked call root block before) := do
  let supplies ← NaturalAffine.witness (RuntimeNamedSelectionPrefix.read call.supplies root)
  let frame ← NaturalAffine.witness (RuntimeNamedCallFrame.read event call.callee block position before)
  let child ← NaturalAffine.witness
    (RuntimeSelectionMeaning.readAt call.selection root frame.val.scope.prepared frame.val.initial)
  let boundary ← NaturalAffine.witness (RuntimeNamedBoundary.read frame.val.scope.interval
    (frame.val.inputs.map (·.port.token)) event before child.val.history child.val.retired child.val.value)
  return ⟨supplies.val,by with_reducible exact supplies.property,frame.val,by with_reducible exact frame.property,
    child.val,by with_reducible exact child.property,boundary.val,by with_reducible exact boundary.property⟩

def CallChecked.node {artifact owner name arguments source event position context references call root program block before}
    (checked : @CallChecked artifact owner name arguments source event position context references call root program block before) :
    RuntimePureBody.Node root.dependencies program block :=
  .named event checked.frame.scope call.callee call.calleeRead checked.frame.scope.prepared.block
    checked.boundary (RuntimePureBody.Nodes.ofList [checked.child.node])

abbrev Checked {artifact owner name arguments source request}
    (occurrence : @RuntimeNamedSelectionOccurrence.Prepared artifact owner name arguments source request)
    (root : Validity.Root) {program : Semantics.Observation.Program}
    (block : RuntimeInterval.Block root.dependencies program) (before : SourceState) :=
  CallChecked occurrence.call root block before

/-- The original singleton/surrounding occurrence API keeps the same genuine
call object and actual read; it is not a fallback or another body evaluator. -/
def read {artifact owner name arguments source request}
    (occurrence : @RuntimeNamedSelectionOccurrence.Prepared artifact owner name arguments source request)
    (root : Validity.Root) {program : Semantics.Observation.Program}
    (block : RuntimeInterval.Block root.dependencies program) (before : SourceState) :
    WorkM (Checked occurrence root block before) := readCall occurrence.call root block before

def Checked.node {artifact owner name arguments source request occurrence root program block before}
    (checked : @Checked artifact owner name arguments source request occurrence root program block before) :
    RuntimePureBody.Node root.dependencies program block := CallChecked.node checked

end QleisliKernel.Qirf.RuntimeNamedSelectionLocal
