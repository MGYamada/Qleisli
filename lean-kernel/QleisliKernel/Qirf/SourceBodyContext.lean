import QleisliKernel.Qirf.SourceBodyHeader

/-! Check every literal source body under the same final root dependencies.
Selection equations use the actual containing program, including an arm's
realized entry implementation; no replacement root is constructed.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceBodyContext
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Qirf Finite
open PureInterval (Witness)
abbrev Context := SourceContextRequest.Context

def interval {sources owner name dependencies program positions}
    {source : SourceTrace.Checked sources owner name}
    (trace : RawTrace.Checked source dependencies program positions)
    (site : SelectionCore.Header artifact source.signature)
    (bound : ContextSector.SelectionSite source dependencies program trace.whole)
    (event : site.event = bound.event) (position : site.request.position = bound.position) :
    PureInterval.Many.Checked 2 dependencies program site.request.position.start site.request.position.count
      bound.site.inputs bound.site.outputs [site.event.selector,site.event.target] := by
  simpa only [event,position,RawTrace.Action] using bound.site.action

structure Local {artifact owner name source request}
    (header : @SourceBodyHeader.Header artifact owner name source request) (root : Validity.Root)
    {nodes : List Nat}
    (fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes root.receipts)
    {program : Semantics.Observation.Program}
    (trace : RawTrace.Checked source root.dependencies program request.positions) where
  site : SelectionCore.Header artifact source.signature
  bound : ContextSector.SelectionSite source root.dependencies program trace.whole
  event : site.event = bound.event
  position : site.request.position = bound.position
  checked : SelectionCore.Checked site root fresh (interval trace site bound event position)

def readLocal {artifact owner name source request}
    (header : @SourceBodyHeader.Header artifact owner name source request) (root : Validity.Root)
    {nodes : List Nat}
    (fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes root.receipts)
    {program : Semantics.Observation.Program}
    (trace : RawTrace.Checked source root.dependencies program request.positions)
    (pair : SelectionCore.Header artifact source.signature ×
      ContextSector.SelectionSite source root.dependencies program trace.whole) :
    WorkM (Local header root fresh trace) := do
  let site := pair.1
  let bound := pair.2
  exactWork (Exact.charge (64*(SourceSequence.eventFields site.event+
    SourceSequence.eventFields bound.event+1)))
  if event : site.event = bound.event then
    if position : site.request.position = bound.position then
      let checked ← SelectionCore.check site root fresh (interval trace site bound event position)
      return ⟨site,bound,event,position,checked⟩
    else throw .request
  else throw .request

structure Checked {artifact owner name source request}
    (header : @SourceBodyHeader.Header artifact owner name source request) (root : Validity.Root)
    {nodes : List Nat}
    (fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes root.receipts)
    (program : Semantics.Observation.Program) where
  trace : Witness (RawTrace.check source root.dependencies program request.positions)
  locals : List (Local header root fresh trace.val)
  everyEvent : locals.map (·.bound.event) = source.result.events.filterMap ContextSector.selection
  everyRequest : locals.map (·.site.request) = request.sites

def check {artifact owner name source request}
    (header : @SourceBodyHeader.Header artifact owner name source request) (root : Validity.Root)
    {nodes : List Nat}
    (fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes root.receipts)
    (program : Semantics.Observation.Program) : WorkM (Checked header root fresh program) := do
  -- Named calls receive the same recursive continuation once their original
  -- signature/return bridge is available. Extra unconsumed nodes never pass.
  guard request.calls.isEmpty .request
  let trace ← NaturalAffine.witness (RawTrace.check source root.dependencies program request.positions)
  let selected ← ContextSector.collect trace.val.sites
  guard (header.sites.length == selected.length) .request
  let locals ← (header.sites.zip selected).mapM (readLocal header root fresh trace.val)
  if everyEvent : locals.map (·.bound.event) = source.result.events.filterMap ContextSector.selection then
    if everyRequest : locals.map (·.site.request) = request.sites then
      return ⟨trace,locals,everyEvent,everyRequest⟩
    else throw .request
  else throw .request

structure ArmChecked {artifact order rows roots}
    (root : Witness (Validity.checkRootFromRoots artifact order rows roots))
    (arm : SourceBodyHeader.Arm artifact) where
  realized : SourceArm.Realized artifact root.val.receipts arm.bound
  body : Checked arm.header root.val (SelectionContract.rootFresh root) realized.receipt.input.implementation

def checkArm {artifact order rows roots}
    (root : Witness (Validity.checkRootFromRoots artifact order rows roots))
    (arm : SourceBodyHeader.Arm artifact) : WorkM (ArmChecked root arm) := do
  let realized ← SourceArm.realize artifact root.val.receipts arm.bound (SelectionContract.rootFresh root)
  let body ← check arm.header root.val (SelectionContract.rootFresh root) realized.receipt.input.implementation
  return ⟨realized,body⟩

/-- The same historical receipt recovered from the one successful graph is
both the original body-check subject and the implementation/specification
execution witness under the final dependencies. -/
theorem ArmChecked.originalExecution {artifact order rows roots}
    {root : Witness (Validity.checkRootFromRoots artifact order rows roots)}
    {arm : SourceBodyHeader.Arm artifact} (checked : ArmChecked root arm) :
    artifact.programs[arm.bound.binding.entry.implementation]? = some checked.realized.receipt.input.implementation ∧
    ReceiptTransport.Executes root.val.dependencies checked.realized.receipt.input.implementation
      checked.realized.receipt.meaning ∧
    ReceiptTransport.Executes root.val.dependencies checked.realized.receipt.input.specification
      checked.realized.receipt.meaning := by
  obtain ⟨implementation,_,actual,specified⟩ :=
    ReceiptTransport.realized_execution root arm.bound checked.realized
  exact ⟨implementation,actual,specified⟩

end QleisliKernel.Qirf.SourceBodyContext
