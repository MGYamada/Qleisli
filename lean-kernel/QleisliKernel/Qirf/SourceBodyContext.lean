import QleisliKernel.Qirf.SourceBodyHeader

/-! Check every literal source body under the same final root dependencies.
Selection equations use the actual containing program, including an arm's
realized entry implementation; no replacement root is constructed.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceBodyContext
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Qirf Finite
open PureInterval (Witness)
abbrev Context := SourceContextRequest.Context

def interval {artifact owner name dependencies program positions}
    {source : SourceTrace.Checked artifact.sources owner name}
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

structure LocalChecked {artifact owner name source request}
    (header : @SourceBodyHeader.Header artifact owner name source request) (root : Validity.Root)
    {nodes : List Nat}
    (fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes root.receipts)
    (program : Semantics.Observation.Program) where
  trace : Witness (RawTrace.check source root.dependencies program request.positions)
  locals : List (Local header root fresh trace.val)
  everyEvent : locals.map (·.bound.event) = source.result.events.filterMap ContextSector.selection
  everyRequest : locals.map (·.site.request) = request.sites

def checkLocal {artifact owner name source request}
    (header : @SourceBodyHeader.Header artifact owner name source request) (root : Validity.Root)
    {nodes : List Nat}
    (fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes root.receipts)
    (program : Semantics.Observation.Program) : WorkM (LocalChecked header root fresh program) := do
  let trace ← NaturalAffine.witness (RawTrace.check source root.dependencies program request.positions)
  let selected ← ContextSector.collect trace.val.sites
  guard (header.sites.length == selected.length) .request
  let locals ← (header.sites.zip selected).mapM (readLocal header root fresh trace.val)
  if everyEvent : locals.map (·.bound.event) = source.result.events.filterMap ContextSector.selection then
    if everyRequest : locals.map (·.site.request) = request.sites then
      return ⟨trace,locals,everyEvent,everyRequest⟩
    else throw .request
  else throw .request

structure CallSite {sources owner name} (source : SourceTrace.Checked sources owner name)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (whole : PureInterval.Slice program 0 program.operations.length) where
  event : SourceCalls.Event sources owner
  position : SourceSequence.Position
  site : RawTrace.Site source dependencies program whole (.named event) position

def CallSite.action {sources owner name source dependencies program whole}
    (site : @CallSite sources owner name source dependencies program whole) :
    RawTrace.NamedAction site.event dependencies program site.position site.site.inputs site.site.outputs :=
  site.site.action

def collectCalls {sources owner name dependencies program whole events positions}
    {source : SourceTrace.Checked sources owner name}
    (sites : RawTrace.Sites source dependencies program whole events positions) :
    WorkM (List (CallSite source dependencies program whole)) :=
  let traverse : Nat → {events : List (SourceTrace.Event sources owner)} → {positions : List SourceSequence.Position} →
      RawTrace.Sites source dependencies program whole events positions →
      WorkM (List (CallSite source dependencies program whole)) :=
    Nat.rec (fun {_} {_} _ => throw .limit) (fun _ next {_} {_} sites => do
      exactWork (Exact.charge 1)
      match sites with
      | .nil => return []
      | .cons (event := event) (position := position) site rest =>
        let collected ← next rest
        match event with
        | .named event => return ⟨event,position,site⟩ :: collected
        | _ => return collected)
  traverse (events.length+1) sites

/-- A child's source is read again through the common checked-signature reader,
and its literal program is the actual parent's call interval. Recursive source
queries were already discovered before the one final graph was accepted. -/
def walkCalls {artifact} (root : Validity.Root) {nodes : List Nat}
    (fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes root.receipts) :
    Nat → {owner name : String} → {source : SourceTrace.Checked artifact.sources owner name} →
    (request : Context) → {program : Semantics.Observation.Program} →
    RawTrace.Checked source root.dependencies program request.positions → WorkM Unit
  | 0,_,_,_,request,_,trace => do
    let calls ← collectCalls trace.sites
    guard (calls.isEmpty && request.calls.isEmpty) .limit
  | fuel+1,_,_,_,request,_,trace => do
    let calls ← collectCalls trace.sites
    exactWork (Exact.charge (16*(calls.length+request.calls.length+1)))
    guard (calls.length == request.calls.length) .request
    let _ ← (calls.zip request.calls).mapM fun (site,requested) => do
      guard (site.position == requested.1) .request
      let child ← SourceBodyHeader.readCall artifact site.event requested
      let checkedBody ← checkLocal child.header root fresh site.action.program
      walkCalls root fresh fuel child.request checkedBody.trace.val
    return ()

structure Checked {artifact owner name source request}
    (header : @SourceBodyHeader.Header artifact owner name source request) (root : Validity.Root)
    {nodes : List Nat}
    (fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes root.receipts)
    (program : Semantics.Observation.Program) where
  context : LocalChecked header root fresh program
  calls : Witness (walkCalls root fresh 128 request context.trace.val)

def Checked.trace {artifact owner name source request header root nodes fresh program}
    (checked : @Checked artifact owner name source request header root nodes fresh program) := checked.context.trace

def check {artifact owner name source request}
    (header : @SourceBodyHeader.Header artifact owner name source request) (root : Validity.Root)
    {nodes : List Nat}
    (fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes root.receipts)
    (program : Semantics.Observation.Program) : WorkM (Checked header root fresh program) := do
  let context ← checkLocal header root fresh program
  let calls ← NaturalAffine.witness (walkCalls root fresh 128 request context.trace.val)
  return ⟨context,calls⟩

structure ArmChecked {artifact order rows roots}
    (root : Witness (Validity.checkRootFromRoots artifact order rows roots))
    (arm : SourceBodyHeader.Arm artifact) where
  pureSource : SourceTrace.inferredEffect arm.source.val.checked.result.events = .unitary
  realized : SourceArm.Realized artifact root.val.receipts arm.bound
  body : Checked arm.header root.val (SelectionContract.rootFresh root) realized.receipt.input.implementation

def checkArm {artifact order rows roots}
    (root : Witness (Validity.checkRootFromRoots artifact order rows roots))
    (arm : SourceBodyHeader.Arm artifact) : WorkM (ArmChecked root arm) := do
  if pureSource : SourceTrace.inferredEffect arm.source.val.checked.result.events = .unitary then
    let realized ← SourceArm.realize artifact root.val.receipts arm.bound (SelectionContract.rootFresh root)
    let body ← check arm.header root.val (SelectionContract.rootFresh root) realized.receipt.input.implementation
    return ⟨pureSource,realized,body⟩
  else throw .request

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
