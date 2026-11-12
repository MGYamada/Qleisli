import QleisliKernel.Qirf.RuntimeBodyOperationTraversal

/-! Bind a checked supplying graph's declared Meaning to the original
child invocation and mixed-kind formal in the source duty queue.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeFormalMeaningDuty
open QleisliKernel Finite SourceTypes GenericDutyQueue

private def key {sources caller} (event : SourceRuntimeContext.NamedEvent sources caller)
    (slot : Fin event.target.operationActuals.sourceActuals.length) : GenericOperation.RequirementKind :=
  .formalMeaning ⟨event.target.resolution.moduleName,event.target.resolution.declaration.name,
    event.target.operationActuals.sourceActuals[slot].actual.formal.ordinal⟩

structure ChildActual {sources caller} (event : SourceRuntimeContext.NamedEvent sources caller)
    (slot : Fin event.target.operationActuals.sourceActuals.length)
    (application : GenericOperation.ApplicationSource sources) where
  original : GenericOperation.ActualOperation sources
  member : original ∈ application.operationActuals
  formal : application.target.header.formals[original.original.ordinal]? =
    some event.target.operationActuals.sourceActuals[slot].actual.formal
  argument : application.written.arguments[original.original.ordinal]? =
    some event.target.operationActuals.sourceActuals[slot].actual.argument
  parameter : key event slot = .formalMeaning original.original

private def readChildActual {sources caller} (event : SourceRuntimeContext.NamedEvent sources caller)
    (slot : Fin event.target.operationActuals.sourceActuals.length)
    (application : GenericOperation.ApplicationSource sources) : WorkM (ChildActual event slot application) := do
  let actual := event.target.operationActuals.sourceActuals[slot].actual
  let fields := application.operationActuals.foldl (fun work candidate =>
    work+candidate.original.moduleName.utf8ByteSize+candidate.original.declarationName.utf8ByteSize+1) 0
  exactWork (Exact.charge (16*(fields+(application.operationActuals.length+1)*
    (event.target.resolution.moduleName.utf8ByteSize+event.target.resolution.declaration.name.utf8ByteSize+1)+
    application.target.header.formals.length+application.written.arguments.length+
    SourceTrace.Meter.tokenFields actual.argument.tokens+1)))
  let [candidate] := application.operationActuals.attach.filter (fun candidate =>
    key event slot == .formalMeaning candidate.val.original) | throw .request
  if parameter : key event slot = .formalMeaning candidate.val.original then
    let ordinal := candidate.val.original.ordinal
    let header := application.target.header.formals[ordinal]?
    let argument := application.written.arguments[ordinal]?
    let headerWork := fun (formal : StaticHeaders.Formal) => formal.name.utf8ByteSize+1+
      match formal.kind with | .operation tokens => SourceTrace.Meter.nameFields tokens | _ => 0
    exactWork (Exact.charge (16*((header.map headerWork).getD 0+headerWork actual.formal+
      (argument.map (fun value => SourceTrace.Meter.tokenFields value.tokens)).getD 0+1)))
    if formal : header = some actual.formal then
      if written : argument = some actual.argument then
        return ⟨candidate.val,candidate.property,formal,written,parameter⟩
      else throw .request
    else throw .request
  else throw .request

structure Match {sources catalogue rootOwner rootName caller}
    (queue : @GenericDutyQueue.Checked sources catalogue)
    (event : SourceRuntimeContext.NamedEvent sources caller)
    (slot : Fin event.target.operationActuals.sourceActuals.length)
    (parent : RuntimeOrdinaryBody.CallPath sources rootOwner rootName caller event.target.callerName)
    (request : SourceMeaning.Request sources)
    (entry : SourcePendingMeaning.Entry queue) where
  prior : RuntimeDutyInvocation.Identified queue parent
  child : RuntimeDutyInvocation.IdentifiedChild queue event parent prior
  record : RecordIndex catalogue
  invocation : Invocation catalogue record
  demand : Demand invocation
  subject : entry.subject = .demand invocation demand
  instanceId : invocation.id = child.invocation.id
  kind : demand.source.original.kind = key event slot
  actual : ChildActual event slot child.call.application.original
  required : entry.unconsumed = true
  originalRequest : SourceMeaning.Request sources
  original : demand.source.original.requirement = .meaning originalRequest
  specification : RuntimeOriginalMeaning.RequestMatch originalRequest request

private def readMatch {sources catalogue rootOwner rootName caller}
    (pending : @SourcePendingMeaning.Prepared sources catalogue)
    (event : SourceRuntimeContext.NamedEvent sources caller)
    (slot : Fin event.target.operationActuals.sourceActuals.length)
    (parent : RuntimeOrdinaryBody.CallPath sources rootOwner rootName caller event.target.callerName)
    (request : SourceMeaning.Request sources) :
    WorkM (Σ position : Fin pending.entries.length,
      Match pending.queue event slot parent request pending.entries[position]) := do
  let prior ← RuntimeDutyInvocation.identify pending.queue parent
  let child ← RuntimeDutyInvocation.identifyChild pending.queue event parent prior
  let depth := child.invocation.depth
  exactWork (Exact.charge (16*((depth+1)^2+pending.entries.length+1)))
  let id := child.invocation.id
  let expected := key event slot
  let entries := pending.entries.toArray
  let candidates ← (List.finRange pending.entries.length).filterM fun position => do
    let entry := entries[position.val]'(by simpa only [entries,List.size_toArray] using position.isLt)
    match entry.subject with
    | .demand invocation demand =>
      match demand.source.original.kind with
      | .formalMeaning formal =>
        exactWork (Exact.charge (16*((invocation.depth+1)^2+depth+
          formal.moduleName.utf8ByteSize+formal.declarationName.utf8ByteSize+
          event.target.resolution.moduleName.utf8ByteSize+event.target.resolution.declaration.name.utf8ByteSize+1)))
        return demand.source.original.kind == expected && invocation.id == id
      | _ => return false
    | _ => return false
  let [position] := candidates | throw .request
  let entry := pending.entries[position]
  match subject : entry.subject with
  | .demand invocation demand =>
    if instanceId : invocation.id = id then
      if kind : demand.source.original.kind = expected then
        if required : entry.unconsumed = true then
          match original : demand.source.original.requirement with
          | .meaning source =>
            let actual ← readChildActual event slot child.call.application.original
            let specification ← RuntimeOriginalMeaning.readRequestMatch source request
            return ⟨position,⟨prior,child,_,invocation,demand,subject,instanceId,kind,actual,required,
              source,original,specification.down⟩⟩
          | _ => throw .request
        else throw .request
      else throw .request
    else throw .request
  | _ => throw .request

abbrev Receipt {artifact owner name arguments request order runtime}
    {prepared : RuntimeBodyOperations.Prepared artifact owner name arguments request}
    (body : RuntimeBodyOperations.Traversed prepared order runtime) :=
  RuntimeGraphOperation.StagedReceipt (RuntimeBodyOperations.stagedConsumption artifact prepared.source.catalogue body.root)

private def AtSite {sources catalogue rootOwner rootName owner name context description graph origin}
    (site : @RuntimeGraphOperation.Site sources owner name context description graph origin)
    (path : RuntimeOrdinaryBody.CallPath sources rootOwner rootName owner name)
    (request : SourceMeaning.Request sources)
    {queue : @GenericDutyQueue.Checked sources catalogue} (entry : SourcePendingMeaning.Entry queue) : Type := by
  cases site with
  | supplying event slot same => exact Match queue event slot (same.symm ▸ path) request entry
  | _ => exact Empty

private def readAtSite {sources catalogue rootOwner rootName owner name context description graph origin}
    (pending : @SourcePendingMeaning.Prepared sources catalogue)
    (site : @RuntimeGraphOperation.Site sources owner name context description graph origin)
    (path : RuntimeOrdinaryBody.CallPath sources rootOwner rootName owner name)
    (request : SourceMeaning.Request sources) :
    WorkM (Σ position : Fin pending.entries.length, AtSite site path request pending.entries[position]) := by
  cases site with
  | supplying event slot same => exact readMatch pending event slot (same.symm ▸ path) request
  | _ => exact throw .request

def AtReceipt {artifact owner name arguments request order runtime}
    {prepared : RuntimeBodyOperations.Prepared artifact owner name arguments request}
    (body : RuntimeBodyOperations.Traversed prepared order runtime) (receipt : Receipt body)
    (position : Fin prepared.source.pending.entries.length) : Type :=
  match receipt.prepared.formal with
  | none => Empty
  | some formal => AtSite receipt.location.site receipt.location.path formal.request prepared.source.pending.entries[position]

def read {artifact owner name arguments request order runtime}
    {prepared : RuntimeBodyOperations.Prepared artifact owner name arguments request}
    (body : RuntimeBodyOperations.Traversed prepared order runtime) (receipt : Receipt body) :
    WorkM (Option (Σ position : Fin prepared.source.pending.entries.length, AtReceipt body receipt position)) := by
  unfold AtReceipt
  split
  · exact pure none
  · rename_i formal found
    exact some <$> readAtSite prepared.source.pending receipt.location.site receipt.location.path formal.request

end QleisliKernel.Qirf.RuntimeFormalMeaningDuty
