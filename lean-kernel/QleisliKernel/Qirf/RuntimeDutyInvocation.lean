import QleisliKernel.Qirf.RuntimeOrdinaryBody
import QleisliKernel.Qirf.RuntimeStructuredRoot
import QleisliKernel.Qirf.SourcePendingMeaning

/-! Bind a concrete original call path to an invocation of the independently
expanded source-duty queue. Every edge keeps its actual source occurrence and
prepared simultaneous substitution. This does not evaluate generic subjects,
discharge a Meaning equation, or turn external root arguments into a closed
generic root premise.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeDutyInvocation
open QleisliKernel Finite SourceTypes GenericDutyQueue
open RuntimeOrdinaryBody (CallPath)

private theorem sameOriginal {sources a b c d}
    (first : OrdinarySignature.Original sources a b) (second : OrdinarySignature.Original sources c d)
    (owner : a = c) (name : b = d) : HEq first second := by
  cases owner
  cases name
  exact heq_of_eq (first.sameSource second)

private def signature {sources rootOwner rootName owner name} :
    CallPath sources rootOwner rootName owner name → SourceRuntimeContext.Signature sources owner name
  | .root (signature := original) _ => original
  | .named event .. => event.target.signature

private def contextFields : StaticOperation.Context → Nat
  | .external => 1
  | .source owner => owner.utf8ByteSize+1

/-- Compare the full set of shadowing names used at an original occurrence. -/
def sameScope (left right : List String) : Bool :=
  left.all right.contains && right.all left.contains

theorem sameScope_members {left right : List String} (same : sameScope left right = true) :
    ∀ name, name ∈ left ↔ name ∈ right := by
  simp only [sameScope,Bool.and_eq_true,List.all_eq_true,List.contains_iff_mem] at same
  exact fun name => ⟨same.1 name,same.2 name⟩

/-- Static written arguments retain their complete original token spans.
The lexical call-name reader tests membership, including consumed names.
The two full scopes induce the same shadowing relation at this occurrence.
The selected declarations and the caller's actual supply context are bound
separately; scope membership alone cannot identify a supplying invocation. -/
structure CallMatch {sources rootOwner rootName caller}
    (event : SourceRuntimeContext.NamedEvent sources caller)
    (parent : CallPath sources rootOwner rootName caller event.target.callerName)
    (source : GenericOperation.ApplicationSource sources) : Type where
  tokens : source.tokens = event.call.call.callee
  scope : ∀ name, name ∈ source.scope ↔ name ∈ event.scope
  written : source.written.arguments = event.target.written.arguments
  actuals : (signature parent).arguments = event.target.callerSignature.arguments
  context : (signature parent).context = event.target.callerSignature.context
  callerOwner : source.state.owner = caller
  callerName : source.state.name = event.target.callerName
  calleeOwner : source.owner = event.target.resolution.moduleName
  calleeName : source.name = event.target.resolution.declaration.name
  callerOriginal : HEq source.state.prepared.original.envelope event.target.callerSignature.original
  calleeOriginal : HEq source.target.envelope event.target.signature.original

private def matchCall {sources rootOwner rootName caller}
    (event : SourceRuntimeContext.NamedEvent sources caller)
    (parent : CallPath sources rootOwner rootName caller event.target.callerName)
    (source : GenericOperation.ApplicationSource sources) : WorkM (Option (CallMatch event parent source)) := do
  let scopeWork := (SourceTrace.Meter.nameFields source.scope+SourceTrace.Meter.nameFields event.scope+1)*
    (source.scope.length+event.scope.length+1)
  exactWork (Exact.charge (16*(scopeWork+SourceTrace.Meter.tokenFields source.tokens+
    SourceTrace.Meter.tokenFields event.call.call.callee+RuntimeStructuredRoot.argumentFields (signature parent).arguments+
    contextFields (signature parent).context+contextFields event.target.callerSignature.context+
    RuntimeStructuredRoot.argumentFields event.target.callerSignature.arguments+source.state.owner.utf8ByteSize+
    source.state.name.utf8ByteSize+source.owner.utf8ByteSize+source.name.utf8ByteSize+caller.utf8ByteSize+
    event.target.callerName.utf8ByteSize+event.target.resolution.moduleName.utf8ByteSize+
    event.target.resolution.declaration.name.utf8ByteSize+1)))
  if names : source.state.owner = caller ∧ source.state.name = event.target.callerName ∧
      source.owner = event.target.resolution.moduleName ∧ source.name = event.target.resolution.declaration.name then
    if same : source.tokens = event.call.call.callee ∧ sameScope source.scope event.scope = true ∧
        source.written.arguments = event.target.written.arguments ∧
        (signature parent).arguments = event.target.callerSignature.arguments ∧
        (signature parent).context = event.target.callerSignature.context then
      return some ⟨same.1,sameScope_members same.2.1,same.2.2.1,same.2.2.2.1,same.2.2.2.2,
        names.1,names.2.1,names.2.2.1,names.2.2.2,
        sameOriginal _ _ names.1 names.2.1,sameOriginal _ _ names.2.2.1 names.2.2.2⟩
    else return none
  else return none

abbrev Edge {sources catalogue record rootOwner rootName caller}
    (event : SourceRuntimeContext.NamedEvent sources caller)
    (parent : CallPath sources rootOwner rootName caller event.target.callerName)
    (application : @ApplicationAt sources catalogue record) :=
  CallMatch event parent application.original

private def matchEdge {sources catalogue record rootOwner rootName caller}
    (event : SourceRuntimeContext.NamedEvent sources caller)
    (parent : CallPath sources rootOwner rootName caller event.target.callerName)
    (application : @ApplicationAt sources catalogue record) : WorkM (Option (Edge event parent application)) :=
  matchCall event parent application.original

structure Supplying {sources rootOwner rootName caller}
    (event : SourceRuntimeContext.NamedEvent sources caller)
    (index : Fin event.target.operationActuals.sourceActuals.length)
    (parent : CallPath sources rootOwner rootName caller event.target.callerName)
    (duty : GenericOperation.Duty sources) where
  binding : GenericOperation.Binding sources
  original : duty.bindings = [binding]
  application : GenericOperation.ApplicationSource sources
  retained : binding.application = some application
  call : CallMatch event parent application
  actual : binding.formal = event.target.operationActuals.sourceActuals[index].actual.formal ∧
    binding.actual.tokens = event.target.operationActuals.sourceActuals[index].actual.argument.tokens
  scope : ∀ name, name ∈ binding.actual.scope ↔ name ∈ event.scope
  callerOriginal : HEq binding.actual.state.prepared.original.envelope event.target.callerSignature.original
  calleeOriginal : HEq binding.original.envelope event.target.signature.original

/-- Associate the written duty with its exact original mixed argument. The
marker inside that argument is checked independently against the native graph. -/
def readSupplying {sources rootOwner rootName caller}
    (event : SourceRuntimeContext.NamedEvent sources caller)
    (index : Fin event.target.operationActuals.sourceActuals.length)
    (parent : CallPath sources rootOwner rootName caller event.target.callerName)
    (duty : GenericOperation.Duty sources) : WorkM (Supplying event index parent duty) := do
  match original : duty.bindings with
  | [binding] =>
    match retained : binding.application with
    | some application =>
      let some call ← matchCall event parent application | throw .request
      let actual := event.target.operationActuals.sourceActuals[index].actual
      let callerOriginal := binding.actual.state.prepared.original.envelope
      let formalWork := fun (formal : StaticHeaders.Formal) =>
        formal.name.utf8ByteSize+1+match formal.kind with
          | .operation tokens => SourceTrace.Meter.nameFields tokens
          | _ => 0
      let scopeWork := (SourceTrace.Meter.nameFields binding.actual.scope+SourceTrace.Meter.nameFields event.scope+1)*
        (binding.actual.scope.length+event.scope.length+1)
      exactWork (Exact.charge (16*(scopeWork+index.val+SourceTrace.Meter.tokenFields
        (binding.actual.tokens ++ actual.argument.tokens)+
        formalWork binding.formal+formalWork actual.formal+
        binding.owner.utf8ByteSize+binding.name.utf8ByteSize+
        binding.actual.state.owner.utf8ByteSize+binding.actual.state.name.utf8ByteSize+
        caller.utf8ByteSize+event.target.callerName.utf8ByteSize+
        event.target.resolution.moduleName.utf8ByteSize+event.target.resolution.declaration.name.utf8ByteSize+1)))
      if exactActual : binding.formal = actual.formal ∧ binding.actual.tokens = actual.argument.tokens then
        if scope : sameScope binding.actual.scope event.scope = true then
          if names : binding.actual.state.owner = caller ∧ binding.actual.state.name = event.target.callerName ∧
              binding.owner = event.target.resolution.moduleName ∧ binding.name = event.target.resolution.declaration.name then
            return ⟨binding,original,application,retained,call,exactActual,sameScope_members scope,
              sameOriginal callerOriginal _ names.1 names.2.1,
              sameOriginal binding.original.envelope _ names.2.2.1 names.2.2.2⟩
          else throw .request
        else throw .request
      else throw .request
    | none => throw .request
  | _ => throw .request

private def readEdge {sources catalogue record rootOwner rootName caller}
    (event : SourceRuntimeContext.NamedEvent sources caller)
    (parent : CallPath sources rootOwner rootName caller event.target.callerName)
    (application : @ApplicationAt sources catalogue record) : WorkM (Edge event parent application) := do
  let some edge ← matchEdge event parent application | throw .request
  return edge

inductive Binding {sources catalogue} (queue : @GenericDutyQueue.Checked sources catalogue)
    {rootOwner rootName} : {owner name : String} → CallPath sources rootOwner rootName owner name →
    {record : RecordIndex catalogue} → Invocation catalogue record → Type where
  | root {signature : SourceRuntimeContext.Signature sources rootOwner rootName}
      (body : SourceRuntimeTrace.Body signature) (record : RecordIndex catalogue)
      (selected : GenericCatalogueIndex.Selection queue.prepared.index signature.original)
      (original : RuntimeInterval.Computed (GenericCatalogueIndex.read queue.prepared.index signature.original) selected)
      (same : selected.entry.index = record) : Binding queue (.root body) (.root record)
  | named {caller record} {event : SourceRuntimeContext.NamedEvent sources caller}
      {body : SourceRuntimeTrace.Body event.target.signature}
      {original : RuntimeInterval.Computed (SourceRuntimeTrace.readNamedBody event) body}
      {parent : CallPath sources rootOwner rootName caller event.target.callerName}
      {invocation : Invocation catalogue record} {application : ApplicationAt catalogue record}
      {target : GenericDutyQueue.Target application}
      (prior : Binding queue parent invocation) (edge : Edge event parent application) :
      Binding queue (.named event body original parent) (.call invocation application target)

/-- Select the genuine root catalogue entry and compare every edge of this
candidate invocation. There is no search for an equal descriptor or matrix. -/
def read {sources catalogue} (queue : @GenericDutyQueue.Checked sources catalogue) {rootOwner rootName owner name}
    (path : CallPath sources rootOwner rootName owner name) {record} (invocation : Invocation catalogue record) :
    WorkM (Binding queue path invocation) :=
  WellFounded.fix (measure (fun packed : CallPath.Packed sources rootOwner rootName => sizeOf packed.2.2)).wf
    (C := fun packed => {record : RecordIndex catalogue} → (invocation : Invocation catalogue record) →
      WorkM (Binding queue packed.2.2 invocation))
    (fun packed => match packed with
      | ⟨_,_,.root (signature := signature) body⟩ => fun _ {_} invocation => do
        match invocation with
        | .root record =>
          let selected ← NaturalAffine.witness (GenericCatalogueIndex.read queue.prepared.index signature.original)
          if same : selected.val.entry.index = record then
            return .root body record selected.val (by with_reducible exact selected.property) same
          else throw .request
        | .call .. => throw .request
      | ⟨_,_,.named event _ _ parent⟩ => fun visit {_} invocation => do
        match invocation with
        | .root _ => throw .request
        | .call caller application _ =>
          let edge ← readEdge event parent application
          let prior ← visit ⟨_,_,parent⟩ (by decreasing_tactic) caller
          return .named prior edge) ⟨owner,name,path⟩ invocation

structure DemandBinding {sources catalogue queue rootOwner rootName owner name}
    (entry : @SourcePendingMeaning.Entry sources catalogue queue)
    (path : CallPath sources rootOwner rootName owner name) where
  record : RecordIndex catalogue
  invocation : Invocation catalogue record
  demand : Demand invocation
  subject : entry.subject = .demand invocation demand
  binding : Binding queue path invocation
  matched : RuntimeInterval.Computed (read queue path invocation) binding

/-- The retained entry supplies its actual queue index, invocation, DutyAt
and substitution chain. Matching the call path grants no equation discharge. -/
def readDemand {sources catalogue queue rootOwner rootName owner name}
    (entry : @SourcePendingMeaning.Entry sources catalogue queue)
    (path : CallPath sources rootOwner rootName owner name) :
    WorkM (DemandBinding entry path) := do
  match subject : entry.subject with
  | .demand invocation demand =>
    let binding ← NaturalAffine.witness (read queue path invocation)
    return ⟨_,invocation,demand,subject,binding.val,by with_reducible exact binding.property⟩
  | _ => throw .request

/-- Typed selection of the original record preparation used by queue expansion. -/
structure RowAt {sources catalogue} (prepared : @GenericDutyQueue.Prepared sources catalogue)
    (record : RecordIndex catalogue) where
  row : PreparedRow catalogue prepared.index
  selected : prepared.records[record.val]? = some row
  same : row.record = record

def RowAt.value {sources catalogue prepared record} (located : @RowAt sources catalogue prepared record) :
    PreparedRecord catalogue record := located.same ▸ located.row.value

private def locateRow {sources catalogue} (prepared : @GenericDutyQueue.Prepared sources catalogue)
    (record : RecordIndex catalogue) : WorkM (RowAt prepared record) := do
  exactWork (Exact.charge (8*(prepared.records.length+1)))
  match selected : prepared.records[record.val]? with
  | none => throw .request
  | some row =>
    if same : row.record = record then return ⟨row,selected,same⟩
    else throw .request

/-- Each callee carries the actual prepared application, target and simultaneous
substitution selected from its parent's row. No resolution or substitution is
constructed anew. Matching a source path to a prepared chain does not certify
that its endpoint has a closed or discharged demand. -/
inductive FromPrepared {sources catalogue} (prepared : @GenericDutyQueue.Prepared sources catalogue) :
    {record : RecordIndex catalogue} → Invocation catalogue record → Type where
  | root (record : RecordIndex catalogue) : FromPrepared prepared (.root record)
  | named {record} {prior : Invocation catalogue record} (parent : FromPrepared prepared prior)
      (row : RowAt prepared record) (call : PreparedApplication catalogue record)
      (member : call ∈ row.value.calls) : FromPrepared prepared (.call prior call.application call.target)

private structure Candidate {sources catalogue record rootOwner rootName caller}
    (event : SourceRuntimeContext.NamedEvent sources caller)
    (parent : CallPath sources rootOwner rootName caller event.target.callerName)
    (row : @PreparedRecord sources catalogue record) where
  call : PreparedApplication catalogue record
  member : call ∈ row.calls
  edge : Edge event parent call.application

private def selectCall {sources catalogue record rootOwner rootName caller}
    (event : SourceRuntimeContext.NamedEvent sources caller)
    (parent : CallPath sources rootOwner rootName caller event.target.callerName)
    (row : @PreparedRecord sources catalogue record) : WorkM (Candidate event parent row) := do
  exactWork (Exact.charge (16*(row.calls.length+1)))
  let start := event.call.call.callee.head?.map (·.span.startByte)
  let found ← row.calls.attach.foldlM (fun found candidate => do
    -- A shared first byte is only a filter. Only the complete checked edge
    -- can select a candidate. Propagate work errors and refuse ambiguities.
    if candidate.val.application.original.tokens.head?.map (·.span.startByte) != start then return found
    let some edge ← matchEdge event parent candidate.val.application | return found
    if found.isSome then throw .request
    return some ⟨candidate.val,candidate.property,edge⟩) (none : Option (Candidate event parent row))
  let some selected := found | throw .request
  return selected

structure Identified {sources catalogue rootOwner rootName owner name}
    (queue : @GenericDutyQueue.Checked sources catalogue) (path : CallPath sources rootOwner rootName owner name) where
  record : RecordIndex catalogue
  invocation : Invocation catalogue record
  binding : Binding queue path invocation
  source : FromPrepared queue.prepared invocation

/-- Derive the record/activity instance ID without taking a proposed ordinal.
The root selection uses immutable original-source identity. Each named step
resolves exactly one original prepared call within the derived parent record.
The genuine root instantiation remains on the path. -/
def identify {sources catalogue} (queue : @GenericDutyQueue.Checked sources catalogue) {rootOwner rootName owner name}
    (path : CallPath sources rootOwner rootName owner name) : WorkM (Identified queue path) :=
  WellFounded.fix (measure (fun packed : CallPath.Packed sources rootOwner rootName => sizeOf packed.2.2)).wf
    (C := fun packed => WorkM (Identified queue packed.2.2))
    (fun packed => match packed with
      | ⟨_,_,.root (signature := original) body⟩ => fun _ => do
        let selected ← NaturalAffine.witness (GenericCatalogueIndex.read queue.prepared.index original.original)
        let record := selected.val.entry.index
        return ⟨record,.root record,
          .root body record selected.val (by with_reducible exact selected.property) rfl,.root record⟩
      | ⟨_,_,.named event _ _ parent⟩ => fun visit => do
        let prior ← visit ⟨_,_,parent⟩ (by decreasing_tactic)
        let row ← locateRow queue.prepared prior.record
        let choice ← selectCall event parent row.value
        return ⟨choice.call.target.entry.index,.call prior.invocation choice.call.application choice.call.target,
          .named prior.binding choice.edge,.named prior.source row choice.call choice.member⟩)
    ⟨owner,name,path⟩

end QleisliKernel.Qirf.RuntimeDutyInvocation
