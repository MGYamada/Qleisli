import QleisliKernel.SourceTypes.GenericCatalogue
import QleisliKernel.SourceTypes.GenericOperationSubstitute

/-! Source-indexed expansion of finite original operation duties.
Applications occupy their original positions in the one checked activity stream.
Every substitution is an actual simultaneous original-call substitution; a path
is composed by retaining those executions, never by fabricating a caller state.
Header references share an instance/formal identity with the callee header.
Written assertions and constructor/access demands keep separate identities.
Recursive back edges remain explicit unresolved coverage. This metadata grants
no Meaning equation, implementation path, native handle or wire authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.GenericDutyQueue
open Finite GenericOperation GenericOperationSubstitute

abbrev RecordIndex {sources} (catalogue : GenericCatalogue.Checked sources) :=
  Fin catalogue.records.length

def activities {sources} (catalogue : GenericCatalogue.Checked sources)
    (record : RecordIndex catalogue) : List (Activity sources) :=
  GenericCatalogue.bodyActivities (catalogue.records[record.val]'record.isLt)

structure SourceId where
  record : Nat
  activity : Nat
  deriving BEq, DecidableEq, Repr

structure InstanceId where
  root : Nat
  calls : List SourceId
  deriving BEq, DecidableEq, Repr

inductive LocalId where
  | header (kind : RequirementKind)
  | written (source : SourceId) (kind : RequirementKind)
  deriving BEq, DecidableEq, Repr

structure RequirementId where
  invocation : InstanceId
  requirement : LocalId
  deriving BEq, DecidableEq, Repr

structure DutyAt {sources} (catalogue : GenericCatalogue.Checked sources)
    (record : RecordIndex catalogue) where
  index : Fin (activities catalogue record).length
  original : Duty sources
  selected : (activities catalogue record)[index.val]'index.isLt = .duty original

structure ApplicationAt {sources} (catalogue : GenericCatalogue.Checked sources)
    (record : RecordIndex catalogue) where
  index : Fin (activities catalogue record).length
  original : ApplicationSource sources
  selected : (activities catalogue record)[index.val]'index.isLt = .application original

def ApplicationAt.id {sources catalogue record}
    (application : @ApplicationAt sources catalogue record) : SourceId :=
  ⟨record.val,application.index.val⟩

structure Target {sources catalogue record}
    (application : @ApplicationAt sources catalogue record) where
  entry : GenericCatalogue.Entry catalogue.toRuntimeChecked application.original.target.envelope
  resolved : ∃ before after,
    (GenericCatalogue.lookup catalogue.toRuntimeChecked application.original.target.envelope).run before =
      (.ok entry,after)
  substitution : GenericOperationSubstitute.Prepared application.original

def readTarget {sources catalogue record}
    (application : @ApplicationAt sources catalogue record) : WorkM (Target application) := do
  let target ← NaturalAffine.witness
    (GenericCatalogue.lookup catalogue.toRuntimeChecked application.original.target.envelope)
  let substitution ← GenericOperationSubstitute.prepare application.original
  return ⟨target.val,by with_reducible exact target.property,substitution⟩

/-- The indices, original occurrences and exact target-original receipts are
retained at every edge. Module/name strings are never used as instance IDs. -/
inductive Invocation {sources} (catalogue : GenericCatalogue.Checked sources) :
    RecordIndex catalogue → Type where
  | root (record : RecordIndex catalogue) : Invocation catalogue record
  | call {record : RecordIndex catalogue} (caller : Invocation catalogue record)
      (application : ApplicationAt catalogue record) (target : Target application) :
      Invocation catalogue target.entry.index

def Invocation.id {sources catalogue record} : @Invocation sources catalogue record → InstanceId
  | .root original => ⟨original.val,[]⟩
  | .call caller application _ =>
    let parent := caller.id
    ⟨parent.root,parent.calls ++ [application.id]⟩

def Invocation.depth {sources catalogue record} : @Invocation sources catalogue record → Nat
  | .root _ => 0
  | .call caller _ _ => caller.depth+1

def Invocation.applications {sources catalogue record} :
    @Invocation sources catalogue record → List (ApplicationSource sources)
  | .root _ => []
  | .call caller application _ => caller.applications ++ [application.original]

def Invocation.records {sources catalogue record} : @Invocation sources catalogue record → List Nat
  | .root original => [original.val]
  | .call caller _ target => caller.records ++ [target.entry.index.val]

/-- The list index is the exact original application chain; there is no
name/descriptor lookup or successful-subject cache at replay. -/
inductive PreparedChain {sources} : List (ApplicationSource sources) → Type where
  | nil : PreparedChain []
  | cons (application : ApplicationSource sources)
      (prepared : GenericOperationSubstitute.Prepared application)
      (rest : List (ApplicationSource sources)) (tail : PreparedChain rest) :
      PreparedChain (application :: rest)

def Invocation.prepared {sources catalogue record}
    (invocation : @Invocation sources catalogue record) : PreparedChain invocation.applications.reverse :=
  match invocation with
  | .root _ => .nil
  | .call parent application target => by
    change PreparedChain ((parent.applications ++ [application.original]).reverse)
    rw [List.reverse_append]
    exact .cons application.original target.substitution parent.applications.reverse parent.prepared

/-- Substitutions run from the innermost original callee toward the root.
Inserted caller Op actuals are left untouched by each simultaneous step. -/
inductive Transport {sources} : List (ApplicationSource sources) →
    Subject sources → Subject sources → Type where
  | identity (original : Subject sources) : Transport [] original original
  | step (application : ApplicationSource sources) (rest : List (ApplicationSource sources))
      (original : Subject sources) (checked : GenericOperationSubstitute.Checked application original)
      {result : Subject sources} (next : Transport rest checked.result.subject result) :
      Transport (application :: rest) original result

structure Transported {sources} (applications : List (ApplicationSource sources))
    (original : Subject sources) where
  subject : Subject sources
  receipt : Transport applications original subject

def readTransport {sources} (applications : List (ApplicationSource sources)) (original : Subject sources) :
    WorkM (Transported applications original) := do
  match applications with
  | [] => return ⟨original,.identity original⟩
  | application :: rest =>
    let checked ← GenericOperationSubstitute.read application original.description original.suppliers
    let next ← readTransport rest checked.result.subject
    return ⟨next.subject,.step application rest original checked next.receipt⟩

def readPreparedTransport {sources applications} (chain : @PreparedChain sources applications)
    (original : Subject sources) : WorkM (Transported applications original) := do
  match chain with
  | .nil => return ⟨original,.identity original⟩
  | .cons application prepared rest tail =>
    let checked ← GenericOperationSubstitute.readWithPrepared prepared original.description original.suppliers
    let next ← readPreparedTransport tail checked.result.subject
    return ⟨next.subject,.step application rest original checked next.receipt⟩

structure Demand {sources catalogue record} (invocation : @Invocation sources catalogue record) where
  source : DutyAt catalogue record
  transported : Transported invocation.applications.reverse ⟨source.original.subject,source.original.suppliers⟩

def Demand.id {sources catalogue record invocation}
    (demand : @Demand sources catalogue record invocation) : RequirementId :=
  ⟨invocation.id,match demand.source.original.kind.formal? with
    | some _ => .header demand.source.original.kind
    | none => .written ⟨record.val,demand.source.index.val⟩ demand.source.original.kind⟩

private def bindingMatches (kind : RequirementKind) {sources} (binding : Binding sources) : Bool :=
  match kind.formal? with
  | none => false
  | some key => binding.owner == key.moduleName && binding.name == key.declarationName &&
      binding.formal.ordinal == key.ordinal && binding.application.isSome

/-- Both candidates belong to the same indexed original record. The complete
original callee token slice and lexical scope identify the occurrence; no
selected matrix, descriptor or display name identifies a supplied instance. -/
private def SameOccurrence {sources} (left right : ApplicationSource sources) : Prop :=
  left.tokens = right.tokens ∧ left.scope = right.scope ∧
    left.state.owner = right.state.owner ∧ left.state.name = right.state.name ∧
    left.owner = right.owner ∧ left.name = right.name

private instance {sources} (left right : ApplicationSource sources) :
    Decidable (SameOccurrence left right) := by unfold SameOccurrence; infer_instance

private def applicationFields {sources} (application : ApplicationSource sources) : Nat :=
  (application.tokens.map fun token => token.text.utf8ByteSize+4).sum+
    (application.scope.map fun name => name.utf8ByteSize+1).sum+
    application.state.owner.utf8ByteSize+application.state.name.utf8ByteSize+
    application.owner.utf8ByteSize+application.name.utf8ByteSize+1

private def activityFields {sources} : Activity sources → Nat
  | .application application => applicationFields application
  | .duty duty =>
    (match duty.kind.formal? with | none => 1 | some key => Meter.key key)+
      (duty.bindings.map fun binding => binding.owner.utf8ByteSize+binding.name.utf8ByteSize+3+
        (binding.application.map applicationFields).getD 0).sum+1

private def reserveActivities {sources} (stream : List (Activity sources)) : WorkM Unit := do
  -- Includes indexed list traversal, all occurrence matching and key/token
  -- comparisons. Retained source snapshots and Origin functions are not read.
  exactWork (Exact.charge (32*(stream.length+1)*((stream.map activityFields).sum+1)))

private def originalApplications {sources} (catalogue : GenericCatalogue.Checked sources)
    (record : RecordIndex catalogue) : List (ApplicationAt catalogue record) :=
  (List.finRange (activities catalogue record).length).filterMap fun index =>
    match selected : (activities catalogue record)[index.val]'index.isLt with
    | .duty _ => none
    | .application original => some ⟨index,original,selected⟩

private def originalDuties {sources} (catalogue : GenericCatalogue.Checked sources)
    (record : RecordIndex catalogue) : List (DutyAt catalogue record) :=
  (List.finRange (activities catalogue record).length).filterMap fun index =>
    match selected : (activities catalogue record)[index.val]'index.isLt with
    | .application _ => none
    | .duty original => some ⟨index,original,selected⟩

private def headerDuties {sources} (catalogue : GenericCatalogue.Checked sources)
    (record : RecordIndex catalogue) : List (DutyAt catalogue record) :=
  (originalDuties catalogue record).filter fun candidate =>
    candidate.original.kind.formal?.isSome && candidate.original.bindings.isEmpty

/-- Only original occurrence resolution and original header projections are
shared. No instance substitution, closed status or native proof is cached. -/
structure PreparedApplication {sources} (catalogue : GenericCatalogue.Checked sources)
    (record : RecordIndex catalogue) where
  application : ApplicationAt catalogue record
  target : Target application
  headers : List (DutyAt catalogue target.entry.index)
  originalHeaders : headers = headerDuties catalogue target.entry.index

structure PreparedRecord {sources} (catalogue : GenericCatalogue.Checked sources)
    (record : RecordIndex catalogue) where
  calls : List (PreparedApplication catalogue record)
  every : calls.map (·.application.index) = (originalApplications catalogue record).map (·.index)

private def prepareRecord {sources} (catalogue : GenericCatalogue.Checked sources)
    (record : RecordIndex catalogue) : WorkM (PreparedRecord catalogue record) := do
  reserveActivities (activities catalogue record)
  let calls ← (originalApplications catalogue record).mapM fun application => do
    let target ← readTarget application
    reserveActivities (activities catalogue target.entry.index)
    return (⟨application,target,headerDuties catalogue target.entry.index,rfl⟩ :
      PreparedApplication catalogue record)
  if every : calls.map (·.application.index) = (originalApplications catalogue record).map (·.index) then
    return ⟨calls,every⟩
  else throw .request

structure PreparedRow {sources} (catalogue : GenericCatalogue.Checked sources) where
  record : RecordIndex catalogue
  value : PreparedRecord catalogue record
  computed : ∃ before after,(prepareRecord catalogue record).run before = (.ok value,after)

structure Prepared {sources} (catalogue : GenericCatalogue.Checked sources) where
  records : List (PreparedRow catalogue)
  every : records.map (·.record) = List.finRange catalogue.records.length

private def prepare {sources} (catalogue : GenericCatalogue.Checked sources) : WorkM (Prepared catalogue) := do
  exactWork (Exact.charge (16*(catalogue.records.length+1)^2))
  let records ← (List.finRange catalogue.records.length).mapM fun record => do
    let value ← NaturalAffine.witness (prepareRecord catalogue record)
    return (⟨record,value.val,by with_reducible exact value.property⟩ : PreparedRow catalogue)
  if every : records.map (·.record) = List.finRange catalogue.records.length then
    return ⟨records,every⟩
  else throw .request

private def preparedRecord {sources catalogue} (prepared : @Prepared sources catalogue)
    (record : RecordIndex catalogue) : WorkM (PreparedRecord catalogue record) := do
  exactWork (Exact.charge (8*(prepared.records.length+1)))
  let some selected := prepared.records[record.val]? | throw .request
  if same : selected.record = record then
    return same ▸ selected.value
  else throw .request

private def preparedCall {sources catalogue record} (prepared : @PreparedRecord sources catalogue record)
    (index : Fin (activities catalogue record).length) :
    WorkM {selected : PreparedApplication catalogue record // selected.application.index = index} := do
  exactWork (Exact.charge (8*(prepared.calls.length+1)))
  let some selected := prepared.calls.find? (·.application.index.val == index.val) | throw .request
  if same : selected.application.index = index then return ⟨selected,same⟩ else throw .request

/-- This is a reference to the one instance-bound callee-header demand. The
caller-side premise occurrence remains retained, including its original actual
binding, while the header's transformed subject is read exactly once there. -/
structure HeaderReference {sources catalogue record}
    (invocation : @Invocation sources catalogue record) where
  source : DutyAt catalogue record
  binding : Binding sources
  supplied : source.original.bindings.find? (bindingMatches source.original.kind) = some binding
  application : ApplicationSource sources
  bound : binding.application = some application
  occurrence : ApplicationAt catalogue record
  same : SameOccurrence occurrence.original application
  target : Target occurrence
  header : DutyAt catalogue target.entry.index
  originalKind : header.original.kind = source.original.kind
  originalHeader : header.original.bindings.isEmpty = true

def HeaderReference.id {sources catalogue record invocation}
    (reference : @HeaderReference sources catalogue record invocation) : RequirementId :=
  ⟨(Invocation.call invocation reference.occurrence reference.target).id,
    .header reference.header.original.kind⟩

private def readHeaderReference {sources catalogue record}
    (invocation : @Invocation sources catalogue record) (source : DutyAt catalogue record)
    (prepared : PreparedRecord catalogue record) : WorkM (HeaderReference invocation) := do
  exactWork (Exact.charge (16*(source.original.bindings.length+1)*
    (activityFields (.duty source.original)+1)))
  match supplied : source.original.bindings.find? (bindingMatches source.original.kind) with
  | none => throw .request
  | some binding =>
    match bound : binding.application with
    | none => throw .request
    | some application =>
      let fields := (prepared.calls.map fun candidate => applicationFields candidate.application.original).sum
      exactWork (Exact.charge (16*(fields+prepared.calls.length*(applicationFields application+1)+1)))
      let matching := prepared.calls.filter fun candidate =>
        decide (SameOccurrence candidate.application.original application)
      let [selected] := matching | throw .request
      let occurrence := selected.application
      let target := selected.target
      if same : SameOccurrence occurrence.original application then
        let fields := (selected.headers.map fun candidate => activityFields (.duty candidate.original)).sum
        exactWork (Exact.charge (16*(fields+selected.headers.length*(activityFields (.duty source.original)+1)+1)))
        let matching := selected.headers.filter fun candidate =>
          candidate.original.kind == source.original.kind && candidate.original.bindings.isEmpty
        let [header] := matching | throw .request
        if originalKind : header.original.kind = source.original.kind then
          if originalHeader : header.original.bindings.isEmpty = true then
            return ⟨source,binding,(by first | exact supplied | rfl),application,
              (by first | exact bound | rfl),occurrence,same,target,header,originalKind,originalHeader⟩
          else throw .request
        else throw .request
      else throw .request

inductive Item {sources} (catalogue : GenericCatalogue.Checked sources) where
  | demand {record} (invocation : Invocation catalogue record) (checked : Demand invocation)
  | header {record} (invocation : Invocation catalogue record) (reference : HeaderReference invocation)
  | call {record} (invocation : Invocation catalogue record)
      (application : ApplicationAt catalogue record) (target : Target application)
  | pendingRecursion {record} (invocation : Invocation catalogue record)
      (application : ApplicationAt catalogue record) (target : Target application)
      (repeated : target.entry.index.val ∈ invocation.records)

def Item.id? {sources catalogue} : @Item sources catalogue → Option RequirementId
  | .demand _ checked => some checked.id
  | .header _ reference => some reference.id
  | .call .. | .pendingRecursion .. => none

def Item.unresolved {sources catalogue} : @Item sources catalogue → Bool
  | .pendingRecursion .. => true
  | _ => false

private def expand {sources} (catalogue : GenericCatalogue.Checked sources) (prepared : Prepared catalogue) :
    Nat → (record : RecordIndex catalogue) → Invocation catalogue record → WorkM (List (Item catalogue)) :=
  Nat.rec (fun _ _ => throw .limit) (fun _ next record invocation => do
    let stream := activities catalogue record
    let originalRecord ← preparedRecord prepared record
    reserveActivities stream
    -- Forming/reversing retained call paths, ancestor checks and eventual
    -- source IDs traverse the depth. The quadratic allowance also covers
    -- copying each nested item through its ancestors, without source scans.
    exactWork (Exact.charge (16*(stream.length+1)*
      ((invocation.depth+1)^2+catalogue.records.length+1)))
    let entries ← (List.finRange stream.length).mapM fun index => do
      match selected : stream[index.val]'index.isLt with
      | .duty original =>
        let source : DutyAt catalogue record := ⟨index,original,selected⟩
        if (original.bindings.find? (bindingMatches original.kind)).isSome then
          return [Item.header invocation (← readHeaderReference invocation source originalRecord)]
        else
          let transported ← readPreparedTransport invocation.prepared ⟨original.subject,original.suppliers⟩
          return [Item.demand invocation ⟨source,transported⟩]
      | .application _original =>
        let cached ← preparedCall originalRecord index
        let application := cached.val.application
        let target := cached.val.target
        if repeated : target.entry.index.val ∈ invocation.records then
          return [Item.call invocation application target,Item.pendingRecursion invocation application target repeated]
        else
          let nested ← next target.entry.index (.call invocation application target)
          return Item.call invocation application target :: nested
    return entries.flatten)

structure Root {sources catalogue} (prepared : @Prepared sources catalogue) where
  record : RecordIndex catalogue
  items : List (Item catalogue)
  traversed : ∃ before after,
    (expand catalogue prepared (catalogue.records.length+1) record (.root record)).run before = (.ok items,after)

structure Checked {sources} (catalogue : GenericCatalogue.Checked sources) where
  prepared : Prepared catalogue
  preparation : ∃ before after,(prepare catalogue).run before = (.ok prepared,after)
  roots : List (Root prepared)
  every : roots.map (·.record) = List.finRange catalogue.records.length

def Checked.items {sources catalogue} (checked : @Checked sources catalogue) : List (Item catalogue) :=
  checked.roots.flatMap (·.items)

def Checked.complete {sources catalogue} (checked : @Checked sources catalogue) : Bool :=
  !checked.items.any Item.unresolved

/-- The depth bound is the number of original records, not caller token fuel.
Every acyclic path is expanded in place. A recursive family gets a retained
back-edge obligation rather than a chosen Nat, unrolling or successful prefix.
A consumer must reject incomplete coverage and discharge all resulting duties;
this reader intentionally does not close guard-dependent numeric obligations. -/
def read {sources} (catalogue : GenericCatalogue.Checked sources) : WorkM (Checked catalogue) := do
  let prepared ← NaturalAffine.witness (prepare catalogue)
  exactWork (Exact.charge (16*(catalogue.records.length+1)^2))
  let roots ← (List.finRange catalogue.records.length).mapM fun record => do
    let items ← NaturalAffine.witness
      (expand catalogue prepared.val (catalogue.records.length+1) record (.root record))
    return (⟨record,items.val,by with_reducible exact items.property⟩ : Root prepared.val)
  if every : roots.map (·.record) = List.finRange catalogue.records.length then
    return ⟨prepared.val,by with_reducible exact prepared.property,roots,every⟩
  else throw .request

end QleisliKernel.SourceTypes.GenericDutyQueue
