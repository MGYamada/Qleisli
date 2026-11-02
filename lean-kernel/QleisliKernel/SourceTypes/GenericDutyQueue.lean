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

def readTarget {sources catalogue record}
    (application : @ApplicationAt sources catalogue record) : WorkM (Target application) := do
  let target ← NaturalAffine.witness
    (GenericCatalogue.lookup catalogue.toRuntimeChecked application.original.target.envelope)
  return ⟨target.val,by with_reducible exact target.property⟩

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

def Invocation.applications {sources catalogue record} :
    @Invocation sources catalogue record → List (ApplicationSource sources)
  | .root _ => []
  | .call caller application _ => caller.applications ++ [application.original]

def Invocation.records {sources catalogue record} : @Invocation sources catalogue record → List Nat
  | .root original => [original.val]
  | .call caller _ target => caller.records ++ [target.entry.index.val]

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
    (invocation : @Invocation sources catalogue record) (source : DutyAt catalogue record) :
    WorkM (HeaderReference invocation) := do
  reserveActivities (activities catalogue record)
  match supplied : source.original.bindings.find? (bindingMatches source.original.kind) with
  | none => throw .request
  | some binding =>
    match bound : binding.application with
    | none => throw .request
    | some application =>
      let matching := (originalApplications catalogue record).filter fun candidate =>
        decide (SameOccurrence candidate.original application)
      let [occurrence] := matching | throw .request
      if same : SameOccurrence occurrence.original application then
        let target ← readTarget occurrence
        reserveActivities (activities catalogue target.entry.index)
        let matching := (originalDuties catalogue target.entry.index).filter fun candidate =>
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

private def expand {sources} (catalogue : GenericCatalogue.Checked sources) :
    Nat → (record : RecordIndex catalogue) → Invocation catalogue record → WorkM (List (Item catalogue)) :=
  Nat.rec (fun _ _ => throw .limit) (fun _ next record invocation => do
    let stream := activities catalogue record
    reserveActivities stream
    let entries ← (List.finRange stream.length).mapM fun index => do
      match selected : stream[index.val]'index.isLt with
      | .duty original =>
        let source : DutyAt catalogue record := ⟨index,original,selected⟩
        if (original.bindings.find? (bindingMatches original.kind)).isSome then
          return [Item.header invocation (← readHeaderReference invocation source)]
        else
          let transported ← readTransport invocation.applications.reverse ⟨original.subject,original.suppliers⟩
          return [Item.demand invocation ⟨source,transported⟩]
      | .application original =>
        let application : ApplicationAt catalogue record := ⟨index,original,selected⟩
        let target ← readTarget application
        if repeated : target.entry.index.val ∈ invocation.records then
          return [Item.call invocation application target,Item.pendingRecursion invocation application target repeated]
        else
          let nested ← next target.entry.index (.call invocation application target)
          return Item.call invocation application target :: nested
    return entries.flatten)

structure Root {sources} (catalogue : GenericCatalogue.Checked sources) where
  record : RecordIndex catalogue
  items : List (Item catalogue)
  traversed : ∃ before after,
    (expand catalogue (catalogue.records.length+1) record (.root record)).run before = (.ok items,after)

structure Checked {sources} (catalogue : GenericCatalogue.Checked sources) where
  roots : List (Root catalogue)
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
  exactWork (Exact.charge (16*(catalogue.records.length+1)^2))
  let roots ← (List.finRange catalogue.records.length).mapM fun record => do
    let items ← NaturalAffine.witness
      (expand catalogue (catalogue.records.length+1) record (.root record))
    return (⟨record,items.val,by with_reducible exact items.property⟩ : Root catalogue)
  if every : roots.map (·.record) = List.finRange catalogue.records.length then
    return ⟨roots,every⟩
  else throw .request

end QleisliKernel.SourceTypes.GenericDutyQueue
