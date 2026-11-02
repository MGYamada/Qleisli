import QleisliKernel.SourceTypes.GenericDutyQueue

/-! Withhold concrete Meaning assertions in the complete original duty queue.
Unbound original formals remain conditional. An inactive numeric exception needs
an actual original branch guard, its checked call substitutions and a universal
contradiction, as well as an original nonzero Nat dependency. Header premises
alone cannot create that exception. Every canonical demand, reference and call
stays indexed; unresolved recursive coverage cannot produce Checked.
This staged guard proves no Meaning equation or implementation path. Closed
access duties are retained for their separate same-final-root native consumers.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourcePendingMeaning
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open GenericOperation GenericDutyQueue GenericOperationSubstitute Semantics.SourceAffine

private def snapshots {sources applications original result}
    (receipt : @Transport sources applications original result) : List Description :=
  match receipt with
  | .identity source => [source.description]
  | .step _ _ source _ next => source.description :: snapshots next

private def isNatural : Key → Bool
  | .natural _ => true
  | _ => false

/-- A real nonzero original Nat key occurs before or between the checked
substitutions. An unused Nat header or a constant selected count is insufficient. -/
structure NaturalDependency {sources catalogue record invocation}
    (demand : @Demand sources catalogue record invocation) where
  index : Fin (snapshots demand.transported.receipt).length
  keys : List Key
  original : ((snapshots demand.transported.receipt)[index.val]'index.isLt).freeKeys = .ok keys
  natural : keys.any isNatural = true

private def readDependency {sources catalogue record invocation}
    (demand : @Demand sources catalogue record invocation) : WorkM (Option (NaturalDependency demand)) := do
  let stages := snapshots demand.transported.receipt
  exactWork (Exact.charge (16*(stages.length+1)^2))
  (List.finRange stages.length).foldlM (fun previous index => do
    if previous.isSome then return previous
    let description := stages[index.val]'index.isLt
    exactWork (Exact.charge (Meter.freeWork description))
    match original : description.freeKeys with
    | .error _ => throw .request
    | .ok keys =>
      if natural : keys.any isNatural = true then
        return some ⟨index,keys,(by first | exact original | rfl),natural⟩
      else return none) none

private def transportedValues {sources} : List (ApplicationSource sources) → Valuation → Valuation
  | [],values => values
  | application :: rest,values =>
    NaturalSubstitute.replacementValues application.naturalActuals (transportedValues rest values)

structure TransferredForm {sources} (applications : List (ApplicationSource sources)) (original : Form) where
  form : Form
  correct : ∀ values,form.evaluate values = original.evaluate (transportedValues applications values)

private def transferForm {sources} (frame : NaturalFrames.Frame)
    (applications : List (ApplicationSource sources)) (original : Form) :
    WorkM (TransferredForm applications original) := do
  match applications with
  | [] => return ⟨original,by intro values; rfl⟩
  | application :: rest =>
    exactWork (Exact.charge (16*(Meter.frame frame+Meter.frame (calleeFrame application)+1)))
    guard (frame.binders == (calleeFrame application).binders) .request
    let _ ← GenericOperationSubstitute.readContext application
    let substituted ← NaturalSubstitute.substitute (callerFrame application).binders.length
      original application.naturalActuals
    let next ← transferForm (callerFrame application) rest substituted.form
    return ⟨next.form,by
      intro values
      rw [next.correct,substituted.correct]
      rfl⟩

private def refute : (alternatives : List (List Form)) →
    WorkM (Option (NaturalPredicates.Established (∀ values,¬Satisfies alternatives values)))
  | [] => return some ⟨by simp [Satisfies]⟩
  | rows :: rest => do
    let some first ← NaturalConstraints.check rows | return none
    let some remaining ← refute rest | return none
    return some ⟨by
      intro values possible
      rcases possible with ⟨branch,member,held⟩
      rcases List.mem_cons.mp member with head | tail
      · subst branch
        exact first.witness values held
      · exact remaining.proof values ⟨branch,tail,held⟩⟩

structure GuardSource (sources : Sources) where
  state : GenericLexicalNatural.SomeEnvironment sources
  scope : List String
  tokens : List LocatedToken
  applications : List (ApplicationSource sources)

private def callGuards {sources catalogue record} : @Invocation sources catalogue record → List (GuardSource sources)
  | .root _ => []
  | .call parent application _ =>
    ⟨application.original.state,application.original.scope,application.original.tokens,
      parent.applications.reverse⟩ :: callGuards parent

private def guardSources {sources catalogue record invocation}
    (demand : @Demand sources catalogue record invocation) : List (GuardSource sources) :=
  let origin := demand.source.original.origin
  ⟨origin.state,origin.scope,origin.tokens,invocation.applications.reverse⟩ :: callGuards invocation

structure GuardAt {sources} (source : GuardSource sources) where
  index : Fin source.state.environment.guards.length
  origin : GenericLexicalNatural.GuardOrigin
    (source.state.environment.guards[index.val]'index.isLt).predicate
  original : (source.state.environment.guards[index.val]'index.isLt).origin = some origin

def GuardAt.guard {sources source} (guardSite : @GuardAt sources source) : GenericLexicalNatural.Guard :=
  source.state.environment.guards[guardSite.index.val]'guardSite.index.isLt

structure FalseGuard {sources} (source : GuardSource sources) where
  guardSite : GuardAt source
  left : TransferredForm source.applications guardSite.guard.left
  right : TransferredForm source.applications guardSite.guard.right
  refuted : ∀ values,¬guardSite.guard.Holds (transportedValues source.applications values)

theorem FalseGuard.inactive {sources source} (checked : @FalseGuard sources source) (values : Valuation) :
    ¬source.state.environment.meaning (transportedValues source.applications values) := by
  intro held
  exact checked.refuted values (source.state.environment.guardsHeld _ held _
    (List.getElem_mem checked.guardSite.index.isLt))

private def readFalseGuard {sources} (source : GuardSource sources) : WorkM (Option (FalseGuard source)) := do
  let guards := source.state.environment.guards
  let cells := (guards.map fun guard => Meter.form guard.left+Meter.form guard.right+
    guard.scope.length+guard.bindings.length+1).sum
  exactWork (Exact.charge (16*(guards.length+1)*(cells+1)))
  (List.finRange guards.length).foldlM (fun previous index => do
    if previous.isSome then return previous
    let originalGuard := guards[index.val]'index.isLt
    match original : originalGuard.origin with
    | none => return none
    | some origin =>
      let guardSite : GuardAt source := ⟨index,origin,(by first | exact original | rfl)⟩
      let frame := StaticHeaders.frame source.state.prepared.original
      let left ← transferForm frame source.applications guardSite.guard.left
      let right ← transferForm frame source.applications guardSite.guard.right
      let compared ← NaturalPredicates.comparison left.form
        (guardSite.guard.predicate.forBranch guardSite.guard.branch).comparison right.form
      let some noValues ← refute compared.alternatives | return none
      return some ⟨guardSite,left,right,by
        intro values held
        apply noValues.proof values
        apply (compared.correct values).mpr
        simpa only [GenericLexicalNatural.Guard.Holds,left.correct,right.correct] using held⟩) none

structure Inactive {sources catalogue record invocation}
    (demand : @Demand sources catalogue record invocation) where
  dependency : NaturalDependency demand
  index : Fin (guardSources demand).length
  guard : FalseGuard ((guardSources demand)[index.val]'index.isLt)

private def readInactive {sources catalogue record invocation}
    (demand : @Demand sources catalogue record invocation) (dependency : NaturalDependency demand) :
    WorkM (Option (Inactive demand)) := do
  let candidates := guardSources demand
  exactWork (Exact.charge (16*(candidates.length+1)^2))
  (List.finRange candidates.length).foldlM (fun previous index => do
    if previous.isSome then return previous
    match ← readFalseGuard (candidates[index.val]'index.isLt) with
    | none => return none
    | some blocked => return some ⟨dependency,index,blocked⟩) none

inductive DemandStatus {sources catalogue record invocation}
    (demand : @Demand sources catalogue record invocation) where
  | classified (status : GenericOperation.Status demand.transported.subject.description)
  | inactive (checked : Inactive demand)

private def inspectDemand {sources catalogue record invocation}
    (demand : @Demand sources catalogue record invocation) : WorkM (DemandStatus demand) := do
  let description := demand.transported.subject.description
  exactWork (Exact.charge (Meter.freeWork description))
  match original : description.freeKeys with
  | .error _ => throw .request
  | .ok keys =>
    if empty : keys = [] then
      if let some dependency ← readDependency demand then
        if let some inactive ← readInactive demand dependency then
          return .inactive inactive
      -- Reuse the exact free-key computation above; do not claim close ran.
      let data ← NaturalAffine.witness (GenericOperation.readClosedData description)
      return .classified (.closed ⟨data.val,by simpa only [empty] using original,
        by with_reducible exact data.property⟩)
    else return .classified (.conditional keys empty original)

def Assessment {sources catalogue} : @Item sources catalogue → Type
  | .demand _ demand => DemandStatus demand
  | _ => Unit

private def inspect {sources catalogue} (item : @Item sources catalogue) : WorkM (Assessment item) := do
  match item with
  | .demand _ demand => inspectDemand demand
  | .header .. => return ()
  | .call .. => return ()
  | .pendingRecursion .. => return ()

def unconsumed {sources catalogue} (item : @Item sources catalogue) : Assessment item → Bool :=
  match item with
  | .demand _ demand => fun assessment =>
    match demand.source.original.requirement,assessment with
    | .meaning _,.classified (.closed _) => true
    | _,_ => false
  | _ => fun _ => false

structure Entry {sources catalogue} (queue : @GenericDutyQueue.Checked sources catalogue) where
  index : Fin queue.items.length
  assessment : Assessment (queue.items[index.val]'index.isLt)
  original : ∃ before after,
    (inspect (queue.items[index.val]'index.isLt)).run before = (.ok assessment,after)

def Entry.unconsumed {sources catalogue queue} (entry : @Entry sources catalogue queue) : Bool :=
  QleisliKernel.Qirf.SourcePendingMeaning.unconsumed
    (queue.items[entry.index.val]'entry.index.isLt) entry.assessment

def conditionalKeys {sources catalogue} (item : @Item sources catalogue) : Assessment item → List Key :=
  match item with
  | .demand _ demand => fun assessment => match demand.source.original.requirement,assessment with
    | .meaning _,.classified (.conditional keys _ _) => keys
    | _,_ => []
  | _ => fun _ => []

def Entry.conditionalKeys {sources catalogue queue} (entry : @Entry sources catalogue queue) : List Key :=
  QleisliKernel.Qirf.SourcePendingMeaning.conditionalKeys
    (queue.items[entry.index.val]'entry.index.isLt) entry.assessment

def inactive {sources catalogue} (item : @Item sources catalogue) : Assessment item → Bool :=
  match item with
  | .demand _ _ => fun assessment => match assessment with
    | .inactive _ => true | _ => false
  | _ => fun _ => false

def Entry.inactive {sources catalogue queue} (entry : @Entry sources catalogue queue) : Bool :=
  QleisliKernel.Qirf.SourcePendingMeaning.inactive
    (queue.items[entry.index.val]'entry.index.isLt) entry.assessment

structure Checked {sources} (catalogue : GenericCatalogue.Checked sources) where
  queue : GenericDutyQueue.Checked catalogue
  expanded : ∃ before after,(GenericDutyQueue.read catalogue).run before = (.ok queue,after)
  complete : queue.complete = true
  entries : List (Entry queue)
  every : entries.map (·.index) = List.finRange queue.items.length
  withheld : entries.all (fun entry => !entry.unconsumed) = true

/-- Both existing preparation entry points use this same complete queue gate.
Closed M remains withheld pending its actual native equation, including honest
closed requests. Symbolic deferral is not an M proof, and inactive Nat metadata
is not an access proof. Recursion with unresolved coverage cannot pass. -/
def read {sources} (catalogue : GenericCatalogue.Checked sources) : WorkM (Checked catalogue) := do
  let queue ← NaturalAffine.witness (GenericDutyQueue.read catalogue)
  let items := queue.val.items
  exactWork (Exact.charge (16*(catalogue.records.length+items.length+1)^2))
  if complete : queue.val.complete = true then
    let entries ← (List.finRange items.length).mapM fun index => do
      let assessment ← NaturalAffine.witness (inspect (items[index.val]'index.isLt))
      return (⟨index,assessment.val,by with_reducible exact assessment.property⟩ : Entry queue.val)
    if every : entries.map (·.index) = List.finRange queue.val.items.length then
      if withheld : entries.all (fun entry => !entry.unconsumed) = true then
        return ⟨queue.val,by with_reducible exact queue.property,complete,entries,every,withheld⟩
      else throw .request
    else throw .request
  else throw .request

end QleisliKernel.Qirf.SourcePendingMeaning
