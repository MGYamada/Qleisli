import QleisliKernel.Qirf.RuntimeDiscoveryScope

/-! One source discovery handler for legacy metadata and indexed body plans.
Original source queries, complete slots and static eligibility are shared.
Only actual Subject views record plans; native actions remain later checks.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeBodyDiscovery
open QleisliKernel Finite SourceTypes
open RuntimeBodyPlan (Queues)

structure GraphResult {artifact context description} (mode : OperationMode artifact)
    (graph : StaticOperation.CheckedGraph artifact.sources context description) (demand : StaticOperation.Paths)
    (before : Queues) (origin : RuntimeGraphOperation.Origin graph := .unlocated) where
  after : Queues
  discovery : Discovery
  receipts : List mode.Receipt
  planned : Option (Σ read : RuntimeBodyPlanReaders.GraphRead mode.preparation graph demand before origin,
    PLift (read.cut.after = after))

private def graphRead {artifact context description} (mode : OperationMode artifact)
    (next : {owner name : String} → (scope : Scope artifact owner name) → (request : Context) →
      WorkM (BodyResult mode scope request))
    (graph : StaticOperation.CheckedGraph artifact.sources context description) (demand : StaticOperation.Paths)
    (before : Queues) (explicit : Bool) (origin : RuntimeGraphOperation.Origin graph := .unlocated) :
    WorkM (GraphResult mode graph demand before origin) := do
  match mode with
  | .extended preparation =>
    let read ← RuntimeBodyPlanReaders.readGraph preparation graph demand before origin
    return ⟨read.cut.after,⟨preparation.rows read.graphPlan.evidence,preparation.roots read.graphPlan.evidence⟩,
      [read.receipt],some ⟨read,⟨rfl⟩⟩⟩
  | .strict =>
    let occurrences ← StaticOperation.readOccurrences description
    let indices := RuntimeProviderHeaders.providerIndices description occurrences
    guard (indices.length ≤ before.bodies.length) .request
    let (_,references) ← OperationMode.takeReferences (artifact := artifact) .strict explicit before.references
    guard (!graph.hasMeaningRequirements) .request
    exactWork (Exact.charge (16*(indices.length+before.bodies.length+1)))
    let (discovery,bodies) ← indices.foldlM (fun (discovery,bodies) index => do
      let bodyRequest :: rest := bodies | throw .request
      let header ← RuntimeProviderHeader.read artifact graph index bodyRequest
      guard (!header.original.supplied.arguments.hasMeaningRequirements) .request
      let body := header.original.body.checked
      let child ← next (.supplied body.signature body.events body.summary.staticRows true) bodyRequest.2
      return (discovery.append (Discovery.append ⟨header.original.supplied.arguments.sourceRows,header.roots⟩ child.discovery),rest))
      (⟨graph.sourceRows,[]⟩,before.bodies)
    return ⟨{before with bodies,references},discovery,[],none⟩

structure PrefixResult {artifact owner name} (mode : OperationMode artifact)
    (signature : SourceRuntimeContext.Signature artifact.sources owner name)
    (actuals : List (Sigma (StaticOperation.Actual artifact.sources signature.context))) (before : Queues) where
  after : Queues
  discovery : Discovery
  receipts : List mode.Receipt
  planned : Option (RuntimeBodyPlan.Prefixes mode.preparation signature actuals before after)

private def prefixRead {artifact owner name} (mode : OperationMode artifact)
    (next : {owner name : String} → (scope : Scope artifact owner name) → (request : Context) → WorkM (BodyResult mode scope request))
    (signature : SourceRuntimeContext.Signature artifact.sources owner name)
    (actuals : List {actual : Sigma (StaticOperation.Actual artifact.sources signature.context) //
      actual ∈ signature.operations.actuals})
    (incoming : Option (RuntimeGraphOperation.Incoming artifact.sources signature))
    (before : Queues) (explicit : Bool) : WorkM (PrefixResult mode signature (actuals.map Subtype.val) before) :=
  let visit : Nat → (remaining : List {actual : Sigma (StaticOperation.Actual artifact.sources signature.context) //
      actual ∈ signature.operations.actuals}) →
      (queues : Queues) → WorkM (PrefixResult mode signature (remaining.map Subtype.val) queues) :=
    Nat.rec (fun remaining queues => match remaining with
      | [] => pure ⟨queues,{},[],some (.nil queues)⟩
      | _ :: _ => throw .limit)
      (fun _ tail remaining queues => do
        match remaining with
        | [] => return ⟨queues,{},[],some (.nil queues)⟩
        | actual :: rest =>
          let origin ← match incoming with
            | none => pure .unlocated
            | some call => call.origin actual.val actual.property
          let first ← graphRead mode next actual.val.2.graph (RuntimeGraphOperation.required signature actual.val.1.1)
            queues explicit origin
          let last ← tail rest first.after
          exactWork (Exact.charge (first.discovery.rows.length+first.discovery.roots.length+first.receipts.length+1))
          let planned := match first.planned,last.planned with
            | some ⟨head,same⟩,some tail => some
                (RuntimeBodyPlan.Prefixes.cons head.cut origin head.graphPlan (same.down.symm ▸ tail))
            | _,_ => none
          return ⟨last.after,first.discovery.append last.discovery,first.receipts ++ last.receipts,planned⟩)
  visit actuals.length actuals before

structure ArmsResult {artifact owner name offset selector target} (mode : OperationMode artifact)
    (table : QuantumArms.Table artifact.sources owner name offset selector target)
    (indices : List (Fin table.arms.length)) (before : Queues) where
  after : Queues
  discovery : Discovery
  receipts : List mode.Receipt
  planned : Option (RuntimeBodyPlan.Arms mode.preparation table indices before after)

private def armsRead {artifact owner name offset selector target} (mode : OperationMode artifact)
    (next : {owner name : String} → (scope : Scope artifact owner name) → (request : Context) → WorkM (BodyResult mode scope request))
    (table : QuantumArms.Table artifact.sources owner name offset selector target)
    (subjects : List RuntimeContextRequest.Arm)
    (indices : List (Fin table.arms.length)) (before : Queues) (explicit : Bool) :
    WorkM (ArmsResult mode table indices before) :=
  let visit : Nat → (remaining : List (Fin table.arms.length)) → (queues : Queues) →
      WorkM (ArmsResult mode table remaining queues) :=
    Nat.rec (fun remaining queues => match remaining with
      | [] => pure ⟨queues,{},[],some (.nil queues)⟩
      | _ :: _ => throw .limit)
      (fun _ tail remaining queues => do
        match remaining with
        | [] => return ⟨queues,{},[],some (.nil queues)⟩
        | index :: rest =>
          let subject ← lift (readOption subjects[index.val]?)
          let _ ← lift (readOption artifact.programs[subject.implementation]?)
          let _ ← lift (readOption artifact.programs[subject.controlled]?)
          let first ← graphRead mode next (table.arms[index]).operation.graph OperationAccess.controllable queues explicit
            (.arm (table.arms[index]).operation)
          let last ← tail rest first.after
          exactWork (Exact.charge (first.discovery.rows.length+first.discovery.roots.length+first.receipts.length+1))
          let planned := match first.planned,last.planned with
            | some ⟨head,same⟩,some tail => some
                (RuntimeBodyPlan.Arms.cons head.cut head.graphPlan
                  (Eq.mpr (congrArg (fun queues =>
                    RuntimeBodyPlan.Arms mode.preparation table rest queues last.after) same.down) tail))
            | _,_ => none
          let discovery := first.discovery.append (Discovery.append ⟨[],[subject.implementation,subject.controlled]⟩ last.discovery)
          return ⟨last.after,discovery,first.receipts ++ last.receipts,planned⟩)
  visit indices.length indices before

private def collectEvents {artifact owner name} (mode : OperationMode artifact) (scope : Scope artifact owner name)
    (step : (event : SourceRuntimeContext.Event artifact.sources owner) → (position : SourceSequence.Position) →
      (before : Queues) → WorkM (EventResult mode scope event position before))
    (pairs : List (SourceRuntimeContext.Event artifact.sources owner × SourceSequence.Position)) (before : Queues) :
    WorkM (EventsResult mode scope pairs before) :=
  let visit : Nat → (remaining : List (SourceRuntimeContext.Event artifact.sources owner × SourceSequence.Position)) →
      (queues : Queues) → WorkM (EventsResult mode scope remaining queues) :=
    Nat.rec (fun remaining queues => match remaining with
      | [] => pure ⟨queues,{},[],scope.emptyEvents mode.preparation queues⟩
      | _ :: _ => throw .limit)
      (fun _ tail remaining queues => do
        match remaining with
        | [] => return ⟨queues,{},[],scope.emptyEvents mode.preparation queues⟩
        | (event,position) :: rest =>
          let first ← step event position queues
          let last ← tail rest first.after
          exactWork (Exact.charge (first.discovery.rows.length+first.discovery.roots.length+first.receipts.length+1))
          return ⟨last.after,first.discovery.append last.discovery,first.receipts ++ last.receipts,
            scope.consEvents mode.preparation first.data last.data⟩)
  visit pairs.length pairs before

private def assembleBody {artifact owner name} (mode : OperationMode artifact) (scope : Scope artifact owner name)
    (request : Context) (positionsCount : request.positions.length = scope.events.length)
    (offsets : request.positions.map (·.offset) = scope.events.map SourceRuntimeContext.Event.offset)
    (actuals : List {actual : Sigma (StaticOperation.Actual artifact.sources scope.signature.context) //
      actual ∈ scope.signature.operations.actuals})
    (originalActuals : RuntimeInterval.Computed
      (if scope.prefixRequired then RuntimeProviderHeaders.originalActualSlots scope.signature.operations else pure []) actuals)
    (prefixResult : PrefixResult mode scope.signature (actuals.map Subtype.val) (Queues.ofContext request))
    (events : EventsResult mode scope (scope.events.zip request.positions) prefixResult.after)
    (exhausted : events.after.isEmpty = true) : scope.BodyData mode.preparation request :=
  match scope with
  | .supplied .. => ()
  | .original _ _ =>
    match prefixResult.planned,events.data with
    | some prefixPlans,some eventPlans =>
      some (.mk positionsCount offsets actuals originalActuals prefixResult.after prefixPlans
        events.after eventPlans exhausted)
    | _,_ => none

def traverse (artifact : Artifact) (mode : OperationMode artifact) : Nat → {owner name : String} →
    (scope : Scope artifact owner name) → (request : Context) → WorkM (BodyResult mode scope request) :=
  Nat.rec (fun {_ _} _ _ => throw .limit)
    (fun _ next {owner name} scope request => do
      let signature := scope.signature
      let events := scope.events
      guard (request.positions.length ≤ 4096 && request.sites.length ≤ 128 && request.calls.length ≤ 4096 &&
        request.branches.length ≤ 4096 && request.bodies.length ≤ 4096 && request.references.length ≤ 4096) .limit
      exactWork (Exact.charge (32*(events.length+request.positions.length+request.sites.length+
        request.calls.length+request.branches.length+request.bodies.length+request.references.length+1)^2))
      if offsets : request.positions.map (·.offset) = events.map SourceRuntimeContext.Event.offset then
        let _ ← if scope.prefixRequired then mode.checkSignature signature scope.incoming.isSome else pure ()
        let originals ← NaturalAffine.witness
          (if scope.prefixRequired then RuntimeProviderHeaders.originalActualSlots signature.operations else pure [])
        let prefixResult ← prefixRead mode next signature originals.val scope.incoming (Queues.ofContext request) (!request.references.isEmpty)
        let eventStep : (event : SourceRuntimeContext.Event artifact.sources owner) → (position : SourceSequence.Position) →
            (before : Queues) → WorkM (EventResult mode scope event position before) := fun event position before => do
          exactWork (Exact.charge (before.references.length+1))
          match event with
          | .primitive event =>
            let data : scope.EventData mode.preparation (.primitive event) position before before := by
              cases scope with
              | supplied => exact ()
              | original => exact some (.primitive event)
            return ⟨before,⟨CallName.sourceRows event.candidate,[]⟩,[],data⟩
          | .phase event =>
            let data : scope.EventData mode.preparation (.phase event) position before before := by
              cases scope with
              | supplied => exact ()
              | original => exact some (.phase event)
            return ⟨before,⟨CallName.sourceRows event.application.candidate ++ event.naturals.sourceRows,[]⟩,[],data⟩
          | .named event =>
            match calls : before.calls with
            | [] => throw .request
            | (callPosition,child) :: remaining =>
              if located : callPosition = position ∧ position.offset = event.call.calleeOffset then
                let body ← NaturalAffine.witness (SourceRuntimeTrace.readNamedBody event)
                let nested ← next (scope.named body.val (some (.named event body.val.originalSignature))) child
                let after := {before with calls := remaining}
                let data : scope.EventData mode.preparation (.named event) position before after := by
                  cases scope with
                  | supplied => exact ()
                  | original source =>
                    if callerName : event.target.callerName = name then
                      exact nested.data.map (fun childPlan => .named callPosition child remaining calls located callerName
                        body.val (by with_reducible exact body.property) childPlan)
                    else exact none
                return ⟨after,⟨event.target.sourceRows ++ nested.discovery.rows,nested.discovery.roots⟩,nested.receipts,data⟩
              else throw .request
          | .selection tokens parsed original selector target lexical naturals held remaining =>
            match sites : before.sites with
            | [] => throw .request
            | site :: rest =>
              if located : site.position = position ∧ position.offset = parsed.keyword.span.startByte then
                let table ← NaturalAffine.witness (QuantumArms.readArmsWithInstantiation signature.original signature.instantiation
                  signature.supply parsed.keyword.span.startByte selector.basis target.basis (some naturals) lexical)
                if count : site.arms.length = table.val.arms.length then
                  guard (site.attached.inputs.map (·.basis) == [selector.basis,target.basis] &&
                    site.attached.outputs.map (·.basis) == [selector.basis,target.basis] &&
                    site.required.inputs.map (·.basis) == [selector.basis,target.basis] &&
                    site.required.outputs.map (·.basis) == [selector.basis,target.basis] &&
                    site.attached.publicEffect == .unitary && site.required.publicEffect == .unitary) .request
                  let arms ← armsRead mode next table.val site.arms (List.finRange table.val.arms.length)
                    {before with sites := rest} (!request.references.isEmpty)
                  let data : scope.EventData mode.preparation
                      (.selection tokens parsed original selector target lexical naturals held remaining) position before arms.after := by
                    cases scope with
                    | supplied => exact ()
                    | original source =>
                      exact arms.planned.map (fun plans => .selection site rest sites located table.val
                        (by with_reducible simpa only [signature,Scope.signature] using table.property) count arms.after plans)
                  return ⟨arms.after,⟨Carrier.sourceRows site.attached site.required ++ table.val.arms.flatMap (·.sourceRows) ++
                    arms.discovery.rows,arms.discovery.roots⟩,
                    arms.receipts,data⟩
                else throw .request
              else throw .request
          | .operation event =>
            match calls : before.calls with
            | [] => throw .request
            | (callPosition,child) :: remaining =>
              if located : callPosition = position ∧ position.offset = event.call.calleeOffset then
                if childEmpty : child.positions.isEmpty = true ∧ child.sites.isEmpty = true ∧
                    child.calls.isEmpty = true ∧ child.branches.isEmpty = true then
                  let childQueues := Queues.ofContext child
                  let graph ← graphRead mode next event.operation.graph OperationAccess.applicable childQueues
                    (!child.references.isEmpty) (.application event)
                  if consumed : graph.after.bodies.isEmpty = true ∧ graph.after.references.isEmpty = true then
                    let after := {before with calls := remaining}
                    let data : scope.EventData mode.preparation (.operation event) position before after := by
                      cases scope with
                      | supplied => exact ()
                      | original source =>
                        match graph.planned with
                        | none => exact none
                        | some ⟨planned,same⟩ =>
                          have bodiesEmpty : planned.cut.remainingBodies = [] := by
                            have empty := consumed.1
                            rw [← same.down] at empty
                            change planned.cut.remainingBodies.isEmpty = true at empty
                            cases actual : planned.cut.remainingBodies with
                            | nil => rfl
                            | cons head tail => rw [actual] at empty; cases empty
                          have refsEmpty : planned.cut.remainingReferences = [] := by
                            have empty := consumed.2
                            rw [← same.down] at empty
                            change planned.cut.remainingReferences.isEmpty = true at empty
                            cases actual : planned.cut.remainingReferences with
                            | nil => rfl
                            | cons head tail => rw [actual] at empty; cases empty
                          have bodies : planned.cut.implementations = child.bodies := by
                            have bound := planned.cut.bodies
                            simpa only [childQueues,Queues.ofContext,bodiesEmpty,List.append_nil] using bound.symm
                          have groups : child.references = [planned.cut.references] := by
                            simpa only [childQueues,Queues.ofContext,refsEmpty] using planned.cut.groups
                          have ownGraph : RuntimeBodyPlan.Graph mode.preparation event.operation.graph OperationAccess.applicable
                              child.bodies planned.cut.references (.application event) := by
                            rw [← bodies]
                            exact planned.graphPlan
                          exact some (.operation callPosition child remaining calls located childEmpty
                            planned.cut.references groups ownGraph)
                    return ⟨after,⟨event.operation.rows ++ event.naturals.sourceRows ++ graph.discovery.rows,
                      graph.discovery.roots⟩,graph.receipts,data⟩
                  else throw .request
                else throw .request
              else throw .request
          | .conditional event thenEvents elseEvents =>
            match branches : before.branches with
            | [] => throw .request
            | (branchPosition,left,right) :: rest =>
              if located : branchPosition = position ∧ position.offset = event.written.parts.keyword.span.startByte then
                let source ← scope.readBranch event
                let leftRead ← next (scope.branchLeft source) left
                let rightRead ← next (scope.branchRight source) right
                let after := {before with branches := rest}
                let data : scope.EventData mode.preparation (.conditional event thenEvents elseEvents) position before after := by
                  cases scope with
                  | supplied => exact ()
                  | original subject =>
                    match leftRead.data,rightRead.data with
                    | some lp,some rp => exact some (.conditional branchPosition left right rest branches located source.callerName
                        source.source source.original lp rp)
                    | _,_ => exact none
                return ⟨after,⟨event.naturals.sourceRows ++ leftRead.discovery.rows ++ rightRead.discovery.rows,
                  leftRead.discovery.roots ++ rightRead.discovery.roots⟩,leftRead.receipts ++ rightRead.receipts,data⟩
              else throw .request
          | .transform event =>
            match calls : before.calls with
            | [] => throw .request
            | (callPosition,child) :: remaining =>
              if located : callPosition = position then
                let transform ← NaturalAffine.witness (RuntimeTransformRequest.read event position child)
                let roots ← subjectRoots artifact transform.val.subject
                let nested ← next (scope.named transform.val.source) transform.val.context
                let after := {before with calls := remaining}
                let data : scope.EventData mode.preparation (.transform event) position before after := by
                  cases scope with
                  | supplied => exact ()
                  | original source =>
                    exact nested.data.map (fun childPlan => .transform child remaining
                      (located ▸ calls) transform.val (by with_reducible exact transform.property) childPlan)
                return ⟨after,⟨event.target.sourceRows ++ event.counts.flatMap (·.checked.rows) ++
                  nested.discovery.rows,roots ++ nested.discovery.roots⟩,nested.receipts,data⟩
              else throw .request
          | .basis event =>
            let checked ← RuntimeBasisAction.readSource event
            let rows ← ordinaryRows artifact.sources 128 checked.body.events
            let data : scope.EventData mode.preparation (.basis event) position before before := by
              cases scope with
              | supplied => exact ()
              | original => exact some (.basis checked)
            return ⟨before,⟨event.staticRows ++ checked.body.staticRows ++ rows,[]⟩,[],data⟩
          | .computed event children =>
            if event.written.parts.logical.isSome then
              let prepared ← RuntimeCertifiedComputed.prepare event
              let rows ← ordinaryRows artifact.sources 128 prepared.predicate.body.checked.events
              let data : scope.EventData mode.preparation (.computed event children) position before before := by
                cases scope with
                | supplied => exact ()
                | original => exact some (.certifiedComputed prepared)
              return ⟨before,⟨prepared.rows ++ rows,[]⟩,[],data⟩
            else
              let prepared ← RuntimeComputedUse.prepare event
              let rows ← ordinaryRows artifact.sources 128 prepared.predicate.body.checked.events
              let data : scope.EventData mode.preparation (.computed event children) position before before := by
                cases scope with
                | supplied => exact ()
                | original => exact some (.computed prepared)
              return ⟨before,⟨prepared.rows ++ rows,[]⟩,[],data⟩
          | .workspace event children =>
            let prepared ← RuntimeWorkspace.readOriginal event children
            let data : scope.EventData mode.preparation (.workspace event children) position before before := by
              cases scope with
              | supplied => exact ()
              | original => exact some (.workspace prepared)
            return ⟨before,⟨prepared.rows,[]⟩,[],data⟩
          | .registerPrimitive event =>
            guard (event.kind == .takeBit || event.kind == .putBit) .request
            let data : scope.EventData mode.preparation (.registerPrimitive event) position before before := by
              cases scope with
              | supplied => exact ()
              | original => exact some (.register event)
            return ⟨before,⟨(SourceRuntimeContext.Event.registerPrimitive event).staticRows,[]⟩,[],data⟩
          | .matching .. | .staticConditional .. => throw .request
        let outerStep : (event : SourceRuntimeContext.Event artifact.sources owner) → (position : SourceSequence.Position) →
            (before : Queues) → WorkM (EventResult mode scope event position before) := fun event position before => do
          match event with
          | .staticConditional event children =>
            let source ← NaturalAffine.witness (RuntimeStaticPrimitive.readContinuation event)
            let partition := before.takeStatic position
            let positions ← NaturalAffine.witness
              (source.val.positions position (before.calls.map (·.1)) (before.sites.map (·.position)) partition.1)
            if count : positions.val.length = source.val.selected.result.events.length then
              let inner ← collectEvents mode scope eventStep (source.val.selected.result.events.zip positions.val) partition.2
              let data : scope.EventData mode.preparation (.staticConditional event children) position before inner.after := by
                cases scope with
                | supplied => exact ()
                | original subject =>
                  exact inner.data.map (fun events => .staticConditional source.val
                    (by with_reducible exact source.property) positions.val
                    (by with_reducible exact positions.property) count events)
              let rows := event.naturals.sourceRows ++ source.val.selected.result.staticRows
              exactWork (Exact.charge (16*(source.val.selected.result.events.length+rows.length+inner.discovery.rows.length+
                inner.discovery.roots.length+1)))
              return ⟨inner.after,⟨rows ++ inner.discovery.rows,inner.discovery.roots⟩,inner.receipts,data⟩
            else throw .request
          | other => eventStep other position before
        let checked ← collectEvents mode scope outerStep (events.zip request.positions) prefixResult.after
        if exhausted : checked.after.isEmpty = true then
          have count : request.positions.length = scope.events.length := by simpa only [List.length_map] using congrArg List.length offsets
          let data := assembleBody mode scope request count offsets originals.val
            (by with_reducible exact originals.property) prefixResult checked exhausted
          let initial : Discovery := ⟨signature.sourceRows ++ scope.staticRows,[]⟩
          return ⟨initial.append (prefixResult.discovery.append checked.discovery),prefixResult.receipts ++ checked.receipts,data⟩
        else throw .request
      else throw .request)

/-- Existing metadata callers keep their exact signature and source view. -/
def traverseUsing (artifact : Artifact) (operationMode : OperationMode artifact) (fuel : Nat) {owner name : String}
    (signature : SourceRuntimeContext.Signature artifact.sources owner name)
    (events : List (SourceRuntimeContext.Event artifact.sources owner)) (staticRows : List SourceRows.Row)
    (request : Context) (prefixRequired : Bool) : WorkM (Discovery × List operationMode.Receipt) := do
  let result ← traverse artifact operationMode fuel (.supplied signature events staticRows prefixRequired) request
  return (result.discovery,result.receipts)

def traverseStrict (artifact : Artifact) (fuel : Nat) {owner name : String}
    (signature : SourceRuntimeContext.Signature artifact.sources owner name)
    (events : List (SourceRuntimeContext.Event artifact.sources owner)) (staticRows : List SourceRows.Row)
    (request : Context) (prefixRequired : Bool) : WorkM Discovery := do
  let (discovery,_) ← traverseUsing artifact .strict fuel signature events staticRows request prefixRequired
  return discovery

structure Planned {artifact : Artifact} (preparation : RuntimeGraphOperation.Preparation artifact)
    {owner name} (source : SourceRuntimeScope.Subject artifact.sources owner name) (request : Context) where
  discovery : Discovery
  receipts : List (RuntimeGraphOperation.PreparedReceipt preparation)
  plan : RuntimeBodyPlan.Body preparation source request
  traversed : RuntimeInterval.Computed (traverse artifact (.extended preparation) 128 (.original source) request)
    (⟨discovery,receipts,some plan⟩ : BodyResult (.extended preparation) (.original source) request)

def visitPlanned {artifact : Artifact} (preparation : RuntimeGraphOperation.Preparation artifact)
    {owner name} (source : SourceRuntimeScope.Subject artifact.sources owner name) (request : Context) :
    WorkM (Planned preparation source request) := do
  let checked ← NaturalAffine.witness (traverse artifact (.extended preparation) 128 (.original source) request)
  match checked with
  | ⟨⟨_,_,none⟩,_⟩ => throw .request
  | ⟨⟨discovery,receipts,some plan⟩,traversed⟩ =>
    return ⟨discovery,receipts,plan,by with_reducible exact traversed⟩

end QleisliKernel.Qirf.RuntimeBodyDiscovery
