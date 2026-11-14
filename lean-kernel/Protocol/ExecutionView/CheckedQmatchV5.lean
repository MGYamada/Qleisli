import Protocol.ExecutionView.QmatchV5
import QleisliKernel.Target.CanonicalOpenQasmPlacement
import Protocol.ExecutionView.Packet
import QleisliKernel.Qirf.RuntimeBodyOperations

/-! Check the complete original v5 body before comparing its execution view.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.CheckedQmatchV5
open Gate
open QleisliKernel.Qirf QleisliKernel.SourceTypes

private def outsideRoot {sources catalogue queue} (root : Nat)
    (entry : @SourcePendingMeaning.Entry sources catalogue queue) : Bool :=
  match entry.subject with
  | .demand invocation _ => invocation.id.root != root
  | _ => false

private def meterResiduals {artifact owner name arguments context order runtime}
    {prepared : RuntimeBodyOperations.Prepared artifact owner name arguments context}
    (checked : RuntimeBodyOperations.Checked prepared order runtime) : Finite.WorkM Unit := do
  Finite.exactWork (Exact.charge (16*(prepared.source.pending.entries.length+1)*
    (checked.coverage.residual.length+1)))
  for position in checked.coverage.residual do
    match prepared.source.pending.entries[position.val].subject with
    | .demand invocation _ => Finite.exactWork (Exact.charge (16*(invocation.depth+1)^2))
    | _ => pure ()

structure RootCoverage {artifact owner name arguments context order runtime}
    {prepared : RuntimeBodyOperations.Prepared artifact owner name arguments context}
    (checked : RuntimeBodyOperations.Checked prepared order runtime) where
  root : RuntimeDutyInvocation.Identified prepared.source.pending.queue (.root prepared.source.body)
  rootRead : RuntimeInterval.Computed
    (RuntimeDutyInvocation.identify prepared.source.pending.queue (.root prepared.source.body)) root
  otherRoots : ∀ position ∈ checked.coverage.residual,
    outsideRoot root.record.val prepared.source.pending.entries[position.val] = true

private def readRootCoverage {artifact owner name arguments context order runtime}
    {prepared : RuntimeBodyOperations.Prepared artifact owner name arguments context}
    (checked : RuntimeBodyOperations.Checked prepared order runtime) : Finite.WorkM (RootCoverage checked) := do
  let root ← NaturalAffine.witness
    (RuntimeDutyInvocation.identify prepared.source.pending.queue (.root prepared.source.body))
  meterResiduals checked
  if otherRoots : checked.coverage.residual.all
      (fun position => outsideRoot root.val.record.val prepared.source.pending.entries[position.val]) = true then
    return ⟨root.val,by with_reducible exact root.property,List.all_eq_true.mp otherRoots⟩
  else throw .request

/-- Standalone basis and Meaning checks retain the full catalogue and queue.
They cover the selected original invocation and its callees. Other roots
retain their pending positions for separate checks. -/
inductive CheckedScope {artifact owner name arguments context order runtime}
    {prepared : RuntimeBodyOperations.Prepared artifact owner name arguments context}
    (checked : RuntimeBodyOperations.Checked prepared order runtime) where
  | selection (present : 0 < checked.selections.count) (complete : checked.coverage.residual = [])
  | basis (noSelections : checked.selections.count = 0)
      (found : ∃ before after,(RuntimeSelectionSteps.readBasisResult checked.checked.result).run before = (.ok true,after))
      (coverage : RootCoverage checked)
  | meaning (noSelections : checked.selections.count = 0)
      (found : ∃ before after,checked.coverage.hasStandaloneMeaning.run before = (.ok true,after))
      (coverage : RootCoverage checked)

def CheckedScope.includes {artifact owner name arguments context order runtime}
    {prepared : RuntimeBodyOperations.Prepared artifact owner name arguments context}
    {checked : RuntimeBodyOperations.Checked prepared order runtime}
    (scope : CheckedScope checked) (position : RuntimeArmDutyCoverage.Position prepared) : Prop :=
  match scope with
  | .selection .. => True
  | .basis _ _ coverage | .meaning _ _ coverage =>
    outsideRoot coverage.root.record.val prepared.source.pending.entries[position.val] = false

theorem CheckedScope.residual_excluded {artifact owner name arguments context order runtime}
    {prepared : RuntimeBodyOperations.Prepared artifact owner name arguments context}
    {checked : RuntimeBodyOperations.Checked prepared order runtime}
    (scope : CheckedScope checked) (position : RuntimeArmDutyCoverage.Position prepared)
    (within : scope.includes position) : position ∉ checked.coverage.residual := by
  cases scope with
  | selection _ complete =>
    rw [complete]
    exact List.not_mem_nil
  | basis _ _ coverage | meaning _ _ coverage =>
    intro remaining
    exact Bool.noConfusion (within.symm.trans (coverage.otherRoots position remaining))

private def readScope {artifact owner name arguments context order runtime}
    {prepared : RuntimeBodyOperations.Prepared artifact owner name arguments context}
    (checked : RuntimeBodyOperations.Checked prepared order runtime) : Finite.WorkM (CheckedScope checked) := do
  let selected ← Protocol.QmatchV5.usesSelection 129 context
  Finite.guard (selected == (0 < checked.selections.count)) .request
  if selection : 0 < checked.selections.count then
    if complete : checked.coverage.residual = [] then return .selection selection complete
    else throw .request
  else
    let noSelections := Nat.eq_zero_of_not_pos selection
    if ← Protocol.QmatchV5.hasMeaningGroup 129 context then
      let meaning ← NaturalAffine.witness checked.coverage.hasStandaloneMeaning
      if found : meaning.val = true then
        return .meaning noSelections (found ▸ meaning.property) (← readRootCoverage checked)
      else throw .request
    else
      let basis ← NaturalAffine.witness (RuntimeSelectionSteps.readBasisResult checked.checked.result)
      if found : basis.val = true then
        return .basis noSelections (found ▸ basis.property) (← readRootCoverage checked)
      else throw .request

structure Original (bytes : ByteArray) where
  body : ByteArray
  requestBytes : ByteArray
  packet : Protocol.Validity.packet bytes = .ok (body,some requestBytes)
  artifact : Artifact
  order : Array Nat
  artifactRead : RuntimeInterval.Computed (Protocol.Qirf.readAll body) (artifact,order)
  request : Protocol.QmatchV5.Request
  requestRead : RuntimeInterval.Computed (Protocol.QmatchV5.readRequest requestBytes) request
  compatible : request.compatible = true
  prepared : RuntimeBodyOperations.Prepared artifact request.source.moduleName request.source.functionName
    request.source.arguments request.context
  preparedRead : RuntimeInterval.Computed (RuntimeBodyOperations.prepare artifact request.source.moduleName
    request.source.functionName request.source.arguments request.context) prepared
  checked : RuntimeBodyOperations.Checked prepared order request.combinedRuntime
  bodyRead : RuntimeInterval.Computed (RuntimeBodyOperations.read prepared order request.combinedRuntime) checked
  sourceScope : CheckedScope checked
  scopeRead : RuntimeInterval.Computed (readScope checked) sourceScope

def readOriginal (bytes : ByteArray) : Finite.WorkM (Original bytes) := do
  match packet : Protocol.Validity.packet bytes with
  | .error _ => throw .invalid
  | .ok (_,none) => throw .request
  | .ok (body,some requestBytes) =>
    let artifact ← NaturalAffine.witness (Protocol.Qirf.readAll body)
    let request ← NaturalAffine.witness (Protocol.QmatchV5.readRequest requestBytes)
    if compatible : request.val.compatible = true then
      let prepared ← NaturalAffine.witness (RuntimeBodyOperations.prepare artifact.val.1
        request.val.source.moduleName request.val.source.functionName request.val.source.arguments request.val.context)
      let checked ← NaturalAffine.witness (RuntimeBodyOperations.read prepared.val artifact.val.2 request.val.combinedRuntime)
      let scope ← NaturalAffine.witness (readScope checked.val)
      return ⟨body,requestBytes,packet,artifact.val.1,artifact.val.2,
        by with_reducible exact artifact.property,
        request.val,by with_reducible exact request.property,compatible,
        prepared.val,by with_reducible exact prepared.property,
        checked.val,by with_reducible exact checked.property,
        scope.val,by with_reducible exact scope.property⟩
    else throw .request

def description {bytes : ByteArray} (original : Original bytes) : Finite.WorkM Value :=
  ExecutionView.QmatchV5.description original.artifact original.checked.root original.request

def check (bytes supplied : ByteArray) : CheckM (Original bytes) := do
  guard (framed supplied) .invalidView
  let checked ← native (readOriginal bytes)
  let view ← native (description checked)
  let expected ← lift ((encode view).mapError fun _ => .encoding)
  guard (supplied.data == expected.data) .decodedView
  return checked

structure Binding (bytes supplied : ByteArray) (checked : Original bytes) (work left : Nat) where
  afterCore : Nat
  view : Value
  framed : framed supplied = true
  core : (readOriginal bytes).run work = (.ok checked,afterCore)
  described : (description checked).run afterCore = (.ok view,left)
  compared : encode view = .ok supplied

theorem check_binding (bytes supplied : ByteArray) (checked : Original bytes) (work left : Nat)
    (ok : (check bytes supplied).run work = (.ok checked,left)) :
    Nonempty (Binding bytes supplied checked work left) := by
  unfold check at ok
  obtain ⟨_,a,hf,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨result,b,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨view,c,hv,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨expected,d,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,e,hs,h⟩ := bind_success _ _ _ _ _ h
  have final : checked = result ∧ left = e := by cases h; exact ⟨rfl,rfl⟩
  rcases final with ⟨rfl,rfl⟩
  have frame := guard_success _ _ _ _ hf
  have encoded := lift_success _ _ _ _ he
  have same := guard_success _ _ _ _ hs
  have equalData : supplied.data = expected.data := beq_iff_eq.mp same.1
  have equal : supplied = expected := by cases supplied; cases expected; cases equalData; rfl
  have encoding : encode view = .ok supplied := by
    cases value : encode view <;> simp_all [Except.mapError]
  have start := frame.2
  have encodedWork := encoded.2
  have comparedWork := same.2
  subst a; subst d; subst c
  exact ⟨⟨b,view,frame.1,native_success _ _ _ _ hc,native_success _ _ _ _ hv,encoding⟩⟩

/-- Every pending position in the reported scope has its own unambiguous
discharge in the original queue. -/
theorem Original.covers {bytes : ByteArray} (original : Original bytes)
    (position : RuntimeArmDutyCoverage.Position original.prepared)
    (within : original.sourceScope.includes position)
    (pending : original.prepared.source.pending.entries[position.val].unconsumed = true) :
    ∃ discharge : RuntimeArmDutyCoverage.Discharge original.checked.coverage.candidates position,
      ⟨position,discharge⟩ ∈ original.checked.coverage.consumed := by
  let coverage := original.checked.coverage
  have all : position ∈ List.finRange original.prepared.source.pending.entries.length := List.mem_finRange _
  have covered : RuntimeArmDutyCoverage.covered coverage.candidates position = true := by
    cases found : RuntimeArmDutyCoverage.covered coverage.candidates position with
    | true => rfl
    | false =>
      have residual : position ∈ coverage.residual := by
        change position ∈ coverage.result.residual
        rw [coverage.result.exactResidual]
        exact List.mem_filter.mpr ⟨all,by simp [RuntimeArmDutyCoverage.remaining,pending,found]⟩
      exact False.elim (original.sourceScope.residual_excluded position within residual)
  have mapped : position ∈ coverage.result.consumed.map (·.1) := by
    rw [coverage.result.exactConsumed]
    exact List.mem_filter.mpr ⟨all,by simp [pending,covered]⟩
  obtain ⟨⟨index,witness⟩,present,same⟩ := List.mem_map.mp mapped
  change index = position at same
  subst index
  exact ⟨witness,present⟩

theorem Original.root_safe {bytes : ByteArray} (original : Original bytes) :
    original.artifact.programs[original.artifact.root]? = some original.checked.root.program ∧
      Semantics.Ownership.OwnershipSafe original.checked.root.program ∧
      Semantics.ClassicalScope.ScopeSafe original.checked.root.program := by
  obtain ⟨_,_,read⟩ := original.checked.fresh
  have root := QleisliKernel.Qirf.Validity.checkRootFromRoots_postcondition _ _ _ _ _ _ _ read
  obtain ⟨_,_,verified⟩ := root.verification
  exact ⟨root.original,Raw.Observation.verify_ownershipSafe _ _ _ _ _ verified,
    Raw.Observation.verify_scopeSafe _ _ _ _ _ verified⟩

open Target.CanonicalOpenQasmPlacement (Match Segment FinishedTrace finishTrace)

/-- Only coordinates in the emitted word are supplied by the producer. Source
offsets, bodies, owner roles and evidence come from the checked root actions. -/
structure WorkspaceAlignment where
  prefixMatches : List Match
  gateCount : Nat
  scratch : Option Nat

private def workspaceSegment {deps program block} (node : RuntimePureBody.Node deps program block) :
    Option (WorkspaceAlignment → Segment program) :=
  match node with
  | .workspace (sources := sources) (caller := caller) (event := event) (children := events)
      (start := start) (count := count) (before := before) interval _ original literal map =>
    some fun plan => ⟨sources,caller,deps,block,start,count,event,events,original,interval,before,literal,map,
      plan.prefixMatches,plan.gateCount,plan.scratch⟩
  | _ => none

def Original.workspaceSegments {bytes : ByteArray} (original : Original bytes) (plans : List WorkspaceAlignment) :
    Finite.WorkM (List (Segment original.checked.root.program)) := do
  let actions := original.checked.checked.result.actions
  Finite.exactWork (Exact.charge (32*(actions.length+plans.length+1)))
  let builders := actions.filterMap workspaceSegment
  Finite.guard (builders.length == plans.length) .request
  return List.zipWith (fun build plan => build plan) builders plans

structure CheckedPlacement {bytes : ByteArray} (original : Original bytes) {targetBytes capacity}
    (target : Target.CanonicalOpenQasmResources.Checked targetBytes capacity) (connected : Nat → Nat → Bool)
    (reserved synthesis : List Nat) (plans : List WorkspaceAlignment) (suffix : List Match) where
  segments : List (Segment original.checked.root.program)
  fromSource : RuntimeInterval.Computed (original.workspaceSegments plans) segments
  trace : FinishedTrace original.checked.root.program target connected reserved synthesis suffix
  checkedTrace : RuntimeInterval.Computed
    (finishTrace target original.checked.root.program connected reserved segments suffix synthesis) trace

/-- Check the emitted bytes and workspace intervals from the same original
source decision. This is the pure checker adapter, before native framing and
producer alignment are connected. -/
def Original.checkPlacement {bytes : ByteArray} (original : Original bytes) {targetBytes capacity}
    (target : Target.CanonicalOpenQasmResources.Checked targetBytes capacity) (connected : Nat → Nat → Bool)
    (reserved synthesis : List Nat) (plans : List WorkspaceAlignment) (suffix : List Match) :
    Finite.WorkM (CheckedPlacement original target connected reserved synthesis plans suffix) := do
  Finite.guard original.request.runtime.parameters.isEmpty .request
  let segments ← NaturalAffine.witness (original.workspaceSegments plans)
  let trace ← NaturalAffine.witness
    (finishTrace target original.checked.root.program connected reserved segments.val suffix synthesis)
  return ⟨segments.val,by exact segments.property,trace.val,by exact trace.property⟩

def input (value : Packet.Input) : CheckM (Original value.original) :=
  match value.scope with
  | .execution => check value.original value.graph
  | .inspection | .caller => throw .packet

def run (bytes : ByteArray) : CheckM (Σ value : Packet.Input, Original value.original) := do
  let value ← lift (Packet.read bytes)
  return ⟨value,← input value⟩

theorem run_binding (bytes : ByteArray) (checked : Σ value : Packet.Input, Original value.original)
    (work left : Nat) (ok : (run bytes).run work = (.ok checked,left)) :
    Packet.read bytes = .ok checked.1 ∧ checked.1.scope = .execution ∧
      Nonempty (Binding checked.1.original checked.1.graph checked.2 work left) := by
  unfold run at ok
  obtain ⟨value,middle,packet,rest⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨original,budget,consumed,returned⟩ := bind_success _ _ _ _ _ rest
  have parsed := lift_success _ _ _ _ packet
  have start := parsed.2
  subst middle
  have final : checked = ⟨value,original⟩ ∧ left = budget := by cases returned; exact ⟨rfl,rfl⟩
  rcases final with ⟨rfl,rfl⟩
  cases scope : value.scope with
  | inspection => simp only [input,scope] at consumed; cases consumed
  | caller => simp only [input,scope] at consumed; cases consumed
  | execution =>
    simp only [input,scope] at consumed
    exact ⟨parsed.1,rfl,check_binding _ _ _ _ _ consumed⟩

#print axioms check_binding
#print axioms Original.covers
#print axioms Original.root_safe
#print axioms run_binding
end QleisliKernel.Protocol.ExecutionView.CheckedQmatchV5
