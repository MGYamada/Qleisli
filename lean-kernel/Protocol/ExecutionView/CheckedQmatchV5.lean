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

/-- Each application can instantiate the independently checked local
workspace at its original position in the closed root. -/
private abbrev WorkspaceBuilder (program : Semantics.Observation.Program) :=
  WorkspaceAlignment → Finite.WorkM (Segment program)

private def workspaceSegment {deps program block} (root : Semantics.Observation.Program)
    (base : Nat) (node : RuntimePureBody.Node deps program block) :
    Option (WorkspaceBuilder root) :=
  match node with
  | .workspace (sources := sources) (caller := caller) (event := event) (children := events)
      (start := start) (count := count) (before := before) interval _ original literal map =>
    some fun plan => do
      Finite.exactWork (Exact.charge (32*(1+base+start+count+root.operations.length)))
      let actual := (root.operations.drop (base+start)).take count
      let localOps := (block.operations.drop start).take count
      if bound : ObservationBinding.lists (ObservationBinding.operation 65) actual localOps = true then
        let same := ObservationBinding.lists_sound (ObservationBinding.operation 65)
          (ObservationBinding.operation_sound 65) _ _ bound
        return ⟨sources,caller,deps,program,block,base,start,count,event,events,original,interval,same,before,
          literal,map,plan.prefixMatches,plan.gateCount,plan.scratch⟩
      else throw .request
  | _ => none

/-- Traverse only original named call intervals. Transform proof operands are
separate programs and cannot add source occurrences to the emitted root. -/
private def workspaceSteps {deps} (root : Semantics.Observation.Program) :
    (fuel : Nat) → {program : Semantics.Observation.Program} →
    {block : RuntimeInterval.Block deps program} →
    Nat → RuntimePureBody.Steps deps program block → Finite.WorkM (List (WorkspaceBuilder root))
  | _, _, _, _, .nil => pure []
  | 0, _, _, _, .cons .. => throw .limit
  | fuel+1, _, _, base, .cons first rest => do
    Finite.exactWork (Exact.charge 32)
    let here ← match first with
      | .pure node => pure ((workspaceSegment root base node).toList)
      | .named (start := start) _ _ _ _ _ _ children =>
        workspaceSteps root fuel (base+start) children
      | .conditional .. => throw .request
      | _ => pure []
    let tail ← workspaceSteps root fuel base rest
    Finite.exactWork (Exact.charge here.length)
    return here ++ tail

def Original.workspaceSegments {bytes : ByteArray} (original : Original bytes) (plans : List WorkspaceAlignment) :
    Finite.WorkM (List (Segment original.checked.root.program)) := do
  let steps := original.checked.checked.result.steps
  Finite.exactWork (Exact.charge (32*(steps.length+plans.length+1)))
  Finite.guard (steps.length ≤ 65536) .limit
  let builders ← workspaceSteps original.checked.root.program 65536 0 (RuntimePureBody.Steps.ofList steps)
  Finite.guard (builders.length == plans.length) .request
  (List.zipWith (fun build plan => build plan) builders plans).mapM id

structure CheckedPlacement {bytes : ByteArray} (original : Original bytes) {targetBytes capacity}
    (target : Target.CanonicalOpenQasmResources.Checked targetBytes capacity) (connected : Nat → Nat → Bool)
    (reserved synthesis : List Nat) (plans : List WorkspaceAlignment) (suffix : List Match) where
  segments : List (Segment original.checked.root.program)
  fromSource : RuntimeInterval.Computed (original.workspaceSegments plans) segments
  trace : FinishedTrace original.checked.root.program target connected reserved synthesis suffix
  checkedTrace : RuntimeInterval.Computed
    (finishTrace target original.checked.root.program connected reserved segments suffix synthesis) trace

/-- Check the emitted bytes and workspace intervals from the same original
source decision. The alignment supplies target coordinates only. The
checker derives original source intervals from the accepted root. -/
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


namespace PlacementPacket
open QleisliKernel.Target

structure PacketParts where
  source : ByteArray
  target : ByteArray
  alignment : ByteArray

/-- QTP1 carries the original QLV3 packet, literal target bytes and an alignment
proposal. All three lengths are checked before slicing the transport. -/
def split (bytes : ByteArray) : Except Gate.Error PacketParts := do
  if bytes.size < 16 || bytes.size > Packet.maxPacketBytes ||
      bytes.extract 0 4 != "QTP1".toUTF8 then throw .packet
  let sourceBytes := Packet.u32 bytes 4
  let targetBytes := Packet.u32 bytes 8
  let alignmentBytes := Packet.u32 bytes 12
  let targetStart := 16 + sourceBytes
  let alignmentStart := targetStart + targetBytes
  if sourceBytes < 28 || targetBytes == 0 || targetBytes > 1048576 ||
      alignmentBytes > 1048576 || bytes.size != alignmentStart + alignmentBytes then
    throw .packet
  return ⟨bytes.extract 16 targetStart, bytes.extract targetStart alignmentStart,
    bytes.extract alignmentStart bytes.size⟩

structure Alignment where
  capacity : Nat
  edges : List (Nat × Nat)
  reserved : List Nat
  synthesis : List Nat
  plans : List WorkspaceAlignment
  suffix : List Match

def Alignment.connected (alignment : Alignment) (a b : Nat) : Bool :=
  alignment.edges.contains (min a b, max a b)

private abbrev Reader := StateT Nat (Except Gate.Error)

private def natural (bytes : ByteArray) : Reader Nat := do
  let offset ← get
  if offset + 4 > bytes.size then throw .packet
  set (offset + 4)
  return Packet.u32 bytes offset

private def items {α : Type} (bytes : ByteArray) (cap : Nat) (read : Reader α) : Reader (List α) := do
  let count ← natural bytes
  let offset ← get
  -- Each element begins with at least one u32. Reject bad counts before allocation.
  if count > cap || count > (bytes.size - offset)/4 then throw .packet
  (List.range count).mapM fun _ => read

private def wires (bytes : ByteArray) : Reader (List Nat) :=
  items bytes 12 (natural bytes)

private def action (bytes : ByteArray) : Reader Match := do
  match ← natural bytes with
  | 0 => return .original
  | 1 => return .route
  | 2 => return .decomposed (← natural bytes)
  | 3 => return .synthesized (← natural bytes) (← wires bytes)
  | 4 => return .optimized (← natural bytes) (← natural bytes) (← wires bytes)
  | _ => throw .packet

private def workspace (bytes : ByteArray) : Reader WorkspaceAlignment := do
  let prefixSteps ← items bytes 65536 (action bytes)
  let gates ← natural bytes
  let scratch ← natural bytes
  if scratch > 12 then throw .packet
  return ⟨prefixSteps,gates,if scratch == 12 then none else some scratch⟩

private def readAlignment (bytes : ByteArray) : Reader Alignment := do
  let capacity ← natural bytes
  if capacity > 12 then throw .packet
  let edges ← items bytes 66 (do
    let a ← natural bytes
    let b ← natural bytes
    if a ≥ b || b ≥ capacity then throw .packet
    return (a,b))
  if edges.eraseDups != edges then throw .packet
  let reserved ← wires bytes
  let synthesis ← wires bytes
  let plans ← items bytes 65536 (workspace bytes)
  let suffix ← items bytes 65536 (action bytes)
  return ⟨capacity,edges,reserved,synthesis,plans,suffix⟩

/-- The plan is only a producer proposal. Precharge its byte traversal before
allocating lists, and use the same work state for source and target checking. -/
def alignment (bytes : ByteArray) : CheckM Alignment := do
  guard (bytes.size ≤ 1048576) .packet
  native (Finite.exactWork (Exact.charge (8*(bytes.size+1))))
  let (proposal,offset) ← lift ((readAlignment bytes).run 0)
  guard (offset == bytes.size) .packet
  return proposal

structure Checked (bytes : ByteArray) where
  parts : PacketParts
  framed : split bytes = .ok parts
  proposal : Alignment
  source : Σ value : Packet.Input, Original value.original
  target : CanonicalOpenQasmResources.Checked parts.target proposal.capacity
  placement : CheckedPlacement source.2 target proposal.connected proposal.reserved proposal.synthesis
    proposal.plans proposal.suffix

private def verify (bytes : ByteArray) : CheckM (Checked bytes) := do
  match framed : split bytes with
  | .error error => throw error
  | .ok parts =>
    let proposal ← alignment parts.alignment
    let source ← CheckedQmatchV5.run parts.source
    let target ← native (CanonicalOpenQasmResources.check parts.target proposal.capacity)
    let placement ← native (source.2.checkPlacement target proposal.connected proposal.reserved
      proposal.synthesis proposal.plans proposal.suffix)
    return ⟨parts,framed,proposal,source,target,placement⟩

/-- Recheck the original source envelope, then independently decode and check
the emitted OpenQASM under the supplied placement proposal. -/
def check (bytes : ByteArray) : CheckM (Checked bytes) := do
  guard (bytes.size ≤ Packet.maxPacketBytes) .packet
  native (Finite.exactWork (Exact.charge (bytes.size+1)))
  verify bytes

theorem check_binding (bytes : ByteArray) (checked : Checked bytes) (work left : Nat)
    (ok : (check bytes).run work = (.ok checked,left)) :
    ∃ afterFrame afterPlan afterSource afterTarget,
      (Finite.exactWork (Exact.charge (bytes.size+1))).run work = (.ok (),afterFrame) ∧
      (alignment checked.parts.alignment).run afterFrame = (.ok checked.proposal,afterPlan) ∧
      (CheckedQmatchV5.run checked.parts.source).run afterPlan = (.ok checked.source,afterSource) ∧
      (CanonicalOpenQasmResources.check checked.parts.target checked.proposal.capacity).run afterSource =
        (.ok checked.target,afterTarget) ∧
      (checked.source.2.checkPlacement checked.target checked.proposal.connected checked.proposal.reserved
        checked.proposal.synthesis checked.proposal.plans checked.proposal.suffix).run afterTarget =
        (.ok checked.placement,left) := by
  unfold check at ok
  obtain ⟨_,start,gated,afterGuard⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,afterFrame,charged,stages⟩ := bind_success _ _ _ _ _ afterGuard
  have entered := (guard_success _ _ _ _ gated).2
  subst start
  clear ok afterGuard gated
  unfold verify at stages
  split at stages
  · change (Except.error _,afterFrame) = (.ok checked,left) at stages
    cases stages
  · obtain ⟨proposal,afterPlan,plan,rest⟩ := bind_success _ _ _ _ _ stages
    obtain ⟨source,afterSource,sourceRun,rest⟩ := bind_success _ _ _ _ _ rest
    obtain ⟨target,afterTarget,targetRun,rest⟩ := bind_success _ _ _ _ _ rest
    obtain ⟨placement,remaining,placementRun,returned⟩ := bind_success _ _ _ _ _ rest
    cases returned
    exact ⟨afterFrame,afterPlan,afterSource,afterTarget,native_success _ _ _ _ charged,
      plan,sourceRun,native_success _ _ _ _ targetRun,native_success _ _ _ _ placementRun⟩

theorem Checked.source_bound {bytes : ByteArray} (checked : Checked bytes) (work left : Nat)
    (ok : (check bytes).run work = (.ok checked,left)) :
    ∃ afterPlan afterSource,
      Packet.read checked.parts.source = .ok checked.source.1 ∧ checked.source.1.scope = .execution ∧
        Nonempty (Binding checked.source.1.original checked.source.1.graph checked.source.2
          afterPlan afterSource) := by
  obtain ⟨_,afterPlan,afterSource,_,_,_,sourceRun,_,_⟩ := check_binding _ _ _ _ ok
  exact ⟨afterPlan,afterSource,run_binding _ _ _ _ sourceRun⟩

theorem Checked.target_counts {bytes : ByteArray} (checked : Checked bytes) :
    (CanonicalOpenQasmResources.decode checked.parts.target).map
      CanonicalOpenQasmResources.Circuit.counts = some checked.target.circuit.counts := by
  rw [checked.target.original]
  rfl

end PlacementPacket

#print axioms check_binding
#print axioms Original.covers
#print axioms Original.root_safe
#print axioms run_binding
#print axioms PlacementPacket.check_binding
#print axioms PlacementPacket.Checked.source_bound
#print axioms PlacementPacket.Checked.target_counts
end QleisliKernel.Protocol.ExecutionView.CheckedQmatchV5
