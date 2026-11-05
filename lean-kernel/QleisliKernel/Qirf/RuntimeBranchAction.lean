import QleisliKernel.Qirf.RuntimeBranchCondition
import QleisliKernel.Qirf.RuntimeOwnerPhis
import QleisliKernel.Qirf.RuntimeOrdinaryPhis
import QleisliKernel.SourceTypes.SourceRuntimeScope

/-! Authentic pure-arm ordinary branches in the common mixed body traversal.
Both original arm outcomes and their actual child blocks remain separate.
This bounded connection admits no arm allocation, consumption or observation;
merge phis retain their genuine fresh source owners and fresh native wires.
No chosen condition suppresses an arm, public effect, caller frame or duty.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeBranchAction
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes SourceRuntimeValues
abbrev SourceState := RuntimeStructuralAction.SourceState
abbrev Owner := Semantics.SourceOwners.Owner
abbrev Ordinary := RuntimeOrdinaryBody.State

structure Source {sources caller} (event : SourceRuntimeContext.BranchEvent sources caller) where
  bodies : SourceRuntimeTrace.BranchBodies event
  original : RuntimeInterval.Computed (SourceRuntimeTrace.readBranchSource event) bodies
  thenPure : SourceRuntimeContext.inferredEffect bodies.thenResult.events = .unitary
  elsePure : SourceRuntimeContext.inferredEffect bodies.elseResult.events = .unitary
  thenAllocated : bodies.thenResult.allocated = []
  elseAllocated : bodies.elseResult.allocated = []
  thenConsumed : bodies.thenResult.consumed = []
  elseConsumed : bodies.elseResult.consumed = []
  thenOrdinal : bodies.thenResult.nextOrdinal = event.nextOrdinal
  elseOrdinal : bodies.elseResult.nextOrdinal = event.nextOrdinal

def readSource {sources caller} (event : SourceRuntimeContext.BranchEvent sources caller) :
    WorkM (Source event) := do
  let bodies ← NaturalAffine.witness (SourceRuntimeTrace.readBranchSource event)
  exactWork (Exact.charge (32*(Raw.OwnerFlow.fields (bodies.val.thenResult.allocated ++ bodies.val.elseResult.allocated ++
    bodies.val.thenResult.consumed ++ bodies.val.elseResult.consumed)+bodies.val.thenResult.events.length+
    bodies.val.elseResult.events.length+event.nextOrdinal+1)))
  if allowed : SourceRuntimeContext.inferredEffect bodies.val.thenResult.events = .unitary ∧
      SourceRuntimeContext.inferredEffect bodies.val.elseResult.events = .unitary ∧
      bodies.val.thenResult.allocated = [] ∧ bodies.val.elseResult.allocated = [] ∧
      bodies.val.thenResult.consumed = [] ∧ bodies.val.elseResult.consumed = [] ∧
      bodies.val.thenResult.nextOrdinal = event.nextOrdinal ∧ bodies.val.elseResult.nextOrdinal = event.nextOrdinal then
    return ⟨bodies.val,by with_reducible exact bodies.property,allowed.1,allowed.2.1,allowed.2.2.1,
      allowed.2.2.2.1,allowed.2.2.2.2.1,allowed.2.2.2.2.2.1,allowed.2.2.2.2.2.2.1,allowed.2.2.2.2.2.2.2⟩
  else throw .request

def sameMeasurements (left right : List RuntimeOrdinaryBody.Measurement) : Bool :=
  left.length == right.length && (left.zip right).all fun (a,b) =>
    decide (a.origin = b.origin ∧ a.calls = b.calls ∧ a.owner = b.owner ∧ a.output = b.output)

def leftRoles {sources caller event} (source : @Source sources caller event) : List Owner :=
  event.held ++ valueOwners source.bodies.thenResult.value ++ owners source.bodies.thenResult.remaining

def rightRoles {sources caller event} (source : @Source sources caller event) : List Owner :=
  event.held ++ valueOwners source.bodies.elseResult.value ++ owners source.bodies.elseResult.remaining

def outputRoles {sources caller} (event : SourceRuntimeContext.BranchEvent sources caller) : List Owner :=
  event.held ++ valueOwners event.value ++ owners event.remaining

def mergedTable {sources caller dependencies program block offset source actual before left right}
    (phis : @RuntimeOrdinaryPhis.Bound sources caller dependencies program block offset source actual
      before left right) (condition : RuntimeOrdinarySSA.Expression) : RuntimeOrdinarySSA.Table :=
  before ++ phis.phis.map fun pair => (pair.1.output,pair.2.expression condition)

structure Checked {sources rootOwner rootName caller name dependencies program block offset}
    (path : RuntimeOrdinaryBody.CallPath sources rootOwner rootName caller name)
    (event : SourceRuntimeContext.BranchEvent sources caller) (source : Source event)
    (actual : @RuntimeInterval.Branch dependencies program block offset)
    (before left right : SourceState) (ordinary leftOrdinary rightOrdinary : Ordinary) where
  beforeFrame : RuntimeOwnerMap.Checked (event.held ++ owners event.before) actual.interval.before
  beforeMap : beforeFrame.bindings.Perm before.bindings
  thenFrame : RuntimeOwnerMap.Checked (leftRoles source) actual.thenState
  elseFrame : RuntimeOwnerMap.Checked (rightRoles source) actual.elseState
  thenMap : thenFrame.bindings.Perm left.bindings
  elseMap : elseFrame.bindings.Perm right.bindings
  ownerPhis : RuntimeOwnerPhis.Bound actual event.phis (event.held ++ owners event.remaining)
    (leftRoles source) (rightRoles source) (outputRoles event) thenFrame elseFrame
  condition : RuntimeBranchCondition.Checked path event actual ordinary
  ordinaryPhis : RuntimeOrdinaryPhis.Bound event actual ordinary.table leftOrdinary.table rightOrdinary.table
  noThenMeasurements : sameMeasurements ordinary.measurements leftOrdinary.measurements = true
  noElseMeasurements : sameMeasurements ordinary.measurements rightOrdinary.measurements = true
  next : SourceState
  bindings : next.bindings = ownerPhis.output.bindings
  issued : next.issued = before.issued ++ event.phis.map (·.output)
  ordinal : next.nextOrdinal = event.nextOrdinal+event.phis.length
  ordinaryAfter : Ordinary
  ordinaryVisible : RuntimeOrdinaryBody.Visible actual.interval.after
    ⟨mergedTable ordinaryPhis condition.required,ordinary.measurements⟩
  ordinaryRead : ordinaryAfter = ordinaryVisible.ssa

private def readFrame (roles : List Owner) (state : Raw.Observation.State) (bindings : RuntimeOwnerMap.Map) :
    WorkM {checked : RuntimeOwnerMap.Checked roles state // checked.bindings.Perm bindings} := do
  exactWork (Exact.charge (32*(Raw.OwnerFlow.fields roles+Raw.OwnerFlow.fields (bindings.map (·.owner))+1)*
    (bindings.length+1)^2))
  let ordered ← RuntimeOwnerMap.order roles bindings
  let checked ← RuntimeOwnerMap.check roles state ordered
  if same : checked.bindings.Perm bindings then return ⟨checked,same⟩ else throw .request

/-- Both fixed child maps/tables are supplied by the SAME block traversal.
Every actual quantum and classical phi is consumed, and every source owner phi
is covered once. Condition equality is checked before the merged table is used. -/
def read {sources rootOwner rootName caller name dependencies program block offset}
    (path : RuntimeOrdinaryBody.CallPath sources rootOwner rootName caller name)
    (event : SourceRuntimeContext.BranchEvent sources caller) (source : Source event)
    (actual : @RuntimeInterval.Branch dependencies program block offset)
    (before left right : SourceState) (ordinary leftOrdinary rightOrdinary : Ordinary) :
    WorkM (Checked path event source actual before left right ordinary leftOrdinary rightOrdinary) := do
  exactWork (Exact.charge (64*(Raw.OwnerFlow.fields (before.issued ++ left.issued ++ right.issued ++
    event.phis.map (·.output))+before.nextOrdinal+event.nextOrdinal+ordinary.measurements.length+
    leftOrdinary.measurements.length+rightOrdinary.measurements.length+1)^2))
  guard (before.nextOrdinal == event.nextOrdinal && left.nextOrdinal == before.nextOrdinal &&
    right.nextOrdinal == before.nextOrdinal && left.issued == before.issued && right.issued == before.issued &&
    event.phis.map (fun phi => phi.output.ordinal) == (List.range event.phis.length).map (before.nextOrdinal+·)) .request
  let beforeFrame ← readFrame (event.held ++ owners event.before) actual.interval.before before.bindings
  let thenFrame ← readFrame (leftRoles source) actual.thenState left.bindings
  let elseFrame ← readFrame (rightRoles source) actual.elseState right.bindings
  let ownerPhis ← RuntimeOwnerPhis.check actual event.phis (event.held ++ owners event.remaining)
    (leftRoles source) (rightRoles source) (outputRoles event) thenFrame.val elseFrame.val
  let condition ← RuntimeBranchCondition.read path event actual ordinary
  let ordinaryPhis ← RuntimeOrdinaryPhis.read event actual ordinary.table leftOrdinary.table rightOrdinary.table
  if noMeasurements : sameMeasurements ordinary.measurements leftOrdinary.measurements = true ∧
      sameMeasurements ordinary.measurements rightOrdinary.measurements = true then
    let next : SourceState := ⟨ownerPhis.output.bindings,before.issued ++ event.phis.map (·.output),
      event.nextOrdinal+event.phis.length⟩
    let ordinaryVisible ← RuntimeOrdinaryBody.readVisible actual.interval.after
      ⟨mergedTable ordinaryPhis condition.required,ordinary.measurements⟩
    return ⟨beforeFrame.val,beforeFrame.property,thenFrame.val,elseFrame.val,thenFrame.property,elseFrame.property,
      ownerPhis,condition,ordinaryPhis,noMeasurements.1,noMeasurements.2,next,rfl,rfl,rfl,
      ordinaryVisible.ssa,ordinaryVisible,rfl⟩
  else throw .request

def Checked.retired {sources rootOwner rootName caller name dependencies program block offset path event source actual
    before left right ordinary leftOrdinary rightOrdinary}
    (_checked : @Checked sources rootOwner rootName caller name dependencies program block offset path event source actual
      before left right ordinary leftOrdinary rightOrdinary) : List Owner :=
  SourceRuntimeBranches.retired event.before event.remaining

end QleisliKernel.Qirf.RuntimeBranchAction
