import QleisliKernel.Qirf.RuntimeScatterTransport
import QleisliKernel.Qirf.RuntimeOwnerTransition

/-! Literal circuit-event composition in the same original runtime interval.
The complete source owner maps, ordered selected wires, actual Raw trace and
local sector reader remain attached. Circuit event boundaries and their work
charges are preserved. No matrix/circuit reassociation, omitted-sector Gram
proof, accepted handle, new profile or source AST theorem is supplied here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeLocalEvents
open QleisliKernel Finite Semantics.Finite Semantics.Exact
open RuntimeOwnerMap (Owner Map)
open RuntimeScatterTransport (pull)

def circuitEvents (bits : Nat) (axes : List Nat) (chunks : List (List Step)) : List Semantics.Raw.Event :=
  chunks.map fun chunk => .circuit bits (chunk.map (Semantics.RawTrace.localize axes))

def localEvents (bits : Nat) (chunks : List (List Step)) : List Semantics.Raw.Event :=
  chunks.map fun chunk => .circuit bits chunk

def evaluate (dependencies : List Dependency) (events : List Semantics.Raw.Event)
    (values : Raw.Coefficient.State) : Raw.Coefficient.State :=
  events.foldl (fun state event => Raw.Coefficient.event dependencies event state) values

/-- The event's own charge stays on both sides. In particular a real empty
circuit event is not confused with a structural operation emitting no event. -/
theorem event_selected (dependencies : List Dependency) (base globalBits localBits : Nat)
    (selected : List Nat) (distinct : selected.Nodup) (chunk : List Step)
    (controls : ∀ step ∈ chunk,∀ control ∈ step.controls,control.index < selected.length)
    (targets : ∀ step ∈ chunk,∀ axis ∈ Finite.targets step.action,axis < selected.length)
    (values : Raw.Coefficient.State) :
    pull base selected (Raw.Coefficient.event dependencies
      (.circuit globalBits (chunk.map (Semantics.RawTrace.localize selected))) values) =
      Raw.Coefficient.event dependencies (.circuit localBits chunk) (pull base selected values) := by
  funext output
  have same : Raw.Coefficient.circuit dependencies (chunk.map (Semantics.RawTrace.localize selected))
      values (scatter base selected output) =
      Raw.Coefficient.circuit dependencies chunk (pull base selected values) output :=
    congrFun (RuntimeScatterTransport.circuit_selected dependencies base selected distinct chunk controls targets values) output
  change (do
    exactWork (Exact.charge 1)
    Raw.Coefficient.circuit dependencies (chunk.map (Semantics.RawTrace.localize selected)) values
      (scatter base selected output)) = (do
    exactWork (Exact.charge 1)
    Raw.Coefficient.circuit dependencies chunk (pull base selected values) output)
  rw [same]

theorem events_selected (dependencies : List Dependency) (base globalBits localBits : Nat)
    (selected : List Nat) (distinct : selected.Nodup) (chunks : List (List Step))
    (controls : ∀ chunk ∈ chunks,∀ step ∈ chunk,∀ control ∈ step.controls,control.index < selected.length)
    (targets : ∀ chunk ∈ chunks,∀ step ∈ chunk,∀ axis ∈ Finite.targets step.action,axis < selected.length)
    (values : Raw.Coefficient.State) :
    pull base selected (evaluate dependencies (circuitEvents globalBits selected chunks) values) =
      evaluate dependencies (localEvents localBits chunks) (pull base selected values) := by
  induction chunks generalizing values with
  | nil => rfl
  | cons first rest ih =>
    have restControls : ∀ chunk ∈ rest,∀ step ∈ chunk,∀ control ∈ step.controls,control.index < selected.length :=
      fun chunk member => controls chunk (List.mem_cons_of_mem _ member)
    have restTargets : ∀ chunk ∈ rest,∀ step ∈ chunk,∀ axis ∈ Finite.targets step.action,axis < selected.length :=
      fun chunk member => targets chunk (List.mem_cons_of_mem _ member)
    change pull base selected (evaluate dependencies (circuitEvents globalBits selected rest)
      (Raw.Coefficient.event dependencies (.circuit globalBits (first.map (Semantics.RawTrace.localize selected))) values)) =
      evaluate dependencies (localEvents localBits rest)
        (Raw.Coefficient.event dependencies (.circuit localBits first) (pull base selected values))
    have tail : pull base selected (evaluate dependencies (circuitEvents globalBits selected rest)
        (Raw.Coefficient.event dependencies (.circuit globalBits (first.map (Semantics.RawTrace.localize selected))) values)) =
        evaluate dependencies (localEvents localBits rest) (pull base selected
          (Raw.Coefficient.event dependencies (.circuit globalBits (first.map (Semantics.RawTrace.localize selected))) values)) := by
      apply ih <;> assumption
    rw [tail,event_selected dependencies base globalBits localBits selected distinct first
      (controls first (List.mem_cons_self)) (targets first (List.mem_cons_self)) values]

/-- This interval has no synthetic finish. The original caller's final output
permutation remains RuntimePureComposition.Prepared.orderedRootTrace's event. -/
def trace (before : Semantics.RawTrace.Interface) (operations : List Semantics.Raw.Op) :
    Option Semantics.RawTrace.Prepared :=
  operations.foldlM Semantics.RawTrace.advance ⟨before,[],before.frame.length⟩

/-- The sector fragment's synthetic identity finish contributes no circuit
chunk. Every actual circuit, including an empty one, retains its own position. -/
def readChunks (bits : Nat) (events : List Semantics.Raw.Event) : Except Error (List (List Step)) := do
  let chunks ← events.mapM fun event => match event with
    | .circuit width steps =>
      if width == bits then pure (some steps) else throw .request
    | .reorder width axes =>
      if width == bits && axes == List.range bits then pure none else throw .request
    | _ => throw .request
  return chunks.filterMap id

def bounds (width : Nat) (chunks : List (List Step)) : Bool :=
  chunks.all fun chunk => chunk.all fun step =>
    step.controls.all (fun control => control.index < width) &&
      (Finite.targets step.action).all (fun axis => axis < width)

theorem bounds_controls {width chunks} (checked : bounds width chunks = true) :
    ∀ chunk ∈ chunks,∀ step ∈ chunk,∀ control ∈ step.controls,control.index < width := by
  intro chunk member step present control held
  have good := List.all_eq_true.mp (List.all_eq_true.mp checked chunk member) step present
  exact of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp good).1 control held)

theorem bounds_targets {width chunks} (checked : bounds width chunks = true) :
    ∀ chunk ∈ chunks,∀ step ∈ chunk,∀ axis ∈ Finite.targets step.action,axis < width := by
  intro chunk member step present axis held
  have good := List.all_eq_true.mp (List.all_eq_true.mp checked chunk member) step present
  exact of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp good).2 axis held)

structure Literal {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (selectorBits targetBits : Nat) (retained : Raw.Sector.Retained)
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained)
    {beforeRoles afterRoles}
    (before : RuntimeOwnerMap.Checked beforeRoles frame.interval.before)
    (after : RuntimeOwnerMap.Checked afterRoles frame.interval.after) where
  selection : RuntimeScatterTransport.Selection before
  selectedRoles : selection.selectedRoles = roles
  selectedPorts : selection.selected.map (·.port) = frame.selected
  inputCode : RuntimeForestCode.Frame before
  outputCode : RuntimeForestCode.Frame after
  traceResult : Semantics.RawTrace.Prepared
  executed : trace frame.interval.before.quantum.reference frame.operations = some traceResult
  afterState : traceResult.state = frame.interval.after.quantum.reference
  chunks : List (List Step)
  localRead : readChunks (selectorBits+targetBits) retained.prepared.events = .ok chunks
  localSteps : chunks.flatten = retained.steps
  bounded : bounds (RuntimeForestCode.forestAxes frame.interval.before.quantum.frame selection.selected).length chunks = true
  literal : traceResult.events = circuitEvents frame.interval.before.quantum.frame.length
    (RuntimeForestCode.forestAxes frame.interval.before.quantum.frame selection.selected) chunks

/-- Only actual source/Raw metadata and existing per-owner readers are used.
The supplied retained sector is indexed by its actual existing read invocation;
this function does not check another root or rerun any sector/target Gram. -/
def read {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (selectorBits targetBits : Nat) (retained : Raw.Sector.Retained)
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained)
    {beforeRoles afterRoles}
    (before : RuntimeOwnerMap.Checked beforeRoles frame.interval.before)
    (after : RuntimeOwnerMap.Checked afterRoles frame.interval.after)
    (selection : RuntimeScatterTransport.Selection before) :
    WorkM (Literal frame selectorBits targetBits retained restricted before after) := do
  let fields := (frame.operations.map fun operation => Raw.rawFields
    ⟨[],[operation],[],.unitary⟩).sum
  -- Each literal take/insert scans a live list. One pure Raw operation grows
  -- that list by at most one; event append likewise visits the earlier trace.
  -- Reserve those actual repeated traversals, not just the input byte count.
  let traversal := frame.interval.before.quantum.live.length+frame.operations.length+
    frame.interval.before.quantum.frame.length+frame.interval.after.quantum.frame.length+1
  exactWork (Exact.charge (16*(fields+retained.steps.length+selection.selected.length+1)*traversal+
    16*(Raw.OwnerFlow.fields roles+Raw.OwnerFlow.fields selection.selectedRoles+1)+
    FiniteRestriction.restrictionFields retained.steps))
  if selectedRoles : selection.selectedRoles = roles then
    if selectedPorts : selection.selected.map (·.port) = frame.selected then
      let inputCode ← RuntimeForestCode.readFrame before
      let outputCode ← RuntimeForestCode.readFrame after
      match executed : trace frame.interval.before.quantum.reference frame.operations with
      | none => throw .request
      | some traceResult =>
        if afterState : traceResult.state = frame.interval.after.quantum.reference then
          match localRead : readChunks (selectorBits+targetBits) retained.prepared.events with
          | .error error => throw error
          | .ok chunks =>
            if localSteps : chunks.flatten = retained.steps then
              if bounded : bounds (RuntimeForestCode.forestAxes frame.interval.before.quantum.frame selection.selected).length chunks = true then
                if literal : traceResult.events = circuitEvents frame.interval.before.quantum.frame.length
                    (RuntimeForestCode.forestAxes frame.interval.before.quantum.frame selection.selected) chunks then
                  pure ⟨selection,selectedRoles,selectedPorts,inputCode,outputCode,traceResult,executed,afterState,chunks,localRead,localSteps,bounded,literal⟩
                else throw .equation
              else throw .request
            else throw .request
        else throw .request
    else throw .request
  else throw .request

/-- Interpret a selection from the original body. Its checked caller frame and
both returned bindings are determined by the source node. -/
def readSource {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (selectorBits targetBits : Nat) (retained : Raw.Sector.Retained)
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles) :
    WorkM (Literal frame selectorBits targetBits retained restricted source.before source.transport.after) := do
  let selected := source.selected.toList
  let wireCount := source.selected.first.port.wires.length+source.selected.second.port.wires.length
  exactWork (Exact.charge (4*(wireCount+1)*(wireCount+frame.interval.before.quantum.frame.length+1)))
  if distinct : (RuntimeForestCode.forestAxes frame.interval.before.quantum.frame selected).Nodup then
    read frame selectorBits targetBits retained restricted source.before source.transport.after
      ⟨roles,selected,source.selected.ordered,distinct⟩
  else throw .request

/-- Concrete event/reference composition for this same literal interval and
its full typed caller forest. Headers, local input order, errors and work are
preserved; neither a matrix identity nor abstract Commutes is a premise. -/
theorem Literal.references {Reference : Type}
    {dependencies program block start count inputs outputs roles frame selectorBits targetBits retained restricted
      beforeRoles afterRoles before after}
    (checked : @Literal dependencies program block start count inputs outputs roles frame selectorBits targetBits retained
      restricted beforeRoles afterRoles before after) (values : Reference → Raw.Coefficient.State) :
    (fun reference output => evaluate dependencies checked.traceResult.events (values reference) output) =
      (fun reference output => evaluate dependencies (localEvents (selectorBits+targetBits) checked.chunks)
        (pull output (RuntimeForestCode.forestAxes frame.interval.before.quantum.frame checked.selection.selected)
          (values reference))
        (gather output (RuntimeForestCode.forestAxes frame.interval.before.quantum.frame checked.selection.selected))) := by
  rw [checked.literal]
  funext reference output
  have point := congrFun (events_selected dependencies output frame.interval.before.quantum.frame.length
    (selectorBits+targetBits) _ checked.selection.distinct checked.chunks
    (bounds_controls checked.bounded) (bounds_targets checked.bounded) (values reference))
      (gather output (RuntimeForestCode.forestAxes frame.interval.before.quantum.frame checked.selection.selected))
  simpa only [pull,RuntimeScatterTransport.scatter_gather _ _ checked.selection.distinct] using point

/-- The same local original Raw fragment and every physical sector remain
bound to the existing gate. No old read invocation or Gram is fabricated. -/
theorem Literal.sectorReference
    {dependencies program block start count inputs outputs roles frame selectorBits targetBits retained restricted
      beforeRoles afterRoles before after}
    (_checked : @Literal dependencies program block start count inputs outputs roles frame selectorBits targetBits retained
      restricted beforeRoles afterRoles before after) :
    Raw.Sector.ReadBinding dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs) retained := by
  obtain ⟨work,left,ran⟩ := restricted
  exact Raw.Sector.read_bound _ _ _ _ _ work left ran

end QleisliKernel.Qirf.RuntimeLocalEvents
