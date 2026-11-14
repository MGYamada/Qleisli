import QleisliKernel.Target.CanonicalOpenQasmWorkspace

/-! Derive a physical placement by replaying matched prefixes of the original
closed Raw root and the decoded terminal gate word. A declared routing step
must occupy an actual SWAP instruction. Literal and decomposed Raw gates
leave the placement alone. Source workspace operators are checked separately.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Target.CanonicalOpenQasmPlacement
open Finite Qirf
open Semantics.RawTrace (Interface)
open CanonicalOpenQasmResources (Circuit Instruction)

inductive Match where
  | original | route | decomposed (gateCount : Nat)
  deriving BEq, DecidableEq, Repr

structure State where
  raw : Interface := {}
  locations : List Nat := []
  rawIndex : Nat := 0
  gateIndex : Nat := 0
  deriving BEq, DecidableEq, Repr

private def gateWord (circuit : Circuit) (atGate : Nat) (locations : List Nat)
    (steps : List Semantics.Finite.Step) : Option Nat := do
  let inFrame := fun (axis : Nat) => axis < locations.length
  if !steps.all (fun step => step.controls.all (inFrame ∘ (·.index)) &&
      (Finite.targets step.action).all inFrame) then none else
  let word := (circuit.gates.drop atGate).take steps.length
  if word.map Instruction.step == steps.map (Semantics.RawTrace.localize locations) then
    some (atGate+steps.length)
  else none

private def fresh (capacity : Nat) (locations reserved : List Nat) : Option (List Nat) :=
  ((List.range capacity).find? fun axis => !locations.contains axis && !reserved.contains axis).map
    (fun wire => locations ++ [wire])

private def stepAxes (step : Semantics.Finite.Step) : List Nat :=
  step.controls.map (·.index) ++ Finite.targets step.action

private def localWord (width : Nat) (axes : List Nat) (steps : List Semantics.Finite.Step) :
    List Semantics.Finite.Step :=
  steps.map (Semantics.RawTrace.localize ((List.range width).map axes.idxOf))

/-- Compare an original Raw circuit event and a decoded target slice on their
complete common support. The target may touch only those placed live wires.
Both words act as identity outside that support. -/
structure Decomposition (circuit : Circuit) (start count : Nat) (locations : List Nat)
    (steps : List Semantics.Finite.Step) where
  axes : List Nat
  originalAxes : axes = (steps.flatMap stepAxes).eraseDups
  inFrame : steps.all (fun step => (stepAxes step).all (· < locations.length)) = true
  layout : List Nat
  placed : axes.mapM (fun axis => locations[axis]?) = some layout
  declared : circuit.declares layout
  actual : List Semantics.Finite.Step
  targetWord : CanonicalOpenQasmWorkspace.interval circuit layout start count = some actual
  matrix : Semantics.Exact.Matrix
  originalOperator : RuntimeInterval.Computed
    (circuitMatrix [] (Raw.circuit axes.length (localWord locations.length axes steps))) matrix
  targetOperator : RuntimeInterval.Computed (circuitMatrix [] (Raw.circuit axes.length actual)) matrix

def checkDecomposition (circuit : Circuit) (start count : Nat) (locations : List Nat)
    (steps : List Semantics.Finite.Step) : WorkM (Decomposition circuit start count locations steps) := do
  guard (locations.length ≤ 12 && steps.length ≤ 1024 && start+count ≤ circuit.gates.length && count ≤ 1024) .limit
  exactWork (Exact.charge (64*(1+start+count+steps.length)*(1+locations.length)))
  if inFrame : steps.all (fun step => (stepAxes step).all (· < locations.length)) then
    let axes := (steps.flatMap stepAxes).eraseDups
    guard (axes.length ≤ 6) .limit
    match placed : axes.mapM (fun axis => locations[axis]?) with
    | none => throw .request
    | some layout =>
      if declared : circuit.declares layout then
        match targetWord : CanonicalOpenQasmWorkspace.interval circuit layout start count with
        | none => throw .request
        | some actual =>
          let original ← SourceTypes.NaturalAffine.witness
            (circuitMatrix [] (Raw.circuit axes.length (localWord locations.length axes steps)))
          let target ← SourceTypes.NaturalAffine.witness (circuitMatrix [] (Raw.circuit axes.length actual))
          exactWork (Exact.charge (original.val.entries.length+target.val.entries.length+1))
          if same : target.val = original.val then
            return ⟨axes,rfl,inFrame,layout,placed,declared,actual,targetWord,original.val,
              by exact original.property,by simpa only [same] using target.property⟩
          else throw .equation
      else throw .request
  else throw .request

private def followRaw (circuit : Circuit) (state : State) (operation : Semantics.Raw.Op)
    (reserved : List Nat) (size : Option Nat := none) : WorkM State := do
  let (next,events) ← lift (readOption (Semantics.RawTrace.step state.raw operation))
  let (locations,gateIndex) ← match size,events with
    | none,[] => pure (state.locations,state.gateIndex)
    | none,[.init0 _] => lift (readOption ((fresh circuit.qubits state.locations reserved).map (·,state.gateIndex)))
    | none,[.liftBasis before after [] [axis] [0]] =>
      if after == before+1 && axis == before then
        lift (readOption ((fresh circuit.qubits state.locations reserved).map (·,state.gateIndex)))
      else throw .request
    | none,[.circuit _ steps] =>
      lift (readOption ((gateWord circuit state.gateIndex state.locations steps).map (state.locations,·)))
    | some count,[.circuit _ steps] => do
      let _ ← checkDecomposition circuit state.gateIndex count state.locations steps
      pure (state.locations,state.gateIndex+count)
    | _,_ => throw .request
  if next.frame.length == locations.length then
    pure ⟨next,locations,state.rawIndex+1,gateIndex⟩
  else throw .request

private def followSwap (circuit : Circuit) (connected : Nat → Nat → Bool) (state : State)
    (reserved : List Nat) : Option State := do
  let some ⟨.swap,[first,second]⟩ := circuit.gates[state.gateIndex]? | none
  if first != second && first < circuit.qubits && second < circuit.qubits && connected first second &&
      !reserved.contains first && !reserved.contains second then
    let move : Routing.Swap := ⟨first,second⟩
    some {state with locations := state.locations.map move.axis, gateIndex := state.gateIndex+1}
  else none

private def replayFrom (original : Array Semantics.Observation.Op) (circuit : Circuit) (connected : Nat → Nat → Bool)
    (alignment : List Match) (initial : State) (reserved : List Nat := []) : WorkM State :=
  alignment.foldlM (fun state action => match action with
    | .route => lift (readOption (followSwap circuit connected state reserved))
    | .original | .decomposed _ => do
      let some (.pure operation) := original[state.rawIndex]? | throw .request
      let size := match action with | .decomposed count => some count | _ => none
      followRaw circuit state operation reserved size) initial

def replay (original : Array Semantics.Observation.Op) (circuit : Circuit) (connected : Nat → Nat → Bool)
    (alignment : List Match) : WorkM State :=
  replayFrom original circuit connected alignment {}

structure Checked {bytes capacity} (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (program : Semantics.Observation.Program) (connected : Nat → Nat → Bool)
    (alignment : List Match) where
  closed : program.inputs.isEmpty = true ∧ program.classicalInputs.isEmpty = true
  state : State
  actual : RuntimeInterval.Computed (replay program.operations.toArray target.circuit connected alignment) state

def check {bytes capacity} (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (program : Semantics.Observation.Program) (connected : Nat → Nat → Bool) (alignment : List Match) :
    WorkM (Checked target program connected alignment) := do
  guard (program.operations.length ≤ 65536 && alignment.length ≤ 65536) .limit
  exactWork (Exact.charge (32*(1+program.operations.length) +
    32*(1+alignment.length)*(1+alignment.length+target.circuit.gates.length)))
  if closed : program.inputs.isEmpty = true ∧ program.classicalInputs.isEmpty = true then
    let original ← SourceTypes.NaturalAffine.witness (replay program.operations.toArray target.circuit connected alignment)
    return ⟨closed,original.val,by exact original.property⟩
  else throw .request

/-- Retain the exact original prefix coordinates used to derive placement. -/
structure WorkspaceBinding {sources caller dependencies program block sourceStart sourceCount event events original
    sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller dependencies program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    (map : RuntimeWorkspace.CallerMap literal) {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity} {connected alignment}
    (prefixCheck : Checked target program connected alignment) (count : Nat) where
  operations : ObservationBinding.lists (ObservationBinding.operation 65) block.operations program.operations = true
  offset : prefixCheck.state.rawIndex = sourceStart
  sameFrame : prefixCheck.state.raw = sourceInterval.before.quantum.reference
  placed : CanonicalOpenQasmWorkspace.Placed map target prefixCheck.state.locations prefixCheck.state.gateIndex count

theorem WorkspaceBinding.originalOperations {sources caller dependencies program block sourceStart sourceCount event
    events original sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller dependencies program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    {map : RuntimeWorkspace.CallerMap literal} {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity} {connected alignment}
    {prefixCheck : Checked target program connected alignment} {count}
    (binding : WorkspaceBinding map prefixCheck count) : block.operations = program.operations :=
  ObservationBinding.lists_sound (ObservationBinding.operation 65) (ObservationBinding.operation_sound 65)
    _ _ binding.operations

/-- A root interval can take its placement only from the checked, literal
prefix ending at that exact Raw operation and target gate. The checked
original frame includes every port, including zero-width owners. -/
def workspace {sources caller dependencies program block sourceStart sourceCount event events original
    sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller dependencies program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    (map : RuntimeWorkspace.CallerMap literal) {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity} {connected alignment}
    (prefixCheck : Checked target program connected alignment)
    (count : Nat) (scratch : Option Nat) :
    WorkM (WorkspaceBinding map prefixCheck count) := do
  exactWork (Exact.charge (16*(program.operations.length+block.operations.length+1)))
  if bound : ObservationBinding.lists (ObservationBinding.operation 65) block.operations program.operations = true ∧
      prefixCheck.state.rawIndex = sourceStart ∧
      prefixCheck.state.raw = sourceInterval.before.quantum.reference then
    let placed ← CanonicalOpenQasmWorkspace.checkPlacement map target prefixCheck.state.locations
      prefixCheck.state.gateIndex count scratch
    return ⟨bound.1,bound.2.1,bound.2.2,placed⟩
  else throw .request

private def followObservation (frame : Interface) (locations : List Nat)
    (operations : List Semantics.Observation.Op) : Option (Interface × List (Nat × Nat)) :=
  operations.foldlM (fun (state,measured) operation => do
    match operation with
    | .measure input output =>
      let (port,next) ← Semantics.RawTrace.take state input
      let [wire] := port.wires | none
      let [location] ← CanonicalOpenQasmWorkspace.placedWires frame.frame locations [wire] | none
      if measured.any (fun pair => pair.1 == output || pair.2 == location) then none else
        some (next,(output,location) :: measured)
    | .discard input =>
      let (_,next) ← Semantics.RawTrace.take state input
      some (next,measured)
    | .pure (original@(.packUnit _)) | .pure (original@(.unpackUnit _)) |
      .pure (original@(.split _ _ _ _)) | .pure (original@(.join _ _ _)) => do
      let (next,[]) ← Semantics.RawTrace.step state original | none
      some (next,measured)
    | _ => none) (frame,[])

/-- Read the original terminal observations in SSA result order. Hidden
measurements and explicit discards consume owners, and no quantum owner
(including a zero-width owner) can be left outside the terminal word. -/
def readout (program : Semantics.Observation.Program) (state : State) : Option (List Nat) := do
  if !program.outputs.isEmpty || state.rawIndex > program.operations.length then none else
  let (finished,measured) ← followObservation state.raw state.locations (program.operations.drop state.rawIndex)
  if !finished.live.isEmpty || !program.classicalOutputs.Nodup then none else
  program.classicalOutputs.mapM fun id => (measured.find? (fun pair => pair.1 == id)).map (·.2)

structure Readout {bytes capacity} (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (program : Semantics.Observation.Program) (state : State) : Type where
  allGates : state.gateIndex = target.circuit.gates.length
  original : readout program state = some target.circuit.measurements

def checkReadout {bytes capacity} (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (program : Semantics.Observation.Program) (state : State) : WorkM (Readout target program state) := do
  let count := program.operations.length - state.rawIndex
  exactWork (Exact.charge (32*(1+program.operations.length) +
    32*(1+count)*(1+count+state.raw.live.length+program.classicalOutputs.length)))
  if done : state.gateIndex = target.circuit.gates.length then
    if words : readout program state = some target.circuit.measurements then
      return ⟨done,words⟩
    else throw .request
  else throw .request

structure FinishedWorkspace {sources caller dependencies program block sourceStart sourceCount event events original
    sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller dependencies program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    (map : RuntimeWorkspace.CallerMap literal) {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity} {connected alignment}
    (prefixCheck : Checked target program connected alignment) (count : Nat) where
  binding : WorkspaceBinding map prefixCheck count
  lifetime : CanonicalOpenQasmWorkspace.lifetimes target.circuit event.fresh
    (binding.placed.liveLayout ++ binding.placed.freshScratch.toList) prefixCheck.state.gateIndex count = true
  sameWires : sourceInterval.after.quantum.reference.frame = prefixCheck.state.raw.frame
  suffix : List Match
  final : State
  replayed : RuntimeInterval.Computed (replayFrom program.operations.toArray target.circuit connected suffix
    ⟨sourceInterval.after.quantum.reference,prefixCheck.state.locations,sourceStart+sourceCount,
      prefixCheck.state.gateIndex+count⟩) final
  readout : Readout target program final

/-- Check a complete literal terminal placement with one checked workspace
body. Carry its original exit owners across the remaining gates, then derive
the actual measured wire order. Fresh scratch uses the exclusive lifetime
condition for this single-interval route. -/
def finishWorkspace {sources caller dependencies program block sourceStart sourceCount event events original
    sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller dependencies program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    (map : RuntimeWorkspace.CallerMap literal) {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity} {connected alignment}
    (prefixCheck : Checked target program connected alignment)
    (count : Nat) (scratch : Option Nat) (suffix : List Match) :
    WorkM (FinishedWorkspace map prefixCheck count) := do
  let binding ← workspace map prefixCheck count scratch
  guard (suffix.length ≤ 65536) .limit
  exactWork (Exact.charge (32*(1+program.operations.length) +
    32*(1+suffix.length)*(1+suffix.length+target.circuit.gates.length) +
    32*(target.circuit.gates.length+target.circuit.measurements.length+1)))
  let layout := binding.placed.liveLayout ++ binding.placed.freshScratch.toList
  if lifetime : CanonicalOpenQasmWorkspace.lifetimes target.circuit event.fresh layout
      prefixCheck.state.gateIndex count = true then
    if same : sourceInterval.after.quantum.reference.frame = prefixCheck.state.raw.frame then
      let entry : State :=
        ⟨sourceInterval.after.quantum.reference,prefixCheck.state.locations,sourceStart+sourceCount,
          prefixCheck.state.gateIndex+count⟩
      let final ← SourceTypes.NaturalAffine.witness
        (replayFrom program.operations.toArray target.circuit connected suffix entry)
      let result ← checkReadout target program final.val
      return ⟨binding,lifetime,same,suffix,final.val,by exact final.property,result⟩
    else throw .request
  else throw .request

/-- One workspace request in the original Raw program. The producer can
choose literal alignment and coordinates, and the checker derives the frame. -/
structure Segment (program : Semantics.Observation.Program) where
  sources : SourceTypes.Sources
  caller : String
  dependencies : List Semantics.Finite.Dependency
  block : RuntimeInterval.Block dependencies program
  start : Nat
  length : Nat
  event : SourceTypes.SourceRuntimeContext.WorkspaceEvent sources caller
  events : List (SourceTypes.SourceRuntimeContext.Event sources caller)
  original : RuntimeWorkspace.Original event events
  sourceInterval : RuntimeInterval.Checked block start length
  sourceBefore : RuntimeStructuralAction.SourceState
  literal : RuntimeWorkspace.Literal original sourceInterval sourceBefore
  map : RuntimeWorkspace.CallerMap literal
  alignment : List Match
  count : Nat
  scratch : Option Nat

private def Segment.exit {program : Semantics.Observation.Program} (segment : Segment program) (entry : State) :
    State :=
  ⟨segment.sourceInterval.after.quantum.reference,entry.locations,segment.start+segment.length,
    entry.gateIndex+segment.count⟩

structure BoundSegment {program : Semantics.Observation.Program} (segment : Segment program)
    {bytes capacity} (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (connected : Nat → Nat → Bool) (reserved : List Nat) (previous entry : State) where
  replayed : RuntimeInterval.Computed
    (replayFrom program.operations.toArray target.circuit connected segment.alignment previous reserved) entry
  operations : segment.block.operations = program.operations
  offset : entry.rawIndex = segment.start
  sameEntry : entry.raw = segment.sourceInterval.before.quantum.reference
  sameWires : segment.sourceInterval.after.quantum.reference.frame = entry.raw.frame
  reservedScratch : ∀ wire ∈ segment.scratch.toList, wire ∈ reserved
  placed : CanonicalOpenQasmWorkspace.Placed segment.map target entry.locations entry.gateIndex segment.count
  scratchUsed : placed.freshScratch = segment.scratch

private def segmentWork {bytes capacity} (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (program : Semantics.Observation.Program) (alignment : List Match) : WorkM Unit := do
  guard (alignment.length ≤ 65536) .limit
  exactWork (Exact.charge (32*(1+program.operations.length) +
    32*(1+alignment.length)*(1+alignment.length+target.circuit.gates.length)))

private def checkSegment {program : Semantics.Observation.Program} (segment : Segment program)
    {bytes capacity} (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (connected : Nat → Nat → Bool) (reserved : List Nat) (previous : State) :
    WorkM (Σ entry, BoundSegment segment target connected reserved previous entry) := do
  segmentWork target program segment.alignment
  exactWork (Exact.charge (16*(1+program.operations.length+segment.block.operations.length)))
  let replayed ← SourceTypes.NaturalAffine.witness
    (replayFrom program.operations.toArray target.circuit connected segment.alignment previous reserved)
  let entry := replayed.val
  if bound : ObservationBinding.lists (ObservationBinding.operation 65)
      segment.block.operations program.operations = true ∧ entry.rawIndex = segment.start ∧
      entry.raw = segment.sourceInterval.before.quantum.reference ∧
      segment.sourceInterval.after.quantum.reference.frame = entry.raw.frame ∧
      (∀ wire ∈ segment.scratch.toList,wire ∈ reserved) then
    let placed ← CanonicalOpenQasmWorkspace.checkPlacement segment.map target entry.locations
      entry.gateIndex segment.count segment.scratch
    if scratchUsed : placed.freshScratch = segment.scratch then
      let operations := ObservationBinding.lists_sound (ObservationBinding.operation 65)
        (ObservationBinding.operation_sound 65) _ _ bound.1
      return ⟨entry,⟨by exact replayed.property,operations,bound.2.1,bound.2.2.1,
        bound.2.2.2.1,bound.2.2.2.2,placed,scratchUsed⟩⟩
    else throw .request
  else throw .request

private def BoundSegment.addCleanUse {program : Semantics.Observation.Program} {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity} {connected reserved previous entry}
    {segment : Segment program} (bound : BoundSegment segment target connected reserved previous entry) (scratch : Nat)
    (earlier : List (CanonicalOpenQasmWorkspace.CleanUse target.circuit scratch)) :
    List (CanonicalOpenQasmWorkspace.CleanUse target.circuit scratch) :=
  if last : bound.placed.freshScratch = some scratch then
    have fresh : segment.event.fresh = true := by
      have mode := bound.placed.scratchMode
      rw [last] at mode
      exact mode.symm
    have layout : (bound.placed.liveLayout ++ bound.placed.freshScratch.toList).getLast? = some scratch := by
      simp [last]
    earlier ++ [bound.placed.body.cleanUse fresh layout]
  else earlier

abbrev CleanUses (circuit : Circuit) := (scratch : Nat) → List (CanonicalOpenQasmWorkspace.CleanUse circuit scratch)

inductive WorkspaceTrace {program : Semantics.Observation.Program} {bytes capacity}
    (target : CanonicalOpenQasmResources.Checked bytes capacity) (connected : Nat → Nat → Bool)
    (reserved : List Nat) : State → CleanUses target.circuit → Type where
  | start : WorkspaceTrace (program := program) target connected reserved {} (fun _ => [])
  | next {previous entry : State} {segment : Segment program} {uses : CleanUses target.circuit}
    (earlier : WorkspaceTrace (program := program) target connected reserved previous uses)
    (bound : BoundSegment segment target connected reserved previous entry) :
      WorkspaceTrace (program := program) target connected reserved (segment.exit entry)
        (fun scratch => bound.addCleanUse scratch (uses scratch))

structure TraceWithUses {program : Semantics.Observation.Program} {bytes capacity}
    (target : CanonicalOpenQasmResources.Checked bytes capacity) (connected : Nat → Nat → Bool)
    (reserved : List Nat) where
  exit : State
  cleanUses : CleanUses target.circuit
  trace : @WorkspaceTrace program bytes capacity target connected reserved exit cleanUses

structure FinishedTrace (program : Semantics.Observation.Program) {bytes capacity}
    (target : CanonicalOpenQasmResources.Checked bytes capacity) (connected : Nat → Nat → Bool)
    (reserved : List Nat) (suffix : List Match) where
  closed : program.inputs.isEmpty = true ∧ program.classicalInputs.isEmpty = true
  declared : target.circuit.declares reserved
  recorded : @TraceWithUses program bytes capacity target connected reserved
  final : State
  replayed : RuntimeInterval.Computed
    (replayFrom program.operations.toArray target.circuit connected suffix recorded.exit reserved) final
  readout : Readout target program final
  restored : ∀ scratch ∈ reserved, Nonempty (CanonicalOpenQasmWorkspace.Reuse target scratch (recorded.cleanUses scratch))

/-- Follow every original interval in order while keeping designations for
clean scratch fixed. Ordinary preparation and routing cannot use a designated
scratch wire. Each such wire is restored by its own exact, disjoint uses. -/
def finishTrace {bytes capacity} (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (program : Semantics.Observation.Program) (connected : Nat → Nat → Bool) (reserved : List Nat)
    (segments : List (Segment program)) (suffix : List Match) : WorkM (FinishedTrace program target connected reserved suffix) := do
  guard (program.operations.length ≤ 65536 && segments.length ≤ program.operations.length && reserved.length ≤ 12) .limit
  exactWork (Exact.charge (32*(program.operations.length+segments.length+1)))
  if closed : program.inputs.isEmpty = true ∧ program.classicalInputs.isEmpty = true then
    if declared : target.circuit.declares reserved then
      let recorded ← segments.foldlM (fun (state : @TraceWithUses program bytes capacity target connected reserved) segment => do
        let ⟨entry,bound⟩ ← checkSegment segment target connected reserved state.exit
        pure ⟨segment.exit entry,fun scratch => bound.addCleanUse scratch (state.cleanUses scratch),.next state.trace bound⟩)
        ⟨{},fun _ => [],.start⟩
      segmentWork target program suffix
      let final ← SourceTypes.NaturalAffine.witness
        (replayFrom program.operations.toArray target.circuit connected suffix recorded.exit reserved)
      let output ← checkReadout target program final.val
      exactWork (Exact.charge (32*(1+reserved.length)*(1+segments.length)*(1+segments.length)))
      let uses ← reserved.attach.mapM fun wire => do
        let intervals := recorded.cleanUses wire.val
        guard (!intervals.isEmpty) .request
        let checked ← CanonicalOpenQasmWorkspace.checkReuse target wire.val intervals
        pure (⟨wire,checked⟩ : Σ item : { axis // axis ∈ reserved },
          CanonicalOpenQasmWorkspace.Reuse target item.val (recorded.cleanUses item.val))
      if covered : ∀ scratch ∈ reserved, (uses.map (fun item => item.1.val)).contains scratch then
        have restored : ∀ scratch ∈ reserved, Nonempty (CanonicalOpenQasmWorkspace.Reuse target scratch (recorded.cleanUses scratch)) := by
          intro scratch member
          have listed := List.contains_iff_mem.mp (covered scratch member)
          obtain ⟨⟨wire,checked⟩,_,rfl⟩ := List.mem_map.mp listed
          exact ⟨checked⟩
        return ⟨closed,declared,recorded,final.val,by exact final.property,output,restored⟩
      else throw .request
    else throw .request
  else throw .request

end QleisliKernel.Target.CanonicalOpenQasmPlacement
