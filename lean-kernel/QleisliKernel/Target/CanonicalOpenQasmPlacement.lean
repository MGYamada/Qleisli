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
  | original | route | decomposed (gateCount : Nat) | synthesized (gateCount : Nat) (scratch : List Nat)
  | optimized (rawCount gateCount : Nat) (scratch : List Nat := [])
  deriving BEq, DecidableEq, Repr

structure State where
  raw : Interface := {}
  locations : List Nat := []
  rawIndex : Nat := 0
  gateIndex : Nat := 0
  synthesis : List Nat := []
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

private def outsideUntouched (circuit : Circuit) (start count : Nat) (scratch : List Nat) : Bool :=
  scratch.all fun wire => !circuit.measurements.contains wire &&
    ((circuit.gates.take start) ++ (circuit.gates.drop (start+count))).all fun gate => !gate.wires.contains wire

private def checkedSynthesis (axes scratch : Nat) (target : List Semantics.Finite.Step)
    (logical : Semantics.Exact.Matrix) : WorkM Semantics.Exact.Matrix := do
  let zero ← Raw.zeroEncoding axes scratch
  let required : Semantics.Finite.Contract := ⟨zero,zero,logical⟩
  Finite.check [] (Raw.circuit (axes+scratch) target) required required

/-- A temporary target register is appended above the original ordered data
support. Its complete entry word starts in zero and the checked equation
returns it to zero, with every original input column and exact phase retained. -/
structure Synthesis (circuit : Circuit) (start count : Nat) (locations scratch reserved : List Nat)
    (steps : List Semantics.Finite.Step) where
  axes : List Nat
  originalAxes : axes = (steps.flatMap stepAxes).eraseDups
  inFrame : steps.all (fun step => (stepAxes step).all (· < locations.length)) = true
  layout : List Nat
  placed : axes.mapM (fun axis => locations[axis]?) = some layout
  declared : circuit.declares (locations ++ scratch)
  lifetime : (∀ wire ∈ scratch, wire ∈ reserved) ∨ outsideUntouched circuit start count scratch = true
  actual : List Semantics.Finite.Step
  targetWord : CanonicalOpenQasmWorkspace.interval circuit (layout ++ scratch) start count = some actual
  logical : Semantics.Exact.Matrix
  originalOperator : RuntimeInterval.Computed
    (circuitMatrix [] (Raw.circuit axes.length (localWord locations.length axes steps))) logical
  physical : Semantics.Exact.Matrix
  restored : RuntimeInterval.Computed (checkedSynthesis axes.length scratch.length actual logical) physical

theorem Synthesis.zeroReturn {circuit start count locations scratch reserved steps}
    (checked : Synthesis circuit start count locations scratch reserved steps) :
    ∃ encoding first middle afterCircuit lhs lhsWork rhs rhsWork,
      (Raw.zeroEncoding checked.axes.length scratch.length).run first = (.ok encoding,middle) ∧
      Exact.Matrix.compose checked.physical encoding.map afterCircuit = (.ok lhs,lhsWork) ∧
      Exact.Matrix.compose encoding.map checked.logical lhsWork = (.ok rhs,rhsWork) ∧ lhs = rhs := by
  obtain ⟨first,left,ran⟩ := checked.restored
  unfold checkedSynthesis at ran
  obtain ⟨encoding,middle,zero,accepted⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨_,afterCircuit,lhs,lhsWork,rhs,rhsWork,_,same⟩ :=
    (Finite.check_conditions _ _ _ _ _ _ _ accepted).2.2.2.2.2.2
  exact ⟨encoding,first,middle,afterCircuit,lhs,lhsWork,rhs,rhsWork,zero,same⟩

theorem Synthesis.exclusiveScratch {circuit start count locations scratch steps}
    (checked : Synthesis circuit start count locations scratch [] steps) {wire : Nat} (member : wire ∈ scratch) :
    wire ∉ circuit.measurements ∧
      ∀ gate ∈ circuit.gates.take start ++ circuit.gates.drop (start+count), wire ∉ gate.wires := by
  have exclusive := checked.lifetime.resolve_left (fun reserved => by simpa using reserved wire member)
  have untouched := List.all_eq_true.mp exclusive wire member
  have places : wire ∉ circuit.measurements ∧
      (∀ gate ∈ circuit.gates.take start, wire ∉ gate.wires) ∧
      (∀ gate ∈ circuit.gates.drop (start+count), wire ∉ gate.wires) := by
    simpa [List.contains_eq_mem,List.all_eq_true] using untouched
  exact ⟨places.1,fun gate occurs => (List.mem_append.mp occurs).elim (places.2.1 gate) (places.2.2 gate)⟩

private def checkSynthesisWith (circuit : Circuit) (start count : Nat) (locations scratch reserved : List Nat)
    (steps : List Semantics.Finite.Step) : WorkM (Synthesis circuit start count locations scratch reserved steps) := do
  guard (locations.length ≤ 12 && scratch.length ≤ 6 && !scratch.isEmpty && steps.length ≤ 1024 &&
    start+count ≤ circuit.gates.length && count ≤ 1024) .limit
  exactWork (Exact.charge (64*(1+start+count+steps.length)*(1+locations.length+scratch.length+reserved.length)))
  if !(scratch.all reserved.contains) then
    exactWork (Exact.charge (64*(1+scratch.length)*(1+circuit.gates.length+circuit.measurements.length)))
  if inFrame : steps.all (fun step => (stepAxes step).all (· < locations.length)) then
    let axes := (steps.flatMap stepAxes).eraseDups
    guard (axes.length + scratch.length ≤ 6) .limit
    if valid : circuit.declares (locations ++ scratch) ∧
        ((∀ wire ∈ scratch, wire ∈ reserved) ∨ outsideUntouched circuit start count scratch = true) then
      match placed : axes.mapM (fun axis => locations[axis]?) with
      | none => throw .request
      | some layout =>
        match targetWord : CanonicalOpenQasmWorkspace.interval circuit (layout ++ scratch) start count with
        | none => throw .request
        | some actual =>
          let logical ← SourceTypes.NaturalAffine.witness
            (circuitMatrix [] (Raw.circuit axes.length (localWord locations.length axes steps)))
          let checked ← SourceTypes.NaturalAffine.witness (checkedSynthesis axes.length scratch.length actual logical.val)
          return ⟨axes,rfl,inFrame,layout,placed,valid.1,valid.2,actual,targetWord,logical.val,
            by exact logical.property,checked.val,by exact checked.property⟩
    else throw .request
  else throw .request

def checkSynthesis (circuit : Circuit) (start count : Nat) (locations scratch : List Nat)
    (steps : List Semantics.Finite.Step) : WorkM (Synthesis circuit start count locations scratch [] steps) :=
  checkSynthesisWith circuit start count locations scratch [] steps

/-- A structural basis lift reorders the encoding of the same live wires.
    Every basis label must match that wiring, including the zero-width case. -/
private def followBasisAxes (locations inputAxes outputAxes table : List Nat) :
    WorkM (List Nat) := do
  let width := inputAxes.length
  guard (width ≤ 12 && locations.length ≤ 12) .limit
  guard (outputAxes.length == width && table.length == 2^width &&
    inputAxes.Nodup && outputAxes.Nodup && outputAxes.all inputAxes.contains &&
    inputAxes.all (· < locations.length)) .request
  exactWork (Exact.charge (64*(1+width)*(1+table.length)))
  let labels := table.toArray
  let destinations := (List.range width).map fun axis =>
    (List.range width).find? (fun destination => labels[2^axis]? == some (2^destination))
  let positions ← lift (readOption (destinations.mapM id))
  guard positions.Nodup .request
  let inputForOutput := (List.range width).map positions.idxOf
  guard (labels.toList.zipIdx.all fun (actual,input) =>
    actual == Semantics.Finite.gather input inputForOutput) .request
  let placed ← lift (readOption (inputAxes.mapM fun axis => locations[axis]?))
  let reordered ← lift (readOption (inputForOutput.mapM fun axis => placed[axis]?))
  return (outputAxes.zip reordered).foldl (fun frame (axis,wire) => frame.set axis wire) locations

#guard ((followBasisAxes [4,7,9] [0,2] [2,0] [0,1,2,3]).run 4096).1.toOption ==
  some [9,7,4]
#guard ((followBasisAxes [4,7,9] [0,2] [0,2] [0,2,1,3]).run 4096).1.toOption ==
  some [9,7,4]
#guard ((followBasisAxes [4,7,9] [] [] [0]).run 4096).1.toOption == some [4,7,9]
#guard ((followBasisAxes [4,7,9] [0,2] [0,2] [0,1,2,0]).run 4096).1.toOption.isNone
#guard ((followBasisAxes [4,7,9] [0,2] [1,2] [0,2,1,3]).run 4096).1.toOption.isNone

private def followRaw (circuit : Circuit) (state : State) (operation : Semantics.Raw.Op)
    (reserved : List Nat) (alignment : Match) : WorkM State := do
  let (next,events) ← lift (readOption (Semantics.RawTrace.step state.raw operation))
  let (locations,gateIndex) ← match alignment,events with
    | .original,[] => pure (state.locations,state.gateIndex)
    | .original,[.init0 _] =>
      lift (readOption ((fresh circuit.qubits state.locations (reserved ++ state.synthesis)).map (·,state.gateIndex)))
    | .original,[.liftBasis before after [] [axis] [0]] =>
      if after == before+1 && axis == before then
        lift (readOption ((fresh circuit.qubits state.locations (reserved ++ state.synthesis)).map (·,state.gateIndex)))
      else throw .request
    | .original,[.liftBasis before after inputAxes outputAxes table] => do
      guard (before == after && before == state.locations.length) .request
      pure (← followBasisAxes state.locations inputAxes outputAxes table,state.gateIndex)
    | .original,[.circuit _ steps] =>
      lift (readOption ((gateWord circuit state.gateIndex state.locations steps).map (state.locations,·)))
    | .decomposed count,[.circuit _ steps] => do
      let _ ← checkDecomposition circuit state.gateIndex count state.locations steps
      pure (state.locations,state.gateIndex+count)
    | .synthesized count scratch,[.circuit _ steps] => do
      guard (scratch.all fun wire => !reserved.contains wire) .request
      let _ ← checkSynthesisWith circuit state.gateIndex count state.locations scratch state.synthesis steps
      pure (state.locations,state.gateIndex+count)
    | _,_ => throw .request
  if next.frame.length == locations.length then
    pure {state with raw := next,locations,rawIndex := state.rawIndex+1,gateIndex}
  else throw .request

private def followSwap (circuit : Circuit) (connected : Nat → Nat → Bool) (state : State)
    (reserved : List Nat) : Option State := do
  let some ⟨.swap,[first,second]⟩ := circuit.gates[state.gateIndex]? | none
  if first != second && first < circuit.qubits && second < circuit.qubits && connected first second &&
      !reserved.contains first && !reserved.contains second &&
      !state.synthesis.contains first && !state.synthesis.contains second then
    let move : Routing.Swap := ⟨first,second⟩
    some {state with locations := state.locations.map move.axis, gateIndex := state.gateIndex+1}
  else none

/-- Keep the actual owner transitions of every operation in a source slice.
Only circuit events and structural owner operations share a target word. -/
private def readSpan (original : Array Semantics.Observation.Op) (state : State) (count : Nat) :
    WorkM (Interface × List Semantics.Finite.Step) := do
  guard (1 < count && count ≤ 1024 && state.rawIndex+count ≤ original.size) .limit
  let (final,chunks,_) ← (List.range count).foldlM (fun (frame,chunks,size) offset => do
    let some (.pure operation) := original[state.rawIndex+offset]? | throw .request
    let fields := Raw.rawFields ⟨[],[operation],[],.unitary⟩
    guard (fields ≤ 1025) .limit
    exactWork (Exact.charge (32*(fields+frame.live.length+state.locations.length)))
    let (next,events) ← lift (readOption (Semantics.RawTrace.step frame operation))
    guard (next.frame == state.raw.frame) .request
    match events with
    | [] => pure (next,chunks,size)
    | [.circuit _ steps] => do
      let total := size + steps.length
      guard (total ≤ 1024) .limit
      pure (next,steps :: chunks,total)
    | _ => throw .request) (state.raw,[],0)
  pure (final,chunks.reverse.flatten)

private def followSpan (original : Array Semantics.Observation.Op) (circuit : Circuit) (state : State)
    (rawCount gateCount : Nat) (scratch reserved : List Nat) : WorkM State := do
  let (next,steps) ← readSpan original state rawCount
  if scratch.isEmpty then
    let _ ← checkDecomposition circuit state.gateIndex gateCount state.locations steps
  else
    guard (scratch.all fun wire => !reserved.contains wire) .request
    let _ ← checkSynthesisWith circuit state.gateIndex gateCount state.locations scratch state.synthesis steps
  pure {state with raw := next,rawIndex := state.rawIndex+rawCount,gateIndex := state.gateIndex+gateCount}

private def replayStep (original : Array Semantics.Observation.Op) (circuit : Circuit)
    (connected : Nat → Nat → Bool) (reserved : List Nat) (state : State) (action : Match) : WorkM State :=
  match action with
  | .route => lift (readOption (followSwap circuit connected state reserved))
  | .optimized rawCount gateCount scratch => followSpan original circuit state rawCount gateCount scratch reserved
  | .original | .decomposed _ | .synthesized _ _ => do
    let some (.pure operation) := original[state.rawIndex]? | throw .request
    followRaw circuit state operation reserved action

private def replayFrom (original : Array Semantics.Observation.Op) (circuit : Circuit) (connected : Nat → Nat → Bool)
    (alignment : List Match) (initial : State) (reserved : List Nat := []) : WorkM State :=
  alignment.foldlM (replayStep original circuit connected reserved) initial

/-- A designated routing action consumes the literal SWAP at that gate index,
and moves the live placement along its checked hardware edge. -/
private theorem replay_route {original circuit connected reserved initial final work left}
    (ok : (replayStep original circuit connected reserved initial .route).run work = (.ok final,left)) :
    ∃ first second, circuit.gates[initial.gateIndex]? = some ⟨.swap,[first,second]⟩ ∧
      connected first second = true ∧
      final = { initial with
        locations := initial.locations.map (Routing.Swap.mk first second).axis
        gateIndex := initial.gateIndex+1 } := by
  have lifted := (lift_success _ _ _ _ ok).1
  have swap : followSwap circuit connected initial reserved = some final := by
    change readOption (followSwap circuit connected initial reserved) = .ok final at lifted
    cases h : followSwap circuit connected initial reserved <;> simp_all [readOption]
  unfold followSwap at swap
  split at swap
  · rename_i first second literal
    split at swap
    · rename_i valid
      have edge : connected first second = true := by
        simp only [Bool.and_eq_true] at valid
        exact valid.1.1.1.1.2
      exact ⟨first,second,literal,edge,(Option.some.inj swap).symm⟩
    · contradiction
  · contradiction

/-- The decoded instruction at this paid gate index is a SWAP on a checked edge. -/
def RoutingAt (circuit : Circuit) (connected : Nat → Nat → Bool) (index : Nat) : Prop :=
  ∃ first second, circuit.gates[index]? = some ⟨.swap,[first,second]⟩ ∧ connected first second = true

theorem RoutingAt.within_count {circuit connected index} (route : RoutingAt circuit connected index) :
    index < circuit.counts.gates ∧ 0 < circuit.counts.swaps := by
  obtain ⟨a,b,read,_⟩ := route
  obtain ⟨within,gate⟩ := List.getElem?_eq_some_iff.mp read
  refine ⟨within,?_⟩
  apply List.length_pos_iff_exists_mem.mpr
  refine ⟨⟨.swap,[a,b]⟩,List.mem_filter.mpr ⟨?_,rfl⟩⟩
  rw [← gate]
  exact List.getElem_mem _

private theorem replay_routing_cost {original circuit connected reserved initial final work left}
    (beforeRoute suffix : List Match)
    (ok : (replayFrom original circuit connected (beforeRoute ++ .route :: suffix) initial reserved).run work =
      (.ok final,left)) :
    ∃ prefixExit prefixLeft, (replayFrom original circuit connected beforeRoute initial reserved).run work =
      (.ok prefixExit,prefixLeft) ∧ RoutingAt circuit connected prefixExit.gateIndex := by
  simp only [replayFrom,List.foldlM_append,List.foldlM_cons] at ok
  obtain ⟨prefixExit,prefixLeft,prefixRun,tail⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,routeRun,_⟩ := bind_success _ _ _ _ _ tail
  obtain ⟨a,b,literal,edge,_⟩ := replay_route routeRun
  exact ⟨prefixExit,prefixLeft,prefixRun,a,b,literal,edge⟩

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
  placed : CanonicalOpenQasmWorkspace.Placed map target sourceInterval.before.quantum.reference.frame
    prefixCheck.state.locations prefixCheck.state.gateIndex count

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
      prefixCheck.state.gateIndex+count,prefixCheck.state.synthesis⟩) final
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
          prefixCheck.state.gateIndex+count,prefixCheck.state.synthesis⟩
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
  localProgram : Semantics.Observation.Program
  block : RuntimeInterval.Block dependencies localProgram
  base : Nat
  start : Nat
  length : Nat
  event : SourceTypes.SourceRuntimeContext.WorkspaceEvent sources caller
  events : List (SourceTypes.SourceRuntimeContext.Event sources caller)
  original : RuntimeWorkspace.Original event events
  sourceInterval : RuntimeInterval.Checked block start length
  literalRoot : (program.operations.drop (base+start)).take length =
    (block.operations.drop start).take length
  sourceBefore : RuntimeStructuralAction.SourceState
  literal : RuntimeWorkspace.Literal original sourceInterval sourceBefore
  map : RuntimeWorkspace.CallerMap literal
  alignment : List Match
  count : Nat
  scratch : Option Nat

def Segment.rootStart {program : Semantics.Observation.Program} (segment : Segment program) : Nat :=
  segment.base + segment.start

private def Segment.selectedPorts {program : Semantics.Observation.Program} (segment : Segment program) :
    List Semantics.Raw.Port := segment.map.selected.map (·.port)

private def Segment.returnedPorts {program : Semantics.Observation.Program} (segment : Segment program) :
    List Semantics.Raw.Port := segment.map.returned.map (·.port)

private def followWorkspace (state : Interface) (operations : List Semantics.Raw.Op) : Option Interface :=
  operations.foldlM (fun current op => (Semantics.RawTrace.step current op).map Prod.fst) state

private def Segment.exit {program : Semantics.Observation.Program} (segment : Segment program)
    (entry : State) (after : Interface) : State :=
  ⟨after,entry.locations,segment.rootStart+segment.length,entry.gateIndex+segment.count,entry.synthesis⟩

structure BoundSegment {program : Semantics.Observation.Program} (segment : Segment program)
    {bytes capacity} (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (connected : Nat → Nat → Bool) (reserved : List Nat) (previous entry : State) where
  replayed : RuntimeInterval.Computed
    (replayFrom program.operations.toArray target.circuit connected segment.alignment previous reserved) entry
  offset : entry.rawIndex = segment.rootStart
  selected : PureInterval.portsOf entry.raw.live (segment.selectedPorts.map (·.token)) =
    some segment.selectedPorts
  after : Interface
  continued : followWorkspace entry.raw segment.literal.operations = some after
  returned : PureInterval.portsOf after.live (segment.returnedPorts.map (·.token)) =
    some segment.returnedPorts
  sameWires : after.frame = entry.raw.frame
  spectators : entry.raw.live.filter (fun port => !(segment.selectedPorts.map (·.token)).contains port.token) =
    after.live.filter (fun port => !(segment.returnedPorts.map (·.token)).contains port.token)
  reservedScratch : ∀ wire ∈ segment.scratch.toList, wire ∈ reserved
  placed : CanonicalOpenQasmWorkspace.Placed segment.map target entry.raw.frame
    entry.locations entry.gateIndex segment.count
  scratchUsed : placed.freshScratch = segment.scratch

/-- Routing before a workspace uses actual SWAP instructions; the workspace
proper consumes the complete decoded slice used in its clean/dirty equation. -/
theorem BoundSegment.literal_costs {program : Semantics.Observation.Program} {segment : Segment program}
    {bytes capacity} {target : CanonicalOpenQasmResources.Checked bytes capacity}
    {connected reserved previous entry} (bound : BoundSegment segment target connected reserved previous entry) :
    bound.placed.body.gates.length = segment.count ∧
      entry.gateIndex+segment.count ≤ target.circuit.counts.gates ∧
      ∀ beforeRoute tail, segment.alignment = beforeRoute ++ .route :: tail →
        ∃ state, RuntimeInterval.Computed
          (replayFrom program.operations.toArray target.circuit connected beforeRoute previous reserved) state ∧
          RoutingAt target.circuit connected state.gateIndex ∧ state.gateIndex < target.circuit.counts.gates ∧
          0 < target.circuit.counts.swaps := by
  have ⟨steps,inside⟩ := CanonicalOpenQasmWorkspace.interval_length bound.placed.body.actualInterval
  refine ⟨steps,inside,?_⟩
  intro beforeRoute tail route
  obtain ⟨work,left,ran⟩ := bound.replayed
  rw [route] at ran
  obtain ⟨state,left,prefixRun,routed⟩ := replay_routing_cost beforeRoute tail ran
  exact ⟨state,⟨work,left,prefixRun⟩,routed,routed.within_count⟩

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
  let replayed ← SourceTypes.NaturalAffine.witness
    (replayFrom program.operations.toArray target.circuit connected segment.alignment previous reserved)
  let entry := replayed.val
  let selected := segment.selectedPorts.map (·.token)
  let returned := segment.returnedPorts.map (·.token)
  exactWork (Exact.charge (64*(1+segment.length)*(1+entry.raw.live.length+entry.raw.frame.length)))
  if before : entry.rawIndex = segment.rootStart ∧
      PureInterval.portsOf entry.raw.live selected = some segment.selectedPorts ∧
      (∀ wire ∈ segment.scratch.toList,wire ∈ reserved) then
    match continued : followWorkspace entry.raw segment.literal.operations with
    | none => throw .request
    | some after =>
      exactWork (Exact.charge (32*(1+after.live.length+entry.raw.live.length)*
        (1+selected.length+returned.length)))
      if exit : PureInterval.portsOf after.live returned = some segment.returnedPorts ∧
          after.frame = entry.raw.frame ∧
          entry.raw.live.filter (fun port => !selected.contains port.token) =
            after.live.filter (fun port => !returned.contains port.token) then
        let placed ← CanonicalOpenQasmWorkspace.checkPlacementInFrame segment.map target entry.raw.frame
          entry.locations entry.gateIndex segment.count segment.scratch
        if scratchUsed : placed.freshScratch = segment.scratch then
          return ⟨entry,⟨by exact replayed.property,before.1,before.2.1,after,continued,
            exit.1,exit.2.1,exit.2.2,before.2.2,placed,scratchUsed⟩⟩
        else throw .request
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
    (reserved synthesis : List Nat) : State → CleanUses target.circuit → Nat → Type where
  | start : WorkspaceTrace (program := program) target connected reserved synthesis
      {synthesis := synthesis} (fun _ => []) 0
  | next {previous entry : State} {segment : Segment program} {uses : CleanUses target.circuit} {peak : Nat}
    (earlier : WorkspaceTrace (program := program) target connected reserved synthesis previous uses peak)
    (bound : BoundSegment segment target connected reserved previous entry) :
      WorkspaceTrace (program := program) target connected reserved synthesis (segment.exit entry bound.after)
        (fun scratch => bound.addCleanUse scratch (uses scratch)) (max peak segment.map.resources.counts.peakWires)

/-- Maximum Raw live width across the checked original workspace occurrences,
including the caller's spectators and every temporary clean wire. -/
theorem WorkspaceTrace.peakWires_le {program : Semantics.Observation.Program} {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity} {connected reserved synthesis state uses peak}
    (trace : WorkspaceTrace (program := program) target connected reserved synthesis state uses peak) :
    peak ≤ target.circuit.qubits := by
  induction trace with
  | start => exact Nat.zero_le _
  | next _ bound ih => exact Nat.max_le.mpr ⟨ih,bound.placed.body.coversRawPeak⟩

structure TraceWithUses {program : Semantics.Observation.Program} {bytes capacity}
    (target : CanonicalOpenQasmResources.Checked bytes capacity) (connected : Nat → Nat → Bool)
    (reserved synthesis : List Nat) where
  exit : State
  cleanUses : CleanUses target.circuit
  peakWires : Nat
  trace : @WorkspaceTrace program bytes capacity target connected reserved synthesis exit cleanUses peakWires

structure FinishedTrace (program : Semantics.Observation.Program) {bytes capacity}
    (target : CanonicalOpenQasmResources.Checked bytes capacity) (connected : Nat → Nat → Bool)
    (reserved synthesis : List Nat) (suffix : List Match) where
  closed : program.inputs.isEmpty = true ∧ program.classicalInputs.isEmpty = true
  declared : target.circuit.declares (reserved ++ synthesis)
  synthesisUnmeasured : ∀ wire ∈ synthesis, wire ∉ target.circuit.measurements
  recorded : @TraceWithUses program bytes capacity target connected reserved synthesis
  final : State
  replayed : RuntimeInterval.Computed
    (replayFrom program.operations.toArray target.circuit connected suffix recorded.exit reserved) final
  readout : Readout target program final
  restored : ∀ scratch ∈ reserved, Nonempty (CanonicalOpenQasmWorkspace.Reuse target scratch (recorded.cleanUses scratch))

/-- Routing in the replay after the final workspace is accounted for in the
same literal gate word that supplies terminal resource counts. -/
theorem FinishedTrace.suffix_routing_paid {program : Semantics.Observation.Program} {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity} {connected reserved synthesis suffix}
    (trace : FinishedTrace program target connected reserved synthesis suffix) (beforeRoute tail : List Match)
    (route : suffix = beforeRoute ++ .route :: tail) :
    ∃ state, RuntimeInterval.Computed
      (replayFrom program.operations.toArray target.circuit connected beforeRoute trace.recorded.exit reserved) state ∧
      RoutingAt target.circuit connected state.gateIndex ∧ state.gateIndex < target.circuit.counts.gates ∧
      0 < target.circuit.counts.swaps := by
  obtain ⟨work,left,ran⟩ := trace.replayed
  have runAt := congrArg (fun alignment =>
    (replayFrom program.operations.toArray target.circuit connected alignment trace.recorded.exit reserved).run work) route
  obtain ⟨state,left,prefixRun,routed⟩ := replay_routing_cost beforeRoute tail (runAt.symm.trans ran)
  exact ⟨state,⟨work,left,prefixRun⟩,routed,routed.within_count⟩

/-- Follow every original interval in order while keeping designations for
clean scratch fixed. Ordinary preparation and routing cannot use a designated
scratch wire. Each such wire is restored by its own exact, disjoint uses. -/
def finishTrace {bytes capacity} (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (program : Semantics.Observation.Program) (connected : Nat → Nat → Bool) (reserved : List Nat)
    (segments : List (Segment program)) (suffix : List Match) (synthesis : List Nat := []) :
    WorkM (FinishedTrace program target connected reserved synthesis suffix) := do
  guard (program.operations.length ≤ 65536 && segments.length ≤ program.operations.length &&
    reserved.length + synthesis.length ≤ 12) .limit
  exactWork (Exact.charge (32*(program.operations.length+segments.length+1)))
  if closed : program.inputs.isEmpty = true ∧ program.classicalInputs.isEmpty = true then
    if valid : target.circuit.declares (reserved ++ synthesis) ∧
        (∀ wire ∈ synthesis, wire ∉ target.circuit.measurements) then
      let recorded ← segments.foldlM (fun (state : @TraceWithUses program bytes capacity target connected reserved synthesis) segment => do
        let ⟨entry,bound⟩ ← checkSegment segment target connected reserved state.exit
        pure ⟨segment.exit entry bound.after,fun scratch => bound.addCleanUse scratch (state.cleanUses scratch),
          max state.peakWires segment.map.resources.counts.peakWires,.next state.trace bound⟩)
        ⟨{synthesis := synthesis},fun _ => [],0,.start⟩
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
        return ⟨closed,valid.1,valid.2,recorded,final.val,by exact final.property,output,restored⟩
      else throw .request
    else throw .request
  else throw .request

end QleisliKernel.Target.CanonicalOpenQasmPlacement
