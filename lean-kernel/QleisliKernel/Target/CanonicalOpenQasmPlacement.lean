import QleisliKernel.Target.CanonicalOpenQasmWorkspace
import QleisliKernel.Qirf.RuntimeNamedFrameAxes

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
structure Decomposition (rootDependencies : List Semantics.Finite.Dependency) (circuit : Circuit) (start count : Nat) (locations : List Nat)
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
    (circuitMatrix rootDependencies (Raw.circuit axes.length (localWord locations.length axes steps))) matrix
  targetOperator : RuntimeInterval.Computed (circuitMatrix [] (Raw.circuit axes.length actual)) matrix

def checkDecomposition (circuit : Circuit) (start count : Nat) (locations : List Nat)
    (steps : List Semantics.Finite.Step) (rootDependencies : List Semantics.Finite.Dependency := []) :
    WorkM (Decomposition rootDependencies circuit start count locations steps) := do
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
            (circuitMatrix rootDependencies (Raw.circuit axes.length (localWord locations.length axes steps)))
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
structure Synthesis (rootDependencies : List Semantics.Finite.Dependency) (circuit : Circuit) (start count : Nat) (locations scratch reserved : List Nat)
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
    (circuitMatrix rootDependencies (Raw.circuit axes.length (localWord locations.length axes steps))) logical
  physical : Semantics.Exact.Matrix
  restored : RuntimeInterval.Computed (checkedSynthesis axes.length scratch.length actual logical) physical

/-- Recover the actual finite contract check for the decoded target interval.
The same zero encoding is used at both ends on the ordered local support. -/
theorem Synthesis.checkedEncoding {rootDependencies circuit start count locations scratch reserved steps}
    (checked : Synthesis rootDependencies circuit start count locations scratch reserved steps) :
    ∃ encoding first middle left,
      (Raw.zeroEncoding checked.axes.length scratch.length).run first = (.ok encoding,middle) ∧
      let required : Semantics.Finite.Contract := ⟨encoding,encoding,checked.logical⟩
      (Finite.check [] (Raw.circuit (checked.axes.length + scratch.length) checked.actual)
        required required).run middle = (.ok checked.physical,left) := by
  obtain ⟨first,left,ran⟩ := checked.restored
  unfold checkedSynthesis at ran
  obtain ⟨encoding,middle,zero,accepted⟩ := bind_success _ _ _ _ _ ran
  exact ⟨encoding,first,middle,left,zero,accepted⟩

theorem Synthesis.zeroReturn {rootDependencies circuit start count locations scratch reserved steps}
    (checked : Synthesis rootDependencies circuit start count locations scratch reserved steps) :
    ∃ encoding first middle afterCircuit lhs lhsWork rhs rhsWork,
      (Raw.zeroEncoding checked.axes.length scratch.length).run first = (.ok encoding,middle) ∧
      Exact.Matrix.compose checked.physical encoding.map afterCircuit = (.ok lhs,lhsWork) ∧
      Exact.Matrix.compose encoding.map checked.logical lhsWork = (.ok rhs,rhsWork) ∧ lhs = rhs := by
  obtain ⟨encoding,first,middle,_,zero,accepted⟩ := checked.checkedEncoding
  obtain ⟨_,afterCircuit,lhs,lhsWork,rhs,rhsWork,_,same⟩ :=
    (Finite.check_conditions _ _ _ _ _ _ _ accepted).2.2.2.2.2.2
  exact ⟨encoding,first,middle,afterCircuit,lhs,lhsWork,rhs,rhsWork,zero,same⟩

theorem Synthesis.exclusiveScratch {rootDependencies circuit start count locations scratch steps}
    (checked : Synthesis rootDependencies circuit start count locations scratch [] steps) {wire : Nat} (member : wire ∈ scratch) :
    wire ∉ circuit.measurements ∧
      ∀ gate ∈ circuit.gates.take start ++ circuit.gates.drop (start+count), wire ∉ gate.wires := by
  have exclusive := checked.lifetime.resolve_left (fun reserved => by simpa using reserved wire member)
  have untouched := List.all_eq_true.mp exclusive wire member
  have places : wire ∉ circuit.measurements ∧
      (∀ gate ∈ circuit.gates.take start, wire ∉ gate.wires) ∧
      (∀ gate ∈ circuit.gates.drop (start+count), wire ∉ gate.wires) := by
    simpa [List.contains_eq_mem,List.all_eq_true] using untouched
  exact ⟨places.1,fun gate occurs => (List.mem_append.mp occurs).elim (places.2.1 gate) (places.2.2 gate)⟩

private def checkSynthesisWith (rootDependencies : List Semantics.Finite.Dependency) (circuit : Circuit) (start count : Nat) (locations scratch reserved : List Nat)
    (steps : List Semantics.Finite.Step) : WorkM (Synthesis rootDependencies circuit start count locations scratch reserved steps) := do
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
            (circuitMatrix rootDependencies (Raw.circuit axes.length (localWord locations.length axes steps)))
          let checked ← SourceTypes.NaturalAffine.witness (checkedSynthesis axes.length scratch.length actual logical.val)
          return ⟨axes,rfl,inFrame,layout,placed,valid.1,valid.2,actual,targetWord,logical.val,
            by exact logical.property,checked.val,by exact checked.property⟩
    else throw .request
  else throw .request

def checkSynthesis (circuit : Circuit) (start count : Nat) (locations scratch : List Nat)
    (steps : List Semantics.Finite.Step) (rootDependencies : List Semantics.Finite.Dependency := []) :
    WorkM (Synthesis rootDependencies circuit start count locations scratch [] steps) :=
  checkSynthesisWith rootDependencies circuit start count locations scratch [] steps

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

private def structuralWord (bits : Nat) (axes : List Nat) (forward inverse : List Semantics.Finite.Step)
    (uses : List Semantics.Raw.Use) : List Semantics.Finite.Step :=
  (forward ++ uses.map (Raw.physicalUse 0 axes.length) ++ inverse).map
    (Semantics.RawTrace.localize (axes ++ [bits]))

private abbrev CheckedWord (rootDependencies : List Semantics.Finite.Dependency) (circuit : Circuit)
    (start count : Nat) (layout scratch reserved : List Nat) (steps : List Semantics.Finite.Step) :=
  if scratch.isEmpty then Decomposition rootDependencies circuit start count layout steps
  else Synthesis rootDependencies circuit start count layout scratch reserved steps

private def checkWord (rootDependencies : List Semantics.Finite.Dependency) (circuit : Circuit)
    (start count : Nat) (layout scratch reserved : List Nat) (steps : List Semantics.Finite.Step) :
    WorkM (CheckedWord rootDependencies circuit start count layout scratch reserved steps) := do
  if empty : scratch.isEmpty then
    let checked ← checkDecomposition circuit start count layout steps rootDependencies
    pure (by simpa only [CheckedWord,if_pos empty] using checked)
  else
    let checked ← checkSynthesisWith rootDependencies circuit start count layout scratch reserved steps
    pure (by simpa only [CheckedWord,if_neg empty] using checked)

private theorem checkedWord_within {rootDependencies circuit start count layout scratch reserved steps}
    (checked : CheckedWord rootDependencies circuit start count layout scratch reserved steps) :
    start+count ≤ circuit.gates.length := by
  unfold CheckedWord at checked
  split at checked
  · exact (CanonicalOpenQasmWorkspace.interval_length checked.targetWord).2
  · exact (CanonicalOpenQasmWorkspace.interval_length checked.targetWord).2

/-- The predicate wire is part of the original operator. Extra synthesis
wires, when present, have their own checked zero-return equation. -/
structure StructuralPlacement (rootDependencies : List Semantics.Finite.Dependency) (circuit : Circuit)
    (state : State) (count auxiliary : Nat) (scratch reserved : List Nat) (bits : Nat) (axes : List Nat)
    (forward inverse : List Semantics.Finite.Step) (uses : List Semantics.Raw.Use) where
  inFrame : bits = state.locations.length ∧ axes.all (· < bits) = true
  predicateReserved : state.synthesis.contains auxiliary = true ∧ reserved.contains auxiliary = false
  declared : circuit.declares (state.locations ++ [auxiliary] ++ scratch)
  action : CheckedWord rootDependencies circuit state.gateIndex count (state.locations ++ [auxiliary])
    scratch state.synthesis (structuralWord bits axes forward inverse uses)

private def checkStructural (rootDependencies : List Semantics.Finite.Dependency) (circuit : Circuit)
    (state : State) (operation : Semantics.Raw.Op) (reserved : List Nat) (count auxiliary : Nat) (scratch : List Nat)
    (bits : Nat) (axes : List Nat) (forward inverse : List Semantics.Finite.Step) (uses : List Semantics.Raw.Use) :
    WorkM (StructuralPlacement rootDependencies circuit state count auxiliary scratch reserved
      bits axes forward inverse uses) := do
  if header : bits = state.locations.length ∧ state.synthesis.contains auxiliary = true ∧
      reserved.contains auxiliary = false ∧ scratch.all (fun wire => !reserved.contains wire) = true then
    let fields := Raw.rawFields ⟨[],[operation],[],.unitary⟩
    guard (fields ≤ 1025) .limit
    exactWork (Exact.charge (32*(1+fields)*(1+bits)))
    let layout := state.locations ++ [auxiliary]
    if valid : circuit.declares (layout ++ scratch) ∧ axes.all (· < bits) = true then
      let word := forward ++ uses.map (Raw.physicalUse 0 axes.length) ++ inverse
      guard (word.all (fun step => (stepAxes step).all (· ≤ axes.length))) .request
      let steps := word.map (Semantics.RawTrace.localize (axes ++ [bits]))
      let action ← checkWord rootDependencies circuit state.gateIndex count layout scratch state.synthesis steps
      return ⟨⟨header.1,valid.2⟩,⟨header.2.1,header.2.2.1⟩,valid.1,action⟩
    else throw .request
  else throw .request

/-- The entire decoded compute-use-inverse interval occupies counted gate
positions, including any physical synthesis and uncomputation. -/
theorem StructuralPlacement.literal_costs {rootDependencies circuit state count auxiliary scratch reserved
    bits axes forward inverse uses}
    (checked : StructuralPlacement rootDependencies circuit state count auxiliary scratch reserved
      bits axes forward inverse uses) :
    state.gateIndex+count ≤ circuit.counts.gates ∧
      ((circuit.gates.drop state.gateIndex).take count).length = count ∧
      (state.locations ++ [auxiliary] ++ scratch).Nodup ∧
      ∀ wire ∈ state.locations ++ [auxiliary] ++ scratch, wire < circuit.counts.reset := by
  have inside := checkedWord_within checked.action
  have enough : count ≤ circuit.gates.length - state.gateIndex := by omega
  exact ⟨inside,by simp [List.length_take,Nat.min_eq_left enough],checked.declared⟩

private def protectedTableWord (sourceBits dataBits auxiliaryBits : Nat) (function : List Nat)
    (uses : List Semantics.Raw.Use) : List Semantics.Finite.Step :=
  let compute := Raw.computeStep sourceBits dataBits auxiliaryBits function
  [compute] ++ uses.map (Raw.physicalUse sourceBits dataBits) ++ [compute]

/-- The checked table action uses the original reversible embedding and
protected operations on their complete ordered carrier. -/
structure ProtectedTablePlacement (rootDependencies : List Semantics.Finite.Dependency) (circuit : Circuit)
    (state : State) (count : Nat) (workspace : List Nat) (bits : Nat) (axes : List Nat)
    (sourceBits auxiliaryBits : Nat) (function : List Nat) (uses : List Semantics.Raw.Use) where
  declared : circuit.declares (state.locations ++ workspace.take auxiliaryBits ++ workspace.drop auxiliaryBits)
  action : CheckedWord rootDependencies circuit state.gateIndex count (state.locations ++ workspace.take auxiliaryBits)
    (workspace.drop auxiliaryBits) state.synthesis
    ((protectedTableWord sourceBits axes.length auxiliaryBits function uses).map
      (Semantics.RawTrace.localize (axes ++ (List.range auxiliaryBits).map (bits+·))))

private def checkProtectedTable (rootDependencies : List Semantics.Finite.Dependency) (circuit : Circuit)
    (state : State) (operation : Semantics.Raw.Op) (reserved : List Nat) (count : Nat)
    (workspace : List Nat) (bits : Nat) (axes : List Nat) (sourceBits auxiliaryBits : Nat)
    (function : List Nat) (uses : List Semantics.Raw.Use) : WorkM
      (ProtectedTablePlacement rootDependencies circuit state count workspace bits axes sourceBits auxiliaryBits function uses) := do
  guard (bits == state.locations.length && sourceBits ≤ axes.length && auxiliaryBits ≤ workspace.length &&
    axes.all (· < bits) && workspace.all (fun wire => !reserved.contains wire)) .request
  let auxiliary := workspace.take auxiliaryBits
  let scratch := workspace.drop auxiliaryBits
  guard (auxiliary.all state.synthesis.contains) .request
  let layout := state.locations ++ auxiliary
  if declared : circuit.declares (layout ++ scratch) then
    let fields := Raw.rawFields ⟨[],[operation],[],.unitary⟩
    let width := axes.length + auxiliaryBits
    guard (width ≤ 6 && fields ≤ 1025) .limit
    exactWork (Exact.charge (32*(1+fields)*(1+bits)+4*(2^width)))
    let word := protectedTableWord sourceBits axes.length auxiliaryBits function uses
    guard (word.all (fun step => (stepAxes step).all (· < width))) .request
    let steps := word.map (Semantics.RawTrace.localize (axes ++ (List.range auxiliaryBits).map (bits+·)))
    let action ← checkWord rootDependencies circuit state.gateIndex count layout scratch state.synthesis steps
    return ⟨declared,action⟩
  else throw .request

theorem ProtectedTablePlacement.literal_costs {rootDependencies circuit state count workspace bits axes sourceBits auxiliaryBits function uses}
    (checked : ProtectedTablePlacement rootDependencies circuit state count workspace bits axes sourceBits auxiliaryBits function uses) :
    state.gateIndex+count ≤ circuit.counts.gates ∧
      (state.locations ++ workspace.take auxiliaryBits ++ workspace.drop auxiliaryBits).Nodup ∧
      ∀ wire ∈ state.locations ++ workspace.take auxiliaryBits ++ workspace.drop auxiliaryBits,
        wire < circuit.counts.reset :=
  ⟨checkedWord_within checked.action,checked.declared⟩

private def followRaw (rootDependencies : List Semantics.Finite.Dependency) (circuit : Circuit) (state : State) (operation : Semantics.Raw.Op)
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
      let _ ← checkDecomposition circuit state.gateIndex count state.locations steps rootDependencies
      pure (state.locations,state.gateIndex+count)
    | .synthesized count scratch,[.circuit _ steps] => do
      guard (scratch.all fun wire => !reserved.contains wire) .request
      let _ ← checkSynthesisWith rootDependencies circuit state.gateIndex count state.locations scratch state.synthesis steps
      pure (state.locations,state.gateIndex+count)
    | .synthesized count (auxiliary :: scratch),[.structuralComputed bits axes forward inverse uses] => do
      let _ ← checkStructural rootDependencies circuit state operation reserved count auxiliary scratch
        bits axes forward inverse uses
      pure (state.locations,state.gateIndex+count)
    | .decomposed count,[.protectedComputed bits axes sourceBits 0 function uses] => do
      let _ ← checkProtectedTable rootDependencies circuit state operation reserved count [] bits axes sourceBits 0 function uses
      pure (state.locations,state.gateIndex+count)
    | .synthesized count workspace,[.protectedComputed bits axes sourceBits auxiliaryBits function uses] => do
      let _ ← checkProtectedTable rootDependencies circuit state operation reserved count workspace bits axes sourceBits auxiliaryBits function uses
      pure (state.locations,state.gateIndex+count)
    | _,_ => throw .request
  if next.frame.length == locations.length then
    pure {state with raw := next,locations,rawIndex := state.rawIndex+1,gateIndex}
  else throw .request

private theorem followRaw_structural {rootDependencies circuit state operation reserved count auxiliary scratch
    bits axes forward inverse uses next final work left}
    (read : Semantics.RawTrace.step state.raw operation = some
      (next,[.structuralComputed bits axes forward inverse uses]))
    (ok : (followRaw rootDependencies circuit state operation reserved
      (.synthesized count (auxiliary :: scratch))).run work = (.ok final,left)) :
    Nonempty (StructuralPlacement rootDependencies circuit state count auxiliary scratch reserved
      bits axes forward inverse uses) ∧
    final = {state with raw := next,rawIndex := state.rawIndex+1,gateIndex := state.gateIndex+count} := by
  have loaded : (lift (readOption (Semantics.RawTrace.step state.raw operation)) : WorkM _) =
      pure (next,[Semantics.Raw.Event.structuralComputed bits axes forward inverse uses]) := by rw [read]; rfl
  simp only [followRaw,loaded,pure_bind] at ok
  obtain ⟨checked,_,_,finish⟩ := bind_success _ _ _ _ _ ok
  refine ⟨⟨checked⟩,?_⟩
  split at finish
  · exact (pure_success _ _ _ _ finish).1
  · cases finish

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
private def readSpanStep (original : Array Semantics.Observation.Op) (state : State)
    (input : Interface × List (List Semantics.Finite.Step) × Nat) (offset : Nat) :
    WorkM (Interface × List (List Semantics.Finite.Step) × Nat) := do
  let (frame,chunks,size) := input
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
  | _ => throw .request

private def readSpan (original : Array Semantics.Observation.Op) (state : State) (count : Nat) :
    WorkM (Interface × List Semantics.Finite.Step) := do
  guard (1 < count && count ≤ 1024 && state.rawIndex+count ≤ original.size) .limit
  let (final,chunks,_) ← (List.range count).foldlM (readSpanStep original state) (state.raw,[],0)
  pure (final,chunks.reverse.flatten)

private def followSpan (rootDependencies : List Semantics.Finite.Dependency) (original : Array Semantics.Observation.Op) (circuit : Circuit) (state : State)
    (rawCount gateCount : Nat) (scratch reserved : List Nat) : WorkM State := do
  let (next,steps) ← readSpan original state rawCount
  if scratch.isEmpty then
    let _ ← checkDecomposition circuit state.gateIndex gateCount state.locations steps rootDependencies
  else
    guard (scratch.all fun wire => !reserved.contains wire) .request
    let _ ← checkSynthesisWith rootDependencies circuit state.gateIndex gateCount state.locations scratch state.synthesis steps
  pure {state with raw := next,rawIndex := state.rawIndex+rawCount,gateIndex := state.gateIndex+gateCount}

private def replayStep (rootDependencies : List Semantics.Finite.Dependency) (original : Array Semantics.Observation.Op) (circuit : Circuit)
    (connected : Nat → Nat → Bool) (reserved : List Nat) (state : State) (action : Match) : WorkM State :=
  match action with
  | .route => lift (readOption (followSwap circuit connected state reserved))
  | .optimized rawCount gateCount scratch => followSpan rootDependencies original circuit state rawCount gateCount scratch reserved
  | .original | .decomposed _ | .synthesized _ _ => do
    let some (.pure operation) := original[state.rawIndex]? | throw .request
    followRaw rootDependencies circuit state operation reserved action

private def replayFrom (rootDependencies : List Semantics.Finite.Dependency) (original : Array Semantics.Observation.Op) (circuit : Circuit) (connected : Nat → Nat → Bool)
    (alignment : List Match) (initial : State) (reserved : List Nat := []) : WorkM State :=
  alignment.foldlM (replayStep rootDependencies original circuit connected reserved) initial

/-- Original ordered steps for one circuit event or for a successfully read
optimized span, with the owner frame recorded at the occurrence. -/
inductive SynthesisSource (original : Array Semantics.Observation.Op) (entry : State) :
    Nat → List Semantics.Finite.Step → Prop where
  | single {operation next bits steps}
      (occurrence : original[entry.rawIndex]? = some (.pure operation))
      (event : Semantics.RawTrace.step entry.raw operation = some (next,[.circuit bits steps])) :
      SynthesisSource original entry 1 steps
  | span {count next steps}
      (read : RuntimeInterval.Computed (readSpan original entry count) (next,steps)) :
      SynthesisSource original entry count steps

/-- The original steps and checked decomposition share the actual ordered
locations and literal gate offset of the replay. -/
def SynthesisAt (dependencies : List Semantics.Finite.Dependency) (original : Array Semantics.Observation.Op)
    (circuit : Circuit) (entry : State) (rawCount gateCount : Nat) (scratch : List Nat) : Prop :=
  ∃ steps, SynthesisSource original entry rawCount steps ∧
    Nonempty (Synthesis dependencies circuit entry.gateIndex gateCount entry.locations scratch entry.synthesis steps)

theorem SynthesisAt.within_gate_count {dependencies original circuit entry rawCount gateCount scratch}
    (atSlice : SynthesisAt dependencies original circuit entry rawCount gateCount scratch) :
    entry.gateIndex + gateCount ≤ circuit.counts.gates := by
  obtain ⟨_,_,⟨checked⟩⟩ := atSlice
  exact (CanonicalOpenQasmWorkspace.interval_length checked.targetWord).2

/-- A synthesized marker can carry a circuit, a structural predicate, or a
protected table. The original Raw event determines which proof applies. -/
def CircuitAt (original : Array Semantics.Observation.Op) (entry : State) : Prop :=
  ∃ operation next bits steps,
    original[entry.rawIndex]? = some (.pure operation) ∧
    Semantics.RawTrace.step entry.raw operation = some (next,[.circuit bits steps])

private theorem replay_synthesized {dependencies original circuit connected reserved entry final count scratch work left}
    (source : CircuitAt original entry)
    (ok : (replayStep dependencies original circuit connected reserved entry
      (.synthesized count scratch)).run work = (.ok final,left)) :
    SynthesisAt dependencies original circuit entry 1 count scratch := by
  obtain ⟨operation,next,bits,steps,occurrence,event⟩ := source
  have originalCheck : (followRaw dependencies circuit entry operation reserved
      (.synthesized count scratch)).run work = (.ok final,left) := by
    simpa only [replayStep,occurrence] using ok
  have loaded : (lift (readOption (Semantics.RawTrace.step entry.raw operation)) : WorkM _) =
      pure (next,[Semantics.Raw.Event.circuit bits steps]) := by rw [event]; rfl
  simp only [followRaw,loaded,pure_bind] at originalCheck
  obtain ⟨_,_,_,ran⟩ := bind_success _ _ _ _ _ originalCheck
  obtain ⟨synthesis,_,_,_⟩ := bind_success _ _ _ _ _ ran
  exact ⟨steps,.single occurrence event,⟨synthesis⟩⟩

private theorem replay_optimized_synthesis {dependencies original circuit connected reserved entry final rawCount gateCount scratch work left}
    (nonempty : scratch.isEmpty = false)
    (ok : (replayStep dependencies original circuit connected reserved entry
      (.optimized rawCount gateCount scratch)).run work = (.ok final,left)) :
    SynthesisAt dependencies original circuit entry rawCount gateCount scratch := by
  change (followSpan dependencies original circuit entry rawCount gateCount scratch reserved).run work =
    (.ok final,left) at ok
  unfold followSpan at ok
  obtain ⟨originalResult,beforeSpan,read,checked⟩ := bind_success _ _ _ _ _ ok
  rcases originalResult with ⟨next,steps⟩
  simp only [nonempty,Bool.false_eq_true,if_false] at checked
  obtain ⟨_,_,_,ran⟩ := bind_success _ _ _ _ _ checked
  obtain ⟨synthesis,_,_,_⟩ := bind_success _ _ _ _ _ ran
  exact ⟨steps,.span ⟨work,beforeSpan,read⟩,⟨synthesis⟩⟩

/-- Identify the original kind of a circuit synthesis occurrence after
replaying its prefix. -/
def SynthesisMatch (original : Array Semantics.Observation.Op) (entry : State)
    (action : Match) (rawCount gateCount : Nat) (scratch : List Nat) : Prop :=
  (action = .synthesized gateCount scratch ∧ rawCount = 1 ∧ CircuitAt original entry) ∨
    (action = .optimized rawCount gateCount scratch ∧ scratch.isEmpty = false)

private theorem replay_synthesis_at {dependencies original circuit connected reserved initial final work left
    action} (prior tail : List Match)
    (ok : (replayFrom dependencies original circuit connected (prior ++ action :: tail)
      initial reserved).run work = (.ok final,left)) :
    ∃ entry, RuntimeInterval.Computed
      (replayFrom dependencies original circuit connected prior initial reserved) entry ∧
      ∀ rawCount gateCount scratch, SynthesisMatch original entry action rawCount gateCount scratch →
        SynthesisAt dependencies original circuit entry rawCount gateCount scratch := by
  simp only [replayFrom,List.foldlM_append,List.foldlM_cons] at ok
  obtain ⟨entry,before,prefixRun,rest⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,sliceRun,_⟩ := bind_success _ _ _ _ _ rest
  refine ⟨entry,⟨work,before,prefixRun⟩,?_⟩
  intro rawCount gateCount scratch kind
  rcases kind with ⟨rfl,rfl,circuitSource⟩ | ⟨rfl,nonempty⟩
  · exact replay_synthesized circuitSource sliceRun
  · exact replay_optimized_synthesis nonempty sliceRun

private theorem replayStep_structural {rootDependencies original circuit connected reserved state count
    auxiliary scratch input output rawScratch forward inverse uses final work left}
    (source : original[state.rawIndex]? = some (.pure (.structuralCompute input output rawScratch forward inverse uses)))
    (ok : (replayStep rootDependencies original circuit connected reserved state
      (.synthesized count (auxiliary :: scratch))).run work = (.ok final,left)) :
    ∃ port taken, Semantics.RawTrace.take state.raw input = some (port,taken) ∧
      Nonempty (StructuralPlacement rootDependencies circuit state count auxiliary scratch reserved
        state.raw.frame.length (Semantics.RawTrace.axes state.raw port.wires) forward inverse uses) ∧
      final = { state with
        raw := Semantics.RawTrace.insert taken output port.wires
        rawIndex := state.rawIndex+1
        gateIndex := state.gateIndex+count } := by
  simp only [replayStep,source] at ok
  cases taken : Semantics.RawTrace.take state.raw input with
  | none =>
    have noEvent : Semantics.RawTrace.step state.raw (.structuralCompute input output rawScratch forward inverse uses) = none := by
      simp [Semantics.RawTrace.step,taken,bind,Option.bind]
    simp only [followRaw,noEvent] at ok
    obtain ⟨loaded,_,first,_⟩ := bind_success _ _ _ _ _ ok
    have invalid : readOption (none : Option (Interface × List Semantics.Raw.Event)) = .ok loaded :=
      (lift_success _ _ _ _ first).1
    cases invalid
  | some originalPort =>
    obtain ⟨port,afterTake⟩ := originalPort
    have sourceEvent : Semantics.RawTrace.step state.raw (.structuralCompute input output rawScratch forward inverse uses) =
        some (Semantics.RawTrace.insert afterTake output port.wires,[.structuralComputed state.raw.frame.length
          (Semantics.RawTrace.axes state.raw port.wires) forward inverse uses]) := by
      simp [Semantics.RawTrace.step,taken,bind,Option.bind]
    obtain ⟨placed,after⟩ := followRaw_structural sourceEvent ok
    exact ⟨port,afterTake,rfl,placed,after⟩

/-- An admitted synthesized segment whose original operation is a structural
computed scope has an exact placement and consumes its full gate interval. -/
def StructuralAt (rootDependencies : List Semantics.Finite.Dependency) (original : Array Semantics.Observation.Op)
    (circuit : Circuit) (reserved : List Nat) (state next : State) (count auxiliary : Nat) (scratch : List Nat) : Prop :=
  ∀ input output rawScratch forward inverse uses,
    original[state.rawIndex]? = some (.pure (.structuralCompute input output rawScratch forward inverse uses)) →
    ∃ port taken, Semantics.RawTrace.take state.raw input = some (port,taken) ∧
      Nonempty (StructuralPlacement rootDependencies circuit state count auxiliary scratch reserved
        state.raw.frame.length (Semantics.RawTrace.axes state.raw port.wires) forward inverse uses) ∧
      state.gateIndex+count ≤ circuit.counts.gates ∧
      next = { state with
        raw := Semantics.RawTrace.insert taken output port.wires
        rawIndex := state.rawIndex+1
        gateIndex := state.gateIndex+count }

private theorem replay_structural_cost {rootDependencies original circuit connected reserved initial final work left
    count auxiliary scratch} (before tail : List Match)
    (ok : (replayFrom rootDependencies original circuit connected
      (before ++ .synthesized count (auxiliary :: scratch) :: tail) initial reserved).run work = (.ok final,left)) :
    ∃ state next, RuntimeInterval.Computed
      (replayFrom rootDependencies original circuit connected before initial reserved) state ∧
      StructuralAt rootDependencies original circuit reserved state next count auxiliary scratch := by
  simp only [replayFrom,List.foldlM_append,List.foldlM_cons] at ok
  obtain ⟨state,middle,prefixRun,rest⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨next,_,stepRun,_⟩ := bind_success _ _ _ _ _ rest
  refine ⟨state,next,⟨work,middle,prefixRun⟩,?_⟩
  intro input output rawScratch forward inverse uses source
  obtain ⟨port,taken,takeRead,⟨placed⟩,after⟩ := replayStep_structural source stepRun
  exact ⟨port,taken,takeRead,⟨placed⟩,placed.literal_costs.1,after⟩

/-- A designated routing action consumes the literal SWAP at that gate index,
and moves the live placement along its checked hardware edge. -/
private theorem replay_route {rootDependencies original circuit connected reserved initial final work left}
    (ok : (replayStep rootDependencies original circuit connected reserved initial .route).run work = (.ok final,left)) :
    ∃ first second, first ≠ second ∧ circuit.gates[initial.gateIndex]? = some ⟨.swap,[first,second]⟩ ∧
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
      have distinct : first ≠ second := by
        simp only [Bool.and_eq_true] at valid
        simpa using valid.1.1.1.1.1.1.1
      have edge : connected first second = true := by
        simp only [Bool.and_eq_true] at valid
        exact valid.1.1.1.1.2
      exact ⟨first,second,distinct,literal,edge,(Option.some.inj swap).symm⟩
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

private theorem replay_routing_cost {rootDependencies original circuit connected reserved initial final work left}
    (beforeRoute suffix : List Match)
    (ok : (replayFrom rootDependencies original circuit connected (beforeRoute ++ .route :: suffix) initial reserved).run work =
      (.ok final,left)) :
    ∃ prefixExit prefixLeft, (replayFrom rootDependencies original circuit connected beforeRoute initial reserved).run work =
      (.ok prefixExit,prefixLeft) ∧ RoutingAt circuit connected prefixExit.gateIndex := by
  simp only [replayFrom,List.foldlM_append,List.foldlM_cons] at ok
  obtain ⟨prefixExit,prefixLeft,prefixRun,tail⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,routeRun,_⟩ := bind_success _ _ _ _ _ tail
  obtain ⟨a,b,_,literal,edge,_⟩ := replay_route routeRun
  exact ⟨prefixExit,prefixLeft,prefixRun,a,b,literal,edge⟩

def replay (original : Array Semantics.Observation.Op) (circuit : Circuit) (connected : Nat → Nat → Bool)
    (alignment : List Match) : WorkM State :=
  replayFrom [] original circuit connected alignment {}

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

private def readoutStep (frame : Interface) (locations : List Nat)
    (entry : Interface × List (Nat × Nat)) (operation : Semantics.Observation.Op) :
    Option (Interface × List (Nat × Nat)) := do
  let (state,measured) := entry
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
  | _ => none

private def followObservation (frame : Interface) (locations : List Nat)
    (operations : List Semantics.Observation.Op) : Option (Interface × List (Nat × Nat)) :=
  operations.foldlM (readoutStep frame locations) (frame,[])

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
  replayed : RuntimeInterval.Computed (replayFrom [] program.operations.toArray target.circuit connected suffix
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
        (replayFrom [] program.operations.toArray target.circuit connected suffix entry)
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
    (rootDependencies : List Semantics.Finite.Dependency)
    {bytes capacity} (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (connected : Nat → Nat → Bool) (reserved : List Nat) (previous entry : State) where
  replayed : RuntimeInterval.Computed
    (replayFrom rootDependencies program.operations.toArray target.circuit connected segment.alignment previous reserved) entry
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
    {rootDependencies connected reserved previous entry} (bound : BoundSegment segment rootDependencies target connected reserved previous entry) :
    bound.placed.body.gates.length = segment.count ∧
      entry.gateIndex+segment.count ≤ target.circuit.counts.gates ∧
      ∀ beforeRoute tail, segment.alignment = beforeRoute ++ .route :: tail →
        ∃ state, RuntimeInterval.Computed
          (replayFrom rootDependencies program.operations.toArray target.circuit connected beforeRoute previous reserved) state ∧
          RoutingAt target.circuit connected state.gateIndex ∧ state.gateIndex < target.circuit.counts.gates ∧
          0 < target.circuit.counts.swaps := by
  have ⟨steps,inside⟩ := CanonicalOpenQasmWorkspace.interval_length bound.placed.body.actualInterval
  refine ⟨steps,inside,?_⟩
  intro beforeRoute tail route
  obtain ⟨work,left,ran⟩ := bound.replayed
  rw [route] at ran
  obtain ⟨state,left,prefixRun,routed⟩ := replay_routing_cost beforeRoute tail ran
  exact ⟨state,⟨work,left,prefixRun⟩,routed,routed.within_count⟩

/-- Recover the checked synthesis evidence from the actual prefix replay
leading to a source workspace. Both a single Raw event and an optimized span
retain the exact original steps and decoded physical interval. -/
theorem BoundSegment.synthesis_at {program : Semantics.Observation.Program} {segment : Segment program}
    {bytes capacity} {target : CanonicalOpenQasmResources.Checked bytes capacity}
    {rootDependencies connected reserved previous entry}
    (bound : BoundSegment segment rootDependencies target connected reserved previous entry)
    {action} (prior tail : List Match)
    (split : segment.alignment = prior ++ action :: tail) :
    ∃ occurrence, RuntimeInterval.Computed
      (replayFrom rootDependencies program.operations.toArray target.circuit connected prior previous reserved) occurrence ∧
      ∀ rawCount gateCount scratch,
        SynthesisMatch program.operations.toArray occurrence action rawCount gateCount scratch →
        SynthesisAt rootDependencies program.operations.toArray target.circuit occurrence rawCount gateCount scratch := by
  obtain ⟨work,left,ran⟩ := bound.replayed
  rw [split] at ran
  exact replay_synthesis_at prior tail ran

theorem BoundSegment.structural_paid {program : Semantics.Observation.Program} {segment : Segment program}
    {bytes capacity} {target : CanonicalOpenQasmResources.Checked bytes capacity}
    {rootDependencies connected reserved previous entry count auxiliary scratch}
    (bound : BoundSegment segment rootDependencies target connected reserved previous entry) (before tail : List Match)
    (splitAt : segment.alignment = before ++ .synthesized count (auxiliary :: scratch) :: tail) :
    ∃ state next, RuntimeInterval.Computed
      (replayFrom rootDependencies program.operations.toArray target.circuit connected before previous reserved) state ∧
      StructuralAt rootDependencies program.operations.toArray target.circuit reserved state next count auxiliary scratch := by
  obtain ⟨_,_,ran⟩ := bound.replayed
  rw [splitAt] at ran
  exact replay_structural_cost before tail ran

private def segmentWork {bytes capacity} (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (program : Semantics.Observation.Program) (alignment : List Match) : WorkM Unit := do
  guard (alignment.length ≤ 65536) .limit
  exactWork (Exact.charge (32*(1+program.operations.length) +
    32*(1+alignment.length)*(1+alignment.length+target.circuit.gates.length)))

/-- A failed workspace equation is located by the selected original Raw interval.
Early placement and shared work failures keep their ordinary rejection. -/
private def workspaceFailure {α : Type} (start count : Nat) (action : WorkM α) : WorkM α := fun work =>
  let (result,left) := action.run work
  (result.mapError (fun error => match error with
    | .workspaceRestoration dirty => .workspacePlacementRestoration dirty start count
    | other => other),left)

private def checkSegment {program : Semantics.Observation.Program} (segment : Segment program)
    (rootDependencies : List Semantics.Finite.Dependency)
    {bytes capacity} (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (connected : Nat → Nat → Bool) (reserved : List Nat) (previous : State) :
    WorkM (Σ entry, BoundSegment segment rootDependencies target connected reserved previous entry) := do
  segmentWork target program segment.alignment
  let replayed ← SourceTypes.NaturalAffine.witness
    (replayFrom rootDependencies program.operations.toArray target.circuit connected segment.alignment previous reserved)
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
        let placed ← workspaceFailure segment.rootStart segment.length
          (CanonicalOpenQasmWorkspace.checkPlacementInFrame segment.map target entry.raw.frame
            entry.locations entry.gateIndex segment.count segment.scratch)
        if scratchUsed : placed.freshScratch = segment.scratch then
          return ⟨entry,⟨by exact replayed.property,before.1,before.2.1,after,continued,
            exit.1,exit.2.1,exit.2.2,before.2.2,placed,scratchUsed⟩⟩
        else throw .request
      else throw .request
  else throw .request

private def BoundSegment.addCleanUse {program : Semantics.Observation.Program} {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity} {rootDependencies connected reserved previous entry}
    {segment : Segment program} (bound : BoundSegment segment rootDependencies target connected reserved previous entry) (scratch : Nat)
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
    (rootDependencies : List Semantics.Finite.Dependency)
    (target : CanonicalOpenQasmResources.Checked bytes capacity) (connected : Nat → Nat → Bool)
    (reserved synthesis : List Nat) : State → CleanUses target.circuit → Nat → Type where
  | start : WorkspaceTrace (program := program) rootDependencies target connected reserved synthesis
      {synthesis := synthesis} (fun _ => []) 0
  | next {previous entry : State} {segment : Segment program} {uses : CleanUses target.circuit} {peak : Nat}
    (earlier : WorkspaceTrace (program := program) rootDependencies target connected reserved synthesis previous uses peak)
    (bound : BoundSegment segment rootDependencies target connected reserved previous entry) :
      WorkspaceTrace (program := program) rootDependencies target connected reserved synthesis (segment.exit entry bound.after)
        (fun scratch => bound.addCleanUse scratch (uses scratch)) (max peak segment.map.resources.counts.peakWires)

/-- Maximum Raw live width across the checked original workspace occurrences,
including the caller's spectators and every temporary clean wire. -/
theorem WorkspaceTrace.peakWires_le {program : Semantics.Observation.Program} {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity} {rootDependencies connected reserved synthesis state uses peak}
    (trace : WorkspaceTrace (program := program) rootDependencies target connected reserved synthesis state uses peak) :
    peak ≤ target.circuit.qubits := by
  induction trace with
  | start => exact Nat.zero_le _
  | next _ bound ih => exact Nat.max_le.mpr ⟨ih,bound.placed.body.coversRawPeak⟩

structure TraceWithUses {program : Semantics.Observation.Program} {bytes capacity}
    (rootDependencies : List Semantics.Finite.Dependency)
    (target : CanonicalOpenQasmResources.Checked bytes capacity) (connected : Nat → Nat → Bool)
    (reserved synthesis : List Nat) where
  exit : State
  cleanUses : CleanUses target.circuit
  peakWires : Nat
  trace : @WorkspaceTrace program bytes capacity rootDependencies target connected reserved synthesis exit cleanUses peakWires

structure FinishedTrace (program : Semantics.Observation.Program) {bytes capacity}
    (rootDependencies : List Semantics.Finite.Dependency)
    (target : CanonicalOpenQasmResources.Checked bytes capacity) (connected : Nat → Nat → Bool)
    (reserved synthesis : List Nat) (suffix : List Match) where
  closed : program.inputs.isEmpty = true ∧ program.classicalInputs.isEmpty = true
  declared : target.circuit.declares (reserved ++ synthesis)
  synthesisUnmeasured : ∀ wire ∈ synthesis, wire ∉ target.circuit.measurements
  recorded : @TraceWithUses program bytes capacity rootDependencies target connected reserved synthesis
  final : State
  replayed : RuntimeInterval.Computed
    (replayFrom rootDependencies program.operations.toArray target.circuit connected suffix recorded.exit reserved) final
  readout : Readout target program final
  restored : ∀ scratch ∈ reserved, Nonempty (CanonicalOpenQasmWorkspace.Reuse target scratch (recorded.cleanUses scratch))

/-- Routing in the replay after the final workspace is accounted for in the
same literal gate word that supplies terminal resource counts. -/
theorem FinishedTrace.suffix_routing_paid {program : Semantics.Observation.Program} {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity} {rootDependencies connected reserved synthesis suffix}
    (trace : FinishedTrace program rootDependencies target connected reserved synthesis suffix) (beforeRoute tail : List Match)
    (route : suffix = beforeRoute ++ .route :: tail) :
    ∃ state, RuntimeInterval.Computed
      (replayFrom rootDependencies program.operations.toArray target.circuit connected beforeRoute trace.recorded.exit reserved) state ∧
      RoutingAt target.circuit connected state.gateIndex ∧ state.gateIndex < target.circuit.counts.gates ∧
      0 < target.circuit.counts.swaps := by
  obtain ⟨work,left,ran⟩ := trace.replayed
  have runAt := congrArg (fun alignment =>
    (replayFrom rootDependencies program.operations.toArray target.circuit connected alignment trace.recorded.exit reserved).run work) route
  obtain ⟨state,left,prefixRun,routed⟩ := replay_routing_cost beforeRoute tail (runAt.symm.trans ran)
  exact ⟨state,⟨work,left,prefixRun⟩,routed,routed.within_count⟩

/-- Recover the actual synthesis slice selected after the final source
workspace, from the same replay that determines the terminal readout. -/
theorem FinishedTrace.suffix_synthesis {program : Semantics.Observation.Program}
    {bytes capacity} {target : CanonicalOpenQasmResources.Checked bytes capacity}
    {rootDependencies connected reserved synthesis suffix}
    (trace : FinishedTrace program rootDependencies target connected reserved synthesis suffix)
    {action} (prior tail : List Match)
    (split : suffix = prior ++ action :: tail) :
    ∃ occurrence, RuntimeInterval.Computed
      (replayFrom rootDependencies program.operations.toArray target.circuit connected prior trace.recorded.exit reserved) occurrence ∧
      ∀ rawCount gateCount scratch,
        SynthesisMatch program.operations.toArray occurrence action rawCount gateCount scratch →
        SynthesisAt rootDependencies program.operations.toArray target.circuit occurrence rawCount gateCount scratch := by
  obtain ⟨work,left,ran⟩ := trace.replayed
  have runAt := congrArg (fun alignment =>
    (replayFrom rootDependencies program.operations.toArray target.circuit connected alignment
      trace.recorded.exit reserved).run work) split
  exact replay_synthesis_at prior tail (runAt.symm.trans ran)

theorem FinishedTrace.suffix_structural_paid {program : Semantics.Observation.Program} {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity}
    {rootDependencies connected reserved synthesis suffix count auxiliary scratch}
    (trace : FinishedTrace program rootDependencies target connected reserved synthesis suffix) (before tail : List Match)
    (splitAt : suffix = before ++ .synthesized count (auxiliary :: scratch) :: tail) :
    ∃ state next, RuntimeInterval.Computed
      (replayFrom rootDependencies program.operations.toArray target.circuit connected before trace.recorded.exit reserved) state ∧
      StructuralAt rootDependencies program.operations.toArray target.circuit reserved state next count auxiliary scratch := by
  obtain ⟨work,_,ran⟩ := trace.replayed
  have runAt := congrArg (fun alignment =>
    (replayFrom rootDependencies program.operations.toArray target.circuit connected alignment trace.recorded.exit reserved).run work) splitAt
  exact replay_structural_cost before tail (runAt.symm.trans ran)

private def recordWorkspace {program : Semantics.Observation.Program} {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity} {rootDependencies connected reserved synthesis}
    (state : @TraceWithUses program bytes capacity rootDependencies target connected reserved synthesis)
    (segment : Segment program) :
    WorkM (@TraceWithUses program bytes capacity rootDependencies target connected reserved synthesis) := do
  let ⟨entry,bound⟩ ← checkSegment segment rootDependencies target connected reserved state.exit
  pure ⟨segment.exit entry bound.after,fun scratch => bound.addCleanUse scratch (state.cleanUses scratch),
    max state.peakWires segment.map.resources.counts.peakWires,.next state.trace bound⟩

/-- Follow every original interval in order while keeping designations for
clean scratch fixed. Ordinary preparation and routing cannot use a designated
scratch wire. Each such wire is restored by its own exact, disjoint uses. -/
def finishTrace {bytes capacity} (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (program : Semantics.Observation.Program) (connected : Nat → Nat → Bool) (reserved : List Nat)
    (segments : List (Segment program)) (suffix : List Match) (synthesis : List Nat := [])
    (rootDependencies : List Semantics.Finite.Dependency := []) :
    WorkM (FinishedTrace program rootDependencies target connected reserved synthesis suffix) := do
  guard (program.operations.length ≤ 65536 && segments.length ≤ program.operations.length &&
    reserved.length + synthesis.length ≤ 12) .limit
  exactWork (Exact.charge (32*(program.operations.length+segments.length+1)))
  if closed : program.inputs.isEmpty = true ∧ program.classicalInputs.isEmpty = true then
    if valid : target.circuit.declares (reserved ++ synthesis) ∧
        (∀ wire ∈ synthesis, wire ∉ target.circuit.measurements) then
      let recorded ← segments.foldlM recordWorkspace
        ⟨{synthesis := synthesis},fun _ => [],0,.start⟩
      segmentWork target program suffix
      let final ← SourceTypes.NaturalAffine.witness
        (replayFrom rootDependencies program.operations.toArray target.circuit connected suffix recorded.exit reserved)
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

#print axioms BoundSegment.synthesis_at
#print axioms FinishedTrace.suffix_synthesis
#print axioms SynthesisAt.within_gate_count

/-- Expose the exact intervening states and consecutive work budgets of a
successful placement replay at a chosen action. -/
private theorem replay_split {rootDependencies original circuit connected reserved initial final work left}
    (prior : List Match) (action : Match) (suffix : List Match)
    (ok : (replayFrom rootDependencies original circuit connected (prior ++ action :: suffix)
      initial reserved).run work = (.ok final,left)) :
    ∃ entry exit atEntry atExit,
      (replayFrom rootDependencies original circuit connected prior initial reserved).run work =
        (.ok entry,atEntry) ∧
      (replayStep rootDependencies original circuit connected reserved entry action).run atEntry =
        (.ok exit,atExit) ∧
      (replayFrom rootDependencies original circuit connected suffix exit reserved).run atExit =
        (.ok final,left) := by
  simp only [replayFrom,List.foldlM_append,List.foldlM_cons] at ok
  obtain ⟨entry,atEntry,prefixRun,restRun⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨exit,atExit,actionRun,suffixRun⟩ := bind_success _ _ _ _ _ restRun
  exact ⟨entry,exit,atEntry,atExit,prefixRun,actionRun,suffixRun⟩

private theorem fresh_spec {capacity locations reserved extended}
    (issued : fresh capacity locations reserved = some extended) :
    ∃ wire, wire < capacity ∧ wire ∉ locations ∧ wire ∉ reserved ∧ extended = locations ++ [wire] := by
  unfold fresh at issued
  obtain ⟨wire,found,equal⟩ := Option.map_eq_some_iff.mp issued
  have valid := List.find?_some found
  simp at valid
  exact ⟨wire,List.mem_range.mp (List.mem_of_find?_eq_some found),valid.1,valid.2,equal.symm⟩

private theorem readOption_success {α : Type} {choice : Option α} {value : α}
    (read : readOption choice = .ok value) : choice = some value := by
  cases choice <;> simp_all [readOption]

private theorem finish_zero_allocation {circuit : Circuit} {state : State} {reserved : List Nat}
    {next : Interface} {final : State} {work left : Nat}
    (ok : (do
      let (locations,gateIndex) ← lift (readOption ((fresh circuit.qubits state.locations
        (reserved ++ state.synthesis)).map (·,state.gateIndex)))
      if next.frame.length == locations.length then
        pure {state with raw := next,locations,rawIndex := state.rawIndex+1,gateIndex}
      else throw .request : WorkM State).run work = (.ok final,left)) :
    ∃ wire, wire < circuit.qubits ∧ wire ∉ state.locations ∧ wire ∉ reserved ++ state.synthesis ∧
      final = {state with raw := next,locations := state.locations ++ [wire],rawIndex := state.rawIndex+1} ∧
      next.frame.length = (state.locations ++ [wire]).length ∧ left = work := by
  obtain ⟨⟨locations,gateIndex⟩,afterFresh,allocated,finish⟩ := bind_success _ _ _ _ _ ok
  change (if next.frame.length == locations.length then
    pure {state with raw := next,locations,rawIndex := state.rawIndex+1,gateIndex}
    else throw .request : WorkM State).run afterFresh = (.ok final,left) at finish
  obtain ⟨read,budget⟩ := lift_success _ _ _ _ allocated
  obtain ⟨extended,found,coordinates⟩ := Option.map_eq_some_iff.mp (readOption_success read)
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj coordinates
  obtain ⟨wire,within,unused,unreserved,rfl⟩ := fresh_spec found
  split at finish
  · rename_i matched
    obtain ⟨rfl,rfl⟩ := pure_success _ _ _ _ finish
    exact ⟨wire,within,unused,unreserved,rfl,by simpa using matched,budget⟩
  · cases finish

/-- A zero allocation in the actual Raw trace appends precisely the physical
wire selected by the placement checker and consumes no decoded gate. -/
private theorem replay_zero_allocation {rootDependencies original circuit connected reserved state final work left}
    {operation : Semantics.Raw.Op} {next : Interface} {event : Semantics.Raw.Event}
    (occurs : original[state.rawIndex]? = some (.pure operation))
    (raw : Semantics.RawTrace.step state.raw operation = some (next,[event]))
    (zero : event = .init0 state.locations.length ∨ event =
      .liftBasis state.locations.length (state.locations.length+1) [] [state.locations.length] [0])
    (ok : (replayStep rootDependencies original circuit connected reserved state .original).run work =
      (.ok final,left)) :
    ∃ wire, wire < circuit.qubits ∧ wire ∉ state.locations ∧ wire ∉ reserved ++ state.synthesis ∧
      final = {state with raw := next,locations := state.locations ++ [wire],rawIndex := state.rawIndex+1} ∧
      next.frame.length = (state.locations ++ [wire]).length ∧ left = work := by
  have loaded : (lift (readOption (Semantics.RawTrace.step state.raw operation)) : WorkM _) =
      pure (next,[event]) := by rw [raw]; rfl
  simp only [replayStep,occurs,followRaw,loaded,pure_bind] at ok
  rcases zero with rfl | rfl
  · exact finish_zero_allocation ok
  · simp only [beq_self_eq_true,Bool.and_self,ite_true] at ok
    exact finish_zero_allocation ok

/-- One occurrence selected from a real placement replay. The prefix, step
and suffix consume the same continuous work state as the complete replay. -/
structure ReplayOccurrence (rootDependencies : List Semantics.Finite.Dependency)
    (original : Array Semantics.Observation.Op) (circuit : Circuit)
    (connected : Nat → Nat → Bool) (reserved : List Nat) (initial final : State)
    (prior : List Match) (action : Match) (suffix : List Match) where
  entry : State
  exit : State
  startWork : Nat
  entryWork : Nat
  exitWork : Nat
  remaining : Nat
  prefixRun : (replayFrom rootDependencies original circuit connected prior initial reserved).run startWork =
    (.ok entry,entryWork)
  stepRun : (replayStep rootDependencies original circuit connected reserved entry action).run entryWork =
    (.ok exit,exitWork)
  suffixRun : (replayFrom rootDependencies original circuit connected suffix exit reserved).run exitWork =
    (.ok final,remaining)

private theorem replay_occurrence {rootDependencies original circuit connected reserved initial final alignment}
    (prior : List Match) (action : Match) (suffix : List Match) (splitAt : alignment = prior ++ action :: suffix)
    (computed : RuntimeInterval.Computed (replayFrom rootDependencies original circuit connected alignment initial reserved) final) :
    Nonempty (ReplayOccurrence rootDependencies original circuit connected reserved initial final prior action suffix) := by
  obtain ⟨work,left,ran⟩ := computed
  rw [splitAt] at ran
  obtain ⟨entry,exit,atEntry,atExit,pre,step,post⟩ := replay_split prior action suffix ran
  exact ⟨⟨entry,exit,work,atEntry,atExit,left,pre,step,post⟩⟩

theorem BoundSegment.occurrence {program : Semantics.Observation.Program} {segment : Segment program}
    {bytes capacity} {target : CanonicalOpenQasmResources.Checked bytes capacity}
    {rootDependencies connected reserved previous final}
    (bound : BoundSegment segment rootDependencies target connected reserved previous final)
    (prior : List Match) (action : Match) (suffix : List Match)
    (splitAt : segment.alignment = prior ++ action :: suffix) :
    Nonempty (ReplayOccurrence rootDependencies program.operations.toArray target.circuit connected reserved
      previous final prior action suffix) :=
  replay_occurrence prior action suffix splitAt bound.replayed

theorem FinishedTrace.suffix_occurrence {program : Semantics.Observation.Program} {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity} {rootDependencies connected reserved synthesis alignment}
    (trace : FinishedTrace program rootDependencies target connected reserved synthesis alignment)
    (prior : List Match) (action : Match) (suffix : List Match) (splitAt : alignment = prior ++ action :: suffix) :
    Nonempty (ReplayOccurrence rootDependencies program.operations.toArray target.circuit connected reserved
      trace.recorded.exit trace.final prior action suffix) :=
  replay_occurrence prior action suffix splitAt trace.replayed

theorem ReplayOccurrence.route {rootDependencies original circuit connected reserved initial final prior suffix}
    (occurrence : ReplayOccurrence rootDependencies original circuit connected reserved initial final prior .route suffix) :
    ∃ first second, first ≠ second ∧ circuit.gates[occurrence.entry.gateIndex]? = some ⟨.swap,[first,second]⟩ ∧
      connected first second = true ∧
      occurrence.exit = {occurrence.entry with
        locations := occurrence.entry.locations.map (Routing.Swap.mk first second).axis
        gateIndex := occurrence.entry.gateIndex+1 } :=
  replay_route occurrence.stepRun

theorem ReplayOccurrence.zero_allocation {rootDependencies original circuit connected reserved initial final prior suffix}
    (occurrence : ReplayOccurrence rootDependencies original circuit connected reserved initial final prior .original suffix)
    {operation : Semantics.Raw.Op} {next : Interface} {event : Semantics.Raw.Event}
    (occurs : original[occurrence.entry.rawIndex]? = some (.pure operation))
    (raw : Semantics.RawTrace.step occurrence.entry.raw operation = some (next,[event]))
    (zero : event = .init0 occurrence.entry.locations.length ∨ event = .liftBasis
      occurrence.entry.locations.length (occurrence.entry.locations.length+1) [] [occurrence.entry.locations.length] [0]) :
    ∃ wire, wire < circuit.qubits ∧ wire ∉ occurrence.entry.locations ∧
      wire ∉ reserved ++ occurrence.entry.synthesis ∧
      occurrence.exit = {occurrence.entry with
        raw := next
        locations := occurrence.entry.locations ++ [wire]
        rawIndex := occurrence.entry.rawIndex+1} ∧
      next.frame.length = (occurrence.entry.locations ++ [wire]).length ∧ occurrence.exitWork = occurrence.entryWork :=
  replay_zero_allocation occurs raw zero occurrence.stepRun

#print axioms BoundSegment.occurrence
#print axioms FinishedTrace.suffix_occurrence
#print axioms ReplayOccurrence.route
#print axioms ReplayOccurrence.zero_allocation

private theorem gateWord_success {circuit : Circuit} {start : Nat} {locations : List Nat}
    {steps : List Semantics.Finite.Step} {stop : Nat}
    (accepted : gateWord circuit start locations steps = some stop) :
    ((circuit.gates.drop start).take steps.length).map Instruction.step =
      steps.map (Semantics.RawTrace.localize locations) ∧ stop = start+steps.length ∧
    ∀ operation ∈ steps,
      (∀ control ∈ operation.controls, control.index < locations.length) ∧
      (∀ axis ∈ Finite.targets operation.action, axis < locations.length) := by
  dsimp only [gateWord] at accepted
  split at accepted
  · cases accepted
  · rename_i bounds
    split at accepted
    · rename_i same
      refine ⟨by simpa using same,(Option.some.inj accepted).symm,?_⟩
      have valid : steps.all (fun operation => (operation.controls.all fun control => control.index < locations.length) &&
          (Finite.targets operation.action).all (· < locations.length)) = true := by
        simpa only [Bool.not_eq_true, Bool.not_eq_false', Function.comp_apply] using bounds
      intro operation member
      have checked := Bool.and_eq_true_iff.mp (List.all_eq_true.mp valid operation member)
      exact ⟨fun control held => of_decide_eq_true (List.all_eq_true.mp checked.1 control held),
        fun axis held => of_decide_eq_true (List.all_eq_true.mp checked.2 axis held)⟩
    · cases accepted

/-- A literal original circuit occurrence consumes the actual decoded word,
using the same ordered controls and target coordinates as the Raw steps. -/
theorem ReplayOccurrence.literal_circuit {rootDependencies original circuit connected reserved initial final prior suffix}
    (occurrence : ReplayOccurrence rootDependencies original circuit connected reserved initial final prior .original suffix)
    {operation : Semantics.Raw.Op} {next : Interface} {bits : Nat} {steps : List Semantics.Finite.Step}
    (occurs : original[occurrence.entry.rawIndex]? = some (.pure operation))
    (raw : Semantics.RawTrace.step occurrence.entry.raw operation = some (next,[.circuit bits steps])) :
    ((circuit.gates.drop occurrence.entry.gateIndex).take steps.length).map Instruction.step =
      steps.map (Semantics.RawTrace.localize occurrence.entry.locations) ∧
    (∀ operation ∈ steps,
      (∀ control ∈ operation.controls, control.index < occurrence.entry.locations.length) ∧
      (∀ axis ∈ Finite.targets operation.action, axis < occurrence.entry.locations.length)) ∧
    occurrence.exit = {occurrence.entry with
      raw := next
      rawIndex := occurrence.entry.rawIndex+1
      gateIndex := occurrence.entry.gateIndex+steps.length } ∧
    next.frame.length = occurrence.entry.locations.length ∧ occurrence.exitWork = occurrence.entryWork := by
  have loaded : (lift (readOption (Semantics.RawTrace.step occurrence.entry.raw operation)) : WorkM _) =
      pure (next,[Semantics.Raw.Event.circuit bits steps]) := by rw [raw]; rfl
  have run := occurrence.stepRun
  simp only [replayStep,occurs,followRaw,loaded,pure_bind] at run
  obtain ⟨⟨layout,stop⟩,afterWord,read,finish⟩ := bind_success _ _ _ _ _ run
  change (if next.frame.length == layout.length then
    pure {occurrence.entry with
      raw := next
      locations := layout
      rawIndex := occurrence.entry.rawIndex+1
      gateIndex := stop }
    else throw .request : WorkM State).run afterWord = (.ok occurrence.exit,occurrence.exitWork) at finish
  obtain ⟨word,budget⟩ := lift_success _ _ _ _ read
  obtain ⟨endAt,checked,equal⟩ := Option.map_eq_some_iff.mp (readOption_success word)
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
  obtain ⟨gates,rfl,bounds⟩ := gateWord_success checked
  split at finish
  · rename_i sameWidth
    obtain ⟨exit,left⟩ := pure_success _ _ _ _ finish
    exact ⟨gates,bounds,exit,by simpa using sameWidth,left.trans budget⟩
  · cases finish

#print axioms ReplayOccurrence.literal_circuit

/-- Retain the exact finite operator comparison performed for one original
circuit event, along with the checked exit coordinates of that occurrence. -/
theorem ReplayOccurrence.decomposed_circuit {rootDependencies original circuit connected reserved initial final prior suffix count}
    (occurrence : ReplayOccurrence rootDependencies original circuit connected reserved initial final prior (.decomposed count) suffix)
    {operation : Semantics.Raw.Op} {next : Interface} {bits : Nat} {steps : List Semantics.Finite.Step}
    (occurs : original[occurrence.entry.rawIndex]? = some (.pure operation))
    (raw : Semantics.RawTrace.step occurrence.entry.raw operation = some (next,[.circuit bits steps])) :
    Nonempty (Decomposition rootDependencies circuit occurrence.entry.gateIndex count occurrence.entry.locations steps) ∧
    occurrence.exit = {occurrence.entry with
      raw := next
      rawIndex := occurrence.entry.rawIndex+1
      gateIndex := occurrence.entry.gateIndex+count } ∧
    next.frame.length = occurrence.entry.locations.length := by
  have loaded : (lift (readOption (Semantics.RawTrace.step occurrence.entry.raw operation)) : WorkM _) =
      pure (next,[Semantics.Raw.Event.circuit bits steps]) := by rw [raw]; rfl
  have run := occurrence.stepRun
  simp only [replayStep,occurs,followRaw,loaded,pure_bind] at run
  obtain ⟨decomposition,_,_,finish⟩ := bind_success _ _ _ _ _ run
  split at finish
  · rename_i matched
    exact ⟨⟨decomposition⟩,(pure_success _ _ _ _ finish).1,by simpa using matched⟩
  · cases finish

/-- An optimized span with no designated scratch uses the same exact
comparison, on the original trace chunks selected by the actual span reader. -/
theorem ReplayOccurrence.optimized_decomposition {rootDependencies original circuit connected reserved initial final prior suffix count gates}
    (occurrence : ReplayOccurrence rootDependencies original circuit connected reserved initial final prior
      (.optimized count gates []) suffix) :
    ∃ next steps,
      RuntimeInterval.Computed (readSpan original occurrence.entry count) (next,steps) ∧
      Nonempty (Decomposition rootDependencies circuit occurrence.entry.gateIndex gates occurrence.entry.locations steps) ∧
      occurrence.exit = {occurrence.entry with
        raw := next
        rawIndex := occurrence.entry.rawIndex+count
        gateIndex := occurrence.entry.gateIndex+gates } := by
  have run := occurrence.stepRun
  change (followSpan rootDependencies original circuit occurrence.entry count gates [] reserved).run
    occurrence.entryWork = (.ok occurrence.exit,occurrence.exitWork) at run
  unfold followSpan at run
  obtain ⟨⟨next,steps⟩,afterRead,read,checked⟩ := bind_success _ _ _ _ _ run
  simp only [List.isEmpty_nil,ite_true] at checked
  obtain ⟨decomposition,_,_,finish⟩ := bind_success _ _ _ _ _ checked
  exact ⟨next,steps,⟨occurrence.entryWork,afterRead,read⟩,⟨decomposition⟩,(pure_success _ _ _ _ finish).1⟩

#print axioms ReplayOccurrence.decomposed_circuit
#print axioms ReplayOccurrence.optimized_decomposition

private theorem localWord_geometry {width : Nat} {axes : List Nat} {steps : List Semantics.Finite.Step}
    (originalAxes : axes = (steps.flatMap stepAxes).eraseDups)
    (inFrame : steps.all (fun step => (stepAxes step).all (· < width)) = true) :
    (∀ axis ∈ axes, axis < width) ∧
    (localWord width axes steps).map (Semantics.RawTrace.localize axes) = steps := by
  have onAxis (operation : Semantics.Finite.Step) (member : operation ∈ steps)
      (axis : Nat) (used : axis ∈ stepAxes operation) : axis < width ∧ axis ∈ axes := by
    have bounds := List.all_eq_true.mp inFrame operation member
    refine ⟨of_decide_eq_true (List.all_eq_true.mp bounds axis used),?_⟩
    rw [originalAxes,List.mem_eraseDups,List.mem_flatMap]
    exact ⟨operation,member,used⟩
  refine ⟨?_,?_⟩
  · intro axis member
    rw [originalAxes,List.mem_eraseDups,List.mem_flatMap] at member
    obtain ⟨operation,held,used⟩ := member
    exact (onAxis operation held axis used).1
  · unfold localWord
    rw [List.map_map]
    conv =>
      rhs
      rw [← List.map_id steps]
    apply List.map_congr_left
    intro operation member
    have recover axis (used : axis ∈ stepAxes operation) :
        (axes[(((List.range width).map axes.idxOf)[axis]?).getD 0]?).getD 0 = axis := by
      obtain ⟨inside,selected⟩ := onAxis operation member axis used
      rw [List.getElem?_map,List.getElem?_range inside]
      simp only [Option.map_some,Option.getD_some]
      rw [RuntimeNamedFrameAxes.wireLookup axes selected,Option.getD_some]
    rcases operation with ⟨controls,action⟩
    have restoreControls : (controls.map (fun control => (⟨
        (axes[(((List.range width).map axes.idxOf)[control.index]?).getD 0]?).getD 0,
        control.whenOne⟩ : Semantics.Finite.Control))) = controls := by
      conv =>
        rhs
        rw [← List.map_id controls]
      apply List.map_congr_left
      intro control held
      rw [recover control.index (List.mem_append_left _ (List.mem_map_of_mem held))]
      cases control
      rfl
    have restoreTargets : ((Finite.targets action).map (fun target =>
        (axes[(((List.range width).map axes.idxOf)[target]?).getD 0]?).getD 0)) =
        Finite.targets action := by
      conv =>
        rhs
        rw [← List.map_id (Finite.targets action)]
      apply List.map_congr_left
      intro target held
      exact recover target (List.mem_append_right _ held)
    cases action with
    | hadamard axis =>
      have again := recover axis (List.mem_append_right _ (List.mem_singleton_self axis))
      simp only [Function.comp_def,id,Semantics.RawTrace.localize,List.map_map,restoreControls,again]
    | monomial axes perm phase =>
      simp only [Finite.targets] at restoreTargets
      simp only [Function.comp_def,id,Semantics.RawTrace.localize,List.map_map,restoreControls,restoreTargets]
    | contract axes dep adjoint =>
      simp only [Finite.targets] at restoreTargets
      simp only [Function.comp_def,id,Semantics.RawTrace.localize,List.map_map,restoreControls,restoreTargets]

/-- Recover the original controls and targets of a checked decomposition. -/
theorem Decomposition.source_geometry {rootDependencies circuit start count locations steps}
    (checked : Decomposition rootDependencies circuit start count locations steps) :
    (∀ axis ∈ checked.axes, axis < locations.length) ∧
    (localWord locations.length checked.axes steps).map (Semantics.RawTrace.localize checked.axes) = steps :=
  localWord_geometry checked.originalAxes checked.inFrame

/-- Recover the original controls and targets of a checked synthesis. -/
theorem Synthesis.source_geometry {rootDependencies circuit start count locations scratch reserved steps}
    (checked : Synthesis rootDependencies circuit start count locations scratch reserved steps) :
    (∀ axis ∈ checked.axes, axis < locations.length) ∧
    (localWord locations.length checked.axes steps).map (Semantics.RawTrace.localize checked.axes) = steps :=
  localWord_geometry checked.originalAxes checked.inFrame

#print axioms Decomposition.source_geometry
#print axioms Synthesis.source_geometry

/-- The synthesized gates compare the actual Raw circuit event at the entry,
and advance both cursor positions to those of the real successful replay. -/
theorem ReplayOccurrence.synthesized_circuit {rootDependencies original circuit connected reserved initial final prior suffix count scratch}
    (occurrence : ReplayOccurrence rootDependencies original circuit connected reserved initial final prior
      (.synthesized count scratch) suffix)
    {operation : Semantics.Raw.Op} {next : Interface} {bits : Nat} {steps : List Semantics.Finite.Step}
    (occurs : original[occurrence.entry.rawIndex]? = some (.pure operation))
    (raw : Semantics.RawTrace.step occurrence.entry.raw operation = some (next,[.circuit bits steps])) :
    Nonempty (Synthesis rootDependencies circuit occurrence.entry.gateIndex count occurrence.entry.locations
      scratch occurrence.entry.synthesis steps) ∧
    occurrence.exit = {occurrence.entry with
      raw := next
      rawIndex := occurrence.entry.rawIndex+1
      gateIndex := occurrence.entry.gateIndex+count } ∧
    next.frame.length = occurrence.entry.locations.length := by
  have loaded : (lift (readOption (Semantics.RawTrace.step occurrence.entry.raw operation)) : WorkM _) =
      pure (next,[Semantics.Raw.Event.circuit bits steps]) := by rw [raw]; rfl
  have run := occurrence.stepRun
  simp only [replayStep,occurs,followRaw,loaded,pure_bind] at run
  obtain ⟨_,_,_,allowed⟩ := bind_success _ _ _ _ _ run
  obtain ⟨checked,_,_,finish⟩ := bind_success _ _ _ _ _ allowed
  split at finish
  · rename_i matched
    exact ⟨⟨checked⟩,(pure_success _ _ _ _ finish).1,by simpa using matched⟩
  · cases finish

/-- The optimized scratch path returns the exact original span read, the
local synthesized comparison, and the next state of the same replay. -/
theorem ReplayOccurrence.optimized_synthesis {rootDependencies original circuit connected reserved initial final prior suffix count gates scratch}
    (occurrence : ReplayOccurrence rootDependencies original circuit connected reserved initial final prior
      (.optimized count gates scratch) suffix) (usesScratch : scratch.isEmpty = false) :
    ∃ next steps,
      RuntimeInterval.Computed (readSpan original occurrence.entry count) (next,steps) ∧
      Nonempty (Synthesis rootDependencies circuit occurrence.entry.gateIndex gates occurrence.entry.locations
        scratch occurrence.entry.synthesis steps) ∧
      occurrence.exit = {occurrence.entry with
        raw := next
        rawIndex := occurrence.entry.rawIndex+count
        gateIndex := occurrence.entry.gateIndex+gates } := by
  have run := occurrence.stepRun
  change (followSpan rootDependencies original circuit occurrence.entry count gates scratch reserved).run
    occurrence.entryWork = (.ok occurrence.exit,occurrence.exitWork) at run
  unfold followSpan at run
  obtain ⟨⟨next,steps⟩,afterRead,read,checked⟩ := bind_success _ _ _ _ _ run
  simp only [usesScratch,Bool.false_eq_true,ite_false] at checked
  obtain ⟨_,_,_,allowed⟩ := bind_success _ _ _ _ _ checked
  obtain ⟨synthesis,_,_,finish⟩ := bind_success _ _ _ _ _ allowed
  exact ⟨next,steps,⟨occurrence.entryWork,afterRead,read⟩,⟨synthesis⟩,(pure_success _ _ _ _ finish).1⟩

#print axioms ReplayOccurrence.synthesized_circuit
#print axioms ReplayOccurrence.optimized_synthesis

/-- The optimized span reads only structural transitions with no gate action
or one original circuit event at a time. Preserve the original event. -/
inductive CircuitChunk : List Semantics.Raw.Event → List (List Semantics.Finite.Step) → Prop where
  | empty : CircuitChunk [] []
  | gates (bits : Nat) (steps : List Semantics.Finite.Step) : CircuitChunk [.circuit bits steps] [steps]

/-- Consecutive occurrences in the original Raw root, retaining each
intermediate owner frame and the actual gate-event order. -/
inductive CircuitSpan (original : Array Semantics.Observation.Op) (start : Nat) (frame : List Nat) :
    List Nat → Interface → Interface → List Semantics.Raw.Event → List (List Semantics.Finite.Step) → Prop where
  | empty (state : Interface) : CircuitSpan original start frame [] state state [] []
  | cons {offset : Nat} {offsets : List Nat} {initial middle final : Interface}
      {operation : Semantics.Raw.Op} {events later : List Semantics.Raw.Event}
      {added chunks : List (List Semantics.Finite.Step)}
      (source : original[start+offset]? = some (.pure operation))
      (step : Semantics.RawTrace.step initial operation = some (middle,events))
      (sameFrame : middle.frame = frame) (chunk : CircuitChunk events added)
      (tail : CircuitSpan original start frame offsets middle final later chunks) :
      CircuitSpan original start frame (offset :: offsets) initial final (events ++ later) (added ++ chunks)

private theorem readSpanStep_success {original : Array Semantics.Observation.Op} {state : State}
    {input output : Interface × List (List Semantics.Finite.Step) × Nat} {offset work left : Nat}
    (ok : (readSpanStep original state input offset).run work = (.ok output,left)) :
    ∃ operation events added,
      original[state.rawIndex+offset]? = some (.pure operation) ∧
      Semantics.RawTrace.step input.1 operation = some (output.1,events) ∧
      output.1.frame = state.raw.frame ∧ CircuitChunk events added ∧
      output.2.1.reverse = input.2.1.reverse ++ added := by
  rcases input with ⟨frame,chunks,size⟩
  dsimp only [readSpanStep] at ok
  split at ok
  · rename_i operation source
    obtain ⟨_,_,_,afterFields⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨_,_,_,afterCharge⟩ := bind_success _ _ _ _ _ afterFields
    obtain ⟨⟨next,events⟩,_,raw,afterRaw⟩ := bind_success _ _ _ _ _ afterCharge
    have read := readOption_success (lift_success _ _ _ _ raw).1
    obtain ⟨_,_,same,afterFrame⟩ := bind_success _ _ _ _ _ afterRaw
    have sameFrame : next.frame = state.raw.frame := by
      exact eq_of_beq (guard_success _ _ _ _ same).1
    cases events with
    | nil =>
      obtain ⟨rfl,_⟩ := pure_success _ _ _ _ afterFrame
      exact ⟨operation,[],[],source,read,sameFrame,.empty,by simp⟩
    | cons event rest =>
      cases rest with
      | cons _ _ => cases event <;> cases afterFrame
      | nil =>
        cases event with
        | circuit bits steps =>
          obtain ⟨_,_,_,done⟩ := bind_success _ _ _ _ _ afterFrame
          obtain ⟨rfl,_⟩ := pure_success _ _ _ _ done
          exact ⟨operation,[.circuit bits steps],[steps],source,read,sameFrame,.gates _ _,by simp⟩
        | init0 | liftBasis | reorder | computed | protectedComputed | structuralComputed => cases afterFrame
  · cases ok

private theorem readSpan_fold {original : Array Semantics.Observation.Op} {state : State}
    (offsets : List Nat) {input output : Interface × List (List Semantics.Finite.Step) × Nat} {work left : Nat}
    (ok : (offsets.foldlM (readSpanStep original state) input).run work = (.ok output,left)) :
    ∃ events chunks,
      CircuitSpan original state.rawIndex state.raw.frame offsets input.1 output.1 events chunks ∧
      output.2.1.reverse = input.2.1.reverse ++ chunks := by
  induction offsets generalizing input work with
  | nil =>
    obtain ⟨rfl,_⟩ := pure_success _ _ _ _ ok
    exact ⟨[],[],.empty _,by simp⟩
  | cons offset rest ih =>
    obtain ⟨middle,_,head,tail⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨operation,events,added,source,step,sameFrame,chunk,prepend⟩ := readSpanStep_success head
    obtain ⟨later,chunks,trace,remaining⟩ := ih tail
    exact ⟨events++later,added++chunks,.cons source step sameFrame chunk trace,
      by rw [remaining,prepend,List.append_assoc]⟩

/-- The actions supplied to optimized placement are exactly the ordered
flattening of the actual original circuit events. Zero-event ownership
operations still advance their original interfaces. -/
theorem readSpan_trace {original : Array Semantics.Observation.Op} {state : State}
    {count : Nat} {final : Interface} {steps : List Semantics.Finite.Step}
    (computed : RuntimeInterval.Computed (readSpan original state count) (final,steps)) :
    ∃ events chunks,
      CircuitSpan original state.rawIndex state.raw.frame (List.range count) state.raw final events chunks ∧
      steps = chunks.flatten := by
  obtain ⟨work,left,ok⟩ := computed
  unfold readSpan at ok
  obtain ⟨_,_,_,afterCount⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨⟨next,reverseChunks,size⟩,_,folded,finish⟩ := bind_success _ _ _ _ _ afterCount
  obtain ⟨equal,_⟩ := pure_success _ _ _ _ finish
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
  obtain ⟨events,chunks,trace,ordered⟩ := readSpan_fold _ folded
  simp only [List.reverse_nil,List.nil_append] at ordered
  exact ⟨events,chunks,trace,congrArg List.flatten ordered⟩

#print axioms readSpan_trace

private theorem followWorkspace_fold_state (operations : List Semantics.Raw.Op) (initial : Semantics.RawTrace.Prepared) :
    (operations.foldlM Semantics.RawTrace.advance initial).map Semantics.RawTrace.Prepared.state =
      followWorkspace initial.state operations := by
  induction operations generalizing initial with
  | nil => rfl
  | cons first rest ih =>
    have unfoldFollow : followWorkspace initial.state (first :: rest) =
        (Semantics.RawTrace.step initial.state first).map Prod.fst >>= fun middle => followWorkspace middle rest := rfl
    rw [unfoldFollow]
    cases read : Semantics.RawTrace.step initial.state first with
    | none => simp [List.foldlM_cons,Semantics.RawTrace.advance,read,bind,Option.bind]
    | some packet =>
      obtain ⟨middle,events⟩ := packet
      simpa [List.foldlM_cons,Semantics.RawTrace.advance,read,bind,Option.bind] using
        ih {initial with state := middle,events := initial.events ++ events}

/-- A successful bound workspace retains the exact Raw interval in the root,
its independently re-read event list, and the actual returned owner frame. -/
theorem BoundSegment.original_workspace_trace {program : Semantics.Observation.Program} {segment : Segment program}
    {bytes capacity} {target : CanonicalOpenQasmResources.Checked bytes capacity}
    {rootDependencies connected reserved previous entry}
    (bound : BoundSegment segment rootDependencies target connected reserved previous entry) :
    ((program.operations.drop entry.rawIndex).take segment.length =
        segment.literal.operations.map Semantics.Observation.Op.pure) ∧
    ∃ traced,
      Semantics.RawTrace.interval entry.raw segment.literal.operations = some traced ∧
      traced.state = bound.after ∧ traced.state.frame = entry.raw.frame := by
  refine ⟨?_,?_⟩
  · rw [bound.offset]
    exact segment.literalRoot.trans segment.literal.originalOperations
  · have linked := followWorkspace_fold_state segment.literal.operations
      ⟨entry.raw,[],entry.raw.frame.length⟩
    change (Semantics.RawTrace.interval entry.raw segment.literal.operations).map Semantics.RawTrace.Prepared.state =
      followWorkspace entry.raw segment.literal.operations at linked
    rw [bound.continued] at linked
    cases observed : Semantics.RawTrace.interval entry.raw segment.literal.operations with
    | none => simp [observed] at linked
    | some traced =>
      have frame : traced.state = bound.after := by simpa [observed] using linked
      exact ⟨traced,rfl,frame,frame ▸ bound.sameWires⟩

/-- The start and end coordinates used to compose the workspace on the
original replay. Carry the actual source continuation and literal gate count. -/
theorem BoundSegment.exit_coordinates {program : Semantics.Observation.Program} {segment : Segment program}
    {bytes capacity} {target : CanonicalOpenQasmResources.Checked bytes capacity}
    {rootDependencies connected reserved previous entry}
    (bound : BoundSegment segment rootDependencies target connected reserved previous entry) :
    (segment.exit entry bound.after).raw = bound.after ∧
    (segment.exit entry bound.after).locations = entry.locations ∧
    (segment.exit entry bound.after).rawIndex = entry.rawIndex+segment.length ∧
    (segment.exit entry bound.after).gateIndex = entry.gateIndex+
      ((target.circuit.gates.drop entry.gateIndex).take segment.count).length := by
  have inside := (CanonicalOpenQasmWorkspace.interval_length bound.placed.body.actualInterval).2
  change entry.gateIndex+segment.count ≤ target.circuit.gates.length at inside
  have length : ((target.circuit.gates.drop entry.gateIndex).take segment.count).length = segment.count := by
    simp only [List.length_take,List.length_drop]
    omega
  simp [Segment.exit,bound.offset,length]

#print axioms BoundSegment.original_workspace_trace
#print axioms BoundSegment.exit_coordinates

/-- The accepted clean packet reads the actual single `certifiedCompute`.
The zero table and the original action fields are retained verbatim. -/
theorem clean_packet_source {bits data scratch operations emitted work left}
    (checked : (RuntimeWorkspace.packet true bits data scratch operations).run work = (.ok emitted,left)) :
    ∃ wire logical, scratch = none ∧ emitted.logicalSteps = some logical ∧
      operations = [.pure (.certifiedCompute data emitted.dataOut [wire] (List.replicate (2^bits) 0) emitted.steps logical)] := by
  unfold RuntimeWorkspace.packet at checked
  split at checked
  · rename_i input output wire table steps logical _
    obtain ⟨_,_,guarded,finish⟩ := bind_success _ _ _ _ _ checked
    have authorized := (guard_success _ _ _ _ guarded).1
    simp only [Bool.and_eq_true,beq_iff_eq] at authorized
    obtain ⟨rfl,rfl⟩ := authorized
    obtain ⟨rfl,_⟩ := pure_success _ _ _ _ finish
    exact ⟨wire,logical,rfl,rfl,rfl⟩
  · contradiction
  · cases checked


/-- The accepted dirty packet uses the original data and scratch, joins
before the ordered gate word, and splits the same packed output. -/
theorem dirty_packet_source {bits data scratch operations emitted work left}
    (checked : (RuntimeWorkspace.packet false bits data scratch operations).run work = (.ok emitted,left)) :
    ∃ auxiliary joined packed returned, scratch = some auxiliary ∧ emitted.scratchOut = some returned ∧
      operations = [.pure (.join data auxiliary joined),.pure (.applyUnitary joined packed emitted.steps),
        .pure (.split packed emitted.dataOut returned bits)] := by
  unfold RuntimeWorkspace.packet at checked
  split at checked
  · contradiction
  · rename_i requested input auxiliary joined applied packed steps split output returned leftBits _
    obtain ⟨_,_,guarded,finish⟩ := bind_success _ _ _ _ _ checked
    have authorized := (guard_success _ _ _ _ guarded).1
    simp only [Bool.and_eq_true,beq_iff_eq] at authorized
    obtain ⟨⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩ := authorized
    obtain ⟨rfl,_⟩ := pure_success _ _ _ _ finish
    exact ⟨_,_,_,_,rfl,rfl,rfl⟩
  · cases checked

#print axioms clean_packet_source
#print axioms dirty_packet_source

/-- The segments stored by the actual placement trace, in source visit order. -/
inductive WorkspaceTrace.RecordsSegments {program : Semantics.Observation.Program} {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity} {rootDependencies connected reserved synthesis} :
    {state : State} → {uses : CleanUses target.circuit} → {peak : Nat} →
    WorkspaceTrace (program := program) rootDependencies target connected reserved synthesis state uses peak →
    List (Segment program) → Prop where
  | start : RecordsSegments .start []
  | next {previous entry : State} {segment : Segment program} {uses : CleanUses target.circuit} {peak : Nat}
      {earlier : WorkspaceTrace (program := program) rootDependencies target connected reserved synthesis previous uses peak}
      {segments : List (Segment program)}
      (bound : BoundSegment segment rootDependencies target connected reserved previous entry)
      (recorded : RecordsSegments earlier segments) :
      RecordsSegments (.next earlier bound) (segments ++ [segment])

private theorem recordWorkspace_segments {program : Semantics.Observation.Program} {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity} {rootDependencies connected reserved synthesis}
    (segments : List (Segment program))
    {initial final : @TraceWithUses program bytes capacity rootDependencies target connected reserved synthesis}
    {work left : Nat} {prior : List (Segment program)}
    (priorRecorded : initial.trace.RecordsSegments prior)
    (ok : (segments.foldlM recordWorkspace initial).run work = (.ok final,left)) :
    final.trace.RecordsSegments (prior ++ segments) := by
  induction segments generalizing initial work prior with
  | nil =>
    obtain ⟨rfl,_⟩ := pure_success _ _ _ _ ok
    simpa using priorRecorded
  | cons segment rest ih =>
    obtain ⟨middle,_,first,tail⟩ := bind_success _ _ _ _ _ ok
    have recorded : middle.trace.RecordsSegments (prior ++ [segment]) := by
      unfold recordWorkspace at first
      obtain ⟨⟨entry,bound⟩,_,_,finished⟩ := bind_success _ _ _ _ _ first
      obtain ⟨rfl,_⟩ := pure_success _ _ _ _ finished
      exact .next bound priorRecorded
    simpa only [List.append_assoc,List.singleton_append] using ih recorded tail

/-- The returned trace contains exactly the ordered workspace spans passed to
its executable fold. Every span retains the real bound source and placement. -/
theorem finishTrace_segments {bytes capacity} {target : CanonicalOpenQasmResources.Checked bytes capacity}
    {program connected reserved synthesis rootDependencies segments suffix work left}
    {trace : FinishedTrace program rootDependencies target connected reserved synthesis suffix}
    (checked : (finishTrace target program connected reserved segments suffix synthesis rootDependencies).run work =
      (.ok trace,left)) : trace.recorded.trace.RecordsSegments segments := by
  unfold finishTrace at checked
  obtain ⟨_,_,_,limited⟩ := bind_success _ _ _ _ _ checked
  obtain ⟨_,_,_,charged⟩ := bind_success _ _ _ _ _ limited
  split at charged
  · split at charged
    · obtain ⟨recorded,_,folded,continued⟩ := bind_success _ _ _ _ _ charged
      obtain ⟨_,_,_,prefixWork⟩ := bind_success _ _ _ _ _ continued
      obtain ⟨_,_,_,replayed⟩ := bind_success _ _ _ _ _ prefixWork
      obtain ⟨_,_,_,readout⟩ := bind_success _ _ _ _ _ replayed
      obtain ⟨_,_,_,checkedUses⟩ := bind_success _ _ _ _ _ readout
      obtain ⟨_,_,_,finish⟩ := bind_success _ _ _ _ _ checkedUses
      split at finish
      · obtain ⟨rfl,_⟩ := pure_success _ _ _ _ finish
        simpa using recordWorkspace_segments segments .start folded
      · cases finish
    · cases charged
  · cases charged

#print axioms finishTrace_segments

/-- The terminal checker retains the original frame coordinates while it
consumes owners. Measured identifiers are bound to actual physical wires. -/
inductive ReadoutStep (frame locations : List Nat) :
    (Interface × List (Nat × Nat)) → Semantics.Observation.Op → (Interface × List (Nat × Nat)) → Prop where
  | measure {state next : Interface} {measured : List (Nat × Nat)} {input output wire location : Nat}
      {port : Semantics.Raw.Port}
      (consume : Semantics.RawTrace.take state input = some (port,next))
      (single : port.wires = [wire])
      (placed : CanonicalOpenQasmWorkspace.placedWires frame locations [wire] = some [location])
      (fresh : measured.any (fun pair => pair.1 == output || pair.2 == location) = false) :
      ReadoutStep frame locations (state,measured) (.measure input output) (next,(output,location) :: measured)
  | discard {state next : Interface} {measured : List (Nat × Nat)} {input : Nat} {port : Semantics.Raw.Port}
      (consume : Semantics.RawTrace.take state input = some (port,next)) :
      ReadoutStep frame locations (state,measured) (.discard input) (next,measured)
  | structural {state next : Interface} {measured : List (Nat × Nat)} {operation : Semantics.Raw.Op}
      (transition : Semantics.RawTrace.step state operation = some (next,[])) :
      ReadoutStep frame locations (state,measured) (.pure operation) (next,measured)

inductive ReadoutTrace (frame locations : List Nat) :
    (Interface × List (Nat × Nat)) → List Semantics.Observation.Op → (Interface × List (Nat × Nat)) → Prop where
  | empty (state : Interface × List (Nat × Nat)) : ReadoutTrace frame locations state [] state
  | cons {before middle final : Interface × List (Nat × Nat)} {operation : Semantics.Observation.Op}
      {rest : List Semantics.Observation.Op}
      (step : ReadoutStep frame locations before operation middle)
      (tail : ReadoutTrace frame locations middle rest final) :
      ReadoutTrace frame locations before (operation :: rest) final

private theorem readout_structural {frame locations state measured operation result}
    (ok : (do
      let (next,[]) ← Semantics.RawTrace.step state operation | none
      some (next,measured)) = some result) :
    ReadoutStep frame locations (state,measured) (.pure operation) result := by
  cases read : Semantics.RawTrace.step state operation with
  | none => simp [read,bind,Option.bind] at ok
  | some transition =>
    obtain ⟨next,events⟩ := transition
    cases events with
    | nil =>
      have same : (next,measured) = result := by simpa [read,bind,Option.bind] using ok
      subst result
      exact .structural read
    | cons _ _ => simp [read,bind,Option.bind] at ok

private theorem readoutStep_success {frame : Interface} {locations : List Nat}
    {before after : Interface × List (Nat × Nat)} {operation : Semantics.Observation.Op}
    (ok : readoutStep frame locations before operation = some after) :
    ReadoutStep frame.frame locations before operation after := by
  obtain ⟨state,measured⟩ := before
  cases operation with
  | measure input output =>
    cases consumed : Semantics.RawTrace.take state input with
    | none => simp [readoutStep,consumed,bind,Option.bind] at ok
    | some taken =>
      obtain ⟨port,next⟩ := taken
      cases single : port.wires with
      | nil => simp [readoutStep,consumed,single,bind,Option.bind] at ok
      | cons wire extra =>
        cases extra with
        | cons _ _ => simp [readoutStep,consumed,single,bind,Option.bind] at ok
        | nil =>
          cases placed : CanonicalOpenQasmWorkspace.placedWires frame.frame locations [wire] with
          | none => simp [readoutStep,consumed,single,placed,bind,Option.bind] at ok
          | some wires =>
            cases wires with
            | nil => simp [readoutStep,consumed,single,placed,bind,Option.bind] at ok
            | cons location extra =>
              cases extra with
              | cons _ _ => simp [readoutStep,consumed,single,placed,bind,Option.bind] at ok
              | nil =>
                by_cases fresh : measured.any (fun pair => pair.1 == output || pair.2 == location) = false
                · have same : (next,(output,location) :: measured) = after := by
                    simpa [readoutStep,consumed,single,placed,bind,Option.bind,fresh] using ok
                  subst after
                  exact .measure consumed single placed fresh
                · have seen : measured.any (fun pair => pair.1 == output || pair.2 == location) = true := by
                    cases seen : measured.any (fun pair => pair.1 == output || pair.2 == location) with
                    | false => exact False.elim (fresh seen)
                    | true => rfl
                  simp [readoutStep,consumed,single,placed,bind,Option.bind,seen] at ok
  | discard input =>
    cases consumed : Semantics.RawTrace.take state input with
    | none => simp [readoutStep,consumed,bind,Option.bind] at ok
    | some taken =>
      obtain ⟨port,next⟩ := taken
      have same : (next,measured) = after := by simpa [readoutStep,consumed,bind,Option.bind] using ok
      subst after
      exact .discard consumed
  | pure operation =>
    cases operation <;> first | exact readout_structural ok | cases ok
  | reset _ _ _ | constant _ _ | not _ _ | xor _ _ _ | and _ _ _ | branch _ _ _ _ _ => cases ok

private theorem followObservation_trace {frame : Interface} {locations : List Nat}
    (operations : List Semantics.Observation.Op) {initial final : Interface × List (Nat × Nat)}
    (ok : operations.foldlM (readoutStep frame locations) initial = some final) :
    ReadoutTrace frame.frame locations initial operations final := by
  induction operations generalizing initial with
  | nil => cases ok; exact .empty _
  | cons operation rest ih =>
    cases read : readoutStep frame locations initial operation with
    | none => simp [List.foldlM_cons,read,bind,Option.bind] at ok
    | some middle =>
      have tail : rest.foldlM (readoutStep frame locations) middle = some final := by
        simpa [List.foldlM_cons,read,bind,Option.bind] using ok
      exact .cons (readoutStep_success read) (ih tail)

/-- Every measured SSA identifier and physical coordinate is unique throughout
an accepted terminal trace. Discard and structural ownership changes leave
that association intact. -/
theorem ReadoutTrace.unique_measurements {frame locations before operations final}
    (trace : ReadoutTrace frame locations before operations final)
    (initial : (before.2.map Prod.fst).Nodup ∧ (before.2.map Prod.snd).Nodup) :
    (final.2.map Prod.fst).Nodup ∧ (final.2.map Prod.snd).Nodup := by
  induction trace with
  | empty _ => exact initial
  | cons head _ ih =>
    apply ih
    cases head with
    | @measure _ _ measured _ output _ wire _ _ _ _ fresh =>
      have excludes (entry : Nat × Nat) (member : entry ∈ measured) : entry.1 ≠ output ∧ entry.2 ≠ wire := by
        have no : (entry.1 == output || entry.2 == wire) = false := by
          cases matched : (entry.1 == output || entry.2 == wire) with
          | false => rfl
          | true =>
            have duplicate : measured.any (fun pair => pair.1 == output || pair.2 == wire) = true :=
              List.any_eq_true.mpr ⟨entry,member,matched⟩
            rw [duplicate] at fresh
            cases fresh
        exact ⟨fun equal => by simp [equal] at no,fun equal => by simp [equal] at no⟩
      have absentId : output ∉ measured.map Prod.fst := by
        intro duplicate
        obtain ⟨entry,member,equal⟩ := List.mem_map.mp duplicate
        exact (excludes entry member).1 equal
      have absentWire : wire ∉ measured.map Prod.snd := by
        intro duplicate
        obtain ⟨entry,member,equal⟩ := List.mem_map.mp duplicate
        exact (excludes entry member).2 equal
      exact ⟨List.nodup_cons.mpr ⟨absentId,initial.1⟩,List.nodup_cons.mpr ⟨absentWire,initial.2⟩⟩
    | discard _ | structural _ => exact initial

private theorem lookup_terminal_output {measured : List (Nat × Nat)} {results measurements : List Nat}
    (read : results.mapM (fun id => (measured.find? (fun pair => pair.1 == id)).map (·.2)) = some measurements) :
    measurements.length = results.length ∧
    ∀ index id : Nat, results[index]? = some id →
      ∃ wire, measurements[index]? = some wire ∧ (id,wire) ∈ measured := by
  induction results generalizing measurements with
  | nil => cases read; simp
  | cons result rest ih =>
    cases found : measured.find? (fun pair => pair.1 == result) with
    | none => simp [List.mapM_cons,found,bind,Option.bind] at read
    | some entry =>
      cases remaining : rest.mapM (fun id => (measured.find? (fun pair => pair.1 == id)).map (·.2)) with
      | none => simp [List.mapM_cons,found,remaining,bind,Option.bind] at read
      | some tail =>
        have same : entry.2 :: tail = measurements := by
          simpa [List.mapM_cons,found,remaining,bind,Option.bind] using read
        subst measurements
        refine ⟨by simp [(ih remaining).1],?_⟩
        intro index id named
        cases index with
        | zero =>
          have equal : result = id := by simpa using named
          have boundId : entry.1 = result := by simpa using List.find?_some found
          have member := List.mem_of_find?_eq_some found
          exact ⟨entry.2,rfl,by simpa only [← equal,← boundId,Prod.eta] using member⟩
        | succ index => exact (ih remaining).2 index id named

/-- Whole terminal acceptance binds each public classical result in written
order to the measured wire in the actual decoded circuit. The original
terminal suffix is consumed once and no quantum owner remains. -/
theorem Readout.original_trace {bytes capacity} {target : CanonicalOpenQasmResources.Checked bytes capacity}
    {program : Semantics.Observation.Program} {state : State} (checked : Readout target program state) :
    program.outputs = [] ∧ state.rawIndex ≤ program.operations.length ∧
      ∃ finished measured,
        ReadoutTrace state.raw.frame state.locations (state.raw,[]) (program.operations.drop state.rawIndex) (finished,measured) ∧
        finished.live = [] ∧ program.classicalOutputs.Nodup ∧
        (measured.map Prod.fst).Nodup ∧ (measured.map Prod.snd).Nodup ∧
        target.circuit.measurements.length = program.classicalOutputs.length ∧
        (∀ index id : Nat, program.classicalOutputs[index]? = some id →
          ∃ wire, target.circuit.measurements[index]? = some wire ∧ (id,wire) ∈ measured) := by
  have accepted := checked.original
  unfold readout at accepted
  split at accepted
  · cases accepted
  · rename_i header
    have bound : program.outputs = [] ∧ state.rawIndex ≤ program.operations.length := by
      simpa [Bool.or_eq_true] using header
    refine ⟨bound.1,bound.2,?_⟩
    cases followed : followObservation state.raw state.locations (program.operations.drop state.rawIndex) with
    | none => simp [followed,bind,Option.bind] at accepted
    | some pair =>
      obtain ⟨finished,measured⟩ := pair
      simp only [followed,bind,Option.bind] at accepted
      split at accepted
      · cases accepted
      · rename_i exhausted
        have done : finished.live = [] ∧ program.classicalOutputs.Nodup := by
          simpa [Bool.or_eq_true] using exhausted
        have trace := followObservation_trace _ followed
        have fresh := trace.unique_measurements (by simp)
        exact ⟨finished,measured,trace,done.1,done.2,fresh.1,fresh.2,lookup_terminal_output accepted⟩

#print axioms Readout.original_trace

/-- An emitted result can be traced through the original successful suffix
to its actual measurement and owner consumption. -/
inductive ReadoutOccurrence (frame locations : List Nat) (id location : Nat) :
    (Interface × List (Nat × Nat)) → List Semantics.Observation.Op → Prop where
  | first {state next : Interface} {earlier : List (Nat × Nat)} {input : Nat}
      {rest : List Semantics.Observation.Op}
      (measurement : ReadoutStep frame locations (state,earlier) (.measure input id) (next,(id,location) :: earlier)) :
      ReadoutOccurrence frame locations id location (state,earlier) (.measure input id :: rest)
  | later {before middle : Interface × List (Nat × Nat)} {first : Semantics.Observation.Op}
      {rest : List Semantics.Observation.Op}
      (advance : ReadoutStep frame locations before first middle)
      (measurement : ReadoutOccurrence frame locations id location middle rest) :
      ReadoutOccurrence frame locations id location before (first :: rest)

private theorem ReadoutTrace.measured_occurrence {frame locations initial final operations id location}
    (trace : ReadoutTrace frame locations initial operations final) (member : (id,location) ∈ final.2) :
    (id,location) ∈ initial.2 ∨ ReadoutOccurrence frame locations id location initial operations := by
  induction trace with
  | empty _ => exact .inl member
  | cons step _ ih =>
    rcases ih member with prior | occurrence
    · cases step with
      | @measure _ _ _ _ output _ wire _ consume single placed fresh =>
        rcases List.mem_cons.mp prior with eq | earlier
        · obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
          exact .inr (.first (.measure consume single placed fresh))
        · exact .inl earlier
      | discard _ | structural _ => exact .inl prior
    · exact .inr (.later step occurrence)

/-- Each public result position names the wire of a concrete original
measurement in the accepted Raw suffix. -/
theorem Readout.measured_at {bytes capacity} {target : CanonicalOpenQasmResources.Checked bytes capacity}
    {program : Semantics.Observation.Program} {state : State} (checked : Readout target program state)
    {index id : Nat} (output : program.classicalOutputs[index]? = some id) :
    ∃ location, target.circuit.measurements[index]? = some location ∧
      ReadoutOccurrence state.raw.frame state.locations id location (state.raw,[]) (program.operations.drop state.rawIndex) := by
  obtain ⟨_,_,_,_,trace,_,_,_,_,_,read⟩ := checked.original_trace
  obtain ⟨wire,named,member⟩ := read index id output
  exact ⟨wire,named,(trace.measured_occurrence member).resolve_left (by simp)⟩

#print axioms Readout.measured_at

private theorem placed_readout_wire {frame locations : List Nat} {wire location : Nat}
    (placed : CanonicalOpenQasmWorkspace.placedWires frame locations [wire] = some [location]) :
    wire ∈ frame ∧ locations[frame.idxOf wire]? = some location := by
  by_cases present : wire ∈ frame
  · refine ⟨present,?_⟩
    cases found : locations[frame.idxOf wire]? with
    | none => simp [CanonicalOpenQasmWorkspace.placedWires,present,found,List.mapM_cons,bind,Option.bind] at placed
    | some actual =>
      have same : actual = location := by
        simpa [CanonicalOpenQasmWorkspace.placedWires,present,found,List.mapM_cons,bind,Option.bind] using placed
      rw [same]
  · simp [CanonicalOpenQasmWorkspace.placedWires,present,List.mapM_cons,bind,Option.bind] at placed

/-- The measurement selected by the decoded terminal output reads exactly
its original Raw bit in the ordered live-frame basis, for every basis label. -/
theorem ReadoutOccurrence.source_coordinate {frame locations start operations id location}
    (occurrence : ReadoutOccurrence frame locations id location start operations) :
    ∃ wire ∈ frame, locations[frame.idxOf wire]? = some location ∧
      ∀ row : Nat, Semantics.Finite.bit (Semantics.Finite.gather row locations) (frame.idxOf wire) =
        Semantics.Finite.bit row location := by
  induction occurrence with
  | first measurement =>
    cases measurement with
    | @measure _ _ _ _ _ wire _ _ _ _ placed _ =>
      obtain ⟨member,physical⟩ := placed_readout_wire placed
      obtain ⟨inside,equal⟩ := List.getElem?_eq_some_iff.mp physical
      refine ⟨wire,member,physical,?_⟩
      intro row
      have bit := RuntimeScatterTransport.gather_at row locations (frame.idxOf wire) inside
      rw [equal] at bit
      exact bit
  | later _ _ ih => exact ih

#print axioms ReadoutOccurrence.source_coordinate

/-- The public bit at the accepted output position is the same evaluation
of the same original measurement, under the checked layout. -/
theorem Readout.measured_axis {bytes capacity} {target : CanonicalOpenQasmResources.Checked bytes capacity}
    {program : Semantics.Observation.Program} {state : State} (checked : Readout target program state)
    {index id : Nat} (output : program.classicalOutputs[index]? = some id) :
    ∃ location, target.circuit.measurements[index]? = some location ∧
      ReadoutOccurrence state.raw.frame state.locations id location (state.raw,[]) (program.operations.drop state.rawIndex) ∧
      ∃ wire ∈ state.raw.frame, state.locations[state.raw.frame.idxOf wire]? = some location ∧
        ∀ row : Nat, Semantics.Finite.bit (Semantics.Finite.gather row state.locations) (state.raw.frame.idxOf wire) =
          Semantics.Finite.bit row location := by
  obtain ⟨location,atPosition,occurrence⟩ := checked.measured_at output
  exact ⟨location,atPosition,occurrence,occurrence.source_coordinate⟩

#print axioms Readout.measured_axis

/-- Read the complete terminal result in the original SSA order. Each
physical wire has already been tied to the corresponding Raw measurement. -/
theorem Readout.measurement_word {bytes capacity} {target : CanonicalOpenQasmResources.Checked bytes capacity}
    {program : Semantics.Observation.Program} {state : State} (checked : Readout target program state)
    (unique : state.locations.Nodup) (row : Nat) :
    target.circuit.measurements.map (Semantics.Finite.bit row) =
      (target.circuit.measurements.map state.locations.idxOf).map
        (Semantics.Finite.bit (Semantics.Finite.gather row state.locations)) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,sameLength,_⟩ := checked.original_trace
  rw [List.map_map]
  apply List.map_congr_left
  intro physical member
  obtain ⟨index,inside,same⟩ := List.getElem_of_mem member
  have sourceIndex : index < program.classicalOutputs.length := sameLength ▸ inside
  obtain ⟨location,emitted,_,wire,_,lookup,bits⟩ := checked.measured_axis (List.getElem?_eq_getElem sourceIndex)
  have actual : physical = location := by
    rw [List.getElem?_eq_getElem inside,same] at emitted
    exact Option.some.inj emitted
  have located := List.mem_of_getElem? lookup
  have locatedOnce := RuntimeNamedFrameAxes.wireLookup state.locations located
  have recovered : state.locations.idxOf location = state.raw.frame.idxOf wire :=
    (List.getElem?_inj (List.idxOf_lt_length_of_mem located) unique).mp (locatedOnce.trans lookup.symm)
  rw [actual]
  change Semantics.Finite.bit row location =
    Semantics.Finite.bit (Semantics.Finite.gather row state.locations) (state.locations.idxOf location)
  rw [recovered,bits]

#print axioms Readout.measurement_word

end QleisliKernel.Target.CanonicalOpenQasmPlacement
