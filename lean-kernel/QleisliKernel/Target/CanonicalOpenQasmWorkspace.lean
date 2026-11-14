import QleisliKernel.Target.CanonicalOpenQasmResources
import QleisliKernel.Qirf.RuntimeWorkspace

/-! Compare a designated gate interval of the decoded target with the checked
source workspace operator. Check access to clean scratch before, between and
after the selected intervals. The caller supplies the data-owner placement.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Target.CanonicalOpenQasmWorkspace
open Finite Qirf
open CanonicalOpenQasmResources (Circuit Instruction)

def interval (circuit : Circuit) (layout : List Nat) (start count : Nat) :
    Option (List Semantics.Finite.Step) :=
  if start+count ≤ circuit.gates.length then
    ((circuit.gates.drop start).take count).mapM (Instruction.localStep layout)
  else none

/-- Bind the target word to the independently proved raw workspace interval.
The layout is ordered data then scratch, in the original source interface
order. Every target operand stays in that layout. -/
structure Checked {sources caller dependencies program block sourceStart sourceCount event events original
    sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller dependencies program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    (map : RuntimeWorkspace.CallerMap literal) {bytes capacity}
    (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (layout : List Nat) (start count : Nat) where
  declared : target.circuit.declares layout
  shape : layout.length = original.layout.bits + 1
  coversRawPeak : map.resources.counts.peakWires ≤ target.circuit.qubits
  gates : List Semantics.Finite.Step
  actualInterval : interval target.circuit layout start count = some gates
  equation : RuntimeWorkspace.Equation original dependencies gates

def check {sources caller dependencies program block sourceStart sourceCount event events original
    sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller dependencies program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    (map : RuntimeWorkspace.CallerMap literal) {bytes capacity}
    (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (layout : List Nat) (start count : Nat) : WorkM (Checked map target layout start count) := do
  guard (layout.length ≤ 6 && start+count ≤ target.circuit.gates.length) .limit
  exactWork (Exact.charge (64*(1+start+count)*(1+layout.length)))
  if placement : target.circuit.declares layout ∧
      layout.length = original.layout.bits+1 ∧ map.resources.counts.peakWires ≤ target.circuit.qubits then
    match actual : interval target.circuit layout start count with
    | none => throw .request
    | some gates =>
      let equation ← RuntimeWorkspace.checkSteps original dependencies gates
      return ⟨placement.1,placement.2.1,placement.2.2,gates,actual,equation⟩
  else throw .request

theorem Checked.sourceOperator {sources caller dependencies program block sourceStart sourceCount event events
    original sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller dependencies program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    {map : RuntimeWorkspace.CallerMap literal} {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity} {layout start count}
    (checked : Checked map target layout start count) :
    checked.equation.actual = original.body.matrix :=
  checked.equation.originalBody

/-- The encoding associates the original Raw frame, in its actual wire order,
with distinct reserved target locations. Unselected locations, including
spectator ports and their correlations, stay outside the local gate word. -/
def placedWires (rawFrame targetFrame wires : List Nat) : Option (List Nat) :=
  wires.mapM fun wire => do
    if rawFrame.contains wire then targetFrame[rawFrame.idxOf wire]? else none

structure Placed {sources caller dependencies program block sourceStart sourceCount event events original
    sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller dependencies program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    (map : RuntimeWorkspace.CallerMap literal) {bytes capacity}
    (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (targetFrame : List Nat) (start count : Nat) where
  full : targetFrame.length = sourceInterval.before.quantum.reference.frame.length
  declared : target.circuit.declares targetFrame
  liveLayout : List Nat
  boundOwners : placedWires sourceInterval.before.quantum.reference.frame targetFrame
    (map.selected.flatMap (·.port.wires)) = some liveLayout
  freshScratch : Option Nat
  scratchMode : freshScratch.isSome = event.fresh
  scratchFree : ∀ location ∈ freshScratch.toList, location ∉ targetFrame
  body : Checked map target (liveLayout ++ freshScratch.toList) start count

def checkPlacement {sources caller dependencies program block sourceStart sourceCount event events original
    sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller dependencies program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    (map : RuntimeWorkspace.CallerMap literal) {bytes capacity}
    (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (targetFrame : List Nat) (start count : Nat) (scratch : Option Nat) :
    WorkM (Placed map target targetFrame start count) := do
  let rawFrame := sourceInterval.before.quantum.reference.frame
  let wires := map.selected.flatMap (·.port.wires)
  guard (rawFrame.length ≤ 12 && targetFrame.length ≤ 12 && wires.length ≤ 12) .limit
  exactWork (Exact.charge (32*(1+wires.length)*(1+rawFrame.length+targetFrame.length)))
  if valid : targetFrame.length = rawFrame.length ∧ target.circuit.declares targetFrame ∧
      scratch.isSome = event.fresh ∧ (∀ location ∈ scratch.toList, location ∉ targetFrame) then
    match read : placedWires rawFrame targetFrame wires with
    | none => throw .request
    | some layout =>
      let body ← check map target (layout ++ scratch.toList) start count
      return ⟨valid.1,valid.2.1,layout,read,scratch,valid.2.2.1,valid.2.2.2,body⟩
  else throw .request

/-- The declaration reserves and resets the entire target register. The two
prefix/suffix restrictions give a sufficient static lifetime condition for a
fresh scratch axis: zero at entry and unused after exact restoration. Dirty
scratch is already live and may continue to participate after the interval. -/
def lifetimes (circuit : Circuit) (fresh : Bool) (layout : List Nat) (start count : Nat) : Bool :=
  match layout.getLast? with
  | none => false
  | some scratch =>
    if fresh then
      let outside := circuit.gates.take start ++ circuit.gates.drop (start+count)
      !(circuit.measurements.contains scratch) && outside.all (fun gate => !gate.wires.contains scratch)
    else true

theorem freshScratchUntouched (circuit : Circuit) (layout : List Nat) (start count scratch : Nat)
    (last : layout.getLast? = some scratch)
    (checked : lifetimes circuit true layout start count = true) :
    scratch ∉ circuit.measurements ∧
      ∀ gate ∈ circuit.gates.take start ++ circuit.gates.drop (start+count), scratch ∉ gate.wires := by
  have facts : scratch ∉ circuit.measurements ∧
      (∀ gate ∈ circuit.gates.take start, scratch ∉ gate.wires) ∧
      (∀ gate ∈ circuit.gates.drop (start+count), scratch ∉ gate.wires) := by
    simpa [lifetimes,last,List.contains_eq_mem,List.all_eq_true] using checked
  exact ⟨facts.1,fun gate member => (List.mem_append.mp member).elim (facts.2.1 gate) (facts.2.2 gate)⟩

structure CheckedLifetime {sources caller dependencies program block sourceStart sourceCount event events original
    sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller dependencies program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    (map : RuntimeWorkspace.CallerMap literal) {bytes capacity}
    (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (layout : List Nat) (start count : Nat) where
  body : Checked map target layout start count
  scratchLifetime : lifetimes target.circuit event.fresh layout start count = true

def checkLifetime {sources caller dependencies program block sourceStart sourceCount event events original
    sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller dependencies program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    (map : RuntimeWorkspace.CallerMap literal) {bytes capacity}
    (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (layout : List Nat) (start count : Nat) : WorkM (CheckedLifetime map target layout start count) := do
  exactWork (Exact.charge (32*(target.circuit.gates.length+target.circuit.measurements.length+1)))
  if live : lifetimes target.circuit event.fresh layout start count = true then
    let body ← check map target layout start count
    return ⟨body,live⟩
  else throw .request

/-- One exact use of a clean physical location in the original byte-decoded
circuit. Its complete local operator satisfies the zero-embedding equation. -/
structure CleanUse (circuit : Circuit) (scratch : Nat) where
  layout : List Nat
  start : Nat
  count : Nat
  declared : circuit.declares layout
  scratchLast : layout.getLast? = some scratch
  dataBits : Nat
  shape : layout.length = dataBits+1
  steps : List Semantics.Finite.Step
  actual : interval circuit layout start count = some steps
  dependencies : List Semantics.Finite.Dependency
  logical : Semantics.Exact.Matrix
  physical : Semantics.Exact.Matrix
  accepted : ∃ work left,(Raw.Workspace.check dependencies false dataBits steps logical).run work =
    (.ok physical,left)

def Checked.cleanUse {sources caller dependencies program block sourceStart sourceCount event events original
    sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller dependencies program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    {map : RuntimeWorkspace.CallerMap literal} {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity} {layout start count scratch}
    (checked : Checked map target layout start count)
    (fresh : event.fresh = true) (last : layout.getLast? = some scratch) : CleanUse target.circuit scratch :=
  ⟨layout,start,count,checked.declared,last,original.layout.bits,checked.shape,checked.gates,
    checked.actualInterval,dependencies,original.logical.matrix,checked.equation.actual,by
      obtain ⟨work,left,ran⟩ := checked.equation.checked
      have actual := (Raw.Workspace.checkOriginal_bound _ _ _ _ _ _ _ work left ran).2
      rw [fresh] at actual
      obtain ⟨after,restored⟩ := actual
      exact ⟨work,after,restored⟩⟩

def CleanUse.covers {circuit scratch} (use : CleanUse circuit scratch) (gateIndex : Nat) : Bool :=
  use.start ≤ gateIndex && gateIndex < use.start+use.count

def CleanUse.before {circuit scratch} (first next : CleanUse circuit scratch) : Prop :=
  first.start+first.count ≤ next.start

instance {circuit scratch} (first next : CleanUse circuit scratch) : Decidable (first.before next) := by
  unfold CleanUse.before
  infer_instance

def CleanUse.complete {circuit : Circuit} {scratch : Nat} (uses : List (CleanUse circuit scratch)) : Bool :=
  circuit.gates.zipIdx.all fun (gate,index) =>
    !(gate.wires.contains scratch) || uses.any (·.covers index)

/-- Each clean owner starts after the previous use is restored. Every access
to this physical location belongs to one of the exact uses, and it remains
unmeasured; all gaps leave the axis untouched. -/
structure Reuse {bytes capacity} (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (scratch : Nat) (uses : List (CleanUse target.circuit scratch)) : Type where
  reserved : scratch < target.circuit.qubits
  ordered : uses.Pairwise CleanUse.before
  nonempty : ∀ use ∈ uses, 0 < use.count
  unmeasured : scratch ∉ target.circuit.measurements
  complete : CleanUse.complete uses = true

def checkReuse {bytes capacity} (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (scratch : Nat) (uses : List (CleanUse target.circuit scratch)) : WorkM (Reuse target scratch uses) := do
  guard (uses.length ≤ target.circuit.gates.length) .limit
  exactWork (Exact.charge (32*(1+uses.length)*(1+uses.length+target.circuit.gates.length)))
  if valid : scratch < target.circuit.qubits ∧ uses.Pairwise CleanUse.before ∧
      (∀ use ∈ uses, 0 < use.count) ∧ scratch ∉ target.circuit.measurements ∧ CleanUse.complete uses = true then
    return ⟨valid.1,valid.2.1,valid.2.2.1,valid.2.2.2.1,valid.2.2.2.2⟩
  else throw .request

theorem Reuse.accessCovered {bytes capacity} {target : CanonicalOpenQasmResources.Checked bytes capacity}
    {scratch uses} (reuse : Reuse target scratch uses)
    (index : Nat) (gate : Instruction) (actual : target.circuit.gates[index]? = some gate)
    (usesScratch : scratch ∈ gate.wires) :
    ∃ use ∈ uses,use.start ≤ index ∧ index < use.start+use.count := by
  have indexed : (gate,index) ∈ target.circuit.gates.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr actual
  have found := List.all_eq_true.mp reuse.complete _ indexed
  simp [List.contains_eq_mem,usesScratch,CleanUse.covers,List.any_eq_true] at found
  exact found

theorem CleanUse.exactRestoration {circuit scratch} (use : CleanUse circuit scratch) :
    ∃ contract first middle work after lhs lhsWork rhs rhsWork,
      (Raw.Workspace.required false use.dataBits use.logical).run first = (.ok contract,middle) ∧
      (circuitMatrix use.dependencies (Raw.circuit (use.dataBits+1) use.steps)).run work =
        (.ok use.physical,after) ∧
      Exact.Matrix.compose use.physical contract.input.map after = (.ok lhs,lhsWork) ∧
      Exact.Matrix.compose contract.output.map contract.logical lhsWork = (.ok rhs,rhsWork) ∧ lhs = rhs := by
  obtain ⟨work,left,ran⟩ := use.accepted
  obtain ⟨contract,middle,circuitWork,after,lhs,lhsWork,rhs,rhsWork,facts⟩ :=
    Raw.Workspace.check_conditions _ _ _ _ _ _ work left ran
  exact ⟨contract,work,middle,circuitWork,after,lhs,lhsWork,rhs,rhsWork,facts⟩

end QleisliKernel.Target.CanonicalOpenQasmWorkspace
