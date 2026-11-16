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

private theorem mapM_length {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (ok : xs.mapM f = some ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil => simp_all
  | cons first rest ih =>
    cases read : f first with
    | none => simp [List.mapM_cons,read] at ok
    | some value =>
      cases remaining : rest.mapM f with
      | none => simp [List.mapM_cons,read,remaining] at ok
      | some tail =>
        have same : value :: tail = ys := by simpa [List.mapM_cons,read,remaining] using ok
        subst ys
        simp [ih tail remaining]

/-- Every decoded instruction in an admitted workspace slice contributes one
step to the checked operator, including the literal cleanup and phase gates. -/
theorem interval_length {circuit layout start count steps}
    (ok : interval circuit layout start count = some steps) :
    steps.length = count ∧ start+count ≤ circuit.gates.length := by
  unfold interval at ok
  split at ok
  · rename_i inside
    have length := mapM_length _ _ _ ok
    have remaining : count ≤ circuit.gates.length - start := by omega
    exact ⟨by simpa [List.length_take,Nat.min_eq_left remaining] using length,inside⟩
  · contradiction

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
    (rawFrame targetFrame : List Nat) (start count : Nat) where
  full : targetFrame.length = rawFrame.length
  declared : target.circuit.declares targetFrame
  liveLayout : List Nat
  boundOwners : placedWires rawFrame targetFrame
    (map.selected.flatMap (·.port.wires)) = some liveLayout
  freshScratch : Option Nat
  scratchMode : freshScratch.isSome = event.fresh
  scratchFree : ∀ location ∈ freshScratch.toList, location ∉ targetFrame
  body : Checked map target (liveLayout ++ freshScratch.toList) start count

def checkPlacementInFrame {sources caller dependencies program block sourceStart sourceCount event events original
    sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller dependencies program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    (map : RuntimeWorkspace.CallerMap literal) {bytes capacity}
    (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (rawFrame targetFrame : List Nat) (start count : Nat) (scratch : Option Nat) :
    WorkM (Placed map target rawFrame targetFrame start count) := do
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

/-- The direct case places the complete workspace caller frame. An enclosing
caller can supply its own frame after binding the selected owner ports. -/
def checkPlacement {sources caller dependencies program block sourceStart sourceCount event events original
    sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller dependencies program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    (map : RuntimeWorkspace.CallerMap literal) {bytes capacity}
    (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (targetFrame : List Nat) (start count : Nat) (scratch : Option Nat) :
    WorkM (Placed map target sourceInterval.before.quantum.reference.frame targetFrame start count) :=
  checkPlacementInFrame map target sourceInterval.before.quantum.reference.frame targetFrame start count scratch

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
  unmeasured : scratch ∉ target.circuit.measurements
  complete : CleanUse.complete uses = true

def checkReuse {bytes capacity} (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (scratch : Nat) (uses : List (CleanUse target.circuit scratch)) : WorkM (Reuse target scratch uses) := do
  exactWork (Exact.charge (32*(1+uses.length)*(1+uses.length+target.circuit.gates.length)))
  if valid : scratch < target.circuit.qubits ∧ uses.Pairwise CleanUse.before ∧
      scratch ∉ target.circuit.measurements ∧ CleanUse.complete uses = true then
    return ⟨valid.1,valid.2.1,valid.2.2.1,valid.2.2.2⟩
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

/-- Each reusable clean wire is in the literal reset register. Any gate that
later uses that wire is counted inside a checked restoration interval. -/
theorem Reuse.prepared_and_counted {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity}
    {scratch uses} (reuse : Reuse target scratch uses) :
    scratch ∈ target.circuit.reservedLocations ∧ scratch < target.circuit.counts.reset ∧
      (∀ index gate, target.circuit.gates[index]? = some gate → scratch ∈ gate.wires →
        ∃ use ∈ uses, use.start ≤ index ∧ index < use.start+use.count ∧
          use.steps.length = use.count ∧ use.start+use.count ≤ target.circuit.counts.gates) := by
  refine ⟨List.mem_range.mpr reuse.reserved,reuse.reserved,?_⟩
  intro index gate emitted touched
  obtain ⟨use,member,start,stop⟩ := reuse.accessCovered index gate emitted touched
  have ⟨count,inside⟩ := interval_length use.actual
  exact ⟨use,member,start,stop,count,inside⟩

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

open Semantics
open CanonicalOpenQasmResources (Gate)

private theorem lookup_idxOf {layout : List Nat} {wire : Nat} (member : wire ∈ layout) :
    layout[layout.idxOf wire]? = some wire := by
  rw [List.idxOf, ← List.find?_eq_getElem?_findIdx]
  have found : (layout.find? (· == wire)).isSome = true :=
    List.find?_isSome.mpr ⟨wire, member, by simp⟩
  cases read : layout.find? (· == wire) with
  | none => simp [read] at found
  | some value =>
    have equal := List.find?_some read
    simp only [beq_iff_eq] at equal
    rw [equal]

private theorem instruction_roundtrip {layout : List Nat} {instruction : Instruction}
    {step : Semantics.Finite.Step} (arity : instruction.wires.length = instruction.gate.arity)
    (localized : instruction.localStep layout = some step) :
    RawTrace.localize layout step = instruction.step := by
  obtain ⟨gate, wires⟩ := instruction
  simp only [Instruction.localStep] at localized
  split at localized
  · rename_i inside
    simp only [List.all_eq_true, List.contains_iff_mem] at inside
    simp only [Option.some.injEq] at localized
    subst step
    have atWire (i : Nat) (valid : i < wires.length) :
        (layout[(wires[i]?.map layout.idxOf).getD 0]?).getD 0 = wires[i]?.getD 0 := by
      rw [List.getElem?_eq_getElem valid]
      simp [lookup_idxOf (inside _ (List.getElem_mem valid))]
    cases gate <;>
      simp [Instruction.step, Gate.action, RawTrace.unitary, RawTrace.gate,
        RawTrace.localize, Routing.Swap.step, Gate.arity] at arity ⊢
    all_goals (repeat' apply And.intro) <;> apply atWire <;> omega
  · cases localized

private theorem word_roundtrip {layout : List Nat} {word : List Instruction}
    {steps : List Semantics.Finite.Step} (valid : ∀ instruction ∈ word, instruction.wires.length = instruction.gate.arity)
    (localized : word.mapM (Instruction.localStep layout) = some steps) :
    steps.map (RawTrace.localize layout) = word.map Instruction.step := by
  induction word generalizing steps with
  | nil => simp_all
  | cons first rest ih =>
    cases one : first.localStep layout with
    | none => simp [List.mapM_cons, one] at localized
    | some step =>
      cases others : rest.mapM (Instruction.localStep layout) with
      | none => simp [List.mapM_cons, one, others] at localized
      | some tail =>
        simp [List.mapM_cons, one, others] at localized
        subst steps
        simp [instruction_roundtrip (valid first (by simp)) one,
          ih (fun instruction member => valid instruction (by simp [member])) others]

private theorem interval_roundtrip {circuit : Circuit} {layout : List Nat} {start count : Nat}
    {steps : List Semantics.Finite.Step}
    (valid : ∀ instruction ∈ (circuit.gates.drop start).take count,
      instruction.wires.length = instruction.gate.arity)
    (localized : interval circuit layout start count = some steps) :
    steps.map (RawTrace.localize layout) =
      ((circuit.gates.drop start).take count).map Instruction.step := by
  unfold interval at localized
  split at localized
  · exact word_roundtrip valid localized
  · cases localized

/-- Reindex a checked local word into the original physical positions of the
literal decoded instruction slice, preserving the order of every operand. -/
theorem decoded_interval_roundtrip {bytes : ByteArray} {circuit : Circuit} {layout : List Nat}
    {start count : Nat} {steps : List Semantics.Finite.Step}
    (decoded : CanonicalOpenQasmResources.decode bytes = some circuit)
    (localized : interval circuit layout start count = some steps) :
    steps.map (RawTrace.localize layout) =
      ((circuit.gates.drop start).take count).map Instruction.step := by
  apply interval_roundtrip _ localized
  intro instruction member
  exact (CanonicalOpenQasmResources.decode_instruction_shape decoded instruction
    (List.mem_of_mem_drop (List.mem_of_mem_take member))).1

#print axioms decoded_interval_roundtrip

end QleisliKernel.Target.CanonicalOpenQasmWorkspace
