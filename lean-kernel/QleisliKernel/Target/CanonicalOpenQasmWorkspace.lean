import QleisliKernel.Target.CanonicalOpenQasmResources
import QleisliKernel.Qirf.RuntimeWorkspace

/-! Compare a designated gate interval of the decoded target with the checked
source workspace operator. The caller still establishes the entry placement
and scratch lifetime in the surrounding target circuit.
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

end QleisliKernel.Target.CanonicalOpenQasmWorkspace
