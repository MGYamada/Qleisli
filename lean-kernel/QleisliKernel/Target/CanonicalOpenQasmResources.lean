import QleisliKernel.Target.CanonicalOpenQasmRouting

/-! Resource accounting for the complete canonical OpenQASM terminal artifact.
The register is reserved and reset at entry and has no intermediate release.
Gate counts are literal counts in the terminal vocabulary. A routing
designation or a correspondence with source owners is a separate premise.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Target.CanonicalOpenQasmResources
open Finite
open CanonicalOpenQasmRouting (ascii operand header index)

inductive Gate where
  | h | x | y | z | s | sdg | t | tdg | cx | cz | swap | ccx
  deriving BEq, DecidableEq, Repr

private def Gate.read (name : List UInt8) : Option Gate :=
  ([("h",.h),("x",.x),("y",.y),("z",.z),("s",.s),("sdg",.sdg),("t",.t),
    ("tdg",.tdg),("cx",.cx),("cz",.cz),("swap",.swap),("ccx",.ccx)] : List (String × Gate)).findSome?
      fun (spelling,gate) => if name == ascii spelling then some gate else none

def Gate.arity : Gate → Nat
  | .cx | .cz | .swap => 2
  | .ccx => 3
  | _ => 1

def Gate.action : Gate → Semantics.Finite.Step
  | .h => ⟨[],.hadamard 0⟩
  | .x => Semantics.RawTrace.gate .x 0
  | .y => ⟨[],.monomial [0] [1,0] [2,6]⟩
  | .z => Semantics.RawTrace.gate .z 0
  | .s => ⟨[],.monomial [0] [0,1] [0,2]⟩
  | .sdg => ⟨[],.monomial [0] [0,1] [0,6]⟩
  | .t => Semantics.RawTrace.gate .t 0
  | .tdg => ⟨[],.monomial [0] [0,1] [0,7]⟩
  | .cx => Semantics.RawTrace.unitary (.cnot 0 1)
  | .cz => {Semantics.RawTrace.gate .z 1 with controls := [⟨0,true⟩]}
  | .swap => (Routing.Swap.mk 0 1).step
  | .ccx => Semantics.RawTrace.unitary (.toffoli 0 1 2)

structure Instruction where
  gate : Gate
  wires : List Nat
  deriving BEq, DecidableEq, Repr

def Instruction.step (gate : Instruction) : Semantics.Finite.Step :=
  Semantics.RawTrace.localize gate.wires gate.gate.action

def Instruction.localStep (layout : List Nat) (gate : Instruction) : Option Semantics.Finite.Step :=
  if gate.wires.all layout.contains then
    some (Semantics.RawTrace.localize (gate.wires.map layout.idxOf) gate.gate.action)
  else none

private def operands : Nat → List UInt8 → Option (List Nat)
  | 0, [59] => some []
  | 0, _ => none
  | fuel+1, bytes => do
    let (wire,rest) ← operand bytes
    match rest with
    | 44 :: 32 :: tail =>
      if fuel == 0 then none else (operands fuel tail).map (wire :: ·)
    | [59] => if fuel == 0 then some [wire] else none
    | _ => none

private def instruction (line : List UInt8) (width : Nat) : Option Instruction := do
  let name := line.takeWhile (· != 32)
  let 32 :: args := line.drop name.length | none
  let gate ← Gate.read name
  let wires ← operands gate.arity args
  if wires.Nodup ∧ (∀ wire ∈ wires, wire < width) then some ⟨gate,wires⟩ else none

private def measurement (line : List UInt8) (next width : Nat) : Option Nat := do
  let 99 :: 91 :: result := line | none
  let (position,rest) ← index result
  let (wire,[59]) ← operand (rest.drop 11) | none
  if position == next && wire < width && rest.take 11 == ascii " = measure " then some wire else none

private def resultWidth (line : List UInt8) : Option Nat := do
  let 98 :: 105 :: 116 :: 91 :: digits := line | none
  let (count,[32,99,59]) ← index digits | none
  if count == 0 then none else some count

private structure Lines where
  partialLine : List UInt8 := []
  completed : List (List UInt8) := []
  count : Nat := 0

private def lines (bytes : List UInt8) : Option (List (List UInt8)) := do
  let scanned ← bytes.foldlM (fun (state : Lines) byte =>
    if byte == 10 then
      if state.count < 4111 then some ⟨[],state.partialLine.reverse :: state.completed,state.count+1⟩ else none
    else if state.partialLine.length < 32 then some {state with partialLine := byte :: state.partialLine}
    else none) {}
  if scanned.partialLine.isEmpty then some scanned.completed.reverse else none

structure Circuit where
  qubits : Nat
  gates : List Instruction
  measurements : List Nat
  deriving BEq, DecidableEq, Repr

private def gatesAndMeasurements (width : Nat) (expected : Nat)
    (lines : List (List UInt8)) : Option Circuit := do
  let result ← lines.foldlM (fun (gates,measured,count) line => do
    if line.head? == some 99 && line[1]? == some 91 then
      let wire ← measurement line count width
      if count < expected && !measured.contains wire then some (gates,wire :: measured,count+1) else none
    else
      if count != 0 then none else
      let gate ← instruction line width
      some (gate :: gates,measured,count)) (([],[],0) : List Instruction × List Nat × Nat)
  let (gates,measured,count) := result
  if count == expected && gates.length ≤ 4096 then some ⟨width,gates.reverse,measured.reverse⟩ else none

def decode (bytes : ByteArray) : Option Circuit := do
  if bytes.size > 1048576 || (bytes.extract 0 header.length).data.toList != header then none else
  if bytes.size == header.length then some ⟨0,[],[]⟩ else
  let (width,after) ← CanonicalOpenQasmRouting.declaration bytes
  let first :: rest ← lines (bytes.extract after bytes.size).data.toList | none
  if first == ascii "reset q;" then
    gatesAndMeasurements width 0 rest
  else
    let expected ← resultWidth first
    let reset :: body := rest | none
    if reset == ascii "reset q;" then gatesAndMeasurements width expected body else none

structure Counts where
  reserved : Nat
  reset : Nat
  gates : Nat
  swaps : Nat
  tGates : Nat
  measurements : Nat
  deriving BEq, DecidableEq, Repr

def Circuit.counts (circuit : Circuit) : Counts :=
  ⟨circuit.qubits,circuit.qubits,circuit.gates.length,
    (circuit.gates.filter (·.gate == .swap)).length,
    (circuit.gates.filter (fun i => i.gate == .t || i.gate == .tdg)).length,circuit.measurements.length⟩

/-- The terminal register retains every location from reset through readout.
The words "live" and "reserved" count that whole register here. -/
def Circuit.reservedLocations (circuit : Circuit) : List Nat := List.range circuit.qubits

theorem Circuit.reserve_count (circuit : Circuit) :
    circuit.reservedLocations.length = circuit.counts.reserved := by
  simp [Circuit.reservedLocations,Circuit.counts]

theorem Circuit.reserve_unique (circuit : Circuit) : circuit.reservedLocations.Nodup :=
  List.nodup_range

def Circuit.declares (circuit : Circuit) (layout : List Nat) : Prop :=
  layout.Nodup ∧ ∀ axis ∈ layout, axis < circuit.qubits

instance (circuit : Circuit) (layout : List Nat) : Decidable (circuit.declares layout) := by
  unfold Circuit.declares
  infer_instance

structure Checked (bytes : ByteArray) (capacity : Nat) where
  circuit : Circuit
  original : decode bytes = some circuit
  capacityBound : circuit.qubits ≤ capacity

def check (bytes : ByteArray) (capacity : Nat) : WorkM (Checked bytes capacity) := do
  guard (bytes.size ≤ 1048576 && capacity ≤ 12) .limit
  exactWork (Exact.charge (64*(bytes.size+1)))
  match original : decode bytes with
  | none => throw .request
  | some circuit =>
    if fits : circuit.qubits ≤ capacity then return ⟨circuit,original,fits⟩ else throw .request

private def sampleHeader : String :=
  "OPENQASM 3.0;\ninclude \"stdgates.inc\";\nqubit[3] q;\nbit[2] c;\nreset q;\n"
private def sampleBody : String :=
  "h q[1];\nswap q[0], q[1];\nccx q[2], q[1], q[0];\ntdg q[1];\nc[0] = measure q[2];\nc[1] = measure q[0];\n"
private def sample := (sampleHeader ++ sampleBody).toUTF8
#guard (decode sample).map Circuit.counts == some ⟨3,3,4,1,1,2⟩
#guard (decode sample).map (·.measurements) == some [2,0]
#guard (decode (sampleHeader ++ "ccx q[1], q[1], q[0];\n" ++ sampleBody).toUTF8).isNone
#guard (decode (sampleHeader ++ "h q[3];\n" ++ sampleBody).toUTF8).isNone
#guard (decode (sampleHeader ++ sampleBody ++ "x q[2];\n").toUTF8).isNone
#guard (decode (sampleHeader ++ sampleBody.replace "c[1]" "c[0]").toUTF8).isNone
#guard (decode (sampleHeader ++ sampleBody.replace "measure q[0]" "measure q[2]").toUTF8).isNone
#guard (decode (sampleHeader ++ sampleBody ++ "reset q;\n").toUTF8).isNone
#guard (decode (sampleHeader.replace "q;\nbit" "q;bit" ++ sampleBody).toUTF8).isNone
#guard (decode ("OPENQASM 3.0;\ninclude \"stdgates.inc\";\nqubit[12] q;\nreset q;\n"
  ++ "ccx q[10], q[11], q[0];\n").toUTF8).map Circuit.counts == some ⟨12,12,1,0,0,0⟩
#guard ((check sample 2).run 100000).1.isOk == false
#guard ((check sample 3).run 0).1.isOk == false

end QleisliKernel.Target.CanonicalOpenQasmResources
