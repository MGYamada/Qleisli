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

private def operands : Nat → List UInt8 → Option (List Nat) :=
  Nat.rec (fun bytes => if bytes == [59] then some [] else none) (fun fuel recurse bytes => do
    let (wire,rest) ← operand bytes
    match rest with
    | 44 :: 32 :: tail =>
      if fuel == 0 then none else (recurse tail).map (wire :: ·)
    | [59] => if fuel == 0 then some [wire] else none
    | _ => none)

private def instruction (line : List UInt8) (width : Nat) : Option Instruction := do
  let name := line.takeWhile (· != 32)
  let 32 :: args := line.drop name.length | none
  let gate ← Gate.read name
  let wires ← operands gate.arity args
  if wires.length = gate.arity ∧ wires.Nodup ∧ (∀ wire ∈ wires, wire < width) then
    some ⟨gate,wires⟩
  else none

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

private def scanLine (width expected : Nat) :
    (List Instruction × List Nat × Nat) → List UInt8 → Option (List Instruction × List Nat × Nat) :=
  fun (gates,measured,count) line => do
    if line.head? == some 99 && line[1]? == some 91 then
      let wire ← measurement line count width
      if count < expected && !measured.contains wire then some (gates,wire :: measured,count+1) else none
    else
      if count != 0 then none else
      let gate ← instruction line width
      some (gate :: gates,measured,count)

private def gatesAndMeasurements (width : Nat) (expected : Nat)
    (lines : List (List UInt8)) : Option Circuit := do
  let result ← lines.foldlM (scanLine width expected) ([],[],0)
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
#guard (decode (sampleHeader ++ "cx q[0];\n" ++ sampleBody).toUTF8).isNone
#guard (decode (sampleHeader ++ "ccx q[0], q[1];\n" ++ sampleBody).toUTF8).isNone
#guard (decode (sampleHeader ++ "swap q[0];\n" ++ sampleBody).toUTF8).isNone
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

private def instructionShape (width : Nat) (gate : Instruction) : Prop :=
  gate.wires.length = gate.gate.arity ∧ gate.wires.Nodup ∧ ∀ wire ∈ gate.wires, wire < width

private theorem instruction_shape {line : List UInt8} {width : Nat} {gate : Instruction}
    (decoded : instruction line width = some gate) : instructionShape width gate := by
  unfold instruction at decoded
  dsimp only at decoded
  split at decoded
  · rename_i args layout
    cases name : Gate.read (line.takeWhile (· != 32)) with
    | none => simp only [name, bind, Option.bind] at decoded
              cases decoded
    | some action =>
      simp only [name, bind, Option.bind] at decoded
      cases wireList : operands action.arity args with
      | none => rw [wireList] at decoded
                cases decoded
      | some wires =>
        rw [wireList] at decoded
        dsimp only at decoded
        split at decoded
        · rename_i shape
          have parsed := Option.some.inj decoded
          subst gate
          exact shape
        · cases decoded
  · cases decoded

private theorem foldlM_preserves {α β : Type} (step : β → α → Option β) (valid : β → Prop)
    (advance : ∀ prior line next, valid prior → step prior line = some next → valid next)
    {lines : List α} {initial final : β} (starts : valid initial)
    (computed : lines.foldlM step initial = some final) : valid final := by
  induction lines generalizing initial with
  | nil => simpa using (show initial = final from Option.some.inj computed) ▸ starts
  | cons line rest ih =>
    rw [List.foldlM_cons] at computed
    cases advanced : step initial line with
    | none => simp [advanced, Option.bind] at computed
    | some next =>
      exact ih (advance initial line next starts advanced) (by simpa [advanced, Option.bind] using computed)

private theorem gatesAndMeasurements_shape {width expected lines circuit}
    (decoded : gatesAndMeasurements width expected lines = some circuit) :
    circuit.qubits = width ∧ ∀ gate ∈ circuit.gates, instructionShape width gate := by
  unfold gatesAndMeasurements at decoded
  match input : lines.foldlM (scanLine width expected) ([],[],0) with
  | none => rw [input] at decoded
            cases decoded
  | some (gates, measured, count) =>
    have valid := foldlM_preserves _ (fun state : List Instruction × List Nat × Nat =>
      ∀ gate ∈ state.1, instructionShape width gate) (fun prior line next before computed => by
        obtain ⟨gates,measured,count⟩ := prior
        dsimp only [scanLine] at before computed
        split at computed
        · cases wire : measurement line count width with
          | none => rw [wire] at computed
                    cases computed
          | some axis =>
            simp only [wire, bind, Option.bind] at computed
            split at computed
            · have same := Option.some.inj computed
              subst next
              exact before
            · cases computed
        · split at computed
          · cases computed
          · cases parsed : instruction line width with
            | none => rw [parsed] at computed
                      cases computed
            | some added =>
              simp only [parsed, bind, Option.bind] at computed
              have same := Option.some.inj computed
              subst next
              intro gate member
              rcases List.mem_cons.mp member with same | tail
              · subst gate
                exact instruction_shape parsed
              · exact before _ tail)
      (by simp) input
    simp only [input, bind, Option.bind] at decoded
    split at decoded
    · have parsed := Option.some.inj decoded
      subst circuit
      exact ⟨rfl, fun gate member => valid gate (List.mem_reverse.mp member)⟩
    · cases decoded

/-- The literal decoder checks the arity and distinct, in-range coordinates
of every actual gate, before any resource or placement claim. -/
theorem decode_instruction_shape {bytes : ByteArray} {circuit : Circuit}
    (decoded : decode bytes = some circuit) (gate : Instruction) (member : gate ∈ circuit.gates) :
    gate.wires.length = gate.gate.arity ∧ gate.wires.Nodup ∧ ∀ wire ∈ gate.wires, wire < circuit.qubits := by
  have finish {width expected lines} (accepted : gatesAndMeasurements width expected lines = some circuit) :
      instructionShape circuit.qubits gate := by
    obtain ⟨same, shape⟩ := gatesAndMeasurements_shape accepted
    rw [same]
    exact shape gate member
  unfold decode at decoded
  split at decoded
  · cases decoded
  · split at decoded
    · have empty := Option.some.inj decoded
      subst circuit
      cases member
    · cases source : CanonicalOpenQasmRouting.declaration bytes with
      | none => rw [source] at decoded
                cases decoded
      | some result =>
        obtain ⟨width,after⟩ := result
        simp only [source, bind, Option.bind] at decoded
        cases body : lines (bytes.extract after bytes.size).data.toList with
        | none => rw [body] at decoded; cases decoded
        | some read =>
          cases read with
          | nil => rw [body] at decoded; cases decoded
          | cons first rest =>
            rw [body] at decoded
            dsimp only at decoded
            split at decoded
            · exact finish decoded
            · cases widthCheck : resultWidth first with
              | none => rw [widthCheck] at decoded
                        cases decoded
              | some expected =>
                rw [widthCheck] at decoded
                dsimp only at decoded
                cases rest with
                | nil => cases decoded
                | cons reset tail =>
                  dsimp only at decoded
                  split at decoded
                  · exact finish decoded
                  · cases decoded

#print axioms decode_instruction_shape

end QleisliKernel.Target.CanonicalOpenQasmResources
