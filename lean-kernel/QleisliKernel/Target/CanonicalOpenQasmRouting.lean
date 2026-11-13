import QleisliKernel.Target.Routing

/-! Read a specified contiguous SWAP segment of the actual terminal OpenQASM
output. The placement claim covers just this segment. The surrounding gates,
the entry occupancy, and designation of the segment as routing are premises
of a separate whole-artifact realization.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Target.CanonicalOpenQasmRouting
open Finite

private def ascii (text : String) : List UInt8 := text.toUTF8.data.toList

private def digit (byte : UInt8) : Option Nat :=
  if 48 ≤ byte.toNat && byte.toNat ≤ 57 then some (byte.toNat - 48) else none

private def index : List UInt8 → Option (Nat × List UInt8)
  | 49 :: 48 :: 93 :: rest => some (10,rest)
  | 49 :: 49 :: 93 :: rest => some (11,rest)
  | 49 :: 50 :: 93 :: rest => some (12,rest)
  | byte :: 93 :: rest => (digit byte).map (·,rest)
  | _ => none

/-- Canonical OpenQASM wire operands have no leading zero. The terminal
exporter only uses physical locations 0 through 11. -/
private def operand : List UInt8 → Option (Nat × List UInt8)
  | 113 :: 91 :: digits => do
    let (axis,rest) ← index digits
    if axis < 12 then some (axis,rest) else none
  | _ => none

private def gate (line : List UInt8) : Option Semantics.Finite.Step := do
  let 115 :: 119 :: 97 :: 112 :: 32 :: arguments := line | none
  let (left,44 :: 32 :: rest) ← operand arguments | none
  let (right,[59]) ← operand rest | none
  return (Routing.Swap.mk left right).step

/-- A tail-recursive scan reads exact gate lines with the emitter's newline
and punctuation. Empty segments represent zero physical routing gates. -/
private def word (bytes : List UInt8) : Option (List Semantics.Finite.Step) := do
  let (line,gates) ← bytes.foldlM (fun (line,gates) byte => do
    if byte == 10 then return ([],(← gate line.reverse) :: gates)
    if line.length >= 19 then none else return (byte :: line,gates)) ([],[])
  if line.isEmpty then some gates.reverse else none

private def header : List UInt8 := ascii "OPENQASM 3.0;\ninclude \"stdgates.inc\";\n"

def declaration (bytes : ByteArray) : Option (Nat × Nat) := do
  let line := ((bytes.extract header.length (header.length+13)).data.toList).takeWhile (· != 10)
  let 113 :: 117 :: 98 :: 105 :: 116 :: 91 :: digits := line | none
  let (qubits,[32,113,59]) ← index digits | none
  if qubits == 0 then none else some (qubits,header.length+line.length+1)

def decode (bytes : ByteArray) (start stop : Nat) : Option (List Semantics.Finite.Step) := do
  if !(bytes.size ≤ 1048576 && header.length ≤ start && start ≤ stop && stop ≤ bytes.size &&
      stop - start ≤ 4096 * 20) then none else
  if (bytes.extract 0 header.length).data.toList != header then none else
  let (qubits,afterDeclaration) ← declaration bytes
  if start < afterDeclaration then none else
  if bytes.data[start - 1]? != some 10 || bytes.data[stop - 1]? != some 10 then none else
  let gates ← word (bytes.extract start stop).data.toList
  if gates.length ≤ 4096 && gates.all (fun step => (Finite.targets step.action).all (· < qubits)) then
    some gates else none

structure Checked (bytes : ByteArray) (profile : Routing.Profile) (occupied : List Nat) (start stop : Nat) where
  qubits : Nat
  readDeclaration : ∃ after, declaration bytes = some (qubits,after)
  fitsTarget : qubits ≤ profile.capacity
  occupiedDeclared : ∀ axis ∈ occupied, axis < qubits
  gates : List Semantics.Finite.Step
  decoded : decode bytes start stop = some gates
  routing : Routing.Schedule profile occupied gates

def check (bytes : ByteArray) (profile : Routing.Profile) (occupied : List Nat) (start stop : Nat) :
    WorkM (Checked bytes profile occupied start stop) := do
  guard (profile.capacity ≤ 12 && occupied.length ≤ 12 && bytes.size ≤ 1048576 &&
    header.length ≤ start && start ≤ stop && stop ≤ bytes.size && stop-start ≤ 4096*20) .limit
  exactWork (Exact.charge (64*(stop-start+header.length+occupied.length+14)))
  match declaredWidth : declaration bytes, decoded : decode bytes start stop with
  | some (qubits,after),some gates =>
    if fits : qubits ≤ profile.capacity then
      if declared : ∀ axis ∈ occupied, axis < qubits then
        let routing ← lift (readOption (Routing.read profile occupied gates))
        return ⟨qubits,⟨after,declaredWidth⟩,fits,declared,gates,decoded,routing⟩
      else throw .request
    else throw .request
  | _,_ => throw .request

private def sampleHeader : String := "OPENQASM 3.0;\ninclude \"stdgates.inc\";\nqubit[3] q;\nbit[1] c;\nreset q;\n"
private def sampleWord : String := "swap q[0], q[1];\nswap q[1], q[2];\n"
private def sample : ByteArray := (sampleHeader ++ sampleWord ++ "c[0] = measure q[2];\n").toUTF8
private def start : Nat := sampleHeader.utf8ByteSize
private def stop : Nat := start + sampleWord.utf8ByteSize
private def line : Routing.Profile := ⟨3,fun a b => a+1 == b || b+1 == a⟩

#guard (((check sample line [0,1,2] start stop).run 100000).1.toOption.map
  (fun checked => (checked.routing.checked.final,checked.routing.swapCount))) == some ([2,0,1],2)
#guard (decode sample (start+1) stop).isNone
#guard (decode sample start (stop-1)).isNone
#guard (decode sample start sample.size).isNone
#guard (((check sample line [0,2] start stop).run 100000).1).isOk == false
#guard (decode sample start start).map List.length == some 0
#guard (gate (ascii "swap q[10], q[11];")).isSome
#guard (gate (ascii "swap q[01], q[1];")).isNone
#guard (gate (ascii "swap q[12], q[1];")).isNone
private def disconnectedWord : String := "swap q[0], q[2];\n"
private def disconnected : ByteArray := (sampleHeader ++ disconnectedWord ++ "c[0] = measure q[2];\n").toUTF8
private def disconnectedEnd : Nat := start + disconnectedWord.utf8ByteSize
#guard (decode disconnected start disconnectedEnd).isSome
#guard (((check disconnected line [0,1,2] start disconnectedEnd).run 100000).1).isOk == false
#guard (((check sample line [0,1,2] start stop).run 0).1).isOk == false
#guard (((check sample ⟨2,fun _ _ => true⟩ [0,1] start start).run 100000).1).isOk == false
#guard (((check sample ⟨8,fun _ _ => true⟩ [0,1,2,3] start stop).run 100000).1).isOk == false

end QleisliKernel.Target.CanonicalOpenQasmRouting
