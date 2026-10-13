import Protocol.ExecutionView.Gate

/-! Versioned native envelope. Original QLV1/hierarchy payloads remain internal
inputs to their existing checkers, never an alternative external protocol.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.Packet

inductive Scope where
  | inspection | execution | caller
  deriving BEq, DecidableEq, Repr

def Scope.name : Scope → String
  | .inspection => "inspection"
  | .execution => "execution"
  | .caller => "caller"

structure Input where
  scope : Scope
  original : ByteArray
  graph : ByteArray
  caller : ByteArray
  indices : List Nat

def maxPacketBytes : Nat := 67108864
def maxIndices : Nat := 100000

private def u32 (bytes : ByteArray) (offset : Nat) : Nat :=
  (List.range 4).foldl (fun n i => n + bytes[offset+i]!.toNat * 256^i) 0

/-- QLV2, scope and four little-endian u32 lengths/counts, then original,
graph, caller and u32 alias indices. Reject missing data and trailing bytes
before allocation proportional to an untrusted count. -/
def read (bytes : ByteArray) : Except Gate.Error Input := do
  if bytes.size < 24 || bytes.size > maxPacketBytes ||
      bytes.extract 0 4 != "QLV2".toUTF8 then throw .packet
  let scope ← match u32 bytes 4 with
    | 0 => pure Scope.inspection | 1 => pure Scope.execution
    | 2 => pure Scope.caller | _ => throw .packet
  let a := u32 bytes 8
  let g := u32 bytes 12
  let c := u32 bytes 16
  let n := u32 bytes 20
  if a == 0 || n > maxIndices || g + c > maxBytes ||
      bytes.size != 24+a+g+c+4*n then throw .packet
  match scope with
  | .inspection => if g != 0 || c != 0 || n != 0 then throw .packet
  | .execution => if g == 0 || c != 0 || n != 0 then throw .packet
  | .caller => if g == 0 || c == 0 then throw .packet
  let start := 24+a+g+c
  return ⟨scope,bytes.extract 24 (24+a),bytes.extract (24+a) (24+a+g),
    bytes.extract (24+a+g) start,(List.range n).map (fun i => u32 bytes (start+4*i))⟩

end QleisliKernel.Protocol.ExecutionView.Packet
