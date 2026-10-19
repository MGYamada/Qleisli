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

inductive Edition where
  | e2026
  deriving BEq, DecidableEq, Repr

def Edition.code : Edition → Nat
  | .e2026 => 2026

structure Input where
  edition : Edition
  scope : Scope
  original : ByteArray
  graph : ByteArray
  caller : ByteArray
  indices : List Nat

def maxPacketBytes : Nat := 67108864
def maxIndices : Nat := 100000

def u32 (bytes : ByteArray) (offset : Nat) : Nat :=
  (List.range 4).foldl (fun n i => n + bytes[offset+i]!.toNat * 256^i) 0

/-- A supported edition is checked from original bytes, never inferred from the
product release, mode, source producer or presence of a valid inner packet. -/
def header (bytes : ByteArray) : Except Gate.Error Edition :=
  if bytes.size < 28 || bytes.size > maxPacketBytes ||
      bytes.extract 0 4 != "QLV3".toUTF8 then .error .packet
  else if u32 bytes 4 != 2026 then .error .edition
  else .ok .e2026

theorem header_code (bytes : ByteArray) (edition : Edition)
    (ok : header bytes = .ok edition) : u32 bytes 4 = edition.code := by
  unfold header at ok
  split at ok
  · cases ok
  · split at ok
    · cases ok
    · rename_i supported
      cases edition
      simpa [Edition.code] using supported

/-- QLV3, explicit edition, scope and four little-endian u32 lengths/counts, then original,
graph, caller and u32 alias indices. Reject missing data and trailing bytes
before allocation proportional to an untrusted count. -/
def read (bytes : ByteArray) : Except Gate.Error Input := do
  let edition ← header bytes
  let scope ← match u32 bytes 8 with
    | 0 => pure Scope.inspection | 1 => pure Scope.execution
    | 2 => pure Scope.caller | _ => throw .packet
  let a := u32 bytes 12
  let g := u32 bytes 16
  let c := u32 bytes 20
  let n := u32 bytes 24
  if a == 0 || n > maxIndices || g + c > maxBytes ||
      bytes.size != 28+a+g+c+4*n then throw .packet
  match scope with
  | .inspection => if g != 0 || c != 0 || n != 0 then throw .packet
  | .execution => if g == 0 || c != 0 || n != 0 then throw .packet
  | .caller => if g == 0 || c == 0 then throw .packet
  let start := 28+a+g+c
  return ⟨edition,scope,bytes.extract 28 (28+a),bytes.extract (28+a) (28+a+g),
    bytes.extract (28+a+g) start,(List.range n).map (fun i => u32 bytes (start+4*i))⟩

/-- Success of the actual parser includes successful original-byte edition
validation. This is a framing property, not a source-preservation theorem. -/
theorem read_header (bytes : ByteArray) (input : Input)
    (ok : read bytes = .ok input) : header bytes = .ok input.edition := by
  cases parsed : header bytes with
  | error error =>
    unfold read at ok
    rw [parsed] at ok
    change Except.error error = Except.ok input at ok
    cases ok
  | ok edition =>
    cases edition
    cases input.edition
    rfl

theorem read_edition (bytes : ByteArray) (input : Input)
    (ok : read bytes = .ok input) : u32 bytes 4 = input.edition.code :=
  header_code bytes input.edition (read_header bytes input ok)

end QleisliKernel.Protocol.ExecutionView.Packet
