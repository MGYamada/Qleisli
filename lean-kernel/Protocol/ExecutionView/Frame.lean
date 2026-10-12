import Protocol.ExecutionView

/-! Total bounded QDV1 framing inspection. It reads only the canonical byte
grammar, independently of either typed profile walker.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView

private def length32 (bytes : ByteArray) (offset : Nat) : Nat :=
  (List.range 4).foldl (fun value index =>
    value + bytes[offset+index]!.toNat * 256^index) 0

private def elements (next : Nat → Except String Nat) (count offset : Nat) : Except String Nat :=
  Nat.rec (.ok offset) (fun _ previous => previous >>= next) count

private def skipValue (fuel : Nat) (bytes : ByteArray) : Nat → Except String Nat :=
  Nat.rec (fun _ => throw "canonical depth capacity") (fun _ recurse offset => do
    if offset ≥ bytes.size then throw "missing canonical value"
    let start := offset+1
    match bytes[offset]!.toNat with
    | 0 | 1 | 2 => return start
    | 3 =>
      if start+8 > bytes.size then throw "truncated canonical natural"
      return start+8
    | 4 | 5 =>
      if start+4 > bytes.size then throw "truncated canonical length"
      let count := length32 bytes start
      let start := start+4
      -- Every array element occupies at least one byte. Check before iteration;
      -- an attacker-controlled u32 never allocates a list or array of that size.
      if count > bytes.size-start then throw "truncated canonical payload"
      if bytes[offset]!.toNat == 4 then
        if (String.fromUTF8? (bytes.extract start (start+count))).isNone then
          throw "invalid canonical UTF-8"
        return start+count
      else
        elements recurse count start
    | _ => throw "unknown canonical tag") fuel

/-- Exactly one complete bounded value, with no trailing bytes. This checks
transport syntax only; no field or semantic acceptance is inferred. -/
def framed (bytes : ByteArray) : Bool :=
  bytes.size ≥ 5 && bytes.size ≤ maxBytes && bytes.extract 0 4 == "QDV1".toUTF8 &&
    match skipValue (maxDepth+1) bytes 4 with
    | .ok endOffset => endOffset == bytes.size
    | .error _ => false

end QleisliKernel.Protocol.ExecutionView
