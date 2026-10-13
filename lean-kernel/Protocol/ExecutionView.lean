import Std

/-! Canonical QDV1 transport trees, independent of QIRF's JSON encoder.
This encoding alone grants no acceptance or runtime-preservation claim.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView

inductive Value where
  | null
  | boolean (value : Bool)
  | natural (value : Nat)
  | text (value : String)
  | array (values : List Value)

def maxBytes : Nat := 67108864
def maxDepth : Nat := 128

private abbrev WriteM := StateT ByteArray (Except String)

private def append (bytes : ByteArray) : WriteM Unit := do
  let previous ← get
  if previous.size + bytes.size > maxBytes then throw "canonical byte capacity"
  set (previous ++ bytes)

private def tag (value : Nat) : WriteM Unit :=
  append ⟨#[value.toUInt8]⟩

private def littleEndian (width value : Nat) : ByteArray :=
  ⟨((List.range width).map (fun i => (value / 256^i % 256).toUInt8)).toArray⟩

private def sized (kind count : Nat) : WriteM Unit := do
  if count ≥ 2^32 then throw "canonical length exceeds u32"
  tag kind
  append (littleEndian 4 count)

private def write (fuel : Nat) : Value → WriteM Unit :=
  Nat.rec (fun _ => throw "canonical depth capacity") (fun _ recurse value => do
    match value with
    | .null => tag 0
    | .boolean false => tag 1
    | .boolean true => tag 2
    | .natural value =>
      if value ≥ 2^64 then throw "canonical natural exceeds u64"
      tag 3
      append (littleEndian 8 value)
    | .text value =>
      sized 4 value.utf8ByteSize
      append value.toUTF8
    | .array values =>
      sized 5 values.length
      values.forM recurse) fuel

def encode (value : Value) : Except String ByteArray := do
  let (_, bytes) ← (write (maxDepth+1) value).run "QDV1".toUTF8
  return bytes

end QleisliKernel.Protocol.ExecutionView
