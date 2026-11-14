import Protocol.Raw
import Protocol.ExecutionView.Finite
import Protocol.ExecutionView.Gate
import QleisliKernel.Qirf.StructuralComputedRaw

/-! Strict circuit-backed protected packet transport. The source and live
frame must come from the enclosing checker. The compared record is tied to
the newly decoded semantic packet and the same ordered physical ports.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.StructuralComputed
open Lean QleisliKernel Qirf SourceTypes SourceRuntimeContext
open Gate

private def field (value : Json) (key : String) := value.getObjVal? key

private def number (value : Json) (fieldName : String) : Except String Nat := do
  let n ← (← field value fieldName).getNat?
  if n > 4294967295 then throw "structural computed integer exceeds u32"
  return n

def decode (bytes : ByteArray) : Except String StructuralComputedRaw.Packet := do
  let some text := String.fromUTF8? bytes | throw "invalid structural computed UTF-8"
  let value ← FiniteCodec.parseWithDepth text 128
  let fields := (← value.getObj?).toList.map (·.1)
  let names := ["tag","source","source_out","scratch","forward","inverse","uses"]
  if fields.length != names.length || !fields.all names.contains then
    throw "unexpected or missing structural computed field"
  if (← (← field value "tag").getStr?) != "structural_compute" then
    throw "unknown structural computed tag"
  return ⟨← number value "source",← number value "source_out",← number value "scratch",
    ← Raw.steps (← field value "forward"),← Raw.steps (← field value "inverse"),
    ← (← (← field value "uses").getArr?).toList.mapM Raw.usage⟩

def packetView (packet : StructuralComputedRaw.Packet) : Value :=
  .array [.text "structural-compute",.natural packet.input,.natural packet.output,.natural packet.scratch,
    FiniteView.steps packet.forward,FiniteView.steps packet.inverse,.array (packet.uses.map FiniteView.usage)]

private def port (value : Semantics.Raw.Port) : Value :=
  .array [.natural value.token,.array (value.wires.map .natural),.natural value.bits]

def view (packet : StructuralComputedRaw.Packet) (input output : Semantics.Raw.Port) : Value :=
  .array [.text "structural-compute-view",packetView packet,port input,port output]

structure Binding {sources caller} {event : ComputedEvent sources caller}
    (original : StructuralXorPredicate.Original event) (before : RuntimeStructuralAction.SourceState)
    (entry : RuntimeOwnerMap.State) (bytes supplied : ByteArray) where
  packet : StructuralComputedRaw.Packet
  decoded : decode bytes = .ok packet
  checked : StructuralComputedRaw.SourceChecked original packet before entry
  core : RuntimeInterval.Computed (StructuralComputedRaw.readSource original packet before entry) checked
  compared : encode (view packet checked.raw.input checked.output) = .ok supplied

/-- Recompute the source/Raw evidence from bytes and compare the resulting
semantic circuit and ports to the execution view, without issuing a handle. -/
def check {sources caller} {event : ComputedEvent sources caller}
    (original : StructuralXorPredicate.Original event) (before : RuntimeStructuralAction.SourceState)
    (entry : RuntimeOwnerMap.State) (bytes supplied : ByteArray) :
    CheckM (Binding original before entry bytes supplied) := do
  guard (supplied.size ≤ maxBytes) .invalidView
  guard (bytes.size ≤ maxBytes) .packet
  native (Finite.exactWork (Exact.charge (8*(bytes.size + supplied.size + 1))))
  guard (framed supplied) .invalidView
  match decoded : decode bytes with
  | .error _ => throw .packet
  | .ok packet =>
    let receipt ← native (NaturalAffine.witness (StructuralComputedRaw.readSource original packet before entry))
    match encoded : encode (view packet receipt.val.raw.input receipt.val.output) with
    | .error _ => throw .encoding
    | .ok expected =>
      if same : supplied.data = expected.data then
        have equal : expected = supplied := by
          cases supplied
          cases expected
          cases same
          rfl
        return ⟨packet,decoded,receipt.val,by with_reducible exact receipt.property,equal ▸ encoded⟩
      else throw .decodedView

#print axioms check

end QleisliKernel.Protocol.ExecutionView.StructuralComputed
