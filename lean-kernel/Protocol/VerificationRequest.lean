import Protocol.NativeContext
import Protocol.RequestDigest

/-! The typed v1 request carries the exact existing obligation packet. No
compatibility reader can decide a weaker obligation after a rejection.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.VerificationRequest

open ExecutionView

def maxInputBytes : Nat := Packet.maxPacketBytes + 144

structure Request where
  obligation : NativeContext.Mode
  work : Nat
  packet : ByteArray

/-- QLR1, work and two little-endian string lengths, exact product and
obligation, then the complete inner packet. Its own reader binds edition,
scope and original source or artifact. -/
def read (bytes : ByteArray) : Except Gate.Error Request := do
  if bytes.size < 16 || bytes.size > maxInputBytes ||
      bytes.extract 0 4 != "QLR1".toUTF8 then throw .packet
  let work := Packet.u32 bytes 4
  if work > exactWorkLimit then throw (.native .limit)
  let versionSize := Packet.u32 bytes 8
  let obligationSize := Packet.u32 bytes 12
  let obligationStart := 16 + versionSize
  let packetStart := obligationStart + obligationSize
  if versionSize > 64 || obligationSize > 64 || packetStart ≥ bytes.size ||
      bytes.size - packetStart > Packet.maxPacketBytes then throw .packet
  if bytes.extract 16 obligationStart != productVersion.toUTF8 then throw .version
  let some name := String.fromUTF8? (bytes.extract obligationStart packetStart)
    | throw .packet
  let some obligation := NativeContext.Mode.parse name
    | throw .packet
  match obligation with
  | .readout | .preparation =>
    -- These component formats carry their own checked visit budgets.
    if work != exactWorkLimit then throw .packet
  | _ => pure ()
  return ⟨obligation, work, bytes.extract packetStart bytes.size⟩

def check (request : Request) :
    Except Gate.Error (NativeContext.Decision request.obligation) × Nat :=
  (NativeContext.run request.obligation productVersion request.packet).run request.work

def resultLines (requestBytes : ByteArray) (lines : List String) : List String :=
  "qleisli.native-result 4" :: RequestDigest.sha256 requestBytes :: lines

def reply (bytes : ByteArray) : NativeContext.Reply :=
  match read bytes with
  | .error error =>
    ⟨false, resultLines bytes ["error", NativeContext.Mode.errorCode .ordinary error]⟩
  | .ok request =>
    let (result,left) := check request
    match result with
    | .error (.native (.arithmetic .workLimit)) => ⟨false, resultLines bytes ["error", "limit"]⟩
    | _ =>
      let inner := NativeContext.reply request.obligation request.work result left
      ⟨inner.success, resultLines bytes inner.lines.tail⟩

/-- Successful checking uses the exact selected packet and original checked
ordinary/source obligations. A reply digest grants no decision. -/
theorem source_binding (request : Request)
    (decision : NativeContext.Decision request.obligation) (left : Nat)
    (source : request.obligation ≠ .openQasmPlacement)
    (ok : check request = (.ok decision,left)) :
    ∃ input, Packet.read request.packet = .ok input ∧
      decision.edition = input.edition ∧ decision.scope = input.scope ∧
      (NativeContext.check request.obligation request.packet).run request.work =
        (.ok decision.value,left) ∧
      NativeContext.scope request.obligation decision.value = input.scope := by
  obtain ⟨input, parsed, _, edition, scope, checked, checkedScope⟩ :=
    NativeContext.run_binding request.obligation productVersion request.packet decision
      request.work left source ok
  exact ⟨input, parsed, edition, scope, checked, checkedScope⟩

end QleisliKernel.Protocol.VerificationRequest
