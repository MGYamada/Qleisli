import Protocol.Core
import QleisliKernel.Hierarchical.Root
import QleisliKernel.Hierarchical.FourierRoot
import QleisliKernel.Hierarchical.Readout
import QleisliKernel.Hierarchical.Preparation
import QleisliKernel.Hierarchical.Instrument
import QleisliKernel.Hierarchical.QpeInstrument

/-! Unproved transport adapter for the existing experimental profiles.
Inputs remain untrusted until checked by the independently specified pure kernel.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Protocol.Hierarchical
open QleisliKernel.Hierarchical.Artifact

/-! Private bounded framing for the strict Rust external decoder. This total
transport decoder is outside the pure acceptance core. Its output is untrusted
until the actual whole-artifact checker runs; finite bytes remain obligations. -/

def maxBridgeBytes : Nat := 67108864

private structure Cursor where
  bytes : ByteArray
  position : Nat := 4
  remaining : Nat := 1000000

private abbrev DecodeM := StateT Cursor (Except Protocol.Error)

private def word : DecodeM Nat := do
  let s ← get
  if s.remaining == 0 then throw .limit
  if s.position + 4 > s.bytes.size then throw .syntax
  let n := s.bytes[s.position]!.toNat + 256 * s.bytes[s.position+1]!.toNat +
    65536 * s.bytes[s.position+2]!.toNat + 16777216 * s.bytes[s.position+3]!.toNat
  set { s with position := s.position + 4, remaining := s.remaining - 1 }
  return n

private def boolean : DecodeM Bool := do
  match ← word with
  | 0 => return false
  | 1 => return true
  | _ => throw .syntax

private def block (limit : Nat) : DecodeM ByteArray := do
  let size ← word
  let s ← get
  if size > limit then throw .limit
  if s.position + size > s.bytes.size then throw .syntax
  set { s with position := s.position + size }
  return s.bytes.extract s.position (s.position + size)

private def bytes : DecodeM ByteArray := block 16777216

private def array {α : Type} (read : DecodeM α) : DecodeM (Array α) := do
  let size ← word
  if size > 100000 || size > (← get).remaining then throw .limit
  let mut result := #[]
  for _ in [:size] do result := result.push (← read)
  return result

private def basis : DecodeM Basis := array do
  match ← word with
  | 0 => return .unit
  | 1 => return .bit
  | 2 => return .bits (← word)
  | 3 => return .tuple (← word)
  | _ => throw .syntax

private def side : DecodeM Side := do
  let quantum ← array do
    return (⟨← word, ← basis, ← array word⟩ : QuantumPort)
  let classical ← array do
    return (⟨← word, ← basis⟩ : ClassicalPort)
  return ⟨quantum,classical⟩

private def interface : DecodeM Interface := do return ⟨← side, ← side⟩
private def portMap : DecodeM PortMap := do return ⟨← array word, ← array word, ← array word⟩

private def structural : DecodeM StructuralOp := do
  match ← word with
  | 0 => return .takeBit (← word) (← word)
  | 1 => return .putBit (← word) (← word)
  | 2 => return .splitTuple
  | 3 => return .joinTuple
  | 4 => return .bitToBits
  | 5 => return .bitsToBit
  | 6 => return .packUnit
  | 7 => return .unpackUnit
  | 8 => return .packEmptyBits
  | 9 => return .unpackEmptyBits
  | _ => throw .syntax

private def body : DecodeM Body := do
  match ← word with
  | 0 => return .leaf (← bytes)
  | 1 => return .sequence (← array word)
  | 2 => return .tensor (← word) (← word)
  | 3 => return .call (← word) (← portMap) (← portMap)
  | 4 => return .repeatOp (← word) (← word)
  | 5 => return .inverse (← word)
  | 6 => return .control (← word) (← boolean)
  | 7 => return .rewire (← portMap)
  | 8 => return .structural (← structural)
  | 9 => return .dyadicPhase (← word) (← word) (← word)
  | 10 => return .computed (← word) (← word) (← word) (← word)
  | 11 => return .observeZ (← word) (← word)
  | 12 => return .init0 (← word)
  | _ => throw .syntax

private def definition : DecodeM Definition := do
  let header ← interface
  let effect ← match ← word with
    | 0 => pure Effect.unitary
    | 1 => pure Effect.iso
    | 2 => pure Effect.observe
    | _ => throw .syntax
  return ⟨header,effect,← body⟩

private def meaningBody : DecodeM MeaningBody := do
  match ← word with
  | 0 => return .identity
  | 1 => return .finite (← bytes)
  | 2 => return .sequence (← array word)
  | 3 => return .tensor (← word) (← word)
  | 4 => return .inverse (← word)
  | 5 => return .control (← word) (← boolean)
  | 6 => return .power (← word) (← word)
  | 7 => return .rewire (← portMap)
  | 8 => return .structural (← structural)
  | 9 => return .phase (← word) (← word)
  | 10 => return .qft (← word)
  | 11 => return .qpeInstrument (← word) (← word) (← word)
  | _ => throw .syntax

private def meaning : DecodeM Meaning := do return ⟨← interface, ← meaningBody⟩

private def encodingBody : DecodeM EncodingBody := do
  match ← word with
  | 0 => return .identity
  | 1 => return .tensor (← word) (← word)
  | 2 => return .rewire (← word) (← portMap)
  | 3 => return .zeroScratch (← word) (← word)
  | _ => throw .syntax

private def encoding : DecodeM Encoding := do return ⟨← side, ← side, ← encodingBody⟩

private def rule : DecodeM Rule := do
  match ← word with
  | 0 => return .finite
  | 1 => return .sequence
  | 2 => return .tensor
  | 3 => return .inverse
  | 4 => return .control
  | 5 => return .repeatOp
  | 6 => return .associativity
  | 7 => return .rewire
  | 8 => return .structural
  | 9 => return .phase
  | 10 => return .computed
  | 11 => return .conjugation
  | _ => throw .syntax  -- External schema entries remain disabled.

private def reference : DecodeM Ref := do
  let table ← match ← word with
    | 0 => pure Table.definition
    | 1 => pure Table.meaning
    | 2 => pure Table.encoding
    | 3 => pure Table.proof
    | _ => throw .syntax
  return ⟨table,← word⟩

private def proof : DecodeM Proof := do
  let kind ← match ← word with
    | 0 => pure Kind.equation
    | 1 => pure Kind.instrument
    | _ => throw .syntax
  let rule ← rule
  let premises ← array word
  let implementation ← word
  let meaning ← word
  let inputEncoding ← word
  let outputEncoding ← word
  let witness : Witness := ⟨← word, ← array word, ← array reference⟩
  return ⟨kind,rule,premises,implementation,meaning,inputEncoding,outputEncoding,witness⟩

/-- Decode complete tables and a proposed schedule, rejecting trailing data.
This never executes embedded strings and issues no evidence or acceptance. -/
private def parseBudget (input : ByteArray) (remaining : Nat) :
    Except Protocol.Error ((QleisliKernel.Hierarchical.Artifact.Artifact × Array Nat) × Nat) := do
  if input.size > maxBridgeBytes then throw .limit
  if input.size < 4 || input.extract 0 4 != "QLH1".toUTF8 then throw .syntax
  let read : DecodeM (QleisliKernel.Hierarchical.Artifact.Artifact × Array Nat) := do
    let definitions ← array definition
    let meanings ← array meaning
    let encodings ← array encoding
    let proofs ← array proof
    let entry : Entry := ⟨← word,← word⟩
    let order ← array word
    return (⟨definitions,meanings,encodings,proofs,entry⟩,order)
  let (result,final) ← read.run { bytes := input, remaining := remaining }
  if final.position != input.size then throw .syntax
  return (result,final.remaining)

def parse (input : ByteArray) : Except Protocol.Error (QleisliKernel.Hierarchical.Artifact.Artifact × Array Nat) :=
  (parseBudget input 1000000).map Prod.fst

/-- Separate caller request and untrusted pairing proposal. -/
structure RootPacket where
  artifact : QleisliKernel.Hierarchical.Artifact.Artifact
  order : Array Nat
  request : QleisliKernel.Hierarchical.Root.Request
  pairs : Array QleisliKernel.Hierarchical.Root.Pair
  pairOrder : Array Nat

private def parseRequestBudget (input : ByteArray) (remaining : Nat) (shared : Bool) :
    Except Protocol.Error (RootPacket × Nat) := do
  if input.size > maxBridgeBytes then throw .limit
  if input.size < 4 || input.extract 0 4 != "QLR1".toUTF8 then throw .syntax
  let read : DecodeM RootPacket := do
    let encoded ← block maxBridgeBytes
    let cursor ← get
    let allowance := if shared then cursor.remaining else 1000000
    let ((artifact,order),left) ← match parseBudget encoded allowance with
      | .error e => throw e
      | .ok result => pure result
    if shared then modify fun cursor => {cursor with remaining := left}
    let kind ← match ← word with
      | 0 => pure Kind.equation
      | 1 => pure Kind.instrument
      | _ => throw .syntax
    let effect ← match ← word with
      | 0 => pure Effect.unitary
      | 1 => pure Effect.iso
      | 2 => pure Effect.observe
      | _ => throw .syntax
    let request : QleisliKernel.Hierarchical.Root.Request :=
      ⟨kind,effect,← interface,← array meaning,← word⟩
    let pairs ← array do
      return (⟨← word,← word,← array word⟩ : QleisliKernel.Hierarchical.Root.Pair)
    return ⟨artifact,order,request,pairs,← array word⟩
  let (result,final) ← read.run { bytes := input, remaining := remaining }
  if final.position != input.size then throw .syntax
  return (result,final.remaining)

def parseRequest (input : ByteArray) : Except Protocol.Error RootPacket :=
  (parseRequestBudget input 1000000 false).map Prod.fst

/-- Canonical singleton Fourier request framing. The full independent interface
is transported twice, as in the external named meaning, and must agree. This
decoder is outside the pure acceptance core; its result remains untrusted. -/
structure FourierPacket where
  artifact : QleisliKernel.Hierarchical.Artifact.Artifact
  order : Array Nat
  request : QleisliKernel.Hierarchical.FourierRoot.Request
  wiringOrder : Array Nat

def parseFourier (input : ByteArray) : Except Protocol.Error FourierPacket := do
  if input.size > maxBridgeBytes then throw .limit
  if input.size < 4 || input.extract 0 4 != "QLF1".toUTF8 then throw .syntax
  let read : DecodeM FourierPacket := do
    let encoded ← block maxBridgeBytes
    let (artifact,order) ← match parse encoded with
      | .error e => throw e
      | .ok result => pure result
    if (← word) != 0 || (← word) != 0 then throw .syntax
    let header ← interface
    let meanings ← array meaning
    if (← word) != 0 || meanings.size != 1 then throw .syntax
    let some m := meanings[0]? | throw .syntax
    if m.interface != header then throw .syntax
    let .qft width := m.body | throw .syntax
    return ⟨artifact,order,⟨width,header⟩,← array word⟩
  let (result,final) ← read.run { bytes := input }
  if final.position != input.size then throw .syntax
  return result

/-- Additive internal readout framing. The request is supplied independently
by the caller; it is never inferred from the proposed measurement nodes. -/
structure ReadoutPacket where
  request : QleisliKernel.Hierarchical.Readout.Request
  packet : QleisliKernel.Hierarchical.Readout.Packet
  budget : Nat

def parseReadout (input : ByteArray) : Except Protocol.Error ReadoutPacket := do
  if input.size > maxBridgeBytes then throw .limit
  if input.size < 4 || input.extract 0 4 != "QLM1".toUTF8 then throw .syntax
  let read : DecodeM ReadoutPacket := do
    let request : QleisliKernel.Hierarchical.Readout.Request := ⟨← side, ← array word, ← word⟩
    let packet : QleisliKernel.Hierarchical.Readout.Packet := ⟨← array definition, ← array word, ← side⟩
    return ⟨request, packet, ← word⟩
  let (result, final) ← read.run { bytes := input }
  if final.position != input.size then throw .syntax
  return result

structure PreparationPacket where
  request : QleisliKernel.Hierarchical.Preparation.Request
  packet : QleisliKernel.Hierarchical.Preparation.Packet
  budget : Nat

/-- Separate explicit fresh-zero request, actual init nodes and work budget.
No field is a submitted success flag or an asserted initial quantum state. -/
def parsePreparation (input : ByteArray) : Except Protocol.Error PreparationPacket := do
  if input.size > maxBridgeBytes then throw .limit
  if input.size < 4 || input.extract 0 4 != "QLZ1".toUTF8 then throw .syntax
  let read : DecodeM PreparationPacket := do
    let inputs ← side
    let fresh ← side
    if !fresh.classical.isEmpty then throw .syntax
    let request : QleisliKernel.Hierarchical.Preparation.Request := ⟨inputs, fresh.quantum⟩
    let packet : QleisliKernel.Hierarchical.Preparation.Packet := ⟨← array definition, ← side⟩
    return ⟨request, packet, ← word⟩
  let (result, final) ← read.run { bytes := input }
  if final.position != input.size then throw .syntax
  return result

structure InstrumentPacket where
  request : QleisliKernel.Hierarchical.Instrument.Request
  packet : QleisliKernel.Hierarchical.Instrument.Packet

/-- The new composite frame shares its word allowance with both nested root
and artifact frames. Existing standalone transports retain their contracts. -/
def parseInstrument (input : ByteArray) : Except Protocol.Error InstrumentPacket := do
  if input.size > maxBridgeBytes then throw .limit
  if input.size < 4 || input.extract 0 4 != "QLI1".toUTF8 then throw .syntax
  let read : DecodeM InstrumentPacket := do
    let encoded ← block maxBridgeBytes
    let (root,left) ← match parseRequestBudget encoded (← get).remaining true with
      | .error error => throw error
      | .ok result => pure result
    modify fun cursor => {cursor with remaining := left}
    let inputs ← side
    let fresh ← side
    if !fresh.classical.isEmpty then throw .syntax
    let initialization : QleisliKernel.Hierarchical.Preparation.Packet := ⟨← array definition,← side⟩
    let readoutRequest : QleisliKernel.Hierarchical.Readout.Request := ⟨← side,← array word,← word⟩
    let readout : QleisliKernel.Hierarchical.Readout.Packet := ⟨← array definition,← array word,← side⟩
    let request : QleisliKernel.Hierarchical.Instrument.Request :=
      ⟨⟨inputs,fresh.quantum⟩,root.request,readoutRequest,← side⟩
    return ⟨request,⟨initialization,root.artifact,root.order,root.pairs,root.pairOrder,readout⟩⟩
  let (result,final) ← read.run {bytes := input}
  if final.position != input.size then throw .syntax
  return result

structure QpeInstrumentPacket where
  request : QleisliKernel.Hierarchical.QpeInstrument.Request
  packet : QleisliKernel.Hierarchical.QpeInstrument.Packet

/-- Private named-QPE framing. The nested root carries the independent provider
request; restore the original circuit entry before fresh whole-artifact checking.
Every nested frame and candidate field shares the same decoder allowance. -/
def parseQpeInstrument (input : ByteArray) : Except Protocol.Error QpeInstrumentPacket := do
  if input.size > maxBridgeBytes then throw .limit
  if input.size < 4 || input.extract 0 4 != "QLQ1".toUTF8 then throw .syntax
  let read : DecodeM QpeInstrumentPacket := do
    let encoded ← block maxBridgeBytes
    let (provider,left) ← match parseRequestBudget encoded (← get).remaining true with
      | .error error => throw error
      | .ok result => pure result
    modify fun cursor => {cursor with remaining := left}
    let entry : Entry := ⟨← word,← word⟩
    let circuit : QleisliKernel.Hierarchical.QpeSchedule.Request :=
      ⟨← interface,← array word,← array word,← array word,← word⟩
    let atom : DecodeM QleisliKernel.Hierarchical.CircuitTrace.Atom := do
      return ⟨← word,← interface⟩
    let candidate : QleisliKernel.Hierarchical.QpeSchedule.Candidate :=
      ⟨← array atom,← array atom,← atom,← array word,← array (array word),← array word⟩
    let root : QleisliKernel.Hierarchical.QpeRoot.Packet :=
      ⟨{provider.artifact with entry := entry},provider.order,provider.artifact.entry.proof,
        provider.pairs,provider.pairOrder,candidate⟩
    let inputs ← side
    let fresh ← side
    if !fresh.classical.isEmpty then throw .syntax
    let initialization : QleisliKernel.Hierarchical.Preparation.Packet := ⟨← array definition,← side⟩
    let readoutRequest : QleisliKernel.Hierarchical.Readout.Request := ⟨← side,← array word,← word⟩
    let readout : QleisliKernel.Hierarchical.Readout.Packet := ⟨← array definition,← array word,← side⟩
    let request : QleisliKernel.Hierarchical.QpeInstrument.Request :=
      ⟨⟨inputs,fresh.quantum⟩,⟨circuit,provider.request⟩,readoutRequest,← side⟩
    return ⟨request,⟨initialization,root,readout⟩⟩
  let (result,final) ← read.run {bytes := input}
  if final.position != input.size then throw .syntax
  return result

end QleisliKernel.Protocol.Hierarchical
