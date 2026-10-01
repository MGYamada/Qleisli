import QleisliKernel.Hierarchy
import QleisliKernel.Finite
import Lean.Data.Json.Parser
import QleisliKernel.Layout
import QleisliKernel.LayoutDag
import QleisliKernel.PhaseLayout
import QleisliKernel.Hierarchical.Root
import QleisliKernel.Hierarchical.FourierRoot
import QleisliKernel.Hierarchical.Readout
import QleisliKernel.Hierarchical.Preparation
import QleisliKernel.Hierarchical.Instrument
import QleisliKernel.Hierarchical.QpeInstrument

/-
Copyright 2026 Masahiko G. Yamada.
Licensed under the Apache License, Version 2.0; see the repository LICENSE.

This deliberately small experimental wire protocol is not QIRF or a general
IR decoder. Parsing is an unproved adapter; the corresponding pure checker
determines acceptance of each experimental profile.
-/

namespace QleisliKernel.Protocol

def maxInputBytes : Nat := 65536

def header : String := "qleisli.phase-word 1 phase256-word-v1"

def interfaceLine : String := "Bit->Bit"

inductive Error where
  | syntax
  | limit
  deriving BEq, Repr

structure Artifact where
  word : Word
  claimed : Summary

private def decimal (text : String) (bound : Nat) : Except Error Nat := do
  if text.isEmpty || !(text.toList.all Char.isDigit) then
    throw .syntax
  if text.length > 1 && text.startsWith "0" then
    throw .syntax
  -- Every protocol integer is at most 4096. Refuse long decimal strings
  -- before allocating arbitrary-precision values for their numeric contents.
  if text.length > 4 then
    throw .limit
  match text.toNat? with
  | none => throw .syntax
  | some value =>
    if value > bound then throw .limit
    return value

private def summary (tag line : String) : Except Error Summary := do
  match line.splitOn " " with
  | [actualTag, flip, phase0, phase1] =>
    if actualTag != tag then throw .syntax
    let bit ← decimal flip 1
    let p0 ← decimal phase0 255
    let p1 ← decimal phase1 255
    return { flip := bit == 1, phase0 := p0, phase1 := p1 }
  | _ => throw .syntax

private def gate (line : String) : Except Error Gate := do
  match line.splitOn " " with
  | ["x"] => return .x
  | ["phase", ticks] => return .phase (← decimal ticks 255)
  | _ => throw .syntax

private def gates (lines : List String) : Except Error Word := do
  -- The final empty split component requires a trailing LF. Folding the
  -- remaining reversed lines reconstructs execution order without a project
  -- recursive declaration or a compiler-generated partial replacement.
  match lines.reverse with
  | "" :: rest =>
    rest.foldlM (fun result line => do return (← gate line) :: result) []
  | _ => throw .syntax

private def envelope (text : String) : Except Error (List String) := do
  if text.utf8ByteSize > maxInputBytes then throw .limit
  -- LF and printable ASCII are the entire alphabet. In particular CR, NUL,
  -- tabs, Unicode separators, and a byte-order mark are never normalized.
  if !(text.toList.all (fun c => c == '\n' || (' ' ≤ c && c ≤ '~'))) then
    throw .syntax
  match text.splitOn "\n" with
  | h :: interface :: rest =>
    if h != header || interface != interfaceLine then throw .syntax
    return rest
  | _ => throw .syntax

/-- Parse an exact LF-terminated `.qpk` artifact, with no ignored fields. -/
def parseArtifact (text : String) : Except Error Artifact := do
  match ← envelope text with
  | claim :: count :: lines =>
    let claimed ← summary "claim" claim
    let expectedLength ← decimal count 4096
    if lines.length != expectedLength + 1 then throw .syntax
    let word ← gates lines
    return { word, claimed }
  | _ => throw .syntax

/-- Parse the client's independent, exact LF-terminated `.qpr` requirement. -/
def parseRequirement (text : String) : Except Error Summary := do
  match ← envelope text with
  | [expected, ""] => summary "expect" expected
  | _ => throw .syntax

end QleisliKernel.Protocol

namespace QleisliKernel.Protocol.Dag
open QleisliKernel.Dag QleisliKernel.Hierarchy

def header : String := "qleisli.phase-dag 1 phase256-dag-v1"

structure Artifact where
  definitions : List Definition
  entry : Nat

private def envelope (text : String) : Except Error (List String) := do
  if text.utf8ByteSize > maxInputBytes then throw .limit
  if !(text.toList.all (fun c => c == '\n' || (' ' ≤ c && c ≤ '~'))) then
    throw .syntax
  match text.splitOn "\n" with
  | h :: rest =>
    if h != header then throw .syntax
    match rest.reverse with
    | "" :: lines => return lines.reverse
    | _ => throw .syntax
  | _ => throw .syntax

private def shape : String → Except Error Shape
  | "Unit" => .ok .unit
  | "Bit" => .ok .bit
  | "Bits0" => .ok .bits0
  | "Bits1" => .ok .bits1
  | _ => .error .syntax

private def naturalList (texts : List String) : Except Error (List Nat) :=
  texts.mapM (fun text => decimal text 4096)

private def leafGate (text : String) : Except Error Gate := do
  if text == "x" then return .x
  if text.startsWith "p" then
    return .phase (← decimal (text.drop 1).toString 255)
  throw .syntax

private def instruction : List String → Except Error Instruction
  | "leaf" :: length :: gates => do
    let count ← decimal length 4096
    if gates.length != count then throw .syntax
    return .leaf (← gates.mapM leafGate)
  | ["repeat", count, body] => do
    return .repeatOp (← decimal count 4096) (← decimal body 255)
  | "sequence" :: length :: children => do
    let count ← decimal length 4096
    if children.length != count then throw .syntax
    return .sequence (← naturalList children)
  | "call" :: body :: inputs :: rest => do
    let definition ← decimal body 255
    let inputCount ← decimal inputs 4096
    if rest.length < inputCount then throw .syntax
    let (input, remaining) := rest.splitAt inputCount
    match remaining with
    | outputs :: output =>
      let outputCount ← decimal outputs 4096
      if output.length != outputCount then throw .syntax
      return .call definition (← naturalList input) (← naturalList output)
    | _ => throw .syntax
  | _ => .error .syntax

private def definition (line : String) : Except Error Definition := do
  match line.splitOn " " with
  | type :: flip :: phase0 :: phase1 :: body =>
    let interface ← shape type
    let claimed ← summary "claim" ("claim " ++ flip ++ " " ++ phase0 ++ " " ++ phase1)
    return ⟨interface, ← instruction body, claimed⟩
  | _ => throw .syntax

/-- Strict transport for the bounded composition slice; no unknown rule is enabled. -/
def parseArtifact (text : String) : Except Error Artifact := do
  match ← envelope text with
  | entryLine :: countLine :: definitions =>
    match entryLine.splitOn " ", countLine.splitOn " " with
    | ["entry", entry], ["nodes", count] =>
      let root ← decimal entry 255
      let count ← decimal count 256
      if definitions.length != count then throw .syntax
      return ⟨← definitions.mapM definition, root⟩
    | _, _ => throw .syntax
  | _ => throw .syntax

def parseRequirement (text : String) : Except Error Request := do
  match ← envelope text with
  | [interface, expected] =>
    return ⟨← shape interface, ← summary "expect" expected⟩
  | _ => throw .syntax

end QleisliKernel.Protocol.Dag

namespace QleisliKernel.Protocol.Layout
open QleisliKernel.Layout

structure Artifact where
  layout : Rewire
  witness : Witness

private def envelope (expected text : String) : Except Error (List String) := do
  if text.utf8ByteSize > maxInputBytes then throw .limit
  if !(text.toList.all (fun c => c == '\n' || (' ' ≤ c && c ≤ '~'))) then
    throw .syntax
  match text.splitOn "\n" with
  | h :: rest =>
    if h != expected then throw .syntax
    match rest.reverse with
    | "" :: lines => return lines.reverse
    | _ => throw .syntax
  | _ => throw .syntax

private def countLine (tag : String) (limit : Nat) (line : String) : Except Error Nat := do
  match line.splitOn " " with
  | [actual, count] =>
    if actual != tag then throw .syntax
    decimal count limit
  | _ => throw .syntax

private def indices (tag : String) (limit : Nat) (line : String) : Except Error (List Nat) := do
  match line.splitOn " " with
  | actual :: length :: items =>
    if actual != tag then throw .syntax
    let count ← decimal length limit
    if items.length != count then throw .syntax
    items.mapM (fun text => decimal text 4096)
  | _ => throw .syntax

private def atom (text : String) : Except Error TypeAtom := do
  if text == "Unit" then return .unit
  if text == "Bit" then return .bit
  if text.startsWith "Bits" then return .bits (← decimal (text.drop 4).toString 4096)
  if text.startsWith "t" then return .tuple (← decimal (text.drop 1).toString 4096)
  throw .syntax

private def port (line : String) : Except Error Port := do
  match line.splitOn " " with
  | "port" :: length :: rest =>
    let count ← decimal length 128
    if rest.length ≤ count then throw .syntax
    let basis ← (rest.take count).mapM atom
    let width :: axes := rest.drop count | throw .syntax
    let bits ← decimal width 16
    if axes.length != bits then throw .syntax
    return ⟨basis, ← axes.mapM (fun text => decimal text 4096)⟩
  | _ => throw .syntax

private def interface (tag : String) (lines : List String) :
    Except Error (Interface × List String) := do
  let first :: rest := lines | throw .syntax
  let count ← countLine tag 64 first
  if rest.length < count then throw .syntax
  return (← (rest.take count).mapM port, rest.drop count)

private def rewire (lines : List String) : Except Error (Rewire × List String) := do
  let (inputs, rest) ← interface "inputs" lines
  let (outputs, rest) ← interface "outputs" rest
  let owners :: axes :: rest := rest | throw .syntax
  return (⟨inputs, outputs, ← indices "owners" 64 owners, ← indices "axes" 16 axes⟩, rest)

def parseArtifact (text : String) : Except Error Artifact := do
  let lines ← envelope "qleisli.layout 1 typed-layout-v1" text
  let (layout, rest) ← rewire lines
  match rest with
  | [owners, axes] =>
    return ⟨layout, ⟨← indices "inverse_owners" 64 owners, ← indices "inverse_axes" 16 axes⟩⟩
  | _ => throw .syntax

def parseRequirement (text : String) : Except Error Rewire := do
  let lines ← envelope "qleisli.layout-request 1 typed-layout-v1" text
  let (layout, rest) ← rewire lines
  if !rest.isEmpty then throw .syntax
  return layout

end QleisliKernel.Protocol.Layout

namespace QleisliKernel.Protocol.LayoutDag
open QleisliKernel.LayoutDag

structure Artifact where
  entry : Nat
  definitions : List Definition

private def certified (lines : List String) : Except Error (Certified × List String) := do
  let (layout, rest) ← Layout.rewire lines
  let owners :: axes :: rest := rest | throw .syntax
  return (⟨layout, ⟨← Layout.indices "inverse_owners" 64 owners,
    ← Layout.indices "inverse_axes" 16 axes⟩⟩, rest)

private def definition (lines : List String) : Except Error (Definition × List String) := do
  let first :: rest := lines | throw .syntax
  match first.splitOn " " with
  | ["leaf"] =>
    let (result, rest) ← certified rest
    return (⟨.leaf result.layout, result⟩, rest)
  | ["call", child] =>
    let child ← decimal child 255
    let (input, rest) ← certified rest
    let (output, rest) ← certified rest
    let (result, rest) ← certified rest
    return (⟨.call child input output, result⟩, rest)
  | ["then", first, second] =>
    let first ← decimal first 255
    let second ← decimal second 255
    let (result, rest) ← certified rest
    return (⟨.then first second, result⟩, rest)
  | _ => throw .syntax

def parseArtifact (text : String) : Except Error Artifact := do
  let lines ← Layout.envelope "qleisli.layout-dag 1 typed-layout-dag-v1" text
  let entry :: count :: rest := lines | throw .syntax
  let entry ← Layout.countLine "entry" 255 entry
  let count ← Layout.countLine "definitions" 256 count
  let mut remaining := rest
  let mut definitions := #[]
  for _ in List.range count do
    let (next, rest) ← definition remaining
    definitions := definitions.push next
    remaining := rest
  if !remaining.isEmpty then throw .syntax
  return ⟨entry, definitions.toList⟩

end QleisliKernel.Protocol.LayoutDag

namespace QleisliKernel.Protocol.PhaseLayout
open QleisliKernel.PhaseLayout QleisliKernel.PhasePolynomial

structure Artifact where
  entry : Nat
  definitions : List Definition

private def term (line : String) : Except Error Term := do
  match line.splitOn " " with
  | "term" :: ticks :: count :: axes =>
    let ticks ← decimal ticks 255
    let count ← decimal count 16
    if axes.length != count then throw .syntax
    return ⟨← axes.mapM (fun axis => decimal axis 15), ticks⟩
  | _ => throw .syntax

private def polynomial (tag : String) (lines : List String) :
    Except Error (Polynomial × List String) := do
  let first :: rest := lines | throw .syntax
  let count ← Layout.countLine tag 128 first
  if rest.length < count then throw .syntax
  return (← (rest.take count).mapM term, rest.drop count)

def parseArtifact (text : String) : Except Error Artifact := do
  let lines ← Layout.envelope "qleisli.phase-layout 1 typed-phase256-dag-v1" text
  let entry :: count :: rest := lines | throw .syntax
  let entry ← Layout.countLine "entry" 255 entry
  let count ← Layout.countLine "definitions" 256 count
  let mut remaining := rest
  let mut definitions := #[]
  for _ in List.range count do
    let (wiring, rest) ← LayoutDag.definition remaining
    let (source, rest) ← polynomial "source_phases" rest
    let (claim, rest) ← polynomial "claim_phases" rest
    definitions := definitions.push ⟨wiring, source, claim⟩
    remaining := rest
  if !remaining.isEmpty then throw .syntax
  return ⟨entry, definitions.toList⟩

def parseRequirement (text : String) : Except Error QleisliKernel.PhaseLayout.Summary := do
  let lines ← Layout.envelope "qleisli.phase-layout-request 1 typed-phase256-dag-v1" text
  let (layout, rest) ← Layout.rewire lines
  let (phases, rest) ← polynomial "expect_phases" rest
  if !rest.isEmpty then throw .syntax
  return ⟨layout, phases⟩

end QleisliKernel.Protocol.PhaseLayout

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

/-! VM-24 experimental serialized-data adapter. This is not a production QIRF
extractor or a decoder-correspondence proof. The pure finite checker rereads all
canonical coefficients and reconstructs the circuit from its original steps. -/
namespace QleisliKernel.Protocol.FiniteCodec
open Lean QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite

inductive Frame where
  | object (keys : List String) (key : Bool) | array
  deriving Repr
inductive Mode where
  | outside | quote | escape | bare
  deriving BEq, Repr
structure Scan where
  mode : Mode := .outside
  literal : List Char := []
  stack : List Frame := []
  depth : Nat := 0
  count : Nat := 0
  deriving Repr

private def bare (literal : List Char) : Except String Unit := do
  let text := String.ofList literal.reverse
  if text == "true" || text == "false" || text == "null" then return
  if text.isEmpty || !text.toList.all Char.isDigit || text.length > 20 then
    throw "expected bounded unsigned integer"
  let some number := text.toNat? | throw "invalid integer"
  if number > 18446744073709551615 then throw "integer exceeds u64"

private def stringToken (scan : Scan) : Except String Scan := do
  let value ← Json.parse (String.ofList scan.literal.reverse)
  let text ← value.getStr?
  match scan.stack with
  | .object keys true :: rest =>
    if keys.contains text then throw "duplicate JSON field"
    if keys.length ≥ 64 then throw "too many object fields"
    return {scan with mode := .outside,literal := [],stack := .object (text::keys) false :: rest}
  | _ => return {scan with mode := .outside,literal := []}

private def punctuation (scan : Scan) (char : Char) : Except String Scan := do
  if char == '{' || char == '[' then
    if scan.depth ≥ 64 then throw "JSON depth exceeds 64"
    let frame := if char == '{' then Frame.object [] true else .array
    return {scan with stack := frame :: scan.stack,depth := scan.depth+1}
  if char == '}' || char == ']' then
    let _ :: rest := scan.stack | throw "unmatched JSON close"
    return {scan with stack := rest,depth := scan.depth-1}
  if char == ',' then
    match scan.stack with
    | .object keys _ :: rest => return {scan with stack := .object keys true :: rest}
    | _ => return scan
  return scan

private def outside (scan : Scan) (char : Char) : Except String Scan := do
  if char == '"' then return {scan with mode := .quote,literal := ['"']}
  if char == ' ' || char == '\n' || char == '\r' || char == '\t' then return scan
  if char == '{' || char == '}' || char == '[' || char == ']' || char == ',' || char == ':' then
    punctuation scan char
  else return {scan with mode := .bare,literal := [char]}

private def scanChar (scan : Scan) (char : Char) : Except String Scan := do
  if scan.count ≥ 16777216 then throw "JSON exceeds 16 MiB"
  let scan := {scan with count := scan.count+1}
  match scan.mode with
  | .outside => outside scan char
  | .escape => return {scan with mode := .quote,literal := char :: scan.literal}
  | .quote =>
    let scan := {scan with literal := char :: scan.literal}
    if char == '\\' then return {scan with mode := .escape}
    if char == '"' then stringToken scan else return scan
  | .bare =>
    if char == ',' || char == ':' || char == '}' || char == ']' ||
        char == ' ' || char == '\n' || char == '\r' || char == '\t' then
      bare scan.literal
      outside {scan with mode := .outside,literal := []} char
    else return {scan with literal := char :: scan.literal}

/-- Duplicate fields are rejected before Lean.Json's map insertion can erase them.
Numeric spelling, byte/depth bounds and full JSON framing are checked afresh. -/
def parse (text : String) : Except String Json := do
  if text.utf8ByteSize > 16777216 then throw "JSON exceeds 16 MiB"
  let scan ← text.toList.foldlM scanChar {}
  if scan.mode == .bare then bare scan.literal
  else if scan.mode != .outside then throw "unterminated JSON string"
  if !scan.stack.isEmpty then throw "unclosed JSON container"
  Json.parse text

private def fields (value : Json) (names : List String) : Except String Unit := do
  let object ← value.getObj?
  let actual := object.toList.map (·.1)
  if actual.length != names.length || !actual.all names.contains then throw "unexpected/missing JSON fields"

private def array (value : Json) : Except String (List Json) := return (← value.getArr?).toList
private def field (value : Json) (name : String) : Except String Json := value.getObjVal? name
private def nat (value : Json) : Except String Nat := value.getNat?

def matrixDescription (value : Json) : Except String MatrixDescription := do
  fields value ["format","version","domain","rows","cols","entries"]
  if (← (← field value "format").getStr?) != "qleisli.finite-matrix" ||
      (← nat (← field value "version")) != 1 ||
      (← (← field value "domain").getStr?) != "zeta8-dyadic-v1" then throw "unsupported exact matrix profile"
  let entries ← (← array (← field value "entries")).mapM fun entry => do
    (← array entry).mapM fun coefficient => do
      fields coefficient ["numerator","denominator_bits"]
      return ⟨← (← field coefficient "numerator").getStr?,← nat (← field coefficient "denominator_bits")⟩
  return ⟨← nat (← field value "rows"),← nat (← field value "cols"),entries⟩

def decodeMatrix (text : String) : Except String MatrixDescription := do
  matrixDescription (← parse text)

private def adapter {α : Type} (result : Except String α) : QleisliKernel.Finite.WorkM α :=
  QleisliKernel.Finite.lift (result.mapError (fun _ => .invalid))

/-- Read the published description under the same shared work ceiling. Nested
coefficient fields are inspected after the four-per-entry charge, as in Rust. -/
def readMatrixValue (value : Json) : QleisliKernel.Finite.WorkM Matrix := do
  let work ← get
  QleisliKernel.Finite.guard (work ≤ 10000000) .limit
  adapter (fields value ["format","version","domain","rows","cols","entries"])
  let profile ← adapter (do
    return (← (← field value "format").getStr?) == "qleisli.finite-matrix" &&
      (← nat (← field value "version")) == 1 &&
      (← (← field value "domain").getStr?) == "zeta8-dyadic-v1")
  QleisliKernel.Finite.guard profile
  let rows ← adapter (nat (← adapter (field value "rows")))
  let cols ← adapter (nat (← adapter (field value "cols")))
  QleisliKernel.Finite.guard (QleisliKernel.Exact.matrixValid rows cols) .limit
  let entries ← adapter (array (← adapter (field value "entries")))
  QleisliKernel.Finite.guard (entries.length == rows * cols)
  QleisliKernel.Finite.exactWork (QleisliKernel.Exact.charge (4 * entries.length))
  let values ← entries.mapM fun entry => do
    let coefficients ← adapter (array entry)
    QleisliKernel.Finite.guard (coefficients.length == 4)
    let descriptions ← adapter (coefficients.mapM fun coefficient => do
      fields coefficient ["numerator","denominator_bits"]
      return DyadicDescription.mk (← (← field coefficient "numerator").getStr?)
        (← nat (← field coefficient "denominator_bits")))
    QleisliKernel.Finite.lift (QleisliKernel.Finite.scalarRead descriptions)
  QleisliKernel.Finite.lift (QleisliKernel.Finite.arithmetic
    (QleisliKernel.Exact.Matrix.make rows cols values))

def readMatrix (text : String) : QleisliKernel.Finite.WorkM Matrix := do
  let work ← get
  QleisliKernel.Finite.guard (work ≤ 10000000) .limit
  readMatrixValue (← adapter (parse text))

/-- Private experimental prefix bridge; legacy type trees retain all atoms. -/
def basis (value : Json) : Except String Basis := do
  (← array value).mapM fun atom => do
    let text ← atom.getStr?
    if text == "unit" then return .unit
    if text == "bit" then return .bit
    if text == "pair" then return .pair
    let some arity := (text.drop 6).toString.toNat? | throw "invalid basis atom"
    if text != "tuple:" ++ toString arity then throw "invalid basis atom"
    return .tuple arity

private def nats (value : Json) : Except String (List Nat) := do (← array value).mapM nat

def circuit (value : Json) : Except String Circuit := do
  fields value ["basis","steps"]
  let steps ← (← array (← field value "steps")).mapM fun step => do
    fields step ["controls","action"]
    let controls ← (← array (← field step "controls")).mapM fun control => do
      fields control ["index","when_one"]
      return Control.mk (← nat (← field control "index")) (← (← field control "when_one").getBool?)
    let action ← field step "action"
    let tag ← (← field action "tag").getStr?
    let action ← if tag == "hadamard" then do
        fields action ["tag","target"]
        pure (Action.hadamard (← nat (← field action "target")))
      else if tag == "monomial" then do
        fields action ["tag","indices","permutation","phases"]
        pure (Action.monomial (← nats (← field action "indices"))
          (← nats (← field action "permutation")) (← nats (← field action "phases")))
      else if tag == "contract" then do
        fields action ["tag","indices","evidence","adjoint"]
        pure (Action.contract (← nats (← field action "indices"))
          (← nat (← field action "evidence")) (← (← field action "adjoint").getBool?))
      else throw "unknown finite action"
    pure ⟨controls,action⟩
  return ⟨← basis (← field value "basis"),steps⟩

def readEncoding (value : Json) : QleisliKernel.Finite.WorkM Encoding := do
  adapter (fields value ["logical","physical","map"])
  let logical ← adapter (basis (← adapter (field value "logical")))
  let physical ← adapter (basis (← adapter (field value "physical")))
  let map ← readMatrixValue (← adapter (field value "map"))
  pure ⟨logical,physical,map⟩

def readContract (value : Json) : QleisliKernel.Finite.WorkM Contract := do
  adapter (fields value ["input","output","logical"])
  let input ← readEncoding (← adapter (field value "input"))
  let output ← readEncoding (← adapter (field value "output"))
  let logical ← readMatrixValue (← adapter (field value "logical"))
  pure ⟨input,output,logical⟩

/-- Experimental complete finite-component data. This is deliberately not a
QIRF decoder, a source-binding receipt or a public production protocol. -/
def readArtifact (text : String) : QleisliKernel.Finite.WorkM QleisliKernel.Semantics.Finite.Artifact := do
  let value ← adapter (parse text)
  adapter (fields value ["format","version","root","evidence"])
  let profile ← adapter (do
    return (← (← field value "format").getStr?) == "qleisli.finite-component" &&
    (← nat (← field value "version")) == 1)
  QleisliKernel.Finite.guard profile
  let entries ← adapter (array (← adapter (field value "evidence")))
  QleisliKernel.Finite.guard (entries.length ≤ 65536) .limit
  let evidence ← entries.mapM fun entry => do
    adapter (fields entry ["circuit","claim"])
    let body ← adapter (circuit (← adapter (field entry "circuit")))
    let claim ← readContract (← adapter (field entry "claim"))
    pure (Evidence.mk body claim)
  let root ← adapter (nat (← adapter (field value "root")))
  pure ⟨evidence,root⟩

def readRequirement (text : String) : QleisliKernel.Finite.WorkM Contract := do
  readContract (← adapter (parse text))

end QleisliKernel.Protocol.FiniteCodec
