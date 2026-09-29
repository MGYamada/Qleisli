import QleisliKernel.Hierarchy
import QleisliKernel.Layout
import QleisliKernel.LayoutDag
import QleisliKernel.PhaseLayout

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
