import QleisliKernel.Hierarchy

/-! Unproved transport adapter for the existing experimental profiles.
Inputs remain untrusted until checked by the independently specified pure kernel.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

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

namespace Internal

def decimal (text : String) (bound : Nat) : Except Error Nat := do
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

def summary (tag line : String) : Except Error Summary := do
  match line.splitOn " " with
  | [actualTag, flip, phase0, phase1] =>
    if actualTag != tag then throw .syntax
    let bit ← decimal flip 1
    let p0 ← decimal phase0 255
    let p1 ← decimal phase1 255
    return { flip := bit == 1, phase0 := p0, phase1 := p1 }
  | _ => throw .syntax

/-- Byte and alphabet checks precede every textual profile's header checks. -/
def checkText (text : String) : Except Error Unit := do
  if text.utf8ByteSize > maxInputBytes then throw .limit
  if !(text.toList.all (fun c => c == '\n' || (' ' ≤ c && c ≤ '~'))) then
    throw .syntax

/-- Strict header and trailing-LF framing shared by DAG and layout profiles. -/
def framedLines (expected text : String) : Except Error (List String) := do
  checkText text
  match text.splitOn "\n" with
  | h :: rest =>
    if h != expected then throw .syntax
    match rest.reverse with
    | "" :: lines => return lines.reverse
    | _ => throw .syntax
  | _ => throw .syntax

end Internal
open Internal

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
  Internal.checkText text
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
open QleisliKernel.Protocol.Internal
open QleisliKernel.Dag QleisliKernel.Hierarchy

def header : String := "qleisli.phase-dag 1 phase256-dag-v1"

structure Artifact where
  definitions : List Definition
  entry : Nat

private def envelope (text : String) : Except Error (List String) :=
  Internal.framedLines header text

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
