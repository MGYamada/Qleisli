import Protocol.Core
import QleisliKernel.LayoutDag
import QleisliKernel.PhaseLayout

/-! Unproved transport adapter for the existing experimental profiles.
Inputs remain untrusted until checked by the independently specified pure kernel.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

open QleisliKernel.Protocol.Internal

namespace QleisliKernel.Protocol.Layout
open QleisliKernel.Layout

structure Artifact where
  layout : Rewire
  witness : Witness

private def envelope (expected text : String) : Except Error (List String) :=
  Internal.framedLines expected text

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
