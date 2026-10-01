import QleisliKernel.Raw.Finite
import QleisliKernel.Semantics.Protected

/-! Evaluate original protected uses on source-selected local amplitudes.
No auxiliary matrix or recursively expanded dependency circuit is constructed.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.ProtectedEvaluation
open Semantics.Exact Semantics.Finite Semantics.Raw Finite

abbrev State := Nat → WorkM Scalar

def phaseValue (exponent : Nat) : Scalar := Exact.Scalar.phase exponent

def multiply (value factor : Scalar) : WorkM Scalar :=
  lift (arithmetic (Exact.Scalar.mul value factor))

def gate (operation : Gate) (axis : Nat) (state : State) (label : Nat) : WorkM Scalar := do
  exactWork (Exact.charge 1)
  match operation with
  | .x => state (label ^^^ 2^axis)
  | .z | .t =>
    let value ← state label
    multiply value (phaseValue (if bit label axis == 1 then (if operation == .z then 4 else 1) else 0))
  | .h =>
    let low := label - bit label axis * 2^axis
    let lowValue ← state low
    let highValue ← state (low+2^axis)
    let signed ← lift (arithmetic (if bit label axis == 1 then Exact.Scalar.neg highValue else .ok highValue))
    let combined ← lift (arithmetic (Exact.Scalar.add lowValue signed))
    multiply combined Finite.halfRoot

def use (source ancilla : Nat) (operation : Use) (state : State) (label : Nat) : WorkM Scalar := do
  exactWork (Exact.charge 1)
  match operation with
  | .protectedGate location operation =>
    guard (operation == .z || operation == .t)
    let value ← state label
    multiply value (phaseValue (if Semantics.Protected.value source ancilla location then
      (if operation == .z then 4 else 1) else 0))
  | .targetGate controls target operation =>
    if Semantics.Protected.enabled source ancilla controls then gate operation target state label else state label
  | .phase controls operation =>
    let value ← state label
    multiply value (phaseValue (if Semantics.Protected.enabled source ancilla controls then
      Semantics.Protected.phaseExponent operation else 0))

def run (source ancilla : Nat) (operations : List Use) (initial : State) : State :=
  operations.foldl (fun state operation => use source ancilla operation state) initial

def coefficient (sourceBits : Nat) (function : List Nat) (uses : List Use)
    (dimension index : Nat) : WorkM Scalar :=
  let row := index / dimension
  let col := index % dimension
  let source := row % 2^sourceBits
  if source == col % 2^sourceBits then
    run source (function[source]?.getD 0) uses
      (fun target => pure (if target == col / 2^sourceBits then Scalar.one else Scalar.zero))
      (row / 2^sourceBits)
  else pure Scalar.zero

def matrix (sourceBits dataBits ancillaBits : Nat) (function : List Nat) (uses : List Use) : WorkM Matrix := do
  guard (sourceBits ≤ dataBits && dataBits ≤ 6 && ancillaBits ≤ 12) .limit
  guard (tableValid sourceBits ancillaBits function false && usesValid sourceBits ancillaBits (dataBits-sourceBits) uses)
  let dimension := 2^dataBits
  exactWork (Exact.charge (dimension*dimension))
  let entries ← (List.range (dimension*dimension)).mapM (coefficient sourceBits function uses dimension)
  let actual ← lift (arithmetic (Exact.Matrix.make dimension dimension entries))
  wholeSpace actual
  return actual

def eventMatrix (dependencies : List Dependency) (event : Event) : WorkM Matrix := do
  match event with
  | .protectedComputed bits axes sourceBits ancillaBits function uses =>
    guard (bits ≤ 6) .limit
    let logical ← matrix sourceBits axes.length ancillaBits function uses
    promote bits axes logical
  | _ => Raw.eventMatrix dependencies event

def evolve (dependencies : List Dependency) (actual : Matrix) (event : Event) : WorkM Matrix := do
  let next ← eventMatrix dependencies event
  exactWork (Exact.Matrix.composeWork next actual)

def reconstruct (dependencies : List Dependency) (program : Program) : WorkM Matrix := do
  exactWork (Exact.charge (rawFields program))
  let prepared ← lift (prepare (dependencies.map (·.signature)) program)
  guard (prepared.inputBits ≤ 6 && prepared.state.frame.length ≤ 6) .limit
  let initial ← lift (arithmetic (Exact.Matrix.identity (2^prepared.inputBits)))
  let actual ← prepared.events.foldlM (evolve dependencies) initial
  let isometry ← exactWork (Exact.Matrix.isometryWork actual)
  guard isometry .notIsometric
  return actual

end QleisliKernel.Raw.ProtectedEvaluation
