import QleisliKernel.Raw.ProtectedEvaluation

/-! Exact original-event action on coefficient functions. No global matrix or
auxiliary vector is constructed. Summation retains every basis coefficient and
uses shared charged arithmetic; exponential enumeration is not a scaling claim.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.Coefficient
open Semantics.Exact Semantics.Finite Semantics.Raw Finite
abbrev State := ProtectedEvaluation.State

def sum (count : Nat) (term : Nat → WorkM Scalar) : WorkM Scalar := do
  exactWork (Exact.charge count)
  (List.range count).foldlM (fun previous index => do
    let value ← term index
    lift (arithmetic (Exact.Scalar.add previous value))) Scalar.zero

def step (dependencies : List Dependency) (operation : Step) (state : State) (output : Nat) : WorkM Scalar := do
  exactWork (Exact.charge 1)
  if !enabled operation.controls output then state output else
    match operation.action with
    | .hadamard axis => ProtectedEvaluation.gate .h axis state output
    | .monomial axes permutation phases => sum permutation.length fun input => do
      if permutation[input]? == some (gather output axes) then
        ProtectedEvaluation.multiply (← state (scatter output axes input))
          (Exact.Scalar.phase (phases[input]?.getD 0))
      else pure Scalar.zero
    | .contract axes index adjoint => do
      let dependency ← lift (readOption dependencies[index]?)
      sum dependency.meaning.cols fun input => do
        let value ← state (scatter output axes input)
        let entry ← lift (arithmetic (if adjoint then Exact.Scalar.conjugate
          (dependency.meaning.entry input (gather output axes))
          else .ok (dependency.meaning.entry (gather output axes) input)))
        ProtectedEvaluation.multiply value entry

def circuit (dependencies : List Dependency) (steps : List Step) (state : State) : State :=
  steps.foldl (fun state operation => step dependencies operation state) state

def event (dependencies : List Dependency) (operation : Event) (state : State) (output : Nat) : WorkM Scalar := do
  exactWork (Exact.charge 1)
  match operation with
  | .circuit _ steps => circuit dependencies steps state output
  | .init0 bits => if output < 2^bits then state output else pure Scalar.zero
  | .liftBasis before _ inputAxes outputAxes table => sum (2^before) (fun input =>
      if scatter input outputAxes (table[gather input inputAxes]?.getD 0) == output then state input else pure Scalar.zero)
  | .reorder bits axes => sum (2^bits) (fun input =>
      if gather input axes == output then state input else pure Scalar.zero)
  | .computed _ axes sourceBits ancillaBits function uses _ =>
    let localInput : State := fun input =>
      if input < 2^axes.length then state (scatter output axes input) else pure Scalar.zero
    circuit dependencies
      ([computeStep sourceBits axes.length ancillaBits function] ++ uses ++
        [computeStep sourceBits axes.length ancillaBits function]) localInput (gather output axes)
  | .protectedComputed _ axes sourceBits ancillaBits function uses => do
    guard (usesValid sourceBits ancillaBits (axes.length-sourceBits) uses)
    let row := gather output axes
    let source := row % 2^sourceBits
    let localInput : State := fun target => state (scatter output axes (source+target*2^sourceBits))
    ProtectedEvaluation.run source (function[source]?.getD 0) uses localInput (row / 2^sourceBits)

def erased (bits : Nat) (axes : List Nat) (outcome : Nat) (state : State) (output : Nat) : WorkM Scalar :=
  let kept := (List.range bits).filter (fun axis => !axes.contains axis)
  sum (2^bits) fun input =>
    if gather input axes == outcome && gather input kept == output then state input else pure Scalar.zero

end QleisliKernel.Raw.Coefficient
