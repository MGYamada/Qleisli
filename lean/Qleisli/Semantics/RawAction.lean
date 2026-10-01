import Qleisli.Semantics.Raw
import Qleisli.Semantics.Protected

/-! Unbounded literal complex action of all straight-line pure raw events.
This mathematical reference allocates no executable global matrix. Original
physical computed scopes are retained, including dirty auxiliary coordinates.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.RawAction
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Raw
open Qleisli.Semantics.Exact Qleisli.Semantics.Finite

noncomputable def step (dependencies : List Dependency) (operation : Step) (ψ : Nat → ℂ) : Nat → ℂ :=
  fun output => if !enabled operation.controls output then ψ output else
    match operation.action with
    | .hadamard axis => Protected.gate .h axis ψ output
    | .monomial axes permutation phases =>
      ((List.range permutation.length).map fun input =>
        if permutation[input]? == some (gather output axes) then
          ψ (scatter output axes input) * phase (phases[input]?.getD 0) else 0).sum
    | .contract axes index adjoint =>
      match dependencies[index]? with
      | none => 0
      | some dependency => ((List.range dependency.meaning.cols).map fun input =>
          ψ (scatter output axes input) * (if adjoint then
            star (entry dependency.meaning input (gather output axes))
          else entry dependency.meaning (gather output axes) input)).sum

noncomputable def circuit (dependencies : List Dependency) (steps : List Step) (ψ : Nat → ℂ) : Nat → ℂ :=
  steps.foldl (fun ψ operation => step dependencies operation ψ) ψ

noncomputable def embed (axes : List Nat) (action : (Nat → ℂ) → Nat → ℂ) (ψ : Nat → ℂ) : Nat → ℂ :=
  fun output => action (fun input => ψ (scatter output axes input)) (gather output axes)

noncomputable def event (dependencies : List Dependency) (operation : Event) (ψ : Nat → ℂ) : Nat → ℂ :=
  match operation with
  | .circuit _ steps => circuit dependencies steps ψ
  | .init0 bits => fun output => if output < 2^bits then ψ output else 0
  | .liftBasis before _ inputAxes outputAxes table => fun output =>
    ((List.range (2^before)).map fun input =>
      if scatter input outputAxes (table[gather input inputAxes]?.getD 0) == output then ψ input else 0).sum
  | .reorder bits axes => fun output => ((List.range (2^bits)).map fun input =>
      if gather input axes == output then ψ input else 0).sum
  | .computed _ axes sourceBits ancillaBits function uses _ =>
    embed axes (fun input =>
      let physical := circuit dependencies
        ([computeStep sourceBits axes.length ancillaBits function] ++ uses ++
          [computeStep sourceBits axes.length ancillaBits function])
        (fun label => if label < 2^axes.length then input label else 0)
      fun output => physical output) ψ
  | .protectedComputed _ axes sourceBits _ function uses =>
    embed axes (fun input =>
      let f := fun source => function[source]?.getD 0
      let logicalInput : Protected.Logical Unit := fun source target _ => input (source+target*2^sourceBits)
      let physical := Protected.compute f (Protected.run uses (Protected.compute f (Protected.zero logicalInput)))
      fun output => physical (output % 2^sourceBits) 0 (output / 2^sourceBits) ()) ψ

noncomputable def events (dependencies : List Dependency) (operations : List Event) (ψ : Nat → ℂ) : Nat → ℂ :=
  operations.foldl (fun ψ operation => event dependencies operation ψ) ψ

noncomputable def program (dependencies : List Dependency) (body : Program) (ψ : Nat → ℂ) : Option (Nat → ℂ) := do
  let trace ← QleisliKernel.Semantics.RawTrace.run body
  return events dependencies trace.events ψ

end Qleisli.Semantics.RawAction
