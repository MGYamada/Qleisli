import QleisliKernel.Target.CanonicalOpenQasmGates
import Qleisli.RawBranchFunction

/-! Exact pre-observation gate meaning for the canonical terminal adapter.
Each declared standard gate table is tied to the actual original Raw body,
including its literal complex phase. This does not grant coherent control or
adopt a hardware/target realization; target specification review remains explicit.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.CanonicalOpenQasmGates
open QleisliKernel QleisliKernel.Target.CanonicalOpenQasmGates

theorem gate_meaning (gate : Semantics.CanonicalTerminalQasm.Gate) :
    Qleisli.Semantics.ObservingFunction.BodyMeaning [] (original gate) (expected gate) := by
  have matrix := gate_matrix gate
  cases result : (Raw.BranchFunction.reconstruct [] (original gate)).run 2000000 with
  | mk answer left =>
    cases answer with
    | error error =>
      have empty : (none : Option Semantics.Exact.Matrix) = some (expected gate) := by
        simpa only [reconstructed,result,Except.toOption] using matrix
      cases empty
    | ok actual =>
      have same : actual = expected gate := by
        have equality : some actual = some (expected gate) := by
          simpa only [reconstructed,result,Except.toOption] using matrix
        exact Option.some.inj equality
      have meaning := Qleisli.Raw.BranchFunction.reconstruct_denotes [] (original gate) rfl
        actual 2000000 left result
      rw [same] at meaning
      exact meaning

end Qleisli.CanonicalOpenQasmGates
