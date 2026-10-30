import QleisliKernel.CodeSpace
import QleisliKernel.Qirf.RuntimeFamily

/-! Tiny exact code-space/effect regressions. These reduce the actual bounded
computations; they do not establish complex denotation or source preservation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeCode
open Semantics.Exact

private def matrix (rows cols : Nat) (entries : List Int) : Matrix :=
  ⟨rows,cols,entries.map fun n => ⟨.integer n,.integer 0,.integer 0,.integer 0⟩⟩
private def code : Matrix := matrix 2 1 [1,0]
private def identity : Matrix := matrix 2 2 [1,0,0,1]
private def phase : Matrix := matrix 2 2 [-1,0,0,1]
private def leaking : Matrix := matrix 2 2 [0,1,1,0]
private def scalar (n : Int) : Matrix := matrix 1 1 [n]

private def logical (physical : Matrix) : Option (List Scalar) :=
  match ((CodeSpace.readMap code code physical).run 100000).1 with
  | .ok checked => some checked.logical.entries
  | _ => none

theorem original_identity_maps_to_identity : logical identity = some [Scalar.one] := by decide +kernel
theorem exact_phase_is_not_erased :
    logical phase = some [⟨.integer (-1),.integer 0,.integer 0,.integer 0⟩] := by decide +kernel
theorem projection_cannot_hide_leakage : logical leaking = none := by decide +kernel

private def accepted (operators : List Matrix) : Bool :=
  ((CodeSpace.read (scalar 1) (scalar 1) (operators.map fun op => ⟨[],[],op⟩)).run 100000).1.isOk

theorem complete_hidden_gram_accepts_identity_and_zero : accepted [scalar 1,scalar 0] = true := by decide +kernel
theorem a_missing_nonzero_history_refuses : accepted [scalar 0] = false := by decide +kernel
theorem duplicate_history_breaks_trace_preservation : accepted [scalar 1,scalar 1] = false := by decide +kernel
theorem empty_history_list_refuses : accepted [] = false := by decide +kernel
theorem equal_physical_width_does_not_make_rectangular_logical_unitary :
    Qirf.RuntimeFamily.logicalEffect .unitary 3 4 = .iso := by decide +kernel
theorem zero_width_observation_never_becomes_pure :
    Qirf.RuntimeFamily.logicalEffect .observe 1 1 = .observe := by decide +kernel
theorem physical_isometry_is_never_sharpened :
    Qirf.RuntimeFamily.logicalEffect .iso 3 3 = .iso := by decide +kernel
theorem declared_observe_is_not_sharpened :
    Qirf.RuntimeFamily.annotationAllowed (some .observe) true true .unitary = false := by decide +kernel
theorem public_quantum_body_requires_annotation :
    Qirf.RuntimeFamily.annotationAllowed none true true .observe = false := by decide +kernel

end QleisliKernel.Tests.RuntimeCode
