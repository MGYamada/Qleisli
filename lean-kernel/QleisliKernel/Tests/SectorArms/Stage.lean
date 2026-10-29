import QleisliKernel.Tests.SectorArms.Data

/-! Small original-arm/control regression stages. Exact original definitions
and theorem bodies are retained in separately compiled modules to bound kernel
reduction memory. No proof/native policy or semantic oracle is weakened.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SectorArms
open Semantics.Exact Semantics.Finite Semantics.CarrierInterface
open QleisliKernel.Tests.FiniteRestriction

theorem exact_actual_arm_phase : (outcome == .ok [scalar imaginaryOne]) = true := by decide +kernel
theorem actual_body_substitution_refuses : (outcome (data := artifact (implementation 6)) ==
    .error .equation) = true := by decide +kernel
theorem controlled_phase_substitution_refuses : (outcome (data := artifact (control := controlled 6)) ==
    .error .equation) = true := by decide +kernel
theorem reversed_control_refuses : (outcome (data := artifact (control := controlled 2 false)) ==
    .error .equation) = true := by decide +kernel
theorem unavailable_control_refuses : (outcome (ref := {reference with controlled := 2}) ==
    .error .invalid) = true := by decide +kernel
theorem public_isometry_refuses : (outcome (ref := {reference with publicEffect := .iso}) ==
    .error .request) = true := by decide +kernel
theorem zero_width_type_substitution_refuses : (outcome (ref := {reference with basis := [.bits 0]}) ==
    .error .request) = true := by decide +kernel
theorem hidden_control_observation_refuses : (outcome (data := artifact (control :=
    {(controlled 2) with operations := [.measure 10 100]})) == .error .invalid) = true := by decide +kernel
theorem control_isometry_label_refuses : (outcome (data := artifact (control :=
    {(controlled 2) with effect := .iso})) == .error .invalid) = true := by decide +kernel

theorem written_order_is_not_logical_order : (allOutcome [oneRef,zeroRef] ==
    .ok [one,scalar imaginaryOne]) = true := by decide +kernel
theorem incomplete_partition_refuses : (allOutcome [zeroRef] == .error .request) = true := by decide +kernel
theorem overlapping_partition_refuses : (allOutcome [zeroRef,zeroRef] == .error .request) = true := by decide +kernel
theorem out_of_range_partition_refuses : (allOutcome [zeroRef,{oneRef with label := 2}] ==
    .error .request) = true := by decide +kernel
theorem every_arm_is_checked : (allOutcome [zeroRef,{oneRef with publicEffect := .iso}] ==
    .error .request) = true := by decide +kernel
theorem singleton_still_requires_control : (allOutcome [{zeroRef with controlled := 9}] 1 ==
    .error .invalid) = true := by decide +kernel

theorem three_state_arm_and_its_control : (cycleOutcome == .ok [NominalSector.cycle3]) = true := by
  decide +kernel
theorem equal_width_target_substitution_refuses : (cycleOutcome (ref := {cycleRef with basis := NominalSector.quad}) ==
    .error .request) = true := by decide +kernel
theorem padded_code_leakage_refuses : (cycleOutcome (data := artifact
    {cycleBody with operations := [.pure (.applyUnitary 10 11
      [⟨[],.monomial [0,1] [0,1,3,2] [0,0,0,0]⟩])]}
    cycleControl) == .error .notIsometric) = true := by decide +kernel

end QleisliKernel.Tests.SectorArms
