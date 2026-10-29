import QleisliKernel.Tests.SectorArms.Data

/-! Small original-arm/control regression stages. Exact original definitions
and theorem bodies are retained in separately compiled modules to bound kernel
reduction memory. No proof/native policy or semantic oracle is weakened.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SectorArms
open Semantics.Exact Semantics.Finite Semantics.CarrierInterface
open QleisliKernel.Tests.FiniteRestriction

theorem one_fresh_original_graph : (wholeOutcome == .ok [one,scalar imaginaryOne]) = true := by decide +kernel
theorem actual_main_sector_substitution_refuses : (wholeOutcome (data := whole (main := controlled 6)) ==
    .error .equation) = true := by decide +kernel
theorem changed_arm_cannot_reuse_main_sector : (wholeOutcome (data := whole
    (body := implementation 6) (control := controlled 6)) == .error .equation) = true := by decide +kernel

end QleisliKernel.Tests.SectorArms
