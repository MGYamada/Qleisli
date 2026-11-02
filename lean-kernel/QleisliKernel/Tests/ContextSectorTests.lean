import QleisliKernel.Tests.ContextSectorData

/-! Existing full contextual controls and their original measured-work claim.
The data module performs no assertions, so focused diagnostics can report the
actual stage/error before this suite's regression assertions are repaired.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.ContextSectorTests
open QleisliKernel.Qirf

-- The controls assert success and exact refusal results; also retain measured work.
#guard ((ContextSector.check artifact order "main" "route" positions requests).run 10000000).2 = 523586
example : controls.length = 25 := by decide +kernel
#guard controls.all (·.2)


end QleisliKernel.Tests.ContextSectorTests
