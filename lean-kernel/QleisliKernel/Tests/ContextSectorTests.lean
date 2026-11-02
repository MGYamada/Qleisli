import QleisliKernel.Tests.ContextSectorData

/-! Complete small contextual controls within the unchanged shared work cap.
Exact historical remainder observations remain in Git; legitimate reuse may
change them without changing the accepted source/IR or any refusal obligation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.ContextSectorTests
open QleisliKernel.Qirf

-- This is one full invocation, not independently replenished stage budgets.
#guard ((ContextSector.check artifact order "main" "route" positions requests).run 10000000).1.isOk
example : controls.length = 26 := by decide +kernel
#guard controls.all (·.2)


end QleisliKernel.Tests.ContextSectorTests
