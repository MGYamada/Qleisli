import Std

/-! Shared capacities of the existing bounded hierarchical profile.
These constants only name the published limits; they add no acceptance rule.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Hierarchical.Limits

abbrev maxVisits : Nat := 2000000
abbrev maxNodes : Nat := 100000
abbrev maxReferences : Nat := 1000000
abbrev maxDepth : Nat := 256
abbrev maxPayloadBytes : Nat := 16777216

end QleisliKernel.Hierarchical.Limits
