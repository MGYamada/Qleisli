import Qleisli.Semantics.Raw
import Qleisli.Semantics.Protected

/-! Independent original physical clean-scope obligations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Raw.Pure
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Raw
open Qleisli.Semantics.Protected Qleisli.Semantics.Raw

noncomputable def CleanupMeaning (dependencies : List Dependency) (event : Event) : Prop :=
  match event with
  | .computed _ axes sourceBits ancillaBits function uses logicalSteps =>
    ∃ logical, CleanMeaning dependencies sourceBits axes.length ancillaBits function uses logicalSteps logical
  | .protectedComputed _ _ _ _ function uses => ∀ (R : Type) (ψ : Logical R),
    compute (fun source => function[source]?.getD 0)
      (run uses (compute (fun source => function[source]?.getD 0) (zero ψ))) =
      zero (logical (fun source => function[source]?.getD 0) uses ψ)
  | _ => True

end Qleisli.Raw.Pure
