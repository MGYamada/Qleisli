import QleisliKernel.Semantics.Qirf
import Qleisli.Semantics.ObservingFunction

/-! Independent finite QIRF request meaning. No checker, work budget, transport
reader or success predicate occurs in the mathematical contract.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.Qirf
open QleisliKernel.Semantics Qleisli.Semantics.ObservingFunction
open scoped Matrix

/-- Both complete original instruments have one identical, phase-sensitive
operator. Unitarity is on the whole input space, including arbitrary references. -/
structure FiniteContract (dependencies : List Finite.Dependency) (program : Observation.Program)
    (signature : Finite.Basis) (target : QleisliKernel.Qirf.Target) (actual : Exact.Matrix) : Prop where
  implementation : BodyMeaning dependencies program actual
  specification : ∃ specification, QleisliKernel.Semantics.Qirf.targetProgram signature target = some specification ∧
    BodyMeaning [] specification actual
  leftInverse : (square actual)ᴴ * square actual = 1
  rightInverse : square actual * (square actual)ᴴ = 1

end Qleisli.Semantics.Qirf
