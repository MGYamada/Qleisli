import Std

/-! Existing separate operation access interfaces, with no source lookup,
effect inference or body/implementation acceptance.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.OperationPaths

structure Paths where
  applicable : Bool
  adjointable : Bool
  controllable : Bool
  deriving BEq, DecidableEq, Repr

def Paths.meet (left right : Paths) : Paths :=
  ⟨left.applicable && right.applicable,left.adjointable && right.adjointable,
    left.controllable && right.controllable⟩

end QleisliKernel.SourceTypes.OperationPaths
