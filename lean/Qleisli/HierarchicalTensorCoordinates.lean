import Qleisli.HierarchicalOperators
import Qleisli.CoordinateOperators

/-! Actual tensor coefficients in ordered finite coordinates.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.HierarchicalTensorCoordinates
open QleisliKernel.Hierarchical
open Artifact HierarchicalOperators

theorem take_ofFn (n m : Nat) (bits : Fin (n+m) → Bool) :
    (List.ofFn bits).take n = List.ofFn (fun i => bits (i.castAdd m)) := by
  rw [List.ofFn_add]
  simp
  rfl

theorem drop_ofFn (n m : Nat) (bits : Fin (n+m) → Bool) :
    (List.ofFn bits).drop n = List.ofFn (fun i => bits (i.natAdd n)) := by
  rw [List.ofFn_add]
  simp

theorem apply_tensor_matrix (interface : Interface) (n m : Nat) (first second : Operator)
    (hi : width interface.inputs = n+m) (ho : width interface.outputs = n+m)
    (firstInput : first.inputWidth = n) (firstOutput : first.outputWidth = n)
    (_secondInput : second.inputWidth = m) (_secondOutput : second.outputWidth = m) :
    matrixAt (n+m) (n+m) (apply interface .tensor [first,second]) =
      CoordinateOperators.tensor (matrixAt n n first) (matrixAt m m second) := by
  ext output input
  simp [matrixAt,apply,bounded,raw,hi,ho,firstInput,firstOutput,
    take_ofFn,drop_ofFn,CoordinateOperators.tensor]

end Qleisli.HierarchicalTensorCoordinates
