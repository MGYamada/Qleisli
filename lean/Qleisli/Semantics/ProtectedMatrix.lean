import Qleisli.Semantics.Protected
import Qleisli.Semantics.Exact

/-! Original physical protected-scope matrix coefficients on the zero image.
No auxiliary expansion, logical replacement, acceptance or capacity is assumed.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.ProtectedMatrix
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Raw
open Qleisli.Semantics.Exact Qleisli.Semantics.Protected

noncomputable def basis (sourceBits column : Nat) : Logical Unit :=
  fun source target _ => if source == column % 2^sourceBits && target == column / 2^sourceBits then 1 else 0

noncomputable def coefficient (sourceBits : Nat) (function : List Nat) (uses : List Use)
    (dimension index : Nat) : ℂ :=
  let row := index / dimension
  let column := index % dimension
  let f := fun source => function[source]?.getD 0
  let physical := compute f (run uses (compute f (zero (basis sourceBits column))))
  physical (row % 2^sourceBits) 0 (row / 2^sourceBits) ()

noncomputable def Meaning (sourceBits dataBits : Nat) (function : List Nat) (uses : List Use)
    (actual : Matrix) : Prop :=
  actual.rows = 2^dataBits ∧ actual.cols = 2^dataBits ∧
    List.Forall₂ (fun index value => scalar value = coefficient sourceBits function uses (2^dataBits) index)
      (List.range (2^dataBits*2^dataBits)) actual.entries

end Qleisli.Semantics.ProtectedMatrix
